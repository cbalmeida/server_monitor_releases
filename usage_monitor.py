#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# =============================================================================
#  usage_monitor.py - monitor contínuo de carga (CPU / memória / disco)
#                     com painel de desempenho em tela cheia no terminal
#
#  Fica rodando e, a cada janela, grava uma linha no relatório com média,
#  p95, pico e quantas vezes cada recurso bateu no teto. A janela é de 30 s
#  no horário comercial (06h-20h) e de 5 min fora dele (a 1ª de cada partida
#  é curta, ~10 s, para a central ter dado logo). Dentro da janela tira
#  amostras a cada 5 s para não perder picos curtos que a média esconderia.
#
#  No início grava o hardware da máquina e roda um mini-benchmark (~1 min)
#  para registrar a capacidade, permitindo comparar servidores diferentes.
#
#  Modos:
#    ./usage_monitor.py                     coleta + painel na tela
#    ./usage_monitor.py --headless          só coleta (nohup, tmux, serviço)
#    sudo ./usage_monitor.py --instalar-servico   serviço systemd (volta sozinho no boot)
#    ./usage_monitor.py --view [ARQ]        só painel, lendo um relatório
#                                           (acompanha um coletor em execução)
#    sudo ./usage_monitor.py -d /var/lib/postgresql   benchmark no disco do banco
#    ./usage_monitor.py -h                  todas as opções
#
#  Feito para Ubuntu 20.04 (Python 3.8, só biblioteca padrão). Na partida
#  verifica as ferramentas do benchmark (fio, util-linux, coreutils...) e
#  instala via apt-get as que faltarem (--no-install para pular).
#  Sucessor do usage_monitor.sh: o formato do relatório é o mesmo.
# =============================================================================

import argparse
import ast
import base64
import bisect
import codecs
import contextlib
import collections
import copy
try:
    import ctypes                  # Windows: coleta pelas APIs do sistema (kernel32, ntdll, pdh)
except ImportError:                # Python sem _ctypes: no Windows a coleta fica indisponível
    ctypes = None
try:
    import curses                  # no Windows vem do pacote windows-curses (pip install windows-curses)
except ImportError:
    curses = None
import datetime
import decimal
import email.utils
try:
    import fcntl                   # só Linux/Mac; no Windows a trava é msvcrt.locking (lock_file)
except ImportError:
    fcntl = None
import getpass
import gzip
import hashlib
import hmac
import html
import http.client
import io
import json
import locale
import math
try:
    import msvcrt                  # só Windows: trava de arquivo e leitura de segredo com eco '*'
except ImportError:
    msvcrt = None
import os
import platform
import queue
import random
import re
import secrets
import select
import shlex
import shutil
import signal
import socket
try:
    import ssl
except ImportError:            # Python sem OpenSSL: só sslmode=disable
    ssl = None
import stat
import struct
import subprocess
import sys
import tempfile
import threading
import time
import unicodedata
import urllib.error
import urllib.parse
import urllib.request
import uuid
import weakref
import zlib
try:
    import winreg                  # só Windows: versão do sistema, CPU, fuso, MachineGuid
except ImportError:
    winreg = None
from array import array
from xml.sax.saxutils import escape as xml_escape

VERSION = "2.15.0"
# Projeto Firebase da C2 (padrão do --firebase-setup). Não são segredos: a URL só identifica o banco e
# a chave só identifica o projeto (restrita às APIs de login); o acesso é decidido pelas regras.
FIREBASE_DB_URL = "https://c2-server-monitor-default-rtdb.firebaseio.com"
FIREBASE_API_KEY = "AIzaSyDToSilQhJ6AQomv5lK_3sLEFdgLvFPAYQ"
PROC = os.environ.get("USAGE_MONITOR_PROC", "/proc")   # sobrescrevíveis só para testes
SYS = os.environ.get("USAGE_MONITOR_SYS", "/sys")
NAN = float("nan")
SHM_DIR = "/dev/shm"             # RAM (tmpfs): amostra ao vivo, heartbeat e estado do envio
IS_WINDOWS = os.name == "nt"     # Windows: monitoramento básico (WindowsSource), sem painel, --service
SERVICE_RESTART = 75             # código de saída do coletor do --service: reiniciar já (autoatualização)
SUPERVISED_ENV = "USAGE_MONITOR_SUPERVISED"   # coletor filho do --service (o pai o reinicia)
STOP_FILE = "server_monitor.parar"            # --parar: pede ao --service que encerre (gravando a janela)
SERVICE_LOG = "server_monitor_servico.log"    # saída do --service (sem console)
SERVICE_LOG_MAX = 5 << 20


# --------------------------------------------------------------------------
# Utilidades
# --------------------------------------------------------------------------
def die(msg):
    sys.stderr.write("ERRO: %s\n" % msg)
    sys.exit(1)


def read_file(path):
    try:
        with open(path) as f:
            return f.read()
    except OSError:
        return ""


def iso_now():
    return datetime.datetime.now().astimezone().isoformat(timespec="seconds")


def hms():
    return time.strftime("%H:%M:%S")


def F(x, fmt):
    return "NA" if x is None else fmt % x


def rnd(x, n):
    """Arredonda como o relatório mostra (médias são feitas sobre o valor gravado)."""
    return float("%.*f" % (n, x))


def run(cmd, capture=False):
    """Roda um comando de shell; devolve (código, saída)."""
    try:
        p = subprocess.run(cmd, shell=True, stdout=subprocess.PIPE if capture else subprocess.DEVNULL,
                           stderr=subprocess.DEVNULL, universal_newlines=True)
        return p.returncode, (p.stdout or "")
    except OSError:
        return 127, ""


def fmax(a, b):
    try:
        a = float(a)
    except (TypeError, ValueError):
        a = 0.0
    try:
        b = float(b)
    except (TypeError, ValueError):
        b = 0.0
    return "%.6g" % max(a, b)


def live_path(log):
    """Arquivo com a última amostra (para o --view de outro terminal). Fica em RAM."""
    h = hashlib.sha1(os.path.abspath(log).encode()).hexdigest()[:12]
    if IS_WINDOWS:          # sem tmpfs: pasta do programa (protegida pelo instalador), não o %TEMP% compartilhado
        d = os.path.join(os.path.dirname(os.path.abspath(log)), SYNC_DIR, "run")
        with contextlib.suppress(OSError):
            os.makedirs(d, exist_ok=True)
    else:
        d = SHM_DIR if os.path.isdir(SHM_DIR) and os.access(SHM_DIR, os.W_OK) else tempfile.gettempdir()
    uid = os.getuid() if hasattr(os, "getuid") else 0
    return os.path.join(d, "usage_monitor.%d.%s.json" % (uid, h))


# --------------------------------------------------------------------------
# Baixo impacto: prioridade reduzida e escrita em disco com ritmo controlado
# --------------------------------------------------------------------------
NICE_LOW = 10                         # prioridade de CPU depois do benchmark (0 = normal, 19 = mínima)
IOPRIO_SET = {"x86_64": 251, "amd64": 251, "aarch64": 30, "arm64": 30}   # nº da syscall ioprio_set
IOPRIO_CLASS_IDLE, IOPRIO_CLASS_SHIFT, IOPRIO_WHO_PROCESS = 3, 13, 1
DISK_RATE = 2 << 20                   # B/s máximos ao reescrever arquivos grandes (retenção, fatias diárias)
PSI_BUSY = 5.0                        # % (PSI io some avg10) acima do qual a retenção espera o disco folgar
FIRST_WINDOW = 10                     # s da 1ª janela de cada sessão (dado na central logo após a partida)
COMPACT_EVERY = 6 * 3600              # s entre verificações da retenção local
COMPACT_RETRY = 900                   # s até tentar de novo uma retenção adiada (disco ocupado)
COMPACT_SYNC_BYTES = 8 << 20          # fdatasync a cada 8 MB copiados


def first_samples(sample):
    """Amostras da 1ª janela (curta) de uma sessão: FIRST_WINDOW s, no mínimo 2."""
    return max(2, -(-FIRST_WINDOW // max(1, int(sample))))


class CompactAbort(Exception):
    """Retenção interrompida (disco ocupado ou monitor parando): tenta de novo depois."""


def tasks():
    """Threads (tids) deste processo; [0] (a própria thread) fora do Linux."""
    try:
        return [int(t) for t in os.listdir("/proc/self/task")] or [0]
    except (OSError, ValueError):
        return [0]


def ioprio_idle(tid):
    """Classe de E/S ociosa (idle) para uma thread: syscall ioprio_set via ctypes ou, em arquiteturas
    sem o número conhecido, o comando ionice. No Linux, nice e ionice valem por THREAD (pid 0 = só a
    chamadora); threads criadas depois herdam. Devolve True se aplicou."""
    nr = IOPRIO_SET.get(platform.machine().lower())
    if nr is not None:
        try:
            import ctypes
            libc = ctypes.CDLL(None, use_errno=True)
            if libc.syscall(nr, IOPRIO_WHO_PROCESS, tid, IOPRIO_CLASS_IDLE << IOPRIO_CLASS_SHIFT) == 0:
                return True
        except (OSError, AttributeError, ImportError):
            pass
    if shutil.which("ionice"):
        return run("ionice -c3 -p %d" % (tid or os.getpid()))[0] == 0
    return False


def lower_priority(enabled=True):
    """Depois do benchmark (que precisa da prioridade normal): CPU com nice NICE_LOW e E/S na classe
    ociosa, em todas as threads já existentes (as próximas herdam). Só diminui a prioridade, nunca
    aumenta (no reinício da autoatualização o processo já vem baixo). Devolve o texto para a tela."""
    if not enabled:
        return "prioridade normal (low_priority desativado)"
    if IS_WINDOWS:
        return win_lower_priority()
    if platform.system() != "Linux":
        return "prioridade normal (só no Linux)"
    cpu = io = 0
    ids = tasks()
    for tid in ids:
        try:
            if os.getpriority(os.PRIO_PROCESS, tid) < NICE_LOW:
                os.setpriority(os.PRIO_PROCESS, tid, NICE_LOW)
            cpu += 1
        except OSError:
            pass
        io += ioprio_idle(tid)
    return "prioridade baixa: CPU nice %d%s, E/S %s" % (
        NICE_LOW, "" if cpu == len(ids) else " (parcial)",
        "ociosa (idle)" if io == len(ids) else "ociosa em %d de %d threads" % (io, len(ids)) if io else "normal (ioprio indisponível)")


def io_pressure():
    """PSI de E/S 'some avg10' (%), ou None sem PSI (kernel antigo)."""
    for line in read_file(PROC + "/pressure/io").splitlines():
        if line.startswith("some "):
            for tok in line.split()[1:]:
                if tok.startswith("avg10="):
                    try:
                        return float(tok[6:])
                    except ValueError:
                        return None
    return None


class Pacer:
    """Limita a taxa de bytes gravados/lidos (dorme entre blocos): escrita grande nunca vira rajada.
    wait() permite interromper (Event)."""

    def __init__(self, rate=None, stop=None):
        self.rate = rate or DISK_RATE
        self.stop = stop
        self.t0 = time.monotonic()
        self.n = 0

    def add(self, nbytes):
        self.n += nbytes
        ahead = self.n / float(self.rate) - (time.monotonic() - self.t0)
        if ahead > 0.05:
            if self.stop is not None:
                self.stop.wait(ahead)
            else:
                time.sleep(ahead)


def datasync(f):
    """fdatasync (só os dados, sem metadados desnecessários); fsync onde não existe (Mac)."""
    getattr(os, "fdatasync", os.fsync)(f.fileno())


def drop_cache(f, end=None):
    """Tira do cache de páginas o que já foi lido/gravado (posix_fadvise DONTNEED): copiar o relatório
    não pode expulsar do cache os dados do banco de dados/aplicação do servidor."""
    if hasattr(os, "posix_fadvise"):
        try:
            os.posix_fadvise(f.fileno(), 0, end or 0, os.POSIX_FADV_DONTNEED)
        except OSError:
            pass


def seek_ts(path, t, size, chunk=1 << 16):
    """Posição (início de uma linha DATA com ts <= t) a partir da qual reler um relatório trocado pela
    retenção, por busca binária: lê ~20 blocos de 64 KB em vez do arquivo inteiro. Sempre igual ou antes
    do ponto exato (quem lê filtra pelo horário); 0 se não achar."""
    lo, hi, best = 0, size, 0
    try:
        with open(path, "rb") as f:
            while hi - lo > chunk:
                mid = (lo + hi) // 2
                f.seek(mid)
                buf = f.read(chunk)
                i = buf.find(b"\nDATA ts=")
                ts = iso_epoch(buf[i + 9:i + 60].split(b" ", 1)[0].decode("ascii", "replace")) if i >= 0 else None
                if ts is None or ts > t:
                    hi = mid
                else:
                    lo, best = mid, mid + i + 1
    except OSError:
        return 0
    return best


# --------------------------------------------------------------------------
# Leitura do kernel (/proc) e cálculo de uma amostra
# --------------------------------------------------------------------------
def snap(disks):
    s = {"t": time.monotonic(), "cpu": {}, "dsk": {}, "mem": {}, "vm": {}, "psi": {}}
    for line in read_file(PROC + "/stat").splitlines():
        p = line.split()
        if not p:
            continue
        if p[0].startswith("cpu"):
            v = [int(x) for x in p[1:9]] + [0] * max(0, 9 - len(p))
            s["cpu"][p[0]] = (sum(v[:8]), v[3] + v[4], v[4], v[7])   # total, ocioso, iowait, steal
        elif p[0] == "procs_running":
            s["run"] = int(p[1])
    want = set(disks)
    for line in read_file(PROC + "/diskstats").splitlines():
        p = line.split()
        if len(p) >= 14 and p[2] in want:
            # leituras, setores lidos, ms lendo, escritas, setores escritos, ms escrevendo, ms ocupado, ms ponderado
            s["dsk"][p[2]] = tuple(int(p[i]) for i in (3, 5, 6, 7, 9, 10, 12, 13))
    for line in read_file(PROC + "/meminfo").splitlines():
        p = line.split()
        if len(p) >= 2:
            s["mem"][p[0].rstrip(":")] = int(p[1])
    for line in read_file(PROC + "/vmstat").splitlines():
        p = line.split()
        if len(p) == 2 and p[0] in ("pswpin", "pswpout", "pgmajfault"):
            s["vm"][p[0]] = int(p[1])
    for res in ("cpu", "memory", "io"):
        for line in read_file("%s/pressure/%s" % (PROC, res)).splitlines():
            p = line.split()
            for tok in p[1:]:
                if tok.startswith("total="):
                    s["psi"][res + "_" + p[0]] = int(tok[6:])
    s["load"] = read_file(PROC + "/loadavg").split()[:3]
    up = read_file(PROC + "/uptime").split()
    s["up"] = float(up[0]) if up else None
    return s


def cpu_count():
    """vCPUs pelo /proc/stat (linhas cpu0, cpu1...); 0 fora do Linux."""
    return sum(1 for l in read_file(PROC + "/stat").splitlines() if l.startswith("cpu") and l[3:4].isdigit())


def load_snapshot(ncpu=None):
    """Carga do instante, barata (só /proc/loadavg e /proc/pressure), para o heartbeat: load1/load5,
    ncpu e PSI avg10 ('some' de cpu/memória/io e 'full' de memória/io). Omite o que não existir."""
    out = {}
    la = read_file(PROC + "/loadavg").split()
    for i, k in ((0, "load1"), (1, "load5")):
        try:
            out[k] = round(float(la[i]), 2)
        except (IndexError, ValueError):
            pass
    if ncpu:
        out["ncpu"] = int(ncpu)
    for res, key in (("cpu", "psi_cpu"), ("memory", "psi_mem"), ("io", "psi_io")):
        for line in read_file("%s/pressure/%s" % (PROC, res)).splitlines():
            p = line.split()
            kind = p[0] if p else ""
            # cpu 'full' (kernels novos) é sempre 0 no nível do sistema: ignorado
            name = key if kind == "some" else key + "_full" if kind == "full" and res != "cpu" else None
            for tok in p[1:] if name else ():
                if tok.startswith("avg10="):
                    try:
                        out[name] = round(float(tok[6:]), 2)
                    except ValueError:
                        pass
    return out


def compute_sample(p, c, disks):
    """Uma amostra a partir de dois snapshots.

    Devolve (valores gravados na janela, extras só para o painel). Os valores são
    arredondados como na linha da v1 para que as médias da janela batam."""
    dt = c["t"] - p["t"]
    if dt <= 0:
        dt = 1.0

    def D(a, b):
        x = b - a
        return x if x > 0 else 0

    def pct(a, b):
        return 100.0 * a / b if b > 0 else 0.0

    pc, cc = p["cpu"], c["cpu"]
    tt = ti = tw = ts = 0
    if "cpu" in pc and "cpu" in cc:
        tt = D(pc["cpu"][0], cc["cpu"][0]); ti = D(pc["cpu"][1], cc["cpu"][1])
        tw = D(pc["cpu"][2], cc["cpu"][2]); ts = D(pc["cpu"][3], cc["cpu"][3])
    cpu = pct(tt - ti, tt); iow = pct(tw, tt); st = pct(ts, tt)
    hot = 0.0
    percpu = []
    for k in sorted((k for k in cc if k != "cpu" and k in pc), key=lambda k: int(k[3:])):
        t = D(pc[k][0], cc[k][0])
        u = pct(t - D(pc[k][1], cc[k][1]), t) if t > 0 else 0.0
        percpu.append(round(u, 1))
        if t > 0 and u > hot:
            hot = u
    rq = max(0, c.get("run", 1) - 1)          # -1 = o próprio processo de leitura
    m = c["mem"]
    mt, ma = m.get("MemTotal", 0), m.get("MemAvailable", 0)
    mem = pct(mt - ma, mt)
    swp = pct(m.get("SwapTotal", 0) - m.get("SwapFree", 0), m.get("SwapTotal", 0))

    def V(k):
        return D(p["vm"].get(k, 0), c["vm"].get(k, 0)) / dt

    swin, swout, majf = V("pswpin"), V("pswpout"), V("pgmajfault")

    def psi(k):
        if k in c["psi"] and k in p["psi"]:
            return rnd(pct(D(p["psi"][k], c["psi"][k]) / 1e6, dt), 2)
        return None

    s = {"dt": rnd(dt, 2), "cpu": rnd(cpu, 1), "iow": rnd(iow, 1), "st": rnd(st, 1), "hot": rnd(hot, 1),
         "rq": rq, "mem": rnd(mem, 1), "swp": rnd(swp, 1), "swin": rnd(swin, 1), "swout": rnd(swout, 1),
         "majf": rnd(majf, 1), "pc": psi("cpu_some"), "pms": psi("memory_some"), "pmf": psi("memory_full"),
         "pis": psi("io_some"), "pif": psi("io_full")}
    for d in disks:
        a, b = p["dsk"].get(d), c["dsk"].get(d)
        if a is None or b is None:
            a = b = (0,) * 8
        rio, rs, rms, wio, ws, wms, tk, wt = (D(a[i], b[i]) for i in range(8))
        ios = rio + wio
        r = rs * 512 / 1048576 / dt
        w = ws * 512 / 1048576 / dt
        u = min(100.0, tk / (dt * 10))
        s[d + ".u"] = rnd(u, 1); s[d + ".r"] = rnd(r, 2); s[d + ".w"] = rnd(w, 2); s[d + ".mb"] = rnd(r + w, 2)
        s[d + ".io"] = rnd(ios / dt, 1)
        s[d + ".aw"] = rnd((rms + wms) / ios if ios else 0, 2)
        s[d + ".qd"] = rnd(wt / (dt * 1000), 2)
        s[d + ".ri"] = rnd(rio / dt, 1); s[d + ".wi"] = rnd(wio / dt, 1)
        s[d + ".raw"] = rnd(rms / rio if rio else 0, 2); s[d + ".waw"] = rnd(wms / wio if wio else 0, 2)
    x = {"percpu": percpu, "load": c.get("load", []), "up": c.get("up"),
         "mem_total": mt, "mem_avail": ma,
         "mem_cache": m.get("Cached", 0) + m.get("Buffers", 0) + m.get("SReclaimable", 0),
         "swap_total": m.get("SwapTotal", 0), "swap_free": m.get("SwapFree", 0)}
    return s, x


def sample_line(s, disks, ncpu):
    """Linha legível de uma amostra (modo --headless)."""
    o = "%s  CPU %5.1f%% (hot %3.0f%%) fila %d/%d iow %.0f%% | MEM %5.1f%% swap %.0f%%" % (
        hms(), s["cpu"], s["hot"], s["rq"], ncpu, s["iow"], s["mem"], s["swp"])
    for d in disks:
        o += " | %s %3.0f%% %.1fMB/s %.0fio" % (d, s[d + ".u"], s[d + ".mb"], s[d + ".io"])
    if s["pc"] is not None:
        o += " | PSI c/m/io %s/%s/%s%%" % (F(s["pc"], "%.2f"), F(s["pms"], "%.2f"), F(s["pis"], "%.2f"))
    return o


# --------------------------------------------------------------------------
# Camada de plataforma: de onde vêm as amostras (Linux: /proc; Windows: APIs do sistema)
# --------------------------------------------------------------------------
# As duas fontes entregam o mesmo formato de snapshot/amostra (snap/compute_sample) e de filesystems,
# então agregação, linha DATA, diagnóstico, histórico e nuvem são os mesmos. Métrica sem equivalente na
# plataforma vira None -> "NA" na linha DATA (contrato do relatório). Caminho 1 (futuro, Windows completo):
# discos em WindowsSource.disks() + contadores PhysicalDisk do PDH preenchendo s["dsk"] como o /proc/diskstats,
# e full=True para o benchmark.
class LinuxSource:
    """Coleta pelo /proc e /sys: o caminho de sempre (monitoramento completo, com benchmark)."""
    name, monitoring, full = "linux", "completo", True
    errors = {}

    def available(self):
        return os.path.isfile(PROC + "/stat") and os.path.isfile(PROC + "/diskstats")

    def disks(self):
        return os.environ.get("DISKS", "").split() or detect_disks()

    def cpu_count(self):
        return cpu_count()

    def snap(self, disks):
        return snap(disks)

    def sample(self, p, c, disks):
        return compute_sample(p, c, disks)

    def line(self, s, disks, ncpu):
        return sample_line(s, disks, ncpu)

    def loadavg(self):
        return read_file(PROC + "/loadavg").split()[:3]

    def filesystems(self):
        return filesystems()

    def load_snapshot(self, ncpu):
        return load_snapshot(ncpu)

    def os_info(self):
        return linux_os_info()


WIN_PDH = (("rq", "\\System\\Processor Queue Length"), ("swp", "\\Paging File(_Total)\\% Usage"))
PDH_FMT_DOUBLE = 0x00000200
DRIVE_FIXED = 3
BELOW_NORMAL_PRIORITY_CLASS = 0x00004000
SystemProcessorPerformanceInformation = 8
# fabricante/modelo do BIOS -> mesmo vocabulário do systemd-detect-virt
VIRT_HINTS = (("vmware", "vmware"), ("virtualbox", "oracle"), ("innotek", "oracle"), ("qemu", "kvm"), ("kvm", "kvm"),
              ("bochs", "kvm"), ("openstack", "kvm"), ("xen", "xen"), ("virtual machine", "microsoft"),
              ("amazon ec2", "amazon"), ("google compute", "google"), ("parallels", "parallels"))


def win_dll(name):
    """DLL do sistema (WinDLL, stdcall) ou None (fora do Windows, sem ctypes ou DLL ausente)."""
    try:
        return ctypes.WinDLL(name)
    except (AttributeError, OSError):
        return None


def win_structs():
    """Estruturas das APIs usadas (só ctypes, sem ctypes.wintypes)."""
    class MEMORYSTATUSEX(ctypes.Structure):
        _fields_ = [("dwLength", ctypes.c_uint32), ("dwMemoryLoad", ctypes.c_uint32)] + [
            (k, ctypes.c_uint64) for k in ("ullTotalPhys", "ullAvailPhys", "ullTotalPageFile", "ullAvailPageFile",
                                            "ullTotalVirtual", "ullAvailVirtual", "ullAvailExtendedVirtual")]

    class SPPI(ctypes.Structure):              # SYSTEM_PROCESSOR_PERFORMANCE_INFORMATION (48 bytes)
        _fields_ = [("IdleTime", ctypes.c_int64), ("KernelTime", ctypes.c_int64), ("UserTime", ctypes.c_int64),
                    ("DpcTime", ctypes.c_int64), ("InterruptTime", ctypes.c_int64), ("InterruptCount", ctypes.c_uint32)]

    class PDHVALUE(ctypes.Structure):          # PDH_FMT_COUNTERVALUE com o double da união (alinhado em 8)
        _fields_ = [("CStatus", ctypes.c_uint32), ("doubleValue", ctypes.c_double)]
    return MEMORYSTATUSEX, SPPI, PDHVALUE


def reg_value(path, name):
    """Valor de HKEY_LOCAL_MACHINE\\path (visão 64 bits mesmo num Python 32 bits); '' se ausente ou fora do Windows."""
    if winreg is None:
        return ""
    try:
        with winreg.OpenKey(winreg.HKEY_LOCAL_MACHINE, path, 0,
                            winreg.KEY_READ | getattr(winreg, "KEY_WOW64_64KEY", 0)) as k:
            v = winreg.QueryValueEx(k, name)[0]
    except OSError:
        return ""
    if isinstance(v, (list, tuple)):                       # REG_MULTI_SZ
        v = " ".join(str(x) for x in v)
    return " ".join(str(v).split())


def virt_guess(man, model):
    """Virtualização pelo fabricante/modelo do BIOS (registro), no vocabulário do systemd-detect-virt."""
    t = ("%s %s" % (man, model)).lower()
    for k, v in VIRT_HINTS:
        if k in t:
            return v
    return "none" if t.strip() else "desconhecido"


def hex32(rc):
    return "0x%08X" % (rc & 0xFFFFFFFF)


class WindowsSource:
    """Coleta no Windows 7 / Server 2008 R2 ou mais novo só com ctypes (sem pywin32, WMI nem processo externo):
    CPU total (GetSystemTimes) e por núcleo (NtQuerySystemInformation), fila do processador e uso do arquivo
    de paginação (PDH com nomes em inglês: PdhAddEnglishCounterW existe desde o Vista/2008, então vale em
    qualquer idioma do Windows), memória (GlobalMemoryStatusEx) e espaço dos volumes fixos
    (GetLogicalDriveStringsW/GetDriveTypeW/GetDiskFreeSpaceExW/GetVolumeInformationW).
    Monitoramento "básico": sem desempenho de disco (util/latência/IOPS), PSI, steal, iowait, swap in/out e
    load average (NA no relatório) e sem benchmark. errors guarda o que falhou (para o --diagnostico)."""
    name, monitoring, full = "windows", "basico", False

    def __init__(self, k32=None, ntdll=None, pdh=None, netapi=None):
        self.netapi = netapi                       # netapi32 (domínio/grupo de trabalho): carregada só no uso
        self.k32 = k32 if k32 is not None else win_dll("kernel32")
        self.ntdll = ntdll if ntdll is not None else win_dll("ntdll")
        self.pdh = pdh if pdh is not None else win_dll("pdh")
        self.S = win_structs() if ctypes is not None else None
        self.ncpu = os.cpu_count() or 1
        self.errors = {}
        self.query, self.counters = None, {}
        if self.k32 is None:
            self.errors["kernel32"] = "kernel32.dll indisponível (não é Windows ou Python sem ctypes)"
            return
        with contextlib.suppress(Exception):
            self.k32.SetErrorMode(1)               # SEM_FAILCRITICALERRORS: unidade sem mídia não abre janela
        self.pdh_open()

    def available(self):
        return self.k32 is not None

    def disks(self):
        return []                                  # caminho 1: discos físicos (PhysicalDisk no PDH)

    def cpu_count(self):
        return self.ncpu

    def pdh_open(self):
        """Fila do processador e uso do arquivo de paginação pelo PDH (os dois são instantâneos: uma coleta basta)."""
        if self.pdh is None:
            self.errors["pdh"] = "pdh.dll indisponível"
            return
        q = ctypes.c_void_p()
        rc = self.pdh.PdhOpenQueryW(None, ctypes.c_size_t(0), ctypes.byref(q))
        if rc != 0:
            self.errors["pdh"] = "PdhOpenQueryW: " + hex32(rc)
            return
        add = getattr(self.pdh, "PdhAddEnglishCounterW", None) or self.pdh.PdhAddCounterW
        for key, path in WIN_PDH:
            h = ctypes.c_void_p()
            rc = add(q, path, ctypes.c_size_t(0), ctypes.byref(h))
            if rc == 0:
                self.counters[key] = h
            else:
                self.errors[key] = "%s: %s" % (path, hex32(rc))
        if self.counters:
            self.query = q

    def pdh_values(self):
        out = {}
        if self.query is None:
            return out
        rc = self.pdh.PdhCollectQueryData(self.query)
        if rc != 0:
            self.errors["pdh"] = "PdhCollectQueryData: " + hex32(rc)
            return out
        for key, h in self.counters.items():
            v = self.S[2]()
            rc = self.pdh.PdhGetFormattedCounterValue(h, PDH_FMT_DOUBLE, None, ctypes.byref(v))
            if rc == 0 and v.CStatus in (0, 1):    # PDH_CSTATUS_VALID_DATA / NEW_DATA
                out[key] = v.doubleValue
            else:
                self.errors[key] = "PdhGetFormattedCounterValue: %s (status %s)" % (hex32(rc), hex32(v.CStatus))
        return out

    def cpu_times(self):
        """(ocioso, kernel, usuário) do sistema em unidades de 100 ns (kernel inclui o ocioso) ou None."""
        idle, kern, user = ctypes.c_uint64(), ctypes.c_uint64(), ctypes.c_uint64()
        if not self.k32.GetSystemTimes(ctypes.byref(idle), ctypes.byref(kern), ctypes.byref(user)):
            self.errors["cpu"] = "GetSystemTimes falhou"
            return None
        return idle.value, kern.value, user.value

    def percpu(self):
        """(ocioso, kernel, usuário) de cada núcleo; [] se indisponível (até 64 núcleos: grupo de processadores atual)."""
        if self.ntdll is None:
            return []
        arr = (self.S[1] * self.ncpu)()
        ret = ctypes.c_uint32()
        rc = self.ntdll.NtQuerySystemInformation(SystemProcessorPerformanceInformation, arr, ctypes.sizeof(arr),
                                                 ctypes.byref(ret))
        if rc != 0:
            self.errors["percpu"] = "NtQuerySystemInformation: " + hex32(rc)
            return []
        n = min(self.ncpu, ret.value // ctypes.sizeof(self.S[1]))
        return [(arr[i].IdleTime, arr[i].KernelTime, arr[i].UserTime) for i in range(n)]

    def memory(self):
        """Bytes de RAM total/disponível e do limite/disponível de commit (RAM + arquivo de paginação) ou None."""
        m = self.S[0]()
        m.dwLength = ctypes.sizeof(m)
        if not self.k32.GlobalMemoryStatusEx(ctypes.byref(m)):
            self.errors["mem"] = "GlobalMemoryStatusEx falhou"
            return None
        return {"total": m.ullTotalPhys, "avail": m.ullAvailPhys, "commit_total": m.ullTotalPageFile,
                "commit_avail": m.ullAvailPageFile}

    def uptime(self):
        """Segundos desde o boot (GetTickCount64: Vista/2008 ou mais novo) ou None."""
        try:
            f = self.k32.GetTickCount64
            f.restype = ctypes.c_uint64
            return f() / 1000.0
        except (AttributeError, OSError):
            return None

    def snap(self, disks):
        """Snapshot no formato do snap() do Linux: compute_sample faz as contas iguais."""
        s = {"t": time.monotonic(), "cpu": {}, "dsk": {}, "mem": {}, "vm": {}, "psi": {}, "load": [], "up": None}
        t = self.cpu_times()
        if t:
            s["cpu"]["cpu"] = (t[1] + t[2], t[0], 0, 0)          # total, ocioso, iowait, steal
        for i, (idle, kern, user) in enumerate(self.percpu()):
            s["cpu"]["cpu%d" % i] = (kern + user, idle, 0, 0)
        m = self.memory()
        if m:
            s["mem"] = {"MemTotal": m["total"] // 1024, "MemAvailable": m["avail"] // 1024}
        s["pdh"] = self.pdh_values()
        return s

    def sample(self, p, c, disks):
        s, x = compute_sample(p, c, disks)
        for k in ("iow", "st", "swin", "swout", "majf"):
            s[k] = None                                # sem equivalente no Windows: NA na linha DATA
        if "cpu" not in c["cpu"] or "cpu" not in p["cpu"]:
            s["cpu"] = None
        if not x["percpu"]:
            s["hot"] = None
        if not c["mem"]:
            s["mem"] = None
        pdh = c.get("pdh") or {}
        q, sw = pdh.get("rq"), pdh.get("swp")
        # Processor Queue Length conta só quem ESPERA; a fila do Linux (procs_running) conta também quem roda.
        # Somando as CPUs ocupadas, "fila > nº de CPUs" continua significando processos esperando CPU.
        s["rq"] = int(round(s["cpu"] * self.ncpu / 100.0)) + int(q) if q is not None and s["cpu"] is not None else None
        s["swp"] = rnd(sw, 1) if sw is not None else None
        return s, x

    def line(self, s, disks, ncpu):
        return "%s  CPU %s%% (núcleo mais ocupado %s%%) fila %s/%d | MEM %s%% paginação %s%%" % (
            hms(), F(s["cpu"], "%5.1f"), F(s["hot"], "%3.0f"), F(s["rq"], "%d"), ncpu, F(s["mem"], "%5.1f"),
            F(s["swp"], "%.0f"))

    def loadavg(self):
        return []                                      # Windows não tem load average: NA

    def load_snapshot(self, ncpu):
        return {"ncpu": int(ncpu)} if ncpu else {}

    def filesystems(self):
        """Volumes fixos (C:\\, D:\\...) no formato de filesystems(): mount = raiz da unidade, fstype = NTFS/ReFS/
        FAT32, livre = disponível para o usuário do serviço. Rede, removíveis e CD ficam de fora (um compartilhamento
        travado bloquearia a coleta); volumes montados em pasta (sem letra) não aparecem."""
        if self.k32 is None:
            return []
        buf = ctypes.create_unicode_buffer(1024)
        n = self.k32.GetLogicalDriveStringsW(len(buf), buf)
        if not 0 < n <= len(buf):
            self.errors["fs"] = "GetLogicalDriveStringsW: %s" % n
            return []
        out = []
        for root in buf[:n].split("\0"):
            if not root or self.k32.GetDriveTypeW(root) != DRIVE_FIXED:
                continue
            free, total, tfree = ctypes.c_uint64(), ctypes.c_uint64(), ctypes.c_uint64()
            if not self.k32.GetDiskFreeSpaceExW(root, ctypes.byref(free), ctypes.byref(total), ctypes.byref(tfree)):
                continue                               # sem permissão, BitLocker travado, desmontado...
            if total.value <= 0:
                continue
            fsn = ctypes.create_unicode_buffer(64)
            ok = self.k32.GetVolumeInformationW(root, None, 0, None, None, None, fsn, len(fsn))
            used = max(0, total.value - tfree.value)
            pct = 100.0 * used / (used + free.value) if used + free.value > 0 else 100.0
            out.append({"mount": root, "device": "", "fstype": (fsn.value if ok else "") or "?",
                        "total_bytes": total.value, "free_bytes": free.value, "used_pct": round(pct, 1)})
            if len(out) >= FS_MAX:
                break
        return out

    def os_info(self):
        """Doc info/<sid>/os do Windows: registro (versão, edição, build, BIOS), netapi32 (domínio) e
        GetTickCount64 (boot). Arquitetura do sistema, não a do Python (PROCESSOR_ARCHITEW6432 num Python 32 bits)."""
        d = {"family": "windows"}
        d.update(win_release())
        d["arch"] = norm_arch(os.environ.get("PROCESSOR_ARCHITEW6432") or os.environ.get("PROCESSOR_ARCHITECTURE")
                              or platform.machine())
        d["hostname"] = short_host(platform.node() or os.environ.get("COMPUTERNAME", ""))
        d["domain"] = win_domain(self.netapi)
        up = self.uptime()
        if up is not None:
            d["boot_at_ms"] = int((time.time() - up) * 1000)
        bios = "HARDWARE\\DESCRIPTION\\System\\BIOS"
        man, model = dmi_clean(reg_value(bios, "SystemManufacturer")), dmi_clean(reg_value(bios, "SystemProductName"))
        # BIOSVersion e SystemBiosVersion (REG_MULTI_SZ, na chave System): Proxmox/Oracle VM aparecem na versão
        ver = dmi_clean(" ".join((reg_value(bios, "BIOSVersion"),
                                  reg_value("HARDWARE\\DESCRIPTION\\System", "SystemBiosVersion"))))
        d["virtualization"], d["hypervisor"] = virt_identify(man, model, dmi_clean(reg_value(bios, "BIOSVendor")),
                                                             bios_version=ver)
        d["manufacturer"], d["product"] = man, model
        return os_doc_clean(d)

    def hardware(self, host):
        """Linhas HW (chave, valor) do Windows: versão (registro), CPU, RAM, virtualização e volumes."""
        cv = "SOFTWARE\\Microsoft\\Windows NT\\CurrentVersion"
        build = reg_value(cv, "CurrentBuildNumber") or reg_value(cv, "CurrentBuild")
        osn = " ".join(x for x in (reg_value(cv, "ProductName") or "Windows", reg_value(cv, "CSDVersion"),
                                   reg_value(cv, "DisplayVersion") or reg_value(cv, "ReleaseId")) if x)
        bios = "HARDWARE\\DESCRIPTION\\System\\BIOS"
        man, model = reg_value(bios, "SystemManufacturer"), reg_value(bios, "SystemProductName")
        cpu0 = "HARDWARE\\DESCRIPTION\\System\\CentralProcessor\\0"
        m = self.memory() or {}
        up = self.uptime()
        out = [("hostname", platform.node() or host), ("os", osn + (" (build %s)" % build if build else "")),
               ("kernel", platform.version()), ("arch", platform.machine()), ("virtualization", virt_guess(man, model)),
               ("hw_model", " ".join(x for x in (man, model) if x) or "?"),
               ("uptime", "up %d dias, %d horas" % (up // 86400, up % 86400 // 3600) if up is not None else ""),
               ("cpu_model", reg_value(cpu0, "ProcessorNameString") or "?"), ("cpu_logical", self.ncpu),
               ("cpu_max_mhz", reg_value(cpu0, "~MHz")), ("mem_total_GB", "%.1f" % (m.get("total", 0) / GIB)),
               # arquivo de paginação ~ limite de commit - RAM
               ("swap_total_GB", "%.1f" % (max(0, m.get("commit_total", 0) - m.get("total", 0)) / GIB))]
        hyp = self.os_info().get("hypervisor")          # v2.9: chave nova, mesmo valor de info/<sid>/os
        if hyp:
            out.insert(5, ("hypervisor", hyp))
        for f in self.filesystems():
            out.append(("fs", "%s em %s (%s) tamanho=%s usado=%s (%.0f%%)" % (
                f["mount"], f["mount"], f["fstype"], fmt_bytes(f["total_bytes"]),
                fmt_bytes(f["total_bytes"] - f["free_bytes"]), f["used_pct"])))
        out.append(("monitoring", "básico (Windows: CPU, fila, memória e espaço; sem desempenho de disco nem benchmark)"))
        return out


# --------------------------------------------------------------------------
# Sistema operacional (v2.9): info/<sid>/os, dados estáticos enviados na partida e quando mudam
# --------------------------------------------------------------------------
# Só leituras baratas (arquivos de texto do /etc, /proc e /sys no Linux; registro e APIs do kernel32/netapi32
# no Windows), nunca processo externo. Campo que não dá para identificar fica ausente (não se inventa valor).
# Nada de número de série, UUID, usuário ou endereço IP.
ROOTFS = ""                      # prefixo dos arquivos do /etc e /usr/lib (sobrescrito só nos testes)
OS_STR_MAX = 128                 # limite dos textos de info/<sid>/os nas regras
OS_RELEASE_KEYS = ("distro_id", "name", "version", "version_id", "codename", "pretty_name")
OS_INFO_TTL = 3600               # releitura (os-release/registro mudam num upgrade; o boot só com reinício)
_OS_CACHE = []                   # [instante da leitura, doc]
DMI_JUNK = {"", "to be filled by o.e.m.", "to be filled by oem", "system manufacturer", "system product name",
            "default string", "not specified", "not applicable", "none", "oem", "o.e.m.", "unknown",
            "type1productconfigid", "invalid", "n/a", "na", "x.x"}
# texto (fabricante + modelo + fornecedor e versão do BIOS, minúsculo) -> hipervisor, na ordem de prioridade:
# a plataforma de gerência (Proxmox VE, OLVM, oVirt, RHV, Oracle VM) vence o motor genérico (KVM/QEMU/Xen), que
# fica no fim; VirtualBox antes do Oracle VM ("Oracle VM VirtualBox"). Expressões regulares (re.search).
HYPERVISORS = ((r"virtualbox|innotek", "VirtualBox"), (r"vmware", "VMware"), (r"parallels", "Parallels"),
               (r"proxmox|\bpve\b", "Proxmox VE"),
               (r"\bolvm\b|oracle linux virtualization manager", "OLVM"),
               (r"\brhev\b|\brhv\b|red hat virtualization|red hat enterprise virtualization", "Red Hat Virtualization"),
               (r"\bovirt\b", "oVirt"),
               (r"oracle ?vm\b|\dovm\b", "Oracle VM"),           # Xen do Oracle VM Server: BIOS "4.4.4OVM"
               (r"microsoft corporation virtual machine|hyper-v", "Hyper-V"),
               (r"amazon ec2|\d\.amazon\b", "Amazon EC2"),       # Xen antigo da AWS: BIOS "4.11.amazon"
               (r"google compute engine", "Google Compute Engine"), (r"openstack", "OpenStack"),
               (r"nutanix", "Nutanix AHV"), (r"alibaba cloud", "Alibaba Cloud ECS"), (r"digitalocean", "DigitalOcean"),
               (r"apple virtualization", "Apple Virtualization"), (r"bhyve", "bhyve"),
               (r"hvm domu|xen", "Xen"), (r"kvm", "KVM"), (r"qemu|bochs", "QEMU"))
RE_HYPERVISORS = tuple((re.compile(k), v) for k, v in HYPERVISORS)
ARCH_NAMES = {"x86_64": "x86_64", "amd64": "x86_64", "x64": "x86_64", "em64t": "x86_64", "aarch64": "arm64",
              "arm64": "arm64", "armv8l": "arm64", "i386": "x86", "i486": "x86", "i586": "x86", "i686": "x86",
              "x86": "x86", "armv7l": "armv7", "armv7": "armv7", "armhf": "armv7"}
# Windows: build -> versão comercial (servidores LTSC e clientes)
WIN_SERVER_BUILDS = {20348: "2022", 17763: "2019", 14393: "2016", 9600: "2012 R2", 9200: "2012", 7601: "2008 R2",
                     7600: "2008 R2", 6003: "2008", 6002: "2008", 6001: "2008"}
WIN_CLIENT_BUILDS = {9600: "8.1", 9200: "8", 7601: "7", 7600: "7", 6003: "Vista", 6002: "Vista", 6001: "Vista",
                     6000: "Vista"}
RE_REDHAT = re.compile(r"^(.*?)\s+release\s+([0-9][0-9.]*)", re.I)
RE_WIN_PRODUCT = re.compile(r"^(?:Microsoft\s+)?Windows(?:\s+Server)?(?:\s+(?:\d{4}(?:\s+R2)?|11|10|8\.1|8|7|Vista))?\s*(.*)$",
                            re.I)


def read_text(path, limit=65536):
    """Texto de um arquivo pequeno (até limit bytes, UTF-8 com substituição); '' se ausente."""
    try:
        with open(path, "rb") as f:
            return f.read(limit).decode("utf-8", "replace")
    except OSError:
        return ""


def kv_file(text):
    """CHAVE=valor por linha (os-release, lsb-release), com ou sem aspas; comentários ignorados."""
    out = {}
    for line in text.splitlines():
        k, sep, v = line.strip().partition("=")
        if not sep or k.startswith("#") or not re.match(r"^[A-Z0-9_]+$", k):
            continue
        v = v.strip()
        if len(v) >= 2 and v[0] == v[-1] and v[0] in "\"'":
            v = v[1:-1].replace('\\"', '"').replace("\\$", "$").replace("\\`", "`").replace("\\\\", "\\")
        out[k] = " ".join(v.split())
    return out


def norm_arch(m):
    m = (m or "").strip()
    return ARCH_NAMES.get(m.lower(), m)


def dmi_clean(v):
    """Fabricante/modelo do DMI/BIOS sem os textos de preenchimento ("To be filled by O.E.M.")."""
    v = " ".join((v or "").split())
    return "" if v.lower() in DMI_JUNK else v


def virt_identify(vendor, product, bios_vendor="", hv_flag=False, hv_type="", clock="", xen_dom0=False, hv_known=True,
                  bios_version=""):
    """(virtualization, hypervisor|None) pelo fabricante/modelo e fornecedor/versão do DMI/BIOS e, no Linux, pelas
    pistas do kernel: flag 'hypervisor' do /proc/cpuinfo, /sys/hypervisor/type e o relógio paravirtual
    (kvm-clock = KVM).
    hv_known=False (ARM: o cpuinfo não tem a flag) = fabricante desconhecido não basta para dizer 'physical'."""
    t = " ".join((vendor, product, bios_vendor, bios_version)).lower()
    if "amazon" in t and product.lower().endswith(".metal"):
        return "physical", None                        # EC2 bare metal: fabricante Amazon, sem hipervisor
    hyp = next((v for k, v in RE_HYPERVISORS if k.search(t)), None)
    if hyp is None and hv_type == "xen" and not xen_dom0:
        hyp = "Xen"
    if hyp is None and (hv_flag or (hv_type and not xen_dom0)):
        hyp = ("KVM" if "kvm-clock" in clock else "Hyper-V" if "hyperv" in clock else "Xen" if "xen" in clock else None)
        return "virtual", hyp
    if hyp == "QEMU" and "kvm-clock" in clock:
        hyp = "KVM"                                    # QEMU com aceleração KVM (Proxmox, libvirt...)
    if hyp:
        return "virtual", hyp
    return ("physical" if (vendor or product) and hv_known else "unknown"), None


def os_doc_clean(d):
    """Doc final: sem campos vazios, textos cortados em OS_STR_MAX."""
    out = {}
    for k, v in d.items():
        if v is None or v == "":
            continue
        out[k] = clip(v, OS_STR_MAX) if isinstance(v, str) else v
    return out


def short_host(name):
    return (name or "").split(".")[0]


def fqdn():
    return socket.getfqdn()


def dns_domain(name):
    """Domínio de um nome completo (srv01.empresa.local -> empresa.local); '' se não houver ou for localhost."""
    name = (name or "").strip().rstrip(".").lower()
    if "." not in name or re.match(r"^[0-9.]+$", name) or ":" in name or name.startswith("localhost"):
        return ""
    dom = name.split(".", 1)[1]
    return "" if dom in ("localdomain", "localhost", "local", "(none)") else dom


def linux_release():
    """Campos da distribuição: /etc/os-release (ou /usr/lib/os-release) e, sem ele (CentOS 6, Ubuntu < 15.04,
    Debian < 7), /etc/lsb-release, /etc/redhat-release (e afins) ou /etc/debian_version."""
    r = kv_file(read_text(ROOTFS + "/etc/os-release") or read_text(ROOTFS + "/usr/lib/os-release"))
    ver = r.get("VERSION", "")
    d = {"distro_id": re.sub(r"[^a-z0-9._-]", "", r.get("ID", "").lower()), "name": r.get("NAME", ""),
         # "20.04.6 LTS (Focal Fossa)" -> "20.04.6 LTS"; "7 (Core)" -> "7" (o nome-código tem campo próprio)
         "version": re.sub(r"\s*\([^)]*\)\s*$", "", ver), "version_id": r.get("VERSION_ID", ""),
         "codename": r.get("VERSION_CODENAME") or r.get("UBUNTU_CODENAME", ""), "pretty_name": r.get("PRETTY_NAME", "")}
    if not d["codename"] and d["distro_id"] == "debian":
        m = re.search(r"\(([a-z]+)\)", ver)                # Debian 8: VERSION="8 (jessie)", sem VERSION_CODENAME
        d["codename"] = m.group(1) if m else ""
    if d["distro_id"] or d["pretty_name"]:
        return d
    lsb = kv_file(read_text(ROOTFS + "/etc/lsb-release"))
    if lsb.get("DISTRIB_ID"):
        return {"distro_id": re.sub(r"[^a-z0-9._-]", "", lsb["DISTRIB_ID"].lower()), "name": lsb["DISTRIB_ID"],
                "version_id": lsb.get("DISTRIB_RELEASE", ""), "codename": lsb.get("DISTRIB_CODENAME", ""),
                "pretty_name": lsb.get("DISTRIB_DESCRIPTION", "")}
    for fn in ("oracle-release", "rocky-release", "almalinux-release", "centos-release", "fedora-release",
               "redhat-release", "system-release"):
        line = read_text(ROOTFS + "/etc/" + fn).strip().split("\n")[0].strip()
        m = RE_REDHAT.match(line)
        if not m:
            continue
        name = m.group(1).strip()
        low = name.lower()
        did = ("ol" if "oracle" in low else "rocky" if "rocky" in low else "almalinux" if "alma" in low
               else "centos" if "centos" in low else "fedora" if "fedora" in low else "amzn" if "amazon" in low
               else "scientific" if "scientific" in low else "rhel" if "red hat" in low else "")
        return {"distro_id": did, "name": name + (" Linux" if did == "centos" and "linux" not in low else ""),
                "version": m.group(2), "version_id": m.group(2).split(".")[0], "pretty_name": line}
    deb = read_text(ROOTFS + "/etc/debian_version").strip()
    if re.match(r"^[0-9]", deb):
        return {"distro_id": "debian", "name": "Debian GNU/Linux", "version": deb, "version_id": deb.split(".")[0],
                "pretty_name": "Debian GNU/Linux " + deb}
    return {}


def linux_virt():
    """(virtualization, hypervisor, fabricante, modelo) pelo DMI (/sys/class/dmi/id: legível por todos, sem
    número de série) e pelas pistas do kernel."""
    dmi = SYS + "/class/dmi/id/"
    vendor, product = dmi_clean(read_text(dmi + "sys_vendor", 256)), dmi_clean(read_text(dmi + "product_name", 256))
    bios = dmi_clean(read_text(dmi + "bios_vendor", 256))
    bios_ver = dmi_clean(read_text(dmi + "bios_version", 256))     # v2.9.1: Proxmox/Oracle VM se mostram aqui
    flag, known = False, False
    try:
        with open(PROC + "/cpuinfo", "rb") as f:          # só até a 1ª linha "flags" (o arquivo cresce com as CPUs)
            for raw in f:
                if raw.startswith(b"flags"):           # x86; no ARM não há flag de hipervisor ("Features")
                    flag, known = b" hypervisor" in raw, True
                    break
    except OSError:
        pass
    hvt = read_text(SYS + "/hypervisor/type", 64).strip().lower()
    clock = read_text(SYS + "/devices/system/clocksource/clocksource0/available_clocksource", 512)
    dom0 = "control_d" in read_text(PROC + "/xen/capabilities", 256)
    virt, hyp = virt_identify(vendor, product, bios, flag, hvt, clock, dom0, known, bios_ver)
    return virt, hyp, vendor, product


def linux_os_info():
    """Doc info/<sid>/os de uma máquina Linux (family 'other' fora do Linux: Mac nos testes, BSD...)."""
    u = os.uname()
    d = {"family": "linux" if u.sysname == "Linux" else "other"}
    d.update(linux_release())
    d["kernel"], d["arch"], d["hostname"] = u.release, norm_arch(u.machine), short_host(u.nodename)
    d["domain"] = dns_domain(u.nodename) or dns_domain(fqdn())
    for line in read_text(PROC + "/stat").splitlines():
        if line.startswith("btime "):
            with contextlib.suppress(ValueError):
                d["boot_at_ms"] = int(line.split()[1]) * 1000
            break
    d["virtualization"], d["hypervisor"], d["manufacturer"], d["product"] = linux_virt()
    return os_doc_clean(d)


def win_reg_int(path, name):
    v = reg_value(path, name)
    try:
        return int(v)
    except ValueError:
        return None


def win_release():
    """Campos da versão do Windows pelo registro (CurrentVersion). ProductName do Windows 11 ainda diz
    'Windows 10': build >= 22000 corrige o nome; a versão comercial dos servidores vem do build."""
    cv = "SOFTWARE\\Microsoft\\Windows NT\\CurrentVersion"
    prod = " ".join(reg_value(cv, "ProductName").replace("(R)", "").replace("®", "").split())
    bstr = reg_value(cv, "CurrentBuildNumber") or reg_value(cv, "CurrentBuild")
    try:
        build = int(bstr)
    except ValueError:
        build = None
    if build is not None and build >= 22000 and re.match(r"^Windows 10\b", prod):
        prod = "Windows 11" + prod[10:]
    itype = reg_value(cv, "InstallationType")
    server = itype.lower().startswith("server") or "server" in prod.lower()
    feat = reg_value(cv, "DisplayVersion") or reg_value(cv, "ReleaseId")
    major, minor = win_reg_int(cv, "CurrentMajorVersionNumber"), win_reg_int(cv, "CurrentMinorVersionNumber")
    vid = "%d.%d" % (major, minor) if major is not None and minor is not None else reg_value(cv, "CurrentVersion")
    if build is None:
        ver = ""
    elif server:
        ver = "2025" if build >= 26100 else WIN_SERVER_BUILDS.get(build) or feat
    else:
        ver = "11" if build >= 22000 else "10" if build >= 10240 else WIN_CLIENT_BUILDS.get(build, "")
        if ver in ("10", "11") and feat:
            ver += " " + feat
    m = RE_WIN_PRODUCT.match(prod)
    edition = m.group(1).strip() if m else ""
    if not edition:
        ed = reg_value(cv, "EditionID")
        edition = ed[6:] if ed.startswith("Server") and len(ed) > 6 else ed
    ubr = win_reg_int(cv, "UBR")
    csd = reg_value(cv, "CSDVersion")
    d = {"distro_id": "windows", "name": ("Windows Server" if server else "Windows") if prod or itype else "",
         "version": ver, "version_id": vid, "pretty_name": " ".join(x for x in (prod, csd) if x), "edition": edition,
         "build": ("%d.%d" % (build, ubr) if ubr is not None else str(build)) if build is not None else "",
         "kernel": "%s.%d" % (vid, build) if vid and build is not None else ""}
    return d


def win_domain(netapi=None):
    """Domínio DNS do AD (registro do TCP/IP), senão o domínio NetBIOS ou grupo de trabalho
    (NetGetJoinInformation, netapi32), senão USERDNSDOMAIN; '' se nada."""
    dom = reg_value("SYSTEM\\CurrentControlSet\\Services\\Tcpip\\Parameters", "Domain")
    if dom:
        return dom.lower()
    netapi = netapi if netapi is not None else win_dll("netapi32")
    if netapi is not None:
        buf, status = ctypes.c_wchar_p(), ctypes.c_int()
        try:
            rc = netapi.NetGetJoinInformation(None, ctypes.byref(buf), ctypes.byref(status))
        except (AttributeError, OSError):
            rc = -1
        if rc == 0:
            name = buf.value or ""
            with contextlib.suppress(Exception):
                netapi.NetApiBufferFree(buf)
            if status.value in (2, 3) and name:          # NetSetupWorkgroupName / NetSetupDomainName
                return name
    return os.environ.get("USERDNSDOMAIN", "").lower()


_SOURCE = []


def source():
    """Fonte de amostras desta máquina (criada uma vez por processo)."""
    if not _SOURCE:
        _SOURCE.append(WindowsSource() if IS_WINDOWS else LinuxSource())
    return _SOURCE[0]


def os_info(force=False):
    """Doc info/<sid>/os desta máquina, relido no máximo a cada OS_INFO_TTL (force=True: agora). O horário do
    boot fica o da primeira leitura do processo: ele só muda com reinício (= nova partida), e recalculado
    (agora - tempo ligado) oscilaria com ajustes do relógio, reenviando o doc à toa."""
    now = time.monotonic()
    if _OS_CACHE and not force and now - _OS_CACHE[0] < OS_INFO_TTL:
        return dict(_OS_CACHE[1])
    try:
        d = source().os_info()
    except Exception:                                  # leitura opcional: nunca derruba a coleta nem o envio
        d = {}
    if _OS_CACHE and "boot_at_ms" in _OS_CACHE[1] and "boot_at_ms" in d:
        d["boot_at_ms"] = _OS_CACHE[1]["boot_at_ms"]
    _OS_CACHE[:] = [now, d]
    return dict(d)


def win_lower_priority(k32=None):
    """Windows: classe de prioridade abaixo do normal (~ nice 10) para o processo todo (as threads herdam).
    Não usa o modo background (PROCESS_MODE_BACKGROUND_BEGIN): ele põe a CPU em prioridade ociosa e, com o
    servidor a 100%, o sinal de vida pararia (a central veria OFFLINE justo na sobrecarga). E/S fica normal
    (o coletor grava pouco)."""
    k32 = k32 if k32 is not None else win_dll("kernel32")
    try:
        cur = k32.GetCurrentProcess
        cur.restype = ctypes.c_void_p              # pseudo-handle (-1) inteiro, sem truncar em 64 bits
        ok = k32.SetPriorityClass(ctypes.c_void_p(cur()), BELOW_NORMAL_PRIORITY_CLASS)
    except (AttributeError, OSError):
        ok = False
    return ("prioridade baixa: CPU abaixo do normal (BELOW_NORMAL), E/S normal" if ok
            else "prioridade normal (SetPriorityClass indisponível)")


def lock_file(f):
    """Trava exclusiva sem esperar num arquivo aberto: flock (Linux/Mac) ou msvcrt.locking no 1º byte
    (Windows). False = outro processo já tem a trava. No Windows a trava é de região e impede até a leitura
    por outro handle: por isso lá se trava um arquivo à parte (<relatório>.lock), nunca o próprio relatório."""
    if fcntl is not None:
        try:
            fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
            return True
        except BlockingIOError:
            return False
    f.seek(0)
    try:
        msvcrt.locking(f.fileno(), msvcrt.LK_NBLCK, 1)
        return True
    except OSError:
        return False


def machine_id():
    """Id da máquina (detecta pasta copiada para outro servidor): /etc/machine-id no Linux, MachineGuid no Windows."""
    if IS_WINDOWS:
        return reg_value("SOFTWARE\\Microsoft\\Cryptography", "MachineGuid")
    return (read_file("/etc/machine-id") or read_file("/var/lib/dbus/machine-id")).strip()


# --------------------------------------------------------------------------
# Agregação de uma janela -> linha DATA (+ resumo legível)
# --------------------------------------------------------------------------
def aggregate(samples, disks, caps, ncpu, cth, mth, dth, ts, loadavg, fs=None):
    """Linha DATA da janela e resumo legível. fs = filesystems() medidos no fim da janela
    (None = não medidos: a linha sai sem os campos fs_*, como até a v2.2)."""
    V = {}
    for s in samples:
        for k, v in s.items():
            if v is not None:
                V.setdefault(k, []).append(v)

    def seqsum(xs):
        t = 0.0                      # soma sequencial, como o awk (sum() do Python 3.12+ compensa)
        for x in xs:
            t += x
        return t

    def avg(k):
        return seqsum(V[k]) / len(V[k]) if V.get(k) else None

    def mx(k):
        return max(V[k]) if V.get(k) else None

    def p95(k):
        a = sorted(V.get(k) or [])
        if not a:
            return None
        return a[max(1, int(math.ceil(0.95 * len(a)))) - 1]

    def cnt(k, th):
        return sum(1 for v in V.get(k, []) if v >= th)

    def hi(x, th):
        return x is not None and x >= th

    def z(x):
        return x or 0

    L = (list(loadavg) + ["NA"] * 3)[:3]
    win = seqsum(V.get("dt", [])); n = len(V.get("dt", []))
    cpu_hi = cnt("cpu", cth); rq_over = cnt("rq", ncpu + 1); mem_hi = cnt("mem", mth)
    o = "DATA ts=%s win=%.0f n=%d" % (ts, win, n)
    o += " cpu_avg=" + F(avg("cpu"), "%.1f") + " cpu_p95=" + F(p95("cpu"), "%.1f") + " cpu_max=" + F(mx("cpu"), "%.1f") + " cpu_hi=%d" % cpu_hi
    o += " hot_avg=" + F(avg("hot"), "%.1f") + " hot_max=" + F(mx("hot"), "%.1f")
    o += " iow_avg=" + F(avg("iow"), "%.1f") + " st_avg=" + F(avg("st"), "%.1f") + " st_max=" + F(mx("st"), "%.1f")
    o += " rq_avg=" + F(avg("rq"), "%.1f") + " rq_max=" + F(mx("rq"), "%d") + " rq_over=%d" % rq_over
    o += " load1=%s load5=%s load15=%s" % tuple(L)
    o += " psi_cpu=" + F(avg("pc"), "%.2f") + " psi_cpu_max=" + F(mx("pc"), "%.2f")
    o += " mem_avg=" + F(avg("mem"), "%.1f") + " mem_max=" + F(mx("mem"), "%.1f") + " mem_hi=%d" % mem_hi
    o += " swap=" + F(mx("swp"), "%.1f") + " swin=" + F(avg("swin"), "%.1f") + " swout=" + F(avg("swout"), "%.1f") + " majf=" + F(avg("majf"), "%.1f")
    o += " psi_mem=" + F(avg("pms"), "%.2f") + " psi_mem_full=" + F(avg("pmf"), "%.2f") + " psi_mem_max=" + F(mx("pms"), "%.2f")
    o += " psi_io=" + F(avg("pis"), "%.2f") + " psi_io_full=" + F(avg("pif"), "%.2f") + " psi_io_max=" + F(mx("pis"), "%.2f")

    flags = []
    if cpu_hi > 0: flags.append("CPU")
    if rq_over > 0: flags.append("RUNQ")
    if hi(mx("pc"), 10): flags.append("PSI_CPU")
    if mem_hi > 0: flags.append("MEM")
    if z(avg("swin")) + z(avg("swout")) >= 10: flags.append("SWAP")
    if hi(mx("pms"), 5): flags.append("PSI_MEM")
    if hi(mx("pis"), 20): flags.append("PSI_IO")

    dsk = ""; extra = ""
    for d in disks:
        cb, ci = caps.get(d, ("NA", "NA"))
        try: cb = float(cb)
        except ValueError: cb = 0.0
        try: ci = float(ci)
        except ValueError: ci = 0.0
        u_hi = cnt(d + ".u", dth)
        bwp = 100 * mx(d + ".mb") / cb if cb > 0 and V.get(d + ".mb") else None
        iop = 100 * mx(d + ".io") / ci if ci > 0 and V.get(d + ".io") else None
        o += (" %s.util_avg=%s %s.util_p95=%s %s.util_max=%s %s.util_hi=%d" % (
            d, F(avg(d + ".u"), "%.1f"), d, F(p95(d + ".u"), "%.1f"), d, F(mx(d + ".u"), "%.1f"), d, u_hi))
        o += (" %s.rMBs=%s %s.wMBs=%s %s.MBs_max=%s %s.bw_pct_max=%s" % (
            d, F(avg(d + ".r"), "%.2f"), d, F(avg(d + ".w"), "%.2f"), d, F(mx(d + ".mb"), "%.1f"), d, F(bwp, "%.1f")))
        o += (" %s.iops_avg=%s %s.iops_max=%s %s.iops_pct_max=%s %s.await=%s %s.qd_avg=%s %s.qd_max=%s" % (
            d, F(avg(d + ".io"), "%.0f"), d, F(mx(d + ".io"), "%.0f"), d, F(iop, "%.1f"),
            d, F(avg(d + ".aw"), "%.2f"), d, F(avg(d + ".qd"), "%.2f"), d, F(mx(d + ".qd"), "%.2f")))
        # Campos da v2.0: vão depois de flags (contrato: só acrescentar no fim da linha)
        extra += (" %s.riops=%s %s.wiops=%s %s.r_await=%s %s.w_await=%s" % (
            d, F(avg(d + ".ri"), "%.0f"), d, F(avg(d + ".wi"), "%.0f"), d, F(avg(d + ".raw"), "%.2f"), d, F(avg(d + ".waw"), "%.2f")))
        if u_hi > 0 or hi(bwp, 90) or hi(iop, 90):
            flags.append("DISK:" + d)
        dsk += (" DISCO %-8s util méd %s%% p95 %s%% máx %s%% (>=%d%%: %d) | %s MB/s (pico %s = %s da capacidade)"
                " | %s IOPS (pico %s = %s da capacidade) | await %s ms, fila %s\n" % (
                    d, F(avg(d + ".u"), "%.0f"), F(p95(d + ".u"), "%.0f"), F(mx(d + ".u"), "%.0f"), dth, u_hi,
                    F(avg(d + ".mb"), "%.1f"), F(mx(d + ".mb"), "%.1f"), F(bwp, "%.0f%%"),
                    F(avg(d + ".io"), "%.0f"), F(mx(d + ".io"), "%.0f"), F(iop, "%.0f%%"),
                    F(avg(d + ".aw"), "%.1f"), F(avg(d + ".qd"), "%.1f")))
    fl = ",".join(flags) if flags else "none"
    line = o + " flags=" + fl + extra + (fs_fields(fs) if fs is not None else "")

    txt = "\n===== %s | janela %.0f s | %d amostras =====\n" % (hms(), win, n)
    txt += " CPU   méd %s%%  p95 %s%%  máx %s%% | >=%d%%: %d amostras | núcleo mais quente máx %s%% | iowait %s%% steal %s%%\n" % (
        F(avg("cpu"), "%.1f"), F(p95("cpu"), "%.1f"), F(mx("cpu"), "%.1f"), cth, cpu_hi, F(mx("hot"), "%.0f"), F(avg("iow"), "%.1f"), F(avg("st"), "%.1f"))
    txt += " FILA  run-queue méd %s máx %s (CPUs: %d) | fila > CPUs: %d amostras | load %s %s %s | PSI cpu %s%% (máx %s%%)\n" % (
        F(avg("rq"), "%.1f"), F(mx("rq"), "%d"), ncpu, rq_over, L[0], L[1], L[2], F(avg("pc"), "%.1f"), F(mx("pc"), "%.1f"))
    txt += " MEM   méd %s%%  máx %s%% | >=%d%%: %d amostras | swap %s%% | swap in/out %s/%s pág/s | PSI mem %s%% (máx %s%%)\n" % (
        F(avg("mem"), "%.1f"), F(mx("mem"), "%.1f"), mth, mem_hi, F(mx("swp"), "%.0f"), F(avg("swin"), "%.0f"), F(avg("swout"), "%.0f"), F(avg("pms"), "%.1f"), F(mx("pms"), "%.1f"))
    txt += dsk
    txt += " I/O   PSI io %s%% (máx %s%%)\n" % (F(avg("pis"), "%.1f"), F(mx("pis"), "%.1f"))
    if fs:
        txt += " ESPAÇO " + " | ".join("%s %.0f%% (%s livres)" % (f["mount"], f["used_pct"], fmt_bytes(f["free_bytes"]))
                                        for f in fs) + "\n"
    txt += " >>> %s" % ("OK - nenhum recurso no teto nesta janela" if fl == "none" else "NO TETO: " + fl)
    return line, txt


# --------------------------------------------------------------------------
# Legenda, hardware, dependências e benchmark
# --------------------------------------------------------------------------
LEGEND = """\
# =============================================================================
# USAGE REPORT - gerado por usage_monitor (.py v2 / .sh v1)
# Cada linha começa com um prefixo que indica o tipo:
#   #        comentário / legenda
#   SESSION  início de uma execução do monitor (parâmetros usados; desde a
#            v2.1 também company=empresa, install_id=id estável do servidor, tz=fuso;
#            desde a v2.4 name=nome amigável do servidor, ex.: "Sescom - Linux")
#   HW       hardware da máquina (registrado a cada início)
#   BENCH    mini-benchmark de capacidade (registrado a cada início)
#   CAP      capacidade de referência por disco, usada para calcular os %
#   DATA     uma janela de medição, campos chave=valor. Padrão: 30 s no
#            horário comercial (06h-20h) e 5 min fora dele (ver SESSION
#            biz_interval / biz_hours); use win para ponderar médias.
#            Desde a v2.7.2 a 1ª janela de cada sessão é curta (~10 s, mín.
#            2 amostras) e a seguinte vai até o próximo limite do relógio
#   EVENT    eventos (parada do monitor etc.)
# Dentro de cada janela são feitas amostras a cada N s (padrão 5 s). A linha
# DATA traz média (avg), percentil 95 (p95), pico (max) e quantas amostras
# ficaram no teto (hi / over) -> mostra picos que a média esconde.
#
# Campos da linha DATA:
#  ts            fim da janela (hora local ISO-8601)
#  win / n       duração real da janela (s) / número de amostras
#  cpu_*         % de uso do conjunto de todas as CPUs (100 = todas ocupadas)
#  cpu_hi        nº de amostras com CPU >= limite (padrão 90%)
#  hot_*         % do núcleo mais ocupado (gargalo de processo single-thread)
#  iow_avg       % do tempo de CPU ociosa esperando disco (iowait)
#  st_*          % steal: CPU tomada pelo hipervisor (host da VM sobrecarregado)
#  rq_*          processos prontos para rodar (run queue)
#  rq_over       nº de amostras com run queue > nº de CPUs => demanda MAIOR
#                que a capacidade (processos na fila esperando CPU)
#  load1/5/15    load average do Linux no fim da janela
#  psi_cpu       % do tempo em que algum processo esperou por CPU (Linux PSI)
#  mem_*         % de RAM realmente em uso (MemTotal - MemAvailable)
#  mem_hi        nº de amostras com memória >= limite (padrão 90%)
#  swap          % máximo de swap ocupado
#  swin / swout  páginas/s lidas/gravadas no swap (sustentado > 0 = falta RAM)
#  majf          major page faults/s (páginas que tiveram de vir do disco)
#  psi_mem       % do tempo com algum processo travado esperando memória
#  psi_mem_full  % do tempo com TODOS os processos travados por memória
#  psi_io / psi_io_full   idem, esperando disco (I/O)
#  <disco>.util_*       % do tempo em que o disco esteve ocupado (iostat %util)
#  <disco>.util_hi      nº de amostras com util >= limite (padrão 90%)
#  <disco>.rMBs / wMBs  MB/s lidos / gravados (média da janela)
#  <disco>.MBs_max      pico de MB/s (leitura+escrita) em uma amostra
#  <disco>.bw_pct_max   esse pico em % da capacidade medida (linha CAP)
#  <disco>.iops_*       operações de I/O por segundo
#  <disco>.iops_pct_max pico de IOPS em % da capacidade (precisa do fio)
#  <disco>.await        latência média por operação (ms)
#  <disco>.qd_*         fila média de I/O no disco (queue depth)
#  flags         recursos que bateram no teto na janela (none = tranquilo):
#                CPU, RUNQ, PSI_CPU(>=10%), MEM, SWAP(>=10 pág/s),
#                PSI_MEM(>=5%), PSI_IO(>=20%), DISK:<disco>
# Acrescentados na v2.0 (no fim da linha, depois de flags):
#  <disco>.riops / wiops      IOPS de leitura / gravação (média da janela)
#  <disco>.r_await / w_await  latência média de leitura / gravação (ms)
# Acrescentados na v2.3 (no fim da linha; medidos uma vez no fim de cada janela):
#  fs_n          nº de filesystems reais medidos (ext4, xfs, btrfs, zfs, vfat...;
#                sem rede, tmpfs, overlay, squashfs/snap nem loop)
#  fs_used_max   maior % ocupado entre eles (NA = nenhum)
#  fs<i>.mount   ponto de montagem (espaço e \\ escritos como \\040 e \\134, como no /proc/mounts)
#  fs<i>.dev / fs<i>.type   dispositivo e tipo do filesystem
#  fs<i>.total / fs<i>.free tamanho e espaço livre (bytes; livre = disponível sem ser root)
#  fs<i>.used    % ocupado, como o df: usado / (usado + livre)
# Windows (v2.8, monitoramento básico): SESSION termina com platform=windows
#  monitoring=basico; sem discos (nenhum campo <disco>.*) e NA no que o Windows
#  não tem: iow, st, load, psi_*, swin/swout/majf. rq = threads esperando CPU
#  (Processor Queue Length) + CPUs ocupadas (mesmo sentido do Linux: rq > nº
#  de CPUs = fila); swap = % de uso do arquivo de paginação; fs<i>.mount = raiz
#  da unidade (C:\\), fs<i>.type = NTFS/ReFS/FAT32, fs<i>.dev = NA.
# Observações:
#  - Em SSD/NVMe util=100% nem sempre é saturação total (paralelismo interno);
#    avalie junto com bw_pct_max, iops_pct_max, await, qd e psi_io.
#  - Só discos inteiros são medidos (sda, vda, nvme0n1...); LVM/dm-* não são
#    somados de novo, pois o I/O deles já aparece no disco físico.
#  - O kernel não expõe a banda de memória (GB/s) em uso; a pressão de memória
#    é medida por mem%, swap, majf e psi_mem. A banda máxima fica no BENCH.
#  - NA = métrica não disponível nesta máquina (ex.: kernel sem PSI).
# =============================================================================
"""

# comando -> pacote apt que o fornece (usados no HW e no benchmark)
DEPS = [("df", "coreutils"), ("dd", "coreutils"), ("head", "coreutils"), ("sha256sum", "coreutils"),
        ("lsblk", "util-linux"), ("lscpu", "util-linux"), ("uptime", "procps"), ("hostname", "hostname"),
        ("systemd-detect-virt", "systemd"), ("fio", "fio")]


def check_deps(do_install):
    missing = [(c, p) for c, p in DEPS if not shutil.which(c)]
    if not missing:
        print("Dependências: OK")
        return
    pkgs = []
    for _, p in missing:
        if p not in pkgs:
            pkgs.append(p)
    print("Dependências faltando: " + " ".join(c for c, _ in missing))
    if not do_install:
        print("  --no-install: seguindo sem instalar (métricas dependentes ficarão NA).")
        return
    if not shutil.which("apt-get"):
        print("  apt-get não encontrado; instale manualmente: " + " ".join(pkgs))
        return
    sudo = ""
    if os.geteuid() != 0:
        if not shutil.which("sudo"):
            print("  sem root e sem sudo; instale manualmente: " + " ".join(pkgs))
            return
        sudo = "sudo "
    print("Instalando via apt-get: " + " ".join(pkgs))
    subprocess.call(sudo + "env DEBIAN_FRONTEND=noninteractive apt-get update -qq", shell=True)
    if subprocess.call(sudo + "env DEBIAN_FRONTEND=noninteractive apt-get install -y -qq " + " ".join(pkgs), shell=True):
        print("  AVISO: falha ao instalar algum pacote; seguindo assim mesmo.")
    for c, _ in DEPS:
        if not shutil.which(c):
            print("  ainda faltando: " + c)


def detect_disks():
    """Discos físicos inteiros (ignora loop, ram, cd, device-mapper, raid md)."""
    out = []
    try:
        names = sorted(os.listdir(SYS + "/block"))
    except OSError:
        return out
    for d in names:
        if d.startswith(("loop", "ram", "zram", "sr", "fd", "dm-", "md", "nbd")):
            continue
        try:
            if int(read_file("%s/block/%s/size" % (SYS, d)) or 0) > 0:
                out.append(d)
        except ValueError:
            pass
    return out


# Ocupação dos filesystems (v2.3): só tipos locais reais. Rede (nfs, cifs), fuse, tmpfs, overlay,
# squashfs (snap) e pseudo-filesystems ficam de fora: além de não serem "disco da máquina", um
# statvfs em compartilhamento de rede travado bloquearia a coleta.
FS_TYPES = frozenset("ext2 ext3 ext4 xfs btrfs zfs f2fs vfat msdos exfat ntfs3 jfs reiserfs nilfs2 bcachefs hfsplus".split())
FS_MAX = 16                    # limite de filesystems por janela (linha DATA de tamanho previsível)
GIB = 1024 ** 3
SPACE_WARN_PCT, SPACE_CRIT_PCT = 85.0, 95.0         # % ocupado
SPACE_WARN_FREE, SPACE_CRIT_FREE = 5 * GIB, 1 * GIB  # livres (para quem não é root)
SPACE_ABS_MIN = 10 * GIB       # limites em GB só para filesystems de 10 GB ou mais (/boot e EFI: só o %)
_OCT = re.compile(r"\\([0-7]{3})")


def mount_unescape(s):
    """/proc/mounts escreve espaço, tab, \\n e \\ como \\040, \\011, \\012, \\134."""
    return _OCT.sub(lambda m: chr(int(m.group(1), 8)), s)


def mount_escape(s):
    """Inverso de mount_unescape: o valor gravado na linha DATA nunca tem espaço."""
    return "".join("\\%03o" % ord(c) if c in " \t\n\\" or ord(c) < 32 else c for c in s)


def filesystems():
    """Filesystems reais montados, com tamanho e espaço livre (os.statvfs, sem processo externo).

    Lido uma vez por janela. Dispositivos de loop (snap, imagens) ficam de fora; o mesmo
    dispositivo montado várias vezes (bind mount, subvolumes btrfs) e os datasets de um mesmo
    pool zfs contam uma vez só, pelo ponto de montagem mais curto. Sem permissão para o statvfs
    (ou desmontado no meio da leitura) o filesystem é pulado."""
    best = {}
    for line in read_file(PROC + "/mounts").splitlines():
        p = line.split()
        if len(p) < 3 or p[2] not in FS_TYPES or p[0].startswith("/dev/loop"):
            continue
        dev, mnt, typ = p[0], p[1], p[2]
        key = dev.split("/")[0] if typ == "zfs" else dev
        if key not in best or (len(mnt), mnt) < (len(best[key][1]), best[key][1]):
            best[key] = (dev, mnt, typ)
    out = []
    for dev, mnt, typ in sorted(best.values(), key=lambda x: x[1]):
        try:
            st = os.statvfs(mount_unescape(mnt))
        except (OSError, ValueError):
            continue
        frs = st.f_frsize or st.f_bsize
        total = st.f_blocks * frs
        if total <= 0:
            continue
        free = st.f_bavail * frs
        used = max(0, st.f_blocks - st.f_bfree) * frs
        # como o df: usado / (usado + disponível); a reserva do root não conta como livre
        pct = 100.0 * used / (used + free) if used + free > 0 else 100.0
        out.append({"mount": mount_unescape(mnt), "device": mount_unescape(dev), "fstype": typ,
                    "total_bytes": total, "free_bytes": free, "used_pct": round(pct, 1)})
        if len(out) >= FS_MAX:
            break
    return out


def fs_fields(fs):
    """Campos da linha DATA (v2.3, no fim da linha): fs_n, fs_used_max e fs<i>.* de cada filesystem."""
    o = " fs_n=%d fs_used_max=%s" % (len(fs), F(max((f["used_pct"] for f in fs), default=None), "%.1f"))
    for i, f in enumerate(fs):
        o += " fs%d.mount=%s fs%d.dev=%s fs%d.type=%s fs%d.total=%d fs%d.free=%d fs%d.used=%.1f" % (
            i, mount_escape(f["mount"]), i, mount_escape(f["device"]) or "NA", i, f["fstype"],
            i, f["total_bytes"], i, f["free_bytes"], i, f["used_pct"])
    return o


def fs_parse(kv):
    """Filesystems de uma linha DATA (lista, talvez vazia); None se a linha é anterior à v2.3."""
    try:
        n = int(kv["fs_n"])
    except (KeyError, ValueError):
        return None
    out = []
    for i in range(min(max(n, 0), 64)):
        p = "fs%d." % i
        try:
            dev = kv.get(p + "dev", "NA")
            out.append({"mount": mount_unescape(kv[p + "mount"]), "device": "" if dev == "NA" else mount_unescape(dev),
                        "fstype": kv.get(p + "type", ""), "total_bytes": int(kv[p + "total"]),
                        "free_bytes": int(kv[p + "free"]), "used_pct": float(kv[p + "used"])})
        except (KeyError, ValueError):
            continue                     # filesystem com campo faltando/ilegível: só ele fica de fora
    return out


def space_level(f):
    """Nível (0 normal, 1 atenção, 2 crítico) de um filesystem pelo % ocupado e pelo espaço livre."""
    big = f["total_bytes"] >= SPACE_ABS_MIN
    if f["used_pct"] >= SPACE_CRIT_PCT or (big and f["free_bytes"] < SPACE_CRIT_FREE):
        return 2
    if f["used_pct"] >= SPACE_WARN_PCT or (big and f["free_bytes"] < SPACE_WARN_FREE):
        return 1
    return 0


def space_worst(fs):
    """(nível, filesystem) do pior filesystem (desempate: maior % ocupado); (None, None) sem nenhum."""
    lv, worst = None, None
    for f in fs or ():
        x = space_level(f)
        if worst is None or (x, f["used_pct"]) > (lv, worst["used_pct"]):
            lv, worst = x, f
    return lv, worst


def lscpu():
    _, out = run("LC_ALL=C lscpu", capture=True)
    r = {}
    for line in out.splitlines():
        k, sep, v = line.partition(":")
        if sep:
            r[k.strip()] = v.strip()
    return r


class Monitor:
    """Coletor: grava SESSION/HW/BENCH/CAP no início e DATA a cada janela."""

    def __init__(self, a, log, logf, host, disks, ncpu, out):
        self.a, self.log, self.logf, self.host, self.disks, self.ncpu = a, log, logf, host, disks, ncpu
        self.out = out                  # função de saída na tela (None = silencioso)
        self.caps = {}
        self.bench_file = ""
        self.live = None                # última amostra (o painel lê daqui)
        self.error = None
        self.stop_ev = threading.Event()
        self.samples = []
        self.src = source()             # LinuxSource (/proc) ou WindowsSource (APIs do Windows)
        # amostra ao vivo para o --view de outro terminal (RAM); no Windows não há painel: nada a gravar
        self.live_file = None if IS_WINDOWS else live_path(log)
        self.verbose = True             # False (--service): sem a linha de cada amostra/janela na saída
        self.stop_file = None           # --service: arquivo que pede o encerramento (--parar)
        self.lockf = None               # Windows: trava à parte (<relatório>.lock)
        self.thread = None
        self.stopped = False
        self.ident = None               # Identity (empresa e id da instalação)
        self.sync = None                # SyncManager (envio para a nuvem), se configurado
        self.compacted_at = 0.0
        self.retention_note = ""
        self.compact_state = ""         # resultado da última retenção (diagnóstico)
        self.compact_thread = None
        self.log_lock = threading.Lock()   # escrita no relatório x troca do arquivo pela retenção
        self.priority = ""              # texto da prioridade aplicada depois do benchmark
        self.updater = None             # Updater (autoatualização), só no coletor
        self.db = None                  # DbAgent (acesso remoto ao Postgres), só no coletor com Firebase
        self.sysev = None               # SysEvents (eventos do sistema: admin.system_email), junto com o DbAgent
        self.sql = None                 # SqlEditor (editor SQL remoto, v2.12), junto com o DbAgent

    def say(self, s):
        if self.out:
            self.out(s)

    def write(self, line):
        with self.log_lock:
            self.logf.write(line + "\n")
            self.logf.flush()

    def emit(self, line):
        self.write(line)
        self.say(line)

    def hw(self, k, v):
        self.emit("HW    %-28s: %s" % (k, v))

    def bench(self, k, v):
        self.emit("BENCH %-28s: %s" % (k, v))

    # ---- início ----
    def start_session(self):
        a = self.a
        if os.path.getsize(self.log) == 0:
            self.logf.write(LEGEND)
        self.say("Relatório: " + self.log)
        self.emit("")
        ident = self.ident
        self.emit("SESSION start=%s host=%s version=%s interval=%d sample=%d cpus=%d disks=\"%s\" cpu_hi=%d mem_hi=%d disk_hi=%d"
                  " bench=%s biz_interval=%d biz_hours=%d-%d company=\"%s\" install_id=%s tz=%s name=\"%s\"" % (
                      iso_now(), self.host, VERSION, a.interval, a.sample, self.ncpu, " ".join(self.disks),
                      a.cpu_hi, a.mem_hi, a.disk_hi, "yes" if a.bench and self.src.full else "no", a.biz_interval, a.biz_start, a.biz_end,
                      (ident.company if ident else "").replace('"', "'"), (ident.install_id if ident else "") or "NA",
                      (timezone_name() or "NA").replace(" ", "_"), (ident.name if ident else "").replace('"', "'"))
                  # Windows (v2.8): plataforma e nível do monitoramento no fim (ausentes = linux/completo)
                  + ("" if self.src.full else " platform=%s monitoring=%s" % (self.src.name, self.src.monitoring)))
        if not self.src.full:                          # Windows (básico): sem df/lsblk/lscpu nem benchmark
            self.bdisks = []
            for k, v in self.src.hardware(self.host):
                self.hw(k, v)
        else:
            self.bdisks = self.bench_disks()
            self.collect_hw()
        if a.bench and self.src.full:
            self.run_bench()
        else:
            self.load_caps()
        for d in self.disks:
            bw, io, src = self.caps.get(d, ("NA", "NA", "none"))
            self.emit("CAP   disk=%s bw_MBs=%s iops=%s src=%s" % (d, bw, io, src))
        self.capv = {d: self.caps.get(d, ("NA", "NA"))[:2] for d in self.disks}

    def bench_disks(self):
        """Disco(s) físico(s) onde fica o diretório do benchmark (atravessa LVM/RAID)."""
        _, out = run("df -P %s" % shlex.quote(self.a.bench_dir), capture=True)
        lines = out.splitlines()
        if len(lines) < 2:
            return []
        src = lines[1].split()[0]
        try:
            if not stat.S_ISBLK(os.stat(src).st_mode):
                return []
        except OSError:
            return []
        _, out = run("lsblk -rnso NAME,TYPE %s" % shlex.quote(src), capture=True)
        return sorted(set(l.split()[0] for l in out.splitlines() if len(l.split()) == 2 and l.split()[1] == "disk"))

    def collect_hw(self):
        od = os_info(force=True)                      # os-release com alternativas (CentOS 6, Ubuntu antigo...)
        _, virt = run("systemd-detect-virt", capture=True)
        model = ""
        for line in read_file(PROC + "/cpuinfo").splitlines():
            if line.startswith("model name"):
                model = line.split(":", 1)[1].strip()
                break
        lc = lscpu()
        model = model or lc.get("Model name", "")
        _, fqdn = run("hostname -f", capture=True)
        _, upt = run("uptime -p", capture=True)
        mem = {}
        for line in read_file(PROC + "/meminfo").splitlines():
            p = line.split()
            if len(p) >= 2:
                mem[p[0].rstrip(":")] = int(p[1])
        self.hw("hostname", fqdn.strip() or self.host)
        self.hw("os", od.get("pretty_name") or "desconhecido")
        self.hw("kernel", os.uname().release)
        self.hw("arch", os.uname().machine)
        self.hw("virtualization", virt.strip() or "desconhecido")
        # v2.9 (chaves novas): hipervisor e fabricante/modelo do DMI, como em info/<sid>/os
        if od.get("hypervisor"):
            self.hw("hypervisor", od["hypervisor"])
        if od.get("manufacturer") or od.get("product"):
            self.hw("hw_model", " ".join(x for x in (od.get("manufacturer"), od.get("product")) if x))
        self.hw("uptime", upt.strip())
        self.hw("cpu_model", model or "?")
        self.hw("cpu_sockets", lc.get("Socket(s)", ""))
        self.hw("cpu_cores_per_socket", lc.get("Core(s) per socket", ""))
        self.hw("cpu_threads_per_core", lc.get("Thread(s) per core", ""))
        self.hw("cpu_logical", self.ncpu)
        self.hw("cpu_max_mhz", lc.get("CPU max MHz", ""))
        self.hw("mem_total_GB", "%.1f" % (mem.get("MemTotal", 0) / 1048576))
        self.hw("swap_total_GB", "%.1f" % (mem.get("SwapTotal", 0) / 1048576))
        for d in self.disks:
            base = "%s/block/%s" % (SYS, d)
            try:
                sz = "%.0f" % (int(read_file(base + "/size") or 0) * 512 / 1e9)
            except ValueError:
                sz = "?"
            rota = "rotacional(HDD)" if read_file(base + "/queue/rotational").strip() == "1" else "SSD/NVMe"
            dmodel = " ".join(read_file(base + "/device/model").split())
            sch = read_file(base + "/queue/scheduler")
            sched = sch[sch.find("[") + 1:sch.find("]")] if "[" in sch else ""
            self.hw("disk." + d, "%s GB, %s, modelo=%s, scheduler=%s" % (sz, rota, dmodel or "?", sched or "?"))
        _, out = run("df -hPT -x tmpfs -x devtmpfs -x squashfs -x overlay -x efivarfs", capture=True)
        for line in out.splitlines()[1:]:
            p = line.split()
            if len(p) >= 7:
                self.hw("fs", "%s em %s (%s) tamanho=%s usado=%s (%s)" % (p[6], p[0], p[1], p[2], p[3], p[5]))
        self.hw("bench_dir", "%s (disco: %s)" % (self.a.bench_dir, " ".join(self.bdisks) or "não identificado"))

    def run_bench(self):
        a = self.a

        def timed(cmd):
            t0 = time.monotonic()
            rc, _ = run(cmd)
            return rc, max(1, int((time.monotonic() - t0) * 1000))

        def rate(mb, ms):
            return "%.1f" % (mb * 1000.0 / max(ms, 1))

        def step(msg):
            self.say("    ... " + msg)

        caps = {}
        self.say("--- mini-benchmark (~1-3 min, gera carga; use --no-bench para pular) ---")
        # CPU: sha256 sobre dados em memória, 1 núcleo e todos os núcleos
        step("CPU, 1 núcleo")
        _, ms = timed("head -c %d /dev/zero | sha256sum > /dev/null" % (1024 * 1048576))
        r1 = rate(1024, ms)
        self.bench("cpu_1core_sha256_MBs", r1)
        step("CPU, todos os %d núcleos" % self.ncpu)
        t0 = time.monotonic()
        ps = [subprocess.Popen("head -c %d /dev/zero | sha256sum > /dev/null" % (512 * 1048576), shell=True)
              for _ in range(self.ncpu)]
        for p in ps:
            p.wait()
        rn = rate(512 * self.ncpu, int((time.monotonic() - t0) * 1000))
        self.bench("cpu_all_cores_sha256_MBs", rn)
        self.bench("cpu_scaling_x", "%.1f (ideal ~ nº de núcleos físicos)" % (float(rn) / max(float(r1), 0.1)))

        # Memória: escrita sequencial em buffer maior que o cache (aprox., 1 thread)
        memmb = 0
        for line in read_file(PROC + "/meminfo").splitlines():
            if line.startswith("MemAvailable:"):
                memmb = int(line.split()[1]) // 1024
        if memmb > 1024:
            step("memória")
            _, ms = timed("dd if=/dev/zero of=/dev/null bs=256M count=40")
            self.bench("mem_write_bw_GBs", "%s (aprox., 1 thread)" % rate(10, ms))

        # Disco do diretório de benchmark: escrita/leitura sequencial (+ IOPS com fio)
        try:
            free = shutil.disk_usage(a.bench_dir).free // 1048576
        except OSError:
            free = 0
        fio = shutil.which("fio")
        if free > a.bench_mb * 2 + 1024:
            self.bench_file = bf = os.path.join(a.bench_dir, ".usage_monitor_bench.%d" % os.getpid())
            q = shlex.quote(bf)
            mode = "direct"
            step("disco: gravação sequencial de %d MB em %s" % (a.bench_mb, a.bench_dir))
            rc, ms = timed("dd if=/dev/zero of=%s bs=1M count=%d oflag=direct conv=fsync" % (q, a.bench_mb))
            if rc:
                mode = "buffered"
                rc, ms = timed("dd if=/dev/zero of=%s bs=1M count=%d conv=fsync" % (q, a.bench_mb))
            w = rate(a.bench_mb, ms)
            step("disco: leitura sequencial")
            rc, ms = timed("dd if=%s of=/dev/null bs=1M iflag=direct" % q)
            if rc:
                mode += ", leitura pode ter vindo do cache"
                rc, ms = timed("dd if=%s of=/dev/null bs=1M" % q)
            r = rate(a.bench_mb, ms)
            self.bench("dir_seq_write_MBs", "%s (%s)" % (w, mode))
            self.bench("dir_seq_read_MBs", r)
            for d in self.bdisks:
                # leitura muito acima da gravação direta = arquivo recém-gravado lido do cache do host
                caps.setdefault(d, ["", "", "bench"])[0] = w if float(r) > 2.5 * float(w) else fmax(w, r)
            if fio:
                step("disco: IOPS de leitura aleatória (fio, 8 s)")
                iops = self.fio_iops("--filename=%s --rw=randread" % q, 7)
                self.bench("dir_rand_read_4k_iops", iops or "NA")
                for d in self.bdisks:
                    if iops:
                        caps.setdefault(d, ["", "", "bench"])[1] = iops
                step("disco: IOPS de gravação aleatória (fio, 8 s)")
                iops = self.fio_iops("--filename=%s --rw=randwrite" % q, 48)
                self.bench("dir_rand_write_4k_iops", iops or "NA")
            try:
                os.remove(bf)
            except OSError:
                pass
            self.bench_file = ""
        else:
            self.bench("dir_seq", "pulado: pouco espaço livre em " + a.bench_dir)

        # Como root: leitura direta (somente leitura, seguro) de cada disco físico
        if os.geteuid() == 0:
            for d in self.disks:
                step("disco %s: leitura direta de %d MB (pode demorar se o disco estiver ocupado)" % (d, a.bench_mb))
                # trecho aleatório: reler sempre o início do disco devolve o que o host já tem em cache
                try:
                    size_mb = int(read_file("%s/block/%s/size" % (SYS, d)) or 0) * 512 // 1048576
                except ValueError:
                    size_mb = 0
                skip = random.randint(0, size_mb - a.bench_mb) if size_mb > 2 * a.bench_mb else 0
                mb = min(a.bench_mb, size_mb) if size_mb > 0 else a.bench_mb     # disco menor que o teste
                rc, ms = timed("dd if=/dev/%s of=/dev/null bs=1M count=%d skip=%d iflag=direct" % (d, mb, skip))
                if rc == 0 and mb > 0:
                    r = rate(mb, ms)
                    self.bench("disk.%s.seq_read_MBs" % d, r)
                    c = caps.setdefault(d, ["", "", "bench"])
                    if not c[0]:                  # o teste no diretório (grava+lê) é mais confiável
                        c[0] = r
                    c[2] = "bench"
                if fio:
                    step("disco %s: IOPS de leitura aleatória (fio, 8 s)" % d)
                    iops = self.fio_iops("--filename=/dev/%s --readonly --rw=randread" % d, 7)
                    self.bench("disk.%s.rand_read_4k_iops" % d, iops or "NA")
                    if iops and int(iops) > 0:
                        # no disco inteiro o cache do host quase não ajuda: este é o IOPS de referência
                        c = caps.setdefault(d, ["", "", "bench"])
                        c[1] = iops
        else:
            self.bench("note", "rode como root (sudo) para medir a capacidade de cada disco")
        if not fio:
            self.bench("note", "instale o fio para medir capacidade de IOPS (ex.: apt/yum install fio)")
        self.bench("note", "medido com a máquina em uso; carga existente reduz os valores")
        for d, (bw, iop, src) in caps.items():
            self.caps[d] = (bw or "NA", iop or "NA", src)

    @staticmethod
    def fio_iops(args, field):
        _, out = run("fio --name=t %s --bs=4k --iodepth=32 --direct=1 --ioengine=libaio --runtime=8"
                     " --time_based --minimal" % args, capture=True)
        try:
            return "%d" % float(out.splitlines()[0].split(";")[field])
        except (IndexError, ValueError):
            return ""

    def load_caps(self):
        """Reaproveita as capacidades da última execução (--no-bench)."""
        try:
            with open(self.log, errors="replace") as f:
                for line in f:
                    if line.startswith("CAP "):
                        kv = dict(t.split("=", 1) for t in line.split()[1:] if "=" in t)
                        if "disk" in kv:
                            self.caps[kv["disk"]] = (kv.get("bw_MBs", "NA"), kv.get("iops", "NA"), "previous")
        except OSError:
            pass

    # ---- laço de coleta ----
    def next_boundary(self):
        """Próximo fim de janela, alinhado ao relógio (:00, :30... ou :00, :05...).
        Como as viradas de horário caem em múltiplos das duas durações, nenhuma
        janela atravessa a troca."""
        now = time.time()
        h = time.localtime(now).tm_hour
        iv = self.a.biz_interval if self.a.biz_start <= h < self.a.biz_end else self.a.interval
        return (int(now) // iv + 1) * iv

    def loop(self):
        """Amostra a cada SAMPLE s. A 1ª janela é curta (first_samples: ~FIRST_WINDOW s) para a central
        receber dado logo depois da partida; as seguintes fecham nos limites alinhados ao relógio (a 2ª
        vai do fim da curta até o próximo limite). Sem sobreposição nem buraco: cada amostra entra em
        exatamente uma janela e o ts (fim) de janelas seguidas difere de pelo menos SAMPLE s."""
        a = self.a
        src = self.src
        prev = src.snap(self.disks)
        nxt = time.monotonic()
        first_n, next_flush = first_samples(a.sample), None
        while True:
            nxt += a.sample
            now = time.monotonic()
            if nxt < now - a.sample:          # máquina suspensa / atraso grande: realinha
                nxt = now + a.sample
            if self.stop_ev.wait(max(0.0, nxt - now)):
                break
            if self.stop_file and os.path.exists(self.stop_file):
                self.say("Pedido de parada (%s): encerrando." % os.path.basename(self.stop_file))
                break
            try:
                cur = src.snap(self.disks)
                s, x = src.sample(prev, cur, self.disks)
                prev = cur
                self.samples.append(s)
                self.publish(s, x)
                if self.verbose:
                    self.say(src.line(s, self.disks, self.ncpu))
                if (len(self.samples) >= first_n) if next_flush is None else (time.time() >= next_flush):
                    self.flush(first=next_flush is None)
                    next_flush = self.next_boundary()
            except Exception as e:            # não derruba a coleta por uma amostra ruim
                self.error = "%s: %s" % (type(e).__name__, e)

    def publish(self, s, x):
        self.live = {"ts": time.time(), "host": self.host, "sample": self.a.sample, "ncpu": self.ncpu,
                     "disks": self.disks, "s": s, "x": x}
        if self.live_file is None:
            return
        tmp = self.live_file + ".tmp"
        try:
            with open(tmp, "w") as f:
                json.dump(self.live, f)
            os.replace(tmp, self.live_file)
        except OSError:
            pass

    def flush(self, first=False):
        """Grava a janela (linha DATA). first = 1ª janela da sessão: o SyncManager envia já."""
        if not self.samples:
            return
        line, txt = aggregate(self.samples, self.disks, self.capv, self.ncpu, self.a.cpu_hi, self.a.mem_hi,
                              self.a.disk_hi, iso_now(), self.src.loadavg(), fs=self.src.filesystems())
        self.write(line)
        if self.verbose:
            self.say(txt)
        self.samples = []
        if self.sync is not None:                     # só sinaliza o nível da janela (sem rede)
            row = window_row(data_kv(line), all_keys(self.disks), self.disks, self.a.sample, self.ncpu)
            sp = row["lv_space"]
            self.sync.on_window(perf_level(row), None if sp != sp else int(sp), first=first)
        if time.time() - self.compacted_at > COMPACT_EVERY:
            self.start_compact()

    def start(self):
        self.thread = threading.Thread(target=self.loop, name="coleta", daemon=True)
        self.thread.start()

    def stop(self, final=True):
        """Encerra: grava a janela parcial e o EVENT stop (uma vez só). final=False (reinício da
        autoatualização): não publica na nuvem que o monitor parou, para o Central não alertar à toa."""
        if self.stopped:
            return
        self.stopped = True
        self.stop_ev.set()
        if self.thread:
            self.thread.join(10)
        if self.compact_thread is not None:
            self.compact_thread.join(10)            # a retenção vê stop_ev e desiste (arquivo intacto)
        if self.bench_file:
            try:
                os.remove(self.bench_file)
            except OSError:
                pass
        self.say("\nEncerrando... gravando janela parcial.")
        try:
            self.flush()
            self.write("EVENT ts=%s type=stop" % iso_now())
        except (OSError, ValueError):
            pass
        try:
            os.remove(self.live_file)
        except (OSError, TypeError):                # TypeError: sem arquivo ao vivo (Windows)
            pass
        if self.updater is not None:
            self.updater.stop()
        if self.sysev is not None:
            self.sysev.stop()
        if self.sql is not None:
            self.sql.stop()
        if self.db is not None:
            self.db.stop()
        if self.sync is not None:
            if final:
                self.say("Publicando na nuvem que o monitor parou...")
            self.sync.stop(final=final)
        FB_HTTP.close_all()                         # conexões persistentes ao Firebase (o reinício faz execv)
        self.say("Relatório: " + self.log)

    def start_compact(self):
        """Dispara a retenção local numa thread própria ('retenção'): reescrever o relatório com ritmo
        controlado leva dezenas de segundos e a coleta não pode parar enquanto isso."""
        if self.compact_thread is not None and self.compact_thread.is_alive():
            return False
        self.compacted_at = time.time()
        self.compact_thread = threading.Thread(target=self.compact, name="retenção", daemon=True)
        self.compact_thread.start()
        return True

    def postpone_compact(self, why):
        self.compacted_at = time.time() - COMPACT_EVERY + COMPACT_RETRY      # tenta de novo em COMPACT_RETRY
        self.compact_state = why

    def held_days(self, cut, final):
        """Dias antigos (< cut) presentes no relatório e ainda não confirmados na nuvem (leitura só do
        começo do arquivo, com ritmo controlado e sem poluir o cache)."""
        held, pacer = set(), Pacer(stop=self.stop_ev)
        with open(self.log, "rb") as f:
            for raw in f:
                pacer.add(len(raw))
                if raw.startswith((b"DATA ts=", b"EVENT ts=")):
                    day = raw.split(b"ts=", 1)[1][:10].decode()
                    if day >= cut:
                        break
                    if day not in final:
                        held.add(day)
            drop_cache(f)
        return held

    def compact(self):
        """Retenção local: mantém retention_local_days dias de medições no relatório.

        Só reescreve quando o dia mais antigo passou de retention_local_days + retention_slack_days
        (com a folga padrão de 7 dias: uma reescrita por semana, não uma por dia), e então volta para
        retention_local_days. Feita para não competir com o servidor:
        - roda na thread 'retenção' (prioridade baixa herdada), nunca na da coleta;
        - espera o disco folgar (PSI io > PSI_BUSY adia COMPACT_RETRY), a não ser que o excesso já
          passe do dobro da folga (o arquivo não cresce sem limite num storage sempre ocupado);
        - lê e grava no máximo DISK_RATE B/s, com fdatasync a cada COMPACT_SYNC_BYTES (o kernel nunca
          acumula dezenas de MB sujos para gravar de uma vez) e tira do cache o que já copiou;
        - troca atômica (os.replace); só a cópia do finalzinho (linhas gravadas durante a cópia), a troca
          e a reabertura acontecem com a trava de escrita (self.log_lock).
        Dias ainda não confirmados na nuvem (histórico configurado) nunca são removidos: a retenção fica
        adiada e o painel avisa."""
        self.compacted_at = time.time()
        cfg = self.ident.sync_cfg() if self.ident else dict(SYNC_DEFAULTS)
        keep, slack = cfg["retention_local_days"], cfg["retention_slack_days"]
        day_of = lambda d: time.strftime("%Y-%m-%d", time.localtime(time.time() - d * 86400))
        cut = day_of(keep)
        first = None
        with open(self.log, "rb") as f:
            for raw in f:
                if raw.startswith(b"DATA ts="):
                    first = raw[8:18].decode()
                    break
        if first is None or first >= day_of(keep + slack):
            self.compact_state = "nada a remover"
            return
        forced = first < day_of(keep + 2 * slack)
        psi = io_pressure()
        if psi is not None and psi > PSI_BUSY and not forced:
            return self.postpone_compact("adiada: disco ocupado (PSI io %.1f%%)" % psi)
        repo = bool(self.ident and self.ident.repo)
        final = set()
        if repo:                                      # não apaga o que ainda não está confirmado na nuvem
            days = CloudSync(self.log, self.ident, self.host).load_state()["days"]
            final = {d for d, v in days.items() if isinstance(v, dict) and v.get("final")}
            if not any(d < cut for d in final):       # nada removível: só conta os dias retidos (sem reescrever)
                held = self.held_days(cut, final)
                self.retention_note = ("retenção adiada: %d dia(s) antigo(s) ainda não confirmado(s) na nuvem"
                                       % len(held)) if held else ""
                self.compact_state = "nada removível"
                return
        tmp = self.log + ".compactando"
        held = set()
        S = {"head": True, "ctx": [], "bench": None, "keeping": False}

        def feed(raw, dst):
            if S["keeping"]:
                dst.write(raw)
                if repo and raw.startswith((b"DATA ts=", b"EVENT ts=")):
                    day = raw.split(b"ts=", 1)[1][:10].decode()
                    if day < cut and day not in final:
                        held.add(day)
                return
            if S["head"] and (raw.startswith(b"#") or not raw.strip()):
                dst.write(raw)                        # legenda do arquivo
                return
            S["head"] = False
            ctx, bench = S["ctx"], S["bench"]
            if raw.startswith(b"SESSION "):
                S["ctx"] = [raw]
            elif raw.startswith((b"HW ", b"BENCH ", b"CAP ")):
                ctx.append(raw)
                if raw.startswith(b"BENCH "):
                    when = ctx[0].split(b"start=", 1)[1].split(b" ", 1)[0] if ctx[0].startswith(b"SESSION ") else b""
                    if bench is None or bench[0] != when:
                        S["bench"] = bench = (when, [])
                    bench[1].append(raw)
            elif raw.startswith((b"DATA ts=", b"EVENT ts=")):
                day = raw.split(b"ts=", 1)[1][:10].decode()
                if day < cut and (not repo or day in final):
                    return                            # dia antigo e já seguro: sai do relatório local
                if day < cut:
                    held.add(day)
                S["keeping"] = True
                if bench and not any(c.startswith(b"BENCH ") for c in ctx):
                    dst.write(b"# bench_de=" + bench[0] + b"\n")
                    dst.writelines(bench[1])
                dst.writelines(ctx)
                dst.write(raw)

        try:
            size0 = os.path.getsize(self.log)        # o que existe agora; o resto é copiado com a trava
            pacer, done, synced = Pacer(stop=self.stop_ev), 0, 0
            with open(self.log, "rb") as src, open(tmp, "wb") as dst:
                while done < size0:
                    raw = src.readline()
                    if not raw:
                        break
                    done += len(raw)
                    feed(raw, dst)
                    pacer.add(len(raw))
                    if done - synced >= COMPACT_SYNC_BYTES:
                        synced = done
                        dst.flush()
                        datasync(dst)    # aos poucos: nada de dezenas de MB sujos de uma vez
                        drop_cache(dst)
                        drop_cache(src, done)
                        psi = io_pressure()
                        if psi is not None and psi > PSI_BUSY and not forced:
                            raise CompactAbort("adiada: disco ocupado durante a cópia (PSI io %.1f%%)" % psi)
                    if self.stop_ev.is_set():
                        raise CompactAbort("interrompida: monitor parando")
                dst.flush()
                datasync(dst)
                with self.log_lock:                   # coleta espera só o finalzinho + troca
                    self.logf.flush()
                    src.seek(done)
                    for raw in src.read().splitlines(True):
                        feed(raw, dst)
                    if not S["keeping"]:              # nada a manter além do contexto da sessão atual
                        dst.writelines(S["ctx"])
                    dst.flush()
                    if IS_WINDOWS:
                        # arquivo aberto não pode ser trocado no Windows: fecha tudo, troca e reabre (a trava
                        # do coletor é o <relatório>.lock, que não muda). Outro leitor com o relatório aberto
                        # (envio à nuvem) faz a troca falhar: OSError abaixo, tenta de novo na próxima vez.
                        os.fsync(dst.fileno())
                        dst.close()
                        src.close()
                        self.logf.close()
                        try:
                            os.replace(tmp, self.log)
                        finally:
                            self.logf = open(self.log, "a")
                    else:
                        os.replace(tmp, self.log)
                        old, self.logf = self.logf, open(self.log, "a")
                        if fcntl is not None:
                            fcntl.flock(self.logf, fcntl.LOCK_EX | fcntl.LOCK_NB)
                        old.close()
                        drop_cache(src)
                if not dst.closed:
                    os.fsync(dst.fileno())            # só o finalzinho ainda não sincronizado
                    n = dst.tell()
                    drop_cache(dst, max(0, n - (2 << 20)))   # o fim (últimas janelas) fica no cache para o painel
        except CompactAbort as e:
            with contextlib.suppress(OSError):
                os.remove(tmp)
            return self.postpone_compact(str(e))
        except OSError as e:
            self.error = "retenção local: %s" % e
            try:
                os.remove(tmp)
            except OSError:
                pass
            return
        self.compact_state = "ok"
        self.retention_note = ("retenção adiada: %d dia(s) antigo(s) ainda não confirmado(s) na nuvem" % len(held)) if held else ""


# --------------------------------------------------------------------------
# Histórico: leitura incremental do relatório
# --------------------------------------------------------------------------
BASE_KEYS = ("n cpu_avg cpu_p95 cpu_max cpu_hi hot_avg hot_max iow_avg st_avg st_max rq_avg rq_max rq_over "
             "load1 load5 load15 psi_cpu psi_cpu_max mem_avg mem_max mem_hi swap swin swout majf "
             "psi_mem psi_mem_full psi_mem_max psi_io psi_io_full psi_io_max").split()
DISK_KEYS = ("util_avg util_p95 util_max util_hi rMBs wMBs MBs_max bw_pct_max iops_avg iops_max iops_pct_max "
             "await qd_avg qd_max riops wiops r_await w_await").split()
# Colunas guardadas para os gráficos (o resto da linha DATA só é usado na última janela)
STORE_BASE = ("n cpu_avg cpu_max cpu_hi_s rq_avg rq_max rq_over rq_over_s psi_cpu psi_cpu_max st_avg st_max hot_avg "
              "load1 mem_avg mem_max mem_hi_s swap swio majf psi_mem psi_mem_full psi_mem_max psi_io psi_io_full "
              "psi_io_max state lv_cpu lv_mem lv_disk lv_space fs_used_max fs_worst_used fs_worst_free fs_worst_total "
              "fs_worst_id").split()
STORE_DISK = ("util_avg util_max util_hi_s MBs_avg MBs_max iops_avg iops_max await qd_avg qd_max bw_pct_max "
              "iops_pct_max riops wiops r_await w_await").split()
# Campos que a avaliação de condição precisa
LEVEL_BASE = ("n cpu_avg cpu_p95 cpu_max cpu_hi rq_avg rq_max rq_over psi_cpu psi_cpu_max st_avg st_max hot_avg load1 mem_avg mem_max "
              "mem_hi swap swin swout majf psi_mem psi_mem_full psi_mem_max psi_io psi_io_full psi_io_max").split()
LEVEL_DISK = "util_avg util_max util_hi rMBs wMBs MBs_max iops_avg iops_max await qd_avg qd_max bw_pct_max iops_pct_max".split()
RES_KEYS = ("cpu", "mem", "disk", "space")     # recursos avaliados (space = ocupação dos filesystems, v2.3)
RAW_KEEP = 8 * 86400          # resolução total dos últimos 8 dias; antes disso, só o resumo por hora
BUCKET = 3600


def diagnose(r, ncpu, disks, msgs=False):
    """Estado de cada recurso numa janela gravada.

    Devolve {"cpu": (nível, frase), "mem": (nível, frase), "disk": (nível, frase, disco),
    "space": (nível, frase, ponto de montagem)} com
    nível 0 normal, 1 atenção, 2 crítico ou None (sem dados). CRÍTICO sempre exige evidência de
    contenção (fila, PSI, latência ou swap); uso alto sozinho chega no máximo a ATENÇÃO. Espaço
    (r["_fs"], lista de filesystems da janela) é a exceção: disco cheio para o servidor mesmo
    sem fila, então >= 95% ocupado (ou < 1 GB livre) já é CRÍTICO.
    Critérios repetidos na ajuda do painel (tecla ?) e no README."""
    def v(k):
        x = r.get(k)
        return None if x is None or x != x else x

    def say(fmt, *a):
        return (fmt % a) if msgs else ""

    n = v("n") or 1
    out = {}
    # ---- CPU: ocupada (uso alto) x pressionada (fila / PSI) ----
    cpu = v("cpu_avg")
    if cpu is None:
        out["cpu"] = (None, say("Sem dados de CPU."))
    else:
        pc, rqa, rqo = v("psi_cpu"), v("rq_avg") or 0, v("rq_over") or 0
        st, hot = v("st_avg") or 0, v("hot_avg") or 0
        if rqa > ncpu:
            c = (2, say("Processos aguardando CPU (fila média %.1f para %d vCPUs). Possível falta de capacidade.", rqa, ncpu))
        elif pc is not None and pc >= 10:
            c = (2, say("Processos esperando CPU %.0f%% do tempo. Possível falta de capacidade.", pc))
        elif st >= 20:
            c = (2, say("O hypervisor está retendo CPU desta VM (%.0f%%): o problema é no host, não na VM.", st))
        elif (pc is not None and pc >= 5) or rqo >= max(1.0, n / 4.0):
            c = (1, say("Fila de processamento começando a se formar."))
        elif st >= 5:
            c = (1, say("Possível disputa por recursos no hypervisor (%.0f%% da CPU retida pelo host).", st))
        elif cpu >= 80:
            c = (1, say("CPU trabalhando intensamente, mas sem fila relevante."))
        elif hot >= 90 and ncpu > 1 and cpu <= max(25.0, 150.0 / ncpu):
            c = (1, say("Um núcleo sempre ocupado: processo limitado a 1 CPU (mais vCPUs não resolvem)."))
        elif pc is None and cpu >= 50:
            c = (0, say("Trabalhando, sem fila (kernel sem PSI: avaliação só pela fila)."))
        else:
            c = (0, say("Trabalhando, sem fila de processamento." if cpu >= 50 else "Sem fila de processamento."))
        out["cpu"] = c
    # ---- Memória: falta real = PSI / paginação; cache não conta ----
    mem = v("mem_avg")
    if mem is None:
        out["mem"] = (None, say("Sem dados de memória."))
    else:
        pm, pmf = v("psi_mem"), v("psi_mem_full")
        sw = v("swio")
        if sw is None:
            sw = (v("swin") or 0) + (v("swout") or 0)
        if (pmf or 0) >= 5 or (pm or 0) >= 10:
            c = (2, say("Falta de memória: processos travados esperando RAM %.0f%% do tempo.", max(pm or 0, pmf or 0)))
        elif sw >= 50 and mem >= 90:
            c = (2, say("Memória disponível muito baixa, com paginação intensa (%.0f páginas/s).", sw))
        elif (pm or 0) >= 2 or sw >= 10:
            c = (1, say("Pressão de memória inicial: o sistema está recorrendo ao swap."))
        elif mem >= 90:
            c = (1, say("Pouca memória disponível, ainda sem pressão de paginação."))
        else:
            c = (0, say("Memória suficiente (o cache do Linux não conta como uso)."))
        out["mem"] = c
    # ---- Disco: ocupado (busy) não é capacidade; gargalo = espera / fila / latência ----
    pio, pif = v("psi_io"), v("psi_io_full")
    best = (-1, -1.0, None, "")
    for d in disks:
        u = v(d + ".util_avg")
        if u is None:
            continue
        aw, qd = v(d + ".await") or 0, v(d + ".qd_avg") or 0
        cap = max(v(d + ".bw_pct_max") or 0, v(d + ".iops_pct_max") or 0)
        if u >= 90 and (qd >= 2 or aw >= 50):
            c = (2, say("Disco %s com operações acumuladas e latência elevada (%.0f ms por operação).", d, aw))
        elif aw >= 20:
            c = (1, say("Latência elevada no disco %s (%.0f ms por operação).", d, aw))
        elif cap >= 90:
            c = (1, say("Disco %s perto da capacidade medida no benchmark.", d))
        elif u >= 90:
            c = (1, say("Disco %s muito ocupado, mas sem evidência de gargalo%s.", d,
                        "" if pio is not None else " (sem PSI: inconclusivo)"))
        else:
            c = (0, say("Disco ativo, sem espera relevante." if u >= 60 else "Sem espera relevante por disco."))
        if (c[0], u) > best[:2]:
            best = (c[0], u, d, c[1])
    lv, _, dk, msg = best
    if dk is None and pio is None:
        out["disk"] = (None, say("Sem dados de disco."), None)
    else:
        if (pif or 0) >= 20 or (pio or 0) >= 30:
            lv, msg = 2, say("Processos parados esperando o disco %.0f%% do tempo. Provável gargalo de armazenamento.", pio or pif)
        elif (pio or 0) >= 10 and lv < 2:
            lv, msg = 1, say("Espera por disco moderada (processos aguardando I/O %.0f%% do tempo).", pio)
        elif lv < 0:
            lv, msg = 0, say("Sem espera relevante por disco.")
        out["disk"] = (lv, msg, dk)
    # ---- Espaço: o pior filesystem (% ocupado ou pouco espaço livre) ----
    lv, f = space_worst(r.get("_fs"))
    if f is None:
        out["space"] = (None, say("Sem dados de espaço em disco."), None)
    else:
        m, used, free = f["mount"], int(f["used_pct"]), fmt_bytes(f["free_bytes"]) if msgs else ""
        if lv == 2:
            msg = say("Disco quase cheio em %s: %d%% ocupado, %s livres.", m, used, free)
        elif lv == 1:
            msg = say("Pouco espaço livre em %s: %d%% ocupado, %s livres.", m, used, free)
        else:
            msg = say("Espaço livre suficiente (o mais ocupado é %s, com %d%%).", m, used)
        out["space"] = (lv, msg, m)
    return out


def data_kv(line):
    """'DATA k=v ...' -> dict de strings."""
    return dict(t.split("=", 1) for t in line[5:].split() if "=" in t)


def window_row(kv, keys, disks, sample, ncpu):
    """Campos numéricos de uma janela + derivados + nível de cada recurso (via diagnose).
    Usado pelo painel, pelo status ao vivo e pelo gatilho de alerta: uma classificação só."""
    row = {}
    for k in keys:
        v = kv.get(k)
        if v is not None and v != "NA":
            row[k] = float(v)
    g = row.get
    row["swio"] = (g("swin") or 0) + (g("swout") or 0)
    for d in disks:
        if d + ".rMBs" in row:
            row[d + ".MBs_avg"] = row[d + ".rMBs"] + g(d + ".wMBs", 0)
        for k in ("cpu_hi", "rq_over", "mem_hi", d + ".util_hi"):
            if k in row and k + "_s" not in row:
                row[k + "_s"] = row[k] * sample      # segundos no teto
    fs = fs_parse(kv)
    if fs is not None:                               # v2.3+: ocupação dos filesystems
        row["_fs"] = fs
        if fs:
            row["fs_used_max"] = max(f["used_pct"] for f in fs)
            w = row["_fs_worst"] = space_worst(fs)[1]
            row["fs_worst_used"], row["fs_worst_free"], row["fs_worst_total"] = (
                w["used_pct"], float(w["free_bytes"]), float(w["total_bytes"]))
    dg = diagnose(row, ncpu, disks)
    lvs = [dg[k][0] for k in RES_KEYS]
    row["lv_cpu"], row["lv_mem"], row["lv_disk"], row["lv_space"] = (NAN if x is None else x for x in lvs)
    known = [x for x in lvs if x is not None]
    row["state"] = max(known) if known else NAN
    return row


def perf_level(row):
    """Pior nível só de CPU, memória e disco (desempenho). Ocupação de espaço muda devagar: não
    acelera o envio (interval_alert), só dispara envio quando o nível dela muda."""
    known = [row[k] for k in ("lv_cpu", "lv_mem", "lv_disk") if row.get(k) is not None and row[k] == row[k]]
    return int(max(known)) if known else None


def all_keys(disks):
    return BASE_KEYS + [d + "." + k for d in disks for k in DISK_KEYS]


class Store:
    """Colunas numéricas (array de double; NaN = sem valor) indexadas por tempo."""

    def __init__(self):
        self.ts = array("d")
        self.win = array("d")
        self.cols = {}

    def __len__(self):
        return len(self.ts)

    def col(self, k):
        c = self.cols.get(k)
        if c is None:
            c = self.cols[k] = array("d", [NAN]) * len(self.ts)
        return c

    def add(self, ts, win, row):
        self.ts.append(ts)
        self.win.append(win)
        g = row.get
        for k, c in self.cols.items():
            c.append(g(k, NAN))

    def trim_before(self, t):
        i = bisect.bisect_left(self.ts, t)
        if i > 0:
            self.ts = self.ts[i:]
            self.win = self.win[i:]
            for k in list(self.cols):
                self.cols[k] = self.cols[k][i:]


class Rollup:
    """Resumo por hora de todo o histórico: média ponderada, máximo e soma."""

    def __init__(self):
        self.ts = array("d")        # início da hora
        self.cols = {}              # k -> (soma ponderada, peso, máximo, soma simples)

    def col(self, k):
        c = self.cols.get(k)
        if c is None:
            n = len(self.ts)
            c = self.cols[k] = (array("d", [0.0]) * n, array("d", [0.0]) * n, array("d", [NAN]) * n, array("d", [0.0]) * n)
        return c

    def add(self, ts, win, row):
        b = (ts - 1) // BUCKET * BUCKET
        if not self.ts or b > self.ts[-1]:
            self.ts.append(b)
            for c in self.cols.values():
                c[0].append(0.0); c[1].append(0.0); c[2].append(NAN); c[3].append(0.0)
        elif b < self.ts[-1]:
            return                   # fora de ordem (relógio voltou): fica só no detalhe
        i = len(self.ts) - 1
        g = row.get
        for k, (ws, w, mx, sm) in self.cols.items():
            v = g(k)
            if v is None or v != v:
                continue
            ws[i] += v * win; w[i] += win; sm[i] += v
            if not (mx[i] >= v):
                mx[i] = v


class History:
    def __init__(self, path):
        self.path = path
        self.reset()

    def reset(self):
        self.pos = 0
        self.ino = None
        self.rest = b""
        self.raw = Store()
        self.roll = Rollup()
        self.session = {}
        self.hw = {}
        self.bench = []
        self.last_bench = {}         # último benchmark completo do relatório (chave -> valor)
        self.last_bench_when = None  # início da sessão em que foi medido
        self.last_bench_hw = {}      # hardware dessa sessão
        self.bench_session = None
        self.caps = {}
        self.disks = []
        self.disk_info = {}
        self.ncpu = 1
        self.sample = 5
        self.last = None             # última linha DATA (dict)
        self.first_ts = None
        self.last_ts = None
        self.bad = 0
        self.version = 0
        self.size = 0
        self.stopped_at = None       # EVENT stop depois da última DATA
        self.rows = 0
        self.export_company = ""
        self.bench_from = None
        self.tz_offset = None        # fuso do servidor (dos horários ISO do relatório)
        self.cutoff = None           # janelas antes disso vão só para o resumo por hora
        self.has_space = False       # o relatório tem ocupação de filesystems (v2.3+)
        self.fs_names = []           # pontos de montagem (coluna fs_worst_id = índice aqui)
        self.fs_ids = {}
        self.last_raw = None         # última linha DATA lida (bytes) e as linhas depois dela: permitem
        self.after = []              # continuar no arquivo reescrito pela retenção sem reler tudo
        self.set_disks([])

    def set_disks(self, disks):
        self.disks = list(disks)
        self.want_all = all_keys(self.disks)
        self.want_old = LEVEL_BASE + [d + "." + k for d in self.disks for k in LEVEL_DISK]
        for k in STORE_BASE + [d + "." + k for d in self.disks for k in STORE_DISK]:
            self.raw.col(k)
            self.roll.col(k)

    def tail_ts(self):
        """Data da última janela do arquivo (lê só o fim), para não guardar detalhe antigo à toa."""
        try:
            with open(self.path, "rb") as f:
                f.seek(max(0, os.path.getsize(self.path) - (1 << 20)))
                tail = f.read().decode("utf-8", "replace")
        except OSError:
            return None
        i = tail.rfind("\nDATA ts=")
        while i >= 0:
            try:
                return datetime.datetime.fromisoformat(tail[i + 9:].split(None, 1)[0]).timestamp()
            except ValueError:
                i = tail.rfind("\nDATA ts=", 0, i)
        return None

    def poll(self, max_bytes=8 << 20):
        """Lê o que foi acrescentado ao arquivo. Devolve True se ainda falta ler."""
        try:
            st = os.stat(self.path)
        except OSError:
            return False
        if self.ino is not None and (st.st_ino != self.ino or st.st_size < self.pos):
            pos = self.resume(st) if st.st_ino != self.ino else None
            if pos is None:
                self.reset()         # arquivo trocado ou truncado: relê do zero
            else:
                self.pos = pos       # retenção local: mesmo final, início cortado; segue de onde estava
        if self.ino is None:
            t = self.tail_ts()
            self.cutoff = t - RAW_KEEP if t is not None else None
        self.ino = st.st_ino
        self.size = st.st_size
        if st.st_size == self.pos:
            return False
        with open(self.path, "rb") as f:
            f.seek(self.pos)
            data = f.read(max_bytes)
        self.pos += len(data)
        data = self.rest + data
        lines = data.split(b"\n")
        self.rest = lines.pop()      # linha incompleta (ainda sendo escrita) fica para depois
        for raw in lines:
            if raw.startswith(b"DATA "):
                self.last_raw, self.after = raw, []
            elif self.after is not None:
                self.after.append(raw)
                if len(self.after) > 2000:
                    self.after = None    # muitas linhas sem DATA: não dá para achar o ponto com segurança
            try:
                self.parse(raw.decode("utf-8", "replace"))
            except Exception:
                self.bad += 1
        if self.last_ts is not None and self.raw.ts and self.raw.ts[0] < self.last_ts - RAW_KEEP - 86400:
            self.raw.trim_before(self.last_ts - RAW_KEEP)
        self.version += 1
        return self.pos < st.st_size

    def resume(self, st):
        """Posição no arquivo novo logo depois da última linha já lida, se ele for o mesmo relatório com o
        começo cortado pela retenção (a última DATA e as linhas seguintes aparecem iguais); senão None.
        Evita reler e reprocessar dezenas de MB a cada retenção (busca binária + um trecho do final)."""
        if self.rest or self.last_raw is None or self.after is None or self.last_ts is None:
            return None
        off = seek_ts(self.path, self.last_ts, st.st_size)
        try:
            with open(self.path, "rb") as f:
                f.seek(off)
                data = f.read(16 << 20)
        except OSError:
            return None
        key = self.last_raw + b"\n"
        i = 0 if data.startswith(key) else data.find(b"\n" + key) + 1
        if i <= 0 and not data.startswith(key):
            return None
        p = i + len(key)
        for raw in self.after:
            if not data.startswith(raw + b"\n", p):
                return None
            p += len(raw) + 1
        return off + p

    def parse(self, line):
        if line.startswith("DATA "):
            self.parse_data(line)
        elif line.startswith("SESSION "):
            kv = {}
            for t in shlex.split(line[8:]):
                k, _, v = t.partition("=")
                kv[k] = v
            self.session = kv
            self.hw = {}
            self.bench = []
            self.caps = {}
            self.set_disks(kv.get("disks", "").split())
            try:
                self.ncpu = int(kv.get("cpus", 1))
                self.sample = int(kv.get("sample", 5))
            except ValueError:
                pass
        elif line.startswith("BENCH "):
            k, _, v = line[6:].partition(":")
            self.bench.append((k.strip(), v.strip()))
            if self.bench_session is not self.session:      # 1ª linha de um benchmark novo
                self.bench_session = self.session
                self.last_bench = {}
                self.last_bench_when = self.bench_from or self.session.get("start")
                self.last_bench_hw = self.hw
                self.bench_from = None
            if k.strip() != "note":
                self.last_bench[k.strip()] = v.strip()
        elif line.startswith("HW "):
            k, _, v = line[3:].partition(":")
            k, v = k.strip(), v.strip()
            self.hw[k] = v
            if k.startswith("disk."):
                self.disk_info[k[5:]] = v
        elif line.startswith("CAP "):
            kv = dict(t.split("=", 1) for t in line.split()[1:] if "=" in t)
            self.caps[kv.get("disk", "?")] = kv
        elif line.startswith("EVENT ") and "type=stop" in line:
            self.stopped_at = self.last_ts
        elif line.startswith("# bench_de="):       # benchmark de uma sessão anterior (arquivo diário)
            self.bench_from = line[11:].strip()
            self.bench_session = None
        elif line.startswith("# empresa="):        # cabeçalho dos arquivos diários vindos da nuvem
            self.export_company = line[10:].split(" | ")[0].strip()
        elif line.strip() and not line.startswith("#"):
            self.bad += 1

    def parse_data(self, line):
        kv = data_kv(line)
        dt = datetime.datetime.fromisoformat(kv["ts"])
        ts = dt.timestamp()
        off = dt.utcoffset()
        if off is not None:
            self.tz_offset = off.total_seconds()
        win = float(kv["win"])
        if win <= 0:
            raise ValueError("DATA sem win")
        if not self.disks:          # relatório sem SESSION: descobre os discos pelos campos
            self.set_disks(sorted(k[:-9] for k in kv if k.endswith(".util_avg")))
        old = self.cutoff is not None and ts < self.cutoff
        row = window_row(kv, self.want_old if old else self.want_all, self.disks, self.sample, self.ncpu)
        if "_fs" in row:
            self.has_space = True
            w = row.get("_fs_worst")
            if w is not None:
                i = self.fs_ids.get(w["mount"])
                if i is None:
                    i = self.fs_ids[w["mount"]] = len(self.fs_names)
                    self.fs_names.append(w["mount"])
                row["fs_worst_id"] = float(i)
        if not old:
            self.raw.add(ts, win, row)
        self.roll.add(ts, win, row)
        self.rows += 1
        if self.first_ts is None or ts - win < self.first_ts:
            self.first_ts = ts - win
        self.last_ts = ts
        self.stopped_at = None
        row["_ts"], row["_win"], row["_flags"] = ts, win, kv.get("flags", "")
        self.last = row

    def expected_window(self, t):
        """Duração esperada da janela no horário t (para detectar dados atrasados)."""
        try:
            iv = int(self.session.get("interval", 300))
            biv = int(self.session.get("biz_interval", iv))
            a, b = (int(x) for x in self.session.get("biz_hours", "0-0").split("-"))
        except ValueError:
            return 300
        hour = (time.gmtime(t + self.tz_offset) if self.tz_offset is not None else time.localtime(t)).tm_hour
        return biv if a <= hour < b else iv


# --------------------------------------------------------------------------
# Identificação da instalação (empresa + id estável)
# --------------------------------------------------------------------------
CONFIG_FILE = "server_monitor.json"      # empresa, id da instalação, repositório (sem segredos)
TOKEN_FILE = "server_monitor.token"      # token do GitHub: permissão 600, nunca vai para relatório/nuvem
SYNC_DIR = ".server_monitor_sync"        # estado do envio e arquivos diários a enviar


def slug(s, maxlen=40):
    """Nome seguro para pasta/arquivo: sem acento, minúsculo, só [a-z0-9-]."""
    s = unicodedata.normalize("NFKD", s).encode("ascii", "ignore").decode()
    s = re.sub(r"[^A-Za-z0-9]+", "-", s).strip("-").lower()
    return s[:maxlen].strip("-") or "sem-nome"


def clean_name(v):
    """Empresa/nome do servidor: espaços colapsados, sem caracteres de controle/formatação, até NAME_MAX."""
    v = "".join(c for c in str(v) if unicodedata.category(c) not in ("Cc", "Cf"))
    return " ".join(v.split())[:NAME_MAX]


def write_private(path, text):
    """Grava atomicamente com permissão 600 (só o dono lê). O temporário tem nome imprevisível e é
    criado com O_EXCL (mkstemp): um link simbólico plantado no diretório não é seguido."""
    fd, tmp = tempfile.mkstemp(dir=os.path.dirname(os.path.abspath(path)), prefix=".tmp-",
                               suffix="-" + os.path.basename(path))
    try:
        if hasattr(os, "fchmod"):            # Windows: quem protege é a permissão da pasta (instalador)
            os.fchmod(fd, 0o600)
        with os.fdopen(fd, "w") as f:
            f.write(text)
        os.replace(tmp, path)
    except BaseException:
        with contextlib.suppress(OSError):
            os.unlink(tmp)
        raise


def state_ram_path(log):
    """Cópia de trabalho do estado do envio em RAM (/dev/shm), ao lado do arquivo da amostra ao vivo.
    None se não houver /dev/shm: aí o estado vai direto para o disco."""
    p = live_path(log)
    return p[:-5] + ".state.json" if p.startswith(SHM_DIR + os.sep) else None


def read_json(path):
    try:
        with open(path) as f:
            return json.load(f)
    except (OSError, ValueError):
        return None


def read_json_owned(path):
    """JSON de um diretório compartilhado (/dev/shm): só se for arquivo comum, do próprio usuário e
    sem link simbólico. Outro usuário da máquina não consegue plantar um estado falso."""
    if not path:
        return None
    try:
        fd = os.open(path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0))
    except OSError:
        return None
    st = os.fstat(fd)
    # Windows: sem dono/modo POSIX; o arquivo fica na pasta do programa (protegida pelo instalador)
    if not stat.S_ISREG(st.st_mode) or (hasattr(os, "getuid") and (st.st_uid != os.getuid() or st.st_mode & 0o077)):
        os.close(fd)
        return None
    with os.fdopen(fd) as f:
        try:
            return json.load(f)
        except ValueError:
            return None


def timezone_name():
    if IS_WINDOWS:                       # nome do fuso em inglês (Vista+), ex.: "E. South America Standard Time"
        return reg_value("SYSTEM\\CurrentControlSet\\Control\\TimeZoneInformation", "TimeZoneKeyName") or time.tzname[0]
    tz = read_file("/etc/timezone").strip()
    if not tz:
        try:
            tz = os.readlink("/etc/localtime").split("zoneinfo/")[-1]
        except OSError:
            tz = time.tzname[0]
    return tz


class Identity:
    """Configuração local da instalação, na pasta do relatório (server_monitor.json)."""

    def __init__(self, base):
        self.base = base
        self.path = os.path.join(base, CONFIG_FILE)
        self.notice = ""
        try:
            with open(self.path) as f:
                self.data = json.load(f)
        except (OSError, ValueError):
            self.data = {}

    company = property(lambda self: self.data.get("company", ""))
    name = property(lambda self: self.data.get("name", ""))      # nome amigável (ex.: "Sescom - Linux")
    install_id = property(lambda self: self.data.get("install_id", ""))
    repo = property(lambda self: self.data.get("cloud_repo", ""))

    def save(self):
        write_private(self.path, json.dumps(self.data, indent=2, ensure_ascii=False) + "\n")

    def update(self, section, key, value):
        """Grava um valor relendo o arquivo antes (outro processo, como --nome, pode tê-lo mudado)."""
        d = read_json(self.path)
        d = d if isinstance(d, dict) else dict(self.data)
        sec = d.get(section) if isinstance(d.get(section), dict) else {}
        sec[key] = value
        d[section] = sec
        self.data = d
        self.save()

    def sync_cfg(self):
        """Parâmetros de sincronização: os do arquivo de configuração sobre os padrões."""
        cfg = dict(SYNC_DEFAULTS)
        for k, v in (self.data.get("sync") or {}).items():
            if k in cfg and isinstance(v, type(cfg[k])):
                cfg[k] = v
        cfg["interval_alert"] = max(5, cfg["interval_alert"])
        cfg["interval_normal"] = max(30, cfg["interval_normal"])
        cfg["history_interval"] = max(600, cfg["history_interval"])      # limite de escrita do GitHub
        cfg["heartbeat_interval"] = max(15, cfg["heartbeat_interval"])
        cfg["offline_after"] = max(cfg["offline_after"], 2 * cfg["heartbeat_interval"])
        cfg["rollup_seconds"] = max(60, cfg["rollup_seconds"])
        cfg["update_interval"] = max(300, cfg["update_interval"])
        cfg["retention_slack_days"] = max(1, cfg["retention_slack_days"])
        cfg["state_disk_interval"] = max(60, cfg["state_disk_interval"])
        cfg["sys_events_interval"] = max(60, cfg["sys_events_interval"])
        cfg["sys_events_retention_days"] = max(1, cfg["sys_events_retention_days"])
        return cfg

    @property
    def company_id(self):
        """Id técnico e estável da empresa (o nome pode mudar sem perder o histórico)."""
        return self.data.get("company_id") or slug(self.company or "sem-empresa")

    def ensure_id(self):
        """Id estável (não muda com o hostname). Se a pasta foi copiada para outra máquina
        (machine-id diferente), gera um novo para não misturar dois servidores."""
        mid = machine_id()
        changed = False
        if not self.install_id:
            self.data["install_id"] = uuid.uuid4().hex
            self.data["created"] = iso_now()
            changed = True
        elif mid and self.data.get("machine_id") and self.data["machine_id"] != mid:
            self.data["previous_install_id"] = self.install_id
            self.data["install_id"] = uuid.uuid4().hex
            self.notice = "configuração copiada de outra máquina: gerado um novo id para este servidor"
            changed = True
        if mid and self.data.get("machine_id") != mid:
            self.data["machine_id"] = mid
            changed = True
        if changed:
            self.save()

    def set_company(self, name):
        self.data["company"] = clean_name(name)
        self.data.setdefault("company_id", slug(self.data["company"]))   # fixado no primeiro nome
        self.save()

    def set_name(self, name):
        """Nome amigável do servidor, mostrado no painel central no lugar do hostname. Vazio = não configurado."""
        self.data["name"] = clean_name(name)
        self.save()

    def rename(self, company=None, name=None):
        """Renome pedido pela central (v2.14): troca empresa e/ou nome relendo o arquivo antes (outro processo, como
        --nome, pode tê-lo mudado). O company_id NUNCA muda: sem ele gravado (instalações antigas), fixa o atual antes
        de trocar o nome da empresa. Devolve True se algo mudou (repetir o mesmo pedido não grava nada)."""
        d = read_json(self.path)
        d = d if isinstance(d, dict) else dict(self.data)
        self.data = d
        changed = False
        if company is not None and company != self.company:
            d.setdefault("company_id", slug(self.company or "sem-empresa"))
            d["company"] = company
            changed = True
        if name is not None and name != self.name:
            d["name"] = name
            changed = True
        if changed:
            self.save()
        return changed

    def default_name(self):
        """Sugestão de nome: "<empresa> - <hostname>" (só o hostname se não houver empresa)."""
        host = platform.node().split(".")[0] or "localhost"
        return " - ".join(x for x in (self.company, host) if x)

    def ask_name(self):
        """Pergunta o nome amigável; Enter aceita a sugestão. Sem entrada (EOF) não grava nada."""
        default = self.default_name()
        print("\nComo este servidor deve aparecer no painel central? (o hostname sozinho pode se repetir")
        print("entre clientes; Enter aceita a sugestão entre colchetes)\n")
        try:
            name = input('Nome deste servidor (ex.: "Sescom - Linux") [%s]: ' % default).strip()
        except EOFError:
            return
        self.set_name(name or default)
        print("Salvo em %s (para mudar depois: --nome \"Novo nome\")\n" % self.path)

    def ask_missing(self):
        """Pergunta o que faltar da identificação: empresa e nome amigável."""
        if not self.company:
            self.ask_company()
        if not self.name:
            self.ask_name()

    def ask_company(self):
        print("=" * 52)
        print("           CONFIGURAÇÃO DO SERVER MONITOR")
        print("=" * 52)
        print("\nQual é o nome da empresa deste servidor?\n")
        while True:
            try:
                name = input("Empresa: ").strip()
            except EOFError:
                return
            if name:
                self.set_company(name)
                print("Salvo em %s (para mudar depois: --empresa \"Novo nome\")\n" % self.path)
                return


def load_token(base):
    """Token do GitHub: arquivo ao lado do relatório, variável de ambiente ou login do gh."""
    t = read_file(os.path.join(base, TOKEN_FILE)).strip()
    if t:
        return t
    for k in ("USAGE_MONITOR_TOKEN", "GH_TOKEN", "GITHUB_TOKEN"):
        if os.environ.get(k):
            return os.environ[k].strip()
    if shutil.which("gh"):
        rc, out = run("gh auth token", capture=True)
        if rc == 0 and out.strip():
            return out.strip()
    return ""


# --------------------------------------------------------------------------
# GitHub (API REST, só biblioteca padrão)
# --------------------------------------------------------------------------
GITHUB_API = os.environ.get("USAGE_MONITOR_GITHUB_API", "https://api.github.com")          # sobrescrevíveis só
GITHUB_UPLOADS = os.environ.get("USAGE_MONITOR_GITHUB_UPLOADS", "https://uploads.github.com")  # para testes


class CloudError(Exception):
    retry_after = None           # segundos a esperar antes de tentar de novo (limite do servidor)
    code = 0
    denied = False


class _NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args, **kw):
        return None          # redirecionamentos tratados à mão (o destino não pode receber o token)


class GitHub:
    def __init__(self, repo, token, timeout=60):
        if not re.match(r"^[\w.-]+/[\w.-]+$", repo or ""):
            raise CloudError("repositório inválido: use dono/nome (ex.: cbalmeida/server_monitor_dados)")
        self.repo, self.token, self.timeout = repo, token, timeout
        self.opener = urllib.request.build_opener(_NoRedirect)

    def call(self, method, path, body=None, data=None, ctype=None, base=None, accept="application/vnd.github+json",
             allow=()):
        headers = {"Accept": accept, "User-Agent": "usage-monitor/" + VERSION, "X-GitHub-Api-Version": "2022-11-28"}
        if self.token:
            headers["Authorization"] = "Bearer " + self.token
        if body is not None:
            data, ctype = json.dumps(body).encode(), "application/json"
        if ctype:
            headers["Content-Type"] = ctype
        req = urllib.request.Request((base or GITHUB_API) + path, data=data, headers=headers, method=method)
        try:
            with self.opener.open(req, timeout=self.timeout) as r:
                raw, status, kind = r.read(), r.status, r.headers.get_content_type()
        except urllib.error.HTTPError as e:
            if e.code in (301, 302, 303, 307, 308):
                return e.code, e.headers.get("Location")
            if e.code in allow:
                return e.code, None
            try:
                msg = json.loads(e.read().decode("utf-8", "replace")).get("message", "")
            except (ValueError, AttributeError):
                msg = ""
            err = CloudError(github_error(e.code, msg, self.repo))
            err.code = e.code
            if e.code in (403, 429) and ("rate limit" in msg.lower() or e.headers.get("Retry-After")
                                         or e.headers.get("X-RateLimit-Remaining") == "0"):
                ra = e.headers.get("Retry-After")
                reset = e.headers.get("X-RateLimit-Reset")
                err.retry_after = max(60, int(ra) if ra and ra.isdigit() else
                                      (int(reset) - int(time.time()) if reset and reset.isdigit() else 60))
            raise err
        except (urllib.error.URLError, OSError) as e:
            raise CloudError("sem conexão com o GitHub (%s)" % getattr(e, "reason", e))
        if kind == "application/json" and raw:
            return status, json.loads(raw.decode("utf-8"))
        return status, raw

    def pages(self, path):
        out, page = [], 1
        while True:
            sep = "&" if "?" in path else "?"
            _, items = self.call("GET", "%s%sper_page=100&page=%d" % (path, sep, page))
            out += items or []
            if not items or len(items) < 100:
                return out
            page += 1

    R = property(lambda self: "/repos/" + self.repo)

    def repo_info(self):
        return self.call("GET", self.R)[1]

    def is_empty(self):
        return self.call("GET", self.R + "/commits?per_page=1", allow=(409,))[0] == 409

    def create_readme(self):
        text = "# Relatórios do usage_monitor\n\nArmazenamento privado: os relatórios ficam nas Releases deste repositório.\n"
        self.call("PUT", self.R + "/contents/README.md",
                  body={"message": "Repositório de relatórios do usage_monitor",
                        "content": base64.b64encode(text.encode()).decode()})

    def release_by_tag(self, tag):
        st, rel = self.call("GET", self.R + "/releases/tags/" + urllib.parse.quote(tag), allow=(404,))
        return rel if st == 200 else None

    def create_release(self, tag, name, body):
        return self.call("POST", self.R + "/releases", body={"tag_name": tag, "name": name, "body": body,
                                                             "draft": False, "prerelease": False})[1]

    def update_release(self, rid, name, body):
        self.call("PATCH", self.R + "/releases/%d" % rid, body={"name": name, "body": body})

    def releases(self):
        return self.pages(self.R + "/releases")

    def assets(self, rid):
        return self.pages(self.R + "/releases/%d/assets" % rid)

    def delete_asset(self, aid):
        self.call("DELETE", self.R + "/releases/assets/%d" % aid, allow=(404,))

    def upload_asset(self, rid, name, data):
        return self.call("POST", self.R + "/releases/%d/assets?name=%s" % (rid, urllib.parse.quote(name)),
                         data=data, ctype="application/gzip", base=GITHUB_UPLOADS)[1]

    def download_asset(self, aid):
        st, res = self.call("GET", self.R + "/releases/assets/%d" % aid, accept="application/octet-stream")
        if st in (301, 302, 303, 307, 308):    # link temporário assinado: sem o token
            req = urllib.request.Request(res, headers={"User-Agent": "usage-monitor/" + VERSION})
            try:
                with urllib.request.urlopen(req, timeout=self.timeout) as r:
                    return r.read()
            except (urllib.error.URLError, OSError) as e:
                raise CloudError("falha ao baixar arquivo (%s)" % getattr(e, "reason", e))
        return res


def github_error(code, msg, repo):
    if code == 401:
        return "token inválido ou expirado (gere outro e rode --cloud-setup)"
    if code == 403 and "rate limit" in msg.lower():
        return "limite de requisições do GitHub atingido; tente mais tarde"
    if code in (403, 404):
        return "sem acesso a %s (repositório inexistente ou token sem permissão Contents: Read and write)" % repo
    if code == 422 and "empty" in msg.lower():
        return "o repositório está vazio: rode --cloud-setup para criar o README inicial"
    return "GitHub respondeu %d%s" % (code, (": " + msg) if msg else "")


# --------------------------------------------------------------------------
# Envio dos relatórios para a nuvem (sob demanda)
# --------------------------------------------------------------------------
META_RE = re.compile(r"```json\s*(\{.*?\})\s*```", re.S)
DAY_RE = re.compile(r"(?:ts|start)=(\d{4}-\d\d-\d\d)")
LIVE_READ = 8 << 20              # bytes do relatório lidos por vez (1ª sincronização: memória limitada)


def bench_dict(lines):
    """Linhas 'BENCH chave : valor' -> {chave: valor} (sem as notas)."""
    out = {}
    for line in lines:
        k, sep, v = line[6:].partition(":")
        if sep and k.strip() != "note":
            out[k.strip()] = v.strip()
    return out


SYNC_DEFAULTS = {
    "auto": True,                # envio automático (só quando a nuvem estiver configurada)
    "interval_normal": 300,      # s entre envios do status com o servidor normal (só se houver novidade)
    "interval_alert": 30,        # s entre envios em ATENÇÃO/CRÍTICO (na prática: a cada janela gravada)
    "send_on_alert": True,       # envio imediato ao entrar em ATENÇÃO/CRÍTICO
    "send_on_recover": True,     # envio imediato ao voltar ao normal
    "history_interval": 3600,    # s entre envios do histórico ao GitHub (limite de escrita da conta)
    "retention_local_days": 30,  # dias de medições mantidos no relatório local
    "retention_cloud_days": 30,  # dias de histórico na nuvem (agregados de 5 min no Firebase; arquivos no GitHub)
    "retention_events_days": 180,  # dias de eventos (mudanças de estado) no Firebase
    "recent_hours": 48,          # horas de medições com resolução total no Firebase
    "rollup_seconds": 300,       # tamanho do bloco do histórico agregado no Firebase
    "heartbeat_interval": 60,    # s entre sinais de vida (independe de dados novos)
    "offline_after": 180,        # s sem sinal de vida para o Central considerar OFFLINE / sem comunicação
    "auto_update": True,         # autoatualização: procura versão nova do programa e, se houver, troca e reinicia
    "update_interval": 600,      # s entre verificações de versão nova (mínimo 300)
    "low_priority": True,        # depois do benchmark: CPU com nice 10 e E/S na classe ociosa (idle)
    "retention_slack_days": 7,   # folga da retenção local: reescreve o relatório só quando passa de
                                 # retention_local_days + isto (uma reescrita por semana, não por dia)
    "state_disk_interval": 600,  # s entre cópias do estado do envio (em RAM, /dev/shm) para o disco
    "db_access": True,           # acesso remoto da central ao Postgres local (db_config/<sid> ou DB_DEFAULTS)
    "sys_events": True,          # eventos do sistema (admin.system_email -> sys_events; exige db_access)
    "sys_events_interval": 180,  # s entre leituras da tabela de e-mails do sistema (mínimo 60)
    "sys_events_retention_days": 30,   # dias de eventos do sistema no Firebase (poda diária pelo last_at)
    "sql_editor": True,          # editor SQL remoto da central (v2.12, só leitura; exige db_access)
    "service": True,             # v2.13: o coletor se registra para iniciar com o sistema (systemd/cron; tarefa no Windows)
}
HIST_MIN_GAP = 600               # mudança de estado só antecipa o histórico se o último envio tiver > 10 min
HB_POLL = 5                      # s entre verificações da thread do heartbeat
HB_BACKOFF, HB_BACKOFF_MAX = 15, 60   # espera após falha do heartbeat: 15 s, 30 s, 60 s, 60 s...
HB_SUFFIX = ".hb"                 # live_path(log) + HB_SUFFIX, em RAM (/dev/shm): último heartbeat / falhas (para o --view)
SIGNAL_KEYS = ("release", "config_at", "catalog_at", "agent_config_at", "rename_at")   # avisos da central em signals/<sid> (v2.6.1; v2.11; v2.14)
RENAME_REFRESH = 6 * 3600        # s entre releituras de garantia de rename/<sid> (o aviso signals/<sid>/rename_at antecipa)
RENAME_RETRY = 300               # s até tentar de novo uma leitura/confirmação de renome que falhou
NAME_MAX = 80                    # empresa e nome do servidor: até 80 caracteres (--empresa/--nome, renome pela central)


class BusyError(CloudError):
    pass


def utc_iso(t):
    return datetime.datetime.fromtimestamp(t, datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def iso_epoch(s):
    try:
        return datetime.datetime.fromisoformat(s).timestamp()
    except (TypeError, ValueError):
        return None


def session_kv(line):
    kv = {}
    try:
        for t in shlex.split(line[8:]):
            k, _, v = t.partition("=")
            kv[k] = v
    except ValueError:
        pass
    return kv


# --------------------------------------------------------------------------
# Status ao vivo (Firebase Realtime Database, REST)
# --------------------------------------------------------------------------
FIREBASE_AUTH = os.environ.get("USAGE_MONITOR_FIREBASE_AUTH", "https://identitytoolkit.googleapis.com")   # testes
FIREBASE_TOKEN = os.environ.get("USAGE_MONITOR_FIREBASE_TOKEN", "https://securetoken.googleapis.com")    # testes
LIVE_FILE = "server_monitor.live"         # uid + refresh token do login anônimo (permissão 600)
LIVE_SCHEMA = 2
STATUS_FULL_EVERY = 1800     # s: status/<sid> inteiro pelo menos nesse intervalo; entre eles, só os campos que mudaram


# Conexões persistentes (v2.10.2): cada chamada REST com urlopen abria uma conexão nova (handshake TLS de ~4-5 KB
# de download cobrado, ~79% das requisições ao RTDB). v2.11: pool COMPARTILHADO entre as threads (antes era uma
# conexão por thread): o Google fecha a conexão ociosa entre 65 e 120 s, e só o heartbeat (60 s) mantinha a sua
# quente; sync (300 s), banco (600 s) e eventos (180 s) sempre encontravam a deles morta. Agora todas pegam a
# conexão usada mais recentemente (LIFO), a mesma que o heartbeat mantém viva.
HTTP_IDEMPOTENT = ("GET", "HEAD", "PUT", "PATCH", "DELETE", "OPTIONS")
HTTP_POOL_MAX = 4                  # conexões ociosas guardadas por servidor (acima disso, fecha ao devolver)
# falhas típicas de conexão reaproveitada que o servidor já fechou: refaz uma vez (só métodos idempotentes)
HTTP_STALE = (http.client.RemoteDisconnected, http.client.BadStatusLine, http.client.CannotSendRequest,
              BrokenPipeError, ConnectionResetError, ConnectionAbortedError) + (
                  (ssl.SSLEOFError, ssl.SSLZeroReturnError) if ssl is not None else ())


class HttpReply:
    """Resposta já lida por inteiro (a conexão fica livre para o próximo pedido), com a interface do urlopen."""

    def __init__(self, status, reason, headers, body):
        self.status, self.reason, self.headers, self.body = status, reason, headers, body

    def read(self):
        return self.body

    def __enter__(self):
        return self

    def __exit__(self, *a):
        return False


class HttpPool:
    """Conexões HTTP(S) keep-alive compartilhadas por servidor (esquema, host), para as chamadas REST ao Firebase RTDB.

    Mesmo contrato do urllib.request.urlopen: devolve a resposta (status 2xx) ou levanta HTTPError (com o corpo),
    URLError (falha ao conectar/enviar) ou o erro da leitura da resposta. Cada pedido pega uma conexão ociosa
    (a usada mais recentemente: LIFO, a que tem mais chance de estar viva), usa com exclusividade e devolve ao
    terminar; sem nenhuma ociosa, abre outra (pedidos simultâneos de threads diferentes nunca dividem uma
    conexão). Guarda até HTTP_POOL_MAX ociosas por servidor. Contexto TLS padrão do http.client (o mesmo do
    urlopen: certificado verificado). Conexão ociosa que o servidor fechou é detectada antes do envio (socket
    legível = EOF) e descartada; se cair durante o pedido, refaz UMA vez, só em método idempotente (o POST nunca
    se repete às cegas). Com proxy configurado (HTTPS_PROXY etc.) ou redirecionamento de GET, usa o urlopen.
    stats (em RAM): conexões novas, reaproveitadas, refeitas após queda e pedidos pelo urlopen (proxy)."""

    def __init__(self, max_idle=HTTP_POOL_MAX):
        self.lock = threading.Lock()
        self.max_idle = max_idle
        self.idle = {}                                # (esquema, servidor) -> conexões ociosas (a última = mais recente)
        self.conns = weakref.WeakSet()                # todas as conexões abertas (close_all)
        self.stats = {"new": 0, "reused": 0, "retried": 0, "urllib": 0}

    def count(self, k):
        with self.lock:
            self.stats[k] += 1

    def snapshot(self):
        with self.lock:
            return dict(self.stats)

    @staticmethod
    def proxied(scheme, netloc):
        """Proxy configurado para este esquema (e o servidor não está no no_proxy)? Igual ao ProxyHandler do urllib."""
        try:
            return bool(urllib.request.getproxies().get(scheme)) and not urllib.request.proxy_bypass(netloc)
        except Exception:
            return False

    def acquire(self, scheme, netloc, timeout):
        """Conexão exclusiva para um pedido: a ociosa usada mais recentemente que ainda esteja viva, senão uma nova
        (ainda sem socket: conecta no envio). As ociosas mortas encontradas no caminho são fechadas."""
        key = (scheme, netloc)
        while True:
            with self.lock:
                lst = self.idle.get(key)
                c = lst.pop() if lst else None
            if c is None:
                break
            if self.alive(c):
                return c
        cls = http.client.HTTPSConnection if scheme == "https" else http.client.HTTPConnection
        c = cls(netloc, timeout=timeout)
        with self.lock:
            self.conns.add(c)
        return c

    def release(self, scheme, netloc, c):
        """Devolve a conexão ao pool (só se continua aberta e há vaga); senão fecha."""
        with self.lock:
            lst = self.idle.setdefault((scheme, netloc), [])
            if c.sock is not None and len(lst) < self.max_idle:
                lst.append(c)
                return
        c.close()

    @staticmethod
    def alive(c):
        """Conexão aberta e ociosa sem nada para ler: reaproveitável. Legível = o servidor fechou (EOF) ou mandou
        algo fora de hora: fecha (o próximo pedido abre outra)."""
        if c.sock is None:
            return False
        try:
            r = select.select([c.sock], [], [], 0)[0]
        except (OSError, ValueError):                 # ValueError: descritor acima do FD_SETSIZE
            r = True
        if r:
            c.close()
            return False
        return True

    def urlopen(self, url, data, headers, method, timeout):
        self.count("urllib")
        return urllib.request.urlopen(urllib.request.Request(url, data=data, headers=headers, method=method),
                                      timeout=timeout)

    def open(self, url, data=None, headers=None, method=None, timeout=30):
        headers = dict(headers or {})
        method = (method or ("POST" if data is not None else "GET")).upper()
        u = urllib.parse.urlsplit(url)
        if u.scheme not in ("http", "https") or (u.scheme == "https" and not hasattr(http.client, "HTTPSConnection")) \
                or self.proxied(u.scheme, u.netloc):
            return self.urlopen(url, data, headers, method, timeout)
        path = (u.path or "/") + ("?" + u.query if u.query else "")
        c = self.acquire(u.scheme, u.netloc, timeout)
        try:
            return self.request(c, url, path, data, headers, method, timeout)
        finally:
            self.release(u.scheme, u.netloc, c)

    def request(self, c, url, path, data, headers, method, timeout):
        for attempt in (1, 2):
            reused = c.sock is not None               # acquire já conferiu que está viva
            self.count("reused" if reused else "new")
            c.timeout = timeout                       # usado ao conectar
            if c.sock is not None:
                c.sock.settimeout(timeout)
            sent = False
            try:
                c.request(method, path, body=data, headers=headers)
                sent = True
                r = c.getresponse()
                body = r.read()                       # sempre inteiro: senão a conexão não pode ser reaproveitada
            except Exception as e:
                c.close()
                if reused and attempt == 1 and method in HTTP_IDEMPOTENT and isinstance(e, HTTP_STALE):
                    self.count("retried")
                    continue
                if not sent and isinstance(e, OSError):
                    raise urllib.error.URLError(e)    # como o urlopen: falha ao conectar/enviar
                raise
            if 300 <= r.status < 400 and method in ("GET", "HEAD"):
                return self.urlopen(url, data, headers, method, timeout)      # o urlopen segue o redirecionamento
            if not 200 <= r.status < 300:
                raise urllib.error.HTTPError(url, r.status, r.reason, r.headers, io.BytesIO(body))
            return HttpReply(r.status, r.reason, r.headers, body)

    def close_all(self):
        """Fecha todas as conexões (parada, reinício da autoatualização). Quem usar de novo reconecta."""
        with self.lock:
            conns = list(self.conns)
            self.idle.clear()
        for c in conns:
            try:
                c.close()
            except Exception:
                pass


FB_HTTP = HttpPool()               # REST do Firebase RTDB (não a escuta SSE, que já é uma conexão longa)


class LiveStatus:
    """Status atual + medições recentes de cada servidor no Firebase Realtime Database.

    Cada instalação entra com login anônimo (uid próprio) e só escreve em servers/<install_id>,
    que as regras do banco amarram ao uid que o criou ('owner'). Envios com print=silent: o
    Firebase não devolve os dados (o plano gratuito limita o volume baixado)."""

    def __init__(self, ident, base):
        cfg = ident.data.get("live") or {}
        self.db = (cfg.get("db_url") or "").rstrip("/")
        self.key = cfg.get("api_key") or ""
        self.path = os.path.join(base, LIVE_FILE)
        self.id_token, self.exp = None, 0.0
        self.tok_lock = threading.Lock()      # worker e thread do heartbeat: um só renova o token
        self.skew = 0.0                       # hora do Firebase - hora local (cabeçalho Date), para pedidos ao banco

    def configured(self):
        return bool(self.db and self.key and os.path.exists(self.path))

    def _req(self, url, data, ctype="application/json", method="POST", timeout=30):
        try:
            with self.http(url, data, {"Content-Type": ctype, "User-Agent": "usage-monitor/" + VERSION}, method,
                           timeout) as r:
                raw = r.read()
                return json.loads(raw.decode()) if raw else {}
        except urllib.error.HTTPError as e:
            try:
                body = json.loads(e.read().decode("utf-8", "replace"))
                msg = (body.get("error") or {}).get("message", "") if isinstance(body.get("error"), dict) else body.get("error", "")
            except (ValueError, AttributeError):
                msg = ""
            err = CloudError(firebase_error(e.code, str(msg)))
            err.code = e.code
            err.denied = "denied" in str(msg).lower()      # regra recusou (não é token vencido)
            raise err
        except (urllib.error.URLError, OSError) as e:
            raise CloudError("sem conexão com o Firebase (%s)" % getattr(e, "reason", e))

    def http(self, url, data, headers, method, timeout):
        """Banco (RTDB): conexão persistente (FB_HTTP). Login (identitytoolkit/securetoken: cadastro e renovação do
        token, ~1 por hora) segue no urlopen: o POST do cadastro não pode ser repetido às cegas."""
        if self.db and url.startswith(self.db + "/"):
            return FB_HTTP.open(url, data, headers, method, timeout)
        return urllib.request.urlopen(urllib.request.Request(url, data=data, headers=headers, method=method),
                                      timeout=timeout)

    def secret(self):
        try:
            with open(self.path) as f:
                return json.load(f)
        except OSError:
            raise CloudError("sem acesso a %s (rode como o mesmo usuário do coletor)" % self.path)
        except ValueError:
            raise CloudError("%s corrompido: rode --cloud-setup" % self.path)

    def sign_up(self):
        r = self._req("%s/v1/accounts:signUp?key=%s" % (FIREBASE_AUTH, urllib.parse.quote(self.key)),
                      json.dumps({"returnSecureToken": True}).encode())
        write_private(self.path, json.dumps({"uid": r["localId"], "refresh_token": r["refreshToken"]}))
        self.id_token, self.exp = r["idToken"], time.time() + int(r.get("expiresIn", 3600))
        return r["localId"]

    def token(self, min_valid=120):
        """Token de acesso; renova se faltar menos de min_valid s para vencer."""
        with self.tok_lock:
            if self.id_token and time.time() < self.exp - min_valid:
                return self.id_token
            sec = self.secret()
            r = self._req("%s/v1/token?key=%s" % (FIREBASE_TOKEN, urllib.parse.quote(self.key)),
                          urllib.parse.urlencode({"grant_type": "refresh_token", "refresh_token": sec["refresh_token"]}).encode(),
                          ctype="application/x-www-form-urlencoded", timeout=15)
            if r.get("refresh_token") and r["refresh_token"] != sec["refresh_token"]:
                sec["refresh_token"] = r["refresh_token"]
                write_private(self.path, json.dumps(sec))
            self.id_token, self.exp = r["id_token"], time.time() + int(r.get("expires_in", 3600))
            return self.id_token

    def uid(self):
        return self.secret()["uid"]

    def get(self, path, params=None, timeout=30):
        q = dict(params or {})
        q["auth"] = self.token()
        url = "%s/%s.json?%s" % (self.db, path, urllib.parse.urlencode(q))
        try:
            with self.http(url, None, {"User-Agent": "usage-monitor/" + VERSION}, "GET", timeout) as r:
                self.note_date(r.headers)
                return json.loads(r.read().decode() or "null")
        except urllib.error.HTTPError as e:
            err = CloudError(firebase_error(e.code, ""))
            err.code = e.code
            raise err
        except (urllib.error.URLError, OSError) as e:
            raise CloudError("sem conexão com o Firebase (%s)" % getattr(e, "reason", e))

    def note_date(self, headers):
        """Estima a hora do Firebase pelo cabeçalho Date (resolução de 1 s: soma meio segundo)."""
        try:
            t = email.utils.parsedate_to_datetime(headers.get("Date")).timestamp()
        except (TypeError, ValueError):
            return
        self.skew = t + 0.5 - time.time()

    def server_now(self):
        return time.time() + self.skew

    def claim(self, sid, code):
        """Cadastra a instalação: owners/<sid> = {uid, code, at}. As regras só aceitam com o código de
        cadastro correto e se o servidor ainda não tiver dono. Do cadastro, o dono só consegue ler
        owners/<sid>/uid (o código nunca é legível); sem dono, a leitura é recusada."""
        uid = self.uid()
        try:
            cur = self.get("owners/%s/uid" % sid)
        except CloudError:
            cur = None
        if cur == uid:
            return "já cadastrado"
        self._req("%s/owners/%s.json?print=silent&auth=%s" % (self.db, sid, urllib.parse.quote(self.token())),
                  json.dumps({"uid": uid, "code": code, "at": {".sv": "timestamp"}}).encode(), method="PUT")
        return "cadastrado"

    def patch(self, path, payload, timeout=30):
        for attempt in (1, 2):
            url = "%s/%s.json?print=silent&auth=%s" % (self.db, path, urllib.parse.quote(self.token()))
            try:
                return self._req(url, json.dumps(payload).encode(), method="PATCH", timeout=timeout)
            except CloudError as e:
                denied = getattr(e, "denied", False) or "denied" in str(e).lower()
                if getattr(e, "code", 0) == 401 and attempt == 1 and not denied:
                    self.id_token = None          # token vencido: renova e tenta de novo
                    continue
                raise


def firebase_error(code, msg):
    m = msg.upper()
    if "OPERATION_NOT_ALLOWED" in m or "ADMIN_ONLY_OPERATION" in m:
        return "login anônimo desativado no Firebase (Authentication > Sign-in method > Anônimo)"
    if "API_KEY" in m or "API KEY" in m:
        return "chave de API do Firebase inválida"
    if "TOKEN_EXPIRED" in m or "INVALID_REFRESH_TOKEN" in m or "USER_NOT_FOUND" in m:
        return "acesso ao Firebase expirou: rode --cloud-setup"
    if "PERMISSION" in m.replace(" ", "_") or code in (401, 403):
        return "o Firebase recusou a escrita (confira as regras do banco no README)"
    return "Firebase respondeu %d%s" % (code, (": " + msg) if msg else "")


# --------------------------------------------------------------------------
# Envio dos relatórios para a nuvem
# --------------------------------------------------------------------------
def status_window(kv, sess, t):
    """window_s do status: a duração real da janela, mas nunca menor que a janela nominal do horário (a 1ª janela
    curta da partida ou uma parcial não podem encurtar o prazo de "dados atrasados" da central)."""
    win = float(kv.get("win") or 0)
    try:
        iv = int(sess.get("interval") or 0)
        biv = int(sess.get("biz_interval") or iv)
        a, b = (int(x) for x in (sess.get("biz_hours") or "0-0").split("-"))
    except ValueError:
        return win
    nominal = biv if a <= time.localtime(t).tm_hour < b else iv
    return float(max(win, nominal))


class CloudSync:
    """Envio para a nuvem em dois canais, com uma trava e um arquivo de estado em comum:

    - histórico (GitHub, repositório PRIVADO): o relatório é fatiado em arquivos diários
      autocontidos em SYNC_DIR/spool (leitura incremental) e cada dia vira 'AAAA-MM-DD.log.gz'
      na release 'srv-<id>-<ano>' (dias fechados uma vez; o dia corrente é substituído); o texto
      da release guarda empresa, host, hardware e benchmark em JSON. Arquivos com mais de
      retention_cloud_days dias são apagados, só nas releases desta instalação.
    - status ao vivo (Firebase, opcional): ver LiveStatus / live_sync.
    Criptografia futura do histórico: só mudar encode() (e o sufixo do nome)."""

    def __init__(self, log, ident, host):
        self.log, self.ident, self.host = log, ident, host
        self.base = os.path.dirname(os.path.abspath(log))
        self.dir = os.path.join(self.base, SYNC_DIR)
        self.acfg = AgentConfig(os.path.join(self.dir, AGENT_CFG_FILE))   # frequências da central (v2.11)
        self.sql_info = {}                # editor SQL (v2.12): sql_cert_fp/sql_proto vão junto se info/<sid> for regravado
        self.spool = os.path.join(self.dir, "spool")
        self.state_path = os.path.join(self.dir, "state.json")
        self.ram_path = state_ram_path(log)   # cópia de trabalho do estado, em RAM (None sem /dev/shm)
        self.disk_at = 0.0                # última cópia do estado gravada no disco (por este processo)
        self.mem_state = None             # último estado salvo (o painel do coletor lê daqui, sem disco)
        self.live = LiveStatus(ident, self.base)
        self.ncpu = None                  # vCPUs para o heartbeat (lido do /proc/stat na 1ª vez)
        self.status_sent = None           # (sid, {campo: json}, quando foi inteiro) do último status confirmado

    def hist_on(self):
        return bool(self.ident.repo)

    def configured(self):
        return self.hist_on() or self.live.configured()

    def load_state(self):
        """Estado do envio: a mais nova (saved_at) entre a cópia em RAM e a do disco. A do disco fica até
        state_disk_interval atrás (ou some a da RAM num reboot): o envio ao vivo é idempotente (chaves por
        horário), então voltar alguns minutos só reenvia janelas; o histórico grava no disco sempre."""
        st = {}
        for path in (self.state_path, self.ram_path):
            d = read_json_owned(path) if path == self.ram_path else read_json(path)
            if isinstance(d, dict) and d.get("saved_at", 0) >= st.get("saved_at", -1):
                st = d                            # empate: a da RAM (lida por último)
        for k, v in (("offset", 0), ("ino", None), ("ctx", []), ("ctx_day", None), ("days", {}),
                     ("releases", {}), ("meta", {}), ("status", {}), ("bench", {}), ("last_line_ts", None),
                     ("skip_ts", None), ("private_at", 0), ("retention_at", 0), ("live", {})):
            st.setdefault(k, v)
        for k, v in (("offset", 0), ("ino", None), ("last_ts", None), ("keys", []), ("hw", ""), ("os", ""), ("sess", {}),
                     ("hwlines", []), ("status", {}), ("last", None), ("stopped", False), ("levels", {}),
                     ("bucket", None), ("pruned_at", 0), ("bench", {}), ("bench_scan", False)):
            st["live"].setdefault(k, v)
        return st

    def save_state(self, st, durable=False):
        """Grava o estado na RAM (/dev/shm: sem E/S de disco) e, no máximo a cada state_disk_interval, no
        disco; durable=True grava no disco já (fim do envio do histórico, parada, envio manual).
        Sem /dev/shm (ou se a gravação lá falhar) vai direto para o disco, como antes."""
        st["saved_at"] = time.time()
        text = json.dumps(st, separators=(",", ":"))
        self.mem_state = st
        ram = False
        if self.ram_path:
            try:
                write_private(self.ram_path, text)
                ram = True
            except OSError:
                pass
        if not ram or durable or time.time() - self.disk_at >= self.ident.sync_cfg()["state_disk_interval"]:
            os.makedirs(self.dir, mode=0o700, exist_ok=True)
            write_private(self.state_path, text)
            self.disk_at = time.time()

    @contextlib.contextmanager
    def session(self, durable=False):
        """Trava (um envio por vez, entre processos) + estado carregado e salvo ao final
        (durable=True: também no disco na hora)."""
        if fcntl is None and msvcrt is None:
            raise CloudError("envio só nos servidores Linux ou Windows")
        os.makedirs(self.spool, mode=0o700, exist_ok=True)
        lockf = open(os.path.join(self.dir, "lock"), "a")
        if not lock_file(lockf):
            lockf.close()
            raise BusyError("já existe um envio em andamento")
        st = self.load_state()
        try:
            yield st
        finally:
            try:
                self.save_state(st, durable=durable)
            finally:
                lockf.close()

    def run(self, out=None):
        """Envio manual (--sync, tecla u no --view): histórico e status ao vivo. Devolve nº de arquivos."""
        if not self.configured():
            raise CloudError("nuvem não configurada: rode %s --cloud-setup" % sys.argv[0])
        with self.session(durable=True) as st:
            n = self.hist_sync(st, out) if self.hist_on() else 0
            if self.live.configured():
                self.live_sync(st, force=True)
                if out:
                    out("  status ao vivo atualizado")
        return n

    # ---- histórico (GitHub) ----
    def hist_sync(self, st, out=None):
        token = load_token(self.base)
        if not token:
            raise CloudError("token do GitHub não encontrado: rode --cloud-setup")
        st["status"] = {"state": "enviando", "at": time.time(), "msg": ""}
        self.save_state(st)
        try:
            self.ingest(st)
            gh = GitHub(self.ident.repo, token)
            n = self.upload(st, gh, out)
            self.retention(st, gh, out)
            st["status"] = {"state": "ok", "at": time.time(), "pending": 0,
                            "msg": "%d arquivo(s) enviado(s)" % n if n else "nada novo para enviar"}
            return n
        except CloudError as e:
            st["status"] = {"state": "erro", "at": time.time(), "msg": str(e), "pending": self.hist_pending(st)}
            raise
        except Exception as e:
            st["status"] = {"state": "erro", "at": time.time(), "msg": "%s: %s" % (type(e).__name__, e),
                            "pending": self.hist_pending(st)}
            raise CloudError(st["status"]["msg"])

    def hist_pending(self, st):
        today = time.strftime("%Y-%m-%d")
        return sum(1 for d, v in st["days"].items() if not v["final"] and (v["sent"] != v["size"] or d < today))

    def day_path(self, day):
        return os.path.join(self.spool, day + ".log")

    def header(self, day):
        return ("# usage_monitor - relatório diário enviado à nuvem (mesmo formato do relatório local)\n"
                "# empresa=%s | servidor=%s | install_id=%s | dia=%s | fuso=%s | monitor v%s\n"
                % (self.ident.company or "?", self.host, self.ident.install_id, day, timezone_name(), VERSION))

    def ingest(self, st):
        """Acrescenta aos arquivos diários as linhas completas novas do relatório."""
        try:
            fst = os.stat(self.log)
        except OSError:
            raise CloudError("relatório não encontrado: %s" % self.log)
        if st["ino"] != fst.st_ino or fst.st_size < st["offset"]:
            # relatório novo, truncado ou compactado pela retenção: relê, pulando o que já foi (a busca
            # binária acha o ponto sem ler o arquivo inteiro)
            last = iso_epoch(st["last_line_ts"]) if st["last_line_ts"] else None
            st.update(offset=seek_ts(self.log, last, fst.st_size) if last is not None else 0, ino=fst.st_ino,
                      skip_ts=st["last_line_ts"])
        if st["offset"] and not st["bench"].get("lines"):
            st["bench"] = self.last_bench_in_log(st["offset"])          # estado de versão anterior
        ctx, cur = st["ctx"], st["ctx_day"]
        skip = iso_epoch(st["skip_ts"]) if st["skip_ts"] else None
        files, need_bench = {}, set()
        pacer = Pacer()

        def put(day, line):
            d = st["days"].setdefault(day, {"size": 0, "sent": -1, "final": False})
            if d["final"]:
                return                            # dia já fechado e enviado
            fh = files.get(day)
            if fh is None:
                p = self.day_path(day)
                new = not os.path.exists(p)
                fh = files[day] = open(p, "a")
                if new:                           # arquivo autocontido: começa com a sessão vigente
                    fh.write(self.header(day))
                    fh.writelines(c + "\n" for c in ctx)
                    if not any(c.startswith("BENCH ") for c in ctx):
                        need_bench.add(day)
            if line.startswith("BENCH "):
                need_bench.discard(day)
            elif day in need_bench and line.startswith(("DATA ", "EVENT ")):
                need_bench.discard(day)
                bench = st["bench"]
                if bench.get("lines"):            # sessão sem benchmark (--no-bench): leva o último medido, com a data
                    fh.write("# bench_de=%s\n" % bench.get("when", ""))
                    fh.writelines(c + "\n" for c in bench["lines"])
            fh.write(line + "\n")
            pacer.add(len(line))                  # 1ª vez com relatório grande: sem rajada de gravação

        try:
            for line in self.new_lines(st):
                m = DAY_RE.search(line[:40])
                if skip is not None:              # releitura após rotação: só reconstrói o contexto
                    if line.startswith("SESSION "):
                        ctx = [line]
                    elif line.startswith(("HW ", "BENCH ", "CAP ")):
                        ctx.append(line)
                    elif line.startswith(("DATA ", "EVENT ")) and m:
                        t = iso_epoch(line.split("ts=", 1)[1].split(" ", 1)[0])
                        if t is not None and t <= skip:
                            continue
                        skip, st["skip_ts"] = None, None
                    else:
                        continue
                    if skip is not None:
                        continue
                if line.startswith("SESSION ") and m:
                    ctx, cur = [], m.group(1)
                    put(cur, line)
                    ctx = [line]
                elif line.startswith(("HW ", "BENCH ", "CAP ")):
                    if cur:
                        put(cur, line)
                    ctx.append(line)
                    if line.startswith("BENCH "):     # último benchmark conhecido (sobrevive a --no-bench)
                        start = ctx[0].split("start=", 1)[1].split(" ", 1)[0] if ctx[0].startswith("SESSION ") else ""
                        if st["bench"].get("when") != start:
                            st["bench"] = {"when": start, "lines": []}
                        st["bench"]["lines"].append(line)
                elif line.startswith(("DATA ", "EVENT ")) and m:
                    cur = m.group(1)
                    put(cur, line)
                    st["last_line_ts"] = line.split("ts=", 1)[1].split(" ", 1)[0]
        finally:
            for day, fh in files.items():
                fh.close()
                st["days"][day]["size"] = os.path.getsize(self.day_path(day))
        st["ctx"], st["ctx_day"] = ctx, cur

    def new_lines(self, st):
        """Linhas completas depois de st["offset"], lidas em trechos de LIVE_READ (memória limitada mesmo
        na 1ª vez com um relatório grande); o offset avança a cada trecho. Linha incompleta fica para depois."""
        with open(self.log, "rb") as f:
            while True:
                f.seek(st["offset"])
                data = f.read(LIVE_READ)
                end = data.rfind(b"\n") + 1
                st["offset"] += end
                yield from data[:end].decode("utf-8", "replace").splitlines()
                if len(data) < LIVE_READ or not end:
                    return

    def last_bench_in_log(self, limit):
        """Último benchmark do relatório (até o byte 'limit'), lido uma vez em streaming."""
        found, start, cur = {}, "", None
        with open(self.log, "rb") as f:
            for raw in f:
                if f.tell() > limit:
                    break
                line = raw.decode("utf-8", "replace").rstrip("\n")
                if line.startswith("SESSION "):
                    start, cur = line.split("start=", 1)[1].split(" ", 1)[0] if "start=" in line else "", None
                elif line.startswith("# bench_de="):              # relatório reescrito pela retenção
                    start, cur = line[11:].strip(), None
                elif line.startswith("BENCH "):
                    if cur is None:
                        cur = found = {"when": start, "lines": []}
                    cur["lines"].append(line)
        return found

    def encode(self, raw):
        """Ponto único de transformação antes do envio (hoje gzip; futuro: + criptografia)."""
        return gzip.compress(raw, 6, mtime=0)

    def hw_meta(self, st):
        hw = {}
        for line in st["ctx"]:
            if line.startswith("HW "):
                k, _, v = line[3:].partition(":")
                k, v = k.strip(), v.strip()
                if k.startswith("disk.") or k == "fs":
                    hw.setdefault("disks" if k.startswith("disk.") else "filesystems", []).append(
                        (k[5:] + ": " + v) if k.startswith("disk.") else v)
                elif k in ("os", "kernel", "virtualization", "cpu_model", "cpu_logical", "mem_total_GB", "swap_total_GB"):
                    hw[k] = v
        return hw

    def release_meta(self, year, st):
        meta = {"company": self.ident.company, "name": self.ident.name, "install_id": self.ident.install_id, "hostname": self.host,
                "year": year, "monitor_version": VERSION, "report_format": "usage_report/2",
                "timezone": timezone_name(), "hardware": self.hw_meta(st),
                "benchmark": bench_dict(st["bench"].get("lines", [])),
                "benchmark_measured": st["bench"].get("when", "")}
        name = "%s · %s · %s" % (self.ident.company or "(empresa não configurada)", self.host, year)
        body = ("Relatórios diários do usage_monitor (um arquivo .log.gz por dia).\n\n"
                "**Empresa:** %s  \n**Servidor:** %s  \n**Ano:** %s\n\n```json\n%s\n```\n"
                % (meta["company"] or "?", self.host, year, json.dumps(meta, indent=2, ensure_ascii=False)))
        return name, body

    def tag(self, year):
        return "srv-%s-%s" % (self.ident.install_id[:12], year)

    def release(self, gh, st, year, cache, create=True):
        tag = self.tag(year)
        if tag in cache:
            return cache[tag]
        name, body = self.release_meta(year, st)
        rel = gh.release_by_tag(tag)
        if rel is None:
            if not create:
                return None
            rel = gh.create_release(tag, name, body)
        h = hashlib.sha1((name + body).encode()).hexdigest()
        if st["meta"].get(tag) != h and rel.get("body") != body:
            gh.update_release(rel["id"], name, body)     # empresa/host/hardware mudaram
        st["meta"][tag] = h
        cache[tag] = {"id": rel["id"], "assets": {a["name"]: a["id"] for a in gh.assets(rel["id"])}}
        return cache[tag]

    def upload(self, st, gh, out=None):
        if time.time() - st["private_at"] > 6 * 3600:    # confere a privacidade a cada 6 h (economiza requisições)
            info = gh.repo_info()
            if not info.get("private"):
                raise CloudError("%s é público: por segurança só envio para repositório privado" % gh.repo)
            st["private_at"] = time.time()
        today = time.strftime("%Y-%m-%d")
        todo = sorted(d for d, v in st["days"].items() if not v["final"] and (v["sent"] != v["size"] or d < today))
        cache, sent = {}, 0
        for day in todo:
            v, p = st["days"][day], self.day_path(day)
            if not os.path.exists(p):
                v["final"] = True
                continue
            with open(p, "rb") as f:
                raw = f.read()
            blob = self.encode(raw)
            rel = self.release(gh, st, day[:4], cache)
            name = day + ".log.gz"
            if name in rel["assets"]:                  # substitui a versão anterior do dia
                gh.delete_asset(rel["assets"].pop(name))
            asset = gh.upload_asset(rel["id"], name, blob)
            rel["assets"][name] = asset["id"]
            v["sent"] = len(raw)
            if day < today:                            # dia fechado: enviado de vez
                v["final"] = True
                os.remove(p)
            sent += 1
            self.save_state(st, durable=v["final"])    # progresso preservado se cair no meio (arquivo do dia já apagado: no disco)
            if out:
                out("  enviado %s (%s KB)" % (name, max(1, len(blob) // 1024)))
        # empresa/host/hardware mudaram sem dados novos: atualiza a descrição da release do ano
        year = today[:4]
        name, body = self.release_meta(year, st)
        if self.tag(year) in st["meta"] and st["meta"][self.tag(year)] != hashlib.sha1((name + body).encode()).hexdigest():
            self.release(gh, st, year, cache)
            self.save_state(st)
        return sent

    def retention(self, st, gh, out=None):
        """Apaga da nuvem os dias além de retention_cloud_days, só nas releases desta instalação
        (uma vez por dia). Releases não guardam histórico Git: apagar libera o espaço de fato."""
        if time.time() - st["retention_at"] < 86400:
            return
        keep = self.ident.sync_cfg()["retention_cloud_days"]
        cut = time.strftime("%Y-%m-%d", time.localtime(time.time() - keep * 86400))
        removed = 0
        for year in range(int(cut[:4]) - 1, int(time.strftime("%Y")) + 1):
            rel = self.release(gh, st, str(year), {}, create=False)
            if not rel:
                continue
            for name, aid in sorted(rel["assets"].items()):
                if name.endswith(".log.gz") and name[:10] < cut:
                    gh.delete_asset(aid)
                    removed += 1
        st["retention_at"] = time.time()
        if out and removed:
            out("  retenção: %d arquivo(s) com mais de %d dias apagados da nuvem" % (removed, keep))

    # ---- status ao vivo, eventos e histórico (Firebase Realtime Database) ----
    def live_sync(self, st, force=False, timeout=30, max_chunks=4):
        """Envio incremental ao Firebase do que foi gravado depois do último checkpoint confirmado.

        Cada janela nova vira: recent/<sid>/<ts> (resolução total, recent_hours), parte do agregado
        history/<sid>/<bloco de 5 min> e, se algum recurso mudou de nível, events/<sid>/<ts>_<recurso>.
        Ao final, status/<sid> (estado atual + heartbeat) e info/<sid> (se mudou). As chaves são
        derivadas do horário: repetir um envio sobrescreve, nunca duplica. O checkpoint (last_ts,
        níveis e agregado em andamento) só avança depois de cada lote confirmado; a primeira
        sincronização de um histórico grande vai em lotes (max_chunks por chamada) e self.more
        indica que ainda há pendências. Devolve nº de janelas enviadas."""
        L = st["live"]
        cfg = self.ident.sync_cfg()
        sid = self.ident.install_id
        self.more = False
        try:
            fst = os.stat(self.log)
        except OSError:
            raise CloudError("relatório não encontrado: %s" % self.log)
        last = iso_epoch(L["last_ts"]) if L["last_ts"] else None
        if L["ino"] != fst.st_ino or fst.st_size < L["offset"]:
            # rotação/compactação: relê a partir da busca binária (não o arquivo inteiro) e filtra pelo horário
            L.update(offset=seek_ts(self.log, last, fst.st_size) if last is not None else 0, ino=fst.st_ino)
        with open(self.log, "rb") as f:
            f.seek(L["offset"])
            data = f.read(LIVE_READ)
        end = data.rfind(b"\n") + 1
        complete = L["offset"] + end >= fst.st_size - 1 or len(data) < LIVE_READ
        sess, hwlines, stopped = dict(L["sess"]), list(L["hwlines"]), L["stopped"]
        # último benchmark conhecido: sobrevive a sessões sem benchmark (--no-bench da autoatualização) e à
        # retenção ('# bench_de=' + BENCH); estado de versão anterior = procura no relatório uma vez só
        bench = dict(L["bench"])
        if not bench.get("lines") and not L["bench_scan"]:
            if L["offset"]:
                bench = self.last_bench_in_log(L["offset"])
            L["bench_scan"] = True
        mark, fresh = sess.get("start", ""), True
        rows = []
        for line in data[:end].decode("utf-8", "replace").splitlines():
            if line.startswith("SESSION "):
                kv = session_kv(line)
                sess = {k: kv.get(k, "") for k in ("start", "cpus", "sample", "disks", "interval", "biz_interval", "biz_hours",
                                                   "platform", "monitoring")}
                hwlines, stopped = [], False
                mark, fresh = sess["start"], True
            elif line.startswith("# bench_de="):
                mark, fresh = line[11:].strip(), True
            elif line.startswith(("HW ", "BENCH ", "CAP ")):
                hwlines.append(line)
                if line.startswith("BENCH "):
                    if fresh:
                        bench, fresh = {"when": mark, "lines": []}, False
                    bench["lines"].append(line)
            elif line.startswith("DATA "):
                try:
                    kv = data_kv(line)
                    t = iso_epoch(kv["ts"])
                except (KeyError, ValueError):
                    continue
                if t is None or (last is not None and t <= last):
                    continue
                rows.append((t, kv, sess.get("disks", "").split(), dict(sess)))
                stopped = False
            elif line.startswith("EVENT ") and "type=stop" in line:
                stopped = True
        now = time.time()
        if not rows and not force and stopped == L["stopped"]:
            # nada a enviar, mas o contexto lido (sessão, hardware) não pode se perder com o avanço do offset
            L.update(offset=L["offset"] + end, sess=sess, hwlines=hwlines[-200:], bench=bench)
            return 0
        keep_from = now - cfg["retention_cloud_days"] * 86400       # primeira sincronização: só o período de retenção
        rows = [r for r in rows if r[0] >= keep_from]
        recent_cut = now - cfg["recent_hours"] * 3600
        levels, bucket = dict(L["levels"]), (copy.deepcopy(L["bucket"]) if L["bucket"] else None)
        R = cfg["rollup_seconds"]
        entries, sent, chunks, lastrow = {}, 0, 0, None

        sent_keys = []

        def commit(t):
            L.update(last_ts=utc_iso(t).replace("Z", "+00:00"), levels=dict(levels),
                     bucket=copy.deepcopy(bucket) if bucket else None,
                     keys=sorted(set(L["keys"]) | set(sent_keys)))      # lotes também entram na poda de recent

        for t, kv, disks, s in rows:
            try:
                ncpu, sample = int(s.get("cpus") or 1), int(s.get("sample") or 5)
            except ValueError:
                ncpu, sample = 1, 5
            row = window_row(kv, all_keys(disks), disks, sample, ncpu)
            dg = diagnose(row, ncpu, disks, msgs=True)
            key = "%010d" % int(t)
            if t >= recent_cut:
                entries["recent/%s/%s" % (sid, key)] = compact_row(row, kv, disks)
                sent_keys.append(int(t))
            for res in RES_KEYS:                        # eventos: só nas mudanças de nível
                lv = dg[res][0]
                if lv is not None and levels.get(res) is not None and lv != levels[res]:
                    entries["events/%s/%s_%s" % (sid, key, res)] = self.event_doc(t, kv, row, dg, res, levels[res], lv, disks)
                if lv is not None:
                    levels[res] = lv
            b = int(t // R) * R                         # agregado de 5 min (histórico longo)
            if bucket and bucket["b"] != b:
                entries["history/%s/%010d" % (sid, bucket["b"])] = bucket_doc(bucket)
                bucket = None
            bucket = bucket_add(bucket, b, row, kv, disks)
            lastrow, sent = (t, kv, disks, s, row), sent + 1
            if len(entries) >= 800:                     # lote: ~200 KB por requisição
                entries["history/%s/%010d" % (sid, bucket["b"])] = bucket_doc(bucket)
                self.live.patch("", entries, timeout=timeout)
                commit(t)
                self.save_state(st)
                entries, chunks = {}, chunks + 1
                if chunks >= max_chunks:                 # devolve a vez (heartbeat, coleta, painel)
                    self.more = True
                    return sent
        if bucket:
            entries["history/%s/%010d" % (sid, bucket["b"])] = bucket_doc(bucket)
        for k in L["keys"]:
            if int(k) < recent_cut:
                entries["recent/%s/%010d" % (sid, int(k))] = None
        if lastrow is None and L["last"]:
            t0, kv0, d0, s0 = L["last"]
            try:
                n0, smp0 = int(s0.get("cpus") or 1), int(s0.get("sample") or 5)
            except ValueError:
                n0, smp0 = 1, 5
            lastrow = (t0, kv0, d0, s0, window_row(kv0, all_keys(d0), d0, smp0, n0))
        pending = None
        if lastrow:
            pending = self.status_entries(entries, sid, self.status_doc(lastrow, st, stopped, sent), force)
        info, h = self.info_doc(st, hwlines, bench)
        osd = os_info()                               # sistema operacional: estático, relido a cada OS_INFO_TTL
        oh = hashlib.sha1(json.dumps(osd, sort_keys=True).encode()).hexdigest() if osd else ""
        if osd:
            osd["updated_at_ms"] = {".sv": "timestamp"}
        if h != L["hw"]:
            if osd:
                info["os"] = osd                      # info/<sid> é sobrescrito inteiro: o os vai junto
            entries["info/" + sid] = info
        elif oh and oh != L.get("os"):
            entries["info/%s/os" % sid] = osd         # só o sistema mudou (upgrade): só ele
        try:
            self.live.patch("", entries, timeout=timeout)
        except Exception:
            self.status_sent = None                   # pode ter sido aplicado sem resposta: o próximo vai inteiro
            raise
        if pending:
            self.status_sent = pending
        # sucesso confirmado: o checkpoint avança
        if rows:
            commit(rows[-1][0])
        L["keys"] = sorted({int(k) for k in L["keys"] if int(k) >= recent_cut} |
                           {int(t) for t, *_ in rows if t >= recent_cut})
        L.update(sess=sess, hwlines=hwlines[-200:], stopped=stopped, hw=h, os=oh if oh else L.get("os", ""), bench=bench)
        if lastrow:
            L["last"] = list(lastrow[:4])
        L["offset"] += end                           # tudo até 'end' foi enviado (ou descartado pela retenção)
        if not complete:
            self.more = True                          # relatório grande (1ª sincronização): próximo trecho logo
        return sent

    def status_entries(self, entries, sid, doc, full=False):
        """Põe status/<sid> em entries: inteiro (1º envio do processo, force, a cada STATUS_FULL_EVERY) ou só os
        campos de 1º nível que mudaram desde o último envio confirmado (v2.11.1: cada envio é repassado a todas as
        centrais abertas; identificação, mensagens e versão quase nunca mudam). Campo com valor do servidor (.sv)
        vai sempre; campo que sumiu vira null. Devolve o que vira self.status_sent quando o envio for confirmado."""
        now = time.time()
        canon = {k: json.dumps(v, sort_keys=True, separators=(",", ":")) for k, v in doc.items()}
        prev = self.status_sent
        if full or prev is None or prev[0] != sid or now - prev[2] >= STATUS_FULL_EVERY:
            entries["status/" + sid] = doc
            return sid, canon, now
        for k, v in doc.items():
            if canon[k] != prev[1].get(k) or '".sv"' in canon[k]:
                entries["status/%s/%s" % (sid, k)] = v
        for k in prev[1]:
            if k not in doc:
                entries["status/%s/%s" % (sid, k)] = None
        return sid, canon, prev[2]

    def ident_doc(self):
        """Identificação repetida em status, info e events (textos até RTDB_ID_MAX)."""
        return {"install_id": self.ident.install_id, "company": clip(self.ident.company, RTDB_ID_MAX),
                "company_id": clip(self.ident.company_id, RTDB_ID_MAX), "hostname": clip(self.host, RTDB_ID_MAX),
                "name": clip(self.ident.name, RTDB_ID_MAX)}

    def status_doc(self, lastrow, st, stopped, nrows):
        """status/<sid>: estado atual do servidor (esquema versionado, horários em UTC).
        measured_at = fim da última janela medida; synced_at = horário (do servidor Firebase) deste
        envio; heartbeat.at = último sinal de vida (também atualizado sem dados novos)."""
        t, kv, disks, sess, row = lastrow
        try:
            ncpu = int(sess.get("cpus") or 1)
        except ValueError:
            ncpu = 1
        dg = diagnose(row, ncpu, disks, msgs=True)
        fs = row.get("_fs")                      # None = janela sem medição de espaço (Client < 2.3)
        levels = {k: dg[k][0] for k in RES_KEYS if k != "space" or fs is not None}
        known = [v for v in levels.values() if v is not None]
        lv = max(known) if known else None
        # desempate: desempenho antes de espaço (que costuma durar dias)
        main = next((k for k in ("disk", "cpu", "mem", "space") if lv and levels.get(k) == lv), None)
        cfg = self.cfg_now()
        g = lambda k: None if row.get(k) is None or row.get(k) != row.get(k) else round(row.get(k), 2)
        dk = dg["disk"][2] if len(dg["disk"]) > 2 else None
        doc = {
            "schema": LIVE_SCHEMA, **self.ident_doc(),
            "level": LEVEL_KEYS.get(lv, "SEM_DADOS"), "main_resource": main,
            "headline": headline(dg[main][1]) if main else "Servidor operando normalmente.",
            "resources": {k: {"level": LEVEL_KEYS.get(levels[k], "SEM_DADOS"), "message": dg[k][1]} for k in levels},
            "cpu_usage": g("cpu_avg"), "memory_usage": g("mem_avg"),
            "disk_busy": g(dk + ".util_avg") if dk else None, "disk_device": rtdb_key(dk) if dk else None,
            "io_pressure": g("psi_io"),
            "metrics": {k: g(k) for k in ("cpu_avg", "cpu_max", "rq_avg", "psi_cpu", "st_avg", "hot_max", "iow_avg",
                                          "load1", "mem_avg", "swap", "swio", "majf", "psi_mem", "psi_mem_full",
                                          "psi_io", "psi_io_full")},
            "disks": {rtdb_key(d): {k: g(d + "." + k) for k in ("util_avg", "util_max", "await", "qd_avg", "iops_avg", "rMBs",
                                                      "wMBs", "riops", "wiops", "r_await", "w_await")} for d in disks},
            "cpus": ncpu, "flags": kv.get("flags", ""),
            "measured_at": utc_iso(t), "measured_at_ms": int(t * 1000), "window_s": status_window(kv, sess, t),
            "synced_at_ms": {".sv": "timestamp"}, "client_sent_at": utc_iso(time.time()),
            "sync_interval_s": cfg["interval_alert"] if perf_level(row) else cfg["interval_normal"],
            "monitor_stopped": bool(stopped), "windows_in_last_sync": nrows,
            "session_started_at": utc_iso(iso_epoch(sess.get("start")) or t),
            "heartbeat": self.heartbeat_doc(not stopped),
            "monitor_version": VERSION, "timezone": clip(timezone_name(), RTDB_ID_MAX),
            # v2.8 (opcionais): sessão sem estes campos = Linux com monitoramento completo
            "platform": "windows" if sess.get("platform") == "windows" else "linux",
            "monitoring": "basico" if sess.get("monitoring") == "basico" else "completo",
        }
        if SERVICE["mode"]:                      # v2.13 (opcionais): início automático com o sistema
            doc["service"] = SERVICE["mode"]
            if SERVICE["note"]:
                doc["service_note"] = clip(SERVICE["note"], 256)
        if fs is not None:                       # schema 2: ocupação de cada filesystem real
            doc["filesystems"] = [{k: f[k] for k in ("mount", "device", "fstype", "total_bytes", "free_bytes", "used_pct")}
                                  for f in fs[:FS_MAX]]
        return clip(doc)

    def cfg_now(self, t=None):
        """Configuração de envio vigente: a local (sync_cfg) com as frequências da central na faixa de horário atual."""
        c = self.ident.sync_cfg()
        return self.acfg.apply(c, t) if self.acfg is not None else c

    def heartbeat_doc(self, running=True):
        """Sinal de vida + carga do instante (load), que explica um heartbeat atrasado (servidor
        sobrecarregado) mesmo sem janela nova. interval_s/offline_after_s: os vigentes (v2.11: podem mudar com a
        faixa de horário e a configuração da central; agent_config diz a origem)."""
        cfg = self.cfg_now()
        doc = {"at_ms": {".sv": "timestamp"}, "client_at": utc_iso(time.time()), "interval_s": cfg["heartbeat_interval"],
               "offline_after_s": cfg["offline_after"], "monitor_running": bool(running)}
        if self.acfg is not None:
            doc["agent_config"] = self.acfg.doc(cfg)
        if self.ncpu is None:
            self.ncpu = source().cpu_count()
        load = source().load_snapshot(self.ncpu)
        if load:
            doc["load"] = load
        return doc

    def event_doc(self, t, kv, row, dg, res, old, new, disks):
        g = lambda k: None if row.get(k) is None or row.get(k) != row.get(k) else round(row.get(k), 2)
        keys = {"cpu": ("cpu_avg", "cpu_max", "rq_avg", "psi_cpu", "st_avg", "hot_avg"),
                "mem": ("mem_avg", "mem_max", "swio", "psi_mem", "psi_mem_full"),
                "disk": ("psi_io", "psi_io_full"), "space": ("fs_used_max",)}[res]
        m = {k: g(k) for k in keys}
        if res == "disk":
            for d in disks:
                for k in ("util_avg", "await", "qd_avg", "iops_avg"):
                    m[rtdb_key(d) + "_" + k] = g(d + "." + k)
        doc = {**self.ident_doc(), "resource": res, "from": LEVEL_KEYS.get(old), "to": LEVEL_KEYS.get(new),
               "at": utc_iso(t), "at_ms": int(t * 1000), "window_s": float(kv.get("win") or 0),
               "message": dg[res][1], "metrics": m}
        w = row.get("_fs_worst")
        if res == "space" and w is not None:     # o filesystem que define o nível
            doc["mount"] = w["mount"]
            m.update(used_pct=w["used_pct"], free_bytes=w["free_bytes"], total_bytes=w["total_bytes"])
        return clip(doc)

    def info_doc(self, st, hwlines, bench=None):
        hw = {}
        for l in hwlines:
            if l.startswith("HW "):
                k, _, v = l[3:].partition(":")
                k, v = k.strip(), v.strip()
                if k == "fs":
                    fsl = hw.setdefault("filesystems", [])
                    if len(fsl) < HW_FS_MAX:
                        fsl.append(v)
                elif k == "uptime":
                    continue                              # muda sempre; não é identificação
                else:
                    hw[rtdb_key(k, 96)] = v              # disk.sda → disk_sda (o RTDB não aceita '.' em chaves)
        # último benchmark conhecido (live_sync), senão o do arquivo do GitHub, senão o da sessão atual
        src = next((b for b in (bench, st["bench"]) if b and b.get("lines")), {})
        lines = src.get("lines") or [l for l in hwlines if l.startswith("BENCH ")]
        # disk.sda.seq_read_MBs → disk_sda_seq_read_MBs (o relatório local continua com pontos)
        bench = {rtdb_key(k, 96): v for k, v in bench_dict(lines).items()}
        doc = clip({**self.ident_doc(), "monitor_version": VERSION, "timezone": clip(timezone_name(), RTDB_ID_MAX),
                    "hardware": hw, "benchmark": bench, "benchmark_measured": src.get("when", "")[:40]})
        h = hashlib.sha1(json.dumps(doc, sort_keys=True).encode()).hexdigest()
        doc["updated_at_ms"] = {".sv": "timestamp"}
        doc.update(self.sql_info)                     # info/<sid> é sobrescrito inteiro: a impressão digital vai junto
        return doc, h

    def heartbeat(self, running=True):
        """Sinal de vida independente de dados novos (status/<sid>/heartbeat)."""
        self.live.patch("status/%s/heartbeat" % self.ident.install_id, self.heartbeat_doc(running), timeout=15)

    def signals(self):
        """Avisos da central para esta instalação (signals/<sid>: release, config_at, catalog_at, agent_config_at) ou None."""
        return self.live.get("signals/" + self.ident.install_id, timeout=15)

    def rename_request(self):
        """Pedido de renome da central (rename/<sid>, v2.14) ou None."""
        return self.live.get("rename/" + self.ident.install_id, timeout=15)

    def rename_done(self, rid, error=""):
        """Confirma o pedido rid (applied_id/applied_at; error = recusado, vazio = aplicado). Só filhos do pedido:
        um pedido novo gravado no meio continua pendente (id diferente) e as regras recusam se ele foi cancelado."""
        self.live.patch("rename/" + self.ident.install_id,
                        {"applied_id": rid, "applied_at": {".sv": "timestamp"}, "error": clip(error, 256) or None}, timeout=15)

    def agent_config(self):
        """(agent_config/default, agent_config/servers/<sid>): dois GETs pequenos (v2.11)."""
        return (self.live.get("agent_config/default", timeout=15),
                self.live.get("agent_config/servers/" + self.ident.install_id, timeout=15))

    def prune(self, st, timeout=30):
        """Retenção na nuvem (1x por dia): apaga, só nos nós desta instalação, o que passou da
        idade configurada. Nunca apaga por ausência no relatório local."""
        L = st["live"]
        if time.time() - L.get("pruned_at", 0) < 86400:
            return 0
        cfg, sid, removed = self.ident.sync_cfg(), self.ident.install_id, 0
        for node, keep in (("history", cfg["retention_cloud_days"] * 86400), ("events", cfg["retention_events_days"] * 86400),
                           ("recent", cfg["recent_hours"] * 3600)):
            cut = '"%010d"' % int(time.time() - keep)
            for _ in range(20):
                old = self.live.get("%s/%s" % (node, sid), {"orderBy": '"$key"', "endAt": cut, "limitToFirst": "500"},
                                    timeout=timeout) or {}
                if not old:
                    break
                self.live.patch("", {"%s/%s/%s" % (node, sid, k): None for k in old}, timeout=timeout)
                removed += len(old)
        L["pruned_at"] = time.time()
        return removed


LEVEL_KEYS = {0: "NORMAL", 1: "ATENCAO", 2: "CRITICO"}
RTDB_KEY_BAD = re.compile(r"[^A-Za-z0-9_!-]")
RTDB_STR_MAX, RTDB_ID_MAX = 1024, 256         # limites de texto das regras do banco (firebase/database.rules.json)
HW_FS_MAX = 32                                # linhas "fs" do hardware enviadas em info/<sid>


def rtdb_key(k, maxlen=64):
    """Chave aceita pelo RTDB e pelas regras: '.', '$', '#', '[', ']', '/' (recusados pelo banco, que
    devolve 400 e perde o envio inteiro) e qualquer outro caractere fora de [A-Za-z0-9_!-] viram '_'."""
    return RTDB_KEY_BAD.sub("_", k)[:maxlen] or "_"


def clip(v, n=RTDB_STR_MAX):
    """Textos dentro do limite das regras (contado como no JavaScript, em unidades UTF-16),
    recursivo em mapas e listas."""
    if isinstance(v, str):
        v = v[:n]
        while len(v.encode("utf-16-le")) > 2 * n:
            v = v[:-1]
        return v
    if isinstance(v, dict):
        return {k: clip(x, n) for k, x in v.items()}
    if isinstance(v, list):
        return [clip(x, n) for x in v]
    return v


def compact_row(row, kv, disks):
    """recent/<sid>/<ts>: uma janela, resolução total (para gráficos recentes no Central)."""
    def g(k, n=1):
        v = row.get(k)
        return None if v is None or v != v else round(v, n)
    us = [row.get(d + ".util_avg") for d in disks if row.get(d + ".util_avg") is not None]
    aws = [row.get(d + ".await") for d in disks if row.get(d + ".await") is not None]
    d = {"w": float(kv.get("win") or 0), "c": g("cpu_avg"), "cm": g("cpu_max"), "q": g("rq_avg"),
         "pc": g("psi_cpu", 2), "st": g("st_avg"), "m": g("mem_avg"), "sw": g("swio"), "pm": g("psi_mem", 2),
         "pi": g("psi_io", 2), "u": round(max(us), 1) if us else None, "aw": round(max(aws), 2) if aws else None,
         "lv": [None if row[k] != row[k] else int(row[k]) for k in ("lv_cpu", "lv_mem", "lv_disk")]}
    if g("fs_used_max") is not None:            # schema 2 (opcionais): maior % ocupado e nível de espaço
        d["fs"] = g("fs_used_max")
    ls = row.get("lv_space")
    if ls is not None and ls == ls:
        d["ls"] = int(ls)
    return d


ROLL_AVG = ("cpu_avg", "rq_avg", "psi_cpu", "st_avg", "mem_avg", "swio", "psi_mem", "psi_io")
ROLL_MAX = ("cpu_max", "rq_max", "mem_max", "psi_io_max", "psi_cpu_max")


def bucket_add(b, start, row, kv, disks):
    """Acumula uma janela no agregado de 5 min (média ponderada pela duração e máximos)."""
    b = b or {"b": start, "n": 0, "w": 0.0, "s": {}, "x": {}, "lv": [None, None, None]}
    w = float(kv.get("win") or 0) or 1.0
    b["n"] += 1
    b["w"] += w
    for k in ROLL_AVG:
        v = row.get(k)
        if v is not None and v == v:
            b["s"][k] = b["s"].get(k, 0.0) + v * w
            b["s"]["w_" + k] = b["s"].get("w_" + k, 0.0) + w
    vals = dict((k, row.get(k)) for k in ROLL_MAX)
    us = [row.get(d + ".util_avg") for d in disks if row.get(d + ".util_avg") is not None]
    um = [row.get(d + ".util_max") for d in disks if row.get(d + ".util_max") is not None]
    aw = [row.get(d + ".await") for d in disks if row.get(d + ".await") is not None]
    if us:
        b["s"]["u"] = b["s"].get("u", 0.0) + max(us) * w
        b["s"]["w_u"] = b["s"].get("w_u", 0.0) + w
    vals.update(um=max(um) if um else None, aw=max(aw) if aw else None)
    for k, v in vals.items():
        if v is not None and v == v and (k not in b["x"] or v > b["x"][k]):
            b["x"][k] = v
    for i, k in enumerate(("lv_cpu", "lv_mem", "lv_disk")):
        v = row.get(k)
        if v is not None and v == v and (b["lv"][i] is None or v > b["lv"][i]):
            b["lv"][i] = int(v)
    v, f = row.get("lv_space"), row.get("fs_used_max")   # espaço (schema 2): chaves à parte, lv continua com 3
    if v is not None and v == v and (b.get("ls") is None or v > b["ls"]):
        b["ls"] = int(v)
    if f is not None and f == f and (b.get("fsm") is None or f > b["fsm"]):
        b["fsm"] = f
    return b


def bucket_doc(b):
    """history/<sid>/<início do bloco>: agregado de 5 min (médias, picos e pior nível)."""
    s, x = b["s"], b["x"]
    avg = lambda k: round(s[k] / s["w_" + k], 2) if s.get("w_" + k) else None
    names = {"cpu_avg": "c", "rq_avg": "q", "psi_cpu": "pc", "st_avg": "st", "mem_avg": "m", "swio": "sw",
             "psi_mem": "pm", "psi_io": "pi"}
    d = {short: avg(k) for k, short in names.items()}
    d.update(u=avg("u"), cm=x.get("cpu_max"), qm=x.get("rq_max"), mm=x.get("mem_max"), pim=x.get("psi_io_max"),
             pcm=x.get("psi_cpu_max"), um=x.get("um"), aw=round(x["aw"], 2) if x.get("aw") is not None else None,
             lv=b["lv"], n=b["n"], w=round(b["w"], 1))
    for k in ("fsm", "ls"):
        if b.get(k) is not None:
            d[k] = b[k]
    return d


# --------------------------------------------------------------------------
# Frequências definidas pela central (v2.11, contrato em docs/CONTRATO_RTDB.md): agent_config/default (padrão
# global) + agent_config/servers/<sid> (exceção, campo a campo). Ausente = padrão local do agente.
# --------------------------------------------------------------------------
AGENT_CFG_FILE = "agent_config.json"     # SYNC_DIR/agent_config.json: última configuração aplicada (vale na partida)
AGENT_CFG_REFRESH = 6 * 3600             # s entre releituras de garantia (o aviso signals/<sid>/agent_config_at antecipa)
AGENT_CFG_RETRY = 300                    # s até tentar de novo uma leitura que falhou
AGENT_SCHEDULE_DEFAULT = ("12345", "6-20")   # horário comercial sem schedule: seg-sex, 6h-20h (hora local)
AGENT_CFG_INTS = {("biz", "heartbeat_s"): (30, 3600), ("biz", "status_s"): (60, 3600),
                  ("off", "heartbeat_s"): (30, 3600), ("off", "status_s"): (60, 3600),
                  ("collect", "biz_interval_s"): (10, 300), ("collect", "interval_s"): (60, 3600),
                  ("update", "interval_s"): (300, 86400)}
AGENT_CFG_STRS = (("schedule", "days"), ("schedule", "hours"), ("collect", "biz_hours"), ("update", "window"))
HOURS_RE = re.compile(r"^([0-9]|1[0-9]|2[0-3])-([0-9]|1[0-9]|2[0-4])$")


def hours_range(v, wrap=False):
    """'6-20' -> (6, 20); None se inválido. Sem wrap exige início < fim; com wrap (janela de atualização) aceita
    início > fim, atravessando a meia-noite ('22-6')."""
    m = HOURS_RE.match(v) if isinstance(v, str) else None
    if not m:
        return None
    a, b = int(m.group(1)), int(m.group(2))
    return (a, b) if a < b or (wrap and a != b and b < 24) else None


def in_hours(h, rng):
    a, b = rng
    return a <= h < b if a < b else (h >= a or h < b)


def agent_cfg_merge(default, server):
    """Seções do default com as da exceção por cima, campo a campo (merge profundo pela chave folha)."""
    out = {}
    for src in (default, server):
        for sec, d in (src.items() if isinstance(src, dict) else ()):
            if isinstance(d, dict):
                out.setdefault(sec, {}).update(d)
    return out


def agent_cfg_clean(merged, sample=5):
    """(configuração válida {seção: {campo: valor}}, campos ignorados). Fora dos limites/formato = ignorado (só esse
    campo; vale o padrão local). collect: múltiplo da amostra e divisor de 3600 (janelas alinhadas ao relógio)."""
    clean, bad = {}, []
    for sec in sorted(merged):
        for k in sorted(merged[sec]):
            v = merged[sec][k]
            if (sec, k) in AGENT_CFG_INTS:
                lo, hi = AGENT_CFG_INTS[(sec, k)]
                ok = is_int(v) and lo <= v <= hi and (sec != "collect" or (v % max(1, sample) == 0 and 3600 % v == 0))
            elif (sec, k) == ("schedule", "days"):
                ok = isinstance(v, str) and re.match(r"^[1-7]{1,7}$", v) is not None and len(set(v)) == len(v)
            elif (sec, k) == ("update", "window"):
                ok = v == "" or hours_range(v, wrap=True) is not None
            elif (sec, k) in AGENT_CFG_STRS:
                ok = hours_range(v) is not None
            elif (sec, k) == ("sql", "relays"):         # editor SQL (v2.12): relays permitidos, em ordem
                ok = sql_relays_parse(v) is not None
            else:
                ok = False                       # campo desconhecido (as regras já recusam)
            if ok:
                clean.setdefault(sec, {})[k] = v
            else:
                bad.append(sec + "." + k)
    return clean, bad


class AgentConfig:
    """Frequências definidas pela central, já validadas (cfg), com a origem (source 'central'|'padrao') e o
    updated_at aplicado (at, ms). apply() devolve a configuração de envio vigente AGORA (faixa biz/off pelo horário
    local): heartbeat, status normal, offline_after = max(local, 3 x heartbeat; olhando também a faixa do próximo
    heartbeat, para a troca de faixa não parecer queda) e intervalo da autoatualização. collect só vale na
    partida do coletor (apply_collect): mudou -> restart_needed() pede o reinício controlado.
    Cópia em SYNC_DIR/agent_config.json (atômica, 600): na partida já vale a última configuração recebida."""

    def __init__(self, path, sample=5):
        self.path, self.sample = path, sample
        self.cfg, self.source, self.at, self.ignored = {}, "padrao", None, []
        self.cli = self.running = None          # coleta da linha de comando / em uso (só no coletor)
        self.persisted = True                   # a última configuração está na cópia em disco (vale no reinício)
        self.out = None
        d = read_json(path) if path else None
        if isinstance(d, dict) and isinstance(d.get("cfg"), dict):
            self.cfg, _ = agent_cfg_clean({k: v for k, v in d["cfg"].items() if isinstance(v, dict)}, sample)
            self.source = "central" if d.get("source") == "central" else "padrao"
            self.at = d.get("at") if is_num(d.get("at")) else None
            self.ignored = [x for x in d.get("ignored") or [] if isinstance(x, str)][:50]

    def say(self, msg):
        if self.out:
            self.out(msg)

    def get(self, sec, key, default=None):
        return (self.cfg.get(sec) or {}).get(key, default)

    def band(self, t=None):
        """'biz' (dia útil e hora dentro do horário comercial, no fuso local) ou 'off'."""
        lt = time.localtime(t)
        days = self.get("schedule", "days", AGENT_SCHEDULE_DEFAULT[0])
        rng = hours_range(self.get("schedule", "hours", AGENT_SCHEDULE_DEFAULT[1]))
        return "biz" if str(lt.tm_wday + 1) in days and in_hours(lt.tm_hour, rng) else "off"

    def apply(self, cfg, t=None):
        """cfg (Identity.sync_cfg) com os valores vigentes da central em t (padrão: agora)."""
        t = time.time() if t is None else t
        band = self.band(t)
        out = dict(cfg)
        hb = self.get(band, "heartbeat_s", cfg["heartbeat_interval"])
        nxt = self.get(self.band(t + hb), "heartbeat_s", cfg["heartbeat_interval"])
        out.update(heartbeat_interval=hb, interval_normal=self.get(band, "status_s", cfg["interval_normal"]),
                   offline_after=max(cfg["offline_after"], 3 * max(hb, nxt)),
                   update_interval=self.get("update", "interval_s", cfg["update_interval"]), band=band)
        return out

    def doc(self, cfg):
        """heartbeat.agent_config: origem, updated_at aplicado, faixa e status vigentes (a central mostra 'aplicado')."""
        d = {"source": self.source, "band": cfg.get("band", "off"), "status_s": cfg["interval_normal"]}
        if self.at is not None:
            d["at"] = self.at
        if self.ignored:
            d["ignored"] = clip(",".join(self.ignored), 512)
        return d

    def window_wait(self, t=None):
        """s até abrir a janela de autoatualização (update.window); 0 = dentro dela ou sem janela."""
        rng = hours_range(self.get("update", "window", ""), wrap=True)
        if rng is None:
            return 0
        lt = time.localtime(t)
        if in_hours(lt.tm_hour, rng):
            return 0
        return ((rng[0] - lt.tm_hour) % 24) * 3600 - lt.tm_min * 60 - lt.tm_sec

    def set(self, default, server):
        """Aplica o que foi lido do Firebase. Devolve as seções que mudaram (lista, talvez vazia)."""
        cfg, bad = agent_cfg_clean(agent_cfg_merge(default, server), self.sample)
        docs = [x for x in (default, server) if isinstance(x, dict)]
        ats = [x["updated_at"] for x in docs if is_num(x.get("updated_at"))]
        source, at = ("central" if docs else "padrao"), (max(ats) if ats else None)
        changed = sorted(k for k in set(cfg) | set(self.cfg) if cfg.get(k) != self.cfg.get(k))
        if bad and bad != self.ignored:
            self.say("Configuração da central: ignorado (fora dos limites): " + ", ".join(bad))
        dirty = changed or (source, at, bad) != (self.source, self.at, self.ignored)
        self.cfg, self.source, self.at, self.ignored = cfg, source, at, bad
        if changed:
            self.say("Configuração da central aplicada (%s): %s" % (source, ", ".join(changed)))
        if dirty and self.path:
            try:
                os.makedirs(os.path.dirname(self.path), mode=0o700, exist_ok=True)
                write_private(self.path, json.dumps({"cfg": cfg, "source": source, "at": at, "ignored": bad},
                                                    separators=(",", ":")))
                self.persisted = True
            except OSError:
                self.persisted = False           # sem cópia: na próxima partida lê do Firebase de novo
        return changed

    def collect_wanted(self):
        c = self.cfg.get("collect") or {}
        return {"biz_hours": c.get("biz_hours", self.cli["biz_hours"]),
                "biz_interval": c.get("biz_interval_s", self.cli["biz_interval"]),
                "interval": c.get("interval_s", self.cli["interval"])}

    def apply_collect(self, a):
        """Partida do coletor: guarda a coleta da linha de comando e põe por cima a da central (última recebida).
        O SESSION do relatório registra os valores em uso (contrato do relatório inalterado)."""
        self.cli = {"biz_hours": a.biz_hours, "biz_interval": a.biz_interval, "interval": a.interval}
        w = self.running = self.collect_wanted()
        a.biz_hours, a.biz_interval, a.interval = w["biz_hours"], w["biz_interval"], w["interval"]
        a.biz_start, a.biz_end = hours_range(w["biz_hours"]) or (a.biz_start, a.biz_end)

    def restart_needed(self):
        """A coleta pedida pela central difere da em uso (só no coletor): reiniciar para gravar um SESSION novo.
        Sem a cópia em disco não reinicia: o processo novo não saberia a coleta nova e reiniciaria sem parar."""
        return self.running is not None and self.persisted and self.collect_wanted() != self.running


class SyncManager:
    """Agenda os envios sem nunca bloquear a coleta: um único worker, pedidos consolidados.

    Status ao vivo: a cada interval_normal com o servidor normal (só se houver janela nova);
    a cada janela gravada (>= interval_alert) em ATENÇÃO/CRÍTICO; imediato ao entrar em alerta e
    ao voltar ao normal. Histórico (GitHub): a cada history_interval, nas mudanças de estado
    (no máximo a cada HIST_MIN_GAP) e no pedido manual. Falhas: nova tentativa com espera
    crescente (30 s, 60 s... até 15 min, ou o tempo pedido pelo GitHub). O estado só avança
    depois do sucesso, então janelas acumuladas na falha vão juntas no envio seguinte.

    Heartbeat: thread própria e leve ('sinal'), que não depende do worker. Num servidor sobrecarregado
    (E/S lenta) o worker pode passar minutos lendo o relatório ou enviando ao GitHub; o sinal de vida
    continua saindo a cada heartbeat_interval. Não usa a trava de sessão nem o state.json (só a
    memória, sob self.lock, e o pequeno arquivo em RAM de hb_path(); nada no disco); falhas têm espera própria e curta (HB_BACKOFF).

    Avisos da central (v2.6.1): depois de cada heartbeat, a mesma thread lê signals/<sid> (um GET pequeno, sem
    disco; falha ignorada, sem mexer no backoff do heartbeat). release maior que VERSION acorda o Updater;
    config_at/catalog_at diferentes do último visto acordam o DbAgent. A 1ª leitura só registra os valores.

    Frequências da central (v2.11, AgentConfig em cloud.acfg): agent_config lido no 1º heartbeat, quando
    signals/<sid>/agent_config_at muda e a cada AGENT_CFG_REFRESH. eff() = configuração vigente na faixa de horário
    atual (heartbeat, status normal, offline_after); configuração nova manda um heartbeat já; coleta diferente da
    em uso chama on_restart (reinício controlado do coletor)."""

    def __init__(self, cloud, auto=True):
        self.cloud = cloud
        self.cfg = cloud.ident.sync_cfg()
        self.auto = auto and self.cfg["auto"] and cloud.configured()
        self.ev, self.stop_ev = threading.Event(), threading.Event()
        self.lock = threading.Lock()
        self.want = {"live": False, "hist": False, "force": False}
        self.alert, self.level, self.space = False, None, None
        self.last = {"live": 0.0, "hist": 0.0}       # último envio confirmado
        self.retry = {"live": 0.0, "hist": 0.0}      # não tentar antes disso (backoff)
        self.fails = {"live": 0, "hist": 0}
        self.thread = self.oneshot = self.hb_thread = None
        self.busy = False
        self.last_hb = 0.0                            # último heartbeat confirmado (ou status, que o leva)
        self.hb = {"fails": 0, "retry": 0.0, "fail_at": 0.0, "msg": ""}
        self._live_ok = False
        self.hb_lock = threading.Lock()               # um envio de heartbeat por vez (o final do stop por último)
        self.updater = self.db = None                 # avisados por signals/<sid> (ligados pelo main)
        self.signals_seen, self.signals_at = None, 0.0   # últimos valores lidos (None = ainda não leu) e quando
        self.acfg_next = 0.0                          # próxima leitura de agent_config (0 = na partida)
        self.hb_force = False                         # configuração nova: heartbeat já (anuncia interval/offline novos)
        self.on_restart = None                        # coleta mudou pela central: reinício controlado (ligado pelo main)
        self.rename_next = 0.0                        # próxima leitura de rename/<sid> (0 = no 1º heartbeat)
        self.on_rename = None                         # renome aplicado: avisa o painel/coletor (ligado pelo main)

    def eff(self):
        """Configuração vigente: self.cfg com as frequências da central na faixa de horário atual (v2.11)."""
        acfg = getattr(self.cloud, "acfg", None)
        return acfg.apply(self.cfg) if acfg is not None else self.cfg

    def start(self):
        if self.thread is None:
            self.thread = threading.Thread(target=self.loop, name="nuvem", daemon=True)
            self.thread.start()
        if self.hb_thread is None and self.auto and self.cloud.live.configured():
            self.hb_thread = threading.Thread(target=self.hb_loop, name="sinal", daemon=True)
            self.hb_thread.start()

    def hb_loop(self):
        """Thread do heartbeat: acorda a cada HB_POLL s; beat() decide se já é hora."""
        while not self.stop_ev.is_set():
            try:
                self.beat()
            except Exception:
                pass                                  # nunca derruba a thread
            self.stop_ev.wait(HB_POLL)

    def on_window(self, level, space=None, first=False):
        """Chamado pela coleta logo após gravar cada janela (só sinaliza; não faz rede).
        level = pior nível de CPU/memória/disco (define o ritmo de envio); space = nível de
        ocupação dos filesystems: só a mudança dele antecipa um envio (não acelera o ritmo).
        first = 1ª janela (curta) da sessão: envia já, para a central sair de "sem dados"."""
        alert = level is not None and level >= 1
        with self.lock:
            prev, prev_sp = self.level, self.space
            self.level, self.alert, self.space = level, alert, space
            # qualquer mudança de nível (inclusive ATENÇÃO -> CRÍTICO) ou partida já em alerta
            changed = (prev is not None and level is not None and level != prev) or (prev is None and alert)
            sp_changed = (prev_sp is not None and space is not None and space != prev_sp) or (
                prev_sp is None and space is not None and space >= 1)
            if sp_changed and not changed:
                changed, alert = True, space >= 1
            if first:
                self.want["live"] = True
            if changed and ((alert and self.cfg["send_on_alert"]) or (not alert and self.cfg["send_on_recover"])):
                self.want["live"] = True
                if time.time() - self.last["hist"] > HIST_MIN_GAP:
                    self.want["hist"] = True
        self.ev.set()

    def manual(self):
        """Tecla u: envia tudo agora (histórico + status), sem conflitar com o envio automático."""
        with self.lock:
            self.want.update(live=True, hist=True, force=True)
            self.retry = {"live": 0.0, "hist": 0.0}
        if self.thread is not None:                   # agendador ativo: ele atende o pedido
            self.ev.set()
            return True
        if self.oneshot is not None and self.oneshot.is_alive():
            return False
        self.oneshot = threading.Thread(target=self.tick, name="nuvem", daemon=True)   # --view: roda uma vez
        self.oneshot.start()
        return True

    def loop(self):
        st = self.cloud.load_state()
        self.last["hist"] = st["status"].get("at", 0) if st["status"].get("state") == "ok" else 0
        self.last["live"] = st["live"]["status"].get("at", 0) if st["live"]["status"].get("state") == "ok" else 0
        with self.lock:
            self.want["live"] = True                  # na partida: envia o que ficou pendente
        self.ev.set()
        while not self.stop_ev.is_set():
            self.ev.wait(5)
            self.ev.clear()
            if self.stop_ev.is_set():
                break
            try:
                self.tick()
            except Exception:
                pass                                  # nunca derruba o worker (o erro fica no estado)

    def due(self, now):
        c = self.eff()
        live = self.cloud.live.configured() and now >= self.retry["live"] and (
            self.want["live"] or (self.auto and now - self.last["live"] >= (c["interval_alert"] if self.alert else c["interval_normal"]) - 1))
        hist = self.cloud.hist_on() and now >= self.retry["hist"] and (
            self.want["hist"] or (self.auto and now - self.last["hist"] >= c["history_interval"]))
        return live, hist

    def tick(self):
        now = time.time()
        with self.lock:
            live, hist = self.due(now)
            force = self.want["force"]
        if not (live or hist):
            return
        self.busy = True
        try:
            with self.cloud.session(durable=hist) as st:
                if hist:
                    self.attempt("hist", st, lambda: self.cloud.hist_sync(st))
                if live:
                    self.attempt("live", st, lambda: self.cloud.live_sync(st, force=force or hist))
                    if self.fails["live"] == 0:
                        self.hb_ok()                        # o status enviado já leva o heartbeat
                        if getattr(self.cloud, "more", False):
                            with self.lock:
                                self.want["live"] = True    # primeira sincronização: próximo lote logo
                            self.ev.set()
                        try:
                            self.cloud.prune(st)
                        except CloudError:
                            pass                            # tenta de novo no próximo envio
        except BusyError:
            self.retry["live"] = self.retry["hist"] = time.time() + 10     # envio manual de outro processo
        finally:
            self.busy = False

    def attempt(self, ch, st, fn):
        with self.lock:
            self.want[ch] = False
            if ch == "live":
                self.want["force"] = False
        try:
            n = fn()
            self.last[ch], self.fails[ch], self.retry[ch] = time.time(), 0, 0.0
            if ch == "live":
                st["live"]["status"] = {"state": "ok", "at": time.time(), "pending": 0,
                                        "msg": "%d janela(s) enviada(s)" % n if n else "sem novidades"}
        except CloudError as e:
            self.fails[ch] += 1
            wait = getattr(e, "retry_after", None) or min(900, 30 * 2 ** (self.fails[ch] - 1))
            self.retry[ch] = time.time() + wait
            if ch == "live":
                st["live"]["status"] = {"state": "erro", "at": time.time(), "msg": str(e),
                                        "pending": self.live_pending(st), "retry_at": self.retry[ch]}
            else:
                st["status"]["retry_at"] = self.retry[ch]

    def beat(self):
        """Heartbeat: sinal de vida a cada heartbeat_interval, mesmo sem dados novos (thread 'sinal').
        Espera própria após falha (15 s, 30 s, 60 s...), independente da do envio de dados. Depois do
        heartbeat (ou, em alerta, quando o status enviado já o levou), lê os avisos da central."""
        if not (self.auto and self.live_ok()):
            return False
        sent = self.send_beat()
        hb = self.eff()["heartbeat_interval"]
        with self.lock:
            due = sent or (self.hb["fails"] == 0 and self.last_hb > 0 and time.time() - self.signals_at >= hb)
        if due and not self.stop_ev.is_set():
            self.check_signals()
        if sent and time.time() >= self.acfg_next and not self.stop_ev.is_set():
            self.refresh_agent_cfg()                  # na partida e a cada AGENT_CFG_REFRESH (garantia)
        if sent and time.time() >= self.rename_next and not self.stop_ev.is_set():
            self.check_rename()                       # na partida (pedido feito com o agente offline) e a cada 6 h
        return sent

    def refresh_agent_cfg(self):
        """Lê agent_config/default + servers/<sid> e aplica (v2.11). Frequências: valem já (e o próximo heartbeat
        sai logo, com interval_s/offline_after_s novos); coleta diferente da em uso: pede o reinício controlado.
        Falha: tenta de novo em AGENT_CFG_RETRY (recusa das regras, ainda sem o nó: só na próxima garantia)."""
        acfg = getattr(self.cloud, "acfg", None)
        if acfg is None:
            return None
        try:
            default, server = self.cloud.agent_config()
        except Exception as e:                        # nunca atrapalha o heartbeat
            self.acfg_next = time.time() + (AGENT_CFG_REFRESH if getattr(e, "denied", False) else AGENT_CFG_RETRY)
            return None
        self.acfg_next = time.time() + AGENT_CFG_REFRESH
        changed = acfg.set(default, server)
        if changed:
            with self.lock:
                self.hb_force = True
        if acfg.restart_needed() and self.on_restart is not None:
            self.on_restart()
        return changed

    def check_signals(self):
        """Lê signals/<sid> e acorda quem precisa: Updater (release maior que VERSION, quando muda) e DbAgent
        (config_at/catalog_at mudaram). Qualquer falha (rede, regras ainda sem o nó: 401/403) é ignorada."""
        self.signals_at = time.time()
        try:
            doc = self.cloud.signals()
        except Exception:                             # nunca atrapalha o heartbeat
            return None
        doc = doc if isinstance(doc, dict) else {}
        cur = {k: doc.get(k) for k in SIGNAL_KEYS}
        prev, self.signals_seen = self.signals_seen, cur
        if prev is None:
            return None                               # 1ª leitura depois de iniciar: só registra
        woke = []
        rel = cur["release"]
        if (rel != prev["release"] and isinstance(rel, str) and version_tuple(rel) > version_tuple(VERSION)
                and self.updater is not None):
            self.updater.wake(rel)
            woke.append("updater")
        if self.db is not None and (cur["config_at"], cur["catalog_at"]) != (prev["config_at"], prev["catalog_at"]):
            self.db.wake()
            woke.append("db")
        if cur["agent_config_at"] != prev["agent_config_at"]:
            self.refresh_agent_cfg()
            woke.append("agent_config")
        if cur["rename_at"] != prev["rename_at"]:
            self.check_rename()
            woke.append("rename")
        return woke

    def check_rename(self):
        """Renome pedido pela central (v2.14, rename/<sid>): {id, company?, name?, ...}. Pendente = id diferente de
        applied_id. Valida como --empresa/--nome (clean_name, não vazio), grava em server_monitor.json (company_id
        preservado), confirma (applied_id/applied_at, error se recusado) e pede um envio do status (os campos
        company/name mudam; o info/<sid> é regravado porque a identificação mudou). Idempotente: se a confirmação
        falhar, a próxima leitura aplica de novo (sem mudança) e confirma. Falha de rede/regras: tenta em RENAME_RETRY.
        Devolve 'aplicado', 'recusado', None (nada pendente) ou 'falha'."""
        self.rename_next = time.time() + RENAME_REFRESH
        try:
            doc = self.cloud.rename_request()
        except Exception:                             # nunca atrapalha o heartbeat (regras antigas: 401/403)
            self.rename_next = time.time() + RENAME_RETRY
            return "falha"
        if not isinstance(doc, dict):
            return None
        rid = doc.get("id")
        if not isinstance(rid, str) or not rid or doc.get("applied_id") == rid:
            return None
        vals, error = {}, ""
        for k in ("company", "name"):
            v = doc.get(k)
            if v is None:
                continue
            c = clean_name(v) if isinstance(v, str) else ""
            if not c:
                error = "%s inválido: precisa ser um texto não vazio" % ("empresa" if k == "company" else "nome")
            vals[k] = c
        if not vals and not error:
            error = "pedido sem empresa nem nome"
        changed = False
        if not error:
            try:
                changed = self.cloud.ident.rename(**vals)
            except OSError:                           # disco: não confirma; tenta de novo depois
                self.rename_next = time.time() + RENAME_RETRY
                return "falha"
        try:
            self.cloud.rename_done(rid, error)
        except Exception:
            self.rename_next = time.time() + RENAME_RETRY
            if error:
                return "falha"
        if error:
            return "recusado"
        if changed:
            with self.lock:
                self.want.update(live=True, force=True)   # já, mesmo sem janela nova: status e info com os nomes novos
                self.hb_force = True
            self.ev.set()
            if self.on_rename is not None:
                self.on_rename()
        return "aplicado"

    def send_beat(self):
        now = time.time()
        hb = self.eff()["heartbeat_interval"]
        with self.lock:
            if now < self.hb["retry"] or (now - self.last_hb < hb and not self.hb_force):
                return False
            self.hb_force = False
        with self.hb_lock:
            if self.stop_ev.is_set():
                return False                          # parando: o stop() publica o heartbeat final
            try:
                self.cloud.heartbeat(True)
            except CloudError as e:
                with self.lock:
                    self.hb["fails"] += 1
                    wait = getattr(e, "retry_after", None) or HB_BACKOFF * 2 ** (self.hb["fails"] - 1)
                    self.hb.update(retry=time.time() + min(HB_BACKOFF_MAX, wait), fail_at=time.time(), msg=str(e)[:200])
                self.hb_save()
                return False
        self.hb_ok()
        return True

    def live_ok(self):
        """Firebase configurado? Lido uma vez e guardado: a thread do sinal não consulta o disco."""
        if not self._live_ok:
            self._live_ok = self.cloud.live.configured()
        return self._live_ok

    def hb_ok(self):
        with self.lock:
            self.last_hb = time.time()
            self.hb.update(fails=0, retry=0.0)
        self.hb_save()

    def hb_path(self):
        return live_path(self.cloud.log) + HB_SUFFIX

    def hb_save(self):
        """Estado do heartbeat para o painel --view, em RAM (/dev/shm): no disco, com o storage travado
        (Cescom: PSI io full ~30%), criar/renomear um arquivo prende a thread do sinal por minutos."""
        with self.lock:
            doc = {"ok_at": self.last_hb, "fails": self.hb["fails"], "fail_at": self.hb["fail_at"], "msg": self.hb["msg"],
                   "http": FB_HTTP.snapshot()}       # conexões ao Firebase (o --diagnostico mostra)
        try:
            with open(self.hb_path(), "w") as f:
                f.write(json.dumps(doc))
        except OSError:
            pass

    def hb_info(self):
        """Estado do heartbeat: da memória se este processo envia; senão do arquivo em RAM de hb_path() (--view)."""
        if self.hb_thread is not None:
            with self.lock:
                return {"ok_at": self.last_hb, "fails": self.hb["fails"]}
        try:
            with open(self.hb_path()) as f:
                d = json.load(f)
            return d if isinstance(d, dict) else {}
        except (OSError, ValueError):
            return {}

    def live_pending(self, st):
        """Janelas gravadas e ainda não confirmadas no status ao vivo (estimativa barata)."""
        try:
            return max(0, int((os.path.getsize(self.cloud.log) - st["live"]["offset"]) // 900))
        except OSError:
            return 0

    def stop(self, final=True):
        """Para o worker e a thread do heartbeat e tenta publicar, com prazo curto, que o monitor parou.
        Com stop_ev ligado nenhum heartbeat 'rodando' começa, e hb_lock espera o que estiver em curso:
        o 'monitor parado' é sempre o último a chegar."""
        self.stop_ev.set()
        self.ev.set()
        for th in (self.thread, self.hb_thread):
            if th is not None and th is not threading.current_thread():
                th.join(15)
        if final and self.cloud.live.configured():
            with self.hb_lock:
                try:
                    with self.cloud.session(durable=True) as st:
                        self.cloud.live_sync(st, force=True, timeout=8, max_chunks=1)
                        self.cloud.heartbeat(False)
                        st["live"]["status"] = {"state": "ok", "at": time.time(), "pending": 0, "msg": "monitor parado"}
                except CloudError:
                    pass

    def summary(self):
        """(texto, nível) do estado real da nuvem para o painel: 'ok', 'enviando', 'erro', 'nunca' ou ''."""
        if not self.cloud.configured():
            return "", ""
        if not self.cloud.live.configured():
            return "FIREBASE NÃO CONFIGURADO: rode --firebase-setup", "erro"
        hb = self.hb_info()
        if hb.get("fails") and time.time() - (hb.get("ok_at") or 0) > self.eff()["offline_after"]:
            return "NUVEM: FALHA · sinal de vida atrasado", "erro"   # o Central já mostra 'sem comunicação'
        # no coletor, o estado em memória do último envio (o painel pergunta a cada 2 s; sem ler arquivo)
        st = self.cloud.mem_state if self.thread is not None and self.cloud.mem_state is not None else self.cloud.load_state()
        chans = []
        if self.cloud.live.configured():
            chans.append(st["live"]["status"])
        if self.cloud.hist_on():
            chans.append(st["status"])
        if self.busy or any(c.get("state") == "enviando" and time.time() - c.get("at", 0) < 120 for c in chans):
            return "NUVEM: enviando", "enviando"
        errs = [c for c in chans if c.get("state") == "erro"]
        if errs:
            pend = sum(int(c.get("pending") or 0) for c in errs)
            return "NUVEM: FALHA" + (" · %d pendente%s" % (pend, "s" if pend != 1 else "") if pend else ""), "erro"
        oks = [c.get("at", 0) for c in chans if c.get("state") == "ok"]
        if oks:
            return "NUVEM: OK · último envio %s" % time.strftime("%H:%M", stime(max(oks))), "ok"
        return ("NUVEM: aguardando 1º envio" if self.auto else "u envia p/ nuvem"), "nunca"


# --------------------------------------------------------------------------
# Acesso remoto ao Postgres local (v2.6): a central pede, o agente executa
# operações de um catálogo assinado (docs/PROPOSTA_BANCO.md, §4.1, §9 e §10)
# --------------------------------------------------------------------------
CATKEY_FILE = "server_monitor.catkey"           # chave do catálogo (64 hex = 32 bytes), permissão 600
DB_AUDIT_FILE = "server_monitor_db_audit.log"   # auditoria local: uma linha JSON por pedido (600)
DB_SUFFIX = ".db"               # live_path(log) + DB_SUFFIX, em RAM: estado para o painel e pedidos em execução
DB_DEFAULTS = {"host": "127.0.0.1", "port": 5432, "dbname": "afv", "user": "admin", "password": "admin",
               "sslmode": "prefer"}  # conexão usada enquanto a central não grava db_config/{sid} (v2.7.1)
DB_REFRESH = 600                # s entre verificações de db_config/updated_at e db_catalog/sig
DB_RETRY = 60                   # s até tentar de novo uma leitura do Firebase que falhou
DB_KEY_CHECK = 5                # s entre verificações (stat) do arquivo da chave (tecla k no --view, --catalogo-chave)
DB_IDLE = 60                    # s ociosa até fechar a conexão com o Postgres
DB_EXPIRE = 60                  # s: pedido mais velho que isso (pela hora do Firebase) não é executado
DB_TIMEOUT_MS = 10000           # statement_timeout de cada operação
DB_MAX_ROWS = 500               # linhas por resposta (max_linhas do catálogo não passa disso)
DB_MAX_JSON = 262144            # tamanho máximo de rows_json (unidades UTF-16, como nas regras)
DB_MAX_COLS = 100
DB_MAX_MSG = 16 << 20           # mensagem do Postgres acima disso = resposta grande demais (fecha a conexão)
DB_TEXT_MAX = 2000              # tamanho padrão de um parâmetro texto (limite das regras de db_requests)
DB_RESP_KEEP = 86400            # respostas apagadas depois de 24 h
DB_AUDIT_KEEP = 180 * 86400     # auditoria no Firebase: 180 dias
DB_PRUNE_EVERY = 86400
DB_PRUNE_FIRST = 300            # s depois da partida até a 1ª poda
DB_CAT_FORCE = 30               # s mínimos entre releituras do catálogo pedidas por operação desconhecida
DB_INFLIGHT_KEEP = 3600         # s que um pedido interrompido fica marcado em RAM
DB_CAT_FILE = "db_catalog.json"  # SYNC_DIR/db_catalog.json (v2.11): último catálogo verificado + sig (evita baixar ~50 KB
                                 # a cada partida/autoatualização quando db_catalog/{sid}/sig não mudou)
SSE_TIMEOUT = 90                # s sem nenhum byte (o Firebase manda keep-alive a cada ~30 s) = conexão morta
SSE_RENEW = 300                 # s antes do token vencer: reconecta a escuta com um token novo
SSE_BACKOFF, SSE_BACKOFF_MAX = 5, 300
SSE_MAX_BUF = 8 << 20
DB_ERROR_CODES = ("desligado", "sem_chave", "catalogo_invalido", "operacao_desconhecida", "parametro_invalido",
                  "expirado", "conexao", "autenticacao", "sql", "tempo_esgotado", "limite_linhas",
                  "resposta_grande", "interno")
OP_TYPES = ("consulta", "alteracao", "lista_dinamica")
DYN_MARK = "{sql}"              # lista_dinamica: lugar do SQL guardado no banco dentro do modelo
DYN_MAX = 10000                 # tamanho máximo do SQL guardado no banco (caracteres)
PARAM_TYPES = ("texto", "inteiro", "decimal", "booleano", "data", "opcoes")
INT_RE = re.compile(r"^-?[0-9]+$")
DEC_RE = re.compile(r"^-?[0-9]+(\.[0-9]+)?$")
DATE_RE = re.compile(r"^[0-9]{4}-[0-9]{2}-[0-9]{2}$")
PG_INT_OIDS = (20, 21, 23)       # int8, int2, int4
PG_BOOL_OID = 16


class DbError(Exception):
    """Erro de um pedido ao banco: code = error_code do contrato; broken = conexão em estado desconhecido."""

    def __init__(self, code, msg, broken=False):
        super().__init__(msg)
        self.code, self.broken = code, broken
        self.sqlstate = self.position = self.detail = self.hint = None     # do ErrorResponse (editor SQL, v2.12)
        self.pgmsg = None


def utf16_len(s):
    return len(s) + sum(1 for c in s if ord(c) > 0xFFFF)


def parse_catkey(text):
    """Chave do catálogo: 64 caracteres hexadecimais (espaços ignorados) -> 32 bytes; senão None."""
    s = "".join((text or "").split()).lower()
    if not re.match(r"^[0-9a-f]{64}$", s):
        return None
    return bytes.fromhex(s)


def read_catkey(path):
    return parse_catkey(read_file(path))


def catalog_canon(sid, version, ops):
    """Texto assinado do catálogo (§4.1): o sid amarra o catálogo a um servidor."""
    return json.dumps({"sid": sid, "version": version, "ops": ops}, sort_keys=True, separators=(",", ":"),
                      ensure_ascii=False).encode("utf-8")


def catalog_sig(key, sid, version, ops):
    return hmac.new(key, catalog_canon(sid, version, ops), hashlib.sha256).hexdigest()


def is_int(v):
    return isinstance(v, int) and not isinstance(v, bool)


def is_num(v):
    return isinstance(v, (int, float)) and not isinstance(v, bool)


def op_ok(op):
    """Operação do catálogo com o formato esperado (o catálogo é assinado, mas o agente não confia em tipos)."""
    if not (isinstance(op, dict) and op.get("tipo") in OP_TYPES and isinstance(op.get("sql"), str)
            and op["sql"].strip()):
        return False
    if op["tipo"] == "lista_dinamica" and not (
            isinstance(op.get("sql_origem"), str) and op["sql_origem"].strip()
            and op["sql"].count(DYN_MARK) == 1):
        return False
    if op["tipo"] == "alteracao" and not is_int(op.get("max_linhas_afetadas")):
        return False
    if "max_linhas" in op and not is_int(op["max_linhas"]):
        return False
    params = op.get("params", [])
    if not isinstance(params, list) or len(params) > 20:
        return False
    for p in params:
        if not (isinstance(p, dict) and isinstance(p.get("nome"), str) and p.get("tipo") in PARAM_TYPES):
            return False
        if any(k in p and not is_num(p[k]) for k in ("min", "max")):
            return False
        if p["tipo"] == "opcoes" and not isinstance(p.get("opcoes"), list):
            return False
        if "auditar" in p and not isinstance(p["auditar"], bool):
            return False
    return True


def param_value(p, v):
    """Valor de um parâmetro já validado pelo tipo/limites declarados -> texto para o Postgres (ou None = NULL)."""
    nome, tipo = p["nome"], p["tipo"]
    rot = p.get("rotulo") or nome

    def bad(why):
        raise DbError("parametro_invalido", clip("%s: %s" % (rot, why), 500))

    if v is None or (v == "" and tipo != "texto"):
        if p.get("obrigatorio", True):
            bad("obrigatório")
        return None
    lo, hi = p.get("min"), p.get("max")
    if tipo == "texto":
        if not isinstance(v, str):
            bad("precisa ser texto")
        if "\x00" in v:
            bad("caractere inválido")
        n, hi = len(v), DB_TEXT_MAX if hi is None else hi
        if lo is not None and n < lo:
            bad("no mínimo %g caracteres" % lo)
        if n > hi:
            bad("no máximo %g caracteres" % hi)
        return v
    if tipo in ("inteiro", "decimal"):
        if isinstance(v, bool):
            bad("precisa ser número")
        if is_int(v):
            s = str(v)
        elif isinstance(v, float):
            if not math.isfinite(v) or (tipo == "inteiro" and not v.is_integer()):
                bad("número inválido")
            s = str(int(v)) if tipo == "inteiro" else repr(v)
        elif isinstance(v, str) and (INT_RE if tipo == "inteiro" else DEC_RE).match(v.strip()):
            s = v.strip()
        else:
            bad("precisa ser número %s" % ("inteiro" if tipo == "inteiro" else "decimal"))
        x = decimal.Decimal(s)
        if lo is not None and x < decimal.Decimal(repr(lo)):
            bad("mínimo %g" % lo)
        if hi is not None and x > decimal.Decimal(repr(hi)):
            bad("máximo %g" % hi)
        return s
    if tipo == "booleano":
        if not isinstance(v, bool):
            bad("precisa ser verdadeiro ou falso")
        return "true" if v else "false"
    if tipo == "data":
        if not (isinstance(v, str) and DATE_RE.match(v)):
            bad("data no formato AAAA-MM-DD")
        try:
            datetime.date(int(v[:4]), int(v[5:7]), int(v[8:]))
        except ValueError:
            bad("data inexistente")
        return v
    if not (isinstance(v, str) and v in p.get("opcoes", [])):
        bad("valor fora das opções")
    return v


def check_params(op, params):
    """Valores na ordem de 'params' ($1, $2...), validados antes de ir ao Postgres."""
    decl = op.get("params", [])
    extra = sorted(set(params) - {p["nome"] for p in decl})
    if extra:
        raise DbError("parametro_invalido", clip("parâmetro desconhecido: %s" % ", ".join(extra), 500))
    return [param_value(p, params.get(p["nome"])) for p in decl]


def masked(op):
    """Nomes dos parâmetros com "auditar": false na operação (valor nunca vai para auditoria, erro ou log)."""
    return {p["nome"] for p in (op or {}).get("params", []) if p.get("auditar") is False}


def scrub(msg, op, params):
    """Tira de uma mensagem de erro os valores dos parâmetros com "auditar": false (entre aspas sempre; soltos
    a partir de 4 caracteres, para não estragar a frase trocando letras isoladas)."""
    for k in sorted(masked(op)):
        v = params.get(k)
        if v is None or isinstance(v, (bool, dict, list)):
            continue
        v = str(v)
        if not v:
            continue
        for q in ('"%s"' % v, "'%s'" % v):
            msg = msg.replace(q, '"***"')
        if len(v) >= 4:
            msg = msg.replace(v, "***")
    return msg


def params_json(params, op=None):
    """Parâmetros para a auditoria (≤ 4000): textos longos são cortados; nunca a resposta nem a senha.
    Parâmetro com "auditar": false na operação vira "***" (ausente/nulo continua null)."""
    hide = masked(op)
    params = {k: ("***" if k in hide and v is not None else v) for k, v in params.items()}
    for cut in (None, 200, 20):
        d = {k: (v[:cut] + "…" if cut and isinstance(v, str) and len(v) > cut else v) for k, v in sorted(params.items())}
        s = json.dumps(d, ensure_ascii=False, separators=(",", ":"))
        if utf16_len(s) <= 4000:
            return s
    return '{"_cortado":true}'


def dynamic_sql(cols, rows, more):
    """lista_dinamica: SQL devolvido por sql_origem (1 linha, 1 coluna) já limpo para entrar no modelo no lugar
    de {sql}: sem espaços nem ';' nas pontas, não vazio, até DYN_MAX caracteres e sem ';' no meio (um comando
    só). Mensagens nunca repetem o SQL."""
    if len(cols) != 1 or len(rows) != 1 or more:
        raise DbError("parametro_invalido", "a origem da lista devolveu %s (esperado 1 linha com 1 coluna)" % (
            "%d colunas" % len(cols) if len(cols) != 1 else "nenhuma linha" if not rows else "mais de uma linha"))
    s = (rows[0][0] or "").strip()
    while s.endswith(";"):
        s = s[:-1].rstrip()
    if not s:
        raise DbError("parametro_invalido", "não há SQL de lista de valores cadastrado (vazio)")
    if len(s) > DYN_MAX:
        raise DbError("sql", "SQL da lista de valores longo demais (%d caracteres; máximo %d)" % (len(s), DYN_MAX))
    if ";" in s:
        raise DbError("sql", "SQL da lista de valores com ';' no meio: só um comando é aceito")
    return s


def _pg_msg(t, payload):
    return t + struct.pack("!i", len(payload) + 4) + payload


def _cstr(s):
    return s.encode("utf-8") + b"\0"


class PgConn:
    """Cliente mínimo do PostgreSQL (protocolo v3), só biblioteca padrão: autenticação trust, senha em texto,
    md5 e SCRAM-SHA-256 (sem channel binding), TLS conforme sslmode e protocolo estendido com parâmetros em
    texto (nunca concatenados no SQL). A senha só é usada na autenticação: nunca aparece em mensagens."""

    def __init__(self, host, port, dbname, user, password, sslmode="prefer", timeout=15, app="usage_monitor"):
        self.host, self.port, self.dbname, self.user = host or "127.0.0.1", int(port or 5432), dbname, user
        self.password, self.sslmode, self.timeout = password or "", sslmode or "prefer", timeout
        self.sock, self.buf, self.params, self.tx = None, bytearray(), {}, b"I"
        self.scram = None
        self.app = app
        self.backend = None              # (pid, chave secreta) do BackendKeyData: CancelRequest (editor SQL, v2.12)
        self.connect()

    server_version = property(lambda self: self.params.get("server_version", ""))

    def where(self):
        return self.host if self.host.startswith("/") else "%s:%d" % (self.host, self.port)

    def open_socket(self):
        try:
            if self.host.startswith("/"):
                s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
                s.settimeout(self.timeout)
                try:
                    s.connect(os.path.join(self.host, ".s.PGSQL.%d" % self.port))
                except OSError:
                    s.close()
                    raise
                return s
            return socket.create_connection((self.host, self.port), self.timeout)
        except OSError as e:
            raise DbError("conexao", "sem conexão com o PostgreSQL em %s (%s)" % (self.where(), e.strerror or e))

    def connect(self):
        s = self.sock = self.open_socket()
        if self.sslmode == "require" and ssl is None:
            self.close()
            raise DbError("conexao", "este Python não tem TLS (módulo ssl) e o sslmode é require")
        if self.sslmode != "disable" and ssl is not None and not self.host.startswith("/"):
            self.send(struct.pack("!ii", 8, 80877103))           # SSLRequest
            try:
                ans = s.recv(1)              # exatamente 1 byte: nada lido antes do TLS fica no buffer
            except OSError as e:
                self.close()
                raise DbError("conexao", "sem resposta do PostgreSQL em %s (%s)" % (self.where(), e))
            if ans == b"S":
                ctx = ssl.create_default_context()
                ctx.check_hostname, ctx.verify_mode = False, ssl.CERT_NONE     # como o libpq com sslmode=require
                try:
                    self.sock = ctx.wrap_socket(s, server_hostname=self.host)
                except (ssl.SSLError, OSError) as e:
                    s.close()
                    if self.sslmode == "require":
                        raise DbError("conexao", "falha no TLS com o PostgreSQL em %s (%s)" % (self.where(), e))
                    self.sock = self.open_socket()                # prefer: segue sem TLS
            elif self.sslmode == "require":
                self.close()
                raise DbError("conexao", "o PostgreSQL em %s não aceita TLS (sslmode=require)" % self.where())
        try:
            self.startup()
        except DbError:
            self.close()
            raise

    def close(self):
        if self.sock is not None:
            with contextlib.suppress(OSError):
                self.sock.sendall(_pg_msg(b"X", b""))
            with contextlib.suppress(OSError):
                self.sock.close()
            self.sock = None

    def send(self, data):
        try:
            self.sock.sendall(data)
        except OSError as e:
            raise DbError("conexao", "conexão com o PostgreSQL caiu (%s)" % (e.strerror or e), broken=True)

    def recv(self, n):
        while len(self.buf) < n:
            try:
                chunk = self.sock.recv(max(65536, n - len(self.buf)))
            except socket.timeout:
                raise DbError("tempo_esgotado", "o PostgreSQL não respondeu a tempo", broken=True)
            except OSError as e:
                raise DbError("conexao", "conexão com o PostgreSQL caiu (%s)" % (e.strerror or e), broken=True)
            if not chunk:
                raise DbError("conexao", "o PostgreSQL fechou a conexão", broken=True)
            self.buf += chunk
        out = bytes(self.buf[:n])
        del self.buf[:n]
        return out

    def read_msg(self):
        head = self.recv(5)
        n = struct.unpack("!i", head[1:])[0] - 4
        if n < 0 or n > DB_MAX_MSG:
            raise DbError("resposta_grande", "resposta do PostgreSQL grande demais", broken=True)
        return head[:1], self.recv(n)

    def error(self, p, startup=False):
        f = {}
        for part in p.split(b"\0"):
            if part:
                f[part[:1].decode("ascii", "replace")] = part[1:].decode("utf-8", "replace")
        code, msg = f.get("C", ""), f.get("M", "erro do PostgreSQL")
        # Mensagens próprias (não dependem do lc_messages do servidor) e sem o DETAIL, que repete os valores
        if code == "23505":
            msg = "já existe um registro com essa chave" + (" (restrição %s)" % f["n"] if f.get("n") else "")
        elif code == "23502":
            msg = "campo obrigatório sem valor" + (" (coluna %s)" % f["c"] if f.get("c") else "")
        elif code == "22001":
            msg = "valor longo demais para o tamanho do campo"
        if code.startswith("28"):
            kind = "autenticacao"
        elif code == "57014":
            kind = "tempo_esgotado"
        elif startup or code.startswith("08") or code in ("3D000", "53300", "57P03"):
            kind = "conexao"
        else:
            kind = "sql"
        e = DbError(kind, clip("%s (%s)" % (msg, code) if code else msg, 500))
        e.sqlstate, e.position, e.detail, e.hint = code or None, f.get("P"), f.get("D"), f.get("H")
        e.pgmsg = f.get("M", "erro do PostgreSQL")
        return e

    def startup(self):
        body = struct.pack("!i", 196608) + b"".join(
            _cstr(k) + _cstr(v) for k, v in (("user", self.user), ("database", self.dbname),
                                             ("application_name", self.app), ("client_encoding", "UTF8"))) + b"\0"
        self.send(struct.pack("!i", len(body) + 4) + body)
        while True:
            t, p = self.read_msg()
            if t == b"R":
                self.auth(p)
            elif t == b"K" and len(p) >= 8:
                self.backend = struct.unpack("!ii", p[:8])
            elif t == b"S":
                k, v = p.split(b"\0")[:2]
                self.params[k.decode("utf-8", "replace")] = v.decode("utf-8", "replace")
            elif t == b"E":
                raise self.error(p, startup=True)
            elif t == b"Z":
                self.tx = p[:1]
                return

    def auth(self, p):
        code = struct.unpack("!i", p[:4])[0]
        pw = self.password.encode("utf-8")
        if code == 0:
            return
        if code == 3:                                            # senha em texto
            self.send(_pg_msg(b"p", pw + b"\0"))
        elif code == 5:                                          # md5
            inner = hashlib.md5(pw + self.user.encode("utf-8")).hexdigest().encode()
            self.send(_pg_msg(b"p", b"md5" + hashlib.md5(inner + p[4:8]).hexdigest().encode() + b"\0"))
        elif code == 10:                                         # SASL
            mechs = [m for m in p[4:].split(b"\0") if m]
            if b"SCRAM-SHA-256" not in mechs:
                raise DbError("autenticacao", "o PostgreSQL exige um método de autenticação não suportado (%s)"
                              % b", ".join(mechs).decode("ascii", "replace"))
            nonce = base64.b64encode(os.urandom(18)).decode()
            bare = "n=,r=" + nonce
            first = ("n,," + bare).encode()
            self.scram = {"nonce": nonce, "bare": bare}
            self.send(_pg_msg(b"p", _cstr("SCRAM-SHA-256") + struct.pack("!i", len(first)) + first))
        elif code == 11:                                         # SCRAM: primeira mensagem do servidor
            sf = p[4:].decode("utf-8", "replace")
            a = dict(x.split("=", 1) for x in sf.split(",") if "=" in x)
            sc = self.scram or {}
            try:
                if not a["r"].startswith(sc["nonce"]):
                    raise ValueError
                salted = hashlib.pbkdf2_hmac("sha256", pw, base64.b64decode(a["s"]), int(a["i"]))
            except (KeyError, ValueError, TypeError):
                raise DbError("autenticacao", "resposta SCRAM inválida do PostgreSQL")
            ckey = hmac.new(salted, b"Client Key", hashlib.sha256).digest()
            final = "c=biws,r=" + a["r"]
            msg = ("%s,%s,%s" % (sc["bare"], sf, final)).encode()
            sig = hmac.new(hashlib.sha256(ckey).digest(), msg, hashlib.sha256).digest()
            proof = bytes(x ^ y for x, y in zip(ckey, sig))
            sc["server"] = hmac.new(hmac.new(salted, b"Server Key", hashlib.sha256).digest(), msg, hashlib.sha256).digest()
            self.send(_pg_msg(b"p", (final + ",p=" + base64.b64encode(proof).decode()).encode()))
        elif code == 12:                                         # SCRAM: assinatura do servidor
            a = dict(x.split("=", 1) for x in p[4:].decode("utf-8", "replace").split(",") if "=" in x)
            try:
                ok = hmac.compare_digest(base64.b64decode(a["v"]), (self.scram or {})["server"])
            except (KeyError, ValueError, TypeError):
                ok = False
            if not ok:
                raise DbError("autenticacao", "assinatura SCRAM do PostgreSQL não confere")
        else:
            raise DbError("autenticacao", "método de autenticação do PostgreSQL não suportado (%d)" % code)

    def simple(self, sql):
        """Comando de controle (BEGIN, SET LOCAL, COMMIT, ROLLBACK) pelo protocolo simples."""
        self.send(_pg_msg(b"Q", _cstr(sql)))
        err = None
        while True:
            t, p = self.read_msg()
            if t == b"E":
                err = err or self.error(p)
            elif t == b"Z":
                self.tx = p[:1]
                break
        if err:
            raise err

    def query(self, sql, values, max_rows=0, max_bytes=4 * DB_MAX_JSON):
        """Parse/Bind/Describe/Execute/Sync: parâmetros em texto, tipos inferidos pelo servidor (um comando só:
        o Postgres recusa vários num Parse). Devolve (colunas, oids, linhas, tag, mais_linhas)."""
        vals = b""
        for v in values:
            if v is None:
                vals += struct.pack("!i", -1)
            else:
                b = v.encode("utf-8")
                vals += struct.pack("!i", len(b)) + b
        self.send(_pg_msg(b"P", b"\0" + _cstr(sql) + struct.pack("!h", 0))
                  + _pg_msg(b"B", b"\0\0" + struct.pack("!hh", 0, len(values)) + vals + struct.pack("!h", 0))
                  + _pg_msg(b"D", b"P\0") + _pg_msg(b"E", b"\0" + struct.pack("!i", max_rows)) + _pg_msg(b"S", b""))
        cols, oids, rows, tag, more, err, size = [], [], [], "", False, None, 0
        while True:
            t, p = self.read_msg()
            if t == b"T":
                n, pos = struct.unpack("!h", p[:2])[0], 2
                for _ in range(n):
                    end = p.index(b"\0", pos)
                    cols.append(p[pos:end].decode("utf-8", "replace"))
                    oids.append(struct.unpack("!i", p[end + 7:end + 11])[0])
                    pos = end + 19
            elif t == b"D":
                size += len(p)
                if size > max_bytes:
                    more = True                                   # já passa do que cabe na resposta
                    continue
                n, pos, row = struct.unpack("!h", p[:2])[0], 2, []
                for _ in range(n):
                    ln = struct.unpack("!i", p[pos:pos + 4])[0]
                    pos += 4
                    if ln < 0:
                        row.append(None)
                    else:
                        row.append(p[pos:pos + ln].decode("utf-8", "replace"))
                        pos += ln
                rows.append(row)
            elif t == b"C":
                tag = p.rstrip(b"\0").decode("ascii", "replace")
            elif t == b"s":
                more = True
            elif t == b"E":
                err = err or self.error(p)
            elif t == b"Z":
                self.tx = p[:1]
                break
        if err:
            raise err
        return cols, oids, rows, tag, more

    # ---- editor SQL (v2.12): portal lido em lotes e cancelamento ----
    @staticmethod
    def values_bytes(values):
        out = b""
        for v in values:
            if v is None:
                out += struct.pack("!i", -1)
            else:
                b = v.encode("utf-8")
                out += struct.pack("!i", len(b)) + b
        return out

    def portal(self, sql, values=()):
        """Parse + Bind no portal sem nome + Describe + Flush (sem Sync: o portal fica aberto na transação).
        Devolve (colunas, oids); ([], []) se a instrução não devolve linhas. Erro: Sync, espera o ReadyForQuery."""
        self.send(_pg_msg(b"P", b"\0" + _cstr(sql) + struct.pack("!h", 0))
                  + _pg_msg(b"B", b"\0\0" + struct.pack("!hh", 0, len(values)) + self.values_bytes(values)
                            + struct.pack("!h", 0))
                  + _pg_msg(b"D", b"P\0") + _pg_msg(b"H", b""))
        cols, oids = [], []
        while True:
            t, p = self.read_msg()
            if t == b"T":
                n, pos = struct.unpack("!h", p[:2])[0], 2
                for _ in range(n):
                    end = p.index(b"\0", pos)
                    cols.append(p[pos:end].decode("utf-8", "replace"))
                    oids.append(struct.unpack("!i", p[end + 7:end + 11])[0])
                    pos = end + 19
                return cols, oids
            if t == b"n":
                return cols, oids
            if t == b"E":
                err = self.error(p)
                self.send(_pg_msg(b"S", b""))
                while True:
                    t, p = self.read_msg()
                    if t == b"Z":
                        self.tx = p[:1]
                        break
                raise err

    def more(self):
        """Lê mais um pedaço do socket para o buffer (mesmos erros do recv)."""
        try:
            chunk = self.sock.recv(262144)
        except socket.timeout:
            raise DbError("tempo_esgotado", "o PostgreSQL não respondeu a tempo", broken=True)
        except OSError as e:
            raise DbError("conexao", "conexão com o PostgreSQL caiu (%s)" % (e.strerror or e), broken=True)
        if not chunk:
            raise DbError("conexao", "o PostgreSQL fechou a conexão", broken=True)
        self.buf += chunk

    def batch(self, max_rows):
        """Execute(portal, max_rows) + Sync. Devolve (partes, linhas, tag, suspenso): as partes são fatias cruas e
        contíguas de mensagens DataRow ('D' + tamanho + campos), sem decodificar linha a linha (memória ~1 lote)."""
        self.send(_pg_msg(b"E", b"\0" + struct.pack("!i", max_rows)) + _pg_msg(b"S", b""))
        parts, rows, tag, suspended, err = [], 0, "", False, None
        while True:
            buf, i, end, run, ready = self.buf, 0, len(self.buf), -1, False
            while i + 5 <= end:
                t = buf[i]
                n = int.from_bytes(buf[i + 1:i + 5], "big") + 1
                if n < 5 or n - 5 > DB_MAX_MSG:
                    raise DbError("resposta_grande", "resposta do PostgreSQL grande demais", broken=True)
                if i + n > end:
                    break
                if t == 0x44:                                    # DataRow
                    if run < 0:
                        run = i
                    rows += 1
                else:
                    if run >= 0:
                        parts.append(bytes(buf[run:i]))
                        run = -1
                    p = bytes(buf[i + 5:i + n])
                    if t == 0x43:                                # CommandComplete
                        tag = p.rstrip(b"\0").decode("ascii", "replace")
                    elif t == 0x73:                              # PortalSuspended
                        suspended = True
                    elif t == 0x45:
                        err = err or self.error(p)
                    elif t == 0x5A:                              # ReadyForQuery
                        self.tx = p[:1]
                        i += n
                        ready = True
                        break
                i += n
            if run >= 0:
                parts.append(bytes(buf[run:i]))
            del buf[:i]
            if ready:
                break
            self.more()
        if err:
            raise err
        return parts, rows, tag, suspended

    def cancel(self):
        """CancelRequest: conexão nova com o pid e a chave secreta do BackendKeyData (o servidor não responde)."""
        if not self.backend:
            return False
        try:
            s = self.open_socket()
        except DbError:
            return False
        try:
            s.sendall(struct.pack("!iiii", 16, 80877102, self.backend[0], self.backend[1]))
            return True
        except OSError:
            return False
        finally:
            with contextlib.suppress(OSError):
                s.close()


def pg_value(v, oid):
    if v is None:
        return None
    if oid == PG_BOOL_OID:
        return v == "t"
    if oid in PG_INT_OIDS:
        n = int(v)
        return n if abs(n) < 2 ** 53 else v                      # JSON/JavaScript: inteiro exato até 2^53
    return v


def rows_doc(cols, oids, rows, more):
    """Campos da resposta com as linhas em JSON (≤ DB_MAX_JSON); truncated se não couber tudo."""
    if len(cols) > DB_MAX_COLS:
        raise DbError("resposta_grande", "a consulta devolveu %d colunas (máximo %d)" % (len(cols), DB_MAX_COLS))
    out, size, truncated = [], 2, more
    for r in rows:
        s = json.dumps([pg_value(v, o) for v, o in zip(r, oids)], ensure_ascii=False, separators=(",", ":"))
        n = utf16_len(s) + (1 if out else 0)
        if size + n > DB_MAX_JSON:
            truncated = True
            break
        out.append(s)
        size += n
    if rows and not out:
        raise DbError("resposta_grande", "uma linha da resposta passa de %d KB" % (DB_MAX_JSON // 1024))
    doc = {"columns": [clip(c, 256) for c in cols], "rows_json": "[" + ",".join(out) + "]", "row_count": len(out),
           "truncated": bool(truncated)}
    if not cols:
        del doc["columns"]                                       # o RTDB não guarda lista vazia
    return doc


def db_panel_file(log):
    return live_path(log) + DB_SUFFIX


def db_panel_text(doc, now=None):
    """(texto, tipo) da linha do banco no painel a partir do estado publicado pelo agente."""
    if not doc or not doc.get("text"):
        return "", ""
    txt = doc["text"]
    if doc.get("kind") == "ok":
        t = doc.get("last_req_at") or 0
        txt += " · último pedido %s" % fmt_ago(max(0, (now or time.time()) - t)) if t else " · nenhum pedido ainda"
    return txt, doc.get("kind", "")


class DbAgent:
    """Acesso remoto ao Postgres local. Duas threads, sem tocar na coleta nem no heartbeat:

    - 'banco': a cada DB_REFRESH lê db_config/{sid}/updated_at e db_catalog/{sid}/sig (o nó inteiro só quando
      muda), verifica o catálogo (HMAC, versão que não regride), atende os pedidos recebidos pela escuta
      (valida, executa, grava resposta + auditoria e remove o pedido num PATCH só), fecha a conexão com o
      Postgres ociosa e poda respostas (24 h) e auditoria (180 d) uma vez por dia;
    - 'banco-escuta': SSE em db_requests/{sid} (enquanto o acesso está permitido; sem db_config/{sid} a
      conexão usa DB_DEFAULTS e o db_status diz config_source "padrao"),
      reconectando com espera crescente e renovando o token antes de vencer.
    Nada no disco no caminho regular: estado em memória e em RAM (/dev/shm); no disco só a linha da
    auditoria local de cada pedido, a versão do catálogo quando sobe e a cópia do catálogo verificado
    (SYNC_DIR/db_catalog.json, v2.11) quando ele muda: na partida, com o mesmo sig no Firebase, não baixa de novo."""

    def __init__(self, cloud, out=None):
        self.cloud, self.live, self.ident, self.out = cloud, cloud.live, cloud.ident, out
        self.sid = self.ident.install_id
        self.key_path = os.path.join(cloud.base, CATKEY_FILE)
        self.audit_path = os.path.join(cloud.base, DB_AUDIT_FILE)
        self.shm = db_panel_file(cloud.log)
        self.q = queue.Queue()
        self.stop_ev, self.listen = threading.Event(), threading.Event()
        self.thread = self.sse_thread = None
        self.resp = None                  # resposta SSE aberta
        self.enabled = None               # sync.db_access
        self.configured = False           # acesso ativo (desligado: só se existe db_config/{sid})
        self.cfg, self.cfg_at = None, None
        self.key, self.key_mtime, self.key_checked = None, None, 0.0
        self.cat_raw, self.cat_sig, self.catalog, self.cat_error, self.cat_forced = None, None, None, "", 0.0
        self.cat_path = os.path.join(cloud.base, SYNC_DIR, DB_CAT_FILE)
        self.cat_cached = False           # cat_raw veio da cópia local (ainda não conferida contra a chave atual)
        self.load_cat_cache()
        self.pg, self.pg_used = None, 0.0
        self.conn_state = (None, "", "")  # (ok?, error_code, mensagem) do último contato com o Postgres
        self.server_version = ""
        self.pending, self.done = {}, set()
        shm = read_json_owned(self.shm) or {}
        self.inflight = {k: v for k, v in (shm.get("inflight") or {}).items()
                         if is_num(v) and time.time() - v < DB_INFLIGHT_KEEP}
        self.last_req_at = shm.get("last_req_at") if is_num(shm.get("last_req_at")) else 0
        self.status_sent = None
        self.shm_sent = None
        self.next_refresh, self.next_prune = 0.0, time.time() + DB_PRUNE_FIRST
        self.sse = {"state": "", "fails": 0, "msg": ""}
        self.fb_error = ""                # última falha lendo o Firebase
        self.test_pending = False         # testar a conexão (configuração nova)
        self.shm_lock = threading.Lock()
        self.sql = None                   # SqlEditor (v2.12): recebe os pedidos de sessão desta mesma escuta

    # ---- ciclo de vida ----
    def start(self):
        self.thread = threading.Thread(target=self.loop, name="banco", daemon=True)
        self.thread.start()
        self.sse_thread = threading.Thread(target=self.sse_loop, name="banco-escuta", daemon=True)
        self.sse_thread.start()

    def key_changed(self):
        """A chave foi gravada pelo painel (tecla k): o próximo passo da thread 'banco' relê o arquivo."""
        self.key_checked = 0.0

    def wake(self):
        """Aviso da central (signals/<sid>: config_at/catalog_at mudou): relê configuração e catálogo já."""
        self.next_refresh = 0.0

    def stop(self):
        self.stop_ev.set()
        self.listen.clear()
        self.close_stream()
        for th in (self.thread, self.sse_thread):
            if th is not None and th is not threading.current_thread():
                th.join(5)
        self.close_pg()
        try:                                              # o --view não mostra mais "conectado"
            write_private(self.shm, json.dumps({"inflight": self.inflight, "last_req_at": self.last_req_at}))
        except OSError:
            pass

    def loop(self):
        while not self.stop_ev.is_set():
            try:
                self.step()
            except Exception as e:                        # nunca derruba a thread
                self.fb_error = "erro interno: %s" % type(e).__name__
                self.stop_ev.wait(5)

    def step(self, wait=5.0):
        now = time.time()
        if now >= self.next_refresh:
            self.refresh()
        elif self.configured and now - self.key_checked >= DB_KEY_CHECK:
            self.check_key()
        if self.listen.is_set() and now >= self.next_prune:
            self.prune()
        if self.pg is not None and now - self.pg_used > DB_IDLE:
            self.close_pg()
        try:
            ev = self.q.get(timeout=wait)
        except queue.Empty:
            return
        self.apply_event(*ev)
        while True:                                       # consome o que já chegou antes de atender
            try:
                self.apply_event(*self.q.get_nowait())
            except queue.Empty:
                break
        self.process()

    # ---- configuração, chave e catálogo ----
    def refresh(self):
        self.next_refresh = time.time() + DB_REFRESH
        try:
            self.load_config()
            if self.configured and self.enabled:
                self.check_key(force=True)
                self.load_catalog()
            self.fb_error = ""
        except CloudError as e:
            self.next_refresh = time.time() + DB_RETRY
            self.fb_error = "sem acesso ao Firebase (%s)" % str(e)[:120]
        else:
            if self.configured:
                if self.test_pending:
                    self.test_conn()
                try:
                    self.publish_status()
                except CloudError:
                    self.status_sent = None               # tenta de novo na próxima vez
        self.save_shm()

    def load_config(self):
        sid = self.sid
        self.enabled = bool(self.ident.sync_cfg()["db_access"])
        if not self.enabled:
            # desligado pelo dono do servidor: nem lê a senha, só se existe configuração (shallow)
            self.configured = self.live.get("db_config/" + sid, {"shallow": "true"}) is not None
            self.cfg = self.cfg_at = None
            self.listen.clear()
            self.close_stream()
            self.close_pg()
            return
        at = self.live.get("db_config/%s/updated_at" % sid)
        if at is not None and (at != self.cfg_at or self.cfg is None):
            cfg = self.live.get("db_config/" + sid)
            at = cfg.get("updated_at") if isinstance(cfg, dict) else None
            if at is not None:
                self.cfg, self.cfg_at = cfg, at
                self.close_pg()
                self.test_pending = True
        if at is None and (self.cfg is None or self.cfg_at is not None):
            # sem db_config/{sid}: conexão padrão (DB_DEFAULTS); db_config gravado pela central prevalece
            self.cfg, self.cfg_at = dict(DB_DEFAULTS), None
            self.close_pg()
            self.conn_state, self.server_version = (None, "", ""), ""
            self.test_pending = True
        self.configured = True
        self.listen.set()

    def check_key(self, force=False):
        """Relê a chave só se o arquivo mudou (stat a cada DB_KEY_CHECK s): --catalogo-chave em outro terminal."""
        self.key_checked = time.time()
        try:
            mt = os.stat(self.key_path).st_mtime
        except OSError:
            mt = None
        if mt == self.key_mtime and not force:
            return
        changed = mt != self.key_mtime
        self.key_mtime = mt
        self.key = read_catkey(self.key_path) if mt is not None else None
        if changed and not force:
            self.catalog, self.cat_error = self.verify(self.cat_raw)
            with contextlib.suppress(CloudError):
                self.publish_status()
            self.save_shm()

    def load_cat_cache(self):
        """Partida: catálogo da cópia local (v2.11) se for deste servidor e estiver inteiro. Vale só enquanto o sig
        remoto for o mesmo (load_catalog compara antes de usar) e a assinatura conferir com a chave atual."""
        d = read_json(self.cat_path)
        raw = d.get("raw") if isinstance(d, dict) else None
        if (isinstance(raw, dict) and d.get("sid") == self.sid and isinstance(d.get("sig"), str)
                and raw.get("sig") == d["sig"]):
            self.cat_raw, self.cat_sig, self.cat_cached = raw, d["sig"], True

    def save_cat_cache(self, raw):
        """Guarda o catálogo baixado e verificado (gravação atômica, 600). Falha de disco só custa um download."""
        try:
            os.makedirs(os.path.dirname(self.cat_path), mode=0o700, exist_ok=True)
            if raw is None:
                with contextlib.suppress(FileNotFoundError):
                    os.remove(self.cat_path)
            else:
                write_private(self.cat_path, json.dumps({"sid": self.sid, "sig": raw.get("sig"), "raw": raw},
                                                        separators=(",", ":"), ensure_ascii=False))
        except OSError:
            pass

    def fetch_catalog(self):
        raw = self.live.get("db_catalog/" + self.sid)
        self.cat_cached = False
        return raw if isinstance(raw, dict) else None

    def load_catalog(self):
        sig = self.live.get("db_catalog/%s/sig" % self.sid)
        fetched = False
        if sig is None:
            if self.cat_raw is not None or self.cat_cached:
                self.save_cat_cache(None)             # catálogo removido na central: a cópia local também sai
            self.cat_raw, self.cat_cached = None, False
        elif sig != self.cat_sig or self.cat_raw is None:
            self.cat_raw, fetched = self.fetch_catalog(), True
        self.cat_sig = sig
        self.catalog, self.cat_error = self.verify(self.cat_raw)
        if self.catalog is None and self.cat_cached and self.key is not None:
            # cópia local recusada (chave trocada, arquivo mexido): baixa o nó do Firebase e confere de novo
            self.cat_raw, fetched = self.fetch_catalog(), True
            self.catalog, self.cat_error = self.verify(self.cat_raw)
        if fetched and self.catalog is not None and self.cat_raw.get("sig") == sig:
            self.save_cat_cache(self.cat_raw)

    def verify(self, raw):
        """(catálogo aceito, motivo da recusa). Só com a assinatura certa e versão >= à última aceita."""
        if self.key is None:
            return None, "falta a chave do catálogo"
        if not raw:
            return None, "catálogo não publicado"
        version, ops, sig = raw.get("version"), raw.get("ops"), raw.get("sig")
        if not (is_int(version) and isinstance(ops, dict) and isinstance(sig, str)):
            return None, "catálogo malformado"
        if not hmac.compare_digest(catalog_sig(self.key, self.sid, version, ops), sig):
            return None, "assinatura do catálogo não confere (chave errada ou catálogo adulterado)"
        last = (self.ident.data.get("db") or {}).get("catalog_version", 0)
        if is_int(last) and version < last:
            return None, "catálogo versão %d é mais antigo que o último aceito (%d)" % (version, last)
        if version != last:
            self.ident.update("db", "catalog_version", version)
        return {"version": version, "ops": {k: o for k, o in ops.items() if op_ok(o)}}, ""

    # ---- Postgres ----
    def conn(self):
        if self.pg is None:
            c = self.cfg or {}
            try:
                self.pg = PgConn(c.get("host"), c.get("port"), c.get("dbname") or "", c.get("user") or "",
                                 c.get("password") or "", c.get("sslmode"))
            except DbError as e:
                self.conn_state = (False, e.code, str(e))
                raise
            self.server_version = self.pg.server_version
            self.conn_state = (True, "", "")
        self.pg_used = time.time()
        return self.pg

    def close_pg(self):
        if self.pg is not None:
            self.pg.close()
            self.pg = None

    def test_conn(self):
        """Uma conexão quando a configuração chega ou muda (versão do servidor e erro de senha no db_status)."""
        self.test_pending = False
        with contextlib.suppress(DbError):
            self.conn()

    def run_op(self, op, values):
        """Executa: consulta e lista_dinamica em transação READ ONLY (sempre desfeita), alteração em transação
        única com limite de linhas afetadas (passou -> ROLLBACK). statement_timeout em todas."""
        pg = self.conn()
        query = op["tipo"] != "alteracao"
        limit = max(1, min(DB_MAX_ROWS, op.get("max_linhas", DB_MAX_ROWS)))
        pg.sock.settimeout(DB_TIMEOUT_MS / 1000.0 + 5)
        try:
            pg.simple("BEGIN TRANSACTION %s; SET LOCAL statement_timeout = %d" % (
                "READ ONLY" if query else "READ WRITE", DB_TIMEOUT_MS))
            if op["tipo"] == "lista_dinamica":
                # 1º o SQL guardado no banco (com os parâmetros), depois o modelo com ele, sem parâmetros
                ocols, _, orows, _, omore = pg.query(op["sql_origem"], values, 2)
                inner = dynamic_sql(ocols, orows, omore)
                cols, oids, rows, tag, more = pg.query(op["sql"].replace(DYN_MARK, inner), [], limit)
            else:
                cols, oids, rows, tag, more = pg.query(op["sql"], values, limit if query else 0)
            doc = {}
            if not query:
                last = tag.split()[-1] if tag else ""
                n = int(last) if last.isdigit() else 0
                if n > op["max_linhas_afetadas"]:
                    pg.simple("ROLLBACK")
                    raise DbError("limite_linhas", "a alteração afetaria %d linha(s) (limite %d): nada foi alterado"
                                  % (n, op["max_linhas_afetadas"]))
                doc["affected"] = n
            if cols or query:
                doc.update(rows_doc(cols, oids, rows[:limit], more or len(rows) > limit))
            pg.simple("ROLLBACK" if query else "COMMIT")
            self.conn_state = (True, "", "")
            return doc
        except DbError as e:
            if e.broken or e.code in ("conexao", "autenticacao"):
                self.close_pg()
                if e.code in ("conexao", "autenticacao"):
                    self.conn_state = (False, e.code, str(e))
            elif pg.tx != b"I":
                try:
                    pg.simple("ROLLBACK")
                except DbError:
                    self.close_pg()
            raise
        finally:
            if self.pg is not None:
                with contextlib.suppress(OSError):
                    self.pg.sock.settimeout(self.pg.timeout)

    # ---- pedidos ----
    def apply_event(self, kind, path, data):
        """Espelha db_requests/{sid} a partir dos eventos put/patch da escuta."""
        parts = [x for x in (path or "/").split("/") if x]
        items = [("", data)] if kind == "put" else list((data or {}).items())
        for k, v in items:
            sub = parts + [x for x in k.split("/") if x]
            if not sub:
                self.pending = dict(v) if isinstance(v, dict) else {}
                continue
            cur = self.pending
            for x in sub[:-1]:
                if not isinstance(cur.get(x), dict):
                    cur[x] = {}
                cur = cur[x]
            if v is None:
                cur.pop(sub[-1], None)
            else:
                cur[sub[-1]] = v

    def process(self):
        if self.sql is not None:                          # editor SQL (v2.12): pedidos em db_requests/{sid}/sql
            inbox = self.pending.get(SQL_INBOX)
            self.sql.inbox(dict(inbox) if isinstance(inbox, dict) else {})
        for rid in sorted(self.pending):
            if self.stop_ev.is_set():
                break
            if rid not in self.done and rid != SQL_INBOX:
                self.handle(rid, self.pending[rid])

    def answer(self, rid, op_id, params, at):
        """Valida e executa um pedido. Devolve os campos da resposta; DbError = recusado/falhou."""
        if rid in self.inflight:
            raise DbError("interno", "pedido interrompido durante a execução (agente reiniciado): não foi reexecutado")
        age = self.live.server_now() * 1000 - at
        if age > DB_EXPIRE * 1000:
            raise DbError("expirado", "pedido expirado (%d s na fila): não foi executado" % (age // 1000))
        if self.key is None:
            raise DbError("sem_chave", "o agente não tem a chave do catálogo (no servidor: --catalogo-chave)")
        op = (self.catalog or {}).get("ops", {}).get(op_id)
        if op is None and time.time() - self.cat_forced >= DB_CAT_FORCE:
            self.cat_forced = time.time()                 # catálogo pode ter sido publicado agora
            with contextlib.suppress(CloudError):
                self.load_catalog()
            op = (self.catalog or {}).get("ops", {}).get(op_id)
        if self.catalog is None:
            raise DbError("catalogo_invalido", clip("catálogo de operações inválido: " + self.cat_error, 500))
        if op is None:
            raise DbError("operacao_desconhecida", clip("operação desconhecida: %s" % op_id, 500))
        values = check_params(op, params)
        if self.cfg is None:
            raise DbError("conexao", "conexão com o banco não configurada")
        self.mark(rid, True)
        self.send_patch({"db_responses/%s/%s" % (self.sid, rid): {"state": "processando",
                                                                  "started_at": {".sv": "timestamp"}}})
        return self.run_op(op, values)

    def op_of(self, op_id):
        """Operação do catálogo aceito (None se desconhecida): define o que é mascarado na auditoria."""
        return (self.catalog or {}).get("ops", {}).get(op_id)

    def handle(self, rid, req):
        t0 = time.time()
        req = req if isinstance(req, dict) else {}
        op_id = req["op"] if isinstance(req.get("op"), str) else "?"
        params = req["params"] if isinstance(req.get("params"), dict) else {}
        at = req["at"] if is_num(req.get("at")) else 0
        by = req["by"] if isinstance(req.get("by"), str) else "?"
        try:
            resp = dict(self.answer(rid, op_id, params, at), ok=True)
        except DbError as e:
            resp = {"ok": False, "error_code": e.code if e.code in DB_ERROR_CODES else "interno",
                    "error": clip(scrub(str(e), self.op_of(op_id), params), 500)}
        except CloudError as e:                           # não conseguiu marcar "processando": não executou
            resp = {"ok": False, "error_code": "interno", "error": clip("falha no Firebase: %s" % e, 500)}
        resp.update(state="concluido", ms=round((time.time() - t0) * 1000, 1), done_at={".sv": "timestamp"})
        audit = {"op": clip(op_id, 64), "params_json": params_json(params, self.op_of(op_id)), "by": clip(by, 128), "requested_at": at,
                 "done_at": {".sv": "timestamp"}, "ok": resp["ok"]}
        for k in ("affected", "error_code"):
            if k in resp:
                audit[k] = resp[k]
        self.done.add(rid)
        self.last_req_at = time.time()
        patch = {"db_responses/%s/%s" % (self.sid, rid): resp, "db_audit/%s/%s" % (self.sid, rid): audit,
                 "db_requests/%s/%s" % (self.sid, rid): None}
        status = self.status_doc()
        if status != self.status_sent:
            patch["db_status/" + self.sid] = dict(status, checked_at={".sv": "timestamp"})
        sent = self.deliver(rid, patch, resp)
        if sent and "db_status/" + self.sid in patch:
            self.status_sent = status
        self.audit_local(rid, op_id, by, at, params_json(params, self.op_of(op_id)), resp)
        self.pending.pop(rid, None)
        if sent:
            self.mark(rid, False)
        self.save_shm()

    def deliver(self, rid, patch, resp):
        """Resposta + auditoria + remoção do pedido (atômico). Recusado pelas regras: só a resposta de erro."""
        for i in range(3):
            try:
                self.send_patch(patch)
                return True
            except CloudError as e:
                if getattr(e, "code", 0) in (400, 401):
                    break
                self.stop_ev.wait(2 * (i + 1))
        else:
            return False
        minimal = {"db_responses/%s/%s" % (self.sid, rid): {
            "state": "concluido", "ok": False, "error_code": "interno", "error": "resposta recusada pelo Firebase",
            "ms": resp["ms"], "done_at": {".sv": "timestamp"}}, "db_requests/%s/%s" % (self.sid, rid): None}
        try:
            self.send_patch(minimal)
            return True
        except CloudError:
            return False

    def send_patch(self, patch):
        self.live.patch("", patch, timeout=15)

    def audit_local(self, rid, op_id, by, at, pjson, resp):
        line = json.dumps({"at": iso_now(), "rid": rid, "op": op_id, "by": by, "requested_at": at, "ok": resp["ok"],
                           "affected": resp.get("affected"), "error_code": resp.get("error_code"),
                           "ms": resp["ms"], "params": pjson}, ensure_ascii=False)
        try:
            fd = os.open(self.audit_path, os.O_WRONLY | os.O_APPEND | os.O_CREAT | getattr(os, "O_BINARY", 0), 0o600)
            try:
                if hasattr(os, "fchmod"):                 # Windows: protegido pela permissão da pasta
                    os.fchmod(fd, 0o600)
                os.write(fd, (line + "\n").encode("utf-8"))
            finally:
                os.close(fd)
        except OSError:
            pass

    def mark(self, rid, on):
        """Pedido em execução, em RAM: se o processo reiniciar no meio, não é reexecutado."""
        with self.shm_lock:
            if on:
                self.inflight[rid] = time.time()
            else:
                self.inflight.pop(rid, None)
        self.save_shm(force=True)

    # ---- poda (1x por dia) ----
    def prune(self):
        self.next_prune = time.time() + DB_PRUNE_EVERY
        now_ms = int(self.live.server_now() * 1000)
        try:
            for node, keep in (("db_responses", DB_RESP_KEEP), ("db_audit", DB_AUDIT_KEEP)):
                cut = '"%013d"' % (now_ms - keep * 1000)
                for _ in range(20):
                    old = self.live.get("%s/%s" % (node, self.sid), {"orderBy": '"$key"', "endAt": cut,
                                                                     "limitToFirst": "100"}) or {}
                    if not old:
                        break
                    self.send_patch({"%s/%s/%s" % (node, self.sid, k): None for k in old})
        except CloudError:
            self.next_prune = time.time() + 3600

    # ---- estado: db_status (Firebase), painel (RAM) ----
    def status_doc(self):
        ok_conn, code, msg = self.conn_state
        doc = {"agent_version": VERSION, "key_present": self.key is not None}
        if self.server_version:
            doc["server_version"] = clip(self.server_version, 64)
        if self.catalog is not None:
            doc["catalog_version"] = self.catalog["version"]
        if self.enabled and self.cfg is not None:
            doc["config_source"] = "padrao" if self.cfg_at is None else "central"
        if not self.enabled:
            code, msg = "desligado", "acesso ao banco desligado neste servidor (sync.db_access)"
        elif ok_conn is False:
            pass
        elif self.key is None:
            code, msg = "sem_chave", "falta a chave do catálogo no servidor (--catalogo-chave)"
        elif self.catalog is None:
            code, msg = "catalogo_invalido", "catálogo de operações inválido: " + self.cat_error
        doc["ok"] = not code
        if code:
            doc.update(error_code=code, error=clip(msg, 500))
        return doc

    def publish_status(self):
        doc = self.status_doc()
        if doc == self.status_sent:
            return
        self.send_patch({"db_status/" + self.sid: dict(doc, checked_at={".sv": "timestamp"})})
        self.status_sent = doc

    def panel(self):
        """Estado para a linha do painel: {"text", "kind" (ok|erro|aviso), "last_req_at"}; {} = sem linha."""
        if not self.configured:
            return {}
        if not self.enabled:
            return {"text": "Banco: acesso desligado neste servidor (sync.db_access)", "kind": "aviso"}
        if self.key is None:                          # a ação que falta é do usuário: vem antes dos outros erros
            return {"text": "Banco: falta a chave do catálogo — tecle k para informar", "kind": "erro",
                    "code": "sem_chave"}
        st = self.status_doc()
        if self.sse["state"] == "erro" and self.sse["fails"] >= 2:
            return {"text": "Banco: sem escuta de pedidos (%s)" % self.sse["msg"], "kind": "erro"}
        if st["ok"]:
            ver = (st.get("server_version") or "").split(" ")[0]
            return {"text": "Banco: conectado" + (" (PostgreSQL %s)" % ver if ver else ""), "kind": "ok",
                    "last_req_at": self.last_req_at}
        return {"text": "Banco: " + st["error"], "kind": "erro"}

    def save_shm(self, force=False):
        with self.shm_lock:
            doc = dict(self.panel(), inflight=dict(self.inflight))
            doc["last_req_at"] = self.last_req_at
            if doc == self.shm_sent and not force:
                return
            try:
                write_private(self.shm, json.dumps(doc))
                self.shm_sent = doc
            except OSError:
                pass

    # ---- escuta (SSE) ----
    def close_stream(self):
        """Fecha a escuta de outra thread: shutdown no socket acorda o recv bloqueado (close sozinho não)."""
        r = self.resp
        if r is not None:
            with contextlib.suppress(Exception):
                r.fp.raw._sock.shutdown(socket.SHUT_RDWR)
            with contextlib.suppress(Exception):
                r.close()

    def sse_loop(self):
        while not self.stop_ev.is_set():
            if not self.listen.wait(1):
                continue
            try:
                ok = self.sse_once()
            except Exception as e:                        # nunca derruba a thread (ex.: segredo corrompido)
                ok = self.sse_fail("erro interno: %s" % type(e).__name__)
            if self.stop_ev.is_set():
                break
            if ok:
                self.sse["fails"] = 0
            else:
                self.sse["fails"] += 1
                self.stop_ev.wait(min(SSE_BACKOFF_MAX, SSE_BACKOFF * 2 ** (self.sse["fails"] - 1)))

    def sse_fail(self, msg):
        self.sse.update(state="erro", msg=msg[:120])
        return False

    def sse_once(self):
        """Uma conexão de escuta. True = terminou normalmente (renovar token, servidor fechou); False = falha."""
        try:
            tok = self.live.token(min_valid=SSE_RENEW + 60)
            url = "%s/db_requests/%s.json?%s" % (self.live.db, self.sid, urllib.parse.urlencode({"auth": tok}))
            req = urllib.request.Request(url, headers={"Accept": "text/event-stream",
                                                       "User-Agent": "usage-monitor/" + VERSION})
            resp = urllib.request.urlopen(req, timeout=SSE_TIMEOUT)
        except urllib.error.HTTPError as e:
            if e.code == 401:
                self.live.id_token = None
            return self.sse_fail("Firebase respondeu %d" % e.code)
        except CloudError as e:
            return self.sse_fail(str(e))
        except (urllib.error.URLError, OSError) as e:
            return self.sse_fail("sem conexão com o Firebase (%s)" % getattr(e, "reason", e))
        exp = self.live.exp
        self.live.note_date(resp.headers)
        self.resp = resp
        self.sse.update(state="ok", msg="")
        buf, event, data = b"", None, []
        try:
            while not self.stop_ev.is_set() and self.listen.is_set():
                chunk = resp.read1(65536)
                if not chunk:
                    return True                           # o servidor fechou: reconecta
                buf += chunk
                if len(buf) > SSE_MAX_BUF:
                    return self.sse_fail("evento grande demais")
                *lines, buf = buf.split(b"\n")
                for line in lines:
                    line = line.rstrip(b"\r")
                    if line:
                        if line.startswith(b"event:"):
                            event = line[6:].strip().decode("utf-8", "replace")
                        elif line.startswith(b"data:"):
                            data.append(line[5:].strip())
                        continue
                    r = self.sse_event(event, b"\n".join(data))
                    event, data = None, []
                    if r is not None:
                        return r
                if exp - time.time() < SSE_RENEW:
                    return True                           # token perto de vencer: reconecta com um novo
            return True
        except (OSError, http.client.HTTPException, ValueError) as e:
            return self.sse_fail("escuta interrompida (%s)" % (str(e)[:80] or type(e).__name__))
        finally:
            self.resp = None
            with contextlib.suppress(Exception):
                resp.close()

    def sse_event(self, event, data):
        """None = continua; True = reconectar já; False = falha (espera antes de reconectar)."""
        if event in ("put", "patch"):
            d = json.loads(data.decode("utf-8"))
            self.q.put((event, d.get("path", "/"), d.get("data")))
        elif event == "auth_revoked":
            self.live.id_token = None
            return True
        elif event == "cancel":
            return self.sse_fail("o Firebase cancelou a escuta (permissão)")
        return None


# --------------------------------------------------------------------------
# Editor SQL remoto (v2.12, só leitura; contrato em docs/EDITOR_SQL.md)
# --------------------------------------------------------------------------
SQL_PROTO = 1                      # versão do protocolo de quadros (hello/hello_ok, info/{sid}/sql_proto)
SQL_INBOX = "sql"                  # db_requests/{sid}/sql/{sess}: pedidos de sessão (mesma escuta do DbAgent)
SQL_CERT_FILE = "server_monitor_sql.crt"     # certificado do TLS interno (ECDSA P-256, autoassinado)
SQL_KEY_FILE = "server_monitor_sql.key"      # chave privada (600)
SQL_AUDIT_FILE = "server_monitor_sql_audit.log"   # auditoria local: uma linha JSON por sessão/execução (600)
SQL_RELAYS_DEFAULT = "relay.cbalmeida.com:443,cbalmeida.com:443,c2.dyndns.org:443,c2tecnologia.dyndns.org:443"
SQL_RELAY_CAFILE = os.environ.get("USAGE_MONITOR_SQL_RELAY_CA") or None   # só testes: CA do relay falso
# Raízes da Let's Encrypt embutidas (v2.14.1) como âncoras ADICIONAIS só do TLS até o relay: o Python no Windows usa só
# as raízes já presentes no repositório do sistema (load_default_certs lê ROOT/CA) e não baixa as que faltam, como a
# CryptoAPI faz; um Windows 2016 sem atualizações não tem a ISRG Root X1 e recusava o relay (CERTIFICATE_VERIFY_FAILED).
# Cadeia e nome continuam verificados. Origem: https://letsencrypt.org/certs/isrgrootx1.pem e isrg-root-x2.pem.
# SHA-256 (DER), conferidos com crt.sh e o repositório de raízes da Apple (teste: test_sql_relay_roots):
#   ISRG Root X1  96bcec06264976f37460779acf28c5a7cfe8a3c0aae11a8ffcee05c0bddf08c6  (RSA 4096, até 2035-06-04)
#   ISRG Root X2  69729b8e15a86efc177a57afb7171dfc64add28c2fca8cf1507e34453ccb1470  (ECDSA P-384, até 2040-09-17)
SQL_RELAY_ROOTS = """\
-----BEGIN CERTIFICATE-----
MIIFazCCA1OgAwIBAgIRAIIQz7DSQONZRGPgu2OCiwAwDQYJKoZIhvcNAQELBQAw
TzELMAkGA1UEBhMCVVMxKTAnBgNVBAoTIEludGVybmV0IFNlY3VyaXR5IFJlc2Vh
cmNoIEdyb3VwMRUwEwYDVQQDEwxJU1JHIFJvb3QgWDEwHhcNMTUwNjA0MTEwNDM4
WhcNMzUwNjA0MTEwNDM4WjBPMQswCQYDVQQGEwJVUzEpMCcGA1UEChMgSW50ZXJu
ZXQgU2VjdXJpdHkgUmVzZWFyY2ggR3JvdXAxFTATBgNVBAMTDElTUkcgUm9vdCBY
MTCCAiIwDQYJKoZIhvcNAQEBBQADggIPADCCAgoCggIBAK3oJHP0FDfzm54rVygc
h77ct984kIxuPOZXoHj3dcKi/vVqbvYATyjb3miGbESTtrFj/RQSa78f0uoxmyF+
0TM8ukj13Xnfs7j/EvEhmkvBioZxaUpmZmyPfjxwv60pIgbz5MDmgK7iS4+3mX6U
A5/TR5d8mUgjU+g4rk8Kb4Mu0UlXjIB0ttov0DiNewNwIRt18jA8+o+u3dpjq+sW
T8KOEUt+zwvo/7V3LvSye0rgTBIlDHCNAymg4VMk7BPZ7hm/ELNKjD+Jo2FR3qyH
B5T0Y3HsLuJvW5iB4YlcNHlsdu87kGJ55tukmi8mxdAQ4Q7e2RCOFvu396j3x+UC
B5iPNgiV5+I3lg02dZ77DnKxHZu8A/lJBdiB3QW0KtZB6awBdpUKD9jf1b0SHzUv
KBds0pjBqAlkd25HN7rOrFleaJ1/ctaJxQZBKT5ZPt0m9STJEadao0xAH0ahmbWn
OlFuhjuefXKnEgV4We0+UXgVCwOPjdAvBbI+e0ocS3MFEvzG6uBQE3xDk3SzynTn
jh8BCNAw1FtxNrQHusEwMFxIt4I7mKZ9YIqioymCzLq9gwQbooMDQaHWBfEbwrbw
qHyGO0aoSCqI3Haadr8faqU9GY/rOPNk3sgrDQoo//fb4hVC1CLQJ13hef4Y53CI
rU7m2Ys6xt0nUW7/vGT1M0NPAgMBAAGjQjBAMA4GA1UdDwEB/wQEAwIBBjAPBgNV
HRMBAf8EBTADAQH/MB0GA1UdDgQWBBR5tFnme7bl5AFzgAiIyBpY9umbbjANBgkq
hkiG9w0BAQsFAAOCAgEAVR9YqbyyqFDQDLHYGmkgJykIrGF1XIpu+ILlaS/V9lZL
ubhzEFnTIZd+50xx+7LSYK05qAvqFyFWhfFQDlnrzuBZ6brJFe+GnY+EgPbk6ZGQ
3BebYhtF8GaV0nxvwuo77x/Py9auJ/GpsMiu/X1+mvoiBOv/2X/qkSsisRcOj/KK
NFtY2PwByVS5uCbMiogziUwthDyC3+6WVwW6LLv3xLfHTjuCvjHIInNzktHCgKQ5
ORAzI4JMPJ+GslWYHb4phowim57iaztXOoJwTdwJx4nLCgdNbOhdjsnvzqvHu7Ur
TkXWStAmzOVyyghqpZXjFaH3pO3JLF+l+/+sKAIuvtd7u+Nxe5AW0wdeRlN8NwdC
jNPElpzVmbUq4JUagEiuTDkHzsxHpFKVK7q4+63SM1N95R1NbdWhscdCb+ZAJzVc
oyi3B43njTOQ5yOf+1CceWxG1bQVs5ZufpsMljq4Ui0/1lvh+wjChP4kqKOJ2qxq
4RgqsahDYVvTH9w7jXbyLeiNdd8XM2w9U/t7y0Ff/9yi0GE44Za4rF2LN9d11TPA
mRGunUHBcnWEvgJBQl9nJEiU0Zsnvgc/ubhPgXRR4Xq37Z0j4r7g1SgEEzwxA57d
emyPxgcYxn/eR44/KJ4EBs+lVDR3veyJm+kXQ99b21/+jh5Xos1AnX5iItreGCc=
-----END CERTIFICATE-----
-----BEGIN CERTIFICATE-----
MIICGzCCAaGgAwIBAgIQQdKd0XLq7qeAwSxs6S+HUjAKBggqhkjOPQQDAzBPMQsw
CQYDVQQGEwJVUzEpMCcGA1UEChMgSW50ZXJuZXQgU2VjdXJpdHkgUmVzZWFyY2gg
R3JvdXAxFTATBgNVBAMTDElTUkcgUm9vdCBYMjAeFw0yMDA5MDQwMDAwMDBaFw00
MDA5MTcxNjAwMDBaME8xCzAJBgNVBAYTAlVTMSkwJwYDVQQKEyBJbnRlcm5ldCBT
ZWN1cml0eSBSZXNlYXJjaCBHcm91cDEVMBMGA1UEAxMMSVNSRyBSb290IFgyMHYw
EAYHKoZIzj0CAQYFK4EEACIDYgAEzZvVn4CDCuwJSvMWSj5cz3es3mcFDR0HttwW
+1qLFNvicWDEukWVEYmO6gbf9yoWHKS5xcUy4APgHoIYOIvXRdgKam7mAHf7AlF9
ItgKbppbd9/w+kHsOdx1ymgHDB/qo0IwQDAOBgNVHQ8BAf8EBAMCAQYwDwYDVR0T
AQH/BAUwAwEB/zAdBgNVHQ4EFgQUfEKWrt5LSDv6kviejM9ti6lyN5UwCgYIKoZI
zj0EAwMDaAAwZQIwe3lORlCEwkSHRhtFcP9Ymd70/aTSVaYgLXTWNLxBo1BfASdW
tL4ndQavEi51mI38AjEAi/V3bNTIZargCyzuFJ0nN6T5U6VR5CmD1/iQMVtCnwr1
/q4AaOeMSQ+2b1tbFfLn
-----END CERTIFICATE-----
"""
SQL_ID_RE = re.compile(r"^[0-9]{13}_[0-9a-z]{8}$")              # sess e exec_id (ms na frente: poda por chave)
SQL_TOKEN_RE = re.compile(r"^[A-Za-z0-9_-]{22,64}$")            # relay_token
SQL_HEX64_RE = re.compile(r"^[0-9a-f]{64}$")
SQL_RELAY_RE = re.compile(r"^[a-z0-9]([a-z0-9.-]{0,251}[a-z0-9])?(:[0-9]{1,5})?$")
SQL_EXPIRE = 60                    # s: pedido de sessão mais velho que isso (hora do Firebase) é recusado
SQL_MAX_SESSIONS = 2               # sessões simultâneas por agente (abrindo ou abertas)
SQL_MAX_EXECS = 3                  # execuções simultâneas por sessão
SQL_MAX_EXECS_AGENT = 4            # execuções simultâneas no agente (cada uma = 1 conexão ao Postgres)
SQL_CONNECT_TIMEOUT = 15           # s: TCP + TLS externo até o relay (cada relay da lista)
SQL_PAIR_TIMEOUT = 40              # s esperando o 101 (o relay espera a outra ponta por 30 s e responde 504)
SQL_HELLO_TIMEOUT = 15             # s: TLS interno + hello da Central depois do 101
SQL_PING_S = 20                    # a Central manda ping a cada 20 s (sempre, inclusive durante execuções)
SQL_DEAD_S = 75                    # s sem nenhum quadro da Central = canal morto (vale também com execução ativa)
SQL_IDLE_S = 900                   # s sem execução em andamento nem exec novo = sessão ociosa (ping não conta)
SQL_SESSION_MAX = 8 * 3600         # duração máxima de uma sessão
SQL_STMT_DEFAULT, SQL_STMT_MAX = 300, 600   # statement_timeout (s) padrão e teto
SQL_CREDIT_WAIT = 600              # s com o crédito esgotado até a execução ser cancelada (transação aberta)
SQL_CREDIT_MAX = 256 << 20         # crédito acumulado máximo (bytes brutos)
SQL_FRAME_IN_MAX = 1 << 20         # quadro máximo vindo da Central
SQL_SQL_MAX = 262144               # bytes (UTF-8) do texto SQL
SQL_PARAMS_MAX = 100
SQL_BATCH_DEFAULT, SQL_BATCH_MAX, SQL_BATCH_FIRST = 1000, 10000, 100   # linhas por lote (1º lote menor)
SQL_OUT_MAX = 1 << 20              # bytes na fila de saída antes de o próximo lote esperar
SQL_POOL_MAX = 2                   # conexões ao Postgres guardadas por sessão (sem transação, DISCARD ALL)
SQL_AUDIT_SQL = 10000              # caracteres do SQL na auditoria do Firebase (o texto inteiro fica no arquivo local)
SQL_AUDIT_BATCH = 50               # auditorias por PATCH
SQL_AUDIT_QUEUE = 1000             # auditorias guardadas sem Firebase (as mais antigas saem)
SQL_RESP_KEEP = 86400              # sql_responses: 24 h
SQL_AUDIT_KEEP = 180 * 86400       # sql_audit: 180 dias
SQL_PRUNE_FIRST = 420              # s depois da partida até a 1ª poda (depois, 1x por dia)
SQL_CERT_RETRY = 600               # s até tentar de novo gerar/ler o certificado
SQL_RECENT = 500                   # execuções lembradas (estado e exec_id repetido)
SQL_ZLIB_DEFAULT = 1
SQL_ERROR_CODES = ("desligado", "expirado", "sessoes_demais", "pedido_invalido", "relay_nao_permitido",
                   "sem_certificado", "nivel_recusado", "parando", "relay_indisponivel", "relay_recusou", "sem_par",
                   "sem_hello", "nao_autorizado", "sem_banco", "canal", "interno")
SQL_MOTIVOS = ("central", "ocioso", "prazo", "morto", "desligado", "parando", "canal")
# quadros [tipo:1][tamanho:4][conteúdo]; Central -> agente (0x08-0x0f reservados: escrita/segundo fator)
SQL_C_HELLO, SQL_C_EXEC, SQL_C_CREDITO, SQL_C_CANCELAR, SQL_C_ESTADO, SQL_C_PING, SQL_C_FECHAR = range(1, 8)
SQL_C_RESERVED = range(0x08, 0x10)
# agente -> Central (0x8a-0x8f reservados)
(SQL_A_HELLO_OK, SQL_A_ACEITO, SQL_A_COLUNAS, SQL_A_LINHAS, SQL_A_FIM, SQL_A_ERRO, SQL_A_ESTADO, SQL_A_PONG,
 SQL_A_ENCERRANDO) = range(0x81, 0x8A)
SQL_HEAD = struct.Struct("!BI")
SQL_TICK = 1.0                     # s: espera máxima de cada select do canal (fechar e prazos valem em até 1 s)
WS_GUID = "258EAFA5-E914-47DA-95CA-C5AB0DC85B11"


class SqlClosed(Exception):
    """Canal com a Central fechado, ou abertura que falhou (code = error_code de sql_responses)."""

    def __init__(self, msg, code="canal", status=0):
        super().__init__(msg)
        self.code, self.status = code, status


class SqlExecError(Exception):
    """Execução recusada ou interrompida pelo agente (sqlstate próprio, ex.: 25006, 53400, C2001)."""

    def __init__(self, sqlstate, msg):
        super().__init__(msg)
        self.sqlstate = sqlstate


class SqlTcp:
    """Socket com uma thread só para enviar. send() só enfileira: quem lê o canal nunca espera o envio (a trava do
    TLS fica presa só enquanto cifra); quem produz lotes espera a fila baixar (room) antes de cifrar o próximo.
    Socket não bloqueante e toda espera num select de até SQL_TICK: fechar o canal de outra thread vale em ~1 s em
    qualquer sistema (no macOS e no Windows shutdown/close não acordam um recv parado) e deadline (instante
    monotônico, None = sem prazo) limita a espera da leitura durante a abertura."""

    def __init__(self, sock):
        sock.setblocking(False)
        self.sock, self.q, self.queued = sock, collections.deque(), 0
        self.closed = self.fin = False
        self.err = ""
        self.deadline = None
        self.cv = threading.Condition()
        threading.Thread(target=self.writer, name="sql-envio", daemon=True).start()

    def send(self, data):
        if not data:
            return
        with self.cv:
            if self.closed or self.fin:
                raise SqlClosed(self.err or "canal fechado")
            self.q.append(data)
            self.queued += len(data)
            self.cv.notify_all()

    def room(self, limit):
        with self.cv:
            while self.queued >= limit and not self.closed:
                self.cv.wait(5)
            if self.closed:
                raise SqlClosed(self.err or "canal fechado")

    def writer(self):
        while True:
            with self.cv:
                while not self.q and not self.closed:
                    if self.fin:
                        break
                    self.cv.wait()
                if self.closed or not self.q:
                    break
                data = self.q[0]
            view, pos = memoryview(data), 0
            try:
                while pos < len(data):
                    if self.closed:
                        return
                    if not select.select([], [self.sock], [], SQL_TICK)[1]:
                        continue
                    try:
                        pos += self.sock.send(view[pos:])
                    except (BlockingIOError, InterruptedError):
                        continue
            except (OSError, ValueError) as e:
                self.close(str(e) or type(e).__name__)
                return
            with self.cv:
                self.q.popleft()
                self.queued -= len(data)
                self.cv.notify_all()
        self.close()

    def finish(self, wait=0.0):
        """Fecha depois de enviar o que já está na fila (despedida, erro do hello); wait: espera até esse tempo e
        então fecha de qualquer jeito (Central parada não segura a sessão)."""
        with self.cv:
            self.fin = True
            self.cv.notify_all()
            end = time.monotonic() + wait
            while wait and not self.closed and time.monotonic() < end:
                self.cv.wait(end - time.monotonic())
        if wait:
            self.close()

    def recv(self):
        while not self.closed:
            if self.deadline is not None and time.monotonic() > self.deadline:
                return b""
            try:
                if select.select([self.sock], [], [], SQL_TICK)[0]:
                    return self.sock.recv(262144)
            except (BlockingIOError, InterruptedError):
                continue
            except (OSError, ValueError):
                return b""
        return b""

    def close(self, err=""):
        with self.cv:
            if self.closed:
                return
            self.closed, self.err = True, err
            self.cv.notify_all()
        with contextlib.suppress(OSError):
            self.sock.shutdown(socket.SHUT_RDWR)
        with contextlib.suppress(OSError):
            self.sock.close()


class SqlTls:
    """TLS sobre a camada de baixo por ssl.MemoryBIO (sem tocar no socket): TLS externo até o relay (cliente) e
    TLS interno com a Central (servidor). Uma trava protege o SSLObject; a saída cifrada vai para baixo ainda com a
    trava (a ordem dos registros se mantém) e lá embaixo só é enfileirada. Nenhuma trava espera a rede."""

    def __init__(self, low, ctx, server_side, hostname=None):
        self.low = low
        self.inb, self.outb = ssl.MemoryBIO(), ssl.MemoryBIO()
        self.obj = ctx.wrap_bio(self.inb, self.outb, server_side=server_side, server_hostname=hostname)
        self.mx = threading.Lock()

    def _flush(self):
        out = self.outb.read()
        if out:
            self.low.send(out)

    def _feed(self):
        d = self.low.recv()
        with self.mx:
            if d:
                self.inb.write(d)
            else:
                self.inb.write_eof()
        return bool(d)

    def handshake(self):
        while True:
            with self.mx:
                try:
                    self.obj.do_handshake()
                    done = True
                except ssl.SSLWantReadError:
                    done = False
                self._flush()
            if done:
                return
            if not self._feed():
                raise SqlClosed("conexão fechada durante o handshake TLS")

    def send(self, data):
        with self.mx:
            try:
                self.obj.write(data)
            except ssl.SSLError as e:
                raise SqlClosed("TLS: %s" % e)
            self._flush()

    def recv(self):
        while True:
            with self.mx:
                try:
                    d = self.obj.read(262144)
                except ssl.SSLWantReadError:
                    d = None
                except (ssl.SSLZeroReturnError, ssl.SSLEOFError):
                    d = b""
                except ssl.SSLError:
                    d = b""
                with contextlib.suppress(SqlClosed):
                    self._flush()
            if d is not None:
                return d
            if not self._feed():
                with self.mx:
                    try:
                        return self.obj.read(262144)
                    except ssl.SSLError:
                        return b""

    def version(self):
        return self.obj.version() or ""

    def peer_der(self):
        return self.obj.getpeercert(True)


class SqlWs:
    """Enquadramento WebSocket binário do lado cliente (quadros mascarados), para redes que só deixam passar
    WebSocket. O relay tira/põe o enquadramento; o conteúdo continua sendo o TLS interno."""

    def __init__(self, low, rest=b""):
        self.low, self.buf, self.mx = low, bytearray(rest), threading.Lock()

    @staticmethod
    def frame(op, data):
        n = len(data)
        h = bytearray([0x80 | op])
        if n < 126:
            h.append(0x80 | n)
        elif n <= 0xFFFF:
            h.append(0x80 | 126)
            h += struct.pack("!H", n)
        else:
            h.append(0x80 | 127)
            h += struct.pack("!Q", n)
        mk = os.urandom(4)
        m = int.from_bytes((mk * (n // 4 + 1))[:n], "big")
        body = (int.from_bytes(data, "big") ^ m).to_bytes(n, "big") if n else b""
        return bytes(h) + mk + body

    def send(self, data):
        with self.mx:
            self.low.send(self.frame(2, data))

    def _read(self, n):
        while len(self.buf) < n:
            d = self.low.recv()
            if not d:
                raise SqlClosed("websocket fechado")
            self.buf += d
        out = bytes(self.buf[:n])
        del self.buf[:n]
        return out

    def recv(self):
        try:
            while True:
                h = self._read(2)
                op, n = h[0] & 0x0F, h[1] & 0x7F
                if n == 126:
                    n = struct.unpack("!H", self._read(2))[0]
                elif n == 127:
                    n = struct.unpack("!Q", self._read(8))[0]
                if n > 4 * SQL_FRAME_IN_MAX:
                    return b""
                mk = self._read(4) if h[1] & 0x80 else None
                p = self._read(n)
                if mk:
                    m = int.from_bytes((mk * (n // 4 + 1))[:n], "big")
                    p = (int.from_bytes(p, "big") ^ m).to_bytes(n, "big") if n else b""
                if op in (0, 1, 2):
                    if p:
                        return p
                elif op == 8:
                    return b""
                elif op == 9:                                # ping -> pong
                    with self.mx, contextlib.suppress(SqlClosed):
                        self.low.send(self.frame(10, p))
        except SqlClosed:
            return b""


class SqlRest:
    """Devolve primeiro os bytes que chegaram junto com o 101."""

    def __init__(self, low, rest):
        self.low, self.rest = low, rest

    def send(self, data):
        self.low.send(data)

    def recv(self):
        if self.rest:
            d, self.rest = self.rest, b""
            return d
        return self.low.recv()


def sql_relay_split(relay):
    host, _, port = relay.partition(":")
    return host, int(port or 443)


def sql_relay_norm(relay):
    host, port = sql_relay_split(relay)
    return "%s:%d" % (host, port)


def sql_relays_parse(text):
    """Lista de relays (host[:porta], separados por vírgula) ou None se inválida."""
    items = [x.strip() for x in text.split(",")] if isinstance(text, str) else []
    if not items or len(items) > 8 or not all(SQL_RELAY_RE.match(x) for x in items):
        return None
    if any(not 1 <= sql_relay_split(x)[1] <= 65535 for x in items):
        return None
    return items


def sql_proxy_for(host):
    """Proxy HTTP do ambiente (https_proxy, respeitando no_proxy) para chegar ao relay: (host, porta, autorização)
    ou None. Só proxy HTTP com CONNECT (o mesmo que o urllib usa para o Firebase)."""
    try:
        if urllib.request.proxy_bypass(host):
            return None
        url = urllib.request.getproxies().get("https")
    except Exception:                                     # configuração de proxy do sistema ilegível: direto
        return None
    if not url:
        return None
    u = urllib.parse.urlsplit(url if "://" in url else "http://" + url)
    if not u.hostname or u.scheme not in ("http", ""):
        return None
    auth = None
    if u.username:
        cred = "%s:%s" % (urllib.parse.unquote(u.username), urllib.parse.unquote(u.password or ""))
        auth = "Basic " + base64.b64encode(cred.encode("utf-8")).decode()
    return u.hostname, u.port or 3128, auth


def sql_read_head(recv, limit=16384):
    """Lê até o fim do cabeçalho HTTP: (status, cabeçalho em texto, bytes que vieram depois)."""
    buf = b""
    while b"\r\n\r\n" not in buf:
        d = recv()
        if not d:
            raise SqlClosed("conexão fechada antes da resposta HTTP")
        buf += d
        if len(buf) > limit:
            raise SqlClosed("resposta HTTP grande demais")
    head, _, rest = buf.partition(b"\r\n\r\n")
    text = head.decode("latin-1")
    first = text.split("\r\n", 1)[0].split(" ")
    status = int(first[1]) if len(first) > 1 and first[1].isdigit() else 0
    return status, text, rest


def sql_connect(relay, timeout):
    """TCP até o relay, direto ou pelo CONNECT do proxy do ambiente. Devolve o socket."""
    host, port = sql_relay_split(relay)
    px = sql_proxy_for(host)
    target = (px[0], px[1]) if px else (host, port)
    try:
        sock = socket.create_connection(target, timeout)
    except OSError as e:
        raise SqlClosed("%s: sem conexão%s (%s)" % (relay, " com o proxy %s:%d" % target if px else "",
                                                    e.strerror or e), "relay_indisponivel")
    sock.settimeout(timeout)
    with contextlib.suppress(OSError, AttributeError):
        sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_KEEPALIVE, 1)
        sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_KEEPIDLE, 20)
        sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_KEEPINTVL, 10)
        sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_KEEPCNT, 3)
    if px:
        req = "CONNECT %s:%d HTTP/1.1\r\nHost: %s:%d\r\n" % (host, port, host, port)
        if px[2]:
            req += "Proxy-Authorization: %s\r\n" % px[2]
        try:
            sock.sendall((req + "\r\n").encode())

            def rd():
                try:
                    return sock.recv(4096)
                except OSError:
                    return b""
            status, _, rest = sql_read_head(rd)
        except (OSError, SqlClosed) as e:
            sock.close()
            raise SqlClosed("proxy %s:%d: %s" % (px[0], px[1], e), "relay_indisponivel")
        if status != 200 or rest:
            sock.close()
            raise SqlClosed("o proxy %s:%d recusou o CONNECT para %s (HTTP %d)" % (px[0], px[1], relay, status),
                            "relay_indisponivel")
    return sock


def sql_relay_ctx():
    """TLS externo até o relay: cadeia pública e nome conferidos (o relay usa certificado público válido)."""
    ctx = ssl.create_default_context(cafile=SQL_RELAY_CAFILE) if SQL_RELAY_CAFILE else ssl.create_default_context()
    ctx.load_verify_locations(cadata=SQL_RELAY_ROOTS)    # + ISRG Root X1/X2 (Windows sem a raiz no repositório)
    ctx.minimum_version = ssl.TLSVersion.TLSv1_2
    return ctx


def sql_tls_reason(e):
    """Motivo curto de uma falha de TLS: 'CERTIFICATE_VERIFY_FAILED unable to get local issuer certificate'."""
    reason = getattr(e, "reason", None)
    detail = getattr(e, "verify_message", None)
    if not reason:
        return str(e)
    return "%s %s" % (reason, detail) if detail else str(reason)


def sql_dial(relay, token, sid, bearer, ctx, ws=False, on_sent=None, on_tcp=None):
    """Perna agente -> relay: TCP (ou CONNECT), TLS verificado, GET /t/<token>?lado=a&sid=<sid> com Upgrade
    (c2-tunnel ou websocket) e Authorization: Bearer <ID token>. Devolve (camada pronta, SqlTcp, versão TLS)."""
    host, port = sql_relay_split(relay)
    sock = sql_connect(relay, SQL_CONNECT_TIMEOUT)
    tcp = SqlTcp(sock)
    tcp.deadline = time.monotonic() + SQL_CONNECT_TIMEOUT
    if on_tcp is not None:
        on_tcp(tcp)                                      # quem disca pode interromper a espera do 101 (parada)
    try:
        layer = SqlTls(tcp, ctx, False, host)
        try:
            layer.handshake()
        except (ssl.SSLError, OSError) as e:
            raise SqlClosed("%s: TLS %s" % (relay, sql_tls_reason(e)), "relay_indisponivel")
        except SqlClosed as e:
            raise SqlClosed("%s: TLS %s" % (relay, e), "relay_indisponivel")
        hdr = ["GET /t/%s?lado=a&sid=%s HTTP/1.1" % (token, sid), "Host: %s" % (host if port == 443 else relay),
               "User-Agent: usage-monitor/%s" % VERSION, "Authorization: Bearer %s" % bearer, "Connection: Upgrade"]
        key = base64.b64encode(os.urandom(16)).decode()
        if ws:
            hdr += ["Upgrade: websocket", "Sec-WebSocket-Version: 13", "Sec-WebSocket-Key: " + key]
        else:
            hdr += ["Upgrade: c2-tunnel"]
        layer.send(("\r\n".join(hdr) + "\r\n\r\n").encode())
        if on_sent is not None:
            on_sent()
        tcp.deadline = time.monotonic() + SQL_PAIR_TIMEOUT
        try:
            status, text, rest = sql_read_head(layer.recv)
        except SqlClosed as e:
            raise SqlClosed("%s: %s" % (relay, e), "relay_indisponivel", -1)      # -1: caiu antes da resposta
        if status != 101:
            code = {504: "sem_par", 401: "relay_recusou", 403: "relay_recusou", 409: "relay_recusou",
                    429: "relay_recusou"}.get(status, "relay_indisponivel")
            raise SqlClosed("%s respondeu HTTP %d" % (relay, status), code, status)
        if ws:
            accept = base64.b64encode(hashlib.sha1((key + WS_GUID).encode()).digest()).decode()
            if accept.lower() not in text.lower():
                raise SqlClosed("%s: Sec-WebSocket-Accept inválido" % relay, "relay_indisponivel")
            return SqlWs(layer, rest), tcp, layer.version()
        return (SqlRest(layer, rest) if rest else layer), tcp, layer.version()
    except BaseException:
        tcp.close()
        raise


# Certificado do TLS interno sem o binário openssl (v2.12.1: Windows não tem openssl). ECDSA P-256 em inteiros
# Python (coordenadas afins, inverso por pow(x, -1, p) do 3.8), nonce determinístico RFC 6979 e X.509 v3 em DER.
EC_P = 2 ** 256 - 2 ** 224 + 2 ** 192 + 2 ** 96 - 1
EC_N = 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551
EC_B = 0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B
EC_G = (0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296,
        0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5)
OID_EC_PUBKEY, OID_P256, OID_ECDSA_SHA256 = "1.2.840.10045.2.1", "1.2.840.10045.3.1.7", "1.2.840.10045.4.3.2"


def ec_add(a, b):
    """Soma de pontos da P-256 (None = ponto no infinito; a = -3)."""
    if a is None:
        return b
    if b is None:
        return a
    if a[0] == b[0]:
        if (a[1] + b[1]) % EC_P == 0:
            return None
        lam = (3 * a[0] * a[0] - 3) * pow(2 * a[1], -1, EC_P) % EC_P
    else:
        lam = (b[1] - a[1]) * pow(b[0] - a[0], -1, EC_P) % EC_P
    x = (lam * lam - a[0] - b[0]) % EC_P
    return x, (lam * (a[0] - x) - a[1]) % EC_P


def ec_mul(k, pt=EC_G):
    out = None
    while k:
        if k & 1:
            out = ec_add(out, pt)
        pt, k = ec_add(pt, pt), k >> 1
    return out


def ecdsa_sign(d, msg):
    """(r, s) de ECDSA-SHA256 com k determinístico (RFC 6979 §3.2; qlen = hlen = 256)."""
    h = hashlib.sha256(msg).digest()
    e = int.from_bytes(h, "big")
    x, h1 = d.to_bytes(32, "big"), (e % EC_N).to_bytes(32, "big")
    v, k = b"\x01" * 32, b"\x00" * 32
    for sep in (b"\x00", b"\x01"):
        k = hmac.new(k, v + sep + x + h1, hashlib.sha256).digest()
        v = hmac.new(k, v, hashlib.sha256).digest()
    while True:
        v = hmac.new(k, v, hashlib.sha256).digest()
        t = int.from_bytes(v, "big")
        if 1 <= t < EC_N:
            r = ec_mul(t)[0] % EC_N
            s = pow(t, -1, EC_N) * (e + r * d) % EC_N
            if r and s:
                return r, s
        k = hmac.new(k, v + b"\x00", hashlib.sha256).digest()      # r ou s nulo (~2^-128): próximo k
        v = hmac.new(k, v, hashlib.sha256).digest()


def der(tag, body):
    n = len(body)
    if n < 0x80:
        size = bytes([n])
    else:
        raw = n.to_bytes((n.bit_length() + 7) // 8, "big")
        size = bytes([0x80 | len(raw)]) + raw
    return bytes([tag]) + size + body


def der_seq(*items):
    return der(0x30, b"".join(items))


def der_int(v):
    return der(0x02, v.to_bytes(v.bit_length() // 8 + 1, "big"))       # +1 byte: positivo (bit alto zerado)


def der_oid(dotted):
    parts = [int(p) for p in dotted.split(".")]
    out = bytearray([40 * parts[0] + parts[1]])
    for p in parts[2:]:
        chunk = [p & 0x7F]
        p >>= 7
        while p:
            chunk.append(0x80 | (p & 0x7F))
            p >>= 7
        out += bytes(reversed(chunk))
    return der(0x06, bytes(out))


def der_time(t):
    """UTCTime até 2049, GeneralizedTime a partir de 2050 (RFC 5280 §4.1.2.5)."""
    if t.year < 2050:
        return der(0x17, t.strftime("%y%m%d%H%M%SZ").encode())
    return der(0x18, t.strftime("%Y%m%d%H%M%SZ").encode())


def der_read(buf, pos):
    """(tag, início do conteúdo, fim) do TLV em buf[pos:]; ValueError se truncado."""
    tag, n = buf[pos], buf[pos + 1]
    pos += 2
    if n & 0x80:
        cnt = n & 0x7F
        if not 1 <= cnt <= 4:
            raise ValueError("tamanho DER inválido")
        n = int.from_bytes(buf[pos:pos + cnt], "big")
        pos += cnt
    if pos + n > len(buf):
        raise ValueError("DER truncado")
    return tag, pos, pos + n


def der_children(buf, start, end):
    out = []
    while start < end:
        item = der_read(buf, start)
        out.append(item)
        start = item[2]
    return out


def cert_not_after(cert_der):
    """notAfter (UTC, datetime ingênuo) do certificado X.509 em DER, sem openssl."""
    _, s, e = der_read(cert_der, 0)
    _, s, e = der_read(cert_der, s)                                      # tbsCertificate
    kids = der_children(cert_der, s, e)
    if kids and kids[0][0] == 0xA0:                                      # [0] version
        kids = kids[1:]
    validity = der_children(cert_der, kids[3][1], kids[3][2])
    tag, s, e = validity[1]
    text = cert_der[s:e].decode("ascii")
    if tag == 0x17:
        return datetime.datetime.strptime(text, "%y%m%d%H%M%SZ")
    if tag == 0x18:
        return datetime.datetime.strptime(text, "%Y%m%d%H%M%SZ")
    raise ValueError("tempo DER desconhecido")


def sql_cert_make(sid=""):
    """(PEM do certificado, PEM da chave "EC PRIVATE KEY" SEC1) autoassinados: ECDSA P-256, 10 anos, CN
    usage-monitor-sql-<sid[:12]>, basicConstraints CA:FALSE e extendedKeyUsage serverAuth."""
    d = secrets.randbelow(EC_N - 1) + 1
    qx, qy = ec_mul(d)
    point = b"\x04" + qx.to_bytes(32, "big") + qy.to_bytes(32, "big")
    alg = der_seq(der_oid(OID_ECDSA_SHA256))
    name = der_seq(der(0x31, der_seq(der_oid("2.5.4.3"), der(0x0C, ("usage-monitor-sql-%s" % (
        sid[:12] or "agente")).encode()))))
    now = datetime.datetime.now(datetime.timezone.utc).replace(tzinfo=None).replace(microsecond=0)
    exts = der(0xA3, der_seq(
        der_seq(der_oid("2.5.29.19"), der(0x01, b"\xff"), der(0x04, der_seq())),
        der_seq(der_oid("2.5.29.37"), der(0x04, der_seq(der_oid("1.3.6.1.5.5.7.3.1"))))))
    tbs = der_seq(der(0xA0, der_int(2)), der_int(secrets.randbits(127) | 1 << 126), alg, name,
                  der_seq(der_time(now - datetime.timedelta(days=1)), der_time(now + datetime.timedelta(days=3650))),
                  name, der_seq(der_seq(der_oid(OID_EC_PUBKEY), der_oid(OID_P256)), der(0x03, b"\x00" + point)),
                  exts)
    r, s = ecdsa_sign(d, tbs)
    cert = der_seq(tbs, alg, der(0x03, b"\x00" + der_seq(der_int(r), der_int(s))))
    key = der_seq(der_int(1), der(0x04, d.to_bytes(32, "big")), der(0xA0, der_oid(OID_P256)),
                  der(0xA1, der(0x03, b"\x00" + point)))
    b64 = base64.encodebytes(key).decode().replace("\n", "")
    key_pem = "-----BEGIN EC PRIVATE KEY-----\n%s\n-----END EC PRIVATE KEY-----\n" % "\n".join(
        b64[i:i + 64] for i in range(0, len(b64), 64))
    return ssl.DER_cert_to_PEM_cert(cert), key_pem


def sql_cert_expiring(cert):
    """O certificado vence em menos de 30 dias? Lê o notAfter do DER (sem openssl); ilegível = não (o load decide)."""
    try:
        with open(cert) as f:
            end = cert_not_after(ssl.PEM_cert_to_DER_cert(f.read()))
    except (OSError, ValueError, IndexError):
        return False
    return end - datetime.datetime.now(datetime.timezone.utc).replace(tzinfo=None) < datetime.timedelta(days=30)


def sql_cert(cert, key, sid=""):
    """(impressão digital SHA-256 do DER, contexto TLS servidor). Gera o par uma vez (chave ECDSA P-256, 10 anos,
    arquivos 600) com o binário openssl se houver, senão em Python puro (`sql_cert_make`: Windows); refaz se faltar
    um dos dois, se não carregar ou se vencer em 30 dias."""
    def load():
        ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
        ctx.minimum_version = ssl.TLSVersion.TLSv1_2
        ctx.load_cert_chain(cert, key)
        with open(cert) as f:
            der = ssl.PEM_cert_to_DER_cert(f.read())
        return hashlib.sha256(der).hexdigest(), ctx
    if os.path.exists(cert) and os.path.exists(key):
        with contextlib.suppress(OSError):
            os.chmod(key, 0o600)
            os.chmod(cert, 0o600)
        if not sql_cert_expiring(cert):
            try:
                return load()
            except (ssl.SSLError, OSError, ValueError):
                pass
    exe = shutil.which("openssl")
    tk, tc = key + ".novo", cert + ".novo"
    old = os.umask(0o077)
    try:
        for f in (tk, tc):
            with contextlib.suppress(FileNotFoundError):
                os.remove(f)
        if exe is None:
            cert_pem, key_pem = sql_cert_make(sid)
            for f, text in ((tk, key_pem), (tc, cert_pem)):
                with open(f, "w") as fh:
                    fh.write(text)
        else:
            subprocess.check_call([exe, "ecparam", "-name", "prime256v1", "-genkey", "-noout", "-out", tk],
                                  stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            subprocess.check_call([exe, "req", "-new", "-x509", "-key", tk, "-out", tc, "-days", "3650", "-sha256",
                                   "-subj", "/CN=usage-monitor-sql-%s" % (sid[:12] or "agente")],
                                  stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    except subprocess.CalledProcessError as e:
        raise OSError("openssl falhou ao gerar o certificado do editor SQL (código %d)" % e.returncode)
    finally:
        os.umask(old)
    for f in (tk, tc):
        os.chmod(f, 0o600)
    os.replace(tk, key)
    os.replace(tc, cert)
    return load()


def sql_probe(relay, timeout=8):
    """Diagnóstico: TCP (ou CONNECT) + TLS verificado até o relay, sem Upgrade."""
    if ssl is None:
        return "sem TLS neste Python"
    try:
        sock = sql_connect(relay, timeout)
    except SqlClosed as e:
        msg = str(e)
        return "erro: %s" % (msg[len(relay) + 2:] if msg.startswith(relay + ": ") else msg)   # o relay já está na linha
    try:
        with sql_relay_ctx().wrap_socket(sock, server_hostname=sql_relay_split(relay)[0]) as s:
            return "TLS ok (%s)" % s.version()
    except (ssl.SSLError, OSError) as e:
        return "erro de TLS: %s" % sql_tls_reason(e)


def sql_json_rows(parts):
    """Formato 'json': uma linha JSON (lista de textos ou null) por registro, a partir das DataRow cruas."""
    out = []
    for pt in parts:
        i, end = 0, len(pt)
        while i < end:
            n = int.from_bytes(pt[i + 1:i + 5], "big") + 1
            p, pos, row = pt[i + 5:i + n], 2, []
            for _ in range(int.from_bytes(p[:2], "big")):
                ln = int.from_bytes(p[pos:pos + 4], "big", signed=True)
                pos += 4
                if ln < 0:
                    row.append(None)
                else:
                    row.append(p[pos:pos + ln].decode("utf-8", "replace"))
                    pos += ln
            out.append(json.dumps(row, ensure_ascii=False, separators=(",", ":")))
            i += n
    return ("\n".join(out) + "\n").encode("utf-8") if out else b""


def sql_int(v, lo, hi, default):
    """Inteiro do pedido dentro de [lo, hi]; ausente = padrão; fora = ValueError."""
    if v is None:
        return default
    if not is_int(v) or not lo <= v <= hi:
        raise ValueError
    return v


class SqlExec:
    def __init__(self, exec_id, d):
        self.id, self.d = exec_id, d
        self.cv = threading.Condition()
        self.credit, self.cancelled, self.pg = 0, False, None
        self.rows = self.batches = self.raw = self.sent = 0
        self.thread = None
        self.final = None                 # estado final, já valendo antes do fim/erro sair (estado_resp sem corrida)


class SqlSession:
    """Uma sessão do editor: abre a perna até o relay (na ordem do pedido, só relays permitidos), faz o TLS interno
    como servidor, confere o sess_key (o pedido traz só o hash) e atende os quadros. Leitura em fluxo: portal com
    Execute limitado repetido só com crédito da Central; cancelamento por CancelRequest. Toda saída libera a vaga."""

    def __init__(self, ed, sess, req, relays):
        self.ed, self.sess, self.req, self.relays = ed, sess, req, relays
        self.by, self.fmt = req["by"], req["formato"]
        self.mx = threading.Lock()
        self.execs, self.pool = {}, []
        self.chan = self.tcp = None
        self.relay, self.tls_ver = "", ""
        self.state = "abrindo"
        self.closing = ""
        self.t0 = self.last_rx = self.last_act = time.monotonic()
        self.t_end = None
        self.nexec = 0
        self.thread = None
        self.announced = ""
        self.frames = iter(())
        self.dialing = None               # SqlTcp da tentativa em curso (end() interrompe a espera do 101)

    # ---- ciclo de vida ----
    def run(self):
        code, msg, opened = "", "", False
        try:
            self.open()
            opened = True
            self.ed.audit_line({"ev": "sessao_aberta", "sess": self.sess, "by": self.by, "relay": self.relay})
            self.serve()
        except SqlClosed as e:
            code, msg = e.code, str(e)
        except Exception as e:                            # defeito inesperado: registra e não vaza a vaga
            code, msg = "interno", "erro interno: %s" % type(e).__name__
        finally:
            self.finish(opened, code, msg)

    def finish(self, opened, code, msg):
        self.state = "fechada"
        with self.mx:
            execs = list(self.execs.values())
        for e in execs:                                   # Central sumiu ou sessão encerrada: cancela no Postgres
            self.cancel(e)
        if self.tcp is not None:
            self.tcp.finish(2.0)                          # erro/despedida já na fila saem; libera quem espera a fila
        for e in execs:
            if e.thread is not None:
                e.thread.join(5)
        with self.mx:
            pool, self.pool = self.pool, []
        for pg in pool:
            pg.close()
        ms = round((time.monotonic() - self.t0) * 1000)
        if opened:
            motivo = self.closing or "canal"
            doc = {"state": "encerrada", "ok": True, "motivo": motivo, "execs": self.nexec, "ms": ms}
            self.ed.audit_line({"ev": "sessao_encerrada", "sess": self.sess, "by": self.by, "motivo": motivo,
                                "execs": self.nexec, "ms": ms})
        else:
            if self.closing in ("parando", "desligado"):
                code, msg = self.closing, "sessão encerrada pelo agente durante a abertura (%s)" % self.closing
            code = code if code in SQL_ERROR_CODES else "interno"
            doc = {"state": "falhou", "ok": False, "error_code": code, "error": clip(msg or code, 500), "ms": ms}
            self.ed.audit_line({"ev": "sessao_falhou", "sess": self.sess, "by": self.by, "error_code": code,
                                "error": clip(msg, 500)})
        self.ed.release(self, doc)

    def end(self, motivo, msg=""):
        """Encerramento pedido pelo agente (ocioso, prazo, desligado, parando): despedida e fecha. Ainda abrindo
        (sem TLS interno pronto): só fecha o que houver, sem quadro."""
        if self.closing:
            return
        self.closing, self.t_end = motivo, time.monotonic()
        if self.state != "aberta" or self.tcp is None:
            for t in (self.tcp, self.dialing):
                if t is not None:
                    t.close()
            return
        with contextlib.suppress(SqlClosed):
            self.send(SQL_A_ENCERRANDO, {"motivo": motivo, "msg": msg or motivo})
        self.tcp.finish()

    def kill(self, motivo):
        self.closing = self.closing or motivo
        if self.tcp is not None:
            self.tcp.close()

    def check(self, now):
        """Vigia (thread de controle, ~1 s): canal mudo, ociosidade (só sem execução), duração máxima."""
        if self.state != "aberta":
            return
        if self.closing:
            if self.t_end is not None and now - self.t_end > 5:
                self.kill(self.closing)                   # despedida não saiu (Central parada): fecha de vez
            return
        with self.mx:
            busy = bool(self.execs)
        if now - self.last_rx > SQL_DEAD_S:
            self.kill("morto")
        elif not busy and now - self.last_act > SQL_IDLE_S:
            self.end("ocioso", "sessão sem uso há %d min" % (SQL_IDLE_S // 60))
        elif now - self.t0 > SQL_SESSION_MAX:
            self.end("prazo", "duração máxima da sessão (%d h)" % (SQL_SESSION_MAX // 3600))

    # ---- abertura ----
    def open(self):
        ctx = sql_relay_ctx()
        try:
            bearer = self.ed.live.token()
        except CloudError as e:
            raise SqlClosed("sem o token do Firebase para o relay (%s)" % e, "interno")
        token, errs, last = self.req["relay_token"], [], "relay_indisponivel"
        for relay in self.relays:
            for ws in (False, True):
                if self.ed.stop_ev.is_set() or self.closing:
                    break
                try:
                    chan, tcp, ver = sql_dial(relay, token, self.ed.sid, bearer, ctx, ws,
                                              on_sent=lambda r=relay: self.announce(r),
                                              on_tcp=lambda t: setattr(self, "dialing", t))
                except SqlClosed as e:
                    if e.code == "sem_par":
                        raise
                    if not ws and e.code == "relay_indisponivel" and e.status in (-1, 400, 405, 426, 501):
                        continue                          # proxy que barra o Upgrade cru: tenta WebSocket
                    errs.append(str(e))
                    last = e.code
                    break
                self.chan, self.tcp, self.relay, self.tls_ver = chan, tcp, relay, ver
                break
            if self.tcp is not None:
                break
        if self.ed.stop_ev.is_set() or self.closing:
            if self.tcp is not None:
                self.tcp.close()
            raise SqlClosed("sessão encerrada pelo agente durante a abertura (%s)" % (self.closing or "parando"),
                            self.closing if self.closing == "desligado" else "parando")
        if self.tcp is None:
            raise SqlClosed(clip("; ".join(errs) or "nenhum relay", 480), last)
        self.tcp.deadline = time.monotonic() + SQL_HELLO_TIMEOUT
        tls = SqlTls(self.chan, self.ed.server_ctx, True)
        try:
            tls.handshake()
        except (ssl.SSLError, OSError, SqlClosed) as e:
            raise SqlClosed("TLS interno falhou (%s)" % (getattr(e, "reason", None) or e), "canal")
        self.chan = tls
        self.frames = self.read_frames()
        t, p = next(self.frames, (None, None))
        if t != SQL_C_HELLO:
            self.err(None, "08P01", "esperava o quadro hello")
            raise SqlClosed("a Central não mandou o hello", "sem_hello")
        try:
            h = json.loads(p.decode("utf-8"))
            key = h["sess_key"]
            proto = h.get("proto", 1)
            ok = (isinstance(key, str) and h.get("sess") == self.sess and hmac.compare_digest(
                hashlib.sha256(key.encode("utf-8")).hexdigest(), self.req["sess_key_sha256"]))
        except (ValueError, KeyError, TypeError, AttributeError):
            ok, proto = False, 1
        if not ok:
            self.err(None, "28000", "sessão não autorizada")
            raise SqlClosed("sess_key ou sess inválidos no hello", "nao_autorizado")
        if not is_int(proto) or proto < 1:
            self.err(None, "08P01", "versão de protocolo não suportada")
            raise SqlClosed("hello com proto inválido", "sem_hello")
        try:
            pg = self.pg_get()
        except DbError as e:
            self.err(None, e.sqlstate or "08001", "sem conexão com o PostgreSQL: %s" % e)
            raise SqlClosed("sem conexão com o PostgreSQL (%s)" % e, "sem_banco")
        version = pg.server_version
        self.pg_put(pg)
        self.send(SQL_A_HELLO_OK, {
            "proto": min(proto, SQL_PROTO), "agente": VERSION, "sess": self.sess, "pg_version": clip(version, 128),
            "nivel": "leitura", "formatos": ["pg", "json"], "formato": self.fmt, "tls": tls.version(),
            "limites": {"consultas": SQL_MAX_EXECS, "consultas_agente": SQL_MAX_EXECS_AGENT,
                        "sql_bytes": SQL_SQL_MAX, "params": SQL_PARAMS_MAX, "lote_max": SQL_BATCH_MAX,
                        "credito_max": SQL_CREDIT_MAX, "timeout_padrao_s": SQL_STMT_DEFAULT,
                        "timeout_max_s": SQL_STMT_MAX, "ping_s": SQL_PING_S, "morto_s": SQL_DEAD_S,
                        "ocioso_s": SQL_IDLE_S, "sessao_max_s": SQL_SESSION_MAX, "quadro_max": SQL_FRAME_IN_MAX,
                        "credito_espera_s": SQL_CREDIT_WAIT}})
        self.tcp.deadline = None                          # aberto: daqui em diante quem decide é o vigia
        self.last_rx = self.last_act = time.monotonic()
        self.state = "aberta"

    def announce(self, relay):
        """Upgrade enviado a este relay: a Central fica sabendo onde encontrar o agente (e o pedido sai)."""
        if relay == self.announced:
            return
        self.announced = relay
        self.ed.respond(self.sess, {"state": "conectando", "ok": True, "relay": relay, "proto": SQL_PROTO},
                        drop=True)

    # ---- quadros ----
    def read_frames(self):
        buf = bytearray()
        while True:
            while len(buf) >= 5:
                t, n = SQL_HEAD.unpack_from(buf)
                if n > SQL_FRAME_IN_MAX:
                    raise SqlClosed("quadro da Central grande demais (%d bytes)" % n)
                if len(buf) < 5 + n:
                    break
                p = bytes(buf[5:5 + n])
                del buf[:5 + n]
                yield t, p
            d = self.chan.recv()
            if not d:
                return
            self.last_rx = time.monotonic()
            buf += d

    def send(self, t, obj, bulk=False):
        payload = obj if isinstance(obj, bytes) else json.dumps(obj, ensure_ascii=False,
                                                                separators=(",", ":")).encode("utf-8")
        if bulk:
            self.tcp.room(SQL_OUT_MAX)
        self.chan.send(SQL_HEAD.pack(t, len(payload)) + payload)

    def err(self, exec_id, sqlstate, msg, **extra):
        doc = {"sqlstate": sqlstate, "msg": clip(msg, 2000)}
        if exec_id is not None:
            doc["exec_id"] = exec_id
        doc.update({k: v for k, v in extra.items() if v is not None})
        with contextlib.suppress(SqlClosed):
            self.send(SQL_A_ERRO, doc)

    def serve(self):
        for t, p in self.frames:
            if not self.handle(t, p):
                return

    def handle(self, t, p):
        if t in (SQL_C_PING, SQL_C_EXEC, SQL_C_CREDITO, SQL_C_CANCELAR, SQL_C_ESTADO, SQL_C_FECHAR):
            try:
                d = json.loads(p.decode("utf-8")) if p else {}
                if not isinstance(d, dict):
                    raise ValueError
            except ValueError:
                self.err(None, "08P01", "quadro com JSON inválido (tipo %d)" % t)
                return True
        else:
            self.err(None, "0A000" if t in SQL_C_RESERVED else "08P01",
                     "quadro %s nesta versão do agente (tipo %d)" % (
                         "não suportado" if t in SQL_C_RESERVED else "desconhecido", t))
            return True
        eid = d.get("exec_id") if isinstance(d.get("exec_id"), str) else None
        if t == SQL_C_PING:
            with self.mx:
                prog = {k: {"linhas": e.rows, "lotes": e.batches} for k, e in self.execs.items()}
            self.send(SQL_A_PONG, dict(d, t=int(time.time() * 1000), execs=prog))
        elif t == SQL_C_EXEC:
            self.last_act = time.monotonic()
            self.start_exec(d)
        elif t == SQL_C_CREDITO:
            e = self.execs.get(eid)
            n = d.get("bytes")
            if e is not None and is_int(n) and n > 0:
                with e.cv:
                    e.credit = min(SQL_CREDIT_MAX, e.credit + n)
                    e.cv.notify_all()
        elif t == SQL_C_CANCELAR:
            e = self.execs.get(eid)
            if e is not None:
                self.cancel(e)
        elif t == SQL_C_ESTADO:
            e = self.execs.get(eid)
            st = (e.final or "executando") if e is not None else self.ed.exec_state(eid)
            self.send(SQL_A_ESTADO, {"exec_id": eid, "estado": st})
        else:                                             # fechar
            self.closing = "central"
            return False
        return True

    # ---- execuções ----
    def start_exec(self, d):
        eid = d.get("exec_id")
        if not isinstance(eid, str) or not SQL_ID_RE.match(eid):
            return self.err(eid if isinstance(eid, str) else None, "C2003",
                            "exec_id inválido (formato ^[0-9]{13}_[0-9a-z]{8}$)")
        try:
            if d.get("modo", "leitura") != "leitura":
                raise SqlExecError("25006", "este agente só executa leitura (modo %r recusado)" % d.get("modo"))
            sql = d.get("sql")
            if not isinstance(sql, str) or not sql.strip():
                raise SqlExecError("C2003", "sql vazio")
            if len(sql.encode("utf-8")) > SQL_SQL_MAX:
                raise SqlExecError("54000", "sql maior que %d KB" % (SQL_SQL_MAX // 1024))
            params = d.get("params") or []
            if not isinstance(params, list) or len(params) > SQL_PARAMS_MAX or not all(
                    v is None or isinstance(v, str) for v in params):
                raise SqlExecError("C2003", "params deve ser uma lista de até %d textos ou null" % SQL_PARAMS_MAX)
            fmt = d.get("formato", self.fmt)
            if fmt not in ("pg", "json"):
                raise SqlExecError("C2003", "formato desconhecido: %r" % fmt)
            try:
                opt = {"zlib": sql_int(d.get("zlib"), 0, 9, SQL_ZLIB_DEFAULT),
                       "lote": sql_int(d.get("lote_linhas"), 1, SQL_BATCH_MAX, SQL_BATCH_DEFAULT),
                       "credito": min(SQL_CREDIT_MAX, sql_int(d.get("credito_bytes"), 0, 2 ** 53, 1 << 20)),
                       "timeout": sql_int(d.get("timeout_s"), 1, SQL_STMT_MAX, SQL_STMT_DEFAULT),
                       "max": sql_int(d.get("max_linhas"), 0, 2 ** 31 - 1, 0)}
            except ValueError:
                raise SqlExecError("C2003", "zlib, lote_linhas, credito_bytes, timeout_s ou max_linhas fora dos limites")
            if self.ed.exec_known(eid):
                raise SqlExecError("C2001", "exec_id já recebido: nada foi reexecutado")
        except SqlExecError as e:
            return self.err(eid, e.sqlstate, str(e))
        with self.ed.mx:
            with self.mx:
                if len(self.execs) >= SQL_MAX_EXECS or self.ed.exec_count() >= SQL_MAX_EXECS_AGENT:
                    busy = True
                else:
                    busy = False
                    e = SqlExec(eid, dict(opt, sql=sql, params=params, fmt=fmt))
                    e.credit = opt["credito"]
                    self.execs[eid] = e
                    self.nexec += 1
        if busy:
            return self.err(eid, "53400", "execuções simultâneas demais (máximo %d por sessão, %d no agente)" % (
                SQL_MAX_EXECS, SQL_MAX_EXECS_AGENT))
        self.ed.remember(eid, "executando")
        e.thread = threading.Thread(target=self.run_exec, args=(e,), name="sql-exec", daemon=True)
        e.thread.start()

    def cancel(self, e):
        with e.cv:
            e.cancelled = True
            e.cv.notify_all()
        pg = e.pg
        if pg is not None:
            pg.cancel()

    def pg_get(self):
        with self.mx:
            if self.pool:
                return self.pool.pop()
        c = self.ed.db.cfg
        if not c:
            raise DbError("conexao", "conexão com o banco não configurada")
        return PgConn(c.get("host"), c.get("port"), c.get("dbname") or "", c.get("user") or "",
                      c.get("password") or "", c.get("sslmode"), app="usage_monitor_sql")

    def pg_put(self, pg):
        with self.mx:
            keep = self.state != "fechada" and len(self.pool) < SQL_POOL_MAX and pg.tx == b"I"
            if keep:
                self.pool.append(pg)
        if not keep:
            pg.close()

    def run_exec(self, e):
        t0, started = time.monotonic(), int(self.ed.live.server_now() * 1000)
        st, sqlstate, msg, tag, truncated, pg = "erro", None, "", "", False, None
        o = e.d
        try:
            self.send(SQL_A_ACEITO, {"exec_id": e.id})
            if e.cancelled:
                raise SqlExecError("57014", "cancelada pelo operador")
            pg = e.pg = self.pg_get()
            pg.sock.settimeout(o["timeout"] + 30)
            pg.simple("BEGIN TRANSACTION READ ONLY; SET LOCAL statement_timeout = %d" % (o["timeout"] * 1000))
            cols, oids = pg.portal(o["sql"], o["params"])
            self.send(SQL_A_COLUNAS, {"exec_id": e.id, "nomes": cols, "tipos": oids, "formato": o["fmt"]})
            z = zlib.compressobj(o["zlib"]) if o["zlib"] else None
            eid = e.id.encode()
            while True:
                with e.cv:
                    wait_end = time.monotonic() + SQL_CREDIT_WAIT
                    while e.credit <= 0 and not e.cancelled:
                        left = wait_end - time.monotonic()
                        if left <= 0:
                            raise SqlExecError("C2002", "sem crédito da Central há %d min: execução cancelada"
                                               % (SQL_CREDIT_WAIT // 60))
                        e.cv.wait(min(left, 5))
                    if e.cancelled:
                        raise SqlExecError("57014", "cancelada pelo operador")
                want = min(o["lote"], SQL_BATCH_FIRST) if not e.batches else o["lote"]
                if o["max"]:
                    want = min(want, o["max"] - e.rows)
                parts, n, tag, suspended = pg.batch(want)
                e.batches += 1
                if n:
                    data = sql_json_rows(parts) if o["fmt"] == "json" else b"".join(parts)
                    parts = None
                    with e.cv:
                        e.credit -= len(data)            # crédito em bytes brutos (o que a Central guarda)
                    e.raw += len(data)
                    if z is not None:
                        data = z.compress(data) + z.flush(zlib.Z_SYNC_FLUSH)
                    e.sent += len(data)
                    self.send(SQL_A_LINHAS, struct.pack("!B", len(eid)) + eid + struct.pack("!II", e.batches - 1, n)
                              + data, bulk=True)
                    e.rows += n
                if not suspended:
                    break
                if o["max"] and e.rows >= o["max"]:
                    truncated = True
                    break
            doc = {"exec_id": e.id, "tag": tag, "linhas": e.rows, "bytes_brutos": e.raw, "bytes_enviados": e.sent,
                   "ms": round((time.monotonic() - t0) * 1000, 1)}
            if truncated:
                doc["truncada"] = True
            st = e.final = "concluida"
            self.send(SQL_A_FIM, doc)
        except SqlExecError as x:
            st = e.final = "cancelada" if x.sqlstate == "57014" else "erro"
            sqlstate, msg = x.sqlstate, str(x)
            self.err(e.id, x.sqlstate, msg, cancelada=True if st == "cancelada" else None)
        except DbError as x:
            sqlstate = x.sqlstate or {"conexao": "08006", "tempo_esgotado": "57014", "autenticacao": "28000",
                                      "resposta_grande": "54000"}.get(x.code, "XX000")
            st = e.final = "cancelada" if e.cancelled else "erro"
            msg = x.pgmsg or str(x)
            self.err(e.id, sqlstate, msg, posicao=x.position, detalhe=x.detail, dica=x.hint,
                     cancelada=True if e.cancelled else None)
        except SqlClosed:
            st = "interrompida"
            if pg is not None:
                pg.cancel()                               # a Central sumiu: para no Postgres também
        except Exception as x:                            # defeito inesperado: a execução termina, a sessão segue
            st, sqlstate, msg = "erro", "XX000", "erro interno do agente: %s" % type(x).__name__
            e.final = st
            self.err(e.id, sqlstate, msg)
        finally:
            e.pg = None
            if pg is not None:
                try:
                    pg.simple("ROLLBACK")                 # leitura: nada fica aberto
                    pg.simple("DISCARD ALL")              # SET/prepare do operador não passam para a próxima
                    pg.sock.settimeout(pg.timeout)
                    self.pg_put(pg)
                except (DbError, OSError):
                    pg.close()
            with self.mx:
                self.execs.pop(e.id, None)
            self.last_act = time.monotonic()
            self.ed.remember(e.id, st)
            self.ed.audit_exec(self, e, st, started, round((time.monotonic() - t0) * 1000, 1), sqlstate, msg,
                               truncated)


class SqlEditor:
    """Editor SQL remoto (v2.12, só leitura). Thread 'sql' (controle): recebe os pedidos de sessão que a escuta do
    DbAgent entrega (db_requests/{sid}/sql), valida e recusa ou abre a sessão (thread própria), responde em
    sql_responses/{sid}/{sess}, mantém o certificado e info/{sid}/sql_cert_fp, vigia as sessões (canal mudo,
    ociosidade, duração), envia a auditoria (sql_audit, sem linhas de resultado) e poda uma vez por dia.
    Liga só com sync.sql_editor e sync.db_access e o acesso ao banco ativo; usa a mesma conexão do DbAgent."""

    def __init__(self, cloud, db, out=None):
        self.cloud, self.db, self.live, self.ident, self.out = cloud, db, cloud.live, cloud.ident, out
        self.sid = self.ident.install_id
        self.cert_path = os.path.join(cloud.base, SQL_CERT_FILE)
        self.key_path = os.path.join(cloud.base, SQL_KEY_FILE)
        self.audit_path = os.path.join(cloud.base, SQL_AUDIT_FILE)
        self.q = queue.Queue()
        self.stop_ev = threading.Event()
        self.thread = None
        self.mx = threading.Lock()
        self.sessions = set()
        self.seen = {}                       # sess -> instante em que foi tratado (nunca duas vezes)
        self.recent = collections.OrderedDict()    # exec_id -> estado (estado/exec_id repetido)
        self.fp = self.server_ctx = None
        self.cert_error, self.cert_next = "", 0.0
        self.enabled = False
        self.why = "aguardando a configuração do banco"
        self.info_sent, self.info_next = None, 0.0
        self.audits = collections.deque()
        self.audit_next = 0.0
        self.next_prune = time.time() + SQL_PRUNE_FIRST
        self.stats = {"sessoes": 0, "recusadas": 0, "execucoes": 0}
        db.sql = self

    def say(self, msg):
        if self.out:
            self.out(msg)

    # ---- ciclo de vida ----
    def start(self):
        self.thread = threading.Thread(target=self.loop, name="sql", daemon=True)
        self.thread.start()

    def stop(self):
        self.stop_ev.set()
        self.q.put(("wake", None))                        # acorda a thread de controle
        for s in self.session_list():
            s.end("parando", "o agente está parando (reinício ou atualização)")
        if self.thread is not None and self.thread is not threading.current_thread():
            self.thread.join(5)
        for s in self.session_list():
            if s.thread is not None:
                s.thread.join(3)
            s.kill("parando")
        self.drain_queue()
        with contextlib.suppress(Exception):
            self.flush_audit(force=True)

    def loop(self):
        while not self.stop_ev.is_set():
            try:
                self.step()
            except Exception as e:                        # nunca derruba a thread
                self.why = "erro interno: %s" % type(e).__name__
                self.stop_ev.wait(5)

    def step(self, wait=None):
        self.check()
        now = time.monotonic()
        for s in self.session_list():
            s.check(now)
        self.flush_audit()
        if self.enabled and time.time() >= self.next_prune:
            self.prune()
        try:
            item = self.q.get(timeout=wait if wait is not None else (1.0 if self.sessions else 5.0))
        except queue.Empty:
            return
        self.apply(item)
        self.drain_queue()

    def drain_queue(self):
        while True:
            try:
                self.apply(self.q.get_nowait())
            except queue.Empty:
                return

    def apply(self, item):
        kind, v = item
        if kind == "inbox":
            self.check()                                  # estado atual antes de decidir
            self.on_inbox(v)
        elif kind == "patch":
            self.send_patch(v)

    def session_list(self):
        with self.mx:
            return list(self.sessions)

    # ---- estado: ligado/desligado, certificado, info/{sid} ----
    def check(self):
        cfg = self.ident.sync_cfg()
        if self.db.enabled is None:                       # o DbAgent ainda não leu a configuração do banco
            return
        if ssl is None:
            want, why = False, "este Python não tem TLS (módulo ssl)"
        elif not cfg["sql_editor"]:
            want, why = False, "editor SQL desligado neste servidor (sync.sql_editor)"
        elif not cfg["db_access"] or not self.db.enabled:
            want, why = False, "acesso ao banco desligado neste servidor (sync.db_access)"
        elif not self.db.configured:
            want, why = False, "acesso ao banco ainda não configurado"
        else:
            want, why = True, ""
        if want and self.server_ctx is None and time.time() >= self.cert_next:
            try:
                self.fp, self.server_ctx = sql_cert(self.cert_path, self.key_path, self.sid)
                self.cert_error = ""
                self.say("Editor SQL: certificado do canal pronto (impressão digital %s...)." % self.fp[:16])
            except (OSError, ssl.SSLError, ValueError, subprocess.SubprocessError) as e:
                self.cert_next = time.time() + SQL_CERT_RETRY
                if str(e) != self.cert_error:
                    self.say("Editor SQL: sem certificado (%s)." % e)
                self.cert_error = str(e)
        if want and self.server_ctx is None:
            want, why = False, "sem certificado do canal (%s)" % self.cert_error
        if want != self.enabled:
            self.enabled = want
            if not want:
                for s in self.session_list():
                    s.end("desligado", why)
        self.why = why
        info = (self.fp, SQL_PROTO) if want else (None, None)
        self.cloud.sql_info = {"sql_cert_fp": self.fp, "sql_proto": SQL_PROTO} if want else {}
        if info != self.info_sent and time.time() >= self.info_next:
            try:
                self.live.patch("info/" + self.sid, {"sql_cert_fp": info[0], "sql_proto": info[1]}, timeout=15)
                self.info_sent = info
            except CloudError:
                self.info_next = time.time() + 60

    def allowed_relays(self):
        acfg = getattr(self.cloud, "acfg", None)
        v = acfg.get("sql", "relays") if acfg is not None else None
        return sql_relays_parse(v) or sql_relays_parse(SQL_RELAYS_DEFAULT)

    # ---- pedidos de sessão ----
    def inbox(self, d):
        """Chamado pela thread 'banco' com o espelho de db_requests/{sid}/sql (só enfileira)."""
        self.q.put(("inbox", d))

    def on_inbox(self, d):
        now = time.time()
        for sess in sorted(d):
            if sess in self.seen:
                continue
            self.seen[sess] = now
            if SQL_ID_RE.match(sess):
                self.consider(sess, d[sess])
        for sess in [k for k, t in self.seen.items() if k not in d and now - t > 600]:
            del self.seen[sess]

    def refuse(self, sess, code, msg):
        self.stats["recusadas"] += 1
        self.respond(sess, {"state": "recusado", "ok": False, "error_code": code, "error": clip(msg, 500),
                            "proto": SQL_PROTO}, drop=True)
        self.audit_line({"ev": "sessao_recusada", "sess": sess, "error_code": code, "error": clip(msg, 500)})

    def consider(self, sess, req):
        if not isinstance(req, dict):
            return self.refuse(sess, "pedido_invalido", "pedido malformado")
        relays = req.get("relays")
        if isinstance(relays, dict):
            relays = [relays[k] for k in sorted(relays, key=lambda x: int(x) if str(x).isdigit() else 99)]
        ok = (isinstance(req.get("by"), str) and is_num(req.get("at")) and is_int(req.get("proto"))
              and isinstance(req.get("relay_token"), str) and SQL_TOKEN_RE.match(req["relay_token"])
              and isinstance(req.get("sess_key_sha256"), str) and SQL_HEX64_RE.match(req["sess_key_sha256"])
              and req.get("formato") in ("pg", "json") and isinstance(relays, list) and 1 <= len(relays) <= 4
              and all(isinstance(r, str) and SQL_RELAY_RE.match(r) for r in relays))
        if not ok:
            return self.refuse(sess, "pedido_invalido", "pedido malformado (campos do contrato docs/EDITOR_SQL.md)")
        if self.stop_ev.is_set():
            return self.refuse(sess, "parando", "o agente está parando (reinício ou atualização)")
        if not self.enabled:
            code = "sem_certificado" if self.why.startswith("sem certificado") else "desligado"
            return self.refuse(sess, code, self.why or "editor SQL desligado")
        age = self.live.server_now() * 1000 - req["at"]
        if age > SQL_EXPIRE * 1000:
            return self.refuse(sess, "expirado", "pedido expirado (%d s na fila)" % (age // 1000))
        if req.get("nivel") != "leitura":
            return self.refuse(sess, "nivel_recusado", "este agente só abre sessões de leitura")
        if req["proto"] < 1:
            return self.refuse(sess, "pedido_invalido", "proto inválido")
        allowed = {sql_relay_norm(r) for r in self.allowed_relays()}
        use = [sql_relay_norm(r) for r in relays if sql_relay_norm(r) in allowed]
        if not use:
            return self.refuse(sess, "relay_nao_permitido", "nenhum relay do pedido está na lista permitida "
                                                            "(agent_config sql.relays)")
        with self.mx:
            if len(self.sessions) >= SQL_MAX_SESSIONS:
                full = True
            else:
                full = False
                s = SqlSession(self, sess, req, use)
                self.sessions.add(s)
        if full:
            return self.refuse(sess, "sessoes_demais", "sessões simultâneas demais (máximo %d)" % SQL_MAX_SESSIONS)
        self.stats["sessoes"] += 1
        s.thread = threading.Thread(target=s.run, name="sql-sessao", daemon=True)
        s.thread.start()

    def release(self, s, doc):
        with self.mx:
            self.sessions.discard(s)
        self.respond(s.sess, doc, drop=True)

    def respond(self, sess, doc, drop=False):
        """sql_responses/{sid}/{sess} (e a remoção do pedido) num PATCH só, pela thread de controle (em ordem)."""
        patch = {"sql_responses/%s/%s" % (self.sid, sess): dict(doc, at={".sv": "timestamp"}, agent_version=VERSION)}
        if drop:
            patch["db_requests/%s/%s/%s" % (self.sid, SQL_INBOX, sess)] = None
        self.q.put(("patch", patch))

    def send_patch(self, patch):
        for i in range(2):
            try:
                self.live.patch("", patch, timeout=15)
                return True
            except CloudError as e:
                if getattr(e, "code", 0) in (400, 401) or self.stop_ev.wait(1 + i):
                    break
        return False

    # ---- execuções: estado e exec_id repetido ----
    def exec_count(self):
        """Execuções em andamento no agente (chamar com self.mx)."""
        n = 0
        for s in self.sessions:
            n += len(s.execs)
        return n

    def exec_known(self, eid):
        with self.mx:
            return eid in self.recent

    def remember(self, eid, st):
        with self.mx:
            self.recent[eid] = st
            self.recent.move_to_end(eid)
            while len(self.recent) > SQL_RECENT:
                self.recent.popitem(last=False)

    def exec_state(self, eid):
        with self.mx:
            return self.recent.get(eid, "desconhecida")

    # ---- auditoria ----
    def audit_line(self, doc):
        line = json.dumps(dict({"at": iso_now()}, **doc), ensure_ascii=False)
        try:
            fd = os.open(self.audit_path, os.O_WRONLY | os.O_APPEND | os.O_CREAT | getattr(os, "O_BINARY", 0), 0o600)
            try:
                if hasattr(os, "fchmod"):
                    os.fchmod(fd, 0o600)
                os.write(fd, (line + "\n").encode("utf-8"))
            finally:
                os.close(fd)
        except OSError:
            pass

    def audit_exec(self, s, e, st, started, ms, sqlstate, msg, truncated):
        sql = e.d["sql"]
        self.stats["execucoes"] += 1
        doc = {"sess": s.sess, "by": clip(s.by, 128), "nivel": "leitura", "sql": clip(sql, SQL_AUDIT_SQL),
               "sql_sha256": hashlib.sha256(sql.encode("utf-8")).hexdigest(), "sql_len": len(sql),
               "started_at": started, "state": st, "rows": e.rows, "bytes": e.raw, "ms": ms}
        if sqlstate and re.match(r"^[0-9A-Z]{5}$", sqlstate):
            doc["sqlstate"] = sqlstate
        if msg:
            doc["error"] = clip(msg, 500)
        if truncated:
            doc["truncada"] = True
        self.audit_line(dict(doc, ev="execucao", exec_id=e.id, sql=sql, params_n=len(e.d["params"])))
        with self.mx:
            self.audits.append((e.id, doc))
            while len(self.audits) > SQL_AUDIT_QUEUE:
                self.audits.popleft()

    def flush_audit(self, force=False):
        if not self.audits or (not force and time.time() < self.audit_next):
            return
        while self.audits:
            with self.mx:
                batch = list(self.audits)[:SQL_AUDIT_BATCH]
            patch = {"sql_audit/%s/%s" % (self.sid, eid): dict(doc, done_at={".sv": "timestamp"})
                     for eid, doc in batch}
            try:
                self.live.patch("", patch, timeout=15)
            except CloudError as e:
                if getattr(e, "code", 0) not in (400, 401):
                    self.audit_next = time.time() + 30    # sem Firebase: tenta depois (a fila fica guardada)
                    return
                for k, v in patch.items():                # recusado pelas regras: uma a uma, descarta a recusada
                    with contextlib.suppress(CloudError):
                        self.live.patch("", {k: v}, timeout=15)
            with self.mx:
                for _ in batch:
                    if self.audits:
                        self.audits.popleft()

    # ---- poda (1x por dia) ----
    def prune(self):
        self.next_prune = time.time() + 86400
        now_ms = int(self.live.server_now() * 1000)
        try:
            for node, keep in (("sql_responses", SQL_RESP_KEEP), ("sql_audit", SQL_AUDIT_KEEP)):
                cut = '"%013d"' % (now_ms - keep * 1000)
                for _ in range(20):
                    old = self.live.get("%s/%s" % (node, self.sid), {"orderBy": '"$key"', "endAt": cut,
                                                                     "limitToFirst": "100"}) or {}
                    if not old:
                        break
                    self.live.patch("", {"%s/%s/%s" % (node, self.sid, k): None for k in old}, timeout=15)
        except CloudError:
            self.next_prune = time.time() + 3600

    def panel(self):
        """Texto curto do estado (diagnóstico e painel)."""
        if self.enabled:
            n = len(self.sessions)
            return "Editor SQL: pronto" + (" · %d sessão(ões) aberta(s)" % n if n else "")
        return "Editor SQL: " + (self.why or "desligado")


# --------------------------------------------------------------------------
# Eventos do sistema: admin.system_email -> sys_events (v2.10, contrato em docs/EVENTOS_SISTEMA.md)
# --------------------------------------------------------------------------
SYS_EV_FILE = "sys_events.json"      # SYNC_DIR/sys_events.json: checkpoint, vistos, eventos abertos e fila pendente
SYS_EV_LIMIT = 500                  # cods por consulta
SYS_EV_BACK = 200                   # reconsulta desde checkpoint - 200: cod visível fora de ordem (commit tardio)
SYS_EV_SEEN = 1800                  # s mínimos de um cod entre os vistos (e só sai abaixo da faixa reconsultada)
SYS_EV_WINDOW = 900                 # s: mesma fingerprint até 15 min do evento aberto = mesmo evento (count+1)
SYS_EV_OPEN_KEEP = 7200             # s (pelo message_date mais novo) que um evento fica aberto no estado
SYS_EV_OPEN_MAX = 1000
SYS_EV_BODY_MAX = 65536             # caracteres do corpo lidos do banco (o md5 das cópias é do corpo inteiro)
SYS_EV_FETCH = 50                   # linhas completas por consulta (corpo grande: memória limitada)
SYS_EV_ROUNDS = 5                   # consultas seguidas num ciclo enquanto vier lote cheio
SYS_EV_CHUNK = 50                   # eventos por PATCH no Firebase
SYS_EV_BACKOFF = (30, 900)          # s de espera depois de uma falha: 30, 60, 120... até 900
SYS_EV_WAIT = 5                     # s até olhar de novo quando a configuração do banco ainda não chegou
SYS_EV_PRUNE_FIRST = 600            # s depois da partida até a 1ª poda (depois, 1x por dia)
SYS_EV_LIMITS = {"subject": 200, "summary": 300, "origin": 120, "cods": 2000, "detail": 8192}
SYS_EV_KINDS = (("remessa rejeitada", "remessa_rejeitada", "erro"),
                ("erro importacao pedidos", "importacao_pedidos", "erro"),
                ("log erros fila proc", "fila_proc", "erro"),
                ("espaco em disco", "espaco_disco", "alerta"),
                ("erro - sp_manutencao_base_dados", "manutencao_base", "erro"))
SYS_EV_SQL_MAX = "SELECT max(cod) FROM admin.system_email"
SYS_EV_SQL_CODS = "SELECT cod FROM admin.system_email WHERE cod > $1 ORDER BY cod LIMIT %d" % SYS_EV_LIMIT
SYS_EV_SQL_ROWS = ("SELECT cod, subject, left(body_html, %d), message_date::text, "
                   "(extract(epoch FROM message_date::timestamptz) * 1000)::bigint, processed::text, md5(body_html) "
                   "FROM admin.system_email WHERE cod = ANY (string_to_array($1, ',')::bigint[]) ORDER BY cod"
                   % SYS_EV_BODY_MAX)
SUBJ_PREFIX = (re.compile(r"^\s*\[[^\]]*\]\s*"),                                  # [EMPRESA] x / [EMPRESA - data] x
               re.compile(r"^.*? - \d\d/\d\d/\d\d(?:\d\d)? \d\d:\d\d:\d\d - "))    # EMPRESA - dd/mm/yy hh:mm:ss - x
BODY_PREFIX = re.compile(r"^\s*[\[(][^\])\n\\]{1,120}[\])][ \t]*(?:\\n|\r\n|\r|\n)")   # (EMPRESA) \n
UNC_RE = re.compile(r"\\\\([^\\\s]+)((?:\\[^\\\s]*)*)")
HTML_HINT = re.compile(r"(?i)</?(?:li|ul|ol|h[1-6]|br|p|div|table|tr|td)\b[^>]*>")
HTML_BREAK = re.compile(r"(?i)<\s*(?:br|/?li|/?ul|/?ol|/?p|/?div|/?tr|/?h[1-6]|/?table)\b[^>]*>")
HTML_TAG = re.compile(r"<[^>]*>")
CTX_START = re.compile(r"(?i)^\s*context[o]?\s*:")
ITEM_START = re.compile(r"^\s*(?:-\s|[A-Z][A-Z0-9_.]*\s*:)")
EMAIL_RE = re.compile(r"[A-Za-z0-9._%+-]+@[A-Za-z0-9-]+(?:\.[A-Za-z0-9-]+)+")
IPV4_RE = re.compile(r"(?<![\d.])(?:\d{1,3}\.){3}\d{1,3}(?!\.?\d)")
VOLATILE_LINE = re.compile(r"(?i)^\s*-?\s*(?:data|data/hora|cod\.conx)\b[\s.]*:")
SYS_TIME_RE = re.compile(r"\d{4}-\d\d-\d\d(?:[ T]\d\d:\d\d(?::\d\d(?:[.,]\d+)?)?)?"
                         r"|\d\d/\d\d/\d{2,4}(?:\s+\d\d:\d\d(?::\d\d(?:[.,]\d+)?)?)?|\d\d:\d\d:\d\d(?:[.,]\d+)?")
EID_RE = re.compile(r"^[0-9]{12}$")
SYS_EV_GEN = 10 ** 10               # eid = geração × 10^10 + cod (geração 0 = cod puro; sobe se a tabela for recriada)


def ev_cut(s, n):
    """Texto em até n unidades UTF-16 (como as regras); cortado termina em "…"."""
    return s if utf16_len(s) <= n else clip(s, n - 1) + "…"


def ev_subject(s):
    """Assunto-base: sem os prefixos de empresa/data das versões do pacote Winthor."""
    s = (s or "").strip()
    for rx in SUBJ_PREFIX:
        s = rx.sub("", s, count=1)
    return " ".join(s.split())


def ev_kind(base):
    k = unicodedata.normalize("NFKD", base).encode("ascii", "ignore").decode().lower()
    for name, kind, level in SYS_EV_KINDS:
        if k.startswith(name):
            return kind, level
    return "outro", "erro"


def ev_text(body, kind):
    """Corpo higienizado (o que vai para o Firebase): sem prefixo de empresa, "\\n" literal dos gatilhos vira
    quebra real, HTML vira texto, sem o bloco CONTEXT (SQL) e com IP, host de caminho UNC e e-mail mascarados."""
    s = BODY_PREFIX.sub("", body or "", count=1)
    trig = "\\n - " in s            # corpo dos gatilhos (cabeçalho " - Campo..: valor" separado por \n literal)
    parts, pos = [], 0
    for m in UNC_RE.finditer(s):    # \n dentro de um caminho UNC (\\host\notas) não é quebra de linha
        seg = s[pos:m.start()]
        parts += [seg.replace("\\n", "\n") if trig else seg, "\\\\<host>" + m.group(2)]
        pos = m.end()
    seg = s[pos:]
    parts.append(seg.replace("\\n", "\n") if trig else seg)
    s = "".join(parts).replace("\r\n", "\n").replace("\r", "\n")
    if kind == "fila_proc" or HTML_HINT.search(s):
        s = "\n".join(x.strip() for x in html.unescape(HTML_TAG.sub("", HTML_BREAK.sub("\n", s))).split("\n")
                      if x.strip())
    s = IPV4_RE.sub("<ip>", EMAIL_RE.sub("<email>", s))
    out, skip = [], False
    for ln in s.split("\n"):
        ln = ln.rstrip()
        if CTX_START.match(ln):
            skip = True                 # CONTEXT: até o fim do parágrafo (ou o próximo item/erro)
            continue
        if skip and ln and not ITEM_START.match(ln):
            continue
        skip = False
        if ln or (out and out[-1]):
            out.append(ln)
    return "\n".join(out).strip("\n")


def ev_fingerprint(kind, base, text):
    """16 hex do SHA-256 de kind + assunto-base + corpo sem as linhas/trechos voláteis (datas, Cod.Conx)."""
    lines = []
    for ln in text.split("\n"):
        if VOLATILE_LINE.match(ln):
            continue
        ln = " ".join(SYS_TIME_RE.sub("", ln).split())
        if ln:
            lines.append(ln)
    if kind == "remessa_rejeitada":
        lines.sort()                    # a lista de erros vem de um ARRAY_AGG sem ORDER BY
    key = "\n".join([kind, base.lower()] + lines)
    return hashlib.sha256(key.encode("utf-8")).hexdigest()[:16]


def ev_summary(kind, base, text):
    """(summary, origin): a 1ª linha útil (por tipo) e de onde veio (remessa, usuário, disco, origem da fila)."""
    lines = [" ".join(ln.split()) for ln in text.split("\n")]
    useful = [ln for ln in lines if ln and not VOLATILE_LINE.match(ln)]
    summary, origin = "", ""
    if kind == "remessa_rejeitada":
        m = re.search(r"Cod\.Rems\.*:\s*(\S+)", text)
        origin = "Remessa " + m.group(1) if m else ""
        errs = [i for i, ln in enumerate(lines) if re.match(r"(?i)^-?\s*erros\b", ln)]
        rest = [ln for ln in lines[errs[0] + 1:] if ln] if errs else []
        if rest:
            i = 0                                         # "XMLNF:" / "ERRO:" sem texto: junta com a linha seguinte
            while rest[i].endswith(":") and i + 1 < len(rest):
                i += 1
            summary = " ".join(rest[:i + 1])
            n = sum(1 for ln in rest if re.match(r"^[A-Z][A-Z0-9_]+\s*:", ln)
                    and not re.match(r"^(?:ERRO|ERROR|DETAIL|DETALHE|HINT|DICA)\s*:", ln))
            summary += " (+%d)" % (n - 1) if n > 1 else ""
    elif kind == "importacao_pedidos":
        m = re.search(r"Cod\.Usr\.*:\s*(\S+)", text)
        origin = "Usuário " + m.group(1) if m else ""
        summary = next((ln for ln in lines if re.match(r"(?i)^erro?r?\s*:", ln)), "")
    elif kind == "espaco_disco":
        drives = []
        for ln in lines:
            m = re.match(r"(?i)^drive\s*:\s*(.+)$", ln)
            if m:
                drives.append({"d": m.group(1), "free": "", "low": False})
            elif drives and re.match(r"(?i)^livre\s*:", ln):
                drives[-1]["free"] = ln.split(":", 1)[1].strip()
            elif drives and "atencao" in ln.lower():
                drives[-1]["low"] = True
        low = [d for d in drives if d["low"]] or drives
        origin = ", ".join(d["d"] for d in low)
        if low:
            summary = "Pouco espaço livre: " + "; ".join(d["d"] + (": livre %s" % d["free"] if d["free"] else "")
                                                         for d in low)
    elif kind == "fila_proc":
        items = useful[1:] if len(useful) > 1 else useful
        summary = items[0] if items else ""
        m = re.match(r"^(.+?)\s*=", summary)
        origin = m.group(1) if m else ""
    elif kind == "manutencao_base":
        m = re.search(r"(?im)^\s*mensagem\s*:\s*(.+)$", text)
        summary = m.group(1).strip() if m else ""
    if not summary:
        summary = next((ln for ln in useful if not ln.endswith(":") and ln.lower() != base.lower()), "")
    return (ev_cut(summary or base or "(sem texto)", SYS_EV_LIMITS["summary"]),
            ev_cut(origin, SYS_EV_LIMITS["origin"]))


def ev_parse(subject, body):
    """Uma ocorrência (assunto e corpo crus) -> campos do evento + detail."""
    base = ev_subject(subject)
    kind, level = ev_kind(base)
    text = ev_text(body, kind)
    summary, origin = ev_summary(kind, base, text)
    return {"kind": kind, "level": level, "subject": ev_cut(base or "(sem assunto)", SYS_EV_LIMITS["subject"]),
            "summary": summary, "origin": origin, "fingerprint": ev_fingerprint(kind, base, text),
            "detail": ev_cut(text, SYS_EV_LIMITS["detail"])}


def ev_cods(s, cods):
    """cods em texto "12345,12346" até SYS_EV_LIMITS["cods"], mantendo os primeiros (só números inteiros). Só
    acrescenta enquanto qualquer cod (até 12 dígitos) ainda cabe: cheio uma vez, fica cheio."""
    for c in cods:
        if len(s) > SYS_EV_LIMITS["cods"] - 13:
            break
        s = (s + "," if s else "") + str(c)
    return s


class SysEvents:
    """Thread 'eventos': lê admin.system_email (só SELECT, transação READ ONLY com statement_timeout) a cada
    sync.sys_events_interval e publica eventos lógicos em sys_events/{sid} (+ sys_events_detail e
    sys_events_state). Usa a conexão do DbAgent (db_config/{sid} ou DB_DEFAULTS), mas com o próprio PgConn,
    aberto e fechado a cada ciclo. Nunca toca na coleta nem no heartbeat; falha de banco/rede = backoff próprio.

    Estado em SYNC_DIR/sys_events.json (gravação atômica): checkpoint (maior cod publicado), vistos (cod -> hora),
    eventos abertos (fingerprint -> evento) e a fila pendente (eid -> documento). Com fila pendente o banco não é
    lido: primeiro publica (idempotente, mesmo eid), depois o checkpoint avança."""

    def __init__(self, cloud, db, out=None):
        self.cloud, self.live, self.ident, self.db, self.out = cloud, cloud.live, cloud.ident, db, out
        self.sid = self.ident.install_id
        self.path = os.path.join(cloud.dir, SYS_EV_FILE)
        self.stop_ev = threading.Event()
        self.thread, self.pg = None, None
        self.st = self.load()
        self.fails, self.next_run = 0, 0.0
        self.error = ("", "")             # (error_code, mensagem) do último ciclo
        self.state_sent = None
        self.next_prune = max(self.st["pruned_at"] + 86400, time.time() + SYS_EV_PRUNE_FIRST)

    # ---- estado ----
    def load(self):
        d = read_json(self.path)
        d = d if isinstance(d, dict) else {}
        ck = d.get("checkpoint")
        st = {"db": d.get("db") if isinstance(d.get("db"), str) else "", "gen": d["gen"] if is_int(d.get("gen")) else 0,
              "checkpoint": ck if is_int(ck) else None, "pruned_at": d.get("pruned_at") if is_num(d.get("pruned_at")) else 0}
        for k in ("seen", "open", "queue"):
            st[k] = d[k] if isinstance(d.get(k), dict) else {}
        return st

    def save(self):
        now = time.time()
        low = (self.st["checkpoint"] or 0) - SYS_EV_BACK
        self.st["seen"] = {c: t for c, t in self.st["seen"].items() if int(c) > low or now - t < SYS_EV_SEEN}
        os.makedirs(os.path.dirname(self.path), mode=0o700, exist_ok=True)
        write_private(self.path, json.dumps(self.st, separators=(",", ":"), ensure_ascii=False))

    def say(self, s):
        if self.out:
            self.out(s)

    # ---- ciclo de vida ----
    def start(self):
        self.thread = threading.Thread(target=self.loop, name="eventos", daemon=True)
        self.thread.start()

    def stop(self):
        self.stop_ev.set()
        if self.thread is not None and self.thread is not threading.current_thread():
            self.thread.join(5)
        self.close_pg()

    def loop(self):
        while not self.stop_ev.is_set():
            wait = self.next_run - time.time()
            if wait > 0:
                self.stop_ev.wait(wait)
                continue
            try:
                self.step()
            except Exception as e:                        # nunca derruba a thread
                self.error = ("interno", "erro interno: %s" % type(e).__name__)
                self.fail()

    def fail(self):
        self.fails += 1
        self.next_run = time.time() + min(SYS_EV_BACKOFF[1], SYS_EV_BACKOFF[0] * 2 ** (self.fails - 1))

    def step(self):
        """Um ciclo. Devolve desligado | aguardando | ok | erro."""
        cfg = self.ident.sync_cfg()
        if not (cfg["sys_events"] and cfg["db_access"]):
            self.close_pg()
            self.error = ("desligado", "eventos do sistema desligados neste servidor (sync.%s)"
                          % ("sys_events" if not cfg["sys_events"] else "db_access"))
            self.publish_state(quiet=True)
            self.next_run = time.time() + cfg["sys_events_interval"]
            return "desligado"
        dbcfg = self.db.cfg
        if dbcfg is None:                                 # o DbAgent ainda não leu db_config/{sid}
            self.next_run = time.time() + SYS_EV_WAIT
            return "aguardando"
        self.maybe_prune(cfg)
        try:
            self.flush()                                  # fila pendente primeiro: sem isso, o banco não é lido
            self.collect(dbcfg)
            self.error = ("", "")
            self.flush()
            self.publish_state()
        except DbError as e:
            self.error = (self.db_code(e), str(e))
            self.publish_state(quiet=True)
            self.fail()
            return "erro"
        except CloudError:
            self.fail()
            return "erro"
        finally:
            self.close_pg()
        self.fails = 0
        self.next_run = time.time() + cfg["sys_events_interval"]
        return "ok"

    @staticmethod
    def db_code(e):
        msg = str(e)
        if e.code == "sql" and "(42P01)" in msg:
            return "sem_tabela"
        if e.code == "sql" and "(42501)" in msg:
            return "sem_permissao"
        return e.code

    # ---- Postgres (só SELECT) ----
    def close_pg(self):
        if self.pg is not None:
            self.pg.close()
            self.pg = None

    def collect(self, c):
        key = "%s:%s/%s" % (c.get("host") or "", c.get("port") or "", c.get("dbname") or "")
        pg = self.pg = PgConn(c.get("host"), c.get("port"), c.get("dbname") or "", c.get("user") or "",
                              c.get("password") or "", c.get("sslmode"))
        pg.sock.settimeout(DB_TIMEOUT_MS / 1000.0 + 5)
        pg.simple("BEGIN TRANSACTION READ ONLY; SET LOCAL statement_timeout = %d" % DB_TIMEOUT_MS)
        top = pg.query(SYS_EV_SQL_MAX, [])[2][0][0]
        top = int(top) if top is not None else 0
        st = self.st
        if st["checkpoint"] is None or st["db"] != key or top < st["checkpoint"]:
            if st["checkpoint"] is None or st["db"] != key:
                self.say("Eventos do sistema: ativados a partir do cod %d (sem histórico)." % top)
            else:
                self.say("Eventos do sistema: tabela recriada (maior cod %d < checkpoint %d): recomeçando do %d, "
                         "sem histórico." % (top, st["checkpoint"], top))
            now = time.time()
            # geração nova: eids da tabela nova (cods recomeçando) não sobrescrevem os eventos da antiga
            st.update(db=key, checkpoint=top, open={}, gen=st["gen"] + (st["checkpoint"] is not None),
                      seen={str(x): now for x in self.cods(pg, top - SYS_EV_BACK)})
        else:
            low = st["checkpoint"] - SYS_EV_BACK
            for _ in range(SYS_EV_ROUNDS):
                cods = self.cods(pg, low)
                new = [x for x in cods if str(x) not in st["seen"]]
                for i in range(0, len(new), SYS_EV_FETCH):
                    part = ",".join(str(x) for x in new[i:i + SYS_EV_FETCH])
                    self.ingest(pg.query(SYS_EV_SQL_ROWS, [part], 0, 8 << 20)[2])
                if len(cods) < SYS_EV_LIMIT:
                    break
                low = cods[-1]
        pg.simple("ROLLBACK")
        self.save()

    @staticmethod
    def cods(pg, low):
        return [int(r[0]) for r in pg.query(SYS_EV_SQL_CODS, [str(low)])[2]]

    # ---- deduplicação ----
    def ingest(self, rows):
        """Linhas -> ocorrências (cópias por destinatário: mesmo message_date, assunto e md5 do corpo) -> eventos."""
        now = time.time()
        groups = {}
        for cod, subject, body, mdate, ms, processed, md5 in rows:
            cod = int(cod)
            self.st["seen"][str(cod)] = now
            g = groups.get((mdate, subject, md5))
            if g is None:
                groups[(mdate, subject, md5)] = {"cods": [cod], "t": int(ms) if ms is not None else int(now * 1000),
                                                 "subject": subject, "body": body, "sent": processed == "1"}
            else:
                g["cods"].append(cod)
                g["sent"] = g["sent"] or processed == "1"
        for g in sorted(groups.values(), key=lambda g: (g["t"], g["cods"][0])):
            self.occurrence(g)
        opened = self.st["open"]
        if opened:
            newest = max(e["last_at"] for e in opened.values())
            keep = sorted((e for e in opened.items() if e[1]["last_at"] >= newest - SYS_EV_OPEN_KEEP * 1000),
                          key=lambda e: -e[1]["last_at"])[:SYS_EV_OPEN_MAX]
            self.st["open"] = dict(keep)

    def occurrence(self, g):
        st, t, cods = self.st, g["t"], g["cods"]
        p = ev_parse(g["subject"], g["body"])
        fp = p["fingerprint"]
        ev = st["open"].get(fp)
        if ev is not None and ev["first_at"] - SYS_EV_WINDOW * 1000 <= t <= ev["last_at"] + SYS_EV_WINDOW * 1000:
            ev.update(count=ev["count"] + 1, copies=ev["copies"] + len(cods), cods=ev_cods(ev["cods"], cods),
                      first_at=min(ev["first_at"], t), last_at=max(ev["last_at"], t), sent=ev["sent"] or g["sent"],
                      top=max(ev["top"], max(cods)))
            old = st["queue"].get(ev["eid"])
            detail = old["detail"] if old else None       # já publicado: o detalhe não muda
        else:
            ev = {"eid": "%012d" % (st["gen"] * SYS_EV_GEN + min(cods)), "kind": p["kind"], "level": p["level"], "subject": p["subject"],
                  "summary": p["summary"], "origin": p["origin"], "first_at": t, "last_at": t, "count": 1,
                  "copies": len(cods), "cods": ev_cods("", cods), "fingerprint": fp, "sent": g["sent"],
                  "top": max(cods)}
            st["open"][fp] = ev
            detail = p["detail"] or None                  # corpo vazio: sem sys_events_detail
        st["queue"][ev["eid"]] = {"doc": self.event_doc(ev), "detail": detail, "top": ev["top"]}

    @staticmethod
    def event_doc(ev):
        doc = {k: ev[k] for k in ("kind", "level", "subject", "summary", "first_at", "last_at", "count", "copies",
                                  "cods", "fingerprint", "sent")}
        if ev["origin"]:
            doc["origin"] = ev["origin"]
        return doc

    # ---- Firebase ----
    def state_doc(self, checkpoint=None, pending=None):
        code, msg = self.error
        doc = {"ok": not code, "checkpoint": max(0, self.st["checkpoint"] or 0) if checkpoint is None else checkpoint,
               "pending": len(self.st["queue"]) if pending is None else pending, "agent_version": VERSION}
        if code:
            doc.update(error_code=code, error=clip(msg, 500))
        return doc

    def flush(self):
        """Publica a fila em lotes (evento + detalhe + estado num PATCH só, atômico); cada lote aceito avança o
        checkpoint e grava o estado. Falha (CloudError) = o resto fica na fila para o próximo ciclo."""
        q = self.st["queue"]
        while q:
            eids = sorted(q)[:SYS_EV_CHUNK]
            ck = max([self.st["checkpoint"] or 0] + [q[e]["top"] for e in eids])
            sdoc = self.state_doc(ck, len(q) - len(eids))
            patch = {"sys_events_state/" + self.sid: dict(sdoc, checked_at={".sv": "timestamp"})}
            for e in eids:
                patch["sys_events/%s/%s" % (self.sid, e)] = dict(q[e]["doc"], updated_at={".sv": "timestamp"})
                if q[e]["detail"] is not None:
                    patch["sys_events_detail/%s/%s" % (self.sid, e)] = {"detail": q[e]["detail"]}
            self.live.patch("", patch, timeout=30)
            for e in eids:
                del q[e]
            self.st["checkpoint"] = ck
            self.state_sent = sdoc
            self.save()

    def publish_state(self, quiet=False):
        doc = self.state_doc()
        if doc == self.state_sent:
            return
        try:
            self.live.patch("", {"sys_events_state/" + self.sid: dict(doc, checked_at={".sv": "timestamp"})}, timeout=30)
            self.state_sent = doc
        except CloudError:
            if not quiet:
                raise

    def maybe_prune(self, cfg):
        """Retenção (1x por dia): apaga sys_events e sys_events_detail com last_at há mais de
        sys_events_retention_days (consulta por last_at, com .indexOn nas regras)."""
        if time.time() < self.next_prune:
            return
        cut = int(self.live.server_now() * 1000) - cfg["sys_events_retention_days"] * 86400000
        try:
            for _ in range(20):
                old = self.live.get("sys_events/" + self.sid, {"orderBy": '"last_at"', "endAt": str(cut),
                                                               "limitToFirst": "100"}) or {}
                eids = [k for k in old if EID_RE.match(k)]
                if eids:
                    patch = {}
                    for e in eids:
                        patch["sys_events/%s/%s" % (self.sid, e)] = None
                        patch["sys_events_detail/%s/%s" % (self.sid, e)] = None
                    self.live.patch("", patch, timeout=30)
                if len(old) < 100:
                    break
        except CloudError:
            self.next_prune = time.time() + 3600
            return
        self.st["pruned_at"] = time.time()
        self.next_prune = self.st["pruned_at"] + 86400
        self.save()


def ask_catkey(ident, live=None, force=False):
    """Pergunta a chave do catálogo (com *, como os outros segredos) e grava em server_monitor.catkey (600).
    Sem force: só quando o acesso está permitido, o Firebase está configurado e ainda não há chave (a conexão
    usa db_config/{sid} ou, sem ele, DB_DEFAULTS). Devolve True se gravou."""
    path = os.path.join(ident.base, CATKEY_FILE)
    if not force:
        if read_catkey(path) is not None or not ident.sync_cfg()["db_access"] or live is None:
            return False
        print("\nACESSO AO BANCO: falta a chave do catálogo de operações deste servidor")
        print("(está com o administrador da C2; também dá para informar depois no painel, tecla k).")
    print("Chave do catálogo: 64 caracteres hexadecimais. Enter sem nada pula.")
    while True:
        try:
            s = ask_secret("Chave do catálogo (aparece como *): ")
        except EOFError:
            return False
        if not s:
            print("Sem chave: os pedidos ao banco serão recusados (depois: %s --catalogo-chave)." % sys.argv[0])
            return False
        k = parse_catkey(s)
        if k is None:
            print("Chave inválida: são 64 caracteres de 0-9 e a-f. Tente de novo.")
            continue
        write_private(path, k.hex() + "\n")
        print("OK: chave salva em %s (permissão 600)." % path)
        return True


# --------------------------------------------------------------------------
# Autoatualização: procura versão nova do programa, troca o arquivo e reinicia
# --------------------------------------------------------------------------
# Mesma origem do instalar.sh (USAGE_MONITOR_URL sobrescreve, como lá; file:// serve para testes)
UPDATE_URL = os.environ.get("USAGE_MONITOR_URL",
                            "https://api.github.com/repos/cbalmeida/server_monitor_releases/contents/usage_monitor.py")
UPDATE_FIRST = (60, 120)         # s até a 1ª verificação (sorteado: muitos servidores não batem juntos no GitHub)
UPDATE_JITTER = 60               # s sorteados somados a cada update_interval
UPDATE_MAX_BYTES = 4 << 20       # o programa tem ~250 KB; acima disso a resposta não é ele
UPDATE_TIMEOUT = 20              # s de rede por tentativa (só a thread da atualização espera)


def version_tuple(v):
    """'2.4.1' -> (2, 4, 1), sem zeros à direita ('2.5.0' == '2.5'); texto sem números -> ()."""
    t = [int(x) for x in re.findall(r"\d+", v or "")]
    while t and t[-1] == 0:
        t.pop()
    return tuple(t)


def source_version(src):
    """Versão declarada num código-fonte do programa (linha VERSION = "...") ou ''."""
    m = re.search(r'^VERSION = "([0-9][0-9.]*)"\s*$', src, re.M)
    return m.group(1) if m else ""


def source_ok(src):
    """O arquivo baixado é o programa inteiro e válido para o Python 3.8? (protege contra download parcial)."""
    if not source_version(src) or "\ndef main(" not in src or "__main__" not in src:
        return False
    try:
        ast.parse(src, feature_version=(3, 8))
    except Exception:                                 # SyntaxError, ValueError, MemoryError...
        return False
    return True


class Updater:
    """Thread 'atualização' do coletor: a cada update_interval baixa o programa publicado e, se a
    versão for MAIOR que a em execução e o arquivo for válido, troca o script (atômico: .novo + rename)
    e pede o reinício (restart + on_restart). Nunca rebaixa, nunca reinicia na mesma versão.
    Falha de rede só fica registrada (note) e tenta de novo na próxima vez. wake() (aviso da central em
    signals/<sid>/release, v2.6.1) antecipa a verificação; as exigências continuam as mesmas. v2.11: a central
    define o intervalo (agent_config update.interval_s) e a janela de horário (update.window) em que a troca pode
    ser feita: fora dela a versão nova fica esperando (verifica de novo quando a janela abre). request_restart():
    reinício controlado sem versão nova (coleta alterada pela central), pelo mesmo caminho."""

    def __init__(self, script, cfg, out=None, on_restart=None, url=None):
        self.script = os.path.realpath(script)
        self.enabled = bool(cfg["auto_update"])
        self.interval = cfg["update_interval"]
        self.out = out                                # saída na tela (None = silencioso)
        self.on_restart = on_restart
        self.url = url or UPDATE_URL
        self.stop_ev, self.restart = threading.Event(), threading.Event()
        self.wake_ev = threading.Event()              # aviso da central: verificar agora
        self.version = ""                             # versão nova já gravada (aguardando reinício)
        self.note = ""                                # resultado da última verificação
        self.alert = ""                               # problema que o painel mostra (gravação/arquivo inválido)
        self.checked_at = 0.0
        self.thread = None
        self.acfg = None                              # AgentConfig (frequências da central), ligado pelo main
        self.reason = ""                              # motivo do reinício sem versão nova (request_restart)
        self.waiting = 0                              # s até a janela de atualização abrir (versão nova esperando)

    def cur_interval(self):
        return self.acfg.get("update", "interval_s", self.interval) if self.acfg is not None else self.interval

    def request_restart(self, reason):
        """Reinício controlado na mesma versão (ex.: coleta alterada pela central): mesmo caminho da atualização."""
        if self.restart.is_set():
            return False
        self.version, self.reason, self.note = self.version or VERSION, reason, reason + "; reiniciando"
        self.say("%s: reiniciando a coleta." % reason)
        self.restart.set()
        if self.on_restart:
            self.on_restart()
        return True

    def say(self, s):
        if self.out:
            self.out(s)

    def start(self):
        """Inicia a thread; devolve False se desativada ou sem permissão para trocar o script."""
        if not self.enabled:
            return False
        d = os.path.dirname(self.script)
        if not (os.access(d, os.W_OK) and os.access(self.script, os.W_OK)):
            self.enabled = False
            print("AVISO: atualização automática desativada: sem permissão de escrita em %s" % self.script)
            return False
        self.thread = threading.Thread(target=self.loop, name="atualização", daemon=True)
        self.thread.start()
        return True

    def stop(self):
        self.stop_ev.set()
        self.wake_ev.set()

    def wake(self, version=""):
        """Aviso da central: versão publicada (maior que a em execução). Verifica já, sem esperar o intervalo."""
        if self.enabled and not self.restart.is_set():
            self.note = "aviso: versão %s publicada; verificando" % version
            self.wake_ev.set()

    def first_wait(self):
        delay = os.environ.get("USAGE_MONITOR_UPDATE_DELAY", "")   # só para testes: 1ª verificação em N s
        return float(delay) if delay.replace(".", "", 1).isdigit() else random.uniform(*UPDATE_FIRST)

    def loop(self):
        wait = self.first_wait()
        while True:
            self.wake_ev.wait(wait)
            self.wake_ev.clear()
            if self.stop_ev.is_set():
                return
            try:
                if self.check():
                    return
            except Exception as e:                    # nunca derruba a thread
                self.note = "erro: %s" % e
            wait = self.cur_interval() + random.uniform(0, UPDATE_JITTER)
            if self.waiting:                          # versão nova esperando a janela: confere quando ela abrir
                wait = min(wait, self.waiting + random.uniform(0, UPDATE_JITTER))

    def fetch(self):
        req = urllib.request.Request(self.url, headers={"Accept": "application/vnd.github.raw",
                                                        "User-Agent": "usage_monitor/" + VERSION})
        with urllib.request.urlopen(req, timeout=UPDATE_TIMEOUT) as r:
            data = r.read(UPDATE_MAX_BYTES + 1)
        if len(data) > UPDATE_MAX_BYTES:
            raise ValueError("resposta grande demais")
        return data.decode("utf-8")

    def check(self):
        """Uma verificação. True = versão nova gravada e reinício pedido."""
        self.checked_at = time.time()
        try:
            src = self.fetch()
        except Exception as e:                        # rede, HTTP, tempo esgotado, texto inválido: tenta depois
            self.note = "sem acesso à versão publicada (%s)" % (str(e)[:120] or type(e).__name__)
            return False
        new = source_version(src)
        if version_tuple(new) <= version_tuple(VERSION):
            self.note = "em dia (publicada: %s)" % (new or "?")
            return False
        if not source_ok(src):
            self.note = self.alert = "atualização %s ignorada: arquivo baixado inválido" % new
            self.say("AVISO: " + self.alert)
            return False
        self.waiting = self.acfg.window_wait() if self.acfg is not None else 0
        if self.waiting:
            self.note = "versão %s disponível; aguardando a janela de atualização (%s h)" % (
                new, self.acfg.get("update", "window"))
            return False
        self.say("Atualização: versão %s disponível (em execução: %s); instalando..." % (new, VERSION))
        try:
            self.install(src)
        except OSError as e:
            self.note = self.alert = "atualização %s falhou ao gravar: %s" % (new, e)
            self.say("AVISO: %s (seguindo na versão %s)" % (self.alert, VERSION))
            return False
        self.version, self.alert = new, ""
        self.note = "versão %s instalada; reiniciando" % new
        self.restart.set()
        if self.on_restart:
            self.on_restart()
        return True

    def install(self, src):
        """Grava ao lado do script (.novo) e troca de uma vez (os.replace): nunca fica meio arquivo."""
        tmp = self.script + ".novo"
        st = os.stat(self.script)
        try:
            with open(tmp, "w", encoding="utf-8") as f:
                f.write(src)
                f.flush()
                os.fsync(f.fileno())
            os.chmod(tmp, stat.S_IMODE(st.st_mode) | 0o755)
            try:
                os.chown(tmp, st.st_uid, st.st_gid)   # rodando como root: mantém o dono original
            except (OSError, AttributeError):         # AttributeError: Windows (sem chown)
                pass
            os.replace(tmp, self.script)
        except OSError:
            with contextlib.suppress(OSError):
                os.remove(tmp)
            raise


def restart_argv(argv):
    """Argumentos do reinício pós-atualização: os originais + --no-bench --no-install (sem repetir)."""
    return list(argv) + [x for x in ("--no-bench", "--no-install") if x not in argv]


def reexec(script, version, argv, reason=""):
    """Substitui este processo pela versão nova, no mesmo terminal (tmux), com os mesmos argumentos.
    Coletor filho do --service: sai com SERVICE_RESTART e o pai (supervisor) inicia a versão nova. Windows sem
    supervisor (console): não há execv que mantenha o console, então roda a versão nova como filho e sai com o
    código dela."""
    print("\n%s; reiniciando..." % (reason or "Atualizado para a versão %s" % version), flush=True)
    FB_HTTP.close_all()                   # sockets já não são herdáveis (PEP 446); fecha antes por garantia
    if os.environ.get(SUPERVISED_ENV) == "1":
        sys.exit(SERVICE_RESTART)
    py = sys.executable or shutil.which("python3") or "/usr/bin/python3"
    args = [py, script] + restart_argv(argv)
    if IS_WINDOWS:
        sys.exit(run_child([py, "-X", "utf8", script] + restart_argv(argv)))
    try:
        os.execv(py, args)
    except OSError as e:
        die("não consegui reiniciar (%s). Inicie de novo: %s" % (e, " ".join(shlex.quote(x) for x in args)))


# --------------------------------------------------------------------------
# Configuração da nuvem (no servidor) e recuperação dos relatórios (em qualquer máquina)
# --------------------------------------------------------------------------
def ask(prompt, default=""):
    ans = input("%s%s: " % (prompt, " [%s]" % default if default else "")).strip()
    return ans or default


def yes(prompt, default=True):
    ans = input("%s [%s] " % (prompt, "S/n" if default else "s/N")).strip().lower()
    return default if not ans else ans in ("s", "sim", "y", "yes")


PASTE_MARKS = ("\x1b[200~", "\x1b[201~")      # "bracketed paste" de alguns terminais


def ask_secret(prompt):
    """Lê um segredo mostrando * a cada caractere (digitado ou colado) e diz quantos chegaram:
    sem eco nenhum não dá para saber se a colagem funcionou. Sem terminal (ou no Windows, sem
    termios) cai no getpass."""
    try:
        import termios
        import tty
    except ImportError:                                  # Windows
        termios = None
    if termios is None and msvcrt is not None and sys.stdin.isatty():
        s = read_masked_win(prompt, msvcrt).strip()      # console do Windows: mesmo eco '*'
    elif termios is None or not sys.stdin.isatty():
        s = getpass.getpass(prompt).strip()
    else:
        s = read_masked(prompt, sys.stdin.fileno(), termios, tty).strip()
    if s:
        print("  (%d caracteres recebidos)" % len(s))
    return s


def read_masked(prompt, fd, termios, tty):
    out = sys.stdout
    out.write(prompt)
    out.flush()
    old = termios.tcgetattr(fd)
    dec = codecs.getincrementaldecoder("utf-8")("replace")
    buf = []
    try:
        tty.setraw(fd)                  # Ctrl+C chega como \x03 (tratado abaixo)
        while True:
            chunk = dec.decode(os.read(fd, 1024))
            for m in PASTE_MARKS:
                chunk = chunk.replace(m, "")
            for ch in chunk:
                if ch in "\r\n":
                    out.write("\r\n")
                    out.flush()
                    return "".join(buf)
                if ch == "\x03":
                    raise KeyboardInterrupt
                if ch == "\x04" and not buf:
                    raise EOFError
                if ch in "\x7f\x08":
                    if buf:
                        buf.pop()
                        out.write("\b \b")
                elif ch == "\x15":                     # Ctrl+U apaga tudo
                    out.write("\b \b" * len(buf))
                    buf = []
                elif ch >= " ":
                    buf.append(ch)
                    out.write("*")
            out.flush()
    finally:
        termios.tcsetattr(fd, termios.TCSADRAIN, old)


def read_masked_win(prompt, con):
    """read_masked para o console do Windows (msvcrt.getwch: caractere a caractere, sem eco; colar chega como
    digitação). Teclas especiais (setas, F1...) chegam como prefixo \\x00/\\xe0 + código e são ignoradas."""
    out = sys.stdout
    out.write(prompt)
    out.flush()
    buf = []
    while True:
        ch = con.getwch()
        if ch in ("\x00", "\xe0"):
            con.getwch()
            continue
        if ch in "\r\n":
            out.write("\n")
            out.flush()
            return "".join(buf)
        if ch == "\x03":
            raise KeyboardInterrupt
        if ch in ("\x1a", "\x04") and not buf:              # Ctrl+Z / Ctrl+D sem nada = fim da entrada
            raise EOFError
        if ch == "\x08":
            if buf:
                buf.pop()
                out.write("\b \b")
        elif ch == "\x15":
            out.write("\b \b" * len(buf))
            buf = []
        elif ch >= " ":
            buf.append(ch)
            out.write("*")
        out.flush()


def db_url_ok(url):
    """https:// sempre; http:// (sem criptografia: o token iria em claro) só para o emulador local:
    localhost, 127.0.0.1, ::1 ou *.localhost (o Firebase Emulator aceita <namespace>.localhost)."""
    u = urllib.parse.urlparse(url)
    host = (u.hostname or "").lower()
    if u.scheme == "https":
        return bool(host)
    return u.scheme == "http" and (host in ("localhost", "127.0.0.1", "::1") or host.endswith(".localhost"))


def setup_firebase(ident):
    """Cadastra esta instalação no Firebase (status ao vivo, eventos e histórico)."""
    cur = ident.data.get("live") or {}
    if not ident.name:                                    # sem nome o painel central só teria o hostname
        ident.ask_name()
    print("""
FIREBASE (painel central da C2). Enter aceita o valor entre colchetes (projeto da C2);
  o código de cadastro fica no console do Firebase, em config/enroll_code.
""")
    db = ask("URL do Realtime Database", cur.get("db_url") or FIREBASE_DB_URL).rstrip("/")
    key = ask("Chave de API da Web", cur.get("api_key") or FIREBASE_API_KEY)
    code = ask_secret("Código de cadastro (aparece como *): ")
    return enroll_firebase(ident, db, key, code)


def enroll_firebase(ident, db, key, code):
    """Cadastro desta instalação no Firebase com URL, chave de API e código já informados (sem perguntas).
    Devolve 0 (ok) ou 1; nunca imprime o código nem tokens."""
    if not key or not db_url_ok(db):
        print("ERRO: URL ou chave inválida (use https://; http:// só para emulador local).")
        return 1
    prev = ident.data.get("live")
    ident.data["live"] = {"db_url": db, "api_key": key}
    live = LiveStatus(ident, ident.base)
    try:
        if os.path.exists(live.path):
            try:
                live.token()                              # reaproveita a identidade desta instalação
            except CloudError:
                live.sign_up()
        else:
            live.sign_up()
        res = live.claim(ident.install_id, code)
        live.patch("", {"info/" + ident.install_id: {
            "install_id": ident.install_id, "company": clip(ident.company, RTDB_ID_MAX),
            "company_id": clip(ident.company_id, RTDB_ID_MAX), "hostname": clip(platform.node().split(".")[0], RTDB_ID_MAX),
            "name": clip(ident.name, RTDB_ID_MAX), "monitor_version": VERSION, "updated_at_ms": {".sv": "timestamp"},
            **({"os": dict(os_info(), updated_at_ms={".sv": "timestamp"})} if os_info() else {})}})
    except CloudError as e:
        if prev is None:                                  # falhou: a memória volta a dizer "não configurado"
            ident.data.pop("live", None)
        else:
            ident.data["live"] = prev
        print("ERRO: %s" % e)
        if "recusou" in str(e):
            print("      (código de cadastro errado, ou este servidor já pertence a outra instalação)")
        return 1
    ident.save()
    print("OK: servidor %s no Firebase (%s). Identidade própria em %s (permissão 600)." % (res, db, live.path))
    return 0


# --------------------------------------------------------------------------
# Configuração por JSON colado (v2.7.1): tudo o que falta de uma vez, na partida ou com --config-json
# --------------------------------------------------------------------------
CONFIG_ITEMS = (("empresa", "empresa"), ("nome", "nome do servidor"),
                ("firebase", "Firebase (url, api_key, codigo_cadastro)"), ("chave_catalogo", "chave do catálogo do banco"))
CONFIG_EXAMPLE = ('{"empresa": "Empresa Exemplo", "nome": "Empresa Exemplo - Linux", "firebase": {"url": '
                  '"https://projeto-exemplo.firebaseio.com", "api_key": "AIza...", "codigo_cadastro": "..."}, '
                  '"chave_catalogo": "<64 caracteres 0-9 a-f>"}')
CONFIG_MAX = 65536               # tamanho máximo do JSON colado


def config_missing(ident):
    """Itens de configuração que faltam nesta instalação, na ordem de CONFIG_ITEMS."""
    miss = []
    if not ident.company:
        miss.append("empresa")
    if not ident.name:
        miss.append("nome")
    if not LiveStatus(ident, ident.base).configured():
        miss.append("firebase")
    if read_catkey(os.path.join(ident.base, CATKEY_FILE)) is None:
        miss.append("chave_catalogo")
    return miss


def parse_config_json(text):
    """Valida o JSON de configuração. Devolve (dict normalizado, erro): erro vazio = válido. Campos ausentes
    ficam de fora do dict; firebase.url/api_key ausentes = padrões do projeto na hora de aplicar."""
    try:
        doc = json.loads(text)
    except ValueError as e:
        return None, "JSON inválido (%s)" % e
    if not isinstance(doc, dict):
        return None, "o JSON precisa ser um objeto { ... }"
    out = {}
    extra = sorted(k for k in doc if k not in dict(CONFIG_ITEMS))
    if extra:
        return None, "campo desconhecido: %s (use empresa, nome, firebase, chave_catalogo)" % ", ".join(extra)
    for k in ("empresa", "nome"):
        if k in doc:
            if not isinstance(doc[k], str) or not doc[k].strip():
                return None, '"%s" precisa ser um texto não vazio' % k
            out[k] = " ".join(doc[k].split())
    if "firebase" in doc:
        fb = doc["firebase"]
        if not isinstance(fb, dict):
            return None, '"firebase" precisa ser um objeto {"url", "api_key", "codigo_cadastro"}'
        bad = sorted(k for k in fb if k not in ("url", "api_key", "codigo_cadastro"))
        if bad:
            return None, "campo desconhecido em firebase: %s" % ", ".join(bad)
        for k in ("url", "api_key", "codigo_cadastro"):
            if k in fb and (not isinstance(fb[k], str) or not fb[k].strip()):
                return None, '"firebase.%s" precisa ser um texto não vazio' % k
        f = {k: fb[k].strip() for k in fb}
        if "url" in f:
            f["url"] = f["url"].rstrip("/")
            if not db_url_ok(f["url"]):
                return None, '"firebase.url" precisa começar com https:// (http:// só para o emulador local)'
        out["firebase"] = f
    if "chave_catalogo" in doc:
        k = parse_catkey(doc["chave_catalogo"] if isinstance(doc["chave_catalogo"], str) else "")
        if k is None:
            return None, '"chave_catalogo" precisa ter 64 caracteres de 0-9 e a-f'
        out["chave_catalogo"] = k
    return out, ""


def apply_config(ident, cfg, missing):
    """Aplica do JSON só os itens que faltavam (os já configurados ficam como estão; avisa). Devolve os itens
    que continuam faltando. Mensagens sem segredos (código de cadastro e chave nunca são impressos)."""
    left = list(missing)
    ignored = [k for k in cfg if k not in missing]
    if ignored:
        print("Já configurado, ignorado do JSON: %s" % ", ".join(dict(CONFIG_ITEMS)[k] for k in ignored))
    if "empresa" in missing and "empresa" in cfg:
        ident.set_company(cfg["empresa"])
        print("OK: empresa = %s" % ident.company)
        left.remove("empresa")
    if "nome" in missing and "nome" in cfg:
        ident.set_name(cfg["nome"])
        print("OK: nome do servidor = %s" % ident.name)
        left.remove("nome")
    if "firebase" in missing and "firebase" in cfg:
        fb, cur = cfg["firebase"], ident.data.get("live") or {}
        db = fb.get("url") or cur.get("db_url") or FIREBASE_DB_URL
        key = fb.get("api_key") or cur.get("api_key") or FIREBASE_API_KEY
        if "codigo_cadastro" not in fb:
            ident.data["live"] = {"db_url": db, "api_key": key}   # padrões das perguntas individuais
            ident.save()
            print("Firebase: falta o codigo_cadastro no JSON (será perguntado)")
        elif enroll_firebase(ident, db, key, fb["codigo_cadastro"]) == 0:
            left.remove("firebase")
    if "chave_catalogo" in missing and "chave_catalogo" in cfg:
        path = os.path.join(ident.base, CATKEY_FILE)
        write_private(path, cfg["chave_catalogo"].hex() + "\n")
        print("OK: chave do catálogo salva em %s (permissão 600)" % path)
        left.remove("chave_catalogo")
    return left


def read_json_paste(prompt):
    """Lê um JSON colado em uma ou várias linhas: para quando as chaves se fecham. Enter na 1ª linha (ou EOF
    sem nada) = None (responder uma a uma)."""
    lines, depth = [], 0
    while True:
        try:
            line = input(prompt if not lines else "")
        except EOFError:
            return "\n".join(lines) or None
        if not lines and not line.strip():
            return None
        lines.append(line)
        depth = sum(l.count("{") - l.count("}") for l in lines)
        if depth <= 0 or sum(len(l) for l in lines) > CONFIG_MAX:
            return "\n".join(lines)


def ask_config_json(ident):
    """Na partida com painel: faltando qualquer item, mostra a lista e aceita um JSON único com tudo.
    Enter vazio = segue para as perguntas individuais. Devolve os itens que continuam faltando."""
    missing = config_missing(ident)
    if not missing:
        return []
    print("\nCONFIGURAÇÃO PENDENTE deste servidor:")
    for k in missing:
        print("  - %s" % dict(CONFIG_ITEMS)[k])
    print("Formato (os campos já configurados podem ficar de fora):\n  %s" % CONFIG_EXAMPLE)
    while True:
        text = read_json_paste("Cole o JSON de configuração (ou Enter para responder uma a uma): ")
        if text is None:
            return missing
        cfg, err = parse_config_json(text)
        if err:
            print("ERRO: %s. Tente de novo (ou Enter para responder uma a uma)." % err)
            continue
        return apply_config(ident, cfg, missing)


def config_from_file(ident, src):
    """--config-json ARQ|-: mesma configuração, sem perguntas. Devolve o código de saída (0 = nada faltando)."""
    try:
        text = sys.stdin.read() if src == "-" else open(src, encoding="utf-8").read()
    except OSError as e:
        print("ERRO: não consegui ler %s: %s" % (src, e.strerror or e))
        return 1
    cfg, err = parse_config_json(text)
    if err:
        print("ERRO: %s" % err)
        return 1
    left = apply_config(ident, cfg, config_missing(ident))
    if left:
        print("Ainda falta: %s" % ", ".join(dict(CONFIG_ITEMS)[k] for k in left))
        return 1
    print("OK: configuração completa.")
    return 0


def require_firebase(ident):
    """Firebase ausente na partida com painel (instalador antigo, ou cadastro que falhou): faz as
    perguntas na hora e repete até dar certo. Ctrl+C encerra; sem entrada (EOF) devolve False."""
    print("\nFIREBASE NÃO CONFIGURADO: este servidor ainda não aparece no painel central da C2.")
    while True:
        try:
            if setup_firebase(ident) == 0:
                return True
        except EOFError:
            return False
        print("\nNão deu certo; vamos de novo (Ctrl+C cancela).")


def setup_github(ident):
    print("""
GITHUB (opcional): arquivo dos relatórios completos, em um repositório PRIVADO.
  Token fine-grained com acesso só a esse repositório, permissão Contents: Read and write.
""")
    repo = ask("Repositório (dono/nome)", ident.repo)
    token = ask_secret("Token (aparece como *; Enter mantém o atual): ") or load_token(ident.base)
    if not token:
        print("ERRO: token não informado.")
        return 1
    try:
        gh = GitHub(repo, token)
        info = gh.repo_info()
        if not info.get("private"):
            print("ERRO: %s é público. Use um repositório privado." % repo)
            return 1
        if gh.is_empty():
            if yes("O repositório está vazio; criar um README inicial (necessário para as Releases)?"):
                gh.create_readme()
            else:
                print("ERRO: sem um primeiro commit o GitHub não permite criar Releases.")
                return 1
    except CloudError as e:
        print("ERRO: %s" % e)
        return 1
    write_private(os.path.join(ident.base, TOKEN_FILE), token + "\n")
    ident.data["cloud_repo"] = repo
    ident.save()
    print("OK: %s configurado (token em %s, permissão 600)." % (repo, os.path.join(ident.base, TOKEN_FILE)))
    return 0


SYNC_LABELS = [("auto", "envio automático"), ("interval_normal", "intervalo normal (s)"),
               ("interval_alert", "intervalo em ATENÇÃO/CRÍTICO (s)"), ("send_on_alert", "envio imediato no alerta"),
               ("send_on_recover", "envio imediato na recuperação"), ("heartbeat_interval", "heartbeat (s)"),
               ("offline_after", "OFFLINE após (s sem heartbeat)"), ("history_interval", "histórico no GitHub a cada (s)"),
               ("retention_local_days", "retenção local (dias)"), ("retention_cloud_days", "retenção na nuvem (dias)"),
               ("retention_events_days", "retenção de eventos (dias)"), ("recent_hours", "resolução total na nuvem (horas)")]


def setup_sync(ident):
    cfg = ident.sync_cfg()
    print("\nSINCRONIZAÇÃO (padrões; podem ser mudados depois em %s, seção \"sync\"):" % CONFIG_FILE)
    for k, label in SYNC_LABELS:
        v = cfg[k]
        print("  %-38s %s" % (label, ("sim" if v else "não") if isinstance(v, bool) else v))
    if yes("Usar esses valores?"):
        ident.data.setdefault("sync", {})
        ident.save()
        return
    new = dict(ident.data.get("sync") or {})
    for k, label in SYNC_LABELS:
        v = cfg[k]
        ans = input("  %s [%s]: " % (label, ("s" if v else "n") if isinstance(v, bool) else v)).strip().lower()
        if not ans:
            continue
        if isinstance(v, bool):
            new[k] = ans in ("s", "sim", "y")
        else:
            try:
                new[k] = int(ans)
            except ValueError:
                print("    valor ignorado (número inteiro)")
    ident.data["sync"] = new
    ident.save()


def cloud_setup(ident, only=None):
    print("=" * 64)
    print("   NUVEM: Firebase (status, eventos e histórico) + GitHub (arquivo, opcional)")
    print("=" * 64)
    try:
        rc = 0
        if only in (None, "firebase") and (only == "firebase" or yes("\nConfigurar o Firebase (painel central)?")):
            rc |= setup_firebase(ident)
        if only in (None, "github") and (only == "github" or yes("\nArquivar também os relatórios completos no GitHub?",
                                                                    default=bool(ident.repo))):
            rc |= setup_github(ident)
        if only is None:
            setup_sync(ident)
    except (EOFError, KeyboardInterrupt):
        print()
        return 1
    if rc == 0:
        print("\nPronto. O envio é automático enquanto o monitor roda (tecla u = enviar agora; --sync = manual).")
    return rc


def choose(title, items, allow_all=True):
    """Menu numerado; aceita '2', '1,3' ou '0' (todos). Devolve a lista escolhida."""
    print("\n%s\n" % title)
    for i, it in enumerate(items, 1):
        print("  %d. %s" % (i, it))
    if allow_all and len(items) > 1:
        print("  0. todos")
    while True:
        try:
            ans = input("\nSelecione: ").strip()
        except EOFError:
            return []
        try:
            nums = [int(x) for x in ans.replace(" ", "").split(",") if x]
        except ValueError:
            nums = []
        if allow_all and nums == [0]:
            return list(range(len(items)))
        if nums and all(1 <= n <= len(items) for n in nums):
            return [n - 1 for n in nums]
        print("Opção inválida.")


def cloud_pull(a, script_dir):
    """Baixa relatórios da nuvem (empresa > servidor > período) e monta um arquivo por servidor."""
    ident = Identity(script_dir)
    repo = a.repo or os.environ.get("USAGE_MONITOR_REPO") or ident.repo
    try:
        if not repo:
            repo = input("Repositório dos relatórios (dono/nome): ").strip()
        token = load_token(script_dir)
        if not token:
            die("sem token: faça 'gh auth login' ou defina GH_TOKEN.")
        gh = GitHub(repo, token)
        print("C2 SERVER MONITOR — RELATÓRIOS NA NUVEM (%s)" % repo)
        servers = {}
        for rel in gh.releases():
            if not rel.get("tag_name", "").startswith("srv-"):
                continue
            m = META_RE.search(rel.get("body") or "")
            try:
                meta = json.loads(m.group(1)) if m else {}
            except ValueError:
                meta = {}
            key = meta.get("install_id") or rel["tag_name"].rsplit("-", 1)[0]
            s = servers.setdefault(key, {"meta": meta, "rels": []})
            s["rels"].append(rel)
            if str(meta.get("year", "")) >= str(s["meta"].get("year", "")):
                s["meta"] = meta                           # dados mais recentes (empresa renomeada etc.)
        if not servers:
            print("\nNenhum relatório na nuvem ainda.")
            return
        companies = sorted({s["meta"].get("company") or "(sem empresa)" for s in servers.values()}, key=str.lower)
        pick = [companies[i] for i in choose("Empresas disponíveis:", companies)]
        cand = sorted((s for s in servers.values() if (s["meta"].get("company") or "(sem empresa)") in pick),
                      key=lambda s: ((s["meta"].get("company") or "").lower(), s["meta"].get("hostname", "")))
        labels = ["%s · %s (%s)" % (s["meta"].get("company") or "?", s["meta"].get("hostname", "?"),
                                    (s["meta"].get("install_id") or "?")[:8]) for s in cand]
        sel = [cand[i] for i in choose("Servidores disponíveis:", labels)]
        per = choose("Período:", ["Últimas 24 horas", "Últimos 7 dias", "Últimos 30 dias", "Personalizado", "Tudo"],
                     allow_all=False)
        if not sel or not per:
            return
        today = datetime.date.today()
        lo, hi = None, today.isoformat()
        if per[0] in (0, 1, 2):
            lo = (today - datetime.timedelta(days=(1, 6, 29)[per[0]])).isoformat()
        elif per[0] == 3:
            lo = input("De (AAAA-MM-DD): ").strip()
            hi = input("Até (AAAA-MM-DD) [hoje]: ").strip() or hi
    except (EOFError, KeyboardInterrupt):
        print()
        return
    except CloudError as e:
        die(str(e))
    made = []
    for s in sel:
        meta = s["meta"]
        dest = os.path.join(a.out, slug(meta.get("company") or "sem-empresa"),
                            "%s-%s" % (slug(meta.get("hostname") or "servidor"), (meta.get("install_id") or "x")[:8]))
        os.makedirs(dest, exist_ok=True)
        days = []
        try:
            for rel in s["rels"]:
                for asset in gh.assets(rel["id"]):
                    day = asset["name"][:10]
                    if not asset["name"].endswith(".log.gz") or (lo and day < lo) or day > hi:
                        continue
                    p = os.path.join(dest, asset["name"])
                    if not (os.path.exists(p) and os.path.getsize(p) == asset["size"]):
                        data = gh.download_asset(asset["id"])
                        with open(p + ".tmp", "wb") as f:
                            f.write(data)
                        os.replace(p + ".tmp", p)
                        print("  baixado %s / %s" % (os.path.basename(dest), asset["name"]))
                    days.append(p)
        except CloudError as e:
            print("ERRO em %s: %s" % (dest, e))
            continue
        if not days:
            print("  %s: nenhum arquivo no período." % dest)
            continue
        merged = os.path.join(dest, "usage_report_%s.log" % slug(meta.get("hostname") or "servidor"))
        with open(merged + ".tmp", "wb") as out:
            for p in sorted(days):
                with gzip.open(p) as f:
                    shutil.copyfileobj(f, out)
        os.replace(merged + ".tmp", merged)
        made.append(merged)
    if not made:
        return
    print("\nRelatórios prontos:")
    for m in made:
        print("  %s" % m)
    print("Para abrir:  %s --view <arquivo>" % sys.argv[0])
    if len(made) == 1 and sys.stdin.isatty() and sys.stdout.isatty():
        try:
            ans = input("\nAbrir no painel agora? [S/n] ").strip().lower()
        except (EOFError, KeyboardInterrupt):
            print()
            return
        if ans in ("", "s", "sim", "y"):
            run_dashboard(History(made[0]), None, a)


# --------------------------------------------------------------------------
# Painel (curses)
# --------------------------------------------------------------------------
PERIODS = [("1", "1h", 3600), ("2", "6h", 6 * 3600), ("3", "24h", 86400), ("4", "7d", 7 * 86400), ("5", "tudo", None)]
LEVEL_NAMES = ["NORMAL", "ATENÇÃO", "CRÍTICO"]
RESOURCES = [("cpu", "CPU"), ("mem", "MEMÓRIA"), ("disk", "DISCO"), ("space", "ESPAÇO")]
RES_NAME = {"cpu": "CPU", "mem": "Memória", "disk": "Disco", "space": "Espaço"}
PERIOD_TITLES = ["ÚLTIMA HORA", "ÚLTIMAS 6 HORAS", "ÚLTIMAS 24 HORAS", "ÚLTIMOS 7 DIAS", "TODO O HISTÓRICO"]

HELP = """\
COMO LER
  O topo diz se o servidor está bem agora e qual recurso é o problema. Cada recurso tem
  uma barra (agora), o histórico do período e uma frase de diagnóstico. No histórico, a
  cor mostra o ESTADO naquele momento (não o tamanho do número), e a linha abaixo marca
  início e fim de cada problema:  ─ atenção   ═ crítico   · monitor parado (sem dados).
  Parte cheia da coluna = média; parte sombreada = pico (picos curtos não somem).
  "Banco:" (só se a central configurou o acesso ao PostgreSQL) = conexão e último pedido;
  faltando a chave do catálogo, a tecla k a pede ali mesmo (aparece como *).

ESTADOS (avaliados em cada janela gravada; o geral é o pior dos recursos)
  NORMAL     sem sinais de pressão.
  ATENÇÃO    uso elevado ou pressão inicial.
  CRÍTICO    evidência de gargalo: processos esperando o recurso.
  SEM DADOS  monitor parado ou medições atrasadas.

CRITÉRIOS
  CPU      crítico: fila média > nº de vCPUs, ou processos esperando CPU >= 10% do tempo
           (PSI), ou CPU retida pelo hypervisor (steal) >= 20%
           atenção: espera >= 5%, fila acima das vCPUs em >= 1/4 das amostras, steal >= 5%,
           uso >= 80% sem fila, ou um núcleo sempre ocupado (processo de 1 thread)
  MEMÓRIA  crítico: processos travados esperando RAM >= 10% do tempo (ou todos >= 5%),
           ou uso >= 90% com paginação de swap >= 50 páginas/s
           atenção: espera >= 2%, swap >= 10 páginas/s, ou disponível < 10%
  DISCO    crítico: processos esperando I/O >= 30% do tempo (ou todos >= 20%), ou disco
           >= 90% ocupado com fila >= 2 ou latência >= 50 ms
           atenção: espera >= 10%, latência >= 20 ms, pico >= 90% da capacidade medida,
           ou disco >= 90% ocupado sem outros sinais
  ESPAÇO   ocupação de cada filesystem (/, /var, /home...; vale o pior):
           crítico: >= 95% ocupado ou < 1 GB livre; atenção: >= 85% ou < 5 GB livres
           (os limites em GB só valem para filesystems de 10 GB ou mais)
  "% ocupado" do disco é o tempo com I/O em andamento, não a capacidade: um storage com
  vários discos/SSD pode estar 100% ocupado e ainda ter folga. Por isso CRÍTICO exige
  espera, fila ou latência. Cache do Linux não conta como memória usada.

TECLAS
  1 2 3 4 5   período: 1 h, 6 h, 24 h, 7 dias, todo o histórico
  d           detalhes técnicos (Tab ou setas trocam a tela; n troca o disco)
  p pausa a tela (a coleta continua)    r relê o relatório    ? esta ajuda    q sair
  u           envia os relatórios para a nuvem agora (se configurada com --cloud-setup)
  k           informa ou troca a chave do catálogo do acesso ao banco (Enter grava, Esc cancela)
"""


class Glyphs:
    """Caracteres dos gráficos. 'unicode' (padrão) tem resolução de 1/8 de célula, mas exige
    fonte completa (sem ela aparecem quadrados vazios); 'compat' (--compat) usa só o que
    praticamente toda fonte tem (inclusive PuTTY/Consolas); 'ascii' para terminal sem UTF-8."""

    def __init__(self, mode):
        self.mode = mode
        if mode == "unicode":
            self.v = " ▁▂▃▄▅▆▇█"
            self.h = "        █"       # barras: só bloco inteiro (blocos parciais faltam em muitas fontes)
            self.peak, self.gap, self.empty, self.rule, self.ref = "░", "·", "░", "─", "┄"
            self.mark = ["", "─", "━"]; self.dot = "●"; self.warn = "▲"
            self.box = "┌┐└┘│─"
        elif mode == "compat":
            self.v = " _▄▄▄▄███"; self.h = "        █"
            self.peak, self.gap, self.empty, self.rule, self.ref = "░", "·", "░", "─", "-"
            self.mark = ["", "─", "═"]; self.dot = "●"; self.warn = "▲"
            self.box = "┌┐└┘│─"
        else:
            self.v = " ..--==##"; self.h = " ..--==##"
            self.peak, self.gap, self.empty, self.rule, self.ref = ":", ".", ".", "-", "-"
            self.mark = ["", "-", "="]; self.dot = "*"; self.warn = "!"
            self.box = "++++|-"


class Quit(Exception):
    pass


class Restart(Quit):
    """O painel sai para o coletor reiniciar na versão nova (autoatualização)."""


class Dashboard:
    def __init__(self, scr, hist, monitor, a, sync=None, ident=None):
        self.scr, self.hist, self.mon, self.a = scr, hist, monitor, a
        self.sync, self.ident = sync, ident
        self.flash = ("", 0, 0.0)    # mensagem curta temporária (texto, atributo, até quando)
        self.cloud_checked, self.cloud_cache = 0.0, ("", "")
        self.db_checked, self.db_cache = 0.0, {}
        self.mode = "coleta + painel" if monitor else "somente visualização"
        self.period = 0
        self.tech = False            # modo técnico (tecla d)
        self.tab = 0
        self.help = False
        self.ev_key = None
        self.ev = []
        self.disk_i = 0
        self.paused = False
        self.quit_armed = 0.0
        self.cache = {}
        self.live = None
        self.live_mtime = 0
        self.live_file = live_path(hist.path)
        self.loading = True
        self.xmax = None             # limite à direita do painel sendo desenhado
        enc = (locale.getpreferredencoding(False) or "").lower().replace("-", "")
        if os.name == "nt":
            enc = "utf8"                 # windows-curses escreve Unicode direto no console
        self.g = Glyphs("ascii" if a.ascii or enc != "utf8" else "compat" if a.compat else "unicode")
        self.init_colors()

    # ---- cores ----
    def init_colors(self):
        A = {}
        mono = self.a.mono or os.environ.get("NO_COLOR") or not curses.has_colors()
        if not mono:
            try:
                curses.start_color()
                bg = -1
                try:
                    curses.use_default_colors()
                except curses.error:
                    bg = curses.COLOR_BLACK
                g256 = curses.COLORS >= 256
                for i, c in enumerate((curses.COLOR_GREEN, curses.COLOR_YELLOW, curses.COLOR_RED, curses.COLOR_CYAN,
                                       244 if g256 else curses.COLOR_WHITE, curses.COLOR_MAGENTA,
                                       250 if g256 else curses.COLOR_WHITE), 1):
                    curses.init_pair(i, c, bg)
                cp = curses.color_pair
                dim = cp(5) | (0 if g256 else curses.A_DIM)
                A = {"ok": cp(1), "warn": cp(2), "high": cp(6) | curses.A_BOLD, "crit": cp(3) | curses.A_BOLD,
                     "title": cp(4) | curses.A_BOLD, "dim": dim, "accent": cp(4), "text": curses.A_NORMAL,
                     "bold": curses.A_BOLD, "neutral": cp(7), "nodata": dim}
            except curses.error:
                mono = True
        if mono:
            A = {"ok": curses.A_NORMAL, "warn": curses.A_BOLD, "high": curses.A_BOLD | curses.A_UNDERLINE,
                 "crit": curses.A_REVERSE | curses.A_BOLD, "title": curses.A_BOLD, "dim": curses.A_DIM,
                 "accent": curses.A_BOLD, "text": curses.A_NORMAL, "bold": curses.A_BOLD,
                 "neutral": curses.A_NORMAL, "nodata": curses.A_DIM}
        self.A = A
        self.lvl_attr = [A["ok"], A["warn"], A["high"], A["crit"]]
        # estado: discreto quando normal, destacado quando não
        self.col_attr = [A["neutral"], A["warn"], A["crit"]]
        self.lbl_attr = [A["dim"], A["warn"] | curses.A_BOLD, A["crit"]]

    def pct_attr(self, v, warn=70, high=90):
        if v is None or v != v:
            return self.A["dim"]
        return self.A["crit"] if v >= high else self.A["warn"] if v >= warn else self.A["ok"]

    # ---- desenho básico ----
    def put(self, y, x, s, attr=0):
        H, W = self.H, self.W
        if self.xmax is not None:
            W = min(W, self.xmax)
        if y < 0 or y >= H or x >= W:
            return x
        s = s[:max(0, W - x - (1 if y == self.H - 1 and W == self.W else 0))]
        try:
            self.scr.addstr(y, x, s, attr)
        except curses.error:
            pass
        return x + len(s)

    def wrap(self, y, x, w, text, attr, bottom, cont_x=None, xmax=None):
        """Escreve quebrando em palavras; linhas seguintes começam em cont_x. Devolve a próxima linha livre."""
        xmax = xmax or x + w
        cont_x = x if cont_x is None else cont_x
        lead = len(text) - len(text.lstrip(" "))
        line, cx = " " * lead, x
        for word in text.split():
            if line.strip() and cx + len(line) + 1 + len(word) > xmax:
                if y >= bottom:
                    return y
                self.put(y, cx, line, attr)
                y, cx, line = y + 1, cont_x, word
            else:
                line = (line + " " + word) if line.strip() else line + word
        if line.strip() and y < bottom:
            self.put(y, cx, line, attr)
            y += 1
        return y

    def puts(self, y, x, parts):
        """Escreve [(texto, atributo), ...] em sequência."""
        for t, a in parts:
            x = self.put(y, x, t, a)
        return x

    def rule(self, y, title, right=""):
        self.put(y, 0, self.g.rule * self.W, self.A["dim"])
        self.put(y, 1, " %s " % title, self.A["title"])
        if right:
            self.put(y, max(0, self.W - len(right) - 2), " %s " % right, self.A["dim"])

    def bar(self, y, x, w, v, vmax=100.0, attr=None):
        if w <= 0:
            return
        if v is None or v != v:
            self.put(y, x, self.g.empty * w, self.A["dim"])
            return
        f = max(0.0, min(1.0, v / vmax)) * w
        s = self.g.h[8] * int(f + 0.5)            # só blocos inteiros: nada de caractere parcial na ponta
        self.put(y, x, s, self.pct_attr(100 * v / vmax) if attr is None else attr)
        self.put(y, x + len(s), self.g.empty * (w - len(s)), self.A["dim"])

    # ---- dados ----
    def anchor(self):
        """Fim do período: agora; ou a última medição, se o relatório parou há mais de 1 h
        (relatório copiado de outro servidor, monitor desligado)."""
        h, now = self.hist, time.time()
        if self.mon or self.cur()[0] == "live" or h.last_ts is None or now - h.last_ts <= 3600:
            return now
        return h.last_ts + 60

    def span(self):
        h = self.hist
        now = self.anchor()
        _, _, p = PERIODS[self.period]
        if p is None:
            t0 = h.first_ts if h.first_ts is not None else now - 3600
            p = math.ceil(max(3600, now - t0) / 3600.0) * 3600     # estável: não invalida o cache a cada segundo
        return now - p, now, p

    def source(self, p):
        h = self.hist
        if p > RAW_KEEP or (h.raw.ts and h.first_ts is not None and h.first_ts < h.raw.ts[0] - h.raw.win[0] - 60 and p > 7 * 86400):
            return "roll"
        return "raw"

    def series(self, ka, km, ncol, mode="avg"):
        """Valores por coluna no período: (médias, máximos, cobertura). None = sem dados."""
        t0, t1, p = self.span()
        cw = p / ncol
        q = math.ceil(t1 / max(cw, 1)) * max(cw, 1)       # estável até a próxima coluna
        t0, t1 = q - p, q
        src = self.source(p)
        key = (ka, km, ncol, round(t0), src, self.hist.version)
        c = self.cache.get(key)
        if c is not None:
            return c
        if len(self.cache) > 400:
            self.cache.clear()
        sums = [0.0] * ncol; ws = [0.0] * ncol; mxs = [None] * ncol; cov = [0.0] * ncol
        h = self.hist
        if src == "raw":
            ts, wins = h.raw.ts, h.raw.win
            A = h.raw.cols.get(ka); M = h.raw.cols.get(km) if km else None
            rng = range(bisect.bisect_left(ts, t0), len(ts))
            get_a = (lambda i: A[i]) if A is not None else (lambda i: NAN)
            get_m = (lambda i: M[i]) if M is not None else get_a
            spans = ((ts[i] - wins[i], ts[i], i) for i in rng)
        else:
            R = h.roll
            ca = R.cols.get(ka); cm = R.cols.get(km) if km else None
            rng = range(bisect.bisect_left(R.ts, t0 - BUCKET), len(R.ts))
            get_a = (lambda i: ca[0][i] / ca[1][i] if ca[1][i] > 0 else NAN) if ca else (lambda i: NAN)
            get_m = (lambda i: cm[2][i]) if cm else (lambda i: ca[2][i]) if ca else (lambda i: NAN)
            spans = ((R.ts[i], R.ts[i] + BUCKET, i) for i in rng)
        for tb, te, i in spans:
            if tb >= t1:
                break
            a, b = max(tb, t0), min(te, t1)
            if b <= a:
                continue
            va, vm = get_a(i), get_m(i)
            c0 = int((a - t0) / cw)
            c1 = min(ncol - 1, int((b - t0) / cw - 1e-9))
            for col in range(max(0, c0), c1 + 1):
                ov = min(b, t0 + (col + 1) * cw) - max(a, t0 + col * cw)
                if ov <= 0:
                    continue
                cov[col] += ov
                if va == va:
                    sums[col] += va * ov; ws[col] += ov
                if vm == vm and (mxs[col] is None or vm > mxs[col]):
                    mxs[col] = vm
        avgs = [sums[i] / ws[i] if ws[i] > 0 else None for i in range(ncol)]
        res = (avgs, mxs, cov, cw)
        self.cache[key] = res
        return res

    def stats(self, ka, km):
        """Média ponderada e pico do período selecionado."""
        avgs, mxs, cov, cw = self.series(ka, km, 240)
        tot = sum(cov)
        w = [(a, c) for a, c in zip(avgs, cov) if a is not None]
        av = sum(a * c for a, c in w) / sum(c for _, c in w) if w else None
        pk = max((m for m in mxs if m is not None), default=None)
        return av, pk, tot

    def ceiling_minutes(self, k):
        t0, t1, p = self.span()
        h = self.hist
        if self.source(p) == "raw":
            c = h.raw.cols.get(k + "_s")
            if c is None:
                return None
            i0 = bisect.bisect_left(h.raw.ts, t0)
            return sum(v for v in c[i0:] if v == v) / 60
        c = h.roll.cols.get(k + "_s")
        if c is None:
            return None
        i0 = bisect.bisect_left(h.roll.ts, t0 - BUCKET)
        return sum(c[3][i0:]) / 60

    # ---- gráfico ----
    def chart(self, y, x, h, w, ka, km, scale=100.0, unit="%", attr_fn=None, ref=None, axis=True, labels=True,
              lv_key=None):
        """Gráfico de colunas: cheio = média, sombreado = pico, '·' = sem dados.
        Com lv_key, a cor de cada coluna é o pior estado do trecho (não o tamanho do valor)."""
        aw = 7 if labels else 0
        if h <= 0 or w <= aw + 2:
            return None
        ncol = w - aw
        avgs, mxs, cov, cw = self.series(ka, km, ncol)
        lvm = self.series(lv_key, lv_key, ncol)[1] if lv_key else None
        if lv_key:
            def attr_fn(a, m, c):
                lv = lvm[c]
                return self.col_attr[int(lv)] if lv is not None else self.A["neutral"]
        if scale is None:
            top = max([m for m in mxs if m is not None] + [a for a in avgs if a is not None] + [ref or 0, 0])
            scale = max(nice(top * (1.1 if ref else 1)), 1.0)      # escala mínima: 1% / 1 unidade
        if labels:
            lu = "%" if unit == "%" else ""          # outras unidades estão no título do gráfico
            self.put(y, x, "%6s" % fmt_val(scale, lu)[:6], self.A["dim"])
            if h > 2:
                self.put(y + h - 1, x, "%6s" % fmt_val(0, lu)[:6], self.A["dim"])
            if h > 4:
                self.put(y + (h - 1) // 2, x, "%6s" % fmt_val(scale / 2, lu)[:6], self.A["dim"])
        G = self.g
        ref_row = None
        if ref is not None and 0 < ref <= scale:
            ref_row = max(0, h - 1 - int(ref / scale * h))
        for c in range(ncol):
            a, m = avgs[c], mxs[c]
            cx = x + aw + c
            if a is None and m is None:
                if cov[c] <= 0:
                    self.put(y + h - 1, cx, G.gap, self.A["dim"])
                continue
            av = a if a is not None else 0.0
            e = max(0.0, min(1.0, av / scale)) * h * 8
            if av > 0 and e < 1:
                e = 1
            mrow = max(0.0, min(1.0, (m if m is not None else av) / scale)) * h
            if lv_key:
                attr = attr_fn(av, m, c)
            else:
                attr = attr_fn(av, m) if attr_fn else self.pct_attr(100 * av / scale if unit != "%" else av)
            for r in range(h):
                cell = int(min(8, max(0, e - r * 8)))
                yy = y + h - 1 - r
                if G.v[cell] == "_" and r > 0:
                    cell = 0                      # '_' só marca valor baixo na linha de base
                if cell > 0:
                    self.put(yy, cx, G.v[cell], attr)
                elif r < math.ceil(mrow - 1e-9) and m is not None and m > av:
                    pa = attr if lv_key else self.pct_attr(100 * m / scale if unit != "%" else m)
                    self.put(yy, cx, G.peak, pa | (0 if lv_key else self.A["dim"]))
                elif ref_row is not None and yy == y + ref_row:
                    self.put(yy, cx, G.ref, self.A["dim"])
        if axis:
            self.time_axis(y + h, x + aw, ncol)
        return lvm

    def time_axis(self, y, x, ncol):
        t0, t1, p = self.span()
        fmt = "%H:%M" if p <= 86400 else "%d/%m %Hh" if p <= 8 * 86400 else "%d/%m"
        labels = [(0, t0), (ncol // 2, (t0 + t1) / 2), (ncol - 1, t1)]
        for c, t in labels:
            s = time.strftime(fmt, stime(t))
            cx = x + c - (len(s) // 2 if 0 < c < ncol - 1 else (len(s) - 1 if c else 0))
            self.put(y, max(x, cx), s, self.A["dim"])

    def state_strip(self, y, x, w):
        """Faixa com a condição (pior estado) de cada trecho do período."""
        aw = 7
        self.put(y, x, " estado", self.A["dim"])
        ncol = w - aw
        _, mxs, cov, _ = self.series("state", "state", ncol)
        for c in range(ncol):
            if mxs[c] is None:
                self.put(y, x + aw + c, self.g.gap, self.A["dim"])
            else:
                lv = int(mxs[c])
                self.put(y, x + aw + c, self.g.v[8] if lv else self.g.v[2], self.lvl_attr[lv])

    # ---- valores atuais ----
    def poll_live(self):
        if self.mon:
            self.live = self.mon.live
            return
        try:
            mt = os.stat(self.live_file).st_mtime
        except OSError:
            self.live = None
            return
        if mt != self.live_mtime:
            try:
                with open(self.live_file) as f:
                    self.live = json.load(f)
                self.live_mtime = mt
            except (OSError, ValueError):
                pass

    def cur(self):
        """Valores atuais: amostra ao vivo (se recente) ou a última janela gravada."""
        lv = self.live
        if lv and time.time() - lv.get("ts", 0) <= 3 * lv.get("sample", 5) + 2:
            return "live", lv
        return "data", self.hist.last

    # ---- telas ----
    def draw(self):
        self.draw_base()
        self.scr.noutrefresh()
        curses.doupdate()

    def draw_base(self):
        self.scr.erase()
        self.H, self.W = self.scr.getmaxyx()
        if self.H < 12 or self.W < 50:
            self.draw_tiny()
        elif self.loading:
            self.title_bar()
            pct = 100 * self.hist.pos / max(1, self.hist.size)
            self.put(3, 2, "Carregando histórico... %.0f%% (%d janelas lidas)" % (pct, self.hist.rows), self.A["bold"])
            self.footer()
        elif self.help:
            y = self.title_bar() + 1
            for i, line in enumerate(HELP.replace("═", self.g.mark[2]).splitlines()):
                self.put(y + i, 2, line, self.A["bold"] if line[:1].isupper() and line.isupper() else self.A["text"])
            self.footer()
        elif self.tech:
            y = self.title_bar()
            y = self.status_line(y)
            y = self.tech_tabs(y)
            if self.hist.last is None and not self.cur()[1]:
                self.put(y + 1, 2, "Ainda sem medições no relatório.", self.A["bold"])
            else:
                self.TECH[self.tab % len(self.TECH)][1](self, y, self.H - 1)
            self.footer()
        else:
            self.view_simple()
            self.footer()

    def title_bar(self):
        h, A, W = self.hist, self.A, self.W
        host = h.session.get("host") or (self.live or {}).get("host") or "?"
        company = h.session.get("company") or h.export_company or (self.ident.company if self.ident else "")
        company = "" if company == "?" else company
        # nome amigável: o do relatório; o da instalação só se o relatório for desta empresa (não de outro cliente)
        name = h.session.get("name") or (self.ident.name if self.ident and company in ("", self.ident.company) else "")
        if self.ident and getattr(self.ident, "install_id", "") and h.session.get("install_id") == self.ident.install_id:
            # relatório desta instalação: os nomes atuais (renome pela central vale já, sem esperar o próximo SESSION)
            company, name = self.ident.company or company, self.ident.name or name
        if name or company:
            x = self.puts(0, 2, [("SERVER MONITOR " + VERSION + "  ", A["dim"]), (name or company, A["bold"]), ("  ·  " + host, A["text"])])
        else:
            x = self.puts(0, 2, [("SERVER MONITOR " + VERSION + "  ", A["dim"]), (host.upper(), A["bold"])])
            if self.ident and W >= 110:
                x = self.put(0, x + 2, "(empresa não configurada: --empresa)", A["dim"])
        right = time.strftime("%d/%m %H:%M", stime())
        tzl = tz_label(DISPLAY_TZ[0])
        if tzl:
            name = h.session.get("tz", "")
            right += " " + tzl + (" (%s)" % name.split("/")[-1].replace("_", " ") if name and name != "NA" and W >= 130 else "")
        if not self.mon and W >= 90:
            right = "somente visualização · " + right
        cloud, cattr = self.cloud_text()
        fits = bool(cloud) and W - len(right) - len(cloud) - 6 > x
        if fits:
            right = cloud + "   " + right
        if W - len(right) - 2 > x + 1:
            self.put(0, W - len(right) - 2, right, A["dim"])
            if fits:
                self.put(0, W - len(right) - 2, cloud, cattr)
        if self.paused:
            t = " PAUSADO (a coleta continua) "
            self.put(0, max(0, (W - len(t)) // 2), t, A["warn"] | curses.A_REVERSE)
        if self.mon and self.mon.error:
            self.put(1, 2, "erro na coleta: " + self.mon.error, A["crit"])
            return 2
        return 1

    def cloud_text(self):
        """Estado discreto do envio para a nuvem (texto, atributo)."""
        A = self.A
        txt, until = self.flash[0], self.flash[2]
        if txt and time.time() < until:
            return txt, self.flash[1]
        if self.mon and self.mon.retention_note:
            return self.mon.retention_note, A["warn"]
        upd = self.mon.updater if self.mon else None
        if upd is not None and (upd.version or upd.alert):
            if upd.reason:                            # reinício sem versão nova (coleta alterada pela central)
                return upd.reason.lower() + "; reiniciando...", A["warn"]
            return ("atualizando para a versão %s..." % upd.version) if upd.version else upd.alert, A["warn"]
        if not self.sync:
            return "", 0
        if time.time() - self.cloud_checked > 2:         # lê o estado no máximo a cada 2 s
            self.cloud_checked, self.cloud_cache = time.time(), self.sync.summary()
        txt, kind = self.cloud_cache
        return txt, A["warn"] if kind == "erro" else A["dim"]

    def db_text(self):
        """Linha do acesso ao banco: do agente em memória (coletor) ou do arquivo em RAM (--view), a cada 2 s."""
        if time.time() - self.db_checked > 2:
            self.db_checked = time.time()
            db = getattr(self.mon, "db", None)
            if db is not None:
                self.db_cache = dict(db.panel(), last_req_at=db.last_req_at)
            elif self.mon is None:
                self.db_cache = read_json_owned(db_panel_file(self.hist.path)) or {}
            else:
                self.db_cache = {}
        return db_panel_text(self.db_cache)

    # ---- chave do catálogo (tecla k) ----
    def catkey_path(self):
        db = getattr(self.mon, "db", None)
        if db is not None:
            return db.key_path
        return os.path.join(os.path.dirname(os.path.abspath(self.hist.path)), CATKEY_FILE)

    def modal(self, lines, attr):
        """Desenha o painel e, por cima, uma caixa com as linhas dadas (entrada da tecla k)."""
        self.draw_base()
        H, W = self.H, self.W
        w = min(W - 2, max(len(t) for t in lines) + 4)
        x, y = max(0, (W - w) // 2), max(0, (H - len(lines) - 2) // 2)
        self.put(y, x, " " * w, attr | curses.A_REVERSE)
        for i, t in enumerate(lines):
            self.put(y + 1 + i, x, ("  " + t).ljust(w)[:w], attr | curses.A_REVERSE)
        self.put(y + 1 + len(lines), x, " " * w, attr | curses.A_REVERSE)
        self.scr.noutrefresh()
        curses.doupdate()

    def modal_key(self):
        """Próxima tecla da caixa; None = desistiu (terminal caiu ou PROMPT_IDLE s sem tecla)."""
        start = last_tty = time.time()
        while True:
            ch = self.scr.getch()
            if ch != -1 and ch != curses.KEY_RESIZE:
                return ch
            now = time.time()
            if now - start > PROMPT_IDLE:
                return None
            if now - last_tty > 5:
                last_tty = now
                if not self.tty_alive():
                    return None

    def read_secret(self, title):
        """Linha digitada sem eco (cada caractere vira *); só ASCII imprimível. None = cancelado (Esc)."""
        buf = []
        while True:
            self.modal([title, "", "> " + "*" * min(len(buf), 40) + "_   (%d caracteres)" % len(buf), "",
                        "Enter grava   Esc cancela   Backspace apaga"], self.A["bold"])
            ch = self.modal_key()
            if ch is None or ch == 27:
                return None
            if ch in (10, 13, curses.KEY_ENTER):
                return "".join(buf)
            if ch in (8, 127, curses.KEY_BACKSPACE):
                if buf:
                    buf.pop()
            elif 32 <= ch < 127 and len(buf) < 256:
                buf.append(chr(ch))

    def catkey_prompt(self):
        """Tecla k: pede a chave do catálogo dentro do painel e grava em server_monitor.catkey (600).
        A chave nunca é desenhada nem registrada: só a contagem de caracteres aparece."""
        A = self.A
        self.db_checked = 0
        self.db_text()
        if not self.db_cache.get("text"):
            self.flash = ("acesso ao banco não configurado pela central", A["warn"], time.time() + 6)
            return
        path = self.catkey_path()
        if read_catkey(path) is not None:
            self.modal(["Este servidor já tem a chave do catálogo.", "", "Trocar a chave? (s = sim, outra tecla = não)"],
                       A["warn"])
            ch = self.modal_key()
            if ch not in (ord("s"), ord("S")):
                self.flash = ("chave do catálogo mantida", A["dim"], time.time() + 4)
                return
        s = self.read_secret("Chave do catálogo: 64 caracteres hexadecimais (0-9, a-f)")
        if s is None or not s.strip():
            self.flash = ("chave do catálogo não alterada", A["dim"], time.time() + 4)
            return
        k = parse_catkey(s)
        if k is None:
            self.flash = ("chave inválida: são 64 caracteres de 0-9 e a-f (tecle k de novo)", A["crit"],
                          time.time() + 8)
            return
        try:
            write_private(path, k.hex() + "\n")
        except OSError as e:
            self.flash = ("não consegui gravar a chave: %s" % (e.strerror or type(e).__name__), A["crit"],
                          time.time() + 8)
            return
        db = getattr(self.mon, "db", None)
        if db is not None:
            db.key_changed()                              # coletor: relê já; no --view, o coletor percebe em DB_KEY_CHECK s
        self.db_checked = 0
        self.flash = ("chave do catálogo salva (permissão 600)", A["ok"] | curses.A_BOLD, time.time() + 8)

    def cloud_sync(self):
        A = self.A
        if not self.sync:
            self.flash = ("nuvem não configurada (--cloud-setup)", A["warn"], time.time() + 6)
        elif not self.sync.manual():
            self.flash = ("envio já em andamento", A["dim"], time.time() + 4)
        else:
            self.flash = ("enviando para a nuvem...", A["dim"], time.time() + 3)
            self.cloud_checked = 0

    def freshness(self):
        """Texto curto sobre a idade da medição mostrada."""
        h = self.hist
        src, cur = self.cur()
        if src == "live":
            return "medido há %.0f s" % max(0, time.time() - cur["ts"])
        if h.last is not None:
            return "última janela %s" % fmt_ago(time.time() - h.last["_ts"])
        return ""

    def status_line(self, y):
        """Status em uma linha (modo técnico)."""
        A = self.A
        lv, res, msg, _ = self.status()
        lab = "SEM DADOS" if lv is None else LEVEL_NAMES[lv]
        x = self.puts(y, 2, [("STATUS ", A["dim"]), (" %s " % lab, self.status_attr(lv))])
        if res:
            x = self.puts(y, x + 2, [(dict(RESOURCES)[res] + ": ", self.lbl_attr[lv]), (msg, A["text"])])
        else:
            x = self.put(y, x + 2, msg, A["dim"])
        f = self.freshness()
        self.put(y, max(x + 2, self.W - len(f) - 2), f, A["dim"])
        return y + 1

    def status_attr(self, lv):
        if lv is None:
            return self.A["nodata"] | curses.A_REVERSE
        return [self.A["ok"] | curses.A_BOLD, self.A["warn"] | curses.A_BOLD | curses.A_REVERSE,
                self.A["crit"] | curses.A_REVERSE][lv]

    def tech_tabs(self, y):
        A = self.A
        x = self.put(y, 2, "DETALHES TÉCNICOS  ", A["bold"])
        for i, (name, _) in enumerate(self.TECH):
            x = self.put(y, x, " %s " % name, (A["title"] | curses.A_REVERSE) if i == self.tab % len(self.TECH) else A["dim"])
        hint = "Tab/setas trocam · d volta"
        self.put(y, max(x + 2, self.W - len(hint) - 2), hint, A["dim"])
        return y + 1

    def footer(self):
        A = self.A
        y = self.H - 1
        x = 2
        narrow = self.W < 100
        for i, (k, name, _) in enumerate(PERIODS):
            x = self.put(y, x, " %s %s " % (k, name), (A["bold"] | curses.A_REVERSE) if self.period == i else A["dim"])
        if self.tech:
            keys = "d visão simples   n disco   ? ajuda   q sair" if not narrow else "d simples  ? ajuda  q"
        else:
            keys = "d detalhes técnicos   ? ajuda   p pausa   q sair" if not narrow else "d detalhes  ? ajuda  q"
        if x + 2 + len(keys) > self.W - 2:
            keys = "? ajuda  q" if x + 12 <= self.W - 2 else ""
        if self.quit_armed and time.time() - self.quit_armed < 3:
            keys = " q de novo encerra a COLETA e sai "
            self.put(y, max(x + 2, self.W - len(keys) - 2), keys, A["crit"] | curses.A_REVERSE)
        else:
            self.put(y, max(x + 2, self.W - len(keys) - 2), keys, A["dim"])

    # ---- diagnóstico atual e eventos do período ----
    def status(self):
        """(nível ou None = sem dados, recurso principal, frase, diagnóstico) da última janela."""
        h, now = self.hist, time.time()
        if h.last is None:
            if self.cur()[0] == "live":
                return None, None, "Coletando a primeira medição (~%d s)." % (first_samples(h.sample) * h.sample), None
            return None, None, "O relatório ainda não tem medições.", None
        dg = diagnose(h.last, h.ncpu, h.disks, msgs=True)
        age = now - h.last["_ts"]
        if age > h.expected_window(now) + 2 * h.sample + 15 and self.cur()[0] != "live":
            why = "Monitor parado" if h.stopped_at is not None else "Sem medições recentes"
            return None, None, "%s: última medição %s (%s)." % (why, fmt_ago(age), fmt_when(h.last["_ts"])), dg
        known = [(dg[k][0], k) for k, _ in RESOURCES if dg[k][0] is not None]
        if not known:
            return None, None, "Medições sem dados suficientes para avaliar.", dg
        lv = max(l for l, _ in known)
        if lv == 0:
            return 0, None, "Servidor operando normalmente.", dg
        # empate: o recurso com o problema em andamento mais longo
        ongoing = {e["res"]: e["end"] - e["start"] for e in self.events() if e["ongoing"]}
        # espaço cheio costuma durar dias: no empate, o problema de desempenho vem antes
        res = max((k for l, k in known if l == lv), key=lambda k: (k != "space", ongoing.get(k, 0)))
        return lv, res, dg[res][1], dg

    def events(self):
        """Períodos contínuos com o recurso em ATENÇÃO ou CRÍTICO dentro do período exibido."""
        t0, t1, p = self.span()
        key = (int(t0 // 30), self.period, self.hist.version)
        if key == self.ev_key:
            return self.ev
        h = self.hist
        ev = []
        join = max(300.0, min(p / 100.0, 3600.0))   # episódios separados por menos que isso viram um só
        everything = PERIODS[self.period][2] is None
        if self.source(p) == "raw":
            ts, win = h.raw.ts, h.raw.win
            i0 = bisect.bisect_left(ts, t0)
            for res, _ in RESOURCES:
                L = h.raw.cols.get("lv_" + res)
                if L is None:
                    continue
                cur = None
                for i in range(i0, len(ts)):
                    lv = L[i]
                    if lv != lv or lv < 1:
                        continue
                    tb, te = max(ts[i] - win[i], t0), ts[i]
                    if cur is not None and tb - cur["end"] <= max(join, 2 * win[i]):
                        cur["end"] = te
                        cur["crit"] += (te - tb) if lv >= 2 else 0
                        if lv > cur["lv"]:
                            cur["lv"], cur["worst"] = lv, i
                        cur["coarse"] = cur["coarse"] or win[i] >= 120
                    else:
                        cur = {"res": res, "start": tb, "end": te, "lv": lv, "worst": i, "coarse": win[i] >= 120, "hour": False,
                               "clipped": tb <= t0 + 1 and not everything, "crit": (te - tb) if lv >= 2 else 0}
                        ev.append(cur)
        else:
            R = h.roll
            i0 = bisect.bisect_left(R.ts, t0 - BUCKET)
            for res, _ in RESOURCES:
                c = R.cols.get("lv_" + res)
                if c is None:
                    continue
                cur = None
                for i in range(i0, len(R.ts)):
                    lv = c[2][i]
                    if lv != lv or lv < 1:
                        continue
                    tb, te = R.ts[i], R.ts[i] + BUCKET
                    if cur is not None and tb - cur["end"] <= join:
                        cur["end"] = te
                        cur["lv"] = max(cur["lv"], lv)
                        cur["crit"] += BUCKET if lv >= 2 else 0
                    else:
                        cur = {"res": res, "start": max(tb, t0), "end": te, "lv": lv, "worst": None, "coarse": True, "hour": True,
                               "clipped": tb < t0 and not everything, "crit": BUCKET if lv >= 2 else 0}
                        ev.append(cur)
        last = h.last_ts
        now = time.time()
        fresh = last is not None and (self.cur()[0] == "live" or now - last <= h.expected_window(now) + 2 * h.sample + 15)
        for e in ev:
            e["ongoing"] = fresh and last is not None and e["end"] >= last - 1 and h.stopped_at is None
        self.ev_key, self.ev = key, ev
        return ev

    def event_msg(self, e):
        """Frase de diagnóstico da pior janela do evento."""
        if e["worst"] is None:
            return "%s no pior momento de cada hora (detalhe só dos últimos 8 dias)." % LEVEL_NAMES[int(e["lv"])].capitalize()
        i = e["worst"]
        h = self.hist
        row = {k: c[i] for k, c in h.raw.cols.items()}
        fi = row.get("fs_worst_id", NAN)
        if e["res"] == "space" and fi == fi:     # o filesystem que estava pior naquela janela
            row["_fs"] = [{"mount": h.fs_names[int(fi)], "used_pct": row["fs_worst_used"],
                           "free_bytes": row["fs_worst_free"], "total_bytes": row["fs_worst_total"]}]
        d = diagnose(row, h.ncpu, h.disks, msgs=True)[e["res"]]
        return d[1]

    def event_span(self, e, short=False):
        """'14:20 até 14:38 (18 min)'; '≈' quando a resolução não permite precisão."""
        a, b = stime(e["start"]), stime(e["end"])
        ta = fmt_when(e["start"], short=True)
        tb = time.strftime("%H:%M", b) if a[:3] == b[:3] else fmt_when(e["end"], short=True)
        if e["hour"]:
            ta, tb = ta[:-3] + "h", tb[:-3] + "h"
        ap = "≈" if e["coarse"] and self.g.dot == "●" else ("~" if e["coarse"] else "")
        if short:
            return "%s%s–%s  %s%s" % (ap, ta, tb, "+" if e.get("clipped") else ap, fmt_span(e["end"] - e["start"]))
        s = "%s%s%s até %s (%s%s)" % (ap, ta, " (ou antes)" if e.get("clipped") else "", tb,
                                      "mais de " if e.get("clipped") else ap, fmt_span(e["end"] - e["start"]))
        dur = e["end"] - e["start"]
        if e["lv"] >= 2 and e["crit"] < 0.9 * dur:
            s = s[:-1] + "; crítico durante %s%s)" % (ap, fmt_span(e["crit"]))
        if e["ongoing"]:
            s += ", em andamento"
        return s

    # ---- visão simples ----
    def view_simple(self):
        A, W, H, G = self.A, self.W, self.H, self.g
        wide = W >= 150
        x0 = 2
        cw = min(W - 4, 110) if not wide else min(W - 70, 120)
        y = self.title_bar() + (1 if H >= 30 else 0)
        lv, res, msg, dg = self.status()
        ev = self.events()
        # ---- A. estado geral ----
        lab = "SEM DADOS" if lv is None else LEVEL_NAMES[lv]
        self.puts(y, x0, [("STATUS  ", A["dim"]), (" %s %s " % (G.dot if lv else "", lab) if lv else " %s " % lab, self.status_attr(lv))])
        f = self.freshness()
        self.put(y, x0 + cw - len(f), f, A["dim"])
        if res:
            self.puts(y + 1, x0, [("Principal problema: ", A["text"]), (dict(RESOURCES)[res], self.lbl_attr[lv]),
                                  (" — " + headline(msg), A["text"])])
            cur = [e for e in ev if e["res"] == res and e["ongoing"]]
            if cur:
                e = cur[-1]
                when = "Começou às %s (há %s) e continua." % (fmt_when(e["start"], short=True), fmt_span(time.time() - e["start"]))
                if e["coarse"]:
                    when += " Horário aproximado: janelas de 5 min."
            else:
                when = "Detectado na última medição."
            self.put(y + 2, x0, when, A["dim"])
        else:
            self.put(y + 1, x0, msg, A["text"] if lv == 0 else A["dim"])
            past = [e for e in ev if not e["ongoing"]]
            if past:
                e = max(past, key=lambda e: e["end"])
                self.put(y + 2, x0, "Último problema: %s, %s." % (RES_NAME[e["res"]], self.event_span(e)), A["dim"])
            else:
                self.put(y + 2, x0, "Nenhum problema registrado: %s." % PERIOD_TITLES[self.period].lower(), A["dim"])
        dbt, dbk = self.db_text()
        if dbt:                                   # acesso ao banco pela central (só quando configurado)
            self.put(y + 3, x0, dbt[:cw], A["warn"] if dbk in ("erro", "aviso") else A["dim"])
        y += 4
        # ---- B. um bloco por recurso (ESPAÇO só se o relatório mede filesystems) ----
        res_list = self.res_list()
        nr = len(res_list)
        bottom = H - 2
        summ = 0 if wide else 6
        per = 5                                   # borda, barra, marcação de eventos, frase, borda
        avail = bottom - y - 1                    # -1: eixo de tempo
        ch = (avail - summ - nr * per) // nr
        if ch < 2 and summ:
            summ = 0
            ch = (avail - nr * per) // nr
        ch = max(0, min(ch, 8))
        if ch == 0 and not wide and avail + 1 - nr * (per - 1) >= 4:
            summ = 4                              # sem espaço para gráficos: usa a sobra para o resumo
        if avail + 1 < nr * (per - 1):
            ch = -1                               # tela muito baixa: caixas de 3 linhas, valor na borda
        v = self.cur_vals()
        dg = dg or {}
        for k, name in res_list:
            y = self.res_block(y, x0, cw, ch, k, name, dg.get(k), v)
        if ch > 0:
            self.time_axis(y, x0 + 2, cw - 4)
            y += 1
        # ---- C. resumo do período ----
        if wide:
            self.summary(self.title_bar() + (1 if H >= 30 else 0), x0 + cw + 6, W - (x0 + cw + 6) - 2, bottom, ev, events_list=True)
        elif summ:
            self.summary(y + (1 if bottom - y > 5 else 0), x0, cw, bottom, ev)

    def res_list(self):
        """Recursos mostrados: ESPAÇO só aparece quando o relatório tem ocupação de filesystems
        (relatórios anteriores à v2.3 mantêm o layout de três blocos)."""
        return [r for r in RESOURCES if r[0] != "space" or self.hist.has_space]

    def res_block(self, y, x, w, ch, k, name, d, v):
        A, G = self.A, self.g
        lv = d[0] if d else None
        msg = d[1] if d else "Sem dados."
        dk = (d[2] if d and len(d) > 2 else None) or (self.hist.disks[0] if self.hist.disks else None)
        lab = "SEM DADOS" if lv is None else LEVEL_NAMES[lv]
        border = A["dim"] if not lv else self.col_attr[lv]     # moldura só chama atenção se houver problema
        y0, ox, ow = y, x, w
        if k == "cpu":
            val, txt = v.get("cpu"), "em uso"
        elif k == "mem":
            val, txt = v.get("mem"), "em uso"
        elif k == "space":
            f = (self.hist.last or {}).get("_fs_worst")
            val, txt = (f["used_pct"] if f else None), "ocupado"
        else:
            val, txt = (v.get(dk) or {}).get("u"), "do tempo ocupado"
        title = name + ("  " + dk if k == "disk" and dk else "")
        if k == "space" and f:
            title += "  %s · %s livres" % (f["mount"], fmt_bytes(f["free_bytes"]))
        if ch < 0:                                # caixa mínima: valor no título, só a frase dentro
            title += " · %s %s" % (fmt_val(val, "%") if val is not None else "NA", txt)
        self.box_top(y, x, w, title, lab, border=border,
                     title_attr=A["bold"], right_attr=A["dim"] if lv is None else self.lbl_attr[lv])
        x, w = x + 2, w - 4
        if ch < 0:
            self.xmax = x + w
            self.put(y + 1, x, ("%s %s" % (G.warn, msg)) if lv else msg, self.lbl_attr[lv] if lv else A["dim"])
            return self.box_close(y0, y + 2, ox, ow, border)
        bw = w - 24
        battr = A["neutral"] if not lv else self.col_attr[lv]
        self.xmax = x + w
        self.bar(y + 1, x, bw, val, attr=battr)
        self.put(y + 1, x + bw + 2, "%4s %s" % (fmt_val(val, "%") if val is not None else "NA", txt), A["text"])
        yy = y + 2
        if ch:
            keys = {"cpu": ("cpu_avg", "cpu_max"), "mem": ("mem_avg", "mem_max"),
                    "disk": ((dk or "?") + ".util_avg", (dk or "?") + ".util_max"),
                    "space": ("fs_worst_used", "fs_worst_used")}[k]
            lvm = self.chart(yy, x, ch, w, keys[0], keys[1], labels=False, axis=False, lv_key="lv_" + k) or []
            for c, l in enumerate(lvm):
                if l is not None and l >= 1:
                    self.put(yy + ch, x + c, G.mark[int(l)], self.col_attr[int(l)])
            yy += ch + 1
        self.xmax = x + w
        self.put(yy, x, ("%s %s" % (G.warn, msg)) if lv else msg, self.lbl_attr[lv] if lv else A["dim"])
        return self.box_close(y0, yy + 1, ox, ow, border)

    def server_block(self, y, x, w, bottom):
        """Hardware e capacidade medida no benchmark (o mais recente do relatório)."""
        A, h = self.A, self.hist
        hw, b = h.hw, h.last_bench

        def num(k):
            v = b.get(k, "").split(" ")[0]
            try:
                return float(v)
            except ValueError:
                return None

        def n0(v, unit=""):
            return "?" if v is None else ("{:,.0f}".format(v).replace(",", ".") + unit)

        when = ""
        if h.last_bench_when:
            try:
                when = " (medido %s)" % fmt_when(datetime.datetime.fromisoformat(h.last_bench_when).timestamp())
            except ValueError:
                pass
        self.put(y, x, "SERVIDOR · CAPACIDADE" + when, A["bold"])
        y += 1
        rows = []
        cpu = "%s vCPUs" % (hw.get("cpu_logical") or h.ncpu)
        if hw.get("cpu_model") and hw["cpu_model"] != "?":
            cpu += " · " + " ".join(hw["cpu_model"].replace("(R)", "").replace("(TM)", "").replace("Processor", "")
                                    .replace(" CPU ", " ").split())
        if hw.get("virtualization") not in (None, "", "none", "desconhecido"):
            cpu += " · VM " + hw["virtualization"]
        rows.append(("CPU", cpu, A["text"]))
        c1, ca, sx = num("cpu_1core_sha256_MBs"), num("cpu_all_cores_sha256_MBs"), num("cpu_scaling_x")
        if c1 is not None:
            txt = "1 núcleo %s MB/s · todos %s MB/s" % (n0(c1), n0(ca))
            rows.append(("", txt, A["dim"]))
            if sx is not None:
                rows.append(("", "rende como %.1f núcleos de %s" % (sx, hw.get("cpu_logical") or h.ncpu), A["dim"]))
        mem = "%s GB de RAM · swap %s GB" % (hw.get("mem_total_GB", "?"), hw.get("swap_total_GB", "?"))
        rows.append(("MEMÓRIA", mem, A["text"]))
        if num("mem_write_bw_GBs") is not None:
            rows.append(("", "escrita ~%.1f GB/s (1 thread)" % num("mem_write_bw_GBs"), A["dim"]))
        sw, sr = num("dir_seq_write_MBs"), num("dir_seq_read_MBs")
        iw, ir = num("dir_rand_write_4k_iops"), num("dir_rand_read_4k_iops")
        cached = False
        ref_iops = None
        for d in h.disks:
            info = h.disk_info.get(d, "")
            size = info.split(",")[0] if info else "?"
            dr, dio = num("disk.%s.seq_read_MBs" % d), num("disk.%s.rand_read_4k_iops" % d)
            ref_iops = ref_iops or dio
            rows.append(("DISCO" if d == h.disks[0] else "", "%s · %s · %s" % (d, size, self.disk_type(d, long=True)), A["text"]))
            if dio:
                rows.append(("", "%s IOPS aleatórias no disco inteiro: %s" % (n0(dio), disk_perf(dio)), A["text"]))
            if dr is not None:
                # leitura muito acima da gravação direta medida = veio da memória do host, não do disco
                star = bool(sw) and dr > 2.5 * sw
                cached = cached or star
                rows.append(("", "leitura direta %s MB/s%s" % (n0(dr), " *" if star else ""), A["dim"]))
        if sw is not None or sr is not None:
            star = bool(sw) and sr is not None and sr > 2.5 * sw
            cached = cached or star
            rows.append(("", "sequencial: grava %s · lê %s MB/s%s" % (n0(sw), n0(sr), " *" if star else ""), A["dim"]))
        if iw is not None or ir is not None:
            star = ref_iops is not None and ir is not None and ir > 5 * ref_iops
            cached = cached or star
            rows.append(("", "4K num arquivo: lê %s · grava %s IOPS%s" % (n0(ir), n0(iw), " *" if star else ""), A["dim"]))
        if cached:
            rows.append(("", "* provável cache do host (memória), não o disco", A["dim"]))
        if not b:
            rows.append(("", "capacidade não medida (rode sem --no-bench)", A["dim"]))
        for lab, txt, at in rows:
            if y >= bottom:
                break
            self.put(y, x, "%-9s" % lab, A["text"])
            y = self.wrap(y, x + 9, w - 9, txt, at, bottom)
        return y + 1

    def disk_type(self, d, long=False):
        """Tipo do disco. Em VM o tipo informado pelo kernel costuma ser falso (disco virtual
        'rotacional' em storage flash); o desempenho medido diz mais."""
        h = self.hist
        kind = disk_kind(h.disk_info.get(d, ""))
        virt = h.hw.get("virtualization") not in (None, "", "none", "desconhecido")
        iops = None
        try:
            iops = float(h.last_bench.get("disk.%s.rand_read_4k_iops" % d, "").split(" ")[0])
        except ValueError:
            pass
        if not virt:
            return kind
        if not long:
            return "flash" if iops and iops >= 5000 else "lento" if iops and iops < 1000 else "VM"
        return "VM informa %s" % kind

    def summary(self, y, x, w, bottom, ev, events_list=False):
        A = self.A
        if y >= bottom:
            return
        self.xmax = x + w
        if events_list:
            y = self.server_block(y, x, w, bottom)
        t0, t1, p = self.span()
        self.put(y, x, PERIOD_TITLES[self.period], A["bold"])
        y += 1
        for k, name in self.res_list():
            es = [e for e in ev if e["res"] == k]
            nc = sum(1 for e in es if e["lv"] >= 2)
            nw = len(es) - nc
            if not es:
                txt, at = "nenhum problema", A["dim"]
            else:
                parts = []
                if nc:
                    parts.append("%d %s" % (nc, "período crítico" if nc == 1 else "períodos críticos"))
                if nw:
                    parts.append("%d de atenção" % nw)
                txt = ", ".join(parts) + " · %s no total" % fmt_span(sum(e["end"] - e["start"] for e in es))
                at = self.lbl_attr[2 if nc else 1]
            self.put(y, x, "%-9s" % name, A["text"])
            y = self.wrap(y, x + 9, w - 9, txt, at, bottom)
        if ev and y + 1 < bottom:
            e = max(ev, key=lambda e: (e["lv"], e["end"] - e["start"]))
            y += 1
            x1 = self.puts(y, x, [("Maior problema: ", A["text"]), (RES_NAME[e["res"]], self.lbl_attr[int(e["lv"])])])
            y = self.wrap(y, x1, w, " — " + self.event_span(e), A["text"], bottom, cont_x=x + 2, xmax=x + w)
            y = self.wrap(y, x + 2, w - 2, self.event_msg(e), A["dim"], bottom)
        cov = self.stats("cpu_avg", "cpu_max")[2]
        first = self.hist.first_ts
        if first is not None and first > t0 + 60 and y < bottom:
            # o histórico começa dentro do período: não é falha, o monitor só começou depois
            y = self.wrap(y, x, w, "Histórico começa %s (%s de medições)." % (
                fmt_when(first), fmt_span(cov)), A["dim"], bottom)
            start = first
        else:
            start = t0
        last = self.hist.last_ts
        known = (min(t1, last) if last is not None else t1) - start   # a janela em andamento não é lacuna
        if known > 120 and cov < 0.9 * known and y < bottom:
            y = self.wrap(y, x, w, "Monitor parado em %.0f%% desse tempo (trechos com ·)." % (100 - 100 * cov / known),
                          A["dim"], bottom)
        if events_list and ev and y + 2 < bottom:
            y += 1
            self.put(y, x, "EVENTOS (mais recentes primeiro)", A["bold"])
            y += 1
            for e in sorted(ev, key=lambda e: -e["start"]):
                if y >= bottom:
                    break
                self.puts(y, x, [(self.g.mark[int(e["lv"])] * 2 + " ", self.col_attr[int(e["lv"])]),
                                 ("%-8s" % RES_NAME[e["res"]], A["text"]), (self.event_span(e, short=True), A["dim"]),
                                 ("  em andamento" if e["ongoing"] else "", self.lbl_attr[int(e["lv"])])])
                y += 1
        self.xmax = None

    def view_hw(self, y, bottom):
        """Hardware, capacidade medida e glossário das métricas técnicas."""
        h, A = self.hist, self.A
        col = max(40, self.W // 2 - 4)
        yy = y + 1
        self.put(yy, 2, "HARDWARE (início da sessão)", A["bold"]); yy += 1
        for k, val in h.hw.items():
            if yy >= bottom:
                break
            self.puts(yy, 2, [("%-22s" % k, A["dim"]), (val, A["text"])]); yy += 1
        yy += 1
        if h.last_bench and yy < bottom:
            when = ""
            try:
                when = " (medido %s)" % fmt_when(datetime.datetime.fromisoformat(h.last_bench_when).timestamp())
            except (TypeError, ValueError):
                pass
            self.put(yy, 2, "MINI-BENCHMARK" + when, A["bold"]); yy += 1
            for k, val in h.last_bench.items():
                if yy >= bottom:
                    break
                self.puts(yy, 2, [("%-28s" % k, A["dim"]), (val, A["text"])]); yy += 1
        x2 = 2 + col + 2 if self.W >= 2 * col + 6 else None
        yy2 = y + 1 if x2 else yy + 1
        x2 = x2 or 2
        for line in GLOSSARY.splitlines():
            if yy2 >= bottom:
                break
            self.put(yy2, x2, line, A["bold"] if line.isupper() else A["text"])
            yy2 += 1

    TECH = None   # preenchido após a classe

    def per_label(self):
        return PERIODS[self.period][1]

    def period_stats(self, ka, km, unit="%", hi_key=None):
        av, pk, cov = self.stats(ka, km)
        _, _, p = self.span()
        s = "%s: méd %s · pico %s" % (self.per_label(), fmt_val(av, unit), fmt_val(pk, unit))
        if hi_key:
            m = self.ceiling_minutes(hi_key)
            if m is not None:
                s += " · no teto %s" % fmt_min(m)
        if cov < 0.9 * p:
            s += " · cobertura %.0f%%" % (100 * cov / p)
        return s

    def cur_vals(self):
        """Valores atuais normalizados (ao vivo ou da última janela)."""
        src, c = self.cur()
        h = self.hist
        v = {"src": src}
        if src == "live":
            s, x = c["s"], c["x"]
            v.update(cpu=s["cpu"], rq=s["rq"], pc=s["pc"], st=s["st"], iow=s["iow"], hot=s["hot"], mem=s["mem"],
                     swp=s["swp"], swin=s["swin"], swout=s["swout"], majf=s["majf"], pms=s["pms"], pmf=s["pmf"],
                     pis=s["pis"], pif=s["pif"], percpu=x.get("percpu"), load=x.get("load"),
                     mt=x["mem_total"] / 1048576, ma=x["mem_avail"] / 1048576, mc=x["mem_cache"] / 1048576,
                     swt=x["swap_total"] / 1048576, swf=x["swap_free"] / 1048576)
            for d in h.disks:
                if d + ".u" in s:
                    v[d] = dict(u=s[d + ".u"], r=s[d + ".r"], w=s[d + ".w"], ri=s.get(d + ".ri"), wi=s.get(d + ".wi"),
                                io=s[d + ".io"], raw=s.get(d + ".raw"), waw=s.get(d + ".waw"), aw=s[d + ".aw"], qd=s[d + ".qd"])
        elif c:
            g = lambda k: c.get(k)
            try:
                mt = float(h.hw.get("mem_total_GB", "nan"))
                swt = float(h.hw.get("swap_total_GB", "nan"))
            except ValueError:
                mt = swt = NAN
            mem = g("mem_avg")
            v.update(cpu=g("cpu_avg"), rq=g("rq_avg"), pc=g("psi_cpu"), st=g("st_avg"), iow=g("iow_avg"), hot=g("hot_max"),
                     mem=mem, swp=g("swap"), swin=g("swin"), swout=g("swout"), majf=g("majf"), pms=g("psi_mem"),
                     pmf=g("psi_mem_full"), pis=g("psi_io"), pif=g("psi_io_full"), percpu=None,
                     load=[g("load1"), g("load5"), g("load15")], mt=mt,
                     ma=mt * (1 - mem / 100) if mem is not None else None, mc=None,
                     swt=swt, swf=swt * (1 - (g("swap") or 0) / 100) if swt == swt else None)
            for d in h.disks:
                v[d] = dict(u=g(d + ".util_avg"), r=g(d + ".rMBs"), w=g(d + ".wMBs"), ri=g(d + ".riops"), wi=g(d + ".wiops"),
                            io=g(d + ".iops_avg"), raw=g(d + ".r_await"), waw=g(d + ".w_await"), aw=g(d + ".await"), qd=g(d + ".qd_avg"))
        return v

    def cpu_tag(self, v):
        cpu, rq, pc = v.get("cpu"), v.get("rq") or 0, v.get("pc") or 0
        n = self.hist.ncpu
        if cpu is None:
            return "", 0
        if rq > n or pc >= 10:
            return "PRESSIONADA: processos esperando CPU", self.A["crit"]
        if cpu >= 90:
            return "ocupada, sem fila (atendendo a demanda)", self.A["warn"]
        return "", 0

    def disk_list(self):
        return self.hist.disks or ["?"]

    def view_general(self, y, bottom):
        v = self.cur_vals()
        W = self.W
        disks = self.disk_list()
        d = disks[self.disk_i % len(disks)]
        avail = bottom - y
        two = W >= 150
        # linhas fixas por painel (título, valores e eixo de tempo; fora o gráfico)
        fixed = {"cpu": 5, "mem": 5, "disk": 4 + len(disks), "psi": 7}     # inclui as bordas
        if two:
            top, low = max(fixed["cpu"], fixed["mem"]), max(fixed["disk"], fixed["psi"])
            ch = (avail - top - low) // 2
            if ch < 2:
                self.draw_compact(y, bottom, v)
                return
            ch2 = avail - top - low - ch
            colw = W // 2
            self.panel_cpu(y, 0, colw, ch + top - fixed["cpu"], v)
            self.panel_mem(y, colw, W - colw, ch + top - fixed["mem"], v)
            y2 = y + top + ch
            self.panel_disk(y2, 0, colw, ch2 + low - fixed["disk"], v, d)
            self.panel_psi(y2, colw, W - colw, ch2 + low - fixed["psi"], v)
            self.xmax = None
        else:
            free = avail - sum(fixed.values())
            ch = free // 4
            if ch < 1:
                self.draw_compact(y, bottom, v)
                return
            hs = [ch + (1 if i < free - 4 * ch else 0) for i in range(4)]
            yy = y
            yy = self.panel_cpu(yy, 0, W, hs[0], v)
            yy = self.panel_mem(yy, 0, W, hs[1], v)
            yy = self.panel_disk(yy, 0, W, hs[2], v, d)
            self.panel_psi(yy, 0, W, hs[3], v)
            self.xmax = None

    def panel_cpu(self, y, x, w, ch, v):
        A, h = self.A, self.hist
        self.box_top(y, x, w, "CPU", self.period_stats("cpu_avg", "cpu_max", hi_key="cpu_hi"))
        y0, ox, ow = y, x, w
        x, w = x + 1, w - 2
        self.xmax = x + w
        cpu = v.get("cpu")
        xx = self.puts(y + 1, x + 1, [("uso ", A["dim"]), ("%5s " % fmt_val(cpu, "%"), self.pct_attr(cpu) | A["bold"])])
        bw = max(10, min(40, w // 3))
        self.bar(y + 1, xx, bw, cpu)
        tag, ta = self.cpu_tag(v)
        if tag:
            self.put(y + 1, xx + bw + 2, tag, ta)
        rq = v.get("rq")
        load = v.get("load") or []
        self.puts(y + 2, x + 1, [
            ("fila ", A["dim"]), ("%s/%d" % (fmt_num(rq), h.ncpu), self.pct_attr(100 * (rq or 0) / max(1, h.ncpu), 100, 101) if rq is not None else A["dim"]),
            ("  load ", A["dim"]), (" ".join(fmt_load(l) for l in load), A["text"]),
            ("  PSI ", A["dim"]), (fmt_val(v.get("pc"), "%"), self.pct_attr(v.get("pc"), 5, 10)),
            ("  steal ", A["dim"]), (fmt_val(v.get("st"), "%"), self.pct_attr(v.get("st"), 2, 5)),
            ("  iowait ", A["dim"]), (fmt_val(v.get("iow"), "%"), A["text"]),
            ("  núcleo + ocupado ", A["dim"]), (fmt_val(v.get("hot"), "%"), self.pct_attr(v.get("hot"), 80, 95))])
        self.chart(y + 3, x, ch, w, "cpu_avg", "cpu_max")
        return self.box_close(y0, y + 3 + ch + 1, ox, ow)

    def panel_mem(self, y, x, w, ch, v):
        A = self.A
        self.box_top(y, x, w, "MEMÓRIA", self.period_stats("mem_avg", "mem_max", hi_key="mem_hi"))
        y0, ox, ow = y, x, w
        x, w = x + 1, w - 2
        self.xmax = x + w
        mem = v.get("mem")
        xx = self.puts(y + 1, x + 1, [("uso ", A["dim"]), ("%5s " % fmt_val(mem, "%"), self.pct_attr(mem, 85, 95) | A["bold"])])
        bw = max(10, min(40, w // 3))
        self.bar(y + 1, xx, bw, mem, attr=self.pct_attr(mem, 85, 95))
        mt, ma, mc = v.get("mt"), v.get("ma"), v.get("mc")
        s = "  %s usados de %s · %s disponíveis" % (fmt_gb(mt - ma if mt is not None and ma is not None else None), fmt_gb(mt), fmt_gb(ma))
        if mc is not None:
            s += " (cache %s, liberável)" % fmt_gb(mc)
        self.put(y + 1, xx + bw, s, A["text"])
        swt, swf = v.get("swt"), v.get("swf")
        sw = (v.get("swin") or 0) + (v.get("swout") or 0)
        self.puts(y + 2, x + 1, [
            ("swap ", A["dim"]), ("%s de %s (%s)" % (fmt_gb(swt - swf if swt is not None and swf is not None else None), fmt_gb(swt), fmt_val(v.get("swp"), "%")), A["text"]),
            ("  swap in/out ", A["dim"]), ("%s/%s pág/s" % (fmt_val(v.get("swin"), ""), fmt_val(v.get("swout"), "")), self.pct_attr(sw, 5, 10)),
            ("  majf ", A["dim"]), ("%s/s" % fmt_val(v.get("majf"), ""), A["text"]),
            ("  PSI ", A["dim"]), (fmt_val(v.get("pms"), "%"), self.pct_attr(v.get("pms"), 1, 5)),
            (" (full %s)" % fmt_val(v.get("pmf"), "%"), self.pct_attr(v.get("pmf"), 1, 5))])
        self.chart(y + 3, x, ch, w, "mem_avg", "mem_max", attr_fn=lambda a, m: self.pct_attr(a, 85, 95))
        return self.box_close(y0, y + 3 + ch + 1, ox, ow)

    def disk_line(self, y, x, d, dv, sel):
        A = self.A
        info = self.disk_type(d)
        u = dv.get("u")
        xx = self.puts(y, x, [((">" if sel else " ") + "%-7s" % d, A["bold"] if sel else A["text"]), ("%-4s" % info, A["dim"]),
                               ("%5s " % fmt_val(u, "%"), self.pct_attr(u))])
        self.bar(y, xx, 8, u)
        self.puts(y, xx + 9, [
            ("MB/s ", A["dim"]), ("%s/%s" % (fmt_val(dv.get("r"), ""), fmt_val(dv.get("w"), "")), A["text"]),
            ("  IOPS ", A["dim"]), ("%s/%s" % (fmt_val(dv.get("ri"), ""), fmt_val(dv.get("wi"), "")), A["text"]),
            ("  lat ", A["dim"]), ("%s/%s ms" % (fmt_val(dv.get("raw"), ""), fmt_val(dv.get("waw"), "")), self.pct_attr(dv.get("aw"), 20, 50)),
            ("  fila ", A["dim"]), (fmt_val(dv.get("qd"), ""), self.pct_attr(dv.get("qd"), 1, 2))])

    def panel_disk(self, y, x, w, ch, v, d):
        A, h = self.A, self.hist
        disks = self.disk_list()
        self.box_top(y, x, w, "DISCO (I/O)", self.period_stats(d + ".util_avg", d + ".util_max", hi_key=d + ".util_hi"))
        y0, ox, ow = y, x, w
        x, w = x + 1, w - 2
        self.xmax = x + w
        for i, dd in enumerate(disks):
            self.disk_line(y + 1 + i, x + 1, dd, v.get(dd) or {}, dd == d and len(disks) > 1)
        yy = y + 1 + len(disks)
        self.put(yy, x + 1, "valores leitura/gravação · gráfico: %% ocupado de %s · %s" % (d, cap_text(h.caps.get(d), short=True)), A["dim"])
        self.chart(yy + 1, x, ch, w, d + ".util_avg", d + ".util_max")
        return self.box_close(y0, yy + 1 + ch + 1, ox, ow)

    def panel_psi(self, y, x, w, ch, v):
        A = self.A
        self.box_top(y, x, w, "PRESSÃO (PSI: % do tempo esperando)", "faixa: condição · gráfico: PSI I/O")
        y0, ox, ow = y, x, w
        x, w = x + 1, w - 2
        self.xmax = x + w
        for i, (name, k, kf) in enumerate((("CPU", "pc", None), ("MEM", "pms", "pmf"), ("I/O", "pis", "pif"))):
            val = v.get(k)
            xx = self.puts(y + 1 + i, x + 1, [("%-4s" % name, A["bold"]), ("%6s " % fmt_val(val, "%"), self.pct_attr(val, 5, 20))])
            self.bar(y + 1 + i, xx, 20, val, attr=self.pct_attr(val, 5, 20))
            if kf:
                self.puts(y + 1 + i, xx + 21, [("full ", A["dim"]), (fmt_val(v.get(kf), "%"), self.pct_attr(v.get(kf), 5, 20))])
        self.state_strip(y + 4, x, w)
        ch2 = max(1, ch)
        self.chart(y + 5, x, ch2, w, "psi_io", "psi_io_max", scale=None, unit="%",
                   attr_fn=lambda a, m: self.pct_attr(a, 5, 20))
        return self.box_close(y0, y + 5 + ch2 + 1, ox, ow)

    def box_top(self, y, x, w, title, right="", border=None, title_attr=None, right_attr=None):
        """Borda de cima de uma caixa, com título à esquerda e texto à direita embutidos."""
        b = self.g.box
        self.xmax = None
        border = self.A["dim"] if border is None else border
        self.put(y, x, b[0] + b[5] * (w - 2) + b[1], border)
        title = title[:max(1, w - 6)]
        self.put(y, x + 2, " %s " % title, self.A["title"] if title_attr is None else title_attr)
        if right:
            right = right[:max(0, w - len(title) - 9)]
            if right:
                self.put(y, x + w - len(right) - 4, " %s " % right, self.A["accent"] if right_attr is None else right_attr)

    def box_close(self, y0, y1, x, w, border=None):
        """Laterais (linhas y0+1..y1-1) e borda de baixo na linha y1. Devolve a linha seguinte."""
        b = self.g.box
        self.xmax = None
        border = self.A["dim"] if border is None else border
        for yy in range(y0 + 1, y1):
            self.put(yy, x, b[4], border)
            self.put(yy, x + w - 1, b[4], border)
        self.put(y1, x, b[2] + b[5] * (w - 2) + b[3], border)
        return y1 + 1

    def rule_at(self, y, x, w, title, right=""):
        self.put(y, x, self.g.rule * w, self.A["dim"])
        self.put(y, x + 1, " %s " % title, self.A["title"])
        if right:
            self.put(y, x + max(len(title) + 4, w - len(right) - 3), " %s " % right, self.A["accent"])

    def draw_compact(self, y, bottom, v):
        """Tela baixa: só números e uma linha de tendência por recurso."""
        A, W, h = self.A, self.W, self.hist
        rows = [("CPU", "cpu_avg", "cpu_max", v.get("cpu"), 100.0, "%"), ("MEM", "mem_avg", "mem_max", v.get("mem"), 100.0, "%")]
        for d in h.disks:
            rows.append((d, d + ".util_avg", d + ".util_max", (v.get(d) or {}).get("u"), 100.0, "%"))
        rows.append(("PSI io", "psi_io", "psi_io_max", v.get("pis"), None, "%"))
        for i, (name, ka, km, val, sc, unit) in enumerate(rows):
            if y + i >= bottom:
                break
            xx = self.puts(y + i, 1, [("%-7s" % name, A["bold"]), ("%6s " % fmt_val(val, unit), self.pct_attr(val))])
            self.chart(y + i, xx, 1, W - xx - 1, ka, km, scale=sc, unit=unit, axis=False, labels=False)
        if y + len(rows) < bottom:
            self.state_strip(y + len(rows), 1, W - 2)
        if y + len(rows) + 1 < bottom:
            self.put(y + len(rows) + 1, 1, "terminal baixo: só tendências (média do período em cada coluna)", A["dim"])

    def draw_tiny(self):
        A = self.A
        lv, res, msg, dg = self.status()
        lab = "SEM DADOS" if lv is None else LEVEL_NAMES[lv]
        self.put(0, 0, " %s " % lab, self.status_attr(lv))
        y = 1
        for k, name in self.res_list():
            d = (dg or {}).get(k)
            l = d[0] if d else None
            self.puts(y, 0, [("%-8s" % name, A["text"]), ("SEM DADOS" if l is None else LEVEL_NAMES[l], A["dim"] if l is None else self.lbl_attr[l])])
            y += 1
        for line in [msg[:self.W * 2], "Terminal pequeno: aumente para ver gráficos.", "q sai"]:
            while line and y < self.H:
                self.put(y, 0, line[:self.W], A["dim"] if "Terminal" in line else A["text"])
                line = line[self.W:]
                y += 1

    # ---- telas de detalhe ----
    def charts_block(self, y, bottom, specs):
        """Empilha gráficos (título + gráfico + eixo) dividindo a altura disponível."""
        n = len(specs)
        avail = bottom - y
        ch = max(1, (avail - 3 * n) // n)          # borda de cima, eixo de tempo e borda de baixo
        W = self.W
        for title, ka, km, scale, unit, hi_key, extra in specs:
            if y + 3 > bottom:
                break
            ch_eff = min(ch, bottom - y - 3)
            self.box_top(y, 0, W, title, self.period_stats(ka, km, unit, hi_key))
            self.xmax = W - 1
            self.chart(y + 1, 1, ch_eff, W - 2, ka, km, scale=scale, unit=unit, **extra)
            y = self.box_close(y, y + ch_eff + 2, 0, W)
        return y

    def view_cpu(self, y, bottom):
        v = self.cur_vals()
        A, W, h = self.A, self.W, self.hist
        pc = v.get("percpu")
        self.box_top(y, 0, W, "CPU · %d vCPUs · uso por CPU" % h.ncpu, "ao vivo" if pc else "sem leitura ao vivo")
        y0 = y
        y += 1
        self.xmax = W - 1
        if pc:
            cell = 22
            per_row = max(1, (W - 4) // cell)
            for i, u in enumerate(pc):
                r, c = divmod(i, per_row)
                xx = self.puts(y + r, c * cell + 2, [("%-4s" % ("c%d" % i), A["dim"]), ("%4.0f%% " % u, self.pct_attr(u))])
                self.bar(y + r, xx, cell - 12, u)
            y += (len(pc) + per_row - 1) // per_row
        tag, ta = self.cpu_tag(v)
        self.puts(y, 2, [("agora: uso ", A["dim"]), (fmt_val(v.get("cpu"), "%"), self.pct_attr(v.get("cpu"))),
                         ("  fila ", A["dim"]), ("%s/%d" % (fmt_num(v.get("rq")), h.ncpu), A["text"]),
                         ("  PSI ", A["dim"]), (fmt_val(v.get("pc"), "%"), self.pct_attr(v.get("pc"), 5, 10)),
                         ("  steal ", A["dim"]), (fmt_val(v.get("st"), "%"), self.pct_attr(v.get("st"), 2, 5)),
                         ("   " + tag, ta)])
        y += 1
        load = v.get("load") or []
        self.put(y, 2, "load 1/5/15 min: %s — processos rodando ou esperando (CPU ou disco); compare com %d vCPUs; não é %% de uso" % (
            " ".join(fmt_load(l) for l in load) or "NA", h.ncpu), A["dim"])
        y = self.box_close(y0, y + 1, 0, W)
        self.charts_block(y, bottom, [
            ("Uso total (%)", "cpu_avg", "cpu_max", 100.0, "%", "cpu_hi", {}),
            ("Fila de execução (processos prontos; linha tracejada = nº de CPUs)", "rq_avg", "rq_max", None, "", "rq_over", {"ref": h.ncpu}),
            ("PSI cpu (% do tempo esperando CPU)", "psi_cpu", "psi_cpu_max", None, "%", None, {"attr_fn": lambda a, m: self.pct_attr(a, 5, 10)}),
            ("Steal (% tomado pelo hipervisor)", "st_avg", "st_max", None, "%", None, {"attr_fn": lambda a, m: self.pct_attr(a, 2, 5)}),
        ])

    def view_mem(self, y, bottom):
        v = self.cur_vals()
        A, W = self.A, self.W
        mt, ma, mc = v.get("mt"), v.get("ma"), v.get("mc")
        self.box_top(y, 0, W, "MEMÓRIA", "usado = total - disponível (cache não conta)")
        self.xmax = W - 1
        self.puts(y + 1, 2, [("total ", A["dim"]), (fmt_gb(mt), A["text"]),
                             ("  usado ", A["dim"]), (fmt_gb(mt - ma if mt is not None and ma is not None else None), self.pct_attr(v.get("mem"), 85, 95)),
                             ("  disponível ", A["dim"]), (fmt_gb(ma), A["text"]),
                             ("  cache/buffers ", A["dim"]), (fmt_gb(mc), A["text"]),
                             ("  swap ", A["dim"]), (fmt_val(v.get("swp"), "%"), A["text"]),
                             ("  PSI some/full ", A["dim"]), ("%s / %s" % (fmt_val(v.get("pms"), "%"), fmt_val(v.get("pmf"), "%")), self.pct_attr(v.get("pms"), 1, 5))])
        self.charts_block(self.box_close(y, y + 2, 0, W), bottom, [
            ("Memória em uso (%)", "mem_avg", "mem_max", 100.0, "%", "mem_hi", {"attr_fn": lambda a, m: self.pct_attr(a, 85, 95)}),
            ("Swap ocupado (%)", "swap", "swap", 100.0, "%", None, {}),
            ("Paginação de swap (in+out, pág/s) — sustentado = falta de RAM", "swio", "swio", None, "", None, {"attr_fn": lambda a, m: self.pct_attr(a, 5, 10)}),
            ("Major page faults/s", "majf", "majf", None, "", None, {"attr_fn": lambda a, m: self.A["accent"]}),
            ("PSI memória (%)", "psi_mem", "psi_mem_max", None, "%", None, {"attr_fn": lambda a, m: self.pct_attr(a, 1, 5)}),
        ])

    def view_disk(self, y, bottom):
        v = self.cur_vals()
        A, W, h = self.A, self.W, self.hist
        disks = self.disk_list()
        d = disks[self.disk_i % len(disks)]
        self.box_top(y, 0, W, "DISCO %s (%d de %d · n troca)" % (d, self.disk_i % len(disks) + 1, len(disks)), h.disk_info.get(d, ""))
        self.xmax = W - 1
        self.disk_line(y + 1, 1, d, v.get(d) or {}, False)
        self.puts(y + 2, 2, [("capacidade: ", A["dim"]), (cap_text(h.caps.get(d)), A["text"]),
                             ("   PSI io ", A["dim"]), ("%s (full %s)" % (fmt_val(v.get("pis"), "%"), fmt_val(v.get("pif"), "%")), self.pct_attr(v.get("pis"), 5, 20)),
                             ("   LVM/dm-* não somados (I/O já contado no disco físico)", A["dim"])])
        lat_spec = (d + ".await", d + ".await")
        self.charts_block(self.box_close(y, y + 3, 0, W), bottom, [
            ("% ocupado (util) — 100% sozinho não prova saturação", d + ".util_avg", d + ".util_max", 100.0, "%", d + ".util_hi", {}),
            ("Vazão (MB/s, leitura+gravação)", d + ".MBs_avg", d + ".MBs_max", None, "MB/s", None, {"attr_fn": lambda a, m: self.A["accent"]}),
            ("IOPS (operações/s)", d + ".iops_avg", d + ".iops_max", None, "", None, {"attr_fn": lambda a, m: self.A["accent"]}),
            ("Latência média (ms)", lat_spec[0], lat_spec[1], None, "ms", None, {"attr_fn": lambda a, m: self.pct_attr(a, 20, 50)}),
            ("Fila de I/O (queue depth)", d + ".qd_avg", d + ".qd_max", None, "", None, {"attr_fn": lambda a, m: self.pct_attr(a, 1, 2)}),
            ("PSI I/O (%)", "psi_io", "psi_io_max", None, "%", None, {"attr_fn": lambda a, m: self.pct_attr(a, 5, 20)}),
        ])

    # ---- laço ----
    def tty_alive(self):
        if not hasattr(os, "tcgetpgrp"):
            return True
        try:
            os.tcgetpgrp(sys.stdin.fileno())
            return True
        except OSError:
            return False

    def run(self):
        try:
            curses.curs_set(0)
        except curses.error:
            pass
        self.scr.timeout(250)
        self.scr.keypad(True)
        last = drawn = 0.0
        last_tty = time.time()
        dirty = True
        while True:
            now = time.time()
            if self.loading or (not self.paused and now - last >= 1):
                ver, live = self.hist.version, self.live
                more = self.hist.poll()
                self.loading = more
                DISPLAY_TZ[0] = self.hist.tz_offset
                self.poll_live()
                last = now
                # redesenha só com novidade (janela gravada, amostra nova) ou a cada REDRAW_IDLE s
                # (idade da medição, relógio): o painel fica parado na tela gastando quase nada
                if more or self.hist.version != ver or self.live is not live or now - drawn >= REDRAW_IDLE:
                    dirty = True
            if dirty:
                self.draw()
                drawn = now
                dirty = False
            if self.mon and self.mon.updater and self.mon.updater.restart.is_set():
                raise Restart()
            ch = self.scr.getch()
            if ch == -1:
                if now - last_tty > 5:
                    last_tty = now
                    if not self.tty_alive():
                        raise OSError("terminal desconectado")
                continue
            dirty = True
            if ch == curses.KEY_RESIZE:
                try:
                    if os.name == "nt":
                        curses.resize_term(0, 0)        # windows-curses precisa disso no redimensionamento
                    curses.update_lines_cols()
                except (AttributeError, curses.error):
                    pass
                self.cache.clear()
                continue
            k = chr(ch).lower() if 0 <= ch < 256 else ""
            if ch == 27 and (self.help or self.tech):
                self.help = self.tech = False
            elif k == "q" or ch == 27:
                if self.help:
                    self.help = False
                elif not self.mon or (self.quit_armed and time.time() - self.quit_armed < 3):
                    raise Quit()
                else:
                    self.quit_armed = time.time()
            elif k in "12345" and k:
                self.period = int(k) - 1
            elif k == "d":
                self.tech = not self.tech
                self.help = False
            elif k == "?":
                self.help = not self.help
            elif self.tech and (k == "\t" or ch in (curses.KEY_RIGHT, curses.KEY_LEFT, curses.KEY_BTAB)):
                self.tab += -1 if ch in (curses.KEY_LEFT, curses.KEY_BTAB) else 1
            elif k == "n":
                self.disk_i += 1
            elif k == "u":
                self.cloud_sync()
            elif k == "k":
                self.catkey_prompt()
            elif k == "p":
                self.paused = not self.paused
            elif k == "r":
                self.hist.reset()
                self.cache.clear()
                self.loading = True


Dashboard.TECH = [("visão geral", Dashboard.view_general), ("CPU", Dashboard.view_cpu),
                  ("memória", Dashboard.view_mem), ("disco", Dashboard.view_disk), ("hardware e glossário", Dashboard.view_hw)]

GLOSSARY = """\
GLOSSÁRIO
Load average   média de processos rodando ou esperando (CPU ou disco)
               em 1, 5 e 15 min. Compare com o nº de vCPUs. Não é % de uso.
Fila (run queue)  processos prontos para rodar agora; acima do nº de
               vCPUs = processos esperando CPU.
PSI            % do tempo em que processos ficaram parados esperando o
               recurso (some = algum processo; full = todos ao mesmo tempo).
Steal          CPU que o hypervisor deu a outras VMs: problema do host.
iowait         CPU ociosa esperando disco (indicador fraco; prefira PSI I/O).
Núcleo + ocupado  um núcleo a 100% com o resto livre = programa de 1 thread.
Swap in/out    páginas trocadas com o disco por falta de RAM.
Major faults   páginas que precisaram ser lidas do disco.
% ocupado      tempo com I/O em andamento no disco (não é capacidade).
MB/s, IOPS     volume e nº de operações por segundo.
Latência       tempo médio por operação de I/O (ms).
Fila de I/O    operações em andamento no disco ao mesmo tempo.
"""


# ---- formatação ----
REDRAW_IDLE = 5          # s entre redesenhos do painel sem dado novo
PROMPT_IDLE = 300        # s sem tecla na caixa da chave do catálogo (tecla k) até desistir
DISPLAY_TZ = [None]      # deslocamento UTC (s) do servidor do relatório; None = fuso desta máquina


def stime(t=None):
    """struct_time no horário do servidor monitorado (o painel nunca usa o fuso de quem olha)."""
    t = time.time() if t is None else t
    off = DISPLAY_TZ[0]
    return time.gmtime(t + off) if off is not None else time.localtime(t)


def tz_label(off):
    if off is None:
        return ""
    h, m = divmod(abs(int(off)) // 60, 60)
    return "UTC%s%d%s" % ("-" if off < 0 else "+", h, ":%02d" % m if m else "")


def headline(msg):
    """Título curto de uma frase de diagnóstico (até o primeiro ponto ou parêntese)."""
    return msg.split(". ")[0].split(" (")[0].rstrip(".")


def fmt_when(t, short=False):
    """Hora de um instante: só HH:MM se for hoje."""
    lt = stime(t)
    if lt[:3] == stime()[:3]:
        return time.strftime("%H:%M" if short else "hoje %H:%M", lt)
    if lt[:3] == stime(time.time() - 86400)[:3]:
        return time.strftime("ontem %H:%M", lt)
    return time.strftime("%d/%m %H:%M", lt)


def fmt_span(sec):
    sec = max(0, sec)
    if sec < 90:
        return "%.0f s" % sec
    if sec < 5400:
        return "%.0f min" % (sec / 60)
    if sec < 2 * 86400:
        h, m = divmod(int(sec // 60), 60)
        return "%d h %02d min" % (h, m) if m else "%d h" % h
    return "%.1f dias" % (sec / 86400)


def nice(x):
    if x is None or x <= 0:
        return 1.0
    e = 10 ** math.floor(math.log10(x))
    for m in (1, 2, 2.5, 5, 10):
        if x <= m * e * 1.0001:
            return m * e
    return 10 * e


def fmt_val(v, unit):
    if v is None or v != v:
        return "NA"
    if unit == "%":
        return "%.0f%%" % v if v >= 10 or v == 0 else "%.1f%%" % v
    if abs(v) >= 10000:
        s = "%.0fk" % (v / 1000)
    elif abs(v) >= 100:
        s = "%.0f" % v
    elif abs(v) >= 10:
        s = "%.1f" % v
    else:
        s = "%.2f" % v if v else "0"
    return s + (" " + unit if unit else "")


def fmt_num(v):
    if v is None or v != v:
        return "NA"
    return "%d" % v if v == int(v) else "%.1f" % v


def fmt_load(x):
    try:
        return "%.2f" % float(x)
    except (TypeError, ValueError):
        return "NA"


def fmt_gb(v):
    if v is None or v != v:
        return "NA"
    return "%.1f GB" % v


def fmt_bytes(b):
    """Bytes em unidades de 1024 (como o df -h): '812 MB', '4.2 GB', '1.8 TB'."""
    if b is None or b != b:
        return "NA"
    for unit, k in (("TB", GIB * 1024), ("GB", GIB)):
        if abs(b) >= k:
            return "%.1f %s" % (b / k, unit)
    return "%.0f MB" % (b / 1048576)


def fmt_dur(sec):
    d, r = divmod(int(sec), 86400)
    h, r = divmod(r, 3600)
    return "%dd %02dh" % (d, h) if d else "%dh %02dmin" % (h, r // 60)


def fmt_ago(sec):
    if sec < 90:
        return "há %.0fs" % sec
    if sec < 5400:
        return "há %.0f min" % (sec / 60)
    if sec < 2 * 86400:
        return "há %.1f h" % (sec / 3600)
    return "há %.0f dias" % (sec / 86400)


def fmt_min(m):
    if m == 0:
        return "0 min"
    if m < 1:
        return "%.0fs" % (m * 60)
    if m < 120:
        return "%.0f min" % m
    return "%.1f h" % (m / 60)


def disk_kind(info):
    return "HDD" if "rotacional" in info else "SSD" if "SSD" in info else "?"


def disk_perf(iops):
    """Classe de desempenho pelo IOPS aleatório medido no disco inteiro."""
    if iops >= 5000:
        return "desempenho de flash/SSD"
    if iops >= 1000:
        return "desempenho de SSD lento ou storage compartilhado"
    return "desempenho de disco mecânico ou storage saturado"


def cap_text(cap, short=False):
    if not cap or (cap.get("bw_MBs", "NA") == "NA" and cap.get("iops", "NA") == "NA"):
        return "capacidade não medida" if short else "não medida (sem % da capacidade; rode com benchmark)"
    if short:
        return "capacidade %s MB/s, %s IOPS" % (cap.get("bw_MBs"), cap.get("iops"))
    return "%s MB/s, %s IOPS (%s)" % (cap.get("bw_MBs"), cap.get("iops"),
                                      "benchmark" if cap.get("src") == "bench" else "benchmark anterior")


# --------------------------------------------------------------------------
# Serviço (--service), parada (--parar), configuração (--configurar) e diagnóstico (--diagnostico)
# --------------------------------------------------------------------------
TASK_NAME = "C2 Server Monitor"          # tarefa agendada criada pelo instalar.ps1 (Windows)
SERVICE_BACKOFF = (30, 600)              # s de espera depois de uma falha do coletor: 30, 60, 120... até 600
UCRT_DLL = "api-ms-win-crt-runtime-l1-1-0.dll"


def run_child(cmd, **kw):
    """Roda um processo filho e devolve o código de saída. Ctrl+C no console chega aos dois: o pai só espera o
    filho terminar (ele grava a janela parcial e sai sozinho)."""
    p = subprocess.Popen(cmd, **kw)
    while True:
        try:
            return p.wait()
        except KeyboardInterrupt:
            continue


def windows_console():
    """Windows: o programa roda sempre no modo UTF-8 do Python (relatório, JSON e saída em UTF-8, nunca na página
    de código ANSI/OEM) e com o console em UTF-8 (65001). Sem o modo UTF-8, reinicia a si mesmo com -X utf8 (a
    tarefa agendada já passa -X utf8)."""
    if not sys.flags.utf8_mode:
        sys.exit(run_child([sys.executable, "-X", "utf8"] + sys.argv))
    with contextlib.suppress(Exception):
        win_dll("kernel32").SetConsoleOutputCP(65001)


def service_log(base):
    """Saída do --service (sem console): server_monitor_servico.log, com rotação simples (> 5 MB vira .1)."""
    path = os.path.join(base, SERVICE_LOG)
    with contextlib.suppress(OSError):
        if os.path.getsize(path) > SERVICE_LOG_MAX:
            os.replace(path, path + ".1")
    return open(path, "a", encoding="utf-8")


def supervise(script, argv, base, sleep=time.sleep):
    """--service: processo pai que mantém o coletor rodando (tarefa agendada do Windows; no Linux serve para
    systemd/cron). Roda o coletor como filho, com os mesmos argumentos e a saída em server_monitor_servico.log:
    - código SERVICE_RESTART (autoatualização): inicia de novo na hora (já na versão nova);
    - server_monitor.parar presente (--parar): apaga o pedido e termina com 0;
    - qualquer outro fim (erro, outro coletor no mesmo relatório): espera 30 s, 60 s... até 10 min e tenta de novo.
    O pai só espera (não coleta nem usa a rede) e é o único que não se atualiza sozinho (só no próximo início)."""
    stop = os.path.join(base, STOP_FILE)
    with contextlib.suppress(OSError):
        os.remove(stop)                                # pedido antigo de parada não vale para esta partida
    env = dict(os.environ)
    env[SUPERVISED_ENV] = "1"
    py = [sys.executable] + (["-X", "utf8"] if IS_WINDOWS else [])
    args, fails = list(argv), 0
    while True:
        with service_log(base) as f:
            f.write("%s serviço: iniciando o coletor (%s)\n" % (iso_now(), " ".join(args)))
            f.flush()
            t0 = time.monotonic()
            rc = run_child(py + [script] + args, stdout=f, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL, env=env)
            ran = time.monotonic() - t0
            args = restart_argv(argv)                  # reinícios: sem benchmark nem apt-get
            if os.path.exists(stop):
                with contextlib.suppress(OSError):
                    os.remove(stop)
                f.write("%s serviço: parado a pedido (--parar)\n" % iso_now())
                return 0
            if rc == SERVICE_RESTART:
                f.write("%s serviço: reiniciando na versão nova\n" % iso_now())
                fails = 0
                continue
            fails = 1 if ran > SERVICE_BACKOFF[1] else fails + 1
            wait = min(SERVICE_BACKOFF[1], SERVICE_BACKOFF[0] * 2 ** (fails - 1))
            f.write("%s serviço: o coletor terminou (código %s); nova tentativa em %d s\n" % (iso_now(), rc, wait))
        end = time.monotonic() + wait
        while time.monotonic() < end:
            if os.path.exists(stop):
                with contextlib.suppress(OSError):
                    os.remove(stop)
                return 0
            sleep(min(5.0, max(0.0, end - time.monotonic())))


def report_has_bench(log):
    """O relatório já tem um benchmark (linha BENCH)? (--bench-auto: o serviço mede a capacidade uma vez só)."""
    try:
        with open(log, "rb") as f:
            return any(line.startswith(b"BENCH ") for line in f)
    except OSError:
        return False


def collector_running(log):
    """Há um coletor gravando neste relatório? Tenta a mesma trava do coletor (e solta na hora)."""
    path = log if fcntl is not None else log + ".lock"
    if not os.path.exists(path):
        return False
    with open(path, "a") as f:
        if not lock_file(f):
            return True
        if fcntl is None:
            with contextlib.suppress(OSError):
                f.seek(0)
                msvcrt.locking(f.fileno(), msvcrt.LK_UNLCK, 1)
    return False


# ---- Início automático com o sistema (v2.13) --------------------------------------------------------------------
# Linux com systemd: unidade server-monitor.service (WorkingDirectory = pasta do monitor; outra pasta no mesmo servidor
# = server-monitor-<hash>.service), coletor --headless como root, Restart=always. Linux sem systemd: /etc/cron.d com
# @reboot rodando o --service (supervisor). Windows: a tarefa agendada do instalar.ps1 (recriada se tiver sumido).
# O coletor confere tudo isso na partida (service_setup); iniciado fora do serviço (tmux, nohup) passa a coleta para
# ele. Qualquer falha só fica registrada (SERVICE: status/<sid>/service, --diagnostico) e a coleta segue como antes.
SYSTEMD_DIR = "/etc/systemd/system"      # unidades locais
SYSTEMD_RUN = "/run/systemd/system"      # existe = o systemd é o init (o mesmo teste do sd_booted)
CRON_DIR = "/etc/cron.d"                 # reserva sem systemd
SYSTEMCTL, SCHTASKS = "systemctl", "schtasks"
UNIT_BASE = "server-monitor"
SYSTEMD_ENV = "USAGE_MONITOR_SYSTEMD"    # coletor iniciado pela unidade (Environment=)
CRON_ENV = "USAGE_MONITOR_CRON"          # supervisor iniciado pelo @reboot do cron
SERVICE_WAIT = 30                        # s para o serviço pegar a trava do relatório (senão: coleta segue aqui)
SERVICE_CMD_TIMEOUT = 120                # s por chamada ao systemctl/schtasks (stop espera o coletor gravar a janela)
SERVICE = {"mode": "", "unit": "", "note": ""}   # estado desta partida: systemd | cron | tarefa | nenhum


def svc_cmd(*args, timeout=SERVICE_CMD_TIMEOUT):
    """systemctl/schtasks/journalctl sem shell: (código, saída). 127 = comando ausente ou tempo esgotado."""
    try:
        p = subprocess.run(list(args), stdout=subprocess.PIPE, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
                           universal_newlines=True, timeout=timeout)
        return p.returncode, (p.stdout or "").strip()
    except (OSError, subprocess.SubprocessError) as e:
        return 127, str(e)


def is_root():
    return hasattr(os, "geteuid") and os.geteuid() == 0


def systemd_ok():
    return os.path.isdir(SYSTEMD_RUN) and bool(shutil.which(SYSTEMCTL))


def unit_workdir(text):
    m = re.search(r"^WorkingDirectory=(.*)$", text or "", re.M)
    return m.group(1).strip().replace("%%", "%") if m else ""


def unit_name(base):
    """server-monitor.service para a 1ª pasta registrada; outra pasta no mesmo servidor ganha um nome próprio."""
    base = os.path.abspath(base)
    if unit_workdir(read_file(os.path.join(SYSTEMD_DIR, UNIT_BASE + ".service"))) in ("", base):
        return UNIT_BASE + ".service"
    return "%s-%s.service" % (UNIT_BASE, hashlib.sha1(base.encode()).hexdigest()[:8])


def cron_path(base):
    return os.path.join(CRON_DIR, "%s-%s" % (UNIT_BASE, hashlib.sha1(os.path.abspath(base).encode()).hexdigest()[:8]))


def service_args(a, log):
    """Opções de coleta desta partida que o serviço repete (só as diferentes do padrão; caminhos absolutos)."""
    out = []
    for flag, k, dflt in (("-i", "interval", 300), ("-b", "biz_interval", 30), ("--biz-hours", "biz_hours", "6-20"),
                          ("-s", "sample", 5), ("-m", "bench_mb", 1024)):
        v = getattr(a, k, dflt)
        if v != dflt:
            out += [flag, str(v)]
    if getattr(a, "output", None):
        out += ["-o", os.path.abspath(log)]
    if getattr(a, "bench_dir", None):
        out += ["-d", os.path.abspath(a.bench_dir)]
    return out


def sd_quote(s):
    """Argumento do ExecStart do systemd: % e $ literais; aspas quando há espaço, aspas ou barra invertida."""
    s = s.replace("%", "%%").replace("$", "$$")
    if not s or re.search(r"[\s\"'\\;]", s):
        s = '"%s"' % s.replace("\\", "\\\\").replace('"', '\\"')
    return s


def unit_text(unit, py, script, base, args):
    """Conteúdo da unidade systemd. Sem a versão do programa: só muda (e é regravada) se o caminho/opções mudarem."""
    cmd = " ".join(sd_quote(x) for x in [py, script, "--headless", "--no-install", "--bench-auto"] + list(args))
    return ("# Gerado pelo usage_monitor.py (v2.13+): coletor do server_monitor iniciado com o sistema.\n"
            "# O próprio monitor reescreve este arquivo se o caminho ou as opções mudarem.\n"
            "# Parar: systemctl stop {u} | iniciar: systemctl start {u} | não iniciar no boot: systemctl disable {u}\n"
            "[Unit]\n"
            "Description=C2 Server Monitor ({d})\n"
            "After=network-online.target\n"
            "Wants=network-online.target\n\n"
            "[Service]\n"
            "Type=simple\n"
            "WorkingDirectory={d}\n"
            "Environment={e}=1 PYTHONUNBUFFERED=1 PYTHONIOENCODING=utf-8\n"
            "ExecStart={c}\n"
            "Restart=always\n"
            "RestartSec=30\n"
            "TimeoutStopSec=90\n\n"
            "[Install]\n"
            "WantedBy=multi-user.target\n").format(u=unit, d=os.path.abspath(base).replace("%", "%%"), e=SYSTEMD_ENV,
                                                    c=cmd)


def write_system_file(path, text, mode=0o644):
    """Grava um arquivo do sistema (unidade, cron) de uma vez: .novo + rename."""
    tmp = path + ".novo"
    try:
        with open(tmp, "w", encoding="utf-8") as f:
            f.write(text)
        os.chmod(tmp, mode)
        os.replace(tmp, path)
    except OSError:
        with contextlib.suppress(OSError):
            os.remove(tmp)
        raise


def systemd_ensure(unit, text):
    """Unidade gravada (só se mudou, com daemon-reload) e habilitada no boot. '' = ok; senão o problema."""
    path = os.path.join(SYSTEMD_DIR, unit)
    if read_file(path) != text:
        try:
            write_system_file(path, text)
        except OSError as e:
            return "não consegui gravar %s (%s)" % (path, e)
        rc, out = svc_cmd(SYSTEMCTL, "daemon-reload")
        if rc:
            return "systemctl daemon-reload falhou (%s)" % out[-200:]
    if svc_cmd(SYSTEMCTL, "is-enabled", unit)[1].splitlines()[-1:] != ["enabled"]:
        rc, out = svc_cmd(SYSTEMCTL, "enable", unit)
        if rc:
            return "systemctl enable %s falhou (%s)" % (unit, out[-200:])
    return ""


def systemd_state(unit):
    """'active', 'inactive', 'failed', 'activating'... (vazio = systemctl indisponível)."""
    rc, out = svc_cmd(SYSTEMCTL, "is-active", unit)
    return (out.splitlines() or [""])[-1].strip() if rc != 127 else ""


def systemd_running(unit):
    return systemd_state(unit) in ("active", "activating", "reloading")


def systemd_handoff(unit, log, wait=None, sleep=time.sleep):
    """Inicia o serviço e espera ele pegar a trava do relatório. '' = assumiu a coleta. Senão devolve o problema,
    com o serviço parado e desabilitado de novo (não fica um 2º coletor tentando): a coleta segue no chamador."""
    wait = SERVICE_WAIT if wait is None else wait
    rc, out = svc_cmd(SYSTEMCTL, "start", "--no-block", unit)
    if rc == 0:
        end = time.monotonic() + wait
        while time.monotonic() < end:
            if collector_running(log):
                return ""
            if systemd_state(unit) == "failed":
                break
            sleep(0.5)
        err = "o serviço %s não assumiu a coleta em %d s" % (unit, wait)
    else:
        err = "systemctl start %s falhou (%s)" % (unit, out[-200:])
    svc_cmd(SYSTEMCTL, "stop", unit)
    svc_cmd(SYSTEMCTL, "disable", unit)
    return err


def cron_text(py, script, base, args):
    cmd = " ".join(shlex.quote(x) for x in [py, script, "--service", "--no-install", "--bench-auto"] + list(args))
    return ("# Gerado pelo usage_monitor.py (v2.13+): sem systemd, o coletor do server_monitor inicia no boot por aqui.\n"
            + ("@reboot root cd %s && %s=1 %s > /dev/null 2>&1\n" % (shlex.quote(os.path.abspath(base)), CRON_ENV, cmd))
            .replace("%", "\\%"))           # % no cron = fim do comando


def cron_ensure(text, base):
    """Linha @reboot em /etc/cron.d (só grava se mudou). '' = ok; senão o problema."""
    path = cron_path(base)
    if not os.path.isdir(CRON_DIR):
        return "sem systemd e sem %s: inicie o monitor de novo depois de reiniciar o servidor" % CRON_DIR
    if read_file(path) != text:
        try:
            write_system_file(path, text)
        except OSError as e:
            return "não consegui gravar %s (%s)" % (path, e)
    return ""


def win_task_xml(py, script, base):
    """A mesma tarefa do instalar.ps1: ao iniciar o Windows (30 s), como SYSTEM, sem limite de tempo, reinicia em falha."""
    e = xml_escape
    return ('<?xml version="1.0" encoding="UTF-16"?>\n'
            '<Task version="1.2" xmlns="http://schemas.microsoft.com/windows/2004/02/mit/task">\n'
            '  <RegistrationInfo><Description>C2 Server Monitor: coleta de CPU, memoria e espaco, envio a central e acesso'
            ' ao banco.</Description></RegistrationInfo>\n'
            '  <Triggers><BootTrigger><Enabled>true</Enabled><Delay>PT30S</Delay></BootTrigger></Triggers>\n'
            '  <Principals><Principal id="Author"><UserId>S-1-5-18</UserId><RunLevel>HighestAvailable</RunLevel>'
            '</Principal></Principals>\n'
            '  <Settings>\n'
            '    <MultipleInstancesPolicy>IgnoreNew</MultipleInstancesPolicy>\n'
            '    <DisallowStartIfOnBatteries>false</DisallowStartIfOnBatteries>\n'
            '    <StopIfGoingOnBatteries>false</StopIfGoingOnBatteries>\n'
            '    <AllowHardTerminate>true</AllowHardTerminate>\n'
            '    <StartWhenAvailable>true</StartWhenAvailable>\n'
            '    <RunOnlyIfNetworkAvailable>false</RunOnlyIfNetworkAvailable>\n'
            '    <IdleSettings><StopOnIdleEnd>false</StopOnIdleEnd><RestartOnIdle>false</RestartOnIdle></IdleSettings>\n'
            '    <AllowStartOnDemand>true</AllowStartOnDemand>\n'
            '    <Enabled>true</Enabled>\n'
            '    <Hidden>false</Hidden>\n'
            '    <RunOnlyIfIdle>false</RunOnlyIfIdle>\n'
            '    <WakeToRun>false</WakeToRun>\n'
            '    <ExecutionTimeLimit>PT0S</ExecutionTimeLimit>\n'
            '    <Priority>7</Priority>\n'
            '    <RestartOnFailure><Interval>PT1M</Interval><Count>999</Count></RestartOnFailure>\n'
            '  </Settings>\n'
            '  <Actions Context="Author">\n'
            '    <Exec>\n'
            '      <Command>%s</Command>\n'
            '      <Arguments>-X utf8 "%s" --service --no-bench</Arguments>\n'
            '      <WorkingDirectory>%s</WorkingDirectory>\n'
            '    </Exec>\n'
            '  </Actions>\n'
            '</Task>\n') % (e(py), e(script), e(os.path.abspath(base)))


def win_task_ensure(py, script, base):
    """Windows fora da tarefa (coletor iniciado à mão): recria a tarefa agendada se ela sumiu, sem iniciá-la (vale
    no próximo boot; iniciar agora daria dois coletores). Devolve (modo, observação)."""
    if svc_cmd(SCHTASKS, "/Query", "/TN", TASK_NAME)[0] == 0:
        return "tarefa", ""
    fd, xf = tempfile.mkstemp(prefix="c2_server_monitor_task", suffix=".xml")
    try:
        with os.fdopen(fd, "w", encoding="utf-16") as f:     # schtasks /XML espera UTF-16 (com BOM)
            f.write(win_task_xml(py, script, base))
        rc, out = svc_cmd(SCHTASKS, "/Create", "/TN", TASK_NAME, "/XML", xf, "/F")
    finally:
        with contextlib.suppress(OSError):
            os.remove(xf)
    if rc:
        return "nenhum", "tarefa agendada '%s' ausente e não consegui criá-la (%s)" % (TASK_NAME, out[-200:] or rc)
    return "tarefa", "tarefa agendada '%s' recriada pelo monitor (vale a partir do próximo boot)" % TASK_NAME


def service_setup(a, log, base, script, enabled=True, out=print):
    """Partida do coletor (v2.13): garante que o monitor volte sozinho quando o servidor reiniciar e, no Linux com
    systemd, passa a coleta para o serviço se este processo foi iniciado de outro jeito (tmux, nohup, terminal; é o
    caminho das instalações antigas, que chegam aqui pela autoatualização). True = o serviço está coletando (este
    processo não coleta). Falha nunca derruba a coleta: fica em SERVICE (status, --diagnostico) e segue como antes."""
    py = os.path.abspath(sys.executable or shutil.which("python3") or "/usr/bin/python3")
    args = service_args(a, log)

    def done(mode, note="", unit=""):
        SERVICE.update(mode=mode, note=note, unit=unit)
        if note:
            out("Início automático com o sistema: %s." % note)
        return False

    supervised = os.environ.get(SUPERVISED_ENV) == "1"
    if IS_WINDOWS:
        if supervised:
            return done("tarefa", unit=TASK_NAME)
        if not enabled:
            return done("nenhum", "desligado (sync.service)")
        mode, note = win_task_ensure(py, script, base)
        return done(mode, note, TASK_NAME)
    if os.environ.get(SYSTEMD_ENV) == "1":               # este processo é o serviço: unidade em dia (vale no próximo início)
        unit = unit_name(base)
        err = systemd_ensure(unit, unit_text(unit, py, script, base, args)) if is_root() and systemd_ok() else ""
        return done("systemd", err and "unidade não atualizada: " + err, unit)
    if os.environ.get(CRON_ENV) == "1":
        err = cron_ensure(cron_text(py, script, base, args), base) if is_root() else ""
        return done("cron", err, cron_path(base))
    if not enabled:
        return done("nenhum", "desligado (sync.service)")
    if supervised:
        return done("nenhum", "--service fora do systemd e do cron")
    if not is_root():
        return done("nenhum", "sem root, não dá para registrar o serviço (rode o instalar.sh com sudo)")
    if not systemd_ok():
        err = cron_ensure(cron_text(py, script, base, args), base)
        return done("nenhum", err) if err else done("cron", "sem systemd: @reboot em %s" % cron_path(base),
                                                    cron_path(base))
    unit = unit_name(base)
    err = systemd_ensure(unit, unit_text(unit, py, script, base, args))
    if err:
        return done("nenhum", err)
    SERVICE.update(mode="systemd", unit=unit, note="")
    if systemd_running(unit):
        out("O monitor já roda como serviço (%s)." % unit)
        return True
    out("Passando a coleta para o serviço %s (inicia sozinho com o servidor)..." % unit)
    err = systemd_handoff(unit, log)
    if err:
        return done("nenhum", err + "; a coleta segue neste processo")
    out("OK: o serviço %s assumiu a coleta." % unit)
    return True


def install_service(a, log, base, script, out=print):
    """--instalar-servico (instalar.sh): registra e inicia o serviço do Linux e espera ele assumir a coleta.
    0 = serviço systemd coletando; 3 = sem systemd (cron @reboot gravado: o instalador inicia a coleta como antes);
    2 = não dá (Windows, sem root, desligado); 1 = falhou (o instalador inicia a coleta como antes)."""
    if IS_WINDOWS:
        out("No Windows o serviço é a tarefa agendada do instalar.ps1.")
        return 2
    if not is_root():
        out("ERRO: --instalar-servico precisa de root (sudo).")
        return 2
    check_deps(a.install)
    py = os.path.abspath(sys.executable or shutil.which("python3") or "/usr/bin/python3")
    args = service_args(a, log)
    if not systemd_ok():
        err = cron_ensure(cron_text(py, script, base, args), base)
        out("Sem systemd: %s" % (err or "início no boot registrado em %s (@reboot)" % cron_path(base)))
        return 1 if err else 3
    unit = unit_name(base)
    running = systemd_running(unit)
    if not running and collector_running(log):
        out("ERRO: há um coletor gravando em %s fora do serviço; pare-o antes." % log)
        return 1
    err = systemd_ensure(unit, unit_text(unit, py, script, base, args))
    if err:
        out("ERRO: %s" % err)
        return 1
    if running:
        rc, msg = svc_cmd(SYSTEMCTL, "restart", unit)  # já rodando: reinicia na versão/opções atuais
        err = "" if rc == 0 else "systemctl restart %s falhou (%s)" % (unit, msg[-200:])
    else:
        err = systemd_handoff(unit, log)
    if err:
        out("ERRO: %s" % err)
        return 1
    out("OK: serviço %s ativo e habilitado no boot." % unit)
    out("SERVICO=%s" % unit)
    return 0


def service_report(base, log, out=print):
    """Linhas do --diagnostico sobre o início automático (Linux; o Windows mostra a tarefa agendada)."""
    if not systemd_ok():
        cp = cron_path(base)
        out("Início automático: sem systemd; cron @reboot %s" % ("registrado em %s" % cp if os.path.isfile(cp)
                                                                  else "NÃO registrado"))
        return
    unit = unit_name(base)
    path = os.path.join(SYSTEMD_DIR, unit)
    if not os.path.isfile(path):
        out("Início automático: serviço %s NÃO registrado (o monitor registra na próxima partida como root, ou rode"
            " o instalar.sh)" % unit)
        return
    en = (svc_cmd(SYSTEMCTL, "is-enabled", unit)[1].splitlines() or ["?"])[-1]
    out("Início automático: serviço %s | no boot: %s | agora: %s" % (unit, en, systemd_state(unit) or "?"))
    m = re.search(r"^ExecStart=(.*)$", read_file(path), re.M)
    if m:
        out("  ExecStart=%s" % m.group(1))
    rc, txt = svc_cmd("journalctl", "-u", unit, "-n", "8", "--no-pager", "-o", "short-iso", timeout=20)
    if rc == 0 and txt:
        out("  últimas linhas do serviço (journalctl -u %s):" % unit)
        for l in txt.splitlines()[-8:]:
            out("    " + l)


def stop_service(base, log):
    """--parar com o coletor rodando como serviço systemd: systemctl stop (o systemd não religa; volta no boot).
    None = não é o caso (segue o pedido por arquivo)."""
    if IS_WINDOWS or not systemd_ok():
        return None
    unit = unit_name(base)
    if not os.path.isfile(os.path.join(SYSTEMD_DIR, unit)) or not systemd_running(unit):
        return None
    if not is_root():
        print("ERRO: o monitor roda como serviço (%s); pare com: sudo systemctl stop %s" % (unit, unit))
        return 1
    print("Parando o serviço %s (o coletor grava a janela em andamento)..." % unit)
    rc, msg = svc_cmd(SYSTEMCTL, "stop", unit)
    if rc:
        print("ERRO: systemctl stop %s falhou: %s" % (unit, msg[-300:]))
        return 1
    print("OK: serviço parado. Volta no próximo boot; para iniciar já: systemctl start %s" % unit)
    return 0


def request_stop(base, log, timeout=60, sleep=time.sleep):
    """--parar: pede ao coletor (--service ou o do Windows) que encerre como no Ctrl+C (janela parcial, EVENT stop,
    "monitor parado" na central) e espera a trava do relatório ficar livre. 0 = parado (ou não estava rodando).
    Linux com o serviço systemd (v2.13): systemctl stop (o systemd não o religa)."""
    rc = stop_service(base, log)
    if rc is not None:
        return rc
    if not collector_running(log):
        print("Nenhum coletor rodando em %s." % log)
        return 0
    with open(os.path.join(base, STOP_FILE), "w") as f:
        f.write(iso_now() + "\n")
    print("Pedido de parada gravado; aguardando o coletor encerrar (até %d s)..." % timeout)
    end = time.monotonic() + timeout
    while time.monotonic() < end:
        if not collector_running(log):
            print("OK: coletor parado.")
            return 0
        sleep(1)
    print("AVISO: o coletor ainda não parou (ele confere o pedido a cada amostra; tente de novo).")
    return 1


def configure(ident, interactive):
    """--configurar (usado pelo instalar.ps1): pergunta o que faltar (JSON colado ou uma a uma: empresa, nome,
    Firebase, chave do catálogo) e sai, sem iniciar a coleta. 0 = configuração completa."""
    if not interactive:
        print("ERRO: --configurar precisa de um console/terminal (use --config-json para configurar sem perguntas).")
        return 2
    try:
        ask_config_json(ident)
        ident.ask_missing()
        live = LiveStatus(ident, ident.base)
        if not live.configured() and require_firebase(ident):
            live = LiveStatus(ident, ident.base)
        if live.configured():
            ask_catkey(ident, live)
    except KeyboardInterrupt:
        print()
    left = config_missing(ident)
    if left:
        print("Ainda falta: %s (rode de novo: %s --configurar)" % (", ".join(dict(CONFIG_ITEMS)[k] for k in left),
                                                                  sys.argv[0]))
        return 1
    print("OK: configuração completa.")
    return 0


def probe(url, timeout=10):
    """Acesso HTTPS a uma URL para o diagnóstico: 'HTTP 200', 'HTTP 401'... ou o erro (com dica de certificado)."""
    req = urllib.request.Request(url, headers={"User-Agent": "usage_monitor/" + VERSION})
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r:
            return "HTTP %d" % r.status
    except urllib.error.HTTPError as e:
        return "HTTP %d" % e.code
    except Exception as e:                             # URLError, timeout, SSL...
        msg = "erro: %s" % (getattr(e, "reason", None) or e)
        if "CERTIFICATE_VERIFY_FAILED" in msg:
            msg += (" -> certificados raiz desatualizados: no Windows 7/2008 R2 instale as atualizações de"
                    " certificados raiz (ou rode o instalar.ps1 de novo, que as aciona pelo .NET)")
        return msg


def run_diagnostics(log, ident, host, script_dir, out=print):
    """--diagnostico: tudo o que importa para acompanhar uma instalação nova (sobretudo no Windows), em texto para
    colar: sistema, Python, uma amostra de cada fonte de dados, configuração, coletor, rede e banco local.
    Não altera nada (nem a configuração) e não mostra segredos. Devolve 0."""
    src = source()
    out("=== DIAGNÓSTICO usage_monitor %s (%s) ===" % (VERSION, iso_now()))
    out("Sistema: %s | arch %s | host %s" % (platform.platform(), platform.machine(), host))
    out("Python: %s %s (%d bits) em %s | UTF-8: %s | saída: %s" % (
        platform.python_implementation(), platform.python_version(), struct.calcsize("P") * 8, sys.executable,
        "sim" if sys.flags.utf8_mode else "não", getattr(sys.stdout, "encoding", "?")))
    out("Pasta: %s | relatório: %s (%s)" % (script_dir, log, "%d bytes" % os.path.getsize(log)
                                             if os.path.isfile(log) else "ainda não existe"))
    out("Fonte de dados: %s (monitoramento %s)" % (src.name, src.monitoring))
    if not src.available():
        out("  INDISPONÍVEL: %s" % ("; ".join("%s: %s" % kv for kv in sorted(src.errors.items())) or "-"))
    else:
        disks = src.disks()
        p = src.snap(disks)
        time.sleep(1)
        s, _ = src.sample(p, src.snap(disks), disks)
        out("  amostra de 1 s: CPU %s%% | núcleo mais ocupado %s%% | fila %s (%d CPUs) | memória %s%% | swap/paginação %s%%"
            % (F(s["cpu"], "%.1f"), F(s["hot"], "%.0f"), F(s["rq"], "%d"), src.cpu_count(), F(s["mem"], "%.1f"),
               F(s["swp"], "%.1f")))
        out("  discos (desempenho): %s" % (" ".join(disks) or "nenhum (Windows: monitoramento básico)"))
        for f in src.filesystems():
            out("  espaço %s (%s): %.1f%% ocupado, %s livres de %s" % (
                f["mount"], f["fstype"], f["used_pct"], fmt_bytes(f["free_bytes"]), fmt_bytes(f["total_bytes"])))
        if not src.full:
            for k, v in src.hardware(host):
                out("  HW %s: %s" % (k, v))
        for k, v in sorted(src.errors.items()):
            out("  falha em %s: %s" % (k, v))
    out("Coletor rodando neste relatório: %s" % ("sim" if collector_running(log) else "não"))
    if not IS_WINDOWS:
        service_report(os.path.dirname(os.path.abspath(log)), log, out)
    hb = read_json(live_path(log) + HB_SUFFIX)
    st = hb.get("http") if isinstance(hb, dict) else None
    if isinstance(st, dict):
        out("  conexões ao Firebase (desde a partida): %s novas, %s reaproveitadas, %s refeitas após queda, %s pelo urllib (proxy)"
            % (st.get("new", 0), st.get("reused", 0), st.get("retried", 0), st.get("urllib", 0)))
    live = LiveStatus(ident, ident.base)
    cfg = ident.sync_cfg()
    out("Configuração: empresa=%r nome=%r id=%s" % (ident.company, ident.name, ident.install_id or "-"))
    out("  Firebase: %s | chave do catálogo: %s | auto_update: %s | db_access: %s" % (
        (ident.data.get("live") or {}).get("db_url") if live.configured() else "NÃO CONFIGURADO",
        "presente" if read_catkey(os.path.join(ident.base, CATKEY_FILE)) is not None else "ausente",
        cfg["auto_update"], cfg["db_access"]))
    ac = AgentConfig(os.path.join(ident.base, SYNC_DIR, AGENT_CFG_FILE))
    e = ac.apply(cfg)
    out("  frequências (%s%s): faixa %s, heartbeat %d s, status %d s, offline após %d s, atualização a cada %d s%s" % (
        "central" if ac.source == "central" else "padrão local", ", carimbo %s" % ac.at if ac.at else "", e["band"],
        e["heartbeat_interval"], e["interval_normal"], e["offline_after"], e["update_interval"],
        "; ignorado: " + ", ".join(ac.ignored) if ac.ignored else ""))
    out("Rede:")
    out("  GitHub (autoatualização): %s" % probe(UPDATE_URL))
    db_url = (ident.data.get("live") or {}).get("db_url") or FIREBASE_DB_URL
    out("  Firebase (%s): %s (401 = acessível; as regras exigem login)" % (db_url, probe(db_url + "/.json?shallow=true")))
    if live.configured():
        try:
            live.token()
            out("  login do servidor no Firebase: OK")
        except CloudError as e:
            out("  login do servidor no Firebase: ERRO %s" % e)
    d = DB_DEFAULTS
    try:
        PgConn(d["host"], d["port"], d["dbname"], d["user"], d["password"], d["sslmode"], timeout=5).close()
        out("Banco local (padrão %s:%s/%s): conectou" % (d["host"], d["port"], d["dbname"]))
    except DbError as e:
        out("Banco local (padrão %s:%s/%s): %s [%s] (a central pode gravar outra conexão em db_config)" % (
            d["host"], d["port"], d["dbname"], e, e.code))
    run_sql_diagnostics(ident, cfg, ac, out)
    if IS_WINDOWS:
        sysdir = os.path.join(os.environ.get("SystemRoot", "C:\\Windows"), "System32")
        out("Windows: Universal C Runtime (%s): %s" % (UCRT_DLL, "presente" if any(os.path.exists(os.path.join(sysdir, f)) for f in ("ucrtbase.dll", UCRT_DLL))
                                                    else "AUSENTE (instale o KB2999226)"))
        rc, txt = run('schtasks /Query /TN "%s" /FO LIST /V' % TASK_NAME, capture=True)
        keep = ("Status", "Last Run Time", "Last Result", "Next Run Time", "Run As User", "Task To Run",
                "Hora da última execução", "Último resultado", "Executar como usuário", "Tarefa a ser executada")
        lines = [l.strip() for l in txt.splitlines() if l.strip().startswith(keep)]
        out("  tarefa agendada '%s': %s" % (TASK_NAME, "registrada" if rc == 0 else "NÃO ENCONTRADA"))
        for l in lines:
            out("    " + l)
        sl = os.path.join(os.path.dirname(os.path.abspath(log)), SERVICE_LOG)
        if os.path.isfile(sl):
            with open(sl, encoding="utf-8", errors="replace") as f:
                tail = f.readlines()[-8:]
            out("  últimas linhas de %s:" % SERVICE_LOG)
            for l in tail:
                out("    " + l.rstrip())
    out("=== fim do diagnóstico: copie tudo acima e envie para a C2 ===")
    return 0


def run_sql_diagnostics(ident, cfg, ac, out=print):
    """Linha SQL do --diagnostico: interruptores, openssl, certificado (sem gerar) e cada relay permitido."""
    on = cfg["sql_editor"] and cfg["db_access"]
    cert = os.path.join(ident.base, SQL_CERT_FILE)
    fp = "ainda não gerado"
    try:
        with open(cert) as f:
            fp = hashlib.sha256(ssl.PEM_cert_to_DER_cert(f.read())).hexdigest()
    except (OSError, ValueError, AttributeError):
        pass
    out("SQL (editor remoto, só leitura): %s | openssl: %s | certificado: %s" % (
        "ligado" if on else "DESLIGADO (sync.%s)" % ("sql_editor" if not cfg["sql_editor"] else "db_access"),
        shutil.which("openssl") or "ausente (gerador próprio em Python)", fp))
    relays = sql_relays_parse(ac.get("sql", "relays")) or sql_relays_parse(SQL_RELAYS_DEFAULT)
    for r in relays:
        out("  relay %s: %s" % (r, sql_probe(r)))


# --------------------------------------------------------------------------
# Programa principal
# --------------------------------------------------------------------------
def parse_args():
    p = argparse.ArgumentParser(
        prog="usage_monitor.py",
        description="usage_monitor v%s - monitor contínuo de CPU / memória / disco com painel no terminal" % VERSION,
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="Variável opcional: DISKS=\"sda sdb\" para escolher os discos monitorados.\n"
               "Exemplos:\n  ./usage_monitor.py\n  nohup ./usage_monitor.py --headless > /dev/null 2>&1 &\n"
               "  ./usage_monitor.py --view                 (acompanha o coletor acima)\n"
               "  ./usage_monitor.py --view reports/servidor1/usage_report_servidor1.log")
    p.add_argument("-i", "--interval", type=int, default=300, metavar="SEG", help="duração da janela fora do horário comercial (padrão 300)")
    p.add_argument("-b", "--biz-interval", type=int, default=30, metavar="SEG", help="duração da janela no horário comercial (padrão 30; use o mesmo valor de -i para janela fixa)")
    p.add_argument("--biz-hours", default="6-20", metavar="H-H", help="horário comercial, hora inicial-final (padrão 6-20)")
    p.add_argument("-s", "--sample", type=int, default=5, metavar="SEG", help="intervalo entre amostras dentro da janela (padrão 5)")
    p.add_argument("-o", "--output", metavar="ARQ", help="arquivo de relatório (padrão ./usage_report_<host>.log)")
    p.add_argument("-d", "--bench-dir", metavar="DIR", help="diretório para o teste de disco (padrão: pasta do script) -> aponte para o disco do banco de dados")
    p.add_argument("-m", "--bench-mb", type=int, default=1024, metavar="MB", help="tamanho do teste de disco (padrão 1024)")
    p.add_argument("--no-bench", dest="bench", action="store_false", help="não roda o benchmark (reaproveita capacidades do log)")
    p.add_argument("--no-install", dest="install", action="store_false", help="não verifica/instala dependências via apt-get")
    p.add_argument("--bench-auto", action="store_true",
                   help="roda o benchmark só se o relatório ainda não tiver um (BENCH); usado pelo serviço do Linux")
    g = p.add_mutually_exclusive_group()
    g.add_argument("--headless", action="store_true", help="só coleta, sem painel (para nohup, tmux, serviço)")
    g.add_argument("--view", nargs="?", const="", metavar="ARQ", help="só painel, lendo um relatório existente (não coleta)")
    p.add_argument("--service", action="store_true",
                   help="serviço (tarefa agendada do Windows, systemd...): coleta sem painel num processo filho, "
                        "reiniciado sozinho (falha e autoatualização); saída em %s" % SERVICE_LOG)
    p.add_argument("--parar", action="store_true",
                   help="para o coletor: o serviço do Linux (systemctl stop; volta no boot) ou o do --service; espera e sai")
    p.add_argument("--instalar-servico", action="store_true",
                   help="Linux, como root: registra o serviço systemd (inicia com o servidor), passa a coleta para "
                        "ele e sai (usado pelo instalar.sh; sem systemd grava um @reboot no cron)")
    p.add_argument("--diagnostico", action="store_true",
                   help="mostra sistema, Python, uma amostra de cada fonte, configuração, rede, banco local, "
                        "editor SQL (certificado e relays) e tarefa agendada (para colar no suporte) e sai")
    p.add_argument("--mono", action="store_true", help="painel sem cores (também com NO_COLOR=1)")
    p.add_argument("--ascii", action="store_true", help="painel só com caracteres ASCII (terminal sem UTF-8)")
    p.add_argument("--compat", action="store_true",
                   help="gráficos só com caracteres presentes em qualquer fonte (use se aparecerem "
                        "quadrados vazios na tela)")
    p.add_argument("--version", action="version", version="usage_monitor " + VERSION)
    c = p.add_argument_group("empresa e nuvem")
    c.add_argument("--empresa", metavar="NOME", help="define/troca o nome da empresa deste servidor, salva e sai")
    c.add_argument("--nome", metavar="NOME", help="define/troca o nome amigável deste servidor no painel central "
                                                 "(ex.: \"Sescom - Linux\"), salva e sai")
    c.add_argument("--config-json", metavar="ARQ|-",
                   help="aplica a configuração que falta (empresa, nome, Firebase, chave do catálogo) de um JSON "
                        "(arquivo ou - para a entrada padrão), salva e sai; formato no README")
    c.add_argument("--configurar", action="store_true",
                   help="pergunta o que faltar (JSON colado ou uma a uma) sem iniciar a coleta e sai (instalar.ps1)")
    c.add_argument("--catalogo-chave", action="store_true",
                   help="pergunta (de novo) a chave do catálogo de operações do banco, salva e sai")
    c.add_argument("--cloud-setup", action="store_true", help="configura a nuvem: Firebase (painel central) e/ou GitHub (arquivo)")
    c.add_argument("--firebase-setup", action="store_true", help="configura só o Firebase")
    c.add_argument("--sync", action="store_true", help="envia agora os relatórios para a nuvem e sai (no painel: tecla u)")
    c.add_argument("--cloud", action="store_true", help="baixa relatórios da nuvem (empresa > servidor > período) e abre no painel")
    c.add_argument("--repo", metavar="DONO/NOME", help="repositório dos relatórios para --cloud (padrão: o configurado)")
    c.add_argument("--out", default="reports", metavar="DIR", help="pasta de destino do --cloud (padrão ./reports)")
    a = p.parse_args()
    try:
        a.biz_start, a.biz_end = (int(x) for x in a.biz_hours.split("-"))
    except ValueError:
        p.error("--biz-hours inválido: %s (use H-H, ex.: 6-20)" % a.biz_hours)
    for k in ("interval", "biz_interval", "sample"):
        if getattr(a, k) <= 0:
            p.error("--%s precisa ser > 0" % k.replace("_", "-"))
    a.cpu_hi = a.mem_hi = a.disk_hi = 90
    if a.service:
        a.headless = True
    return a


def run_dashboard(hist, mon, a, sync=None, ident=None):
    """Abre o painel; devolve 'quit' (usuário saiu), 'restart' (autoatualização) ou 'lost' (terminal caiu)."""
    if curses is None:
        die("falta o módulo curses. No Windows: py -m pip install windows-curses")
    def ui(scr):
        Dashboard(scr, hist, mon, a, sync, ident).run()
    try:
        curses.wrapper(ui)
    except Restart:
        return "restart"
    except Quit:
        return "quit"
    except KeyboardInterrupt:
        return "quit"
    except (curses.error, OSError):
        return "lost"
    return "quit"


def utf8_locale():
    """Locale do sistema; se não for UTF-8 (LANG vazio/C, comum em servidor mínimo como o Ubuntu 18.04), usa
    C.UTF-8 — senão o curses desenha acentos e bordas como "Ã©"/"â". Devolve o locale final de LC_CTYPE."""
    try:
        locale.setlocale(locale.LC_ALL, "")
    except locale.Error:
        pass
    if "UTF" not in (locale.nl_langinfo(locale.CODESET) or "").upper().replace("-", ""):
        for name in ("C.UTF-8", "C.utf8", "en_US.UTF-8"):
            try:
                locale.setlocale(locale.LC_ALL, name)
                os.environ["LC_ALL"] = name            # filhos (apt, tmux) e o reinício da autoatualização
                break
            except locale.Error:
                continue
    return locale.setlocale(locale.LC_CTYPE)


def main():
    if IS_WINDOWS:
        windows_console()
    else:
        utf8_locale()
    a = parse_args()
    script_dir = os.path.dirname(os.path.abspath(__file__))
    host = platform.node().split(".")[0] or "localhost"
    log = a.output or os.path.join(script_dir, "usage_report_%s.log" % host)

    def on_term(sig, frm):
        raise KeyboardInterrupt
    signal.signal(signal.SIGTERM, on_term)
    interactive = sys.stdin.isatty() and sys.stdout.isatty()

    # ---- relatórios da nuvem (em qualquer máquina, inclusive no Mac) ----
    if a.cloud:
        cloud_pull(a, script_dir)
        return
    if a.view is not None:
        log = a.view or log
    base = os.path.dirname(os.path.abspath(log))
    ident = Identity(base)
    if a.diagnostico:
        sys.exit(run_diagnostics(log, ident, host, script_dir))
    if a.parar:
        sys.exit(request_stop(base, log))
    if a.instalar_servico:
        sys.exit(install_service(a, log, base, os.path.abspath(__file__)))
    if a.empresa or a.nome:
        ident.ensure_id()
        if a.empresa:
            ident.set_company(a.empresa)
            print("Empresa deste servidor: %s (salvo em %s)" % (ident.company, ident.path))
        if a.nome:
            ident.set_name(a.nome)
            print("Nome deste servidor: %s (salvo em %s)" % (ident.name, ident.path))
        if not (a.cloud_setup or a.firebase_setup):
            return                       # só grava; o monitor é iniciado sem --empresa/--nome
    if a.config_json:
        ident.ensure_id()
        sys.exit(config_from_file(ident, a.config_json))
    if a.catalogo_chave:
        ident.ensure_id()
        try:
            sys.exit(0 if ask_catkey(ident, force=True) else 1)
        except KeyboardInterrupt:
            print()
            sys.exit(1)
    if a.cloud_setup or a.firebase_setup:
        ident.ensure_id()
        if interactive:
            ident.ask_missing()
        sys.exit(cloud_setup(ident, "firebase" if a.firebase_setup else None))
    if a.configurar:
        ident.ensure_id()
        sys.exit(configure(ident, interactive))
    if a.sync:
        try:
            n = CloudSync(log, ident, host).run(out=print)
            print("OK: %s" % ("%d arquivo(s) enviado(s)" % n if n else "nada novo para enviar"))
        except CloudError as e:
            die(str(e))
        return
    cloud = CloudSync(log, ident, host)
    sync = SyncManager(cloud, auto=False) if cloud.configured() else None

    # ---- somente visualização ----
    if a.view is not None:
        if not os.path.isfile(log):
            die("relatório não encontrado: %s" % log)
        if not sys.stdout.isatty():
            die("--view precisa de um terminal.")
        lower_priority(ident.sync_cfg()["low_priority"])     # ler o histórico não compete com o servidor
        run_dashboard(History(log), None, a, sync, ident if ident.data else None)
        return

    if a.service and os.environ.get(SUPERVISED_ENV) != "1":
        sys.exit(supervise(os.path.abspath(__file__), sys.argv[1:], base))   # pai: mantém o coletor (filho) rodando
    # v2.13: início automático com o sistema; iniciado fora do serviço (tmux, nohup) = o serviço assume a coleta
    if service_setup(a, log, base, os.path.abspath(__file__), ident.sync_cfg()["service"]):
        if interactive and not a.headless and not IS_WINDOWS:
            view = [x for x in ("--mono", "--ascii", "--compat") if getattr(a, x[2:])]
            py = sys.executable or shutil.which("python3") or "/usr/bin/python3"
            print("Abrindo o painel (q fecha só o painel; o serviço continua coletando)...", flush=True)
            FB_HTTP.close_all()
            os.execv(py, [py, os.path.abspath(__file__), "--view", log] + view)
        sys.exit(0)
    src = source()
    if not src.available():
        die("este programa precisa de Linux (/proc) ou Windows 7/2008 R2+ (%s). Para só ver um relatório use --view ARQ."
            % ("; ".join(v for _, v in sorted(src.errors.items())) or platform.system()))
    if src.full:
        check_deps(a.install)
    else:
        a.bench = False                                   # Windows (monitoramento básico): sem benchmark
    if a.bench and a.bench_auto and report_has_bench(log):
        a.bench = False                                   # serviço: benchmark só na 1ª partida (reaproveita o CAP)
    a.bench_dir = a.bench_dir or script_dir
    disks = src.disks()
    ncpu = src.cpu_count()

    # Um coletor por arquivo: trava o relatório (o --view só lê, não trava). Windows: trava num arquivo à parte
    lockf = None
    try:
        logf = open(log, "a")
        if fcntl is not None:
            # serviço: o coletor que passou a coleta confere a trava por instantes (collector_running); espera um pouco
            for i in range(5 if os.environ.get(SYSTEMD_ENV) == "1" else 1):
                try:
                    fcntl.flock(logf, fcntl.LOCK_EX | fcntl.LOCK_NB)
                    break
                except BlockingIOError:
                    if i == 4 or os.environ.get(SYSTEMD_ENV) != "1":
                        raise
                    time.sleep(0.5)
        else:
            lockf = open(log + ".lock", "a")
            if not lock_file(lockf):
                raise BlockingIOError
    except BlockingIOError:
        die("já existe um coletor gravando em %s.\n  Para acompanhá-lo: %s --view %s" % (log, sys.argv[0], log))
    except OSError as e:
        die("não consegui abrir %s: %s" % (log, e))

    ask_ok = not a.headless and interactive               # pode perguntar o que falta na partida
    dashboard = ask_ok and not IS_WINDOWS                 # Windows: sem painel (coleta no console ou --service)
    ident.ensure_id()
    if ident.notice:
        print("AVISO: " + ident.notice)
    if ask_ok:
        try:
            if "firebase" not in ask_config_json(ident):    # tudo o que falta num JSON só (Enter = uma a uma)
                cloud = CloudSync(log, ident, host)
        except KeyboardInterrupt:
            print()
        ident.ask_missing()
    else:
        if not ident.company:
            print("AVISO: empresa não configurada (rode uma vez: %s --empresa \"Nome da empresa\")" % sys.argv[0])
        if not ident.name:
            print("AVISO: nome do servidor não configurado; o painel central mostra só o hostname"
                  " (rode uma vez: %s --nome \"Empresa - Servidor\")" % sys.argv[0])

    if not cloud.live.configured():
        if ask_ok and require_firebase(ident):
            cloud = CloudSync(log, ident, host)               # relê a configuração recém-salva
        elif not cloud.live.configured():
            print("AVISO: Firebase não configurado; este servidor não aparece no painel central"
                  " (rode: %s --firebase-setup)" % sys.argv[0])
    if ask_ok and cloud.live.configured():
        try:
            ask_catkey(ident, cloud.live)                     # acesso ao banco configurado na central e sem chave
        except KeyboardInterrupt:
            print()

    def out(s):
        try:
            print(s, flush=True)
        except OSError:
            pass
    # frequências da central (v2.11): a última recebida já vale na partida (a coleta entra no SESSION)
    cloud.acfg = AgentConfig(os.path.join(cloud.dir, AGENT_CFG_FILE), a.sample)
    cloud.acfg.apply_collect(a)
    cloud.acfg.out = out
    mon = Monitor(a, log, logf, host, disks, ncpu, out)
    mon.ident, mon.lockf = ident, lockf
    if a.service or IS_WINDOWS:                           # --parar encerra este coletor
        mon.stop_file = os.path.join(base, STOP_FILE)
        with contextlib.suppress(OSError):
            os.remove(mon.stop_file)                      # pedido antigo não vale para esta partida
    mon.verbose = not (a.service or os.environ.get(SYSTEMD_ENV) == "1")   # serviço: sem a linha de cada amostra
    if cloud.configured():
        sync = SyncManager(cloud, auto=True)
        mon.sync = sync
        if sync.auto and cloud.live.configured():
            mon.db = DbAgent(cloud, out=mon.say)              # liga sozinho quando existir db_config/<sid>
            mon.sysev = SysEvents(cloud, mon.db, out=mon.say)  # eventos do sistema: mesma conexão do DbAgent
            mon.sql = SqlEditor(cloud, mon.db, out=mon.say)    # editor SQL: pedidos pela mesma escuta do DbAgent
    # autoatualização: só o coletor; ao gravar a versão nova para a coleta e o laço abaixo sai para reiniciar
    mon.updater = Updater(os.path.abspath(__file__), ident.sync_cfg(), out=mon.say, on_restart=mon.stop_ev.set)
    mon.updater.acfg = cloud.acfg                         # intervalo e janela da autoatualização (central)
    if sync is not None:
        sync.updater, sync.db = mon.updater, mon.db       # avisos da central (signals/<sid>) acordam os dois
        sync.on_restart = lambda: mon.updater.request_restart("Coleta alterada pela central")
        sync.on_rename = lambda: mon.say("Renomeado pela central: empresa %s, servidor %s" % (
            ident.company or "-", ident.name or "-"))
    if hasattr(signal, "SIGHUP"):                     # (não existe no Windows)
        signal.signal(signal.SIGHUP, signal.SIG_IGN)  # não morre se a sessão SSH cair
    try:
        mon.start_session()
        # benchmark feito (na prioridade normal): daqui em diante, antes de criar qualquer thread
        # (elas herdam), CPU e E/S com a prioridade mínima útil
        mon.priority = lower_priority(ident.sync_cfg()["low_priority"])
        print(mon.priority[:1].upper() + mon.priority[1:] + ".")
        mon.start_compact()
        if mon.updater.start():
            print("Atualização automática: ATIVA (verifica a cada %d min)." % (mon.updater.cur_interval() // 60))
        if sync is not None:
            sync.start()
            c = ident.sync_cfg()
            print("Nuvem: envio automático %s (a cada %d s; %d s em alerta; histórico a cada %d min)." % (
                "ATIVO" if sync.auto else "desativado", c["interval_normal"], c["interval_alert"], c["history_interval"] // 60))
        if mon.db is not None:
            mon.db.start()
            print("Acesso ao banco pela central: %s." % ("liga quando configurado na central" if ident.sync_cfg()["db_access"]
                                                        else "DESLIGADO (sync.db_access)"))
        if mon.sql is not None:
            mon.sql.start()
            c = ident.sync_cfg()
            print("Editor SQL remoto (só leitura): %s." % (
                "liga junto com o acesso ao banco" if c["sql_editor"] and c["db_access"]
                else "DESLIGADO (sync.%s)" % ("sql_editor" if not c["sql_editor"] else "db_access")))
        if mon.sysev is not None:
            mon.sysev.start()
            c = ident.sync_cfg()
            print("Eventos do sistema (admin.system_email): %s." % (
                "ATIVOS (a cada %d s)" % c["sys_events_interval"] if c["sys_events"] and c["db_access"]
                else "DESLIGADOS (sync.%s)" % ("sys_events" if not c["sys_events"] else "db_access")))
        print("\nMonitorando: amostra a cada %ds, 1ª gravação em ~%ds, depois a cada %ds das %dh às %dh e a cada %ds fora"
              " desse horário." % (a.sample, first_samples(a.sample) * a.sample, a.biz_interval, a.biz_start, a.biz_end,
                                   a.interval))
        if dashboard:
            mon.out = None
            mon.start()
            res = run_dashboard(History(log), mon, a, sync, ident)
            if res == "lost":
                # terminal caiu: segue coletando em silêncio até receber SIGTERM/SIGINT
                while mon.thread.is_alive():
                    mon.thread.join(1)
        else:
            print("Ctrl+C para parar.\n")
            mon.start()
            while mon.thread.is_alive():
                mon.thread.join(1)
    except KeyboardInterrupt:
        pass
    finally:
        mon.out = out
        restart = mon.updater.restart.is_set()
        mon.stop(final=not restart)
    if mon.lockf is not None:                           # Windows: solta a trava (<relatório>.lock)
        mon.lockf.close()
    if restart:
        mon.logf.close()                                # libera a trava do relatório antes do novo processo
        reexec(mon.updater.script, mon.updater.version, sys.argv[1:], mon.updater.reason)


if __name__ == "__main__":
    main()
