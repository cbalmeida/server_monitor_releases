#!/bin/bash
# =============================================================================
#  instalar.sh - instala ou atualiza o usage_monitor neste servidor
#
#  Uso (no servidor, com internet):
#    U=https://api.github.com/repos/cbalmeida/server_monitor_releases/contents/instalar.sh
#    curl -fsSL -H "Accept: application/vnd.github.raw" -o instalar.sh $U
#    bash instalar.sh
#
#  Só instala e dispara: cria a pasta, baixa o programa, registra o monitor como
#  serviço do sistema (systemd: server-monitor.service, volta sozinho quando o
#  servidor reinicia) e abre o painel numa sessão tmux. NÃO faz perguntas: o próprio
#  usage_monitor.py (--configurar) pergunta o que faltar (empresa, nome, Firebase).
#  Sem systemd (ou se o serviço falhar) o monitor roda na sessão tmux, como antes
#  (e, sem systemd, inicia no boot por um @reboot em /etc/cron.d).
#  Atualização: baixa a versão nova e reinicia; configuração e histórico ficam.
#  Antes de tudo o instalador se autoatualiza: se a versão publicada for
#  diferente desta, troca o próprio arquivo e se reexecuta com os mesmos argumentos.
#  Opcional: USAGE_MONITOR_CONFIG=<arquivo JSON> (comando único da central, "Instalar
#  agente") aplica a configuração com --config-json antes de iniciar e apaga o arquivo.
#  Modelos dos comandos que a central mostra: instalacao/comandos.json (mudou o
#  instalador? atualize os modelos).
# =============================================================================
set -u
SELF=$(cd "$(dirname "$0")" && pwd)/$(basename "$0")      # caminho absoluto (o script muda de pasta)
REPO_URL=${USAGE_MONITOR_URL:-https://api.github.com/repos/cbalmeida/server_monitor_releases/contents/usage_monitor.py}
INSTALADOR_URL=${INSTALADOR_URL:-https://api.github.com/repos/cbalmeida/server_monitor_releases/contents/instalar.sh}
SESSAO=monitor

ok()   { echo "  [ok] $*"; }
erro() { echo "  [ERRO] $*" >&2; exit 1; }
SUDO=""
[ "$(id -u)" = 0 ] || SUDO="sudo"

# 0. Autoatualização ------------------------------------------------------------
# Uma vez por execução (INSTALADOR_ATUALIZADO evita laço). Sem internet: segue com esta versão.
if [ -z "${INSTALADOR_ATUALIZADO:-}" ] && command -v curl > /dev/null; then
    NOVO=$(mktemp) || NOVO=""
    if [ -n "$NOVO" ] && curl -fsSL -H "Accept: application/vnd.github.raw" -o "$NOVO" "$INSTALADOR_URL" 2> /dev/null \
        && [ -s "$NOVO" ] && bash -n "$NOVO" 2> /dev/null; then
        if ! cmp -s "$NOVO" "$SELF"; then
            if cat "$NOVO" > "$SELF" 2> /dev/null || $SUDO cp "$NOVO" "$SELF"; then
                rm -f "$NOVO"
                echo "  [ok] instalador atualizado; reiniciando com a versão nova..."
                INSTALADOR_ATUALIZADO=1 exec bash "$SELF" "$@"
            fi
            echo "  [aviso] não consegui gravar $SELF; seguindo com a versão nova sem gravá-la."
            INSTALADOR_ATUALIZADO=1 exec bash "$NOVO" "$@"
        fi
    else
        echo "  [aviso] não consegui verificar atualização do instalador (sem internet?); seguindo com esta versão."
    fi
    rm -f "$NOVO"
fi


# Pasta: a informada; senão uma instalação existente; senão /home/c2/server_monitor (padrão da C2)
if [ $# -ge 1 ]; then
    DIR=$1
else
    ACHADAS=()
    for d in "$PWD" "$HOME/server_monitor" /home/*/server_monitor /opt/server_monitor; do
        [ -f "$d/usage_monitor.py" ] || continue
        d=$(cd "$d" && pwd)
        case " ${ACHADAS[*]-} " in *" $d "*) ;; *) ACHADAS+=("$d") ;; esac
    done
    # a mais usada primeiro (relatório modificado por último)
    if [ ${#ACHADAS[@]} -gt 1 ]; then
        mapfile -t ACHADAS < <(for d in "${ACHADAS[@]}"; do
            echo "$(stat -c %Y "$d"/usage_report_*.log 2> /dev/null | sort -n | tail -1 || echo 0) $d"
        done | sort -rn | cut -d' ' -f2-)
    fi
    if [ ${#ACHADAS[@]} -eq 1 ]; then
        DIR=${ACHADAS[0]}
        echo "Instalação existente encontrada: $DIR (será atualizada)"
    elif [ ${#ACHADAS[@]} -gt 1 ]; then
        DIR=${ACHADAS[0]}                       # a usada por último (sem perguntar)
        echo "Há mais de uma instalação; atualizando a usada por último: $DIR"
        for d in "${ACHADAS[@]:1}"; do echo "  (outra: $d; para ela: bash instalar.sh $d)"; done
    else
        DIR=/home/c2/server_monitor
    fi
fi

echo "=================================================="
echo "        SERVER MONITOR - instalação"
echo "=================================================="
echo "Pasta: $DIR"
echo

# UTF-8 para o tmux e o painel (sem isso, acentos e bordas saem como Ã© / â em servidores com LANG=C)
case "${LC_ALL:-${LC_CTYPE:-${LANG:-}}}" in *[Uu][Tt][Ff]-8*|*[Uu][Tt][Ff]8*) ;; *) export LANG=C.UTF-8 LC_ALL=C.UTF-8 ;; esac

# 1. Requisitos ---------------------------------------------------------------
echo "1. Verificando requisitos"
[ -r /proc/stat ] || erro "este servidor não é Linux."
command -v curl > /dev/null || erro "curl não encontrado (apt-get install curl)."
# Python 3.8+ com curses: o python3 do sistema ou, se ele for antigo, um python3.x instalado ao lado
# (ex.: Ubuntu 18.04 com python3.8 do apt) - sem trocar o python3 do sistema, que o apt usa.
PY=""
for c in python3 python3.13 python3.12 python3.11 python3.10 python3.9 python3.8; do
    p=$(command -v "$c" 2> /dev/null) || continue
    if "$p" -c 'import sys, curses; sys.exit(sys.version_info < (3, 8))' 2> /dev/null; then PY=$p; break; fi
done
[ -n "$PY" ] || erro "precisa de Python 3.8 ou mais novo, com curses (veja 'Preparar o Python' na documentação de instalação)."
ok "python $("$PY" -c 'import platform; print(platform.python_version())') ($PY)"
if ! command -v tmux > /dev/null; then
    echo "  instalando tmux..."
    $SUDO env DEBIAN_FRONTEND=noninteractive apt-get install -y -qq tmux > /dev/null || erro "falha ao instalar tmux."
fi
ok "tmux"

# 2. Pasta e download ---------------------------------------------------------
echo "2. Baixando o programa"
mkdir -p "$DIR" && cd "$DIR" || erro "não consegui criar $DIR"
ATUALIZACAO=0
[ -f usage_monitor.py ] && ATUALIZACAO=1
if tmux has-session -t "$SESSAO" 2> /dev/null; then
    DONO=$(tmux display-message -p -t "$SESSAO" '#{pane_current_path}' 2> /dev/null)
    if [ -n "$DONO" ] && [ "$(cd "$DONO" 2> /dev/null && pwd)" != "$(pwd)" ]; then
        erro "a sessão tmux '$SESSAO' é de outra instalação ($DONO). Rode: bash instalar.sh $DONO"
    fi
    echo "  o monitor está rodando na sessão tmux '$SESSAO': parando para atualizar..."
    tmux send-keys -t "$SESSAO" q; sleep 1; tmux send-keys -t "$SESSAO" q; sleep 3
    tmux send-keys -t "$SESSAO" Enter 2> /dev/null; sleep 1
    tmux kill-session -t "$SESSAO" 2> /dev/null
fi
# serviço systemd desta pasta (v2.13): para antes de trocar o programa (o passo 3 inicia de novo)
UNIDADE=""
if [ -d /run/systemd/system ] && command -v systemctl > /dev/null; then
    for u in /etc/systemd/system/server-monitor*.service; do
        [ -f "$u" ] || continue
        if grep -Fqx "WorkingDirectory=$(pwd)" "$u"; then UNIDADE=$(basename "$u"); break; fi
    done
fi
if [ -n "$UNIDADE" ] && systemctl is-active --quiet "$UNIDADE"; then
    echo "  o monitor está rodando como serviço ($UNIDADE): parando para atualizar..."
    $SUDO systemctl stop "$UNIDADE" || erro "não consegui parar o serviço $UNIDADE (rode com sudo)."
fi
# coletor desta pasta rodando fora do tmux (ex.: num terminal ou nohup): não dá para iniciar outro
for f in usage_report_*.log; do
    [ -f "$f" ] || continue
    if ! "$PY" -c 'import fcntl, sys; fcntl.flock(open(sys.argv[1], "a"), fcntl.LOCK_EX | fcntl.LOCK_NB)' "$f" 2> /dev/null; then
        erro "há um monitor gravando em $DIR/$f fora da sessão tmux '$SESSAO' e do serviço. Pare-o (q duas vezes no painel, ou: pkill -f usage_monitor.py) e rode de novo."
    fi
done
curl -fsSL -H "Accept: application/vnd.github.raw" -o usage_monitor.py.novo "$REPO_URL" \
    || erro "falha no download (sem internet?)."
"$PY" -c 'import ast, sys; ast.parse(open("usage_monitor.py.novo").read())' 2> /dev/null \
    || erro "arquivo baixado está corrompido; tente de novo."
mv usage_monitor.py.novo usage_monitor.py && chmod +x usage_monitor.py
ok "$("$PY" usage_monitor.py --version) em $DIR"
# Configuração pronta (comando único gerado pela central em "Instalar agente"): USAGE_MONITOR_CONFIG = arquivo com
# o JSON de configuração (o mesmo do --config-json). Aplicada antes de iniciar e apagada em seguida; o que faltar
# o monitor pergunta no painel, como sem ela. Sem a variável nada muda.
if [ -n "${USAGE_MONITOR_CONFIG:-}" ]; then
    if [ -f "$USAGE_MONITOR_CONFIG" ]; then
        echo "  aplicando a configuração recebida (empresa, nome, Firebase, chave do catálogo)..."
        if $SUDO "$PY" usage_monitor.py --config-json "$USAGE_MONITOR_CONFIG"; then
            ok "configuração aplicada"
        else
            echo "  [aviso] configuração incompleta: o monitor pergunta o que faltar no painel."
        fi
        rm -f "$USAGE_MONITOR_CONFIG" 2> /dev/null || $SUDO rm -f "$USAGE_MONITOR_CONFIG"
    else
        echo "  [aviso] arquivo de configuração não encontrado ($USAGE_MONITOR_CONFIG): o monitor pergunta no painel."
    fi
    unset USAGE_MONITOR_CONFIG
fi

# 3. Iniciar ------------------------------------------------------------------
echo "3. Iniciando o monitor"
# o que faltar configurar o próprio monitor pergunta aqui (o serviço roda sem terminal)
if [ -t 0 ] && [ -t 1 ]; then
    $SUDO "$PY" usage_monitor.py --configurar \
        || echo "  [aviso] configuração incompleta: o monitor roda assim mesmo; para completar: sudo $PY $DIR/usage_monitor.py --configurar"
fi
PRIMEIRA=0
if [ "$ATUALIZACAO" = 0 ] || ! grep -q "^BENCH" usage_report_*.log 2> /dev/null; then
    PRIMEIRA=1                                 # primeira vez: mede a capacidade (1-3 min)
    echo "  primeira execução: o benchmark mede a capacidade do servidor (1 a 3 minutos)."
fi
# iniciar.sh: roda o monitor (ou só o painel, com --view) e, se ele terminar, mantém a mensagem na tela
{ echo '#!/bin/bash'; echo "PY='$PY'"; } > iniciar.sh
cat >> iniciar.sh <<'INI'
cd "$(dirname "$0")" || exit 1
# painel em UTF-8 (acentos, bordas) mesmo em servidor com LANG vazio/C (ex.: Ubuntu 18.04 mínimo)
case "${LC_ALL:-${LC_CTYPE:-${LANG:-}}}" in *[Uu][Tt][Ff]-8*|*[Uu][Tt][Ff]8*) ;; *) export LANG=C.UTF-8 LC_ALL=C.UTF-8 ;; esac
"$PY" usage_monitor.py "$@"
code=$?
echo
case " $* " in
    *" --view "*) echo "Painel fechado (o monitor continua coletando como serviço). Enter fecha esta janela." ;;
    *) echo "Monitor encerrado (código $code). Enter fecha esta janela." ;;
esac
read -r _
INI
chmod +x iniciar.sh
# serviço do sistema: o monitor registra, inicia e espera o serviço assumir a coleta (0 = ok)
SAIDA=$($SUDO "$PY" usage_monitor.py --instalar-servico 2>&1)
RC=$?
echo "$SAIDA" | grep -v '^SERVICO=' | sed 's/^/  /'
UNIDADE=$(echo "$SAIDA" | sed -n 's/^SERVICO=//p' | tail -1)
if [ "$RC" = 0 ] && [ -n "$UNIDADE" ]; then
    ok "serviço $UNIDADE ativo (inicia sozinho com o servidor)"
    tmux -u new-session -d -s "$SESSAO" "$SUDO bash '$DIR/iniciar.sh' --view"
    sleep 1
    PAINEL="sudo tmux -u new-session -A -s $SESSAO \"bash $DIR/iniciar.sh --view\""
    cat <<FIM

==================================================
 Pronto. O monitor roda como serviço ($UNIDADE) e volta
 sozinho se o servidor reiniciar. Comandos úteis:
   ver o painel ............ $PAINEL
   sair do painel .......... q (ou Ctrl+B e depois D); a coleta continua
   situação do serviço ..... systemctl status $UNIDADE
   parar ................... sudo systemctl stop $UNIDADE   (volta no próximo boot)
   iniciar ................. sudo systemctl start $UNIDADE
   saída do serviço ........ sudo journalctl -u $UNIDADE -n 50
   enviar para a nuvem ..... tecla u no painel
   atualizar ............... sudo bash $DIR/instalar.sh
==================================================
FIM
else
    [ "$RC" = 3 ] || echo "  [aviso] não deu para usar o serviço do sistema; o monitor roda na sessão tmux '$SESSAO' (como antes)."
    ARGS="--no-bench"
    [ "$PRIMEIRA" = 1 ] && ARGS=""
    tmux -u new-session -d -s "$SESSAO" "$SUDO bash '$DIR/iniciar.sh' $ARGS"
    sleep 2
    tmux has-session -t "$SESSAO" 2> /dev/null || erro "a sessão tmux não iniciou."
    ok "rodando na sessão tmux '$SESSAO'"
    cat <<FIM

==================================================
 Pronto. Comandos úteis:
   ver o painel ............ tmux -u attach -t $SESSAO
   sair sem parar o monitor  Ctrl+B e depois D
   enviar para a nuvem ..... tecla u no painel
   parar o monitor ......... q duas vezes, no painel
   atualizar ............... bash $DIR/instalar.sh
   iniciar sem tmux ........ $DIR/iniciar.sh --no-bench
==================================================
FIM
fi
[ "$SELF" -ef "$DIR/instalar.sh" ] || cp "$SELF" "$DIR/instalar.sh" 2> /dev/null
# abre o painel (no modo antigo é ali que o monitor pergunta o que faltar)
if [ -t 0 ] && [ -t 1 ] && tmux has-session -t "$SESSAO" 2> /dev/null; then
    exec tmux -u attach -t "$SESSAO"
fi
echo "Abra o painel com: sudo tmux -u attach -t $SESSAO"
