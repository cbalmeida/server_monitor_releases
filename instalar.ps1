# =============================================================================
#  instalar.ps1 - instala ou atualiza o usage_monitor num servidor WINDOWS
#                 (Windows 7 / Server 2008 R2 ou mais novo; PowerShell 2.0+)
#
#  No PowerShell COMO ADMINISTRADOR (uma linha; funciona no PowerShell 2.0):
#    [Net.ServicePointManager]::SecurityProtocol = [Net.ServicePointManager]::SecurityProtocol -bor 3072; $w = New-Object Net.WebClient; $w.Headers.Add("User-Agent", "c2"); $w.Headers.Add("Accept", "application/vnd.github.raw"); $w.DownloadFile("https://api.github.com/repos/cbalmeida/server_monitor_releases/contents/instalar.ps1", "$env:TEMP\instalar.ps1"); powershell -NoProfile -ExecutionPolicy Bypass -File "$env:TEMP\instalar.ps1"
#
#  Opcoes:  -Dir C:\outra\pasta   (padrao C:\c2\server_monitor)
#           -Parar                (para o monitor e a tarefa agendada; nao remove nada)
#           -Desinstalar          (para e remove a tarefa agendada; a pasta com relatorio e configuracao fica)
#
#  So instala e dispara: baixa o Python 3.8.10 "embeddable" oficial (confere o SHA-256), baixa o
#  usage_monitor.py, abre o proprio monitor no console para ele perguntar o que faltar (JSON de
#  configuracao: empresa, nome, Firebase, chave do catalogo) e registra a tarefa agendada
#  "C2 Server Monitor" (ao iniciar o Windows, como SYSTEM, sem limite de tempo, reinicia em falha) que
#  roda: python.exe -X utf8 usage_monitor.py --service --no-bench
#  O instalador NAO faz perguntas. Rodar de novo atualiza (configuracao e historico ficam).
#  Antes de tudo se autoatualiza (versao publicada diferente = troca o proprio arquivo e se reexecuta).
#  Opcional: $env:USAGE_MONITOR_CONFIG = arquivo JSON (comando unico da central, "Instalar agente"): aplicado com
#  --config-json antes do --configurar e apagado. Modelos dos comandos da central: instalacao/comandos.json
#  (mudou o instalador? atualize os modelos).
#  (Sem acentos de proposito: o PowerShell le scripts baixados como ANSI.)
# =============================================================================
param([string]$Dir = "C:\C2Tecnologia\ServerMonitor", [switch]$Parar, [switch]$Desinstalar)

# "Continue": com "Stop", qualquer linha no stderr de um programa (2>&1) viraria erro fatal no PowerShell 2-5;
# os erros que importam sao tratados com try/catch e $LASTEXITCODE.
$ErrorActionPreference = "Continue"
$Self = $MyInvocation.MyCommand.Path                  # vazio quando rodado por "iex" (sem arquivo)
$ApiBase = "https://api.github.com/repos/cbalmeida/server_monitor_releases/contents"
$ProgUrl = $ApiBase + "/usage_monitor.py"
if ($env:USAGE_MONITOR_URL) { $ProgUrl = $env:USAGE_MONITOR_URL }
$InstUrl = $ApiBase + "/instalar.ps1"
if ($env:INSTALADOR_URL) { $InstUrl = $env:INSTALADOR_URL }
$TaskName = "C2 Server Monitor"
$PyVersion = "3.8.10"
# SHA-256 dos pacotes oficiais (python.org/ftp/python/3.8.10/), conferidos em 2026-11-08 contra a assinatura
# GPG do release manager do Windows (Steve Dower, 7ED10B6531D7C8E1BC296021FC624643487034E5).
$PyHash = @{
    "amd64" = "abbe314e9b41603dde0a823b76f5bbbe17b3de3e5ac4ef06b759da5466711271";
    "win32" = "760dc79bcb434ee80b1001a30bb6f798287881851bac6d8137867894d40ef1fc"
}

function Ok($m)    { Write-Host "  [ok] $m" }
function Aviso($m) { Write-Host "  [aviso] $m" -ForegroundColor Yellow }
function Erro($m)  { Write-Host "  [ERRO] $m" -ForegroundColor Red; exit 1 }

function Set-Tls12 {
    # TLS 1.2 (GitHub e python.org recusam TLS 1.0). 3072 = Tls12, mesmo no .NET 3.5 do PowerShell 2.0,
    # desde que o Windows tenha o KB3154518 (7/2008 R2) ou o .NET 4.5+ (com WMF 3.0+).
    try {
        [Net.ServicePointManager]::SecurityProtocol = [Net.ServicePointManager]::SecurityProtocol -bor 3072
        return $true
    } catch {
        return $false
    }
}

function New-Web {
    $w = New-Object Net.WebClient
    $w.Headers.Add("User-Agent", "c2-server-monitor-instalador")
    return $w
}

function Get-GitHubFile($url, $dest) {
    # API "contents": pede o arquivo cru (Accept raw); se vier o JSON (proxy/.NET que ignore o Accept),
    # decodifica o campo "content" (base64) sem ConvertFrom-Json (nao existe no PowerShell 2.0).
    $w = New-Web
    $w.Headers.Add("Accept", "application/vnd.github.raw")
    $bytes = $w.DownloadData($url)
    $text = [Text.Encoding]::UTF8.GetString($bytes)
    if ($text.TrimStart().StartsWith("{") -and $text -match '"content"\s*:\s*"([^"]*)"') {
        $bytes = [Convert]::FromBase64String(($matches[1] -replace '\\n', '' -replace '\s', ''))
    }
    [IO.File]::WriteAllBytes($dest, $bytes)
}

function Get-Sha256($path) {
    $sha = [Security.Cryptography.SHA256]::Create()
    $fs = [IO.File]::OpenRead($path)
    try { $h = $sha.ComputeHash($fs) } finally { $fs.Close() }
    return ([BitConverter]::ToString($h) -replace "-", "").ToLower()
}

function Expand-Zip($zip, $dest) {
    New-Item -ItemType Directory -Force -Path $dest | Out-Null
    try {
        Add-Type -AssemblyName System.IO.Compression.FileSystem           # .NET 4.5+
        $z = [IO.Compression.ZipFile]::OpenRead($zip)
        try {
            foreach ($e in $z.Entries) {
                $t = Join-Path $dest $e.FullName
                if ($e.Name -eq "") { New-Item -ItemType Directory -Force -Path $t | Out-Null; continue }
                New-Item -ItemType Directory -Force -Path (Split-Path $t) | Out-Null
                [IO.Compression.ZipFileExtensions]::ExtractToFile($e, $t, $true)
            }
        } finally { $z.Dispose() }
    } catch {
        $shell = New-Object -ComObject Shell.Application                  # Windows 7 com .NET 3.5
        $items = $shell.NameSpace($zip).Items()
        $shell.NameSpace($dest).CopyHere($items, 0x14)                     # sem janela, sobrescreve
        for ($i = 0; $i -lt 60 -and -not (Test-Path (Join-Path $dest "python.exe")); $i++) { Start-Sleep -Seconds 1 }
    }
}

function Find-Python {
    $p = Join-Path $Dir "python\python.exe"
    if (Test-Path $p) { return $p }
    return $null
}

function Stop-Monitor($py) {
    # pedido de parada normal (grava a janela parcial e avisa a central), depois encerra a tarefa
    $prog = Join-Path $Dir "usage_monitor.py"
    if ($py -and (Test-Path $prog)) {
        & $py -X utf8 $prog --parar 2>&1 | ForEach-Object { Write-Host "  $_" }
    }
    cmd /c "schtasks /End /TN `"$TaskName`" >nul 2>&1" | Out-Null
}

function Update-Roots {
    # O Python le os certificados raiz do repositorio do Windows, mas nao baixa os que faltam; o .NET (CryptoAPI)
    # baixa. Uma conexao HTTPS pelo .NET a cada servico usado instala as raizes num Windows 7/2008 R2 sem
    # atualizacoes (resposta 401/404 nao importa: o que conta e o TLS).
    foreach ($u in @("https://c2-server-monitor-default-rtdb.firebaseio.com/.json",
                     "https://identitytoolkit.googleapis.com/", "https://securetoken.googleapis.com/",
                     "https://api.github.com/")) {
        try { [void](New-Web).DownloadString($u) } catch { }
    }
}

function Test-Admin {
    $id = [Security.Principal.WindowsIdentity]::GetCurrent()
    return (New-Object Security.Principal.WindowsPrincipal($id)).IsInRole([Security.Principal.WindowsBuiltInRole]::Administrator)
}

Write-Host "=================================================="
Write-Host "   SERVER MONITOR (Windows) - instalacao"
Write-Host "=================================================="
if (-not (Test-Admin)) { Erro "rode no PowerShell como Administrador (botao direito > Executar como administrador)." }
if (-not (Set-Tls12)) {
    Aviso "este .NET nao habilita TLS 1.2 (instale o KB3154518 ou o .NET Framework 4.5+ e o WMF 5.1); os downloads podem falhar."
}

# 0. Autoatualizacao ------------------------------------------------------------
# Uma vez por execucao (INSTALADOR_ATUALIZADO evita laco). Sem internet: segue com esta versao.
if ($Self -and -not $env:INSTALADOR_ATUALIZADO) {
    $novo = [IO.Path]::GetTempFileName()
    try {
        Get-GitHubFile $InstUrl $novo
        $txt = [IO.File]::ReadAllText($novo)
        $errs = $null
        [void][Management.Automation.PSParser]::Tokenize($txt, [ref]$errs)
        if ($txt.Length -gt 0 -and $errs.Count -eq 0 -and $txt -ne [IO.File]::ReadAllText($Self)) {
            Copy-Item -Force $novo $Self
            Ok "instalador atualizado; reiniciando com a versao nova..."
            $env:INSTALADOR_ATUALIZADO = "1"
            $a = @("-NoProfile", "-ExecutionPolicy", "Bypass", "-File", $Self, "-Dir", $Dir)
            if ($Parar) { $a += "-Parar" }
            if ($Desinstalar) { $a += "-Desinstalar" }
            & powershell @a
            exit $LASTEXITCODE
        }
    } catch {
        Aviso "nao consegui verificar atualizacao do instalador ($($_.Exception.Message)); seguindo com esta versao."
    } finally {
        Remove-Item -Force $novo -ErrorAction SilentlyContinue
    }
}

# Instalacao antiga (padrao ate a 2.8.1: C:\c2\server_monitor): sem -Dir explicito, parar/desinstalar agem nela
# e a instalacao/atualizacao a move para a pasta nova (mesma maquina: configuracao, historico e Python vao juntos).
$OldDir = "C:\c2\server_monitor"
if (-not $PSBoundParameters.ContainsKey("Dir") -and -not (Test-Path (Join-Path $Dir "usage_monitor.py")) -and
    (Test-Path (Join-Path $OldDir "usage_monitor.py"))) {
    if ($Parar -or $Desinstalar) {
        $Dir = $OldDir
    } else {
        Write-Host "Instalacao antiga em $OldDir`: movendo para $Dir ..."
        $novoDir = $Dir; $Dir = $OldDir
        Stop-Monitor (Find-Python)
        $Dir = $novoDir
        $pai = Split-Path $Dir -Parent
        if (-not (Test-Path $pai)) { New-Item -ItemType Directory -Force -Path $pai | Out-Null }
        $movido = $false
        for ($i = 0; $i -lt 15 -and -not $movido; $i++) {
            try { Move-Item -Path $OldDir -Destination $Dir -ErrorAction Stop; $movido = $true }
            catch { Start-Sleep -Seconds 2 }                  # o monitor ainda fechando arquivos
        }
        if (-not $movido) { Erro "nao consegui mover $OldDir para $Dir (arquivo em uso?). Pare o monitor e rode de novo." }
        Ok "instalacao movida para $Dir"
    }
}
Write-Host "Pasta: $Dir`n"
$Py = Find-Python

if ($Parar -or $Desinstalar) {
    Write-Host "Parando o monitor..."
    Stop-Monitor $Py
    if ($Desinstalar) {
        cmd /c "schtasks /Delete /TN `"$TaskName`" /F >nul 2>&1" | Out-Null
        Ok "tarefa agendada '$TaskName' removida."
        Write-Host "  A pasta $Dir foi mantida (relatorio, configuracao, Python). Para remover tudo, apague-a."
        Write-Host "  O servidor continua cadastrado no Firebase (a central o mostra como OFFLINE/parado)."
    } else {
        Ok "monitor parado (a tarefa continua registrada e volta no proximo boot; para iniciar ja: schtasks /Run /TN `"$TaskName`")."
    }
    exit 0
}

# 1. Requisitos -----------------------------------------------------------------
Write-Host "1. Verificando requisitos"
$v = [Environment]::OSVersion.Version
if ($v.Major -lt 6 -or ($v.Major -eq 6 -and $v.Minor -lt 1)) { Erro "Windows $v nao suportado (minimo: Windows 7 / Server 2008 R2)." }
$arch = "win32"
if ($env:PROCESSOR_ARCHITECTURE -eq "AMD64" -or $env:PROCESSOR_ARCHITEW6432 -eq "AMD64") { $arch = "amd64" }
Ok "Windows $v ($arch), PowerShell $($PSVersionTable.PSVersion)"
# Universal C Runtime (o Python 3.8 precisa; vem no Windows 10/2016+; no 7/2008 R2/8.1/2012 e o KB2999226)
$sys32 = Join-Path $env:windir "System32"
if ((Test-Path (Join-Path $env:windir "Sysnative")) -and $arch -eq "amd64") { $sys32 = Join-Path $env:windir "Sysnative" }
# No Windows 10/2016+ o UCRT faz parte do sistema (ucrtbase.dll; as api-ms-win-crt-* sao "API sets" virtuais,
# sem arquivo em System32). So no 7/2008 R2/8/8.1/2012 ele pode faltar: confere o ucrtbase.dll (ou a DLL antiga).
$temUcrt = ($v.Major -ge 10) -or (Test-Path (Join-Path $sys32 "ucrtbase.dll")) -or
           (Test-Path (Join-Path $sys32 "api-ms-win-crt-runtime-l1-1-0.dll"))
if (-not $temUcrt) {
    Erro ("falta o Universal C Runtime (api-ms-win-crt-runtime-l1-1-0.dll). Instale a atualizacao KB2999226 " +
          "(Windows 7/2008 R2 precisam do Service Pack 1, KB976932) pelo Windows Update ou pelo Catalogo do " +
          "Microsoft Update, reinicie e rode este instalador de novo.")
}
Ok "Universal C Runtime"
Update-Roots
Ok "certificados raiz (Firebase, Google, GitHub) verificados pelo Windows"

# 2. Python 3.8.10 embeddable (dentro da pasta; nao mexe em outro Python da maquina) ---------------
Write-Host "2. Python $PyVersion ($arch, embeddable)"
New-Item -ItemType Directory -Force -Path $Dir | Out-Null
$pyOk = $false
if ($Py) {
    $out = & $Py -c "import sys; print('%d.%d.%d' % sys.version_info[:3])" 2>$null
    if ($out -eq $PyVersion) { $pyOk = $true; Ok "ja instalado ($Py)" }
}
if (-not $pyOk) {
    $zipName = "python-$PyVersion-embed-$arch.zip"
    $zip = Join-Path $Dir $zipName
    if (-not (Test-Path $zip)) {
        try {
            (New-Web).DownloadFile("https://www.python.org/ftp/python/$PyVersion/$zipName", $zip)
        } catch {
            Erro ("falha ao baixar o Python ($($_.Exception.Message)). Sem TLS 1.2/internet: baixe " +
                  "https://www.python.org/ftp/python/$PyVersion/$zipName em outra maquina, copie para $Dir e rode de novo.")
        }
    }
    $h = Get-Sha256 $zip
    if ($h -ne $PyHash[$arch]) {
        Remove-Item -Force $zip
        Erro "o arquivo do Python nao confere (SHA-256 $h). Download corrompido ou adulterado; rode de novo."
    }
    Ok "SHA-256 conferido"
    $pdir = Join-Path $Dir "python"
    if (Test-Path $pdir) { Remove-Item -Recurse -Force $pdir }
    Expand-Zip $zip $pdir
    Remove-Item -Force $zip
    $Py = Find-Python
    if (-not $Py) { Erro "nao consegui extrair o Python em $pdir." }
}
$out = & $Py -c "import sys, ctypes, ssl, sqlite3; print('python-ok')" 2>&1
if ("$out" -notmatch "python-ok") {
    Erro ("o Python nao executa neste Windows ($out). No Windows 7/2008 R2: instale o Service Pack 1 (KB976932), " +
          "o KB2533623 (ou o KB3063858, que o substitui) e o KB2999226 (Universal C Runtime), reinicie e rode de novo.")
}
Ok "Python executa ($Py)"

# 3. Programa ---------------------------------------------------------------------
Write-Host "3. Baixando o programa"
$Prog = Join-Path $Dir "usage_monitor.py"
$atualizacao = Test-Path $Prog
Stop-Monitor $Py                                            # coletor em execucao: para antes de trocar
try { Get-GitHubFile $ProgUrl "$Prog.novo" } catch { Erro "falha no download do programa ($($_.Exception.Message))." }
$chk = & $Py -c "import ast, sys; ast.parse(open(sys.argv[1], encoding='utf-8').read(), feature_version=(3, 8)); print('ok')" "$Prog.novo" 2>&1
if ("$chk" -ne "ok") { Remove-Item -Force "$Prog.novo"; Erro "arquivo baixado esta corrompido ($chk); tente de novo." }
Move-Item -Force "$Prog.novo" $Prog
Ok "$(& $Py -X utf8 $Prog --version) em $Dir"
$inst = Join-Path $Dir "instalar.ps1"
if ($Self) {
    if ($Self -ne $inst) { Copy-Item -Force $Self $inst }
} else {
    try { Get-GitHubFile $InstUrl $inst } catch { Aviso "nao consegui guardar o instalador em $inst." }
}

# so SYSTEM e Administradores acessam a pasta (segredos: server_monitor.live, .catkey, .token)
# SIDs em vez de nomes: funciona em Windows de qualquer idioma
cmd /c "icacls `"$Dir`" /inheritance:r /grant:r *S-1-5-18:(OI)(CI)F *S-1-5-32-544:(OI)(CI)F >nul 2>&1" | Out-Null
if ($LASTEXITCODE -ne 0) { Aviso "nao consegui restringir as permissoes de $Dir (icacls)." } else { Ok "permissoes: so SYSTEM e Administradores" }

# 4. Configuracao (quem pergunta e o monitor) -------------------------------------------
Write-Host "4. Configuracao (o monitor pergunta o que faltar; cole o JSON de configuracao)"
Push-Location $Dir
try {
    # Configuracao pronta (comando unico gerado pela central em "Instalar agente"): USAGE_MONITOR_CONFIG = arquivo
    # com o JSON de configuracao (o mesmo do --config-json). Aplicada e apagada; o --configurar a seguir so
    # pergunta o que ainda faltar. Sem a variavel nada muda.
    $cfg = $env:USAGE_MONITOR_CONFIG
    if ($cfg) {
        if (Test-Path $cfg) {
            Write-Host "  aplicando a configuracao recebida (empresa, nome, Firebase, chave do catalogo)..."
            & $Py -X utf8 $Prog --config-json $cfg
            if ($LASTEXITCODE -eq 0) { Ok "configuracao aplicada" } else { Aviso "configuracao incompleta: o monitor pergunta o que faltar." }
            Remove-Item -Force $cfg -ErrorAction SilentlyContinue
        } else {
            Aviso "arquivo de configuracao nao encontrado ($cfg): o monitor pergunta o que faltar."
        }
        $env:USAGE_MONITOR_CONFIG = $null
    }
    & $Py -X utf8 $Prog --configurar
} finally { Pop-Location }
if ($LASTEXITCODE -ne 0) {
    Aviso "configuracao incompleta: o monitor roda assim mesmo; para completar: `"$Py`" -X utf8 `"$Prog`" --configurar"
}

# 5. Tarefa agendada (XML: sem limite de 72 h do schtasks, reinicia em falha, nao para na bateria) -----
Write-Host "5. Tarefa agendada '$TaskName'"
$e = [Security.SecurityElement]
$xml = @"
<?xml version="1.0" encoding="UTF-16"?>
<Task version="1.2" xmlns="http://schemas.microsoft.com/windows/2004/02/mit/task">
  <RegistrationInfo><Description>C2 Server Monitor: coleta de CPU, memoria e espaco, envio a central e acesso ao banco.</Description></RegistrationInfo>
  <Triggers><BootTrigger><Enabled>true</Enabled><Delay>PT30S</Delay></BootTrigger></Triggers>
  <Principals><Principal id="Author"><UserId>S-1-5-18</UserId><RunLevel>HighestAvailable</RunLevel></Principal></Principals>
  <Settings>
    <MultipleInstancesPolicy>IgnoreNew</MultipleInstancesPolicy>
    <DisallowStartIfOnBatteries>false</DisallowStartIfOnBatteries>
    <StopIfGoingOnBatteries>false</StopIfGoingOnBatteries>
    <AllowHardTerminate>true</AllowHardTerminate>
    <StartWhenAvailable>true</StartWhenAvailable>
    <RunOnlyIfNetworkAvailable>false</RunOnlyIfNetworkAvailable>
    <IdleSettings><StopOnIdleEnd>false</StopOnIdleEnd><RestartOnIdle>false</RestartOnIdle></IdleSettings>
    <AllowStartOnDemand>true</AllowStartOnDemand>
    <Enabled>true</Enabled>
    <Hidden>false</Hidden>
    <RunOnlyIfIdle>false</RunOnlyIfIdle>
    <WakeToRun>false</WakeToRun>
    <ExecutionTimeLimit>PT0S</ExecutionTimeLimit>
    <Priority>7</Priority>
    <RestartOnFailure><Interval>PT1M</Interval><Count>999</Count></RestartOnFailure>
  </Settings>
  <Actions Context="Author">
    <Exec>
      <Command>$($e::Escape($Py))</Command>
      <Arguments>-X utf8 "$($e::Escape($Prog))" --service --no-bench</Arguments>
      <WorkingDirectory>$($e::Escape($Dir))</WorkingDirectory>
    </Exec>
  </Actions>
</Task>
"@
$xf = Join-Path $env:TEMP "c2_server_monitor_task.xml"
[IO.File]::WriteAllText($xf, $xml, [Text.Encoding]::Unicode)       # schtasks /XML espera UTF-16
$r = cmd /c "schtasks /Create /TN `"$TaskName`" /XML `"$xf`" /F 2>&1"
$rc = $LASTEXITCODE
Remove-Item -Force $xf -ErrorAction SilentlyContinue
if ($rc -ne 0) { Erro "falha ao registrar a tarefa agendada: $r" }
Ok "registrada (ao iniciar o Windows, como SYSTEM)"
$r = cmd /c "schtasks /Run /TN `"$TaskName`" 2>&1"
if ($LASTEXITCODE -ne 0) { Erro "falha ao iniciar a tarefa: $r" }
Start-Sleep -Seconds 8
$log = Join-Path $Dir "server_monitor_servico.log"
if (Test-Path $log) { Get-Content -Encoding UTF8 $log | Select-Object -Last 5 | ForEach-Object { Write-Host "    $_" } }
Ok "monitor rodando em segundo plano"

Write-Host @"

==================================================
 Pronto. Comandos uteis (PowerShell como Administrador):
   diagnostico ......... & "$Py" -X utf8 "$Prog" --diagnostico
   configurar .......... & "$Py" -X utf8 "$Prog" --configurar
   saida do servico .... Get-Content -Encoding UTF8 "$log" | Select-Object -Last 30
   parar ............... powershell -ExecutionPolicy Bypass -File "$Dir\instalar.ps1" -Parar
   iniciar ............. schtasks /Run /TN "$TaskName"
   desinstalar ......... powershell -ExecutionPolicy Bypass -File "$Dir\instalar.ps1" -Desinstalar
   atualizar ........... powershell -ExecutionPolicy Bypass -File "$Dir\instalar.ps1"
 O monitor se atualiza sozinho (verifica a cada 10 min).
==================================================
"@
