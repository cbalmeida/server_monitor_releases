# =============================================================================
#  instalar_visualizador.ps1 - visualizador dos relatorios do Server Monitor (Windows)
#
#  No PowerShell:
#    irm https://raw.githubusercontent.com/cbalmeida/server_monitor_releases/master/instalar_visualizador.ps1 | iex
#
#  Instala Python (se faltar) e windows-curses, baixa o programa, guarda o token
#  (somente leitura) e cria o atalho "Server Monitor - Relatorios" na Area de Trabalho.
#  Rodar de novo atualiza o programa.
#  (Mensagens sem acento de proposito: o PowerShell 5 le scripts baixados como ANSI.)
# =============================================================================
function Install-ServerMonitorViewer {
    $Repo = "cbalmeida/server_monitor_dados"
    $Url = "https://api.github.com/repos/cbalmeida/server_monitor_releases/contents/usage_monitor.py"
    $Dir = Join-Path $env:USERPROFILE "server_monitor_viewer"
    [Net.ServicePointManager]::SecurityProtocol = [Net.SecurityProtocolType]::Tls12

    Write-Host "=================================================="
    Write-Host "   SERVER MONITOR - visualizador de relatorios"
    Write-Host "=================================================="
    Write-Host "Pasta: $Dir`n"

    # 1. Python 3.8+ ----------------------------------------------------------
    Write-Host "1. Python"
    function Find-Python {
        foreach ($c in @("py", "python", "python3")) {
            if (Get-Command $c -ErrorAction SilentlyContinue) {
                $ok = & $c -c "import sys; print(sys.version_info >= (3, 8))" 2>$null
                if ($ok -eq "True") { return $c }
            }
        }
        return $null
    }
    $Py = Find-Python
    if (-not $Py) {
        if (Get-Command winget -ErrorAction SilentlyContinue) {
            Write-Host "   instalando Python 3.12 (winget)..."
            winget install -e --id Python.Python.3.12 --scope user --accept-source-agreements --accept-package-agreements | Out-Null
            $env:Path = [Environment]::GetEnvironmentVariable("Path", "Machine") + ";" + [Environment]::GetEnvironmentVariable("Path", "User")
            $Py = Find-Python
        }
        if (-not $Py) {
            Write-Host "   [ERRO] Instale o Python 3 em https://www.python.org/downloads/"
            Write-Host "          (marque 'Add python.exe to PATH') e rode este script de novo."
            return
        }
    }
    Write-Host "   [ok] $(& $Py --version)"

    # 2. curses para Windows ----------------------------------------------------
    Write-Host "2. Biblioteca de tela (windows-curses)"
    & $Py -m pip install --user --quiet --disable-pip-version-check windows-curses
    $ok = & $Py -c "import curses; print('ok')" 2>$null
    if ($ok -ne "ok") { Write-Host "   [ERRO] falha ao instalar windows-curses."; return }
    Write-Host "   [ok]"

    # 3. Programa ---------------------------------------------------------------
    Write-Host "3. Baixando o programa"
    New-Item -ItemType Directory -Force -Path $Dir | Out-Null
    $Prog = Join-Path $Dir "usage_monitor.py"
    try {
        # API em JSON + base64: sem cabecalho especial (o PowerShell 5.1 restringe o Accept) e sem cache antigo
        $j = Invoke-RestMethod -UseBasicParsing -Uri $Url
        [IO.File]::WriteAllBytes("$Prog.novo", [Convert]::FromBase64String(($j.content -replace "\s", "")))
    } catch { Write-Host "   [ERRO] falha no download: $_"; return }
    Move-Item -Force "$Prog.novo" $Prog
    Write-Host "   [ok] $(& $Py $Prog --version)"

    # 4. Acesso ao repositorio privado dos relatorios ---------------------------
    Write-Host "4. Acesso aos relatorios ($Repo)"
    [IO.File]::WriteAllText((Join-Path $Dir "server_monitor.json"), "{`"cloud_repo`": `"$Repo`"}`n")
    $TokFile = Join-Path $Dir "server_monitor.token"
    if (Test-Path $TokFile) {
        Write-Host "   [ok] token ja configurado (para trocar, apague $TokFile e rode de novo)"
    } else {
        Write-Host "   Cole o token do GitHub (somente leitura). Ele nao aparece na tela."
        $sec = Read-Host "   Token" -AsSecureString
        $tok = [Runtime.InteropServices.Marshal]::PtrToStringAuto([Runtime.InteropServices.Marshal]::SecureStringToBSTR($sec))
        if (-not $tok) { Write-Host "   [ERRO] token vazio."; return }
        [IO.File]::WriteAllText($TokFile, $tok.Trim())
        icacls $TokFile /inheritance:r /grant:r "$($env:USERNAME):(R,W)" | Out-Null   # so este usuario le
        Write-Host "   [ok] token salvo (acesso so deste usuario)"
    }

    # 5. Atalhos ----------------------------------------------------------------
    Write-Host "5. Atalhos"
    $Bat = Join-Path $Dir "ver_relatorios.bat"
    [IO.File]::WriteAllText($Bat, "@echo off`r`ncd /d `"%~dp0`"`r`nset PYTHONUTF8=1`r`n$Py usage_monitor.py --cloud %*`r`necho.`r`npause`r`n")
    $Upd = Join-Path $Dir "atualizar.bat"
    [IO.File]::WriteAllText($Upd, "@echo off`r`npowershell -NoProfile -ExecutionPolicy Bypass -Command `"irm https://raw.githubusercontent.com/cbalmeida/server_monitor_releases/master/instalar_visualizador.ps1 | iex`"`r`npause`r`n")
    $Lnk = Join-Path ([Environment]::GetFolderPath("Desktop")) "Server Monitor - Relatorios.lnk"
    $sh = (New-Object -ComObject WScript.Shell).CreateShortcut($Lnk)
    $sh.TargetPath = $Bat; $sh.WorkingDirectory = $Dir; $sh.Save()
    Write-Host "   [ok] atalho na Area de Trabalho: Server Monitor - Relatorios"

    Write-Host "`n=================================================="
    Write-Host " Pronto. Para ver os relatorios: duplo clique no atalho da Area de Trabalho"
    Write-Host " (ou $Bat). Para atualizar: $Upd"
    Write-Host " Dica: use o 'Terminal do Windows' para a melhor aparencia; se aparecerem"
    Write-Host " quadrados nos graficos, abra o painel com --compat."
    Write-Host "=================================================="
    $r = Read-Host "Abrir agora? [S/n]"
    if ($r -notmatch '^[nN]') {
        Push-Location $Dir
        $env:PYTHONUTF8 = "1"
        & $Py usage_monitor.py --cloud
        Pop-Location
    }
}
Install-ServerMonitorViewer
