#!/bin/bash
# =============================================================================
#  instalar_visualizador.sh - visualizador dos relatórios do Server Monitor
#  (Mac ou Linux; para Windows use instalar_visualizador.ps1)
#
#    U=https://api.github.com/repos/cbalmeida/server_monitor_releases/contents/instalar_visualizador.sh
#    curl -fsSL -H "Accept: application/vnd.github.raw" -o instalar_visualizador.sh $U
#    bash instalar_visualizador.sh
#
#  Baixa o programa, guarda o token (somente leitura) e cria o atalho
#  ver_relatorios.sh. Rodar de novo atualiza o programa.
# =============================================================================
set -u
SELF=$(cd "$(dirname "$0")" && pwd)/$(basename "$0")      # caminho absoluto (o script muda de pasta)
REPO=cbalmeida/server_monitor_dados
URL=https://api.github.com/repos/cbalmeida/server_monitor_releases/contents/usage_monitor.py
DIR=${1:-$HOME/server_monitor_viewer}
erro() { echo "  [ERRO] $*" >&2; exit 1; }
[ -t 0 ] || erro "rode com 'bash instalar_visualizador.sh' (o script faz perguntas)."

echo "=================================================="
echo "   SERVER MONITOR - visualizador de relatórios"
echo "=================================================="
echo "Pasta: $DIR"; echo

echo "1. Python"
command -v python3 > /dev/null || erro "instale o Python 3 (Mac: xcode-select --install; Linux: apt-get install python3)."
python3 -c 'import sys, curses; sys.exit(sys.version_info < (3, 8))' 2> /dev/null || erro "precisa de Python 3.8 ou mais novo, com curses."
echo "  [ok] $(python3 --version)"

echo "2. Baixando o programa"
mkdir -p "$DIR" && cd "$DIR" || erro "não consegui criar $DIR"
curl -fsSL -H "Accept: application/vnd.github.raw" -o usage_monitor.py.novo "$URL" || erro "falha no download."
mv usage_monitor.py.novo usage_monitor.py && chmod +x usage_monitor.py
echo "  [ok] $(python3 usage_monitor.py --version)"

echo "3. Acesso aos relatórios ($REPO)"
umask 077
printf '{"cloud_repo": "%s"}\n' "$REPO" > server_monitor.json
if [ -s server_monitor.token ]; then
    echo "  [ok] token já configurado (para trocar, apague server_monitor.token e rode de novo)"
else
    read -r -s -p "  Cole o token do GitHub (somente leitura; não aparece na tela): " TOKEN; echo
    [ -n "$TOKEN" ] || erro "token vazio."
    printf '%s\n' "$TOKEN" > server_monitor.token
    echo "  [ok] token salvo (permissão 600)"
fi

echo "4. Atalho"
cat > ver_relatorios.sh <<INI
#!/bin/bash
cd "$DIR" && python3 usage_monitor.py --cloud "\$@"
INI
chmod 700 ver_relatorios.sh
if [ "$(uname)" = Darwin ] && [ -d "$HOME/Desktop" ]; then     # duplo clique no Finder
    cp ver_relatorios.sh "$HOME/Desktop/Server Monitor - Relatórios.command"
    echo "  [ok] atalho na Mesa: Server Monitor - Relatórios"
fi
echo "  [ok] $DIR/ver_relatorios.sh"
cat <<FIM

==================================================
 Pronto. Para ver os relatórios:  $DIR/ver_relatorios.sh
 Para atualizar:                   bash $DIR/instalar_visualizador.sh
==================================================
FIM
[ "$SELF" -ef "$DIR/instalar_visualizador.sh" ] || cp "$SELF" "$DIR/instalar_visualizador.sh" 2> /dev/null
read -r -p "Abrir agora? [S/n] " R
case "$R" in n|N) ;; *) exec ./ver_relatorios.sh ;; esac
