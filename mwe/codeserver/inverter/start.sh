#!/bin/sh

umask 000

set -e

: "${IVE_VERSION:?IVE version is not set}"
: "${BACKBONE_VERSION:?Backbone version is not set}"

export USER_HOME=/home/isabelle
export ISABELLE_HOME_USER="$USER_HOME/.isabelle"
export PATH="/home/isabelle/Isabelle/bin:$PATH"
export PATH="/usr/local/bin:${PATH}"

PROJECT_DIR="/builds/montibelle/case-studies/sysml/doubleinverter"
PROJECT_TEMPLATE_DIR="/opt/templates/doubleinverter"
if [ ! -f "$PROJECT_DIR/build.gradle" ]; then
  mkdir -p "$PROJECT_DIR"
  cp -a "$PROJECT_TEMPLATE_DIR/." "$PROJECT_DIR/"
  chown -R isabelle:isabelle "$PROJECT_DIR"
fi

java -jar /home/isabelle/.local/share/code-server/extensions/montibelle.ive-$IVE_VERSION/bin/backbone-$BACKBONE_VERSION.jar &

mkdir -p "$PROJECT_DIR/target/logs"
cd /llm2sysml/llm2sysml-agent \
  && /home/isabelle/.venv/llm2sysml/bin/python main.py \
  > "$PROJECT_DIR/target/logs/agent.log" 2>&1 &

exec runuser -u isabelle -- code-server "$PROJECT_DIR"
