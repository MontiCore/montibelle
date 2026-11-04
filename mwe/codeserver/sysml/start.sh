#!/bin/sh

umask 000

set -e

if [ ! -f /home/coder/workspace/model.sysml ]; then
  mv /home/coder/model.sysml /home/coder/workspace/model.sysml
  chown coder:coder /home/coder/workspace/model.sysml
  chmod 666 /home/coder/workspace/model.sysml
fi

cd /llm2sysml/llm2sysml-agent \
  && /home/coder/.venv/llm2sysml/bin/python main.py \
  > /home/coder/workspace/agent.log 2>&1 &

exec runuser -u coder -- code-server "/home/coder/workspace"
