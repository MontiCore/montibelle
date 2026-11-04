ARG CODE_VERSION="4.106.2"
FROM codercom/code-server:$CODE_VERSION

# Define arguments and provide defaults
ARG SYSML_VERSION="7.8.46"
ARG TOKEN_TYPE="private-token"
ARG TOKEN="<your_access_token>"
ARG OPENAI_API_KEY="<your_openai_api_key>"
ARG CLONE_TOKEN=$TOKEN

USER root

# install java
RUN apt-get update && DEBIAN_FRONTEND="noninteractive" apt-get install -y \
  openjdk-17-jdk-headless \
  python3-full \
  python3-pip \
  python3-venv

# install llm2sysml agent
RUN git clone https://$TOKEN_TYPE:$CLONE_TOKEN@git.rwth-aachen.de/montibelle/frontend/tooling/llm2sysml.git /llm2sysml \
  && git -C /llm2sysml checkout $AGENT_VERSION \
  && chown -R root:root /llm2sysml \
  && chmod -R 700 /llm2sysml

# install llm2sysml requirements
RUN python3 -m venv /home/coder/.venv/llm2sysml \
  && /home/coder/.venv/llm2sysml/bin/python -m pip install --upgrade pip \
  && /home/coder/.venv/llm2sysml/bin/python -m pip install -r /llm2sysml/llm2sysml-agent/requirements.txt

# add llm2sysml envs 
RUN echo "OPENAI_API_KEY=$OPENAI_API_KEY\nCHAT_SESSIONS_DIR=/home/coder/workspace" > /llm2sysml/llm2sysml-agent/.env \
  && chown root:root /llm2sysml/llm2sysml-agent/.env \
  && chmod 600 /llm2sysml/llm2sysml-agent/.env

USER coder

WORKDIR /home/coder/workspace

# configure code-server to run on port 80 and without authentication
RUN mkdir -p /home/coder/.config/code-server \
  && printf "bind-addr: 0.0.0.0:80\nauth: none" > /home/coder/.config/code-server/config.yaml

# add general settings and continue config
RUN mkdir -p /home/coder/.local/share/code-server/User \
           /home/coder/.continue \
 && printf '{\n\
  "remote.autoForwardPorts": false,\n\
  "security.workspace.trust.enabled": false,\n\
  "workbench.editor.enablePreview": false,\n\
  "workbench.startupEditor": "none",\n\
  "workbench.secondarySideBar.defaultVisibility": "hidden",\n\
  "window.menuBarVisibility": "false",\n\
}\n' \
 > /home/coder/.local/share/code-server/User/settings.json \
 && printf 'name: Local Config\n\
version: 1.0.0\n\
schema: v1\n\
models:\n\
  - name: Sysml Agent\n\
    provider: openai\n\
    model: gpt-4____ai-generated\n\
    apiBase: http://localhost:8000/\n' \
 > /home/coder/.continue/config.yaml


# install sysml extension
RUN curl -L --fail --output sysmlv2.vsix -u "$GH_USER:$GH_PA" \
    "https://maven.pkg.github.com/MontiCore/sysmlv2/de/monticore/lang/sysml_v2/language-server/$SYSML_VERSION/language-server-$SYSML_VERSION-vscode.vsix" \
  && code-server --install-extension sysmlv2.vsix \
  && rm sysmlv2.vsix

# install continue extension
RUN code-server --install-extension continue.continue@1.2.22

USER root

# add example model
COPY model.sysml /home/coder/model.sysml

# Copy start script into the container
COPY start.sh /start.sh

# Entfernt den Entry-Point des Codeserver-Images. Ist nötig,
# da wir den Codeserver in start.sh als root unter Nutzer "coder"
# selbst starten. Die Konfigurationsdateien liegen entsprechend in
# /home/coder, der Default-Entry-Point würde aber als root starten,
# deswegen die Config-Datei nicht finden und auf Port 8080 statt 80
# laufen und ein Passwort verlangen.
# FYI, nur relevant für lokales starten des Containers, Kubernetes
# überschreibt den Entry-Point mit "command: [...]"
# Siehe troubleshooting.md#interaktion-von-docker-arguments-mit-entry-points-und-kubernetes-command
ENTRYPOINT []

EXPOSE 80
