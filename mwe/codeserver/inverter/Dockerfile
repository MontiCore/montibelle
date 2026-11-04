FROM registry.git.rwth-aachen.de/montibelle/frontend/tooling/autosledgi-python:3.1.26

# Define arguments and provide defaults
ARG SYSML_VERSION="7.8.109"
ARG IVE_VERSION="1.3.9"
ARG BACKBONE_VERSION="3.0.21"
ARG TRANSFORMER_VERSION="3.0.0-SNAPSHOT"
ARG INVERTER_VERSION="cabb602"
ARG AGENT_VERSION="d8a1f17f"
ARG CODE_VERSION="4.144.0"
ARG CONTINUE_VERSION="2.0.0"
ARG TOKEN_TYPE="private-token"
ARG TOKEN="<your_access_token>"
ARG OPENAI_API_KEY="<your_openai_api_key>"
ARG CLONE_TOKEN=$TOKEN

# Set Ive and Backbone version to environment variables for the start script
ENV IVE_VERSION=$IVE_VERSION \
    BACKBONE_VERSION=$BACKBONE_VERSION

ENV LANG=C.UTF-8 \
    LC_ALL=C.UTF-8

USER root

# install autosledgi for root
RUN pip install /home/isabelle/dist/*.whl --break-system-packages

# install llm2sysml agent
RUN git clone https://$TOKEN_TYPE:$CLONE_TOKEN@git.rwth-aachen.de/montibelle/frontend/tooling/llm2sysml.git /llm2sysml \
  && git -C /llm2sysml checkout $AGENT_VERSION \
  && chown -R root:root /llm2sysml \
  && chmod -R 700 /llm2sysml

# install llm2sysml requirements
RUN python3 -m venv /home/isabelle/.venv/llm2sysml \
  && /home/isabelle/.venv/llm2sysml/bin/python -m pip install --upgrade pip \
  && /home/isabelle/.venv/llm2sysml/bin/python -m pip install -r /llm2sysml/llm2sysml-agent/requirements.txt

# add llm2sysml envs
RUN echo "OPENAI_API_KEY=$OPENAI_API_KEY\nCHAT_SESSIONS_DIR=/builds/montibelle/case-studies/sysml/doubleinverter" > /llm2sysml/llm2sysml-agent/.env \
  && chown root:root /llm2sysml/llm2sysml-agent/.env \
  && chmod 600 /llm2sysml/llm2sysml-agent/.env \
  && chown -R isabelle:isabelle /home/isabelle/.venv

# Clone inverter. Der Inhalt des CLONE_TOKEN ist ein in montibelle erstelltes
# group access token, read repository und developer. Die Variabe namens
# CLONE_TOKEN wurde in MWE angelegt und mit dem token befüllt. Grund ist, dass
# Pipeline-Token nicht clonen können. Das Token muss aus Montibelle kommen, da
# core und case-studies gecloned werden.
RUN git clone --recursive \
              https://$TOKEN_TYPE:$CLONE_TOKEN@git.rwth-aachen.de/montibelle/case-studies/sysml/doubleinverter.git \
              "/builds/montibelle/case-studies/sysml/doubleinverter" \
    && git -C "/builds/montibelle/case-studies/sysml/doubleinverter" \
       checkout --recurse-submodules $INVERTER_VERSION

RUN curl --fail-with-body --output isabelle-heaps.zip --header "$TOKEN_TYPE: $TOKEN" https://git.rwth-aachen.de/api/v4/projects/48669/packages/generic/isabelle-heaps/$INVERTER_VERSION/isabelle-heaps-polyml-5.9.1_x86_64-linux-$INVERTER_VERSION.zip \
  && curl --fail-with-body --output isabelle-browser_info.zip --header "$TOKEN_TYPE: $TOKEN" https://git.rwth-aachen.de/api/v4/projects/48669/packages/generic/isabelle-browser_info/$INVERTER_VERSION/isabelle-browser_info-$INVERTER_VERSION.zip \
  && mkdir -p /builds/montibelle/case-studies/sysml/doubleinverter/.isabelle/heaps \
  && mkdir -p /builds/montibelle/case-studies/sysml/doubleinverter/.isabelle/browser_info \
  && unzip isabelle-heaps.zip -d /builds/montibelle/case-studies/sysml/doubleinverter/.isabelle/heaps \
  && unzip isabelle-browser_info.zip -d /builds/montibelle/case-studies/sysml/doubleinverter/.isabelle/browser_info \
  && rm isabelle-heaps.zip \
  && rm isabelle-browser_info.zip

# install codeserver and create config
RUN curl -fsSL https://code-server.dev/install.sh | sh -s -- --version $CODE_VERSION
RUN mkdir -p /home/isabelle/.config/code-server \
  && printf "bind-addr: 0.0.0.0:80\nauth: none" > /home/isabelle/.config/code-server/config.yaml

USER isabelle

# install sysml extension
RUN curl -L --fail --output sysmlv2.vsix -u "$GH_USER:$GH_PA" \
    "https://maven.pkg.github.com/MontiCore/sysmlv2/de/monticore/lang/sysml_v2/language-server/$SYSML_VERSION/language-server-$SYSML_VERSION-vscode.vsix" \
  && code-server --install-extension sysmlv2.vsix \
  && rm sysmlv2.vsix

# install ive extension
RUN curl --fail-with-body --output ive.vsix --header "$TOKEN_TYPE: $TOKEN" https://git.rwth-aachen.de/api/v4/projects/33488/packages/generic/ive/$IVE_VERSION/ive-$IVE_VERSION.vsix \
  && code-server --install-extension ive.vsix \
  && rm ive.vsix

WORKDIR /builds/montibelle/case-studies/sysml/doubleinverter

# install continue extension
RUN code-server --install-extension continue.continue@$CONTINUE_VERSION

# download backbone
RUN mkdir -p /home/isabelle/.local/share/code-server/extensions/montibelle.ive-$IVE_VERSION/bin/  \
  && curl --fail-with-body --output /home/isabelle/.local/share/code-server/extensions/montibelle.ive-$IVE_VERSION/bin/backbone-$BACKBONE_VERSION.jar \
          --header "$TOKEN_TYPE: $TOKEN" https://git.rwth-aachen.de/api/v4/projects/41628/packages/maven/montibelle/backbone/$BACKBONE_VERSION/backbone-$BACKBONE_VERSION.jar

# add continue config
RUN mkdir -p /home/isabelle/.continue \
  && printf 'name: Local Config\n\
version: 1.0.0\n\
schema: v1\n\
models:\n\
  - name: Sysml Agent\n\
    provider: openai\n\
    model: gpt-4____ai-generated\n\
    apiBase: http://localhost:8000/\n' \
  > /home/isabelle/.continue/config.yaml \
  && chown -R isabelle:isabelle /home/isabelle/.continue

USER root

# add accesstoken
RUN mkdir -p /root/.montibelle/ \
  && echo "$TOKEN" > /root/.montibelle/accesstoken.txt \
  && chmod o-r /root/.montibelle/accesstoken.txt

# install gradle 7 (for transformation)
RUN curl -fsSL https://services.gradle.org/distributions/gradle-7.6.4-bin.zip \
         -o gradle.zip \
  && unzip gradle.zip -d /opt/gradle \
  && ln -s /opt/gradle/gradle-7.6.4/bin/gradle /usr/bin/gradle \
  && rm gradle.zip \
  && echo "gitLabPrivateToken = " >> /builds/montibelle/case-studies/sysml/doubleinverter/gradle.properties

# download transformer, transform, pipe output to log
RUN mkdir -p target/logs
RUN gradle -p /builds/montibelle/case-studies/sysml/doubleinverter \
           -PgitLabPrivateToken=$TOKEN \
           -PtokenType=$TOKEN_TYPE \
           -Ptransformer_version=$TRANSFORMER_VERSION \
         transform >target/logs/transformer_$(date -u +%Y%m%dT%H%M%SZ).log 2>&1

# Ab jetzt läuft Gradle in Offline-Mode, damit er nicht versucht den Transformer
# zu downloaden (das Token liegt im Docker Image nicht mehr vor)
RUN echo "startParameter.offline=true" >> /root/.gradle/init.gradle

# add settings
RUN echo '{\n \
  "remote.autoForwardPorts": false,\n \
  "security.workspace.trust.enabled": false,\n \
  "ive.dependencies.backboneServer.aMode": "Connect to Running Server",\n \
  "ive.dependencies.backboneServer.proofFinding.timeout": 30,\n \
  "ive.showWelcome": false,\n \
  "ive.systemsView.enabled": false,\n \
  "ive.structureView.enabled": false,\n \
  "ive.theoriesView.enabled": false,\n \
  "lsp.sysmlv2.cocoCheckerMode": "None",\n \
  "workbench.editor.enablePreview": false,\n \
  "workbench.startupEditor": "readme",\n \
  "workbench.secondarySideBar.defaultVisibility": "hidden",\n \
  "window.menuBarVisibility": "false",\n \
  "files.exclude": {\n \
    "**/.*": true,\n \
    "**/doc": true,\n \
    "**/lib": true,\n \
    "**/src/counterexamples": true,\n \
    "**/src/hwls": true,\n \
    "**/src/vizualization": true,\n \
    "**/target/bin": true,\n \
    "**/target/theories/bundle": true,\n \
    "**/target/theories/code": true,\n \
    "**/target/theories/inc": true,\n \
    "**/target/theories/sps": true,\n \
    "**/target/theories/user": true,\n \
    "**/ROOTS": true\n \
  }\n \
}' > /home/isabelle/.local/share/code-server/User/settings.json

# -------- READ ONLY -----------------------

# remove unnecessary files, keep doc-folder
RUN rm -r /builds/montibelle/case-studies/sysml/doubleinverter/doc/** \
  /builds/montibelle/case-studies/sysml/doubleinverter/gradle \
  /builds/montibelle/case-studies/sysml/doubleinverter/.git \
  /builds/montibelle/case-studies/sysml/doubleinverter/.gitattributes \
  /builds/montibelle/case-studies/sysml/doubleinverter/.gitignore \
  /builds/montibelle/case-studies/sysml/doubleinverter/.gitlab-ci.yml \
  /builds/montibelle/case-studies/sysml/doubleinverter/.gitmodules \
  /builds/montibelle/case-studies/sysml/doubleinverter/gradlew \
  /builds/montibelle/case-studies/sysml/doubleinverter/gradlew.bat \
  /builds/montibelle/case-studies/sysml/doubleinverter/README.md

# only allow necessary permissions (target wird von gradle erstellt, deswegen
# hat es die falschen Rechte von root)
RUN chmod -R o-w /builds \
  && chmod -R o-r \
    /builds/montibelle/case-studies/sysml/doubleinverter/lib \
    /builds/montibelle/case-studies/sysml/doubleinverter/src/hwls \
    /builds/montibelle/case-studies/sysml/doubleinverter/target/focusSymbols \
    /builds/montibelle/case-studies/sysml/doubleinverter/target/sysmlSymbols \
    /builds/montibelle/case-studies/sysml/doubleinverter/target/theories/bundle \
    /builds/montibelle/case-studies/sysml/doubleinverter/target/theories/code \
    /builds/montibelle/case-studies/sysml/doubleinverter/target/theories/inc \
    /builds/montibelle/case-studies/sysml/doubleinverter/target/theories/sps \
    /builds/montibelle/case-studies/sysml/doubleinverter/target/theories/user \
  && mkdir -p /builds/montibelle/case-studies/sysml/doubleinverter/target/logs \
  && chown -R isabelle:isabelle /builds/montibelle/case-studies/sysml/doubleinverter/target/logs

# ------------------------------------------

# ---------- NAMENSGEBUNG & DOC ------------

COPY README.md /builds/montibelle/case-studies/sysml/doubleinverter
COPY doc/*.png /builds/montibelle/case-studies/sysml/doubleinverter/doc

# Keep a copy for pro users to copy into the PVC in the start script
RUN mkdir -p /opt/templates \
  && cp -a /builds/montibelle/case-studies/sysml/doubleinverter /opt/templates/doubleinverter \
  && chmod -R a+rX /opt/templates/doubleinverter

# ------------------------------------------

# Copy start script into the container
COPY start.sh /start.sh

EXPOSE 80
