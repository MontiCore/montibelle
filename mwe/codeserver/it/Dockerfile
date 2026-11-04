FROM registry.git.rwth-aachen.de/montibelle/frontend/tooling/autosledgi-python:3.0.1

# Define arguments and provide defaults
ARG SYSML_VERSION="7.8.46"
ARG IVE_VERSION="1.3.1"
ARG BACKBONE_VERSION="3.0.7"
ARG TRANSFORMER_VERSION="3.0.0-SNAPSHOT"
ARG CASE_VERSION="3bc3997"
ARG CODE_VERSION="4.106.2"
ARG TOKEN_TYPE="private-token"
ARG TOKEN="<your_access_token>"
ARG CLONE_TOKEN=$TOKEN

# Set Ive and Backbone version to environment variables for the start script
ENV IVE_VERSION=$IVE_VERSION \
    BACKBONE_VERSION=$BACKBONE_VERSION

USER root

# install autosledgi for root
RUN pip install /home/isabelle/dist/*.whl --break-system-packages

# Clone Case-Study. Der Inhalt des CLONE_TOKEN ist ein in montibelle erstelltes
# group access token, read repository und developer. Die Variabe namens
# CLONE_TOKEN wurde in MWE angelegt und mit dem token befüllt. Grund ist, dass
# Pipeline-Token nicht clonen können. Das Token muss aus Montibelle kommen, da
# core und case-studies gecloned werden.
RUN git clone --recursive \
              https://$TOKEN_TYPE:$CLONE_TOKEN@git.rwth-aachen.de/montibelle/case-studies/sysml/security-gate.git \
              "/builds/montibelle/case-studies/sysml/security-gate" \
    && git -C "/builds/montibelle/case-studies/sysml/security-gate" \
       checkout --recurse-submodules $CASE_VERSION

# download heaps and browser info
RUN curl --fail-with-body \
         --output isabelle-heaps.zip \
         --header "$TOKEN_TYPE: $TOKEN" \
         https://git.rwth-aachen.de/api/v4/projects/115382/packages/generic/isabelle-heaps/$CASE_VERSION/isabelle-heaps-$CASE_VERSION.zip \
 && curl --fail-with-body \
          --output isabelle-browser_info.zip \
          --header "$TOKEN_TYPE: $TOKEN" \
          https://git.rwth-aachen.de/api/v4/projects/115382/packages/generic/isabelle-browser_info/$CASE_VERSION/isabelle-browser_info-$CASE_VERSION.zip \
 && mkdir -p /builds/montibelle/case-studies/sysml/security-gate/.isabelle/heaps \
 && mkdir -p /builds/montibelle/case-studies/sysml/security-gate/.isabelle/browser_info \
 && unzip isabelle-heaps.zip \
    -d /builds/montibelle/case-studies/sysml/security-gate/.isabelle/heaps \
 && unzip isabelle-browser_info.zip \
    -d /builds/montibelle/case-studies/sysml/security-gate/.isabelle/browser_info \
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
RUN curl --fail-with-body \
         --output ive.vsix \
         --header "$TOKEN_TYPE: $TOKEN" \
         https://git.rwth-aachen.de/api/v4/projects/33488/packages/generic/ive/$IVE_VERSION/ive-$IVE_VERSION.vsix \
  && code-server --install-extension ive.vsix \
  && rm ive.vsix

WORKDIR /builds/montibelle/case-studies/sysml/security-gate

# download backbone
RUN mkdir -p /home/isabelle/.local/share/code-server/extensions/montibelle.ive-$IVE_VERSION/bin/  \
 && curl --fail-with-body \
         --output /home/isabelle/.local/share/code-server/extensions/montibelle.ive-$IVE_VERSION/bin/backbone-$BACKBONE_VERSION.jar \
         --header "$TOKEN_TYPE: $TOKEN" \
         https://git.rwth-aachen.de/api/v4/projects/41628/packages/maven/montibelle/backbone/$BACKBONE_VERSION/backbone-$BACKBONE_VERSION.jar

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
  && (test -f /builds/montibelle/case-studies/sysml/security-gate/gradle.properties \
      && echo "" >> /builds/montibelle/case-studies/sysml/security-gate/gradle.properties || true) \
  && echo "gitLabPrivateToken = " >> /builds/montibelle/case-studies/sysml/security-gate/gradle.properties

# download transformer, transform, pipe output to log
RUN mkdir -p target/logs
RUN gradle -p /builds/montibelle/case-studies/sysml/security-gate \
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
RUN (rm -rf /builds/montibelle/case-studies/sysml/security-gate/doc/* 2>/dev/null || true) \
  && rm -rf /builds/montibelle/case-studies/sysml/security-gate/gradle \
  /builds/montibelle/case-studies/sysml/security-gate/.git \
  /builds/montibelle/case-studies/sysml/security-gate/.gitattributes \
  /builds/montibelle/case-studies/sysml/security-gate/.gitignore \
  /builds/montibelle/case-studies/sysml/security-gate/.gitlab-ci.yml \
  /builds/montibelle/case-studies/sysml/security-gate/.gitmodules \
  /builds/montibelle/case-studies/sysml/security-gate/gradlew \
  /builds/montibelle/case-studies/sysml/security-gate/gradlew.bat \
  /builds/montibelle/case-studies/sysml/security-gate/README.md

# only allow necessary permissions (target wird von gradle erstellt, deswegen
# hat es die falschen Rechte von root)
RUN chmod -R o-w /builds \
  && (chmod -R o-r \
    /builds/montibelle/case-studies/sysml/security-gate/lib \
    /builds/montibelle/case-studies/sysml/security-gate/src/hwls \
    /builds/montibelle/case-studies/sysml/security-gate/target/focusSymbols \
    /builds/montibelle/case-studies/sysml/security-gate/target/sysmlSymbols \
    /builds/montibelle/case-studies/sysml/security-gate/target/theories/bundle \
    /builds/montibelle/case-studies/sysml/security-gate/target/theories/code \
    /builds/montibelle/case-studies/sysml/security-gate/target/theories/inc \
    /builds/montibelle/case-studies/sysml/security-gate/target/theories/sps \
    /builds/montibelle/case-studies/sysml/security-gate/target/theories/user \
    2>/dev/null || true) \
  && mkdir -p /builds/montibelle/case-studies/sysml/security-gate/target/logs \
  && chown -R isabelle:isabelle /builds/montibelle/case-studies/sysml/security-gate/target/logs

# ------------------------------------------

# ---------- NAMENSGEBUNG & DOC ------------

COPY README.md /builds/montibelle/case-studies/sysml/security-gate
COPY doc/*.png /builds/montibelle/case-studies/sysml/security-gate/doc

# ------------------------------------------

# Copy start script into the container
COPY start.sh /start.sh

EXPOSE 80
