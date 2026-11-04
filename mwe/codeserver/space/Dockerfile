FROM registry.git.rwth-aachen.de/montibelle/frontend/tooling/autosledgi-python:3.1.12

# Define arguments and provide defaults
ARG SYSML_VERSION="7.8.46"
ARG IVE_VERSION="1.3.3"
ARG BACKBONE_VERSION="3.0.7"
ARG TRANSFORMER_VERSION="3.0.0-20260715.140233-262"
ARG DLUF_VERSION="547226b"
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

# Clone dluf. Der Inhalt des CLONE_TOKEN ist ein in montibelle erstelltes
# group access token, read repository und developer. Die Variabe namens
# CLONE_TOKEN wurde in MWE angelegt und mit dem token befüllt. Grund ist, dass
# Pipeline-Token nicht clonen können. Das Token muss aus Montibelle kommen, da
# core und case-studies gecloned werden.
RUN git clone --recursive \
              https://$TOKEN_TYPE:$CLONE_TOKEN@git.rwth-aachen.de/montibelle/case-studies/sysml/dluf.git \
              "/builds/montibelle/case-studies/sysml/dluf" \
    && git -C "/builds/montibelle/case-studies/sysml/dluf" \
       checkout --recurse-submodules $DLUF_VERSION

# download dluf heaps and browser info
RUN curl --fail-with-body --output isabelle-heaps.zip --header "$TOKEN_TYPE: $TOKEN" https://git.rwth-aachen.de/api/v4/projects/71650/packages/generic/isabelle-heaps/$DLUF_VERSION/isabelle-heaps-polyml-5.9.1_x86_64-linux-$DLUF_VERSION.zip \
  && curl --fail-with-body --output isabelle-browser_info.zip --header "$TOKEN_TYPE: $TOKEN" https://git.rwth-aachen.de/api/v4/projects/71650/packages/generic/isabelle-browser_info/$DLUF_VERSION/isabelle-browser_info-$DLUF_VERSION.zip \
  && mkdir -p /builds/montibelle/case-studies/sysml/dluf/.isabelle/heaps \
  && mkdir -p /builds/montibelle/case-studies/sysml/dluf/.isabelle/browser_info \
  && unzip isabelle-heaps.zip -d /builds/montibelle/case-studies/sysml/dluf/.isabelle/heaps \
  && unzip isabelle-browser_info.zip -d /builds/montibelle/case-studies/sysml/dluf/.isabelle/browser_info \
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

WORKDIR /builds/montibelle/case-studies/sysml/dluf

# download backbone
RUN mkdir -p /home/isabelle/.local/share/code-server/extensions/montibelle.ive-$IVE_VERSION/bin/  \
  && curl --fail-with-body --output /home/isabelle/.local/share/code-server/extensions/montibelle.ive-$IVE_VERSION/bin/backbone-$BACKBONE_VERSION.jar \
          --header "$TOKEN_TYPE: $TOKEN" https://git.rwth-aachen.de/api/v4/projects/41628/packages/maven/montibelle/backbone/$BACKBONE_VERSION/backbone-$BACKBONE_VERSION.jar

USER root

# add accesstoken
RUN mkdir -p /root/.montibelle/ \
  && echo "$TOKEN" > /root/.montibelle/accesstoken.txt \
  && chmod o-r /root/.montibelle/accesstoken.txt

# install gradle 7 (for transformation)
RUN curl -fsSL https://services.gradle.org/distributions/gradle-7.6.4-bin.zip -o gradle.zip \
    && unzip -o gradle.zip -d /opt/gradle \
    && ln -sf /opt/gradle/gradle-7.6.4/bin/gradle /usr/bin/gradle \
    && rm gradle.zip \
    && echo "gitLabPrivateToken = " >> /builds/montibelle/case-studies/sysml/dluf/gradle.properties

# download transformer, transform, pipe output to log
RUN mkdir -p target/logs
RUN gradle -p /builds/montibelle/case-studies/sysml/dluf \
           -PgitLabPrivateToken=$TOKEN \
           -PtokenType=$TOKEN_TYPE \
           -Ptransformer_version=$TRANSFORMER_VERSION \
         transform >target/logs/transformer_$(date -u +%Y%m%dT%H%M%SZ).log 2>&1

# Ab jetzt läuft Gradle in Offline-Mode, damit er nicht versucht den Transformer
# zu downloaden (das Token liegt im Docker Image nicht mehr vor)
RUN echo "startParameter.offline=true" >> /root/.gradle/init.gradle

# add settings
RUN echo '{ \
  "remote.autoForwardPorts": false,\n \
  "security.workspace.trust.enabled": false,\n \
  "ive.dependencies.backboneServer.aMode": "Connect to Running Server", \
  "ive.dependencies.backboneServer.cVersion": "$BACKBONE_VERSION", \
  "ive.dependencies.backboneServer.proofFinding.timeout": 60, \
  "ive.showWelcome": false, \
  "ive.systemsView.enabled": false, \
  "ive.structureView.enabled": false, \
  "ive.theoriesView.enabled": false, \
  "workbench.editor.enablePreview": false, \
  "workbench.startupEditor": "readme", \
  "workbench.secondarySideBar.defaultVisibility": "hidden", \
  "window.menuBarVisibility": "false",\n \
  "files.exclude": { \
    "**/.*": true, \
    "**/doc": true, \
    "**/lib": true, \
    "**/src/counterexamples": true, \
    "**/src/hwls": true, \
    "**/src/vizualization": true, \
    "**/target/bin": true, \
    "**/target/theories/bundle": true, \
    "**/target/theories/code": true, \
    "**/target/theories/inc": true, \
    "**/target/theories/sps": true, \
    "**/target/theories/user": true, \
    "**/ROOTS": true \
  } \
}' > /home/isabelle/.local/share/code-server/User/settings.json

# -------- READ ONLY -----------------------

# remove unnecessary files, keep doc-folder
RUN rm -r /builds/montibelle/case-studies/sysml/dluf/.gitlab \
  /builds/montibelle/case-studies/sysml/dluf/cameo \
  /builds/montibelle/case-studies/sysml/dluf/doc/** \
  /builds/montibelle/case-studies/sysml/dluf/gradle \
  /builds/montibelle/case-studies/sysml/dluf/.git \
  /builds/montibelle/case-studies/sysml/dluf/.gitattributes \
  /builds/montibelle/case-studies/sysml/dluf/.gitignore \
  /builds/montibelle/case-studies/sysml/dluf/.gitlab-ci.yml \
  /builds/montibelle/case-studies/sysml/dluf/.gitmodules \
  /builds/montibelle/case-studies/sysml/dluf/gradlew \
  /builds/montibelle/case-studies/sysml/dluf/gradlew.bat \
  /builds/montibelle/case-studies/sysml/dluf/mkdocs.yml \
  /builds/montibelle/case-studies/sysml/dluf/README.md

# only allow necessary permissions
RUN chmod -R o-w /builds \
  && chmod -R o-r \
    /builds/montibelle/case-studies/sysml/dluf/lib \
    /builds/montibelle/case-studies/sysml/dluf/src/hwls

# ------------------------------------------

# README und zugehörige Bilder
COPY README.md /builds/montibelle/case-studies/sysml/dluf
COPY doc/ /builds/montibelle/case-studies/sysml/dluf/doc/
  
# Copy start script into the container
COPY start.sh /start.sh

EXPOSE 80
