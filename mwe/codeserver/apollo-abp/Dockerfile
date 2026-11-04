FROM registry.git.rwth-aachen.de/montibelle/frontend/tooling/autosledgi-python:3.1.26

# Define arguments and provide defaults
ARG SYSML_VERSION="7.8.109"
ARG IVE_VERSION="1.3.9"
ARG BACKBONE_VERSION="3.0.21"
ARG TRANSFORMER_VERSION="3.0.0-SNAPSHOT"
ARG CODE_VERSION="4.144.0"
ARG TOKEN_TYPE="private-token"
ARG TOKEN="<your_access_token>"
ARG CLONE_TOKEN=$TOKEN

# Set Ive and Backbone version to environment variables for the start script
ENV IVE_VERSION=$IVE_VERSION \
    BACKBONE_VERSION=$BACKBONE_VERSION

ENV LANG=C.UTF-8 \
    LC_ALL=C.UTF-8

USER root

# install autosledgi for root
RUN pip install /home/isabelle/dist/*.whl --break-system-packages

# Clone ABP's Apollo branch
RUN git clone --recursive --branch "$ABP_BRANCH" \
      "https://oauth2:${CLONE_TOKEN}@git.rwth-aachen.de/montibelle/case-studies/sysml/abp.git" \
      "/builds/montibelle/case-studies/sysml/abp" \
      && git -C "/builds/montibelle/case-studies/sysml/abp" \
      checkout --recurse-submodules "$ABP_SOURCE_VERSION"

RUN ln -s /builds/montibelle/case-studies/sysml/abp \
          /builds/montibelle/case-studies/sysml/apollo-abp

# download abp heaps and browser info
RUN curl --fail-with-body --output isabelle-heaps.zip --header "$TOKEN_TYPE: $TOKEN" \
      "https://git.rwth-aachen.de/api/v4/projects/115220/packages/generic/isabelle-heaps/$ABP_HEAP_VERSION/isabelle-heaps-polyml-5.9.1_x86_64-linux-$ABP_HEAP_VERSION.zip" \
      && curl --fail-with-body  --output isabelle-browser_info.zip --header "$TOKEN_TYPE: $TOKEN" \
      "https://git.rwth-aachen.de/api/v4/projects/115220/packages/generic/isabelle-browser_info/$ABP_HEAP_VERSION/isabelle-browser_info-polyml-5.9.1_x86_64-linux-$ABP_HEAP_VERSION.zip" \
       && mkdir -p /builds/montibelle/case-studies/sysml/abp/.isabelle/heaps \
       && mkdir -p /builds/montibelle/case-studies/sysml/abp/.isabelle/browser_info \
       && unzip isabelle-heaps.zip \
      -d /builds/montibelle/case-studies/sysml/abp/.isabelle/heaps \
       && unzip isabelle-browser_info.zip \
      -d /builds/montibelle/case-studies/sysml/abp/.isabelle/browser_info \
       && rm isabelle-heaps.zip isabelle-browser_info.zip \
       && chown -R isabelle:isabelle /builds/montibelle/case-studies/sysml/abp/.isabelle

# Install code-server and code-server
RUN curl -fsSL https://code-server.dev/install.sh | sh -s -- --version $CODE_VERSION
RUN mkdir -p /home/isabelle/.config/code-server \
 && printf "bind-addr: 0.0.0.0:80\nauth: none\n"  > /home/isabelle/.config/code-server/config.yaml && chown -R isabelle:isabelle /home/isabelle/.config

USER isabelle

# Install the SysML v2 extension
RUN curl -L --fail --output sysmlv2.vsix -u "$GH_USER:$GH_PA" \
      "https://maven.pkg.github.com/MontiCore/sysmlv2/de/monticore/lang/sysml_v2/language-server/$SYSML_VERSION/language-server-$SYSML_VERSION-vscode.vsix" \
 && code-server --install-extension sysmlv2.vsix \
 && rm sysmlv2.vsix

# Install the IVE extension
RUN curl --fail-with-body --output ive.vsix --header "$TOKEN_TYPE: $TOKEN" \
      "https://git.rwth-aachen.de/api/v4/projects/33488/packages/generic/ive/$IVE_VERSION/ive-$IVE_VERSION.vsix" \
 && code-server --install-extension ive.vsix \
 && rm ive.vsix

WORKDIR /builds/montibelle/case-studies/sysml/abp

# Download Backbone separately.
# IVE 1.3.3 does not include the Backbone JAR in its VSIX.
RUN mkdir -p /home/isabelle/.local/share/code-server/extensions/montibelle.ive-$IVE_VERSION/bin \
 && curl --fail-with-body --output /home/isabelle/.local/share/code-server/extensions/montibelle.ive-$IVE_VERSION/bin/backbone-$BACKBONE_VERSION.jar \
      --header "$TOKEN_TYPE: $TOKEN" \
      "https://git.rwth-aachen.de/api/v4/projects/41628/packages/maven/montibelle/backbone/$BACKBONE_VERSION/backbone-$BACKBONE_VERSION.jar"

USER root

# add accesstoken
RUN mkdir -p /root/.montibelle/ \
  && echo "$TOKEN" > /root/.montibelle/accesstoken.txt \
  && chmod o-r /root/.montibelle/accesstoken.txt

# install gradle 7 (for transformation)
RUN curl -fsSL https://services.gradle.org/distributions/gradle-7.6.4-bin.zip \
      -o /tmp/gradle.zip \
 && unzip /tmp/gradle.zip -d /opt/gradle \
 && ln -s /opt/gradle/gradle-7.6.4/bin/gradle /usr/bin/gradle \
 && rm /tmp/gradle.zip \
 && echo "gitLabPrivateToken = " >> /builds/montibelle/case-studies/sysml/abp/gradle.properties

# download transformer, transform abp, pipe output to abp's log
RUN mkdir -p /builds/montibelle/case-studies/sysml/abp/target/logs
RUN gradle -p /builds/montibelle/case-studies/sysml/abp \
      -PgitLabPrivateToken=$TOKEN \
      -PtokenType=$TOKEN_TYPE \
      -Ptransformer_version=$TRANSFORMER_VERSION \
      transform \
      > /builds/montibelle/case-studies/sysml/abp/target/logs/transformer_$(date -u +%Y%m%dT%H%M%SZ).log \
      2>&1

# Ab jetzt läuft Gradle in Offline-Mode, damit er nicht versucht den Transformer
# zu downloaden (das Token liegt im Docker Image nicht mehr vor)
RUN echo "startParameter.offline=true" >> /root/.gradle/init.gradle

# Add code-server/IVE settings
RUN mkdir -p /home/isabelle/.local/share/code-server/User \
 && printf '{\n\
  "remote.autoForwardPorts": false,\n\
  "security.workspace.trust.enabled": false,\n\
  "lsp.sysmlv2.cocoCheckerMode": "None", \n\
  "ive.dependencies.backboneServer.aMode": "Connect to Running Server",\n\
  "ive.dependencies.backboneServer.cVersion": "%s",\n\
  "ive.dependencies.backboneServer.proofFinding.timeout": 60,\n\
  "ive.showWelcome": false,\n\
  "ive.systemsView.enabled": false,\n\
  "ive.structureView.enabled": false,\n\
  "ive.theoriesView.enabled": false,\n\
  "workbench.editor.enablePreview": false,\n\
  "workbench.startupEditor": "readme",\n\
  "workbench.secondarySideBar.defaultVisibility": "hidden",\n\
  "window.menuBarVisibility": "false",\n\
  "files.exclude": {\n\
    "**/.*": true,\n\
    "**/doc": true,\n\
    "**/lib": true,\n\
    "**/src/counterexamples": true,\n\
    "**/src/hwls": true,\n\
    "**/src/vizualization": true,\n\
    "**/target/bin": true,\n\
    "**/target/theories/bundle": true,\n\
    "**/target/theories/code": true,\n\
    "**/target/theories/inc": true,\n\
    "**/target/theories/sps": true,\n\
    "**/target/theories/user": true,\n\
    "**/ROOTS": true\n\
  }\n\
}\n' "$BACKBONE_VERSION" \
    > /home/isabelle/.local/share/code-server/User/settings.json \
 && chown -R isabelle:isabelle \
    /home/isabelle/.local/share/code-server/User

# -------- READ ONLY -----------------------

# only allow necessary permissions
RUN chmod -R o-w /builds

# ------------------------------------------

# Copy startup script
COPY start.sh /start.sh
RUN chmod +x /start.sh

EXPOSE 80
