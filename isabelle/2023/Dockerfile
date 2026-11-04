FROM ubuntu:23.04

RUN apt-get update && DEBIAN_FRONTEND="noninteractive" apt-get install -y \
    git \
    curl \
    less \
    libgomp1 \
    libfontconfig1 \
    rlwrap \
    unzip \
    make \
    libwww-perl \
    openjdk-11-jdk-headless \
    python3 \
    python3-pip \
    python3-venv \
    && ln $(which python3) $(dirname $(which python3))/python \
    && apt-get clean \
    && rm -rf /var/lib/apt/lists/*

RUN useradd -m isabelle && (echo isabelle:isabelle | chpasswd)
USER isabelle

WORKDIR /home/isabelle
RUN curl --fail https://isabelle.in.tum.de/dist/Isabelle2023_linux.tar.gz > Isabelle.tar.gz && \
    tar xzf Isabelle.tar.gz && \
    mv Isabelle2023 Isabelle && \
    rm -f Isabelle/doc/*.pdf && \
    sed -i -e 's@ISABELLE_HOME_USER=.*@ISABELLE_HOME_USER="$USER_HOME/.isabelle"@g' Isabelle/etc/settings && \
    rm Isabelle.tar.gz
ENV PATH="/home/isabelle/Isabelle/bin:${PATH}"

ADD preferences /home/isabelle/.isabelle/etc/preferences
ADD settings /home/isabelle/.isabelle/etc/settings

ARG DEF_LOGIC="HOLCF"
RUN sed -i -e 's@ISABELLE_LOGIC=.*@'"ISABELLE_LOGIC=$DEF_LOGIC"'@g' Isabelle/etc/settings && \
    isabelle build -o system_heaps -b -j 4 -v HOLCF

ADD activate /home/isabelle/Isabelle/bin/activate

USER root
RUN chown -R isabelle:isabelle /home/isabelle/.isabelle
RUN chown isabelle:isabelle /home/isabelle/Isabelle/bin/activate
USER isabelle

