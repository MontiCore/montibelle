FROM ubuntu:latest

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
    default-jre \
    python3.8 \
    python3-pip \
    && apt-get clean \
    && rm -rf /var/lib/apt/lists/*

RUN yes w | pip3 install boto3 psutil events matplotlib numpy scipy kubernetes

RUN useradd -m isabelle && (echo isabelle:isabelle | chpasswd)
USER isabelle

WORKDIR /home/isabelle
RUN curl --fail https://isabelle.in.tum.de/dist/Isabelle2021_linux.tar.gz > Isabelle.tar.gz && \
    tar xzf Isabelle.tar.gz && \
    mv Isabelle2021 Isabelle && \
    rm -f Isabelle/doc/*.pdf && \
    sed -i -e 's@ISABELLE_HOME_USER=.*@ISABELLE_HOME_USER="$USER_HOME/.isabelle"@g' Isabelle/etc/settings && \
    rm Isabelle.tar.gz
ENV PATH="/home/isabelle/Isabelle/bin:${PATH}"

ARG DEF_LOGIC="HOLCF"
RUN sed -i -e 's@ISABELLE_LOGIC=.*@'"ISABELLE_LOGIC=$DEF_LOGIC"'@g' Isabelle/etc/settings && \
    isabelle build -o system_heaps -b -j 4 -v HOLCF
