FROM ubuntu:latest

RUN apt-get update && apt-get install -y \
    curl \
    less \
    libgomp1 \
    libfontconfig1 \
    rlwrap \
    unzip \
    make \
    libwww-perl \
    && apt-get clean \
    && rm -rf /var/lib/apt/lists/*

RUN useradd -m isabelle && (echo isabelle:isabelle | chpasswd)
USER isabelle

WORKDIR /home/isabelle
RUN curl --fail https://isabelle.in.tum.de/website-Isabelle2019/dist/Isabelle2019_linux.tar.gz > Isabelle.tar.gz && \
    tar xzf Isabelle.tar.gz && \
    mv Isabelle2019 Isabelle && \
    rm -f Isabelle/doc/*.pdf && \
    sed -i -e 's@ISABELLE_HOME_USER=.*@ISABELLE_HOME_USER="$USER_HOME/.isabelle"@g' Isabelle/etc/settings && \
    rm Isabelle.tar.gz
ENV PATH="/home/isabelle/Isabelle/bin:${PATH}"

ARG DEF_LOGIC="HOLCF"
RUN sed -i -e 's@ISABELLE_LOGIC=.*@'"ISABELLE_LOGIC=$DEF_LOGIC"'@g' Isabelle/etc/settings && \
    isabelle build -o system_heaps -b -j 4 -v HOLCF
