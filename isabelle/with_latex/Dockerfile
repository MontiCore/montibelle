ARG ISABELLE_IMAGE

FROM $ISABELLE_IMAGE

USER root

ADD 01_nodoc /etc/dpkg/dpkg.cfg.d/01_nodoc

RUN apt-get update \
    && DEBIAN_FRONTEND=noninteractive apt-get install -y \
       texlive \
       texlive-plain-generic \
       texlive-lang-german \
       texlive-latex-extra \
       texlive-science \
       texlive-fonts-extra \
       texlive-publishers \
       latexdiff \
       biber \
       gnuplot \
    && apt-get --purge -y remove tex.\*-doc$ \
    && apt-get clean \
    && rm -rf /var/lib/apt/lists/*

    
USER isabelle
