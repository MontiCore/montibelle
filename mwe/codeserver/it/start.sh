#!/bin/sh

set -e

: "${IVE_VERSION:?IVE version is not set}"
: "${BACKBONE_VERSION:?Backbone version is not set}"

export USER_HOME=/home/isabelle
export ISABELLE_HOME_USER="$USER_HOME/.isabelle"
export PATH="/home/isabelle/Isabelle/bin:$PATH"
export PATH="/usr/local/bin:${PATH}"

java -jar /home/isabelle/.local/share/code-server/extensions/montibelle.ive-$IVE_VERSION/bin/backbone-$BACKBONE_VERSION.jar &

exec runuser -u isabelle -- code-server "/builds/montibelle/case-studies/sysml/security-gate"