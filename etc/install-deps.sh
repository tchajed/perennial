#!/bin/bash

set -e

apt-get update -y
apt-get upgrade -y

ln -fs /usr/share/zoneinfo/America/Chicago /etc/localtime
DEBIAN_FRONTEND=noninteractive apt-get install -y tzdata
dpkg-reconfigure --frontend noninteractive tzdata

# opam dependencies
apt-get install -y wget patch unzip bzip2 gcc make

# coq dependencies
apt-get install -y libgmp-dev pkg-config

# other dependencies
apt-get install -y sudo git python3 zsh
