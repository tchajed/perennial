#!/bin/bash

set -e

# opam dependencies
sudo apt-get install -y wget patch unzip bzip2 gcc make

# coq dependencies
sudo apt-get install -y libgmp-dev pkg-config

# other dependencies
sudo apt-get install -y sudo git python3 zsh
