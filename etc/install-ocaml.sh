#!/bin/bash

set -e

OCAML_VERSION=5.2.0

wget 'https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh'
yes '' | bash install.sh --fresh
rm install.sh

if [ "$(uname -m)" = "x86_64" ]; then
  export OPAMJOBS=1
fi

# disable sandboxing since the container is enough isolation, and further
# sandboxing doesn't work in a container anyway
opam init -y --bare --disable-sandboxing
opam switch create -y default ocaml-base-compiler.${OCAML_VERSION}

# shellcheck disable=SC2016
echo 'eval $(opam env)' >>~/.profile

# shellcheck disable=SC2046
eval $(opam env --switch=default)

#opam install -y dune

opam clean --logs --all-switches --download-cache --repo-cache --untracked
