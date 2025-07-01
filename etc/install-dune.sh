#!/bin/bash

set -e

# shellcheck disable=SC2046
eval $(opam env --switch=default)
opam install -y dune
opam clean --logs --all-switches --download-cache --repo-cache --untracked
