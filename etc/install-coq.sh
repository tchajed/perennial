#!/bin/bash

set -e

opam install -y coq vscoq-language-server
opam clean --logs --all-switches --download-cache --repo-cache --untracked
