#!/bin/bash

set -e

opam install -y coq
opam clean --logs --all-switches --download-cache --repo-cache --untracked
