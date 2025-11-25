#!/usr/bin/env bash
set -euo pipefail
# Install elan & build the project
if ! command -v elan >/dev/null 2>&1; then
  curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | bash -s -- -y
  export PATH="$HOME/.elan/bin:$PATH"
fi
elan default leanprover/lean4:4.8.0
lake build
lake exe rbuftt
