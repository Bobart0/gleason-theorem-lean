#!/usr/bin/env bash
# Compatibility entry point retained for existing local workflows.
set -euo pipefail
exec "$(dirname "$0")/verify.sh" "$@"
