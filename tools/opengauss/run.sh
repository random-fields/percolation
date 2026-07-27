#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
STATE_DIR="${PERCOLATION_OPENGAUSS_STATE_DIR:-$SCRIPT_DIR/.state}"
GAUSS_EXE="$STATE_DIR/venv/bin/gauss"
SOURCE_DIR="$STATE_DIR/source"

if [ ! -x "$GAUSS_EXE" ]; then
  printf 'OpenGauss is not installed. Run %s/bootstrap.sh first.\n' "$SCRIPT_DIR" >&2
  exit 2
fi

real_codex="$(command -v codex || true)"
if [ -z "$real_codex" ]; then
  printf '%s\n' 'OpenGauss Codex backend is unavailable: codex was not found on PATH.' >&2
  exit 2
fi

first_argument="${1:-}"
case "$first_argument" in
  version|doctor|status|--help|-h)
    ;;
  *)
    if [ "${PERCOLATION_OPENGAUSS_ALLOW_NESTED_AGENTS:-0}" != "1" ]; then
      printf '%s\n' \
        'Refusing to launch a separate OpenGauss agent session while native agents may be active.' \
        'Use OpenGauss only from an exclusive worktree/session, then set:' \
        '  PERCOLATION_OPENGAUSS_ALLOW_NESTED_AGENTS=1' >&2
      exit 2
    fi
    ;;
esac

export PERCOLATION_OPENGAUSS_REAL_CODEX="$real_codex"
export PATH="$SCRIPT_DIR/bin:$PATH"
export PYTHONPATH="$SOURCE_DIR${PYTHONPATH:+:$PYTHONPATH}"
export GAUSS_HOME="$STATE_DIR/gauss-home"
export GAUSS_AUTOFORMALIZE_BACKEND=codex
export GAUSS_AUTOFORMALIZE_MANAGED_STATE_DIR="$STATE_DIR/managed"
export UV_CACHE_DIR="$STATE_DIR/uv-cache"
export UV_PYTHON_INSTALL_DIR="$STATE_DIR/python"

exec "$GAUSS_EXE" "$@"
