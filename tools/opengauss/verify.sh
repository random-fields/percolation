#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=pins.env
source "$SCRIPT_DIR/pins.env"

RUN_UPSTREAM_TESTS=0
if [ "${1:-}" = "--upstream-tests" ]; then
  RUN_UPSTREAM_TESTS=1
  shift
fi
if [ "$#" -ne 0 ]; then
  printf 'usage: %s [--upstream-tests]\n' "$0" >&2
  exit 2
fi

STATE_DIR="${PERCOLATION_OPENGAUSS_STATE_DIR:-$SCRIPT_DIR/.state}"
SOURCE_DIR="$STATE_DIR/source"
VENV_DIR="$STATE_DIR/venv"
ARCHIVE_PATH="$STATE_DIR/downloads/OpenGauss-$OPENGAUSS_COMMIT.tar.gz"

[ -x "$VENV_DIR/bin/python" ] || {
  printf 'OpenGauss is not installed. Run %s/bootstrap.sh first.\n' "$SCRIPT_DIR" >&2
  exit 2
}
[ -f "$ARCHIVE_PATH" ] || {
  printf 'Pinned source archive is missing: %s\n' "$ARCHIVE_PATH" >&2
  exit 2
}

actual_sha="$(shasum -a 256 "$ARCHIVE_PATH" | awk '{print $1}')"
[ "$actual_sha" = "$OPENGAUSS_ARCHIVE_SHA256" ] || {
  printf 'Checksum mismatch: expected %s, got %s\n' \
    "$OPENGAUSS_ARCHIVE_SHA256" "$actual_sha" >&2
  exit 2
}

installed_revision="$(sed -n '1p' "$SOURCE_DIR/.opengauss-revision")"
[ "$installed_revision" = "$OPENGAUSS_COMMIT" ] || {
  printf 'Revision mismatch: expected %s, got %s\n' \
    "$OPENGAUSS_COMMIT" "$installed_revision" >&2
  exit 2
}

export PYTHONPATH="$SOURCE_DIR${PYTHONPATH:+:$PYTHONPATH}"
"$VENV_DIR/bin/python" "$SCRIPT_DIR/smoke.py"
"$SCRIPT_DIR/run.sh" version

real_codex="$(command -v codex || true)"
[ -n "$real_codex" ] || {
  printf '%s\n' 'Codex CLI is missing.' >&2
  exit 2
}
PERCOLATION_OPENGAUSS_REAL_CODEX="$real_codex" "$SCRIPT_DIR/bin/codex" --version

shim_output="$(
  PERCOLATION_OPENGAUSS_REAL_CODEX="$SCRIPT_DIR/testdata/record-argv.sh" \
    "$SCRIPT_DIR/bin/codex" \
    --dangerously-bypass-approvals-and-sandbox \
    --sandbox danger-full-access \
    --ask-for-approval on-request \
    shim-sentinel
)"
expected_shim_output=$'--sandbox\nworkspace-write\n--ask-for-approval\nnever\nshim-sentinel'
if [ "$shim_output" != "$expected_shim_output" ]; then
  printf 'Safe Codex shim emitted unexpected arguments:\n%s\n' "$shim_output" >&2
  exit 2
fi

if [ "$RUN_UPSTREAM_TESTS" = "1" ]; then
  "$VENV_DIR/bin/python" -c 'import pytest' 2>/dev/null || {
    printf 'pytest is missing; run %s/bootstrap.sh --dev first.\n' "$SCRIPT_DIR" >&2
    exit 2
  }
  (
    cd "$SOURCE_DIR"
    "$VENV_DIR/bin/python" -m pytest -q -o addopts='' \
      tests/test_swarm_manager.py \
      tests/gauss_cli/test_autoformalize.py
  )
fi

printf 'Verified OpenGauss %s at %s\n' "$OPENGAUSS_VERSION" "$OPENGAUSS_COMMIT"
printf '%s\n' 'No agent subprocess was launched.'
