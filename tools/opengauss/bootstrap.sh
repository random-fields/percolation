#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=pins.env
source "$SCRIPT_DIR/pins.env"

STATE_DIR="${PERCOLATION_OPENGAUSS_STATE_DIR:-$SCRIPT_DIR/.state}"
DOWNLOAD_DIR="$STATE_DIR/downloads"
SOURCE_DIR="$STATE_DIR/source"
VENV_DIR="$STATE_DIR/venv"
UV_CACHE_DIR="$STATE_DIR/uv-cache"
UV_PYTHON_INSTALL_DIR="$STATE_DIR/python"
ARCHIVE_PATH="$DOWNLOAD_DIR/OpenGauss-$OPENGAUSS_COMMIT.tar.gz"
ARCHIVE_URL="https://codeload.github.com/$OPENGAUSS_REPOSITORY/tar.gz/$OPENGAUSS_COMMIT"

die() {
  printf 'OpenGauss bootstrap: %s\n' "$1" >&2
  exit 1
}

INSTALL_DEV=0
if [ "${1:-}" = "--dev" ]; then
  INSTALL_DEV=1
  shift
fi
[ "$#" -eq 0 ] || die "usage: $0 [--dev]"

for command_name in curl shasum tar uv rg; do
  command -v "$command_name" >/dev/null 2>&1 \
    || die "required command is unavailable: $command_name"
done

mkdir -p "$DOWNLOAD_DIR" "$STATE_DIR"

if [ ! -f "$ARCHIVE_PATH" ]; then
  partial_archive="$ARCHIVE_PATH.partial"
  printf 'Downloading %s at %s...\n' "$OPENGAUSS_REPOSITORY" "$OPENGAUSS_COMMIT"
  curl --fail --location --output "$partial_archive" "$ARCHIVE_URL"
  mv "$partial_archive" "$ARCHIVE_PATH"
fi

actual_sha="$(shasum -a 256 "$ARCHIVE_PATH" | awk '{print $1}')"
if [ "$actual_sha" != "$OPENGAUSS_ARCHIVE_SHA256" ]; then
  die "archive checksum mismatch (expected $OPENGAUSS_ARCHIVE_SHA256, got $actual_sha)"
fi

if [ ! -d "$SOURCE_DIR" ]; then
  extract_dir="$(mktemp -d "$STATE_DIR/extract.XXXXXX")"
  tar -xzf "$ARCHIVE_PATH" --strip-components=1 -C "$extract_dir"
  printf '%s\n' "$OPENGAUSS_COMMIT" > "$extract_dir/.opengauss-revision"
  mv "$extract_dir" "$SOURCE_DIR"
fi

[ -f "$SOURCE_DIR/.opengauss-revision" ] \
  || die "source directory exists without a revision marker: $SOURCE_DIR"
installed_revision="$(sed -n '1p' "$SOURCE_DIR/.opengauss-revision")"
[ "$installed_revision" = "$OPENGAUSS_COMMIT" ] \
  || die "source directory is pinned to $installed_revision, expected $OPENGAUSS_COMMIT"

rg -F -q "version = \"$OPENGAUSS_VERSION\"" "$SOURCE_DIR/pyproject.toml" \
  || die "upstream package version does not match $OPENGAUSS_VERSION"

export UV_CACHE_DIR UV_PYTHON_INSTALL_DIR
if [ ! -x "$VENV_DIR/bin/python" ]; then
  printf 'Creating isolated Python 3.13 environment...\n'
  uv venv --managed-python --python 3.13 "$VENV_DIR"
fi

printf 'Installing OpenGauss into the project-local environment...\n'
uv pip install --python "$VENV_DIR/bin/python" --editable "$SOURCE_DIR"

if [ "$INSTALL_DEV" = "1" ]; then
  printf 'Installing OpenGauss development dependencies for upstream tests...\n'
  uv pip install --python "$VENV_DIR/bin/python" --editable "$SOURCE_DIR[dev]"
fi

printf 'OpenGauss %s is installed under %s\n' "$OPENGAUSS_VERSION" "$STATE_DIR"
printf 'Run %s/verify.sh, then read %s/README.md.\n' "$SCRIPT_DIR" "$SCRIPT_DIR"
