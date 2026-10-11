#!/usr/bin/env bash
set -euo pipefail

# Synchronize with the installed parent workspace; update mathlib there first.
PROJECT_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
WORKSPACE_ROOT="$(cd -- "$PROJECT_ROOT/.." && pwd)"
MATHLIB_DIR="$WORKSPACE_ROOT/.lake/packages/mathlib"

if [ ! -f "$MATHLIB_DIR/lean-toolchain" ]; then
  echo "shared mathlib is missing: $MATHLIB_DIR" >&2
  exit 1
fi

if [ "$(tr -d '\r\n' < "$WORKSPACE_ROOT/lean-toolchain")" != \
     "$(tr -d '\r\n' < "$MATHLIB_DIR/lean-toolchain")" ]; then
  echo "parent workspace and shared mathlib toolchains differ" >&2
  exit 1
fi

cd -- "$PROJECT_ROOT"
cp "$WORKSPACE_ROOT/lean-toolchain" lean-toolchain
MATHLIB_NO_CACHE_ON_UPDATE=1 lake --keep-toolchain update mathlib
