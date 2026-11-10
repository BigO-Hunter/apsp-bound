#!/bin/bash
# One clean, unambiguously-logged build of CallerUniversalBody.
# Unique log per invocation so no two runs can interleave (the failure that
# made a previous verdict unreadable).
set -u
trap "" TERM
TOOLCHAIN="$HOME/.elan/toolchains/leanprover--lean4---v4.33.1/bin"
export PATH="$TOOLCHAIN:$PATH"
LOG="${1:-/private/tmp/apsp_univ_build.log}"
cd /Volumes/Substrate-1/bigo/apsp-l1-work/.machine-build/machine || exit 66
rm -f "$LOG"
{
  lake env lean -j1 CallerUniversalBody.lean -o .lake/build/lib/lean/CallerUniversalBody.olean
  echo "=== exit: $?"
} >> "$LOG" 2>&1
