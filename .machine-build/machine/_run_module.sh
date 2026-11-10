#!/bin/bash
# One clean, unambiguously-logged build of ONE module, with the lane's
# established discipline plus kill-retry.
#
# Why each piece (all measured on this host, 2026-11-10):
#   * `trap "" TERM` — the harness and the host's governors both send TERM;
#     a build is not a verdict until it writes its own exit line.
#   * one unique log per invocation — no two runs can interleave (the failure
#     that once made a verdict unreadable).
#   * `-o .lake/build/lib/lean/<Mod>.olean` — without it the olean lands in
#     the CWD or nowhere, and the receipt cannot name an artifact.
#   * the single-writer fcntl lock — several lanes share this bench.
#   * RETRY, but ONLY on transport deaths (rc < 0 or >= 128). A real
#     elaboration error is reported on the first attempt and never retried:
#     retrying a red proof would launder it into a flaky-looking green.
#
# Usage: _run_module.sh <Module> [<tag>] [<tries>]
# Receipt: /private/tmp/apsp_<tag>.log  and  /private/tmp/apsp_<tag>.exit
set -u
trap "" TERM
MOD="${1:?usage: _run_module.sh <Module> [tag] [tries]}"
TAG="${2:-$MOD}"
TRIES="${3:-5}"
TOOLCHAIN="$HOME/.elan/toolchains/leanprover--lean4---v4.33.1/bin"
export PATH="$TOOLCHAIN:$PATH"
BENCH=/Volumes/Substrate-1/bigo/apsp-l1-work/.machine-build/machine
LOG="/private/tmp/apsp_${TAG}.log"
EXITF="/private/tmp/apsp_${TAG}.exit"
cd "$BENCH" || exit 66
rm -f "$LOG" "$EXITF"
attempt=1
final=1
while [ "$attempt" -le "$TRIES" ]; do
  {
    echo "=== START ${MOD} attempt ${attempt}/${TRIES} $(date -u +%FT%TZ) ==="
  } >> "$LOG"
  python3 _build_lock.py -- \
    lake env lean -j1 "${MOD}.lean" -o ".lake/build/lib/lean/${MOD}.olean" >> "$LOG" 2>&1
  rc=$?
  echo "=== attempt ${attempt} rc=${rc} ===" >> "$LOG"
  if [ "$rc" -eq 0 ]; then final=0; break; fi
  if [ "$rc" -ge 128 ] || [ "$rc" -lt 0 ]; then
    attempt=$((attempt + 1)); sleep 5; continue
  fi
  final=$rc; break
done
{
  echo "rc=${final}"
  echo "attempts=${attempt}"
  echo "olean=$(stat -f '%z bytes %Sm' ".lake/build/lib/lean/${MOD}.olean" 2>/dev/null || echo absent)"
} > "$EXITF"
