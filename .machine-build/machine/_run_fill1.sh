#!/bin/bash
# One clean, unambiguously-logged build of CallerFill1Measure, with host-reap
# retries. The verdict is read from the log; the wrapper's return is never the
# verdict (5 builds were reaped by the host in the previous session).
set -u
trap "" TERM
TOOLCHAIN="$HOME/.elan/toolchains/leanprover--lean4---v4.33.1/bin"
export PATH="$TOOLCHAIN:$PATH"
LOG="${1:-/private/tmp/apsp_fill1_measure.log}"
cd /Volumes/Substrate-1/bigo/apsp-l1-work/.machine-build/machine || exit 66
rm -f "$LOG"
attempt=0
while [ "$attempt" -lt 6 ]; do
  attempt=$((attempt + 1))
  echo "=== attempt $attempt start $(date -u +%FT%TZ)" >> "$LOG"
  lake env lean -j1 CallerFill1Measure.lean \
     -o .lake/build/lib/lean/CallerFill1Measure.olean >> "$LOG" 2>&1
  rc=$?
  echo "=== attempt $attempt exit: $rc" >> "$LOG"
  if [ "$rc" -eq 0 ]; then
    echo "=== FINAL exit: 0" >> "$LOG"
    exit 0
  fi
  # 137/139/143/9: host reaps (admission watchdog / SIGKILL). Retry those only.
  case "$rc" in
    137|139|143|9|134) sleep 20 ;;
    *) echo "=== FINAL exit: $rc (elaboration error, not a reap)" >> "$LOG"; exit "$rc" ;;
  esac
done
echo "=== FINAL exit: exhausted retries" >> "$LOG"
exit 1
