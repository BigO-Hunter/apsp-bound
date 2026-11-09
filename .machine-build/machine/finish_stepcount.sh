#!/bin/bash
trap "" TERM
cd /Volumes/Substrate-1/bigo/apsp-l1-work/.machine-build/machine
rm -f /private/tmp/apsp_sc.exit
LOG=/private/tmp/apsp_sc.log
{
  echo "=== CallerStepCount build $(date -u +%FT%TZ) ==="
  for attempt in 1 2; do
    lake env lean -j1 CallerStepCount.lean -o .lake/build/lib/lean/CallerStepCount.olean
    rc=$?
    echo "=== CallerStepCount attempt $attempt exit: $rc at $(date -u +%FT%TZ) ==="
    [ "$rc" = "0" ] && break
    grep -q "error:" "$LOG" && break
    sleep 5
  done
  echo "=== olean: $(ls -la .lake/build/lib/lean/CallerStepCount.olean 2>&1) ==="
  echo "=== axioms: ==="
  grep "depends on" "$LOG"
} > "$LOG" 2>&1
rc=$(grep -m1 "attempt 1 exit" "$LOG" | sed 's/.*exit: //')
echo "$rc" > /private/tmp/apsp_sc.exit
