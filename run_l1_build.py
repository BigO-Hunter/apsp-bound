#!/usr/bin/env python3
"""Detached lake build runner (survives harness restarts).
Usage: python3 run_l1_build.py <module> [<module>...]
Log: /private/tmp/apsp_l1.log ; exit marker: /private/tmp/apsp_l1.exit
"""
import subprocess, sys, os

WD = "/Volumes/Substrate-1/bigo/apsp-l1-work/verified"
mods = sys.argv[1:]
if not mods:
    print("usage: run_l1_build.py <module> [...]", file=sys.stderr)
    sys.exit(2)
log = open("/private/tmp/apsp_l1.log", "w")
pid = subprocess.Popen(
    ["nice", "-n", "19", "lake", "build", *mods],
    cwd=WD, stdout=log, stderr=subprocess.STDOUT, start_new_session=True,
)
with open("/private/tmp/apsp_l1.pid", "w") as f:
    f.write(str(pid.pid))
print(f"detached build pid={pid.pid} modules={mods}")
