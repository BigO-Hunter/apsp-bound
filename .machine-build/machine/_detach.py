#!/usr/bin/env python3
"""Launch a command in its OWN session so it survives the death of the
calling shell's process group.

WHY (measured 2026-11-10): a build launched with `nohup ... &` was reaped with
exit 143 (SIGTERM) the moment the polling tool-call that launched it was
killed -- nohup only ignores SIGHUP, and the harness kills the whole process
GROUP. os.setsid() in the child puts the build in a new session and process
group, so group-wide TERM/KILL aimed at the caller no longer reaches it.

Usage: python3 _detach.py -- <command> [args...]
"""
from __future__ import annotations

import os
import subprocess
import sys

cmd = sys.argv[1:]
if cmd and cmd[0] == "--":
    cmd = cmd[1:]
if not cmd:
    print("_detach: no command", file=sys.stderr)
    sys.exit(64)

proc = subprocess.Popen(
    cmd,
    stdin=subprocess.DEVNULL,
    stdout=subprocess.DEVNULL,
    stderr=subprocess.DEVNULL,
    start_new_session=True,  # setsid(): new session + new process group
    close_fds=True,
)
print(proc.pid)
