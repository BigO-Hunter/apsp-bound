#!/usr/bin/env python3
"""Exclusive build lock for the apsp lanes (the `flock -w 7200` the brief names).

WHY THIS FILE EXISTS (measured 2026-11-09, this session): macOS ships no
`flock(1)` binary and no brew formula is installed on this host, so the
prescribed `flock -w 7200 /Volumes/Substrate-1/bigo/.build.lock bash
finish_univ3.sh` fails instantly with `nohup: flock: No such file or
directory` -- the build never starts and the log stays empty, which reads
exactly like "the build is still elaborating".  `fcntl.flock` is the same
advisory lock (BSD flock semantics) reached through the interpreter the lane
already uses.

Usage:
    python3 _build_lock.py [--secs 7200] -- <command> [args...]

Exit codes: the child's rc, or 75 if the lock could not be taken in time
(EX_TEMPFAIL -- "busy", not "failed").
"""
from __future__ import annotations

import argparse
import fcntl
import os
import subprocess
import sys
import time

LOCK_PATH = "/Volumes/Substrate-1/bigo/.build.lock"


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--secs", type=int, default=7200)
    parser.add_argument("--poll", type=float, default=5.0)
    parser.add_argument("cmd", nargs=argparse.REMAINDER)
    ns = parser.parse_args(argv)

    cmd = ns.cmd[1:] if ns.cmd and ns.cmd[0] == "--" else ns.cmd
    if not cmd:
        print("_build_lock: no command given", file=sys.stderr)
        return 64

    deadline = time.monotonic() + ns.secs
    with open(LOCK_PATH, "a+") as lock_file:
        while True:
            try:
                fcntl.flock(lock_file, fcntl.LOCK_EX | fcntl.LOCK_NB)
                break
            except BlockingIOError:
                if time.monotonic() >= deadline:
                    print(
                        f"_build_lock: lock busy for {ns.secs}s, giving up "
                        f"(EX_TEMPFAIL -- busy, not failed)",
                        file=sys.stderr,
                    )
                    return 75
                time.sleep(ns.poll)

        print(f"_build_lock: acquired {LOCK_PATH} at {time.strftime('%FT%TZ', time.gmtime())}",
              flush=True)
        env = dict(os.environ)
        env["APSP_LOCK_HELD"] = "1"
        rc = subprocess.call(cmd, env=env)
        print(f"_build_lock: child rc={rc}", flush=True)
        return rc


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
