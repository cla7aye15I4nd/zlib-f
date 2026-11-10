#!/usr/bin/env python3
"""Queue committed source snapshots for a separate verification worker."""
from __future__ import annotations

import argparse
import fcntl
import errno
import hashlib
import json
import os
import re
import shutil
from pathlib import Path
import subprocess
import sys
import time
import uuid

STAGES = {
    "build": ["lake", "build", "ZlibF"],
    "no-sorry": ["bash", "scripts/check-sorry.sh"],
    "audit": [sys.executable, "scripts/verification.py", "specs"],
    "mutants": [sys.executable, "scripts/verification.py", "mutants"],
}


def write_json(path: Path, value: dict) -> None:
    temporary = path.with_name(path.name + "." + uuid.uuid4().hex)
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    os.replace(temporary, path)


def git(repo: Path, *args: str) -> str:
    return subprocess.check_output(["git", "-C", str(repo), *args], text=True).strip()


def enqueue(repo: Path, spool: Path, revision: str, stages: list[str]) -> tuple[str, bool]:
    commit = git(repo, "rev-parse", "--verify", revision + "^{commit}")
    # Canonical ordering also deduplicates a different ordering of the same request.
    stages = [stage for stage in STAGES if stage in stages]
    key = hashlib.sha256((str(repo) + commit + json.dumps(stages)).encode()).hexdigest()[:24]
    job = spool / "jobs" / key
    job.parent.mkdir(parents=True, exist_ok=True)
    pending = spool / ("pending-" + uuid.uuid4().hex)
    pending.mkdir()
    write_json(pending / "request.json", {"repository": str(repo), "commit": commit,
               "stages": stages, "created": time.time(), "key": key})
    write_json(pending / "state.json", {"status": "queued"})
    try:
        pending.rename(job)
    except OSError as error:
        shutil.rmtree(pending)
        if error.errno not in (errno.EEXIST, errno.ENOTEMPTY):
            raise
        return key, False
    return key, True


def snapshot(request: dict, destination: Path, log) -> None:
    repo = Path(request["repository"])
    subprocess.run(["git", "clone", "--no-hardlinks", "--no-checkout", str(repo), str(destination)],
                   stdout=log, stderr=subprocess.STDOUT, check=True)
    subprocess.run(["git", "checkout", "--detach", request["commit"]], cwd=destination,
                   stdout=log, stderr=subprocess.STDOUT, check=True)
    # Use the exact recorded gitlink, never the mutable source submodule checkout.
    for line in git(destination, "ls-tree", "-r", "HEAD").splitlines():
        metadata, name = line.split("\t", 1)
        mode, _, pin = metadata.split()
        if mode != "160000":
            continue
        if name != "zlib":
            raise ValueError("unsupported submodule: " + name)
        target = destination / name
        subprocess.run(["git", "clone", "--no-hardlinks", "--no-checkout", str(repo / name), str(target)],
                       stdout=log, stderr=subprocess.STDOUT, check=True)
        subprocess.run(["git", "checkout", "--detach", pin], cwd=target,
                       stdout=log, stderr=subprocess.STDOUT, check=True)


def process(job: Path, spool: Path, hook: str | None = None) -> dict:
    request = json.loads((job / "request.json").read_text())
    result = {"key": job.name, "commit": request["commit"], "status": "running",
              "started": time.time(), "stages": [], "acceptance": "development checks only"}
    write_json(job / "state.json", result)
    try:
        with (job / "snapshot.log").open("w") as log:
            snapshot(request, job / "source", log)
        for stage in request["stages"]:
            start = time.time()
            with (job / (stage + ".log")).open("w") as log:
                checked = subprocess.run(STAGES[stage], cwd=job / "source", stdout=log,
                                         stderr=subprocess.STDOUT)
            result["stages"].append({"name": stage, "exit": checked.returncode,
                                      "seconds": time.time() - start})
            write_json(job / "state.json", result)
            if checked.returncode:
                result["status"] = "failed"
                break
        else:
            result["status"] = "passed"
    except Exception as error:
        result.update(status="failed", error=str(error))
    result["finished"] = time.time()
    write_json(job / "state.json", result)
    events = spool / "events"
    events.mkdir(exist_ok=True)
    event = events / (job.name + ".json")
    write_json(event, {**result, "result": str(job / "state.json")})
    # Notification failure never changes the verification outcome. The event is durable.
    if hook:
        try:
            with (job / "notification.log").open("w") as log:
                sent = subprocess.run([hook, str(event)], stdout=log, stderr=subprocess.STDOUT,
                                      timeout=60)
            write_json(job / "notification.json", {"exit": sent.returncode})
        except Exception as error:
            write_json(job / "notification.json", {"error": str(error)})
    return result


def worker(spool: Path, once: bool, interval: float, hook: str | None,
           repository: Path | None = None, watch_ref: str | None = None) -> None:
    spool.mkdir(parents=True, exist_ok=True)
    with (spool / "worker.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        while True:
            if watch_ref:
                enqueue(repository, spool, watch_ref, ["build", "no-sorry"])
            jobs = sorted((spool / "jobs").glob("*/state.json"), key=lambda p: p.stat().st_mtime)
            pending = [p.parent for p in jobs if json.loads(p.read_text())["status"] == "queued"]
            if pending:
                print(json.dumps(process(pending[0], spool, hook)), flush=True)
            if once:
                return
            if not pending:
                time.sleep(interval)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository", type=Path, default=Path.cwd())
    parser.add_argument("--spool", type=Path)
    sub = parser.add_subparsers(dest="command", required=True)
    submit = sub.add_parser("submit")
    submit.add_argument("revision", nargs="?", default="HEAD")
    submit.add_argument("--stages", nargs="+", choices=STAGES, default=["build", "no-sorry"])
    run = sub.add_parser("worker")
    run.add_argument("--once", action="store_true")
    run.add_argument("--watch-ref", help="enqueue new commits from this ref before checking the queue")
    run.add_argument("--interval", type=float, default=5)
    run.add_argument("--on-result", help="executable called with the durable event path")
    sub.add_parser("status")
    retry = sub.add_parser("retry")
    retry.add_argument("key")
    watch = sub.add_parser("watch")
    watch.add_argument("--ref", default="HEAD")
    watch.add_argument("--interval", type=float, default=5)
    args = parser.parse_args()
    repo = Path(git(args.repository.resolve(), "rev-parse", "--show-toplevel"))
    spool = (args.spool or repo / ".lake" / "verification-queue").resolve()
    if args.command == "submit":
        key, created = enqueue(repo, spool, args.revision, args.stages)
        print(json.dumps({"key": key, "queued": created}))
    elif args.command == "worker":
        if args.interval <= 0:
            parser.error("interval must be positive")
        worker(spool, args.once, args.interval, args.on_result, repo, args.watch_ref)
    elif args.command == "retry":
        if not re.fullmatch(r"[0-9a-f]{24}", args.key):
            parser.error("invalid job key")
        with (spool / "worker.lock").open("a") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            job = spool / "jobs" / args.key
            if not (job / "request.json").is_file():
                parser.error("unknown job")
            history = job / "history" / uuid.uuid4().hex
            history.mkdir(parents=True)
            for path in job.iterdir():
                if path.name not in ("history", "request.json"):
                    path.rename(history / path.name)
            write_json(job / "state.json", {"status": "queued"})
    elif args.command == "watch":
        if args.interval <= 0:
            parser.error("interval must be positive")
        while True:
            key, created = enqueue(repo, spool, args.ref, ["build", "no-sorry"])
            if created:
                print(json.dumps({"key": key, "queued": True}), flush=True)
            time.sleep(args.interval)
    else:
        for path in sorted((spool / "jobs").glob("*/state.json")):
            print(json.dumps({"key": path.parent.name, **json.loads(path.read_text())}))


if __name__ == "__main__":
    main()
