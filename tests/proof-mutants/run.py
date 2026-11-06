#!/usr/bin/env python3
"""Run the API boundary proof mutants in isolated copies.

Usage: python3 tests/proof-mutants/run.py [list.tsv] [--report report.json] [--keep]

The list has the same five TAB-separated fields as the existing proof-mutant lists.
Proof module paths such as Api/Concrete are converted to ZlibF.Proof.Api.Concrete.
The original audit runner quotes the entire path and cannot build directory modules.
A baseline must build first. A mutant is killed only when its first source error is
inside an explicitly listed proof module. Timeouts, translation errors and missing
replacement text fail the check. The workspace and the warm cache are never changed.

PROOFMUT_CACHE selects the warm .lake directory. PROOFMUT_TIMEOUT is the per-build
limit in seconds (default 3600). Literal backslash-n in OLD/NEW denotes a newline.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile


def build(workspace, modules, timeout, log):
    targets = ["ZlibF.Proof." + module.replace("/", ".") for module in modules]
    try:
        with log.open("w") as output:
            result = subprocess.run(
                ["lake", "build", *targets], cwd=workspace, stdout=output,
                stderr=subprocess.STDOUT, timeout=timeout, check=False,
            )
        return result.returncode
    except subprocess.TimeoutExpired:
        with log.open("a") as output:
            output.write("\nAPI proof-mutant build timed out.\n")
        return 124


def main():
    root = Path(__file__).resolve().parents[2]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("list", nargs="?", type=Path, default=root / "tests/proof-mutants/api-boundary.tsv")
    parser.add_argument("--report", type=Path)
    parser.add_argument("--keep", action="store_true", help="keep isolated copies and build logs")
    args = parser.parse_args()
    cache = Path(os.environ.get("PROOFMUT_CACHE", root / ".lake")).resolve()
    if not cache.is_dir():
        parser.error("no warm .lake directory; set PROOFMUT_CACHE")
    if shutil.which("lake") is None:
        parser.error("lake is not on PATH")
    timeout = int(os.environ.get("PROOFMUT_TIMEOUT", "3600"))
    if timeout <= 0:
        parser.error("PROOFMUT_TIMEOUT must be positive")

    rows = []
    hashes = {}
    for number, line in enumerate(args.list.read_text().splitlines(), 1):
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        columns = line.split("\t")
        if len(columns) != 5:
            parser.error(f"line {number}: expected exactly five TAB-separated fields")
        name, file, old, new, raw_modules = columns
        modules = raw_modules.split(",")
        if not name or any(not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(/[A-Za-z_][A-Za-z_0-9]*)*", m) for m in modules):
            parser.error(f"line {number}: invalid name or proof module path")
        relative = Path(file)
        if relative.is_absolute() or ".." in relative.parts:
            parser.error(f"line {number}: FILE must stay inside the workspace")
        source = root / relative
        old, new = old.replace("\\n", "\n"), new.replace("\\n", "\n")
        if old == new or not old or source.read_text().count(old) != 1:
            parser.error(f"line {number}: OLD must occur exactly once and differ from NEW")
        for path in [source, *(root / "ZlibF/Proof" / (m + ".lean") for m in modules)]:
            if not path.is_file():
                parser.error(f"line {number}: missing file {path.relative_to(root)}")
            hashes[str(path.relative_to(root))] = hashlib.sha256(path.read_bytes()).hexdigest()
        rows.append((name, file, old, new, modules))
    if not rows:
        parser.error("empty mutant list")
    if len({row[0] for row in rows}) != len(rows):
        parser.error("mutant names must be unique")

    temporary = Path(tempfile.mkdtemp(prefix="api-proofmut-"))
    report = {"baseline_sha256": hashes, "baseline_exit": None, "mutants": []}
    try:
        def copy_workspace(destination):
            shutil.copytree(root, destination, ignore=shutil.ignore_patterns(".git", ".lake", "build", "zlib", "__pycache__"))
            shutil.copytree(cache, destination / ".lake")

        baseline = temporary / "baseline"
        copy_workspace(baseline)
        modules = sorted({m for row in rows for m in row[4]})
        report["baseline_exit"] = build(baseline, modules, timeout, temporary / "baseline.log")
        if report["baseline_exit"] != 0:
            print("BASELINE FAILED: the unmutated proof modules do not build", flush=True)
            print((temporary / "baseline.log").read_text()[-8000:])
            return 1
        print("BASELINE PASS: " + ", ".join(modules), flush=True)
        shutil.rmtree(baseline)

        for index, (name, file, old, new, modules) in enumerate(rows):
            candidate = temporary / f"mutant-{index}"
            copy_workspace(candidate)
            source = candidate / file
            source.write_text(source.read_text().replace(old, new, 1))
            log = temporary / f"mutant-{index}.log"
            exit_code = build(candidate, modules, timeout, log)
            match = re.search(r"^error: ([^\n]+?\.lean):[0-9]+:[0-9]+:.*", log.read_text(), re.MULTILINE)
            first_error = match.group(0) if match else ""
            error_file = match.group(1) if match else ""
            path = Path(error_file)
            if path.is_absolute():
                try:
                    error_file = str(path.relative_to(candidate))
                except ValueError:
                    pass
            expected = {"ZlibF/Proof/" + m + ".lean" for m in modules}
            killed = exit_code not in (0, 124) and error_file in expected
            report["mutants"].append({"name": name, "exit": exit_code,
                "killed_in_expected_proof": killed, "first_error": first_error})
            print(f"{name}: {'KILLED' if killed else 'FAILED'} {first_error}", flush=True)
            if not args.keep:
                shutil.rmtree(candidate)
        passed = all(item["killed_in_expected_proof"] for item in report["mutants"])
        print("PROOFMUT " + ("PASS" if passed else "FAIL"), flush=True)
        return 0 if passed else 1
    finally:
        if args.report:
            args.report.parent.mkdir(parents=True, exist_ok=True)
            args.report.write_text(json.dumps(report, indent=2) + "\n")
        if args.keep:
            print(f"Kept evidence: {temporary}")
        else:
            shutil.rmtree(temporary)


if __name__ == "__main__":
    sys.exit(main())
