#!/usr/bin/env python3
"""Check coverage, the declaration audit, proof mutants and final acceptance separately."""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

import mutation_spans
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
AUDITOR_ROOT = ROOT
MANIFEST = Path("tests/audit/public-api.json")


class Rejected(Exception):
    pass


def run(args: list[str], *, stdout=None) -> subprocess.CompletedProcess:
    return subprocess.run(args, cwd=ROOT, text=True, stdout=stdout, check=True)


def read_names(path: Path) -> list[str]:
    if not path.is_file() or path.is_symlink():
        raise Rejected(f"missing registry: {path}")
    names = [s.strip() for s in path.read_text().splitlines()
             if s.strip() and not s.lstrip().startswith("#")]
    if not names or len(names) != len(set(names)):
        raise Rejected(f"empty or duplicate registry: {path}")
    return names


def public_names(header: str) -> set[str]:
    header = re.sub(r"/\*.*?\*/", "", header, flags=re.S)
    return set(re.findall(r"ZEXTERN\s+[^;]*?\bZEXPORT(?:VA)?\s+(\w+)\s*\(", header, re.S))


UNDOCUMENTED_MARK = "/* undocumented functions (not part of the zlib API) */"


def undocumented_names(header: str) -> set[str]:
    """The exported functions zlib.h declares after its undocumented-functions comment."""
    at = header.find(UNDOCUMENTED_MARK)
    return public_names(header[at:]) if at >= 0 else set()


def required_public_goals(manifest: dict) -> list[str]:
    """The required targets: the safety goal of every function compiled by the target and part of
    the zlib API, the listed safety goals and the non-vacuity goals
    (docs/design/safety-functional-split.md).

    zlib.h declares some exported functions as undocumented and not part of the zlib API. They stay
    in the inventory, and their registered theorems stay audited, but their goals are not required.
    A functional goal is not required: a registered proof of it is audited in full, an unproved one
    is reported and fails nothing.
    """
    hidden = set(manifest.get("undocumented", {}).get("functions", []))
    required = [a["safety_goal"] for a in manifest["apis"]
                if a["scope"] == "lp64-linux" and a["function"] not in hidden]
    required += manifest.get("safety_goals", []) + manifest.get("nonvacuity_goals", [])
    return list(dict.fromkeys(required))


def functional_goals(manifest: dict) -> list[str]:
    """The functional goals: each function's full contract and the sequence goals. Not required."""
    goals = [a["functional_goal"] for a in manifest["apis"] if a["scope"] == "lp64-linux"]
    return list(dict.fromkeys(goals + manifest.get("sequence_goals", [])))


def open_safety(manifest: dict) -> list[str]:
    return [entry["goal"] for entry in manifest.get("open_safety", [])]


def check_open_safety(manifest: dict) -> None:
    """`open_safety` names required goals that have no registered theorem yet, each with an owner."""
    entries = manifest.get("open_safety")
    if not isinstance(entries, list):
        raise Rejected("open_safety must be a list")
    required = set(required_public_goals(manifest))
    names = []
    for entry in entries:
        if not isinstance(entry, dict) or set(entry) != {"goal", "owner"} or \
                not isinstance(entry["owner"], str) or not entry["owner"].strip():
            raise Rejected(f"open_safety entries need a goal and an owner: {entry}")
        if entry["goal"] not in required:
            raise Rejected(f"open_safety names a goal that is not required: {entry['goal']}")
        names.append(entry["goal"])
    if len(names) != len(set(names)):
        raise Rejected("duplicate open_safety entry")


def base_revision() -> str:
    """The base branch the open list is compared with: ZLIBF_BASE_REF, else the pull request's
    base branch, else origin/main. When that is this very commit (a run on main), its first parent."""
    ref = os.environ.get("ZLIBF_BASE_REF") or \
        ("origin/" + os.environ["GITHUB_BASE_REF"] if os.environ.get("GITHUB_BASE_REF") else "origin/main")
    try:
        base = subprocess.check_output(["git", "rev-parse", "--verify", ref + "^{commit}"],
                                       cwd=ROOT, text=True, stderr=subprocess.DEVNULL).strip()
        head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
        if base == head:
            base = subprocess.check_output(["git", "rev-parse", "--verify", "HEAD^"],
                                           cwd=ROOT, text=True, stderr=subprocess.DEVNULL).strip()
    except subprocess.CalledProcessError:
        raise Rejected(f"base branch {ref} is not available: fetch it, or set ZLIBF_BASE_REF")
    return base


def check_open_safety_shrinks(manifest: dict) -> None:
    """The open list only shrinks: a goal that the base branch requires and does not list as open
    may not become open. A goal new to the required set may enter the open list."""
    base = base_revision()
    try:
        text = subprocess.check_output(["git", "show", f"{base}:{MANIFEST.as_posix()}"],
                                       cwd=ROOT, text=True, stderr=subprocess.DEVNULL)
    except subprocess.CalledProcessError:
        raise Rejected(f"the base branch {base} has no {MANIFEST}")
    previous = json.loads(text)
    if "open_safety" not in previous:
        # The base predates the open list; it closes no goal, so there is nothing to compare.
        print(f"open_safety: base {base[:12]} predates the open list")
        return
    closed = set(required_public_goals(previous)) - set(open_safety(previous))
    reopened = sorted(closed & set(open_safety(manifest)))
    if reopened:
        raise Rejected("open_safety grew: required goals closed on the base branch are open again: " +
                       ", ".join(reopened))
    print(f"open_safety: {len(open_safety(manifest))} open, base {base[:12]} had "
          f"{len(open_safety(previous))}")


def check_required_proved(report: Path, manifest: dict) -> None:
    """Every required goal that is not listed as open has a registered theorem of exactly its type."""
    proved = set(re.findall(r"^goal (\S+) PROVED by ", report.read_text(), re.M))
    missing = [g for g in required_public_goals(manifest)
               if g not in proved and g not in set(open_safety(manifest))]
    if missing:
        raise Rejected("required goals without a registered theorem and not listed in open_safety: " +
                       ", ".join(missing))
    listed_proved = sorted(set(open_safety(manifest)) & proved)
    if listed_proved:
        raise Rejected("open_safety lists proved goals; remove them: " + ", ".join(listed_proved))


def mutation_apis(manifest: dict) -> dict:
    """The public functions by the goal their mutants are replayed against.

    Each function is keyed by its functional goal from the public inventory, and also by its
    safety goal where that goal belongs to this function alone (not a sequence goal shared by
    several functions), so mutants of that function are checked against the proof of either.
    """
    lp64 = [a for a in manifest["apis"] if a["scope"] == "lp64-linux"]
    apis = {a["functional_goal"]: a for a in lp64}
    shared = {}
    for a in lp64:
        if a.get("safety_goal"):
            shared.setdefault(a["safety_goal"], []).append(a)
    for goal, owners in shared.items():
        if len(owners) == 1:
            apis.setdefault(goal, owners[0])
    return apis


def public_mutants(manifest: dict) -> dict:
    packet = json.loads((ROOT / "tests/audit/public-mutants.json").read_text())
    if set(packet) != {"version", "targets"} or packet["version"] != 1:
        raise Rejected("unknown public proof mutation manifest")
    apis = mutation_apis(manifest)
    targets = packet["targets"]
    if not isinstance(targets, dict) or set(targets) - set(apis):
        raise Rejected("unknown public mutation target")
    allowed = {"tests/audit/proofmut", "tests/proof-mutants", "tests/proofmut"}
    for goal, references in targets.items():
        if not isinstance(references, list) or not references:
            raise Rejected(f"no translation mutants for {goal}")
        api = apis[goal]
        source = (ROOT / api["source"]).read_text()
        start = re.search(r"^def\s+«?" + re.escape(api["function"]) + r"»?(?:\s|:)", source, re.M)
        if not start:
            raise Rejected(f"missing mutation entry: {api['function']}")
        following = re.search(r"^(?:def|theorem|abbrev|instance|structure|inductive|namespace|end)\b",
                              source[start.end():], re.M)
        end = start.end() + following.start() if following else len(source)
        body = source.find(":=", start.end(), end)
        if body < 0:
            raise Rejected(f"missing translated function body: {api['function']}")
        signature = source[start.start():body + 2]
        seen = set()
        for reference in references:
            if not isinstance(reference, dict) or set(reference) != {"list", "name"} or \
                    not isinstance(reference["name"], str) or not reference["name"]:
                raise Rejected(f"invalid mutation reference for {goal}")
            path = Path(reference["list"])
            key = (str(path), reference["name"])
            if str(path.parent) not in allowed or path.suffix != ".tsv" or key in seen:
                raise Rejected(f"invalid or duplicate mutation list for {goal}")
            seen.add(key)
            rows = [line.split("\t") for line in (ROOT / path).read_text().splitlines()
                    if line and not line.startswith("#")]
            matching = [row for row in rows if row[0] == reference["name"]]
            if len(matching) != 1 or not 5 <= len(matching[0]) <= 6:
                raise Rejected(f"missing or ambiguous mutation for {goal}: {key}")
            row = matching[0]
            old, new = row[2].replace("\\n", "\n"), row[3].replace("\\n", "\n")
            position = source.find(old)
            if row[1] != api["source"] or (len(row) == 6 and row[5]) or not row[4] or \
                    not old or old == new or source.count(old) != 1 or \
                    position < start.start() or position + len(old) > end or \
                    not source.replace(old, new).startswith(signature, start.start()):
                raise Rejected(f"mutation must change the actual function body without a gap: {goal}: {key}")
    return targets


def check_public_mutant_coverage(report: Path, manifest: dict) -> None:
    targets = public_mutants(manifest)
    public = {a["functional_goal"] for a in manifest["apis"] if a["scope"] == "lp64-linux"}
    proved = set(re.findall(r"^goal (\S+) PROVED by ", report.read_text(), re.M))
    missing = (proved & public) - set(targets)
    if missing:
        raise Rejected("proved public targets have no function mutants: " + ", ".join(sorted(missing)))


def source_module(path: str) -> str:
    return ".".join("«" + part + "»" for part in Path(path).with_suffix("").parts)


def check_public_mutant_spans(manifest: dict, selected: set[str] | None = None) -> None:
    """Parse both source commands without loading candidate imports or executing commands."""
    targets = public_mutants(manifest)
    apis = mutation_apis(manifest)
    for goal, references in targets.items():
        if selected is not None and goal not in selected:
            continue
        api = apis[goal]
        original = ROOT / api["source"]
        source = original.read_text()
        for reference in references:
            row = mutation_row(reference)
            with tempfile.TemporaryDirectory(prefix="public-mutation-syntax-") as directory:
                mutant = Path(directory) / "mutant.lean"
                mutant.write_text(source.replace(row[2].replace("\\n", "\n"),
                                                 row[3].replace("\\n", "\n")))
                try:
                    mutation_spans.check(original, mutant, api["function"])
                except (ValueError, subprocess.TimeoutExpired) as error:
                    raise Rejected(f"mutation is outside the parsed function body: {goal}: {error}") from error



REPLAY_RSS_LIMIT = int(os.environ.get("ZLIBF_REPLAY_RSS_MB", "12288")) * 2**20
REPLAY_WARN_RSS = 11 * 2**30


def group_rss(group: int) -> int:
    """Resident bytes of every process in a process group (Linux /proc; 0 elsewhere)."""
    total = 0
    for entry in Path("/proc").glob("[0-9]*"):
        try:
            fields = (entry / "stat").read_text().rsplit(")", 1)[1].split()
            if int(fields[2]) != group:
                continue
            for line in (entry / "status").read_text().splitlines():
                if line.startswith("VmRSS:"):
                    total += int(line.split()[1]) * 1024
        except (OSError, ValueError, IndexError):
            continue
    return total


def run_replay(args: list[str], what: str) -> subprocess.CompletedProcess:
    """Run one kernel replay in its own process group, within a resident-memory budget.

    A legitimate replay of the largest registered closure stays near 10.5 GB. A replay
    whose kernel work grows without bound is stopped at the budget and fails closed,
    so the stage stays inside the 16 GB build limit instead of meeting the
    out-of-memory killer (which may also hit unrelated processes).
    """
    process = subprocess.Popen(args, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE, start_new_session=True)
    stdout, stderr, over, peak = "", "", False, 0
    while True:
        try:
            stdout, stderr = process.communicate(timeout=2)
            break
        except subprocess.TimeoutExpired:
            peak = max(peak, group_rss(process.pid))
            if peak > REPLAY_RSS_LIMIT:
                over = True
                os.killpg(process.pid, 9)
    if over:
        raise Rejected(f"replay over budget ({REPLAY_RSS_LIMIT >> 20} MB): {what}: move this row to a "
                       "source-level table if it edits a loop body or machine arithmetic "
                       "(docs/checking/proof-mutants.md)")
    result = subprocess.CompletedProcess(args, process.returncode, stdout, stderr)
    result.peak = peak
    return result


def report_peak(goal: str, peak: int) -> None:
    """Print the peak of a legitimate replay; warn when it nears the budget.

    The budget is not raised when closures grow: the fix is a smaller replay closure.
    """
    print(f"replay peak: {goal}: {peak >> 20} MB", flush=True)
    if peak > REPLAY_WARN_RSS:
        print(f"WARNING: legitimate replay of {goal} peaked at {peak >> 20} MB, above "
              f"{REPLAY_WARN_RSS >> 20} MB of the {REPLAY_RSS_LIMIT >> 20} MB budget", flush=True)


def mutation_row(reference: dict) -> list[str]:
    return next(line.split("\t") for line in (ROOT / reference["list"]).read_text().splitlines()
                if line and not line.startswith("#") and line.split("\t")[0] == reference["name"])


def copy_build_cache(source: Path, destination: Path) -> None:
    """Copy compiler artifacts, not unused native audit executables.

    The variant builds a translated module and replays through the original
    snapshot's absolute tool path. Copying its native tools into every variant
    adds large binaries that are never used. Keep all module traces and objects.
    """
    build = source.resolve() / 'build'
    shutil.copytree(source, destination, ignore=lambda path, names:
                    {'bin'} if Path(path).resolve() == build else set())


def replay_public_mutants(manifest: dict, selected: set[str] | None = None) -> None:
    """A failure in an unrelated or stronger theorem does not count."""
    targets = public_mutants(manifest)
    apis = mutation_apis(manifest)
    library = ROOT / ".lake/build/lib/lean"
    # Compile the unchanged replay program once. Each invocation still creates
    # a fresh kernel and checks the exact original registered proof closure.
    subprocess.run(['lake', 'build', 'zlibf-proof-replay'], cwd=AUDITOR_ROOT, check=True)
    replay = AUDITOR_ROOT / '.lake/build/bin/zlibf-proof-replay'
    registry = ROOT / "tests/audit/theorems.txt"
    for goal, references in targets.items():
        if selected is not None and goal not in selected:
            continue
        api = apis[goal]
        module = source_module(api["source"])
        command = ["lake", "env", str(replay), str(library)]
        control = run_replay(command + [str(library), module, goal, str(registry)], goal)
        sys.stdout.write(control.stdout)
        sys.stderr.write(control.stderr)
        if control.returncode != 0:
            raise Rejected(f"exact public proof does not replay: {goal}")
        report_peak(goal, control.peak)
        for reference in references:
            row = mutation_row(reference)
            with tempfile.TemporaryDirectory(prefix="public-proof-replay-") as directory:
                candidate = Path(directory)
                shutil.copytree(ROOT / "ZlibF", candidate / "ZlibF")
                for name in ("ZlibF.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain"):
                    shutil.copyfile(ROOT / name, candidate / name)
                copy_build_cache(ROOT / ".lake", candidate / ".lake")
                path = candidate / api["source"]
                path.write_text(path.read_text().replace(row[2].replace("\\n", "\n"),
                                                        row[3].replace("\\n", "\n")))
                subprocess.run(["lake", "build", module], cwd=candidate, check=True,
                               text=True, stdout=subprocess.DEVNULL)
                result = run_replay(command + [str(candidate / ".lake/build/lib/lean"), module,
                                               goal, str(registry)], f"{goal}: {reference['name']}")
                if result.returncode != 2 or not result.stdout.startswith("EXACT_PROOF_REJECTED: "):
                    raise Rejected(f"original exact public proof survives or replay failed: {goal}: "
                                   f"{reference['name']}\n{result.stdout}{result.stderr}")
                print(f"exact public proof rejects: {goal}: {reference['name']}")


SAFETY_MUTANT_LISTS = ("tests/proof-mutants/deflate-header.tsv", "tests/proof-mutants/deflate-strategies.tsv",
                       "tests/proof-mutants/deflate-ops.tsv", "tests/proof-mutants/stream-refusal.tsv",
                       "tests/proof-mutants/infback-sequence.tsv")


def mutation_partition(manifest: dict, count: int = 1, index: int = 0) -> tuple[set[str], dict[str, list[str]]]:
    """Assign every goal bundle and every full proof-list row exactly once.

    A goal's unchanged exact-proof control travels with all its public mutants.
    Full proof lists also contain cases outside the public registry. Partition
    those rows independently so none are lost or concentrated in one worker.
    """
    if count <= 0 or not 0 <= index < count:
        raise Rejected('shard count must be positive and index must be in range')
    targets = public_mutants(manifest)
    goals = {goal for ordinal, goal in enumerate(sorted(targets)) if ordinal % count == index}
    lists = {reference["list"] for references in targets.values() for reference in references}
    lists.add("tests/proof-mutants/api-boundary.tsv")
    # The semantic mutants of the deflate safety proof: script rows that edit the translation and
    # every proof restatement of it, so they cannot key a public goal, but each must be killed in
    # its semantic lemma. The public mutants of Goal.deflate are only rejected at the phase
    # restatement, so these lists carry the semantic evidence: a missing or empty one is an error.
    for path in SAFETY_MUTANT_LISTS:
        table = ROOT / path
        if not table.is_file() or table.is_symlink() or not any(
                row and not row.startswith("#") for row in table.read_text().splitlines()):
            raise Rejected(f"missing or empty semantic mutant list: {path}")
        lists.add(path)
    selected = {}
    ordinal = 0
    for path in sorted(lists):
        rows = []
        for row in (ROOT / path).read_text().splitlines():
            if not row or row.startswith('#'):
                continue
            if ordinal % count == index:
                rows.append(row)
            ordinal += 1
        if rows:
            selected[path] = rows
    if not goals and not selected:
        raise Rejected('empty proof mutation shard')
    return goals, selected


def run_public_mutants(manifest: dict, count: int = 1, index: int = 0) -> None:
    goals, lists = mutation_partition(manifest, count, index)
    check_public_mutant_spans(manifest, goals)
    replay_public_mutants(manifest, goals)
    with tempfile.TemporaryDirectory(prefix='proof-mutation-shard-') as directory:
        for ordinal, (path, rows) in enumerate(lists.items()):
            subset = Path(directory) / (str(ordinal) + '-' + Path(path).name)
            subset.write_text('\n'.join(rows) + '\n')
            print(f'proof mutation shard {index}/{count}: {path}: {len(rows)} cases', flush=True)
            run(["env", "PROOFMUT_STRICT=1", "bash", "tests/audit/proofmut.sh", str(subset)])


def build_library() -> None:
    # Consumers must fail on a stale/missing artifact instead of silently doing
    # another full compile. Final acceptance retains its explicit clean build.
    flag = os.environ.get('ZLIBF_REQUIRE_PREBUILT', '0')
    if flag not in {'0', '1'}:
        raise Rejected('ZLIBF_REQUIRE_PREBUILT must be 0 or 1')
    run(['lake'] + (['--no-build'] if flag == '1' else []) + ['build', 'ZlibF'])


def check_imports() -> None:
    seen: set[Path] = set()

    def visit(path: Path):
        if path in seen:
            return
        seen.add(path)
        for line in path.read_text().splitlines():
            if not line.startswith("import "):
                continue
            # A quoted component may contain dots, as in «inflate.c».
            for name in line[7:].split("--", 1)[0].split():
                local = name == "ZlibF" or name.startswith("ZlibF.")
                standard = any(name == p or name.startswith(p + ".") for p in ("Init", "Std", "Lean"))
                if not local and not standard:
                    raise Rejected(f"unapproved external module: {name}")
                parts = re.findall(r"«[^»]+»|[^.]+", name)
                child = ROOT / ("/".join(p.strip("«»") for p in parts) + ".lean")
                if child.is_file():
                    if not local:
                        raise Rejected(f"local source shadows a pinned standard module: {name}")
                    visit(child)
                elif name == "ZlibF" or name.startswith("ZlibF."):
                    raise Rejected(f"import has no source (a stale object could hide it): {name}")

    visit(ROOT / "ZlibF.lean")
    missing = set((ROOT / "ZlibF").rglob("*.lean")) - seen
    if missing:
        raise Rejected("modules outside the audited import closure: " +
                       ", ".join(str(p.relative_to(ROOT)) for p in sorted(missing)))


def coverage() -> dict:
    lake_manifest = ROOT / "lake-manifest.json"
    if lake_manifest.is_file():
        expected = {"version": "1.3.0", "packagesDir": ".lake/packages", "packages": [],
                    "name": "ZlibF", "lakeDir": ".lake", "fixedToolchain": False}
        if json.loads(lake_manifest.read_text()) != expected:
            raise Rejected("unapproved package manifest; dependencies need a reviewed policy update")
    manifest = json.loads((ROOT / MANIFEST).read_text())
    if manifest.get("version") != 1:
        raise Rejected("unknown public contract manifest version")
    expected_properties = {"documented-domain", "total-execution", "functional-result", "frame", "ownership"}
    if set(manifest.get("required_properties", [])) != expected_properties:
        raise Rejected("public contract properties are incomplete")
    apis = manifest["apis"]
    names = [a["function"] for a in apis]
    header = (ROOT / "zlib/zlib.h").read_text()
    exports = public_names(header)
    if len(names) != len(set(names)) or set(names) != exports:
        raise Rejected(f"public API coverage differs: missing={sorted(exports - set(names))}, "
                       f"extra={sorted(set(names) - exports)}")
    undocumented = manifest.get("undocumented")
    listed = undocumented.get("functions", []) if isinstance(undocumented, dict) else []
    if not isinstance(undocumented, dict) or undocumented.get("header_comment") != UNDOCUMENTED_MARK or \
            not undocumented.get("reason") or len(listed) != len(set(listed)) or \
            set(listed) != undocumented_names(header):
        raise Rejected(f"undocumented functions differ from zlib.h: listed={sorted(listed)}, "
                       f"declared={sorted(undocumented_names(header))}")
    pin = subprocess.check_output(["git", "-C", "zlib", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    index = subprocess.check_output(["git", "ls-files", "-s", "zlib"], cwd=ROOT, text=True).split()
    if len(index) < 2 or index[0] != "160000":
        raise Rejected("zlib must be a pinned submodule")
    if pin != manifest["source_pin"] or pin != index[1]:
        raise Rejected("the manifest, submodule checkout and source pin disagree")
    dirty_source = subprocess.check_output(
        ["git", "-C", "zlib", "status", "--porcelain", "--untracked-files=all"], cwd=ROOT, text=True)
    if dirty_source:
        raise Rejected("the pinned source submodule has local changes")
    goals = []
    for api in apis:
        manual, anchor = api["manual"].split("#", 1)
        for relative in (manual, api.get("source", manual)):
            path = Path(relative)
            if path.is_absolute() or ".." in path.parts or (ROOT / path).is_symlink():
                raise Rejected("public inventory paths must be ordinary repository files")
        if not re.search(r"^##\s+`?" + re.escape(api["function"]) + r"`?\s*$",
                         (ROOT / manual).read_text(), re.M) or anchor != api["function"].lower():
            raise Rejected(f"missing function contract documentation: {api['function']}")
        if api["scope"] != "lp64-linux":
            if api["function"] != "gzopen_w" or api["scope"] != "windows" or not api.get("reason"):
                raise Rejected(f"unreviewed scope exclusion: {api['function']}")
            continue
        src = (ROOT / api["source"]).read_text()
        if not re.search(r"^def\s+«?" + re.escape(api["function"]) + r"»?(?:\s|:)", src, re.M):
            raise Rejected(f"missing translated entry: {api['function']}")
        namespace = re.search(r"^namespace\s+(\S+)", src, re.M)
        if not namespace or api["implementation"] != namespace[1] + "." + api["function"]:
            raise Rejected(f"wrong translated entry binding: {api['function']}")
        if api["functional_goal"] != "ZlibF.Spec.Public.Goal." + api["function"]:
            raise Rejected(f"wrong public contract target: {api['function']}")
        goals.append(api["functional_goal"])
        hidden = api["function"] in listed
        safety = api.get("safety_goal")
        if hidden:
            if safety is not None:
                raise Rejected(f"undocumented function with a required safety goal: {api['function']}")
        elif not isinstance(safety, str):
            raise Rejected(f"missing safety goal: {api['function']}")
        elif safety == api["functional_goal"]:
            if not api.get("safety_note"):
                raise Rejected(f"a full contract used as safety goal needs a safety_note: {api['function']}")
        elif safety not in manifest.get("safety_goals", []):
            raise Rejected(f"safety goal is not a listed safety target: {api['function']}: {safety}")
    groups = {
        "sequence_goals": ["inflate_sequence", "deflate_sequence", "inflate_back_sequence", "gz_sequence"],
        "nonvacuity_goals": ["inflate_initialisation_domain", "deflate_initialisation_domain",
                              "inflate_back_initialisation_domain", "gz_initialisation_domain",
                              "gz_sequence_nonvacuity"],
        "safety_goals": ["inflate_sequence_safety", "deflate_sequence_safety", "uncompress_safe", "uncompress_z_safe", "uncompress2_safe", "uncompress2_z_safe", "compress_safety", "compress_z_safety", "compress2_safety", "compress2_z_safety",
                         "inflate_back_sequence_safety", "deflateCopy_safety",
                         "inflate_refusal", "deflate_refusal", "gz_sequence_safety", "gz_refusal",
                         "inflate_safety", "inflateSetDictionary_safety", "inflateGetDictionary_safety", "inflateSync_safety",
                         "inflateReset_safety", "inflateReset2_safety", "inflatePrime_safety", "inflateMark_safety",
                         "inflateGetHeader_safety", "deflate_safety", "deflateSetDictionary_safety", "deflateGetDictionary_safety",
                         "deflateReset_safety", "deflateParams_safety", "deflateTune_safety", "deflateBound_safety",
                         "deflateBound_z_safety", "deflatePending_safety", "deflateUsed_safety", "deflatePrime_safety",
                         "deflateSetHeader_safety", "inflateEnd_safety", "deflateEnd_safety", "inflateInit2__safety",
                         "inflateInit__safety", "deflateInit2__safety", "deflateInit__safety", "inflateCopy_safety",
                         "adler32_safety", "adler32_z_safety", "adler32_combine_safety", "adler32_combine64_safety",
                         "crc32_safety", "crc32_z_safety", "crc32_combine_gen_safety", "crc32_combine_gen64_safety",
                         "crc32_combine_op_safety", "crc32_combine_safety", "crc32_combine64_safety", "zlibVersion_safety",
                         "zlibCompileFlags_safety"],
    }
    for group, suffixes in groups.items():
        expected = ["ZlibF.Spec.Public.Goal." + suffix for suffix in suffixes]
        if manifest.get(group) != expected:
            raise Rejected(f"missing {group}")
        goals.extend(manifest[group])
    if len(goals) != len(set(goals)):
        raise Rejected("public contracts must have distinct targets")
    check_open_safety(manifest)
    public_mutants(manifest)
    check_imports()
    run([sys.executable, "scripts/gen_public_calls.py", "--check"])
    print(f"coverage: {len(exports)} public declarations, "
          f"{len(goals) - len(manifest['sequence_goals']) - len(manifest['nonvacuity_goals']) - len(manifest['safety_goals'])} default-build entries "
          f"({len([a for a in apis if a['scope'] == 'lp64-linux' and a['function'] not in listed])} documented, "
          f"the rest undocumented in zlib.h), "
          f"{len(manifest['sequence_goals'])} sequence targets, {len(manifest['nonvacuity_goals'])} non-vacuity targets, "
          f"{len(manifest['safety_goals'])} safety targets; "
          f"{len(required_public_goals(manifest))} required goals, {len(open_safety(manifest))} open")
    return manifest


def build_auditor() -> Path:
    """Compile the invoking snapshot's auditor, never a candidate-supplied tool."""
    subprocess.run(["lake", "build", "zlibf-audit"], cwd=AUDITOR_ROOT, check=True)
    return AUDITOR_ROOT / ".lake/build/bin/zlibf-audit"


def audit(report: Path, *, strict: bool = False, public: bool = False) -> int:
    names = read_names(ROOT / "tests/audit/goals.txt")
    if public:
        manifest = coverage()
        listed = required_public_goals(manifest) + functional_goals(manifest)
        names += [name for name in listed if name not in names]
    with tempfile.TemporaryDirectory(prefix="verification-goals-") as directory:
        targets = Path(directory) / "goals.txt"
        targets.write_text("\n".join(names) + "\n")
        args = ["lake", "env", str(build_auditor()),
                "tests/audit/theorems.txt", str(targets)]
        if strict:
            args.append("--require-complete")
        with report.open("w") as out:
            return subprocess.run(args, cwd=ROOT, text=True, stdout=out).returncode


def main() -> int:
    global ROOT
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("coverage", "check", "specs", "mutants", "final"))
    parser.add_argument("--report", type=Path)
    parser.add_argument("--root", type=Path, help="candidate checkout; the auditor remains the invoking snapshot")
    parser.add_argument('--shard-count', type=int, default=1)
    parser.add_argument('--shard-index', type=int, default=0)
    args = parser.parse_args()
    if args.root:
        ROOT = args.root.resolve()
    try:
        if args.mode != 'mutants' and (args.shard_count, args.shard_index) != (1, 0):
            raise Rejected('sharding applies only to the mutants stage')
        manifest = coverage()
        if args.mode == "coverage":
            print("coverage is not specification readiness or proof completion")
            return 0
        if args.mode == "mutants":
            mutation_partition(manifest, args.shard_count, args.shard_index)
            build_library()
            run_public_mutants(manifest, args.shard_count, args.shard_index)
            print("stage passed: mutants")
            return 0
        if args.mode == "final":
            if os.environ.get('ZLIBF_REQUIRE_PREBUILT', '0') != '0':
                raise Rejected('final acceptance requires a clean build')
            run(["lake", "clean"])
        build_library()
        check_public_mutant_spans(manifest)
        # Recheck the compiled proof terms in a fresh kernel environment, not just the build trace.
        run(["lake", "env", "leanchecker", "--fresh", "ZlibF"])
        with tempfile.TemporaryDirectory(prefix="verification-report-") as directory:
            report = args.report or Path(directory) / "audit.txt"
            # The auditor's strict mode would reject every unproved goal, functional ones included.
            # Only the required goals are required: check_required_proved below.
            rc = audit(report, public=args.mode in ("specs", "final"))
            if rc:
                for line in report.read_text().splitlines():
                    if line.startswith(("goal ", "PROBLEM:")):
                        print(line)
                raise Rejected("audit rejected the requested verification stage")
            check_public_mutant_coverage(report, manifest)
            if args.mode in ("specs", "final"):
                check_required_proved(report, manifest)
                check_open_safety_shrinks(manifest)
            if args.mode == "final" and open_safety(manifest):
                raise Rejected("final acceptance requires an empty open_safety: " +
                               ", ".join(open_safety(manifest)))
        if args.mode == "final":
            dirty = subprocess.check_output(["git", "status", "--porcelain", "--untracked-files=normal"],
                                            cwd=ROOT, text=True)
            if dirty:
                raise Rejected("final acceptance requires a clean committed source tree")
            run(["bash", "scripts/check-sorry.sh"])
            run(["bash", "tests/audit/selftest.sh"])
            replay_public_mutants(manifest)
            run(["env", f"ZLIB_SRC={ROOT / 'zlib'}", "bash", "tests/run.sh"])
            run(["env", "SAN=1", f"ZLIB_SRC={ROOT / 'zlib'}", "bash", "tests/run.sh"])
            run(["env", f"ZLIB_BUILD={ROOT / 'tests/build/zlib'}", "bash", "tests/selftest.sh"])
            mutation_lists = sorted(path for directory in
                ("tests/audit/proofmut", "tests/proof-mutants", "tests/proofmut")
                for path in (ROOT / directory).glob("*.tsv"))
            if not mutation_lists:
                raise Rejected("final acceptance requires proof mutation lists")
            for mutations in mutation_lists:
                run(["env", "PROOFMUT_STRICT=1", "bash", "tests/audit/proofmut.sh",
                     str(mutations.relative_to(ROOT))])
            commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
            print(f"final acceptance on commit: {commit}")
        print("stage passed: " + args.mode)
        if args.mode == "check":
            print("development audit only; public specification readiness and final proofs are separate gates")
        return 0
    except (Rejected, OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        print(f"REJECTED: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
