#!/usr/bin/env python3
"""Positive CRC comparisons on actual model byte views and native buffers."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shlex
import shutil
import subprocess
import tempfile
import time

BOUNDARIES = [0, 1, 7, 8, 39, 40, 46, 47, 48, 79, 80, 81]
SEEDS = [0, 0x12345678, 0xFFFFFFFFFFFFFFFF]
ENTRIES = ["crc32_z", "crc32"]
NAMES = ["raw", "str", "str_empty", "dstate_depth", "st_dist_code", "st_length_code"]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def module_path(name):
    parts, part, quoted = [], "", False
    for ch in name:
        if ch == "«":
            quoted = True
        elif ch == "»":
            quoted = False
        elif ch == "." and not quoted:
            parts.append(part)
            part = ""
        else:
            part += ch
    return Path(*parts, part + ".lean")


def closure(root, names):
    found = {}

    def visit(name):
        if not name.startswith("ZlibF.") or name in found:
            return
        rel = module_path(name)
        source = (root / rel).read_text()
        found[name] = rel
        for line in source.splitlines():
            if line.startswith("import "):
                for dep in line[7:].split():
                    visit(dep)

    for name in names:
        visit(name)
    return found


def parse_export(path):
    result = {}
    for line in path.read_text().splitlines():
        tag, name, size, string_id, data = line.split("|")
        assert tag == "DATA"
        raw = bytes.fromhex(data)
        assert len(raw) == int(size)
        result[name] = {"bytes": raw, "string_id": int(string_id)}
    assert list(result) == NAMES
    return result


def write_fixtures(path, views):
    lines = []
    for name, data in views.items():
        raw = data["bytes"]
        if name.startswith("str"):
            assert raw[-1:] == b"\0"
            literal = "".join("\\x%02x" % b for b in raw[:-1])
            lines.append(f'static const unsigned char fixture_{name}[] = "{literal}";')
        else:
            values = ",".join(str(b) for b in raw)
            lines.append(f"static const unsigned char fixture_{name}[] = {{{values}}};")
    path.write_text("\n".join(lines) + "\n")


def write_cases(path, views):
    records, coverage = [], {}
    for name, data in views.items():
        size = len(data["bytes"])
        offsets = sorted(set(range(8)) | {15, 16, 39, 40, 46, 47, 48, 79, 80, 81, max(size - 1, 0), size})
        offsets = [n for n in offsets if n <= size]
        lengths_seen = set()
        for off in offsets:
            available = size - off
            lengths = sorted(set(BOUNDARIES) | {available, max(available - 1, 0)})
            for length in lengths:
                if length > available:
                    continue
                lengths_seen.add(length)
                for seed in SEEDS:
                    for entry in ENTRIES:
                        records.append((entry, name, off, length, seed))
        coverage[name] = {"size": size, "offsets": offsets, "lengths": sorted(lengths_seen)}
    path.write_text("".join(" ".join(map(str, row)) + "\n" for row in records))
    return records, coverage


def parse_native(path, views, cases):
    rows, origins, meta, end = {}, {}, None, None
    for line in path.read_text().splitlines():
        fields = line.split("|")
        if fields[0] == "META":
            meta = dict(zip(["ulong_bytes", "size_t_bytes", "holder_bytes", "depth_offset"], map(int, fields[1:])))
        elif fields[0] == "DATA":
            _, name, size, origin, data = fields
            assert int(size) == len(views[name]["bytes"])
            assert bytes.fromhex(data) == views[name]["bytes"]
            origins[name] = int(origin)
        elif fields[0] == "R":
            _, entry, name, origin, off, length, seed, low, crc = fields
            key = (entry, name, int(off), int(length), int(seed))
            assert int(origin) == origins[name]
            assert int(low) == (int(origin) + int(off)) % 8
            assert key not in rows
            rows[key] = int(crc)
        elif fields[0] == "END":
            end = [int(value) for value in fields[1:]]
        else:
            raise AssertionError("unexpected native output")
    assert set(origins) == set(NAMES)
    assert origins["raw"] == 0
    assert len(rows) == len(cases) and set(rows) == set(cases)
    assert end == [len(cases), 1]
    return {"rows": rows, "origins": origins, "metadata": meta}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--zlib-source", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path)
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    root = here.parents[2]
    output = args.output_dir or Path(tempfile.mkdtemp(prefix="crc-byte-views-"))
    output.mkdir(parents=True, exist_ok=True)
    output = output.resolve()
    model = output / "model"
    native = output / "native"
    model.mkdir()
    native.mkdir()
    source = args.zlib_source.resolve()
    report = {"status": "running", "commands": {}, "platform": platform.platform(),
              "system": platform.system(), "machine": platform.machine(),
              "scope": "Positive local CRC evidence; not a proof or a default-target execution claim.",
              "layout_scope": "Only the model origin matching a recorded native origin is ABI-matched. Other model origins are checked against the same byte-sequence CRC value, not executed as extra native layouts."}

    def command(label, cmd, cwd, stdin=None, env=None):
        start = time.monotonic()
        with (output / (label + ".stdout")).open("w") as out, (output / (label + ".stderr")).open("w") as err:
            if stdin is None:
                run = subprocess.run(cmd, cwd=cwd, env=env, stdout=out, stderr=err)
            else:
                with stdin.open("r") as inp:
                    run = subprocess.run(cmd, cwd=cwd, env=env, stdin=inp, stdout=out, stderr=err)
        report["commands"][label] = {"argv": list(map(str, cmd)), "exit": run.returncode,
                                     "seconds": round(time.monotonic() - start, 3)}
        if run.returncode:
            raise RuntimeError(f"{label} exited {run.returncode}")

    try:
        deps = closure(root, ["ZlibF.Zlib.«crc32.c»", "ZlibF.Zlib.«trees.c»"])
        before = {}
        for rel in deps.values():
            dest = model / rel
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(root / rel, dest)
            before[str(rel)] = sha(dest)
        for cfg in ["lakefile.toml", "lean-toolchain", "lake-manifest.json"]:
            if (root / cfg).exists():
                shutil.copy2(root / cfg, model / cfg)
        shutil.copy2(here / "driver.lean", model / "driver.lean")
        (output / "model-source-hashes.json").write_text(json.dumps(before, indent=2) + "\n")
        report["model_dependency_count"] = len(deps)
        command("model-build", ["lake", "build", "ZlibF.Zlib.«crc32.c»", "ZlibF.Zlib.«trees.c»"], model)
        command("export", ["lake", "env", "lean", "--run", "driver.lean", "export"], model)
        views = parse_export(output / "export.stdout")
        report["data"] = {name: {"size": len(data["bytes"]), "sha256": hashlib.sha256(data["bytes"]).hexdigest(),
                                 "string_id": data["string_id"]} for name, data in views.items()}
        cases_path = output / "cases.txt"
        cases, coverage = write_cases(cases_path, views)
        report["coverage"] = coverage
        report["requested_lengths"] = BOUNDARIES
        report["seeds"] = SEEDS
        report["entries"] = ENTRIES
        shutil.copytree(source, native / "zlib", ignore=shutil.ignore_patterns(".git"))
        upstream = {str(p.relative_to(native)): sha(p) for p in sorted((native / "zlib").rglob("*")) if p.is_file()}
        (output / "native-source-hashes.json").write_text(json.dumps(upstream, indent=2) + "\n")
        try:
            report["upstream_pin"] = subprocess.check_output(["git", "-C", str(source), "rev-parse", "HEAD"], text=True).strip()
        except subprocess.CalledProcessError:
            report["upstream_pin"] = None
        shutil.copy2(here / "probe.c", native / "probe.c")
        write_fixtures(native / "fixtures.h", views)
        compiler = shlex.split(os.environ.get("CC", "cc"))
        report["compiler"] = subprocess.check_output(compiler + ["--version"], text=True).splitlines()
        architecture = ["-march=armv8-a"] if platform.machine().lower() in ("arm64", "aarch64") else []
        flags = ["-std=c11", "-O1", "-g", "-fno-omit-frame-pointer", "-Izlib"] + architecture
        sources = ["probe.c", "zlib/crc32.c", "zlib/trees.c", "zlib/zutil.c"]
        native_runs = {}
        report["native_crc_paths"] = {}
        for label, extra in [("plain", []), ("sanitized", ["-fsanitize=address,undefined", "-fno-sanitize-recover=all"])]:
            command(label + "-crc-macros", compiler + flags + extra + ["-dM", "-E", "zlib/crc32.c"], native)
            macros = {}
            for line in (output / (label + "-crc-macros.stdout")).read_text().splitlines():
                parts = line.split(maxsplit=2)
                if len(parts) >= 2 and parts[0] == "#define":
                    macros[parts[1]] = parts[2] if len(parts) > 2 else ""
            selected = {name: macros.get(name) for name in
                        ["N", "W", "Z_U8", "Z_U4", "__aarch64__", "__ARM_FEATURE_CRC32", "__BYTE_ORDER__"]}
            selected["disabled_branches"] = {name: name not in macros for name in
                ["ARMCRC32", "HAVE_S390X_VX", "DYNAMIC_CRC_TABLE", "MAKECRCH", "Z_TESTN", "Z_TESTW"]}
            report["native_crc_paths"][label] = selected
            assert macros.get("N") == "5" and macros.get("W") == "8"
            assert all(selected["disabled_branches"].values())
            assert macros.get("__BYTE_ORDER__") == "__ORDER_LITTLE_ENDIAN__"
            command(label + "-build", compiler + flags + extra + sources + ["-o", label], native)
            env = dict(os.environ)
            env["ASAN_OPTIONS"] = "halt_on_error=1:abort_on_error=1"
            env["UBSAN_OPTIONS"] = "halt_on_error=1:print_stacktrace=1"
            command(label + "-run", [str(native / label)], native, stdin=cases_path, env=env)
            result = parse_native(output / (label + "-run.stdout"), views, cases)
            native_runs[label] = result
        assert native_runs["plain"]["rows"] == native_runs["sanitized"]["rows"]
        report["native_crc_path_scope"] = "Preprocessed portable N=5/W=8 little-endian braid path, without optional hardware CRC branches. This is still local-platform evidence."
        command("model-run", ["lake", "env", "lean", "--run", "driver.lean", "run", str(cases_path)], model)
        seen = set()
        layout_sets = {name: set() for name in NAMES}
        matched = {label: 0 for label in native_runs}
        extra_layouts = {label: 0 for label in native_runs}
        for line in (output / "model-run.stdout").read_text().splitlines():
            tag, entry, name, origin, off, length, seed, low, crc, data_same, base_same = line.split("|")
            assert tag == "R" and data_same == "true" and base_same == "true"
            origin, off, length, seed, low, crc = map(int, [origin, off, length, seed, low, crc])
            key = (entry, name, off, length, seed)
            assert (key, origin) not in seen
            seen.add((key, origin))
            layout_sets[name].add(origin)
            assert low == (origin + off) % 8
            for label, native_result in native_runs.items():
                assert crc == native_result["rows"][key], (label, key, origin)
                if origin == native_result["origins"][name]:
                    matched[label] += 1
                else:
                    extra_layouts[label] += 1
        expected = {(case, base) for case in cases for base in ([0] if case[1] == "raw" else range(8))}
        assert seen == expected
        assert all(count == len(cases) for count in matched.values())
        assert set(BOUNDARIES).issubset({case[3] for case in cases})
        report["native_cases_per_run"] = len(cases)
        report["model_layout_cases"] = len(seen)
        report["abi_matched_comparisons"] = matched
        report["extra_modeled_layout_comparisons"] = extra_layouts
        report["modeled_origins_by_view"] = {name: sorted(bases) for name, bases in layout_sets.items()}
        report["native_runs"] = {label: {"origins": result["origins"], "metadata": result["metadata"]}
                                 for label, result in native_runs.items()}
        report["sanitizer_stderr_bytes"] = (output / "sanitized-run.stderr").stat().st_size
        assert report["sanitizer_stderr_bytes"] == 0
        report["model_sources_unchanged"] = all(sha(model / rel) == digest for rel, digest in before.items())
        report["native_sources_unchanged"] = all(sha(native / rel) == digest for rel, digest in upstream.items())
        report["shared_model_sources_still_match_snapshot"] = all(sha(root / rel) == digest for rel, digest in before.items())
        report["shared_native_sources_still_match_snapshot"] = all(sha(source / Path(rel).relative_to("zlib")) == digest
                                                                  for rel, digest in upstream.items())
        assert report["model_sources_unchanged"] and report["native_sources_unchanged"]
        report["status"] = "passed"
    except Exception as exc:
        report["status"] = "failed"
        report["error"] = str(exc)
    finally:
        (output / "evidence.json").write_text(json.dumps(report, indent=2) + "\n")
        print(json.dumps({"status": report["status"], "output": str(output), "error": report.get("error"),
                          "native_cases": report.get("native_cases_per_run"), "model_cases": report.get("model_layout_cases")}))
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
