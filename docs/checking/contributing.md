# Contributing a proof

This page is the short path from an open target to a merged, registered proof. The rules
behind each step are in [`AGENTS.md`](../../AGENTS.md), [checking](README.md) and the
[verification policy](../anti-cheating.md). Terms are defined in the [glossary](../glossary.md).

Run every command from the repository root. Each command block says where it was checked:
**run locally** means it was run on an arm64 macOS machine with a 6 GiB per-process memory
limit; **CI** means it runs in the named CI job and was not run locally.

## Before you start

```sh
git submodule update --init zlib
lake build ZlibF
```

`lake build ZlibF` builds every module; later builds are incremental. Some modules need more
than 6 GiB of memory (for example `ZlibF/Proof/crc32.c.lean`, which evaluates CRC tables in
the kernel). If your machine cannot build them, take the build of the same commit from CI.
The `build` job publishes the artifact `lean-build`; extract its outputs over `.lake/build` and
check that nothing is left to rebuild (run locally):

```sh
gh run download RUN_ID -n lean-build
tar -xzf lean-build.tar.gz .lake/build/lib/lean .lake/build/ir
lake build --no-build ZlibF
```

`RUN_ID` is a `lean` workflow run on the same commit. The artifact is kept for two days.

## 1. Pick a target

Open [progress](../progress.md). Its generated block lists every target in
`tests/audit/goals.txt` with its status. The [ordered next work](../progress.md#ordered-next-work)
table gives the order and the prerequisite of each open target. Do not start a target whose
statement has a recorded counterexample; the owner decides the correction first.

A target `ZlibF.Spec.Public.Goal.gztell` is the definition `Goal.gztell` in a file under
`ZlibF/Spec/Public/`. Search for it:

```sh
grep -rn "def Goal.gztell " ZlibF/Spec
```

## 2. State and prove

1. Put the proof in `ZlibF/Proof/<C file>.<topic>.lean`, for example
   `ZlibF/Proof/gzlib.c.tell-public.lean`. Translations are in `ZlibF/Zlib/`, specifications
   in `ZlibF/Spec/`, heap-free mathematics in `ZlibF/Math/`.
2. State a theorem whose type is exactly the goal, for example
   `theorem gztell_public : ZlibF.Spec.Public.Goal.gztell := by …`.
   Its docstring starts with the C signature and states the scope.
3. Prove callee facts as theorems about the translated callee. Do not assume a callee contract.
4. Import the module from `ZlibF.lean` or from a module it imports, so that `lake build ZlibF`
   checks it.
5. Check it (run locally):

```sh
lake build ZlibF
scripts/check-sorry.sh
```

Never use `sorry`, `axiom`, `native_decide`, `bv_decide`, `implemented_by`, `extern`, `unsafe`,
`partial` or `opaque`. If the proof is stuck, classify the cause (proof technique, wrong
specification, translation bug, zlib bug) as [`AGENTS.md`](../../AGENTS.md) describes. Never
change a goal, specification or translation to make a proof go through.

## 3. Add proof mutants

Each proved public entry needs mutations of its translated body that its proof rejects.

1. Add rows to the list for the entry's area in `tests/proof-mutants/` (`public-queries.tsv`,
   `public-checksums.tsv`, `public-streams.tsv`). Each row is
   `NAME<TAB>FILE<TAB>OLD<TAB>NEW<TAB>PROOF_MODULES`; `OLD` must occur exactly once in `FILE`,
   and `PROOF_MODULES` names files under `ZlibF/Proof/` without `.lean`.
2. Run your rows in strict mode, as `audit_mutants` does. The runner works in a temporary copy
   and never changes your workspace. The last argument is a regular expression on the mutant
   name (run locally):

```sh
PROOFMUT_STRICT=1 bash tests/audit/proofmut.sh tests/proof-mutants/public-queries.tsv '^zlibVersion-wrong-string$'
```

3. Every new row must report `KILLED`, with the first error in your proof module.
4. Record the mutant names for the target in `tests/audit/public-mutants.json`. This file is
   under `tests/audit/`, so the pull request needs owner review.

[Proof mutants](proof-mutants.md) explains each verdict.

## 4. Add a differential test

A differential test runs the real C and the translation on the same inputs. It is evidence of
fidelity, not proof. Add inputs for the function to `tests/gen/<name>.py` and, if needed, a
dispatch case to `tests/c/<name>.c` and `tests/lean/Driver/<Name>.lean`.
[tests/README.md](../../tests/README.md#add-a-c-file-for-example-crc32c) has the five steps.
The harness targets x86_64 Linux; on macOS the C drivers do not compile (`adler32_combine64` is
not declared). Run it on Linux, or rely on the CI job `diff_core` (CI):

```sh
ONLY=gz ZLIB_SRC=$PWD/zlib bash tests/run.sh
SAN=1 ONLY=gz ZLIB_SRC=$PWD/zlib bash tests/run.sh
```

## 5. Register the theorem

Register only a theorem you have proved. Add its full name, one per line, to
`tests/audit/theorems.txt`. Registration changes `tests/audit/`, so the pull request needs owner
review; say so in its description.

## 6. Regenerate locks

Locks are never edited by hand. Regenerate them with the auditor, then read the diff:

```sh
python3 scripts/verification.py regenerate
git diff tests/audit/
```

`regenerate` builds the library, replays every declaration in a fresh kernel with `leanchecker`,
runs the declaration audit and only then writes the locks. The fresh replay needs more than
6 GiB of memory; it was killed on the local machine, so this step needs a larger machine.

Explain every changed lock line in the pull request: a statement record for each newly registered
theorem, and a new hash for each changed protected file. Any change to `tests/audit/policy.lock`
or `tests/audit/trusted.lock` also needs the owner to move the approved admission baseline (see
`audit_mutants` below).

## 7. Refresh progress

Run locally (with the CI build, it needs about 4.5 GiB):

```sh
python3 scripts/proof-progress.py
python3 scripts/proof-progress.py --check
```

The first command rewrites the generated block of `docs/progress.md`. The second is what CI
runs. Keep `docs/progress.zh.md` in step: copy the new link revision and input fingerprint and
update its `source-sha256` line to the SHA-256 of `docs/progress.md`.

## 8. Open the pull request

Keep it small: one target family per pull request. A result is proved only when the four
required statuses are green on a named commit.

## CI job → local command

| Required status | CI job | Local command | Checked locally |
| --- | --- | --- | --- |
| `build` | `build` | `lake build ZlibF zlibf-audit zlibf-span zlibf-proof-replay` | `ZlibF` part: yes, with the CI build. The job also rejects forbidden constructs and checks that `patches/*.patch` apply to `zlib/`. |
| `no-sorry` | `no-sorry` | `scripts/check-sorry.sh` | Yes. |
| `audit` | `audit_core` | `python3 scripts/verification.py specs`, the tests in `tests/verification/`, then `python3 scripts/proof-progress.py --check` | `--check` and `python3 scripts/verification.py coverage`: yes. `specs` runs the fresh replay: needs more than 6 GiB. |
| `audit` | `audit_selftest` | `bash tests/audit/selftest.sh` | No (CI). Every planted cheat must be rejected. |
| `audit` | `audit_mutants` | `python3 scripts/verification.py mutants --baseline COMMIT --scoped-approved-commit COMMIT` | No (CI). `COMMIT` is the repository variable `ZLIBF_SCOPED_ADMISSION_APPROVED_COMMIT`. Shard 0 fails whenever `policy.lock` or `trusted.lock` differs from that commit; only the owner can move it. |
| `difftest` | `diff_core` | `ZLIB_SRC=$PWD/zlib bash tests/run.sh`, then with `SAN=1` | No: Linux only. The second run builds the C side with ASan and UBSan. |
| `difftest` | `diff_harness` | `ZLIB_SRC=$PWD/zlib bash tests/selftest.sh` | No: Linux only. Each harness mutation must be detected. |

`python3 scripts/verification.py check` combines build, fresh replay, declaration audit and the
lock check. Like `specs` and `regenerate`, it needs more than 6 GiB for the fresh replay.
