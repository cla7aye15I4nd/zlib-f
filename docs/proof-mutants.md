# Proof mutants

A proof about a translation is only worth something if it breaks when the translation is wrong. The
proof mutation check tests exactly that: it changes one thing in a copy of a translation file and
requires that the proofs of that function **no longer check**, with the first error inside the proof
files of that function.

This is a different check from `tests/selftest.sh`. The self-test mutates the translation and needs the
differential test (the Lean translation against the real C) to notice. The proof mutants need the
kernel-checked proofs to notice. A mutant that the differential test catches but the proofs accept means
the theorem says less than the C does.

## Running it

From the workspace root, with a warm `.lake` build cache (the build output of the proof modules):

```
bash tests/audit/proofmut.sh tests/audit/proofmut/adler32.tsv
bash tests/audit/proofmut.sh tests/audit/proofmut/crc32.tsv '^combine'   # only the mutants whose name matches
```

For every line of the list the script

1. copies the workspace (without `.git`, `.lake`, `zlib/`) and the warm `.lake` cache to a fresh temporary
   directory; the original cache is never touched;
2. applies the replacement; the text to replace must occur exactly once in the file;
3. runs `lake build` for the listed proof modules only, never the whole project;
4. reads the first `error: <file>:<line>:<col>` line of the output.

A first run builds the unmutated copy of all listed modules and requires it to pass, so that every later
failure is caused by the mutation.

| Verdict | Meaning | Run |
|---|---|---|
| `KILLED` | the build fails, and the first error is in one of the expected proof modules | passes |
| `SAME ok` | marked `same:`; the proofs still build, as expected for an equivalent mutant | passes |
| `GAP (known)` | marked `gap:`; the proofs still build because no theorem covers that code. The reason says what is not proved | passes, and is counted |
| `SURVIVED` | the proofs still build and nothing excuses it | fails: the theorem is too weak, or the mutant is equivalent and must be marked `same:` |
| `BAD MUTANT` | the error is in the mutated translation file, or outside `ZlibF/Proof` | fails: the mutation is not well typed, change it |
| `WRONG PLACE` | the error is in a proof module that is not in the expected list | fails: fix the list, or the proof layout has changed |
| `NO ERROR` | the build failed without an error line (timeout, killed from outside; it is retried once first) | fails: rerun |
| `UNEXPECTED` | marked `same:` but the build fails | fails: the mutant is not equivalent |
| `NOT APPLIED` | the old text does not occur exactly once | fails: the translation changed, update the list |

A `gap:` mutant that is killed after all is reported as `KILLED (stale gap flag)` and fails, so that the
flag is removed once the hole is closed.

Environment: `PROOFMUT_CACHE` (the warm `.lake`, default `<workspace>/.lake`), `PROOFMUT_TIMEOUT`
(seconds per build, default 3600), `PROOFMUT_BASELINE=0` (skip the unmutated build), `PROOFMUT_KEEP=1`
(keep the temporary copies), `PROOFMUT_SHOWLOG=1` (print the end of the log of a surviving or bad mutant).
One mutant runs at a time. The script uses the gated `lake` wrapper when it is on the path (it waits for a
free build slot and enough free memory; `LB_SLOTS` is 3 and `LB_MIN_GB` is 6 unless set).

## List format

One mutant per line in `tests/audit/proofmut/<c-file>.tsv`, fields separated by a tab; `#` starts a
comment line:

```
NAME <TAB> FILE <TAB> OLD <TAB> NEW <TAB> PROOF_MODULES [<TAB> same:REASON | gap:REASON]
```

* `FILE`: the translation file, for example `ZlibF/Zlib/adler32.c.lean`.
* `OLD`, `NEW`: the replacement; a literal `\n` is a newline. `OLD` must occur once.
* `PROOF_MODULES`: comma-separated modules under `ZlibF/Proof` (file name without `.lean`), for example
  `adler32.c` or `inflate.c.uw,inflate.c.window`. Only these are built, and the first error must be in
  one of them. Choose the module that proves the function and the modules it imports from the same
  function group; the build time of one mutant is the build time of the modules that depend on the
  mutated file.
* `same:REASON`: an equivalent mutant, with the reason. `gap:REASON`: a known hole in the theorems.

A good mutant changes the meaning of the C: a constant, a comparison, a shift amount, a branch, a loop
bound, an index, a returned value, an assignment that is swapped or dropped. Prefer several per proved
function, at different places of the function.

## What the lists cover

| List | Translation | Proof modules |
|---|---|---|
| `adler32.tsv` | `adler32.c` (`adler32_z`, `adler32_combine`) | `adler32.c` |
| `zutil.tsv` | `zutil.c` | `zutil.c` |
| `crc32.tsv` | `crc32.c` (`crc32_z`, combine, polynomial arithmetic) | `crc32.c` |
| `inftrees.tsv` | `inflate_table` | `inftrees.c.base`, `.geom`, `.step`, `.main`, `inftrees.c` |
| `inflate.tsv` | `inflateStateCheck`, `inflateReset*`, `inflateInit2_`, `inflateEnd`, `inflatePrime`, `inflateGetHeader`, the small `inflate*` functions, `updatewindow` | one module per function group, from `inflate.c.base` to `inflate.c.uw` |
| `trees.tsv` | `smaller`, `pqdownheap`, `pqremove` | `trees.c.heap.*` |

Results of the last run are in the section below. The functions that have no list yet have no proof
mutants; adding a list is the way to extend the check.

## Optional CI job

The job below is not part of the workflow files. It needs a runner that can build the project (the
proof modules take a long time on a cold cache, so it should restore a cached `.lake` first) and it
runs one mutant at a time. Paste it under `jobs:` of the workflow if wanted.

```yaml
  proof-mutants:
    runs-on: ubuntu-latest
    timeout-minutes: 360
    strategy:
      fail-fast: false
      max-parallel: 1
      matrix:
        list: [adler32, zutil, crc32, inftrees, inflate, trees]
    steps:
      - uses: actions/checkout@v4
      - name: Install elan
        run: |
          curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
          echo "$HOME/.elan/bin" >> "$GITHUB_PATH"
      - name: Restore the build cache
        uses: actions/cache@v4
        with:
          path: .lake
          key: lake-${{ hashFiles('lean-toolchain', 'lakefile.toml', 'ZlibF/**') }}
          restore-keys: lake-
      - name: Warm the cache (the listed modules, unmutated)
        run: lake build ZlibF
      - name: Proof mutants
        run: PROOFMUT_BASELINE=0 PROOFMUT_TIMEOUT=3000 bash tests/audit/proofmut.sh tests/audit/proofmut/${{ matrix.list }}.tsv
```

`PROOFMUT_BASELINE=0` is fine there because the previous step has just built the same modules.
