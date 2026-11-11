# Contributing

This page lists the steps to change the proofs, the translation or the documentation.
Run every command from the repository root. The rules are in `AGENTS.md`.

Commands marked **site** were run when this page was written. The Lean and audit
commands are copied from the CI workflow `.github/workflows/lean.yml` and the scripts
it calls. They were not re-run for this page.

## Two levels

- **Checked.** The theorem is on `dev`, and the fast gate is green on that commit.
- **Accepted.** The theorem is also in `tests/audit/theorems.txt`, and the acceptance suite is
  green on a named commit. Only an accepted result is final.

## Steps

1. Get the sources, including the upstream submodule.

   ```bash
   git clone --recurse-submodules <repository-url>
   git submodule update --init zlib
   ```

2. Work on a branch from `dev`. Commit small steps and push them to `dev`, or merge a pull
   request into `dev` once the fast gate is green. No review is needed.

3. Build the library. Use at most four parallel jobs and a 16 GB limit. The proofs of
   `crc32.c` and `inftrees.c` need 8 to 9 GB each.

   ```bash
   lake build ZlibF zlibf-audit zlibf-span zlibf-proof-replay
   ```

4. Check for forbidden constructs and `sorry`.

   ```bash
   scripts/check-sorry.sh
   grep -rnE '\b(native_decide|bv_decide|implemented_by)\b|^\s*axiom\b' ZlibF.lean ZlibF
   ```

   The first command is the gate. The second is a short form of the grep in `lean.yml`, which also
   rejects `partial`, `unsafe`, `opaque` and `extern`.

5. Check that every patch applies to the pinned upstream source (copy of the step in `lean.yml`).

   ```bash
   cp -r zlib /tmp/zlib-verified && rm -rf /tmp/zlib-verified/.git
   for p in patches/*.patch; do (cd /tmp/zlib-verified && git apply "$OLDPWD/$p"); done
   ```

6. Build and check the website if you changed `docs/` (**site**). Use Python 3.12 or newer.

   ```bash
   python3 -m pip install -r docs/web/requirements.txt
   python3 docs/web/build.py
   python3 docs/web/check.py
   node --test docs/web/tests/*.test.mjs
   ```

7. Every English document has a Chinese twin `*.zh.md` next to it. Its first line records
   `source-sha256` of the English file. After you edit the English file, update the Chinese text
   and set the hash.

   ```bash
   shasum -a 256 docs/glossary.md
   ```

   A stale twin does not fail the build. The Chinese page shows a notice that the English source is newer.

8. Push to `dev`. The fast gate (`build`, `no-sorry`) runs on every push and pull request.
   It is the only gate for merging. If a push breaks it, fix that first.

## At a milestone

Acceptance work is done in batches, not for each change.

1. Register new theorems in `tests/audit/theorems.txt`, one fully qualified name per line.
2. Add proof mutants for each newly proved public function. A mutated translation must fail
   to check, with the error in that function's proof.

   ```bash
   bash tests/audit/proofmut.sh tests/audit/proofmut/adler32.tsv
   ```

3. Regenerate the lock files with the tool, never by hand. Write one line per lock on why it changed.

   ```bash
   python3 scripts/verification.py regenerate
   python3 scripts/verification.py check
   ```

4. Regenerate the progress view, the block between the `proof-progress` markers in
   `docs/progress.md`.

   ```bash
   python3 scripts/proof-progress.py
   python3 scripts/proof-progress.py --check
   ```

5. Run the acceptance suite. Start the `lean` workflow with its manual trigger, or run the
   differential tests locally.

   ```bash
   ZLIB_SRC=$PWD/zlib bash tests/run.sh
   SAN=1 ZLIB_SRC=$PWD/zlib bash tests/run.sh
   ```

6. Name the commit on which the suite is green when you report a result as accepted.
   `main` receives `dev` after that.

Never report a check as passing unless it was run.
