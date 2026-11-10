# Working rules

Goal: kernel-checked Lean 4 proofs about a faithful translation of upstream zlib `develop`.
The goal is full safety (no undefined behaviour, no memory error, no leak, termination) and full
functional correctness, for the default x86_64 Linux build first and then for every configuration
that upstream CI builds. Work starts with `inflate` and `deflate`. Read
`docs/overview.md` first, then `docs/spec/safety.md`. Keep proof explanations in `docs/proof/`. Keep current status and remaining work
only in `docs/progress.md`.

The priority is to finish the proofs of `inflate`, `deflate` and then every other target, as
fast as honest work allows. Process exists to keep the result honest, not to slow it down.

## Source

- `zlib/` is the upstream submodule. Never modify it. The verified source is `zlib/` plus
  `patches/*.patch` applied in name order.
- A patch is allowed only for a confirmed zlib bug that blocks a proof. It must be minimal, match
  a fix submitted upstream, and be listed in `patches/README.md`. Delete it once upstream merges
  the fix and the pin moves past it.
- Translations mirror the C layout: `zlib/X.c` is `ZlibF/Zlib/X.c.lean`, and `zlib/X.h` is
  `ZlibF/Zlib/X.h.lean`. Each function keeps its C name, and its docstring starts with the C
  signature.
- Specifications are in `ZlibF/Spec/`. Proofs about `zlib/X.c` are in
  `ZlibF/Proof/X.c.<topic>.lean`. Proofs of public goals are in `ZlibF/Proof/public-<name>.lean`.
- Heap-free mathematics goes to `ZlibF/Math/`. The runtime (heap, pointers, loops, faults) is
  `ZlibF/Runtime/*.lean`.

## Translation

- Translate statement by statement. Do not reorder, merge or simplify.
- Every undefined behaviour the C can reach raises `Fault.ub`. Unsigned arithmetic wraps. Signed
  arithmetic is checked.
- Reading an uninitialised integer returns an arbitrary value, and a theorem must hold for every
  value. A pointer in fresh memory is NULL in the model, which is weaker than C: the proof shows that a pointer
  field was written before it is read (`docs/spec/safety.md`, section 3; `docs/trusted-base.md`, item 2).
- Never change a translation to make a proof easier. A mismatch with the C is a translation bug.
  Fix it, and add a differential test that catches it.
- Every proof depends on the runtime. Change it only for a confirmed mismatch with C.

## What counts as proved

There are two levels. Say which one you mean.

- **Checked.** The theorem is on `main`, and the fast gate is green on that commit: everything
  builds, there is no `sorry`, and no forbidden construct. Lean's kernel has checked the proof.
  Day-to-day work is merged at this level.
- **Accepted.** The theorem is also listed in `tests/audit/theorems.txt`, and the acceptance suite
  is green on a commit you name: axiom gate, exact goal match, locks, proof mutants and
  differential tests. Only an accepted result may be reported as final.

Rules that hold at both levels:

- Only `propext`, `Classical.choice` and `Quot.sound` are allowed. Never use `sorry`,
  `native_decide`, `bv_decide`, `axiom`, `implemented_by`, `extern`, `unsafe`, `partial` or
  `opaque`. Do not look for ways around the checks; report the obstacle.
- A goal is proved only by a theorem whose type is exactly the goal.
- A theorem states its precondition explicitly. A precondition narrower than `zlib.h` allows is
  written in the theorem's docstring and listed in `docs/deviations.md`. Never shrink the domain
  silently.
- **No callee contracts as assumptions.** A callee's specification is a theorem about the
  translated callee. A representation invariant is established by the init function, which also
  shows that the invariant can hold. A concrete witness is needed only for a top-level theorem.
- When a proof is stuck, decide which of four causes it is, without assuming the answer: the
  proof technique, a wrong specification, a translation bug, or a real zlib bug. For a possible
  zlib bug, build a concrete input, run the real C under a sanitiser, and report it with the
  reproduction. Never narrow a precondition to hide it.
- Differential tests are evidence of fidelity, not proof. Say so when reporting.

## Correcting a specification, a goal or a translation

A wrong statement is corrected, not worked around.

- Change it when there is evidence: a checked counterexample, or a documented mismatch with
  `zlib.h` or the C source. Put the correction in its own commit. Say what was wrong and why.
- Keep the counterexample as a regression under `tests/verification/regressions/`.
- Never weaken a statement, narrow a domain or change a translation to make a proof go through.
  Strengthening a weak goal is allowed and wanted.
- A translation mismatch with the C is a bug. Fix it and add a differential test that catches it.
- A change to `ZlibF/Runtime/` is its own commit, with the reason and the proofs it affects.

## Checking

**Fast gate, on every push and pull request** (`build`, `no-sorry`): all modules build, no
forbidden construct, patches apply to the pinned `zlib/`, no `sorry`. This is the only gate for
merging.

**Acceptance suite, every night on `main` and on request** (`audit`, `difftest`): axiom gate,
exact goals, locks, self tests, proof mutants, differential tests with and without sanitisers.
Run it on request with the `lean` workflow's manual trigger. A red nightly run is fixed before
new acceptance work, but it does not block proof work.

Work that belongs to acceptance is done in batches at a milestone, not for each change:

- registering theorems in `tests/audit/theorems.txt`;
- proof mutants for each newly proved public function: a mutated translation (a dropped check,
  an off-by-one) must fail to check, with the error in that function's proof;
- regenerating lock files with the audit tooling, never by hand, with one line per lock on why
  it changed;
- regenerating the progress view.

A milestone is one of: `inflate` proved, `deflate` proved, a stream sequence goal proved, or
about twenty newly checked targets. Never report a check as passing unless it was run.

Full builds use a lot of memory. `ZlibF/Proof/crc32.c.lean` and `ZlibF/Proof/inftrees.c.lean`
each need 8 to 9 GB. Build with at most four parallel jobs under a 16 GB limit. If one module
needs more than that, find out why before raising any limit.

## Findings

Record a confirmed zlib issue in `README.md`: give a short description, link a reproduction under
`docs/findings/`, and state the confidence and the scope. Keep unconfirmed reports in
`docs/progress.md`.

## Documents

- File names are lowercase, with hyphens: `method.md`. `README.md` and `AGENTS.md` keep their
  conventional names.
- Write short sentences. Say what is proved, what is assumed, and what is open.
- Mark a reading of the C that the proof must still confirm with **to confirm**.
- Use diagrams (mermaid) for structure and order. Do not use a diagram for a list.
- Do not put machine names, addresses, user names, local paths or tool names in the repository.

## Collaboration

- Commit small, self-contained steps. A pull request is merged as soon as the fast gate is
  green; it needs no review and need not be up to date with `main`. Direct pushes to `main` are
  fine for a single worker when the fast gate was run on that commit.
- Parallel work uses separate C files or functions. Two workers never edit the same file.
- Prove the universal goal. Do not add proofs for a fixed parameter or a default configuration
  unless they are a lemma of the universal proof.
- Commit messages describe the change. They carry no attribution lines for tools.
- Report what is checked, what is accepted and what is open. Name the commit.

[docs/anti-cheating.md](docs/anti-cheating.md) says why a green build can still be worthless,
and what the acceptance suite defends against.
