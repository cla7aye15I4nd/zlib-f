# Working rules

Goal: kernel-checked Lean 4 proofs about a faithful translation of upstream zlib `develop`.
The goal is full safety (no undefined behaviour, no memory error, no leak, termination) and full
functional correctness, for the default x86_64 Linux build first and then for every configuration
that upstream CI builds. Work starts with `inflate` and `deflate`. Read
`docs/overview.md` first, then `docs/spec/safety.md`. Keep the proof explanation in `docs/proof/`
(implementation arguments by C component) and `docs/guide/` (guided chapters); `docs/overview.md`
is the short reading path. Keep current status and remaining work only in `docs/progress.md`.

## Source

- `zlib/` is the upstream submodule. Never modify it. The verified source is `zlib/` plus
  `patches/*.patch` applied in name order.
- A patch is allowed only for a confirmed zlib bug that blocks a proof. It must be minimal, match
  a fix submitted upstream, and be listed in `patches/README.md`. Delete it once upstream merges
  the fix and the pin moves past it.
- Lean sources mirror the C layout: the translation of `zlib/X.c` is `ZlibF/Zlib/X.c.lean`, and
  that of `zlib/X.h` is `ZlibF/Zlib/X.h.lean`. Specifications are in `ZlibF/Spec/` (public
  targets in `ZlibF/Spec/Public/`, the abstract API model in `ZlibF/Spec/Api/`). Proofs about
  `zlib/X.c` are in `ZlibF/Proof/X.c.lean` and `ZlibF/Proof/X.c.<topic>.lean`. Each function
  keeps its C name, and its docstring starts with the C signature.
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
- A change to the runtime needs an independent review, because every proof depends on it.

## What counts as proved

- The theorem is listed in `tests/audit/theorems.txt`, and the audit passes. Only `propext`,
  `Classical.choice` and `Quot.sound` are allowed. Never use `native_decide`, `bv_decide`,
  `axiom` or `implemented_by`.
- No `sorry` anywhere in the Lean sources is the final requirement. The CI job `no-sorry` checks it on its own, so that a work in progress can be pushed and the other jobs (build, audit, differential test) still show whether everything builds. Never report a result as final while `no-sorry` fails.
- A theorem states its precondition explicitly. A precondition narrower than `zlib.h` allows is
  written in the theorem's docstring and listed in `docs/deviations.md`. Never shrink the domain
  silently.
- **No callee contracts as assumptions.** A callee's specification is a theorem about the
  translated callee. A representation invariant is established by the init function, which also
  shows that the invariant can hold. A concrete witness is needed only for a top-level theorem.
- Each proved function has proof mutants: a mutated translation (a dropped check, an off-by-one)
  must fail to check, with the error in that function's proof.
- When a proof is stuck, decide which of four causes it is, without assuming the answer: the
  proof technique, a wrong specification, a translation bug, or a real zlib bug. For a possible
  zlib bug, build a concrete input, run the real C under a sanitiser, and report it with the
  reproduction. Never narrow a precondition to hide it.
- Differential tests are evidence of fidelity, not proof. Say so when reporting.

## Checking

CI reports four required statuses: `build` (all modules, forbidden constructs, patches apply to the
pinned `zlib/`; must always be green), `no-sorry` (the final requirement), `audit` and `difftest`.
`audit` passes only if its jobs `audit_core` (specification audit, locks, goals, auditor tests,
progress view), `audit_selftest` (planted cheats are rejected) and `audit_mutants` (proof mutants,
in four shards) all pass. `difftest` passes only if `diff_core` (differential test, also under
sanitisers) and `diff_harness` (harness mutation check, in eight shards) pass. The local command for
each job is in `docs/checking/contributing.md`. Never report a check as passing unless it was run.

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

- Work in small, stacked pull requests. Each one is reviewable alone.
- Parallel work uses separate C files or functions. Shared files (runtime, headers) change through
  one reviewer.
- Commit messages describe the change. They carry no attribution lines for tools.

## Rules for agents that work in this repository

These rules exist because a green build can still be worthless. [docs/anti-cheating.md](docs/anti-cheating.md) says why.

- Never edit `tests/audit/`, `.github/`, `scripts/`, `patches/`, `lakefile.toml`, `lean-toolchain`, `docs/spec/`, `docs/README.md`,
  `docs/design/api-model.md`, `docs/spec/internal-contracts.md`,
  `docs/checking/goals.md`, `docs/checking/contract-review.md`,
  `ZlibF/Runtime/` or `AGENTS.md` unless the task is to change exactly that. Say so in the pull request.
- Never edit a lock file by hand. Regenerate it with the audit, and explain the diff.
- Never change a theorem statement, a specification definition or a translation to make a proof go through.
  If the statement is wrong, say that it is wrong and why, and stop.
- Never add a theorem to `tests/audit/theorems.txt` that you have not proved. Never remove one.
- Do not use `sorry`, `axiom`, `native_decide`, `bv_decide`, `implemented_by`, `extern`, `unsafe`, `partial` or
  `opaque`. The audit rejects them. Do not look for ways around the audit; report the obstacle.
- Report what is proved and what is not. A result is proved only if CI is green on the commit you name.
