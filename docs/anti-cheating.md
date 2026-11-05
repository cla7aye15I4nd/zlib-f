# What stops a proof from cheating

The kernel checks that a proof proves its statement. It does not check that the statement says what we
mean, that the translation matches the C, or that nobody weakened the checks. Those are the ways a proof
can be worthless while the build is green. This page lists them, says what stops each, and says what is
left for a human.

## The ways to cheat, and what stops them

| Way to cheat | What stops it |
| --- | --- |
| `sorry`, `axiom`, `native_decide`, `bv_decide`, `implemented_by`, `extern`, `unsafe`, `partial`, `opaque` | the audit reads the compiled modules and rejects every declaration of ZlibF that uses one, **not only the listed theorems**. It also rejects any axiom outside `propext`, `Classical.choice`, `Quot.sound`, for definitions as well as theorems, so a translated function cannot hide a `sorry` |
| A new tactic, macro or syntax in a proof module that hides one of the above | the audit does not elaborate source and does not run code from the audited modules. It loads the compiled declarations and inspects them |
| Making the runtime or the translation weaker, so that a theorem is easier | `tests/audit/trusted.lock` holds a hash of every trusted definition (runtime, translation, specification, invariants: everything that is not a theorem and not inside a `Proofs` namespace). A change shows up as a diff, and the paths are protected |
| Changing a theorem's statement to something weaker | `tests/audit/statements.lock` holds the exact type of every listed theorem. A change shows up as a diff |
| Adding a theorem that is not on the list, and claiming the result | only `tests/audit/theorems.txt` counts, and only a human may change it. Every listed theorem must also have a doc string |
| Weakening the audit itself, or the CI | CI runs the audit program **from `main`**, not from the branch under test. A branch that changes `tests/audit/Audit.lean` is judged by the old program. `tests/audit/`, `.github/`, `scripts/` and the runtime are protected paths (`CODEOWNERS`) |
| An audit that has silently stopped working | `tests/audit/selftest.sh` feeds the audit a set of cheat samples (`tests/audit/cheats/`) and fails if any is accepted. CI runs it |
| A theorem whose hypotheses can never hold | invariants are established by the `Init` function, so they can hold. Top-level theorems carry a concrete witness (planned); a lock on the invariant definitions makes it visible when one changes |
| A translation that differs from the C | differential tests (`tests/`): the Lean translation and the real C, built from the pinned zlib with the patches, must agree on every input, also with the C side under ASan and UBSan. `tests/selftest.sh` mutates the translation and checks that the harness notices; CI runs both. Evidence, not proof: the inputs are finite, and the translation is still trusted by review (`docs/trusted-base.md`) |

## What is still left to a human

1. **Reading the statements.** A lock says that a statement did not change, not that it was right. The first
   time a statement enters the lock, a human compares it with `docs/spec/`.
2. **Reading the trusted definitions.** The same for the runtime and the translation. They are short
   compared with the proofs, which is the point of the design.
3. **Branch protection.** The files above only take effect if `main` requires a pull request, requires the
   status check to pass, and requires a review from the code owner. That is a repository setting (Settings,
   Branches, a rule for `main`), and it is done once by the owner.
4. **Credentials.** An agent that holds the owner's token can change repository settings. Give an agent a
   token without administration rights, or a fork.

## How to change a locked thing

A change to the runtime, a translation, a specification definition or a theorem statement is a change to what
the result means. Make it in its own pull request, regenerate the locks with the command below, and explain the
diff of the lock files in the description:

```bash
lake build ZlibF
lake env lean --run tests/audit/Audit.lean tests/audit/theorems.txt > /tmp/report.txt
grep '^trusted '   /tmp/report.txt > tests/audit/trusted.lock
grep '^statement ' /tmp/report.txt > tests/audit/statements.lock
```
