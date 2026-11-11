# Fixed questions, editable proofs

A proof may change. The question it answers must not change to make a proof pass. The kernel
checks a term against its type. The acceptance suite also checks that the type is exactly a
registered target.

A successful build is not acceptance. [Progress](progress.md) records current status. The
[checking guide](checking/README.md) says what each check establishes; the
[trusted base](trusted-base.md) explains the judgments that automation cannot make.

## What the acceptance suite defends against

| Attack | Defence |
| --- | --- |
| A proof of a weaker statement presented as the goal | A goal is proved only by a theorem whose type is exactly the goal. An extra premise, a similar name or an abstract-model theorem does not count. |
| An unsupported assumption | Only `propext`, `Classical.choice` and `Quot.sound` are allowed. The declaration audit rejects other axioms and forbidden declaration kinds in the import closure. Missing, empty or duplicate registries fail. |
| A proof term the kernel never saw | Compiled declarations are replayed in a fresh environment of the same Lean kernel. A cached trace is not a certificate. |
| An unregistered goal | Every standalone `Goal` proposition in the audited closure must be registered. The inventory in `tests/audit/public-api.json` is checked against the pinned header, the translated entries and the manual sections. |
| A proof that does not depend on the translation | Proof mutants: a deliberately wrong translation, such as a dropped check, must fail to check, with the error in that function's proof. |
| A translation that differs from the C | Differential tests run the real C and the translation on the same inputs, with and without sanitisers. They are evidence of fidelity, not proof. |
| `sorry` and the other forbidden constructs | The fast gate rejects them on every push. |

## What it no longer defends against

There are no lock files and no approved baseline. Definitions, translations, specifications and
statements are tracked by git alone. A silent change to a trusted definition, to the translation,
to a specification or to the statement of a goal, in the same commit as a proof that uses it, is
no longer rejected by a tool. It is visible only in git history and in review of the diff.

What still holds in that case:

- the goal must still be proved by a theorem of exactly its type, whatever that type now is;
- the axiom gate still applies;
- proof mutants and differential tests still run against the changed translation.

None of these detects a goal that was changed to be easier. Compare the statement of a goal with
its earlier version in git when you read a result. The rules for correcting a statement are in
`AGENTS.md`: a correction needs evidence, its own commit and a regression under
`tests/verification/regressions/`. Never weaken a statement, narrow a domain or change a
translation to make a proof go through.

## What counts as a proof

The registered theorem's type must be exactly the target constant. Initialisation must establish
the shared invariant over the permitted domain. Top-level concrete witnesses supplement this
obligation and never replace universal coverage. No result may assume an unproved library callee
contract. An invariant that no permitted heap satisfies cannot justify a public claim.

Compiler-generated execution helpers are listed in `tests/audit/compiler-helpers.txt`. Ordinary
private unsupported definitions are rejected.

## Proof mutants

Every exactly proved public entry needs a record in `tests/audit/public-mutants.json`. Each
mutation changes that function's translated body and keeps its signature. A missing record, a
mutation of another function, a specification-only change or a marked proof gap fails the check.
A fresh-kernel replay substitutes only the mutated declarations into the original registered
proof's dependency closure. That proof must check before the mutation and fail afterwards.
Failure only in an unrelated or stronger theorem does not count.

Proof sensitivity alone does not establish a behavioural difference. An equivalent rewrite can
break a particular proof term, so a mutation should change behaviour on an allowed input.
`verification.py mutants` runs the model list and every referenced public-function list. The
[mutant guide](checking/proof-mutants.md) explains the checks.

## Human review

Review still decides whether the contracts are complete, the runtime represents the selected C
semantics and the translation matches the source. Kernel checking of proof bodies cannot replace
that. Review statements, preconditions, runtime, deviations and patches. Report an audit obstacle
instead of bypassing it.
