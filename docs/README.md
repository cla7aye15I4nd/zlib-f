# Documentation

Start with [current status](overview.md) and [the safety claim](safety.md).
Then choose the question you want to answer.

The [overview](overview.md#proof-progress-graph) contains the single graph of all
fixed targets. [Proof evidence](progress.md) links every target to its statement
and checked results. [Input configurations](input-configurations.md) defines
the common colour scheme and the default/common/all input ranges.

| Question | Read |
| --- | --- |
| What does a function require, return or change? | [API](api/README.md) |
| What bytes are valid compressed data? | [Data format](format/README.md) |
| How are memory, C operations and external I/O represented? | [Model semantics](design/README.md) |
| How do the proofs fit together? | [Proof guides](proof/README.md) |
| What makes a proof acceptable? | [Checking and reviews](checking/README.md) |
| Which C details matter for a proof? | The component's C correspondence section in [proof guides](proof/README.md) |
| What arguments were adapted from earlier work? | [Reference sources](proof/references.md) |

## Shared requirements

- [Safety](safety.md): faults, termination, frames and resource lifetimes.
- [Trusted base](trusted-base.md): what the kernel does not establish.
- [Scope and limitations](deviations.md): explicit restrictions and model gaps.
- [Acceptance policy](anti-cheating.md): fixed questions and editable proofs.
- [Findings](findings.md): reported source behaviour and its evidence.

The [runtime field reference](runtime-schema.md) is generated from source headers.
Read the [design guide](design/README.md) before its detailed tables.

## Reading paths

**Understand an API:** [API index](api/README.md) → the function's Pre, Post and
Effects → its relevant edge cases. Shared vocabulary is in [contracts](api/contracts.md).

**Understand the verification:** [safety](safety.md) → [design](design/README.md)
→ [proof method](proof/method.md) → [acceptance criteria](checking/goals.md).

**Review a claim:** [status](overview.md) → its exact registered target → checked
theorem and evidence. A prose proof, build or finite test alone is not final verification.

Current progress and remaining work have one home: [overview.md](overview.md).
API pages describe behaviour, design pages representation, proof pages reasoning,
and checking pages acceptance. Review and historical records do not override the
current source, goals or status.

## One home for each kind of statement

| Material | Purpose and canonical home |
| --- | --- |
| API contracts | What callers may pass and what an entry must return: `api/`. |
| Byte-format specification | What compressed bytes mean, independently of the implementation: `format/`. |
| Model semantics | What the translated operations represent: `design/`. This includes external I/O. |
| Component arguments | Invariants, path composition and file-specific C correspondence: `proof/`. |
| Evidence and acceptance | Checked target/proof links in `progress.md`; audit rules in `checking/`. |
| Current status | The single all-target graph and remaining-work inventory in `overview.md`. |

Earlier theorem-family mappings live in one reference appendix. The old migration
and translation-note paths contain only the redirects still named by source
comments; they are not alternative guides or progress trackers.
