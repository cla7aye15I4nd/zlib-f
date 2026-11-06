# Documentation

Start with [current status](overview.md) and [the safety claim](safety.md).
Then choose the question you want to answer.

See the [coloured proof target graph](progress.md) for every registered target and its proof status.
The [overview](overview.md#proof-progress-graph) has the group graph and current work.

| Question | Read |
| --- | --- |
| What does a function require, return or change? | [API](api/README.md) |
| What bytes are valid compressed data? | [Data format](format/README.md) |
| How are C, memory and specifications represented? | [Design](design/README.md) |
| How do the proofs fit together? | [Proof guides](proof/README.md) |
| What makes a proof acceptable? | [Checking and reviews](checking/README.md) |
| How can earlier proofs be reused? | [Migration records](migration/README.md) |
| Which source details affect the translation? | [Translation notes](translation-notes/README.md) |
| What earlier work informed this project? | [Verification references](history/README.md) |

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
