# What must be proved

This is the specification section. Read it before the model and proof guides.
It states required behaviour. It does not report completed verification.
[Overview](../overview.md) is the single current-status and remaining-work page.

## Read in this order

| Order | Document | Question it answers |
| --- | --- | --- |
| 1 | [Safety](safety.md) | What are UB, memory safety, termination, frame and ownership obligations? |
| 2 | [Input configurations](input-configurations.md) | Which fixed build and nested input ranges does a coverage colour describe? |
| 3 | [API contracts](api/README.md) | What may each caller pass, and what must each entry return or change? |
| 4 | [Internal helper contracts](internal-contracts.md) | What must the real caller establish before invoking a helper? |
| 5 | [Compressed-data format](format/README.md) | What do DEFLATE, zlib and gzip bytes mean independently of the implementation? |
| 6 | [Format relations](format/model.md) | How is that byte meaning expressed as mathematical relations? |

API pages define entry behaviour. Format pages define byte meaning. Safety is
shared by both engines and every public entry. These are different obligations,
so each has one canonical home here.

## Documentary and formal statements

The exact fixed questions are Lean propositions under `ZlibF/Spec/` and the
file-specific specification namespaces. The [target index](../progress.md)
links each question to its exact statement and proof evidence. The documentary
contracts explain those questions; a prose change cannot discharge a target,
change its preconditions or grant a coverage colour.

Some documentary preconditions are narrower than the public header. Read the
entry's explicit scope and [deviations](../deviations.md). A narrow internal
lemma does not establish the complete public contract.

## Continue to the model and proofs

The [model guide](../design/README.md) explains how C operations are represented.
The [trusted base](../trusted-base.md) records assumptions and representation gaps.
The [proof guides](../proof/README.md) explain how the specifications are established.
The [checking guide](../checking/README.md) explains acceptance and registration.

Old `docs/api/`, `docs/format/` and `docs/safety.md` pages retained for source
references are forwarding pages only. All maintained specifications live here.
