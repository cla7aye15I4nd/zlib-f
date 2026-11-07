# What must be proved

This is the specification section. Read it before the model and proof guides.
It states required behaviour. It does not report completed verification.
[Progress](../progress.md) is the single current-status and remaining-work page.

## Read in this order

| Order | Document | Question it answers |
| --- | --- | --- |
| 1 | [Platform assumptions](platform.md) | Which system environment, including the per-object size bound, is accepted? |
| 2 | [Safety](safety.md) | What are UB, memory safety, termination, frame and ownership obligations? |
| 3 | [Input configurations](input-configurations.md) | Which fixed build and nested input ranges does a coverage colour describe? |
| 4 | [API contracts](api/README.md) | What may each caller pass, and what must each entry return or change? |
| 5 | [Internal helper contracts](internal-contracts.md) | What must the real caller establish before invoking a helper? |
| 6 | [Compressed-data format](format/README.md) | What do DEFLATE, zlib and gzip bytes mean independently of the implementation? |
| 7 | [Format relations](format/model.md) | How is that byte meaning expressed as mathematical relations? |

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
