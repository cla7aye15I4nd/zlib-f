## Behaviour and scope

State the public behaviour or verification requirement changed.
Name any protected paths changed, including specifications, translation, runtime, scripts, tests,
configuration or locks. Explain every domain change and any new deviation.

## Semantic baseline

For a lock update, give the previous baseline commit and explain the generated diff.
Lock regeneration is not approval. Keep semantic changes separate from proof-only changes.

## Validation

List commands actually run and their results. Distinguish development checks, specification
readiness and final proof completion. Include expected failing readiness checks when contracts
or proofs remain open. Do not report a green build as complete API verification.
