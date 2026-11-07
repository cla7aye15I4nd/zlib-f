# Documentation

Start with [Understanding and proving zlib](overview.md). Follow its six illustrated
chapters from a complete task through encoded bytes, streaming, format wrappers,
state operations and application interfaces. Each chapter explains the relevant
proof obligations alongside the operation that needs them.

Use these sections for detail:

- [Specifications](spec/README.md): platform scope, safety, input ranges, public
  API contracts, internal helper contracts and compressed-byte meaning.
- [Model](design/README.md): translation and memory semantics, abstract relations
  and external I/O.
- [Implementation arguments](proof/README.md): the common method and detailed
  reasoning for each C component, reached from the illustrated chapters.
- [Checking](checking/README.md): what the evidence establishes and how it is accepted.
- [Progress](progress.md): the all-target dependency graph, exact proof evidence,
  blockers and remaining work.

[Trusted base](trusted-base.md) and [deviations](deviations.md) state assumptions
and model limits. [Findings](findings.md) records source reports with their scope.
[Runtime schema](runtime-schema.md) is a field reference. [Earlier arguments](proof/references.md)
is a reference appendix, not a second specification or status report.
