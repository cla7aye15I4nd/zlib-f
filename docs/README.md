# Documentation

Start with [Proving the zlib implementation](overview.md). Its contents link to
sections and subsections explaining the claim, assumptions and proof framework,
then the inflate and deflate arguments.

Use these sections for detail:

- [Specifications](spec/README.md): platform scope, safety, input ranges, public
  API contracts, internal helper contracts and compressed-byte meaning.
- [Model](design/README.md): translation and memory semantics, abstract relations
  and external I/O.
- [Proofs](proof/README.md): the common method and each component's argument.
- [Checking](checking/README.md): what the evidence establishes and how it is accepted.
- [Progress](progress.md): the all-target dependency graph, exact proof evidence,
  blockers and remaining work.

[Trusted base](trusted-base.md) and [deviations](deviations.md) state assumptions
and model limits. [Findings](findings.md) records source reports with their scope.
[Runtime schema](runtime-schema.md) is a field reference. [Earlier arguments](proof/references.md)
is a reference appendix, not a second specification or status report.
