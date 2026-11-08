# Documentation

Start with the [illustrated reading path](overview.md). The website offers
English and 简体中文 through the header language menu, including diagram labels.

Use these sections for detail:

- [Specifications](spec/README.md): platform scope, safety, input ranges, public
  API contracts, internal helper contracts and compressed-byte meaning.
- [Model](design/README.md): translation and memory semantics, abstract relations
  and external I/O.
- [Implementation arguments](proof/README.md): the common method and detailed
  reasoning for each C component, reached from the illustrated chapters.
- [Checking](checking/README.md): acceptance rules, with earlier review records
  grouped separately from the reading path and current status.
- [Progress](progress.md): the all-target dependency graph, exact proof evidence,
  blockers and remaining work.

[Trusted base](trusted-base.md) and [deviations](deviations.md) state assumptions
and model limits. [Findings](findings.md) records source reports with their scope.
[Runtime schema](runtime-schema.md) is a field reference. [Earlier arguments](proof/references.md)
is a reference appendix, not a second specification or status report.
