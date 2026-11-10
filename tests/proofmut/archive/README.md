# Historical baseline-provider review

The [provider map](provider-map.json) records the review at publication base
`f22433f57c47a9e5fbce27b70053b17293541203`. At that base, ten complete original
harnesses were preserved as WIP source archives in commit
`67b3964c8efe3bfe0adf4935d6722020ae29d232`. Their mutations, assertions, options
and expected direct failures were not changed.

A later review approved 44 existing helper modules under the current contracts.
Those include all six exact module paths previously missing. The follow-up restores
the ten entire scripts to their original test paths, byte for byte. The historical
archive copies remain available in that earlier commit. The provider map here is
historical evidence, not a claim that those paths remain missing after promotion.

Apply the follow-up only after the approved provider source set and dependency
closure are present. The six provider paths and hashes are in
[`../original-companions-publication.json`](../original-companions-publication.json).
No generic replacement baseline or new proof is introduced. Provider retention does
not establish historical contract equivalence or mutation sensitivity. No harness,
mutant, or existing Lean counterexample was executed for this follow-up. The three
TSV strict suites still await the coordinated final artifact.
