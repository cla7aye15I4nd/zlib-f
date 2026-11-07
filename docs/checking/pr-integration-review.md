# Independent integration review

This review covers the integration boundaries of three pull requests.
It does not rederive every translated C statement or establish complete
zlib verification. Current obligations remain in [overview](../overview.md).

## Reviewed snapshots

| Request | Source snapshot | Scope |
| --- | --- | --- |
| 7 | `9e624d723321357e4cd37eaeaec4be10010bc4d0` | Proof registrations, changed semantic boundary, documentation protection and integration. |
| 8 | `a1368ba1d0d86c18acda63566fff371281fdacfe` | Compatibility of the approved source-policy calculation with both documentation layouts. |
| 9 | `d6a9becf5d3fcd2dc9be2b9af152cfc082ae1eeb` | Exact default compressor initialization, ownership, failures, witness and direct mutations. |

## Findings and corrections

The failed audit runs for requests 7 and 9 reported a protected-source
policy difference. They did not report duplicate proof registrations.
The old approved policy omitted sixteen relocated documentation files.
The compatibility policy reproduces the candidate policy exactly on both
reviewed snapshots: 310 and 312 protected files respectively. There are
no missing paths, extra paths or changed digests in those comparisons.

Request 8 preserves the old documentation scope and adds the new API and
format directories. The five relocated normative pages are mandatory in
the new layout. Empty, mixed and unknown manual layouts are rejected.
Its 21 regression tests pass. The three layout tests also pass with
assertions disabled.

Integrating requests 7 and 8 causes conflicts in the policy calculation
and its generated lock. The integration retains the compatibility
implementation and the new rejection tests. Generated locks require the
declaration audit; conflict markers are not resolved by editing digests.

The default initialization proof states the exact existing public goal.
Its success path establishes the representation invariant from actual
allocation, reset and initialization. Failure cleanup and the concrete
successful witness are explicit. It does not assume the general Init2
contract. All five independently rerun mutations are rejected: three
wrapper changes by the original exact proof, and two synchronized body
changes by their execution proofs. The positive baseline also passes.

The earlier registration batch includes explicit semantic changes, not
only added proofs. In particular, the Adler NULL-query domain is narrower
and the byte-address model changes. Their recorded scopes remain necessary.
Abstract-model targets do not establish implementation refinement.

The warning cleanup replaces 673 deprecated conditional-lemma references
in 67 mathematical and proof modules. It changes no theorem statement,
specification, translation or runtime definition. It does not disable
the unused-simplification diagnostics. Workflow checkout references use
the fixed revision of release 7.0.1, whose declared runtime is Node.js 24.
This intentionally changes the protected workflow files.

The complete rerun for request 9 exceeded the audit job's 90-minute limit.
The log records a passing baseline and rejection of eight negative examples
before cancellation. Each declaration audit took about five and a half minutes
in that run; the remaining examples and runtime mutations had not completed.
The audit job now has 180 minutes. Its commands, locks, negative examples and
proof mutations are unchanged. A timeout is not an audit pass.

## Concurrent proof work

A separate source snapshot contains the two ongoing stream developments.
The compressor connects actual default initialization, input refill and
one non-flushing slow iteration to stored-symbol meaning on the same heap.
The decoder connects its slow length/distance/match chain to caller ranges.
These are internal conditional results, not the exact public stream goals.
Both selected composition modules pass independent fresh-kernel replay.
Their inspected proofs use only the three permitted axioms.

At capture, four new decoder modules were outside the root import closure.
Coverage rejects that snapshot even if the imported root builds. This is
an observation about work in progress, not about the three reviewed commits.
Those concurrent sources are not included in this integration.

The proposed byte-object platform premise also changes the former public
inflate domain. Its documentation makes that change explicit. The unchanged
sequence target does not inherit that premise. This review does not count
the scoped result as a proof of the former domain or of the sequence goal.

## Acceptance

Only the checks recorded for a named final integration commit establish
its CI status. A merged request, a local build and a regenerated lock do
not themselves establish acceptance. Differential checks remain finite
evidence of translation fidelity, not proof. Full stream correctness is
not claimed by this review.
