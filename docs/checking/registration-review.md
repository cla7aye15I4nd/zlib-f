# Local proof registration checks

This batch registers 59 existing exact target proofs: six queries, nine checksum
entries, 29 stream or gzip entries, two initialization-domain goals and 13 abstract
model goals. It does not change a target statement, specification or translation.

The CRC generator wrapper proof now splits the zero-length case explicitly before
using its existing 64-bit theorem. Its type is unchanged. Twenty-three existing
proofs receive missing C-signature and scope docstrings.

## Mutation evidence

| List | Cases | Scope |
| --- | ---: | --- |
| `public-queries.tsv` | 20 | Query results and boundary behavior. |
| `public-checksums.tsv` | 9 | Adler updates/combinations and CRC combination entries. |
| `public-streams.tsv` | 94 | Stream and gzip entry results, guards and state changes. |
| `api-boundary.tsv` | 18 | Existing abstract-model and query boundary checks. |

The 48 mapped public targets passed fresh-kernel replay of their original exact
proofs. All 61 required mutants were rejected by those original proofs, in addition
to failures in the corresponding function proof modules.
All four strict lists pass on the integrated snapshot: 141 kills, no equivalent
cases, known gaps or bad mutants. Supplementary cases test additional branches.
A timeout or kernel resource error does not count as rejection.

Checksum mutations have concrete witnesses in the recorded domains:

| Entry | Permitted input | Changed behavior |
| --- | --- | --- |
| `adler32` | NULL buffer, length zero. | The wrapper changes the length to one, reaching a forbidden dereference. |
| `adler32_z` | One zero byte; seed `(65520 << 16) + 1`. | A high sum equal to 65521 is left unreduced. |
| `adler32_combine` | Two empty-input checksums (both one), second length zero. | The concatenation checksum becomes zero. |
| `adler32_combine64` | The same empty-input case. | The concatenation checksum becomes zero. |
| `crc32_combine_gen` | Length zero and initialized CRC tables. | The identity operator becomes the one-byte operator. |
| `crc32_combine_gen64` | Length minus one. | The rejection result changes from zero to one. |
| `crc32_combine_op` | Generated zero-length operator, first CRC zero, second CRC one. | Omitting the XOR changes the result from one to zero. |
| `crc32_combine` | First CRC zero, second CRC one, length one. | Swapping arguments changes the exact polynomial result. |
| `crc32_combine64` | The same numeric input. | Swapping the delegated arguments changes the exact result. |

The CRC operator and combination goals cover arbitrary checksum values and the
specified generated operators; the last three witnesses use that numeric domain.
Their concatenation interpretation still requires genuine checksums.

Three required stream mappings avoid resource failures in earlier attempts:

| Entry | Required mutation | Admitted behavior that changes |
| --- | --- | --- |
| `inflateInit_` | Omit delegation and return success. | A NULL version must be refused. |
| `inflateMark` | Return zero for a refused stream. | A NULL stream must return the documented negative sentinel. |
| `gzerror` | Return NULL instead of the message pointer. | An admitted non-memory-error view retains its non-NULL message. |

The default-window initialization mutation remains supplementary. Its first
failure is in the wrapper source-equation proof. That failure alone is insufficient
for exact public-proof acceptance. The required omission mutation separately
rejects the original exact public proof.

The query boundary resource limitation and the required replacement mapping are
recorded in the [query review](query-registration-review.md).

## Scope

Abstract model proofs establish properties of those models. They do not establish
refinement of the translated C implementation. Initialization-domain goals establish
usable call domains; they do not discharge every initialization entry contract.
Finite differential tests are evidence of translation fidelity, not proof.

The registration audit checks the compiled terms, allowed axioms and exact target
types. Canonical lock regeneration also captures previously accumulated source
changes, including the independently reviewed CRC byte-address representation.
Thirteen retained theorem types expand the new `Heap.byteBase` field. Comparing
the exported kernel syntax shows exactly one copied metadata field per type.
Removing only that new constructor argument reproduces each previous type byte
for byte. Its source heap is the same as the copied `garbage` field. The existing
binders, hypotheses and other result fields are unchanged. This read-only comparison
does not alter either canonical lock.

The 110 changed retained definitions split into eight earlier source or namespace changes, 70
heap-constructor expansions, 21 generated binder-name changes, nine heap
constructor/recursor declarations, and the CRC address function and its alignment
predicate. The 21 binder-name changes disappear when only lambda, forall and let
binder names are erased; their de Bruijn variables and other syntax stay equal.
The heap and CRC changes belong to the earlier byte-address repair, not this
registration patch.

The baseline also retires 42 obsolete `Pilot` definition entries after the earlier
module removal, plus two superseded generated address helpers. Compiler-generated helper additions are covered by the
[recursive helper review](compiler-helper-review.md).
Lock changes require review; regeneration by itself does not approve them.

The integrated root passes the fresh-kernel check and declaration audit. The audit
recognizes 77 exact registered targets, 382 listed theorems and 20,014 declarations.
The local auditor/harness tests (24), graph tests (18), no-sorry check and forbidden
construct check pass. The repaired tree-depth harness case also passes its positive
C/Lean baseline and detects the mutation. These checks do not report a full Linux
or sanitized differential-test pass for the integration commit.

Current counts, remaining work and final acceptance status are maintained only in
[the overview](../overview.md). A local registration is not a report of final CI
acceptance.

## Scoped open, close and priming branches

This batch adds fourteen scoped execution/frame theorems to the theorem registry.
It adds no proof of a complete public target. The public and supporting goal counts
remain unchanged; the new branches cannot turn a whole-function node green.

| Source | Checked domain and result | Remaining public work |
| --- | --- | --- |
| `gzlib.c.open` | NULL path/mode, negative descriptor, or initial allocation failure; exact returned handle, heap and file-system effects for `gzopen`, `gzopen64` and `gzdopen`. | Mode parsing, successful construction, later failures and public invariant establishment. |
| `gzread.c.close` | NULL/wrong-mode refusal; full `size = 0` reader-close execution under the existing `GzGood`, including owned strings, handle freeing, descriptor failure and unrelated-allocation frame. | Initialized readers and derivation of ownership/decoder invariants from public histories. |
| `deflate.c.prime` | Refused stream or bit count outside 0 through 16; refusal precedes compaction and has no heap effect. | Accepted counts, pending-byte compaction, emitted bits and invariant preservation. |

The positive root build passed. The strict targeted mutation lists
`tests/proofmut/gzip-frontier.tsv` and `tests/proofmut/deflate-prime-entry.tsv`
killed all eight and two direct source mutations respectively, with errors in the
matching function proof modules. These checks cover the stated branches, not every
branch of the public entries. Independent fresh-kernel replay passed separately for each of the three new proof
modules and its dependencies. The root declaration audit passed for 20,047 declarations
and 396 listed theorems, with 77 of 181 exact targets registered as before. This is not
a claim of a fresh replay of the complete root. Machine reports keep diagnostic output
separate. All existing semantic and statement lock records remain byte-for-byte unchanged.
The lock additions are two source helpers, five generated match/split definitions and
fourteen theorem types. The generated definitions are the close-result matcher and
private splitters produced while checking the close proof; they do not alter the existing
file-system or monad definitions. The viewer's 28 tests also pass, including checks that
readiness labels cannot grant proof status or create a blocker.
This record is not final CI acceptance.

The contracts, translations and runtime are unchanged. The new pure helper definitions
name the closed heap and fixed external close result; they are not assumptions about
library callees. Semantic and theorem-type lock additions are generated by the declaration
audit. The source-policy update covers the explicit milestone deviations, mutation lists
and the requested progress-viewer changes. Existing locked meanings and theorem types
must remain unchanged. Current prerequisites live in [overview](../overview.md#public-api-proof-readiness).
