# Heap-table review record

This historical review covers the move from function tables to array-backed `Tbl` values and
`Space.modify`. It found no incorrect primitive result in the inspected code. It identified
important differences in table equality and evaluation cost. This is not independent baseline
approval or a current defect list. Current work belongs in [progress](../progress.md).

## Scope and method

The review inspected `Runtime/Space.lean` (`Tbl`, `upd`, `Space.modify`), `Ptr.lean`, `Alloc.lean`,
`Tables.lean`, generated `Space` instances, the schema generator, the trusted-base account and
audit locks. Small examples were compiled with Lean 4.35.0 after building the runtime modules.
The scratch examples imported `ZlibF.Runtime.Alloc`. No source was changed.
The full audit, witness build and differential suite were not rerun. A prior recorded audit
pass was cited by the review; it was not reproduced there or by this documentation rewrite.

The review found the same entry-level behaviour for `get`, `put`, `upd`, liveness, slot use,
freshness, allocation and freeing as for function tables. Structural equality and resource
use differ. The examples below preserve the review evidence without claiming they have been
rerun against a later revision.

## Operations checked

| Operation | Review evidence |
| --- | --- |
| Out-of-range read | `Tbl.get` used `Array.getD`; missing optional entries were `none` and missing Boolean entries were `false`. Empty-table examples closed by reflexivity. |
| Extending write | `Tbl.set` padded with defaults and pushed. `get_set` covered both in-range and extending branches, including the boundary. Update and repeated-update lemmas were kernel checked. |
| Array modification | Out-of-range `Array.modify` left the array unchanged. `Tbl.modify_opt` required a live entry, which implied an in-range index. |
| `Space.modify` | Generated live-reference proofs established equality with `put h r (f a)` through `Tbl.modify_opt`. Static and string cases left the heap unchanged. An unfinished proof would still fail compilation. |
| Dead references | Byte, string and generated record-array examples did not resurrect a dead entry. The instances used `Option.map`; pointer writes checked liveness before calling `modify`. |
| Read-only checks | Callers tested `Space.ro` before modification, as they did before `put`. `modify` itself did not enforce it. |
| Executed definitions | The search across `ZlibF`, `tests` and `tools` found no `unsafe`, `implemented_by`, `extern`, `csimp`, `opaque` or execution-changing attributes on runtime definitions. Inlining on deflate helpers did not change results. Core array implementations remained outside the audited namespace. |
| Locks | The review observed the expected locked declarations and cited the earlier lock check. It did not rerun that check. |

## F1. Structural equality is stronger than agreement at every entry

Historical severity: Low, completeness and statement design.
`Tbl` stores an array. Writing a default value beyond the end grows that array, even though
all observable entries remain unchanged. Consequently no extensionality theorem can identify
all tables with equal entries.

The review compiled these counterexamples:

```lean
theorem neq : upd (Tbl.empty : Tbl (Option Nat)) 3 none ≠ Tbl.empty := by
  intro h
  have := congrArg (fun t => t.arr.size) h
  simp [upd, Tbl.set, Tbl.empty] at this

example : ¬ ∀ (t : Tbl (Option Nat)) k, t k = none → upd t k none = t := by
  intro H
  exact neq (H Tbl.empty 3 (by simp))

example : ¬ (∀ (a b : Tbl (Option Nat)), (∀ k, a k = b k) → a = b) := by
  intro H
  have := H (upd Tbl.empty 3 none) Tbl.empty
    (by intro k; by_cases k = 3 <;> simp_all [upd_apply])
  exact neq this
```

`upd Tbl.empty 3 none` had array size four. After allocation of one byte followed by free,
the byte table retained one `none` slot. Therefore exact heap restoration after allocate/free
is not the same statement as restoration of live objects and table entries.

A table-equality precondition can also be narrower than an entrywise condition. The review's
search outside `Schema.lean` found no such hypothesis; the inspected statement-lock table
equalities occurred in conclusions. That search is scoped evidence, not a general guarantee
against vacuous domains. A false restoration goal is a specification issue requiring separate
review; it must not be silently weakened to complete a proof. [The trusted base](../trusted-base.md)
explains the equality distinction.

## F2. Large block numbers cause proportional array allocation

Historical severity: Low, evaluation cost.
The extending branch of `Tbl.set` padded to the chosen index. Setting index 3,000,000 in an
empty table produced 3,000,001 slots in the compiled example. From an empty heap, allocation
numbers grow one at a time and table size is bounded by the allocation count. A manually
constructed huge `nextBlk` can instead require a huge array during evaluation or kernel
reduction. This was a test/witness resource hazard, not a false mathematical result.
The reviewed invariant did not bound `nextBlk`.

## F3. Comments still described function-table closures

Historical severity: Low, documentation.
The old `Space.lean` header described `upd` as updating a function. Driver comments for deflate,
inflate and callback inflate described closure compaction and flattening. Their reconstruction
steps preserved every entry but could change structural equality. The drivers did not compare
tables, so no incorrect observation was found. These are review-time comment findings; later
text must be assessed separately.

## F4. The class law constrained modification only for live references

Historical classification: Informational; need unconfirmed.
`Space.modify_eq` assumed `get h r = some a`. It said nothing about modification of a dead
reference. The generated instances handled dead references safely, and the reviewed primitives
checked liveness first. A later unchecked caller could not derive dead-reference behaviour
from this class law alone. The proposed additional law was
`get h r = none → modify h r f = h`; it was not needed by the inspected callers.

## F5. Locks covered the definitions; a targeted negative self-test was absent

Historical severity: Low, checking coverage.
The inspected trusted lock covered `C.Tbl`, its array field, get/set/modify/empty, coercion and
default instances, `C.upd`, `C.Space`, `Space.modify` and generated instances with their
auxiliaries. Type-and-value fingerprints included the `modify_eq` field in `Space.mk`.
Helper theorems were kernel checked and axiom audited rather than semantically locked.

The existing runtime-touch and runtime-weakening cheats exercised the general mechanism.
The review did not find a targeted cheat such as making `Tbl.get` ignore its array or making
modification resurrect a dead block. Detection of those mutations was not executed, so that
specific coverage remained unconfirmed. This finding is not permission to weaken the audit.

## F6. Freed slots remain allocated in the model's table storage

Historical classification: Informational.
Block numbers were never reused. Freeing replaced an entry with `none` rather than shrinking
the array. Each used table therefore retained slots up to its largest allocated block number.
The old closure representation had the same growth order and worse constants. This is a
property of the never-reuse model, separate from the proved ownership of live zlib objects.

## Lessons for later review

Separate object-level frame and ownership claims from the representation's storage equality.
Review arbitrary-heap preconditions as carefully as runs from the empty heap. Require liveness
checks before in-place modification and preserve the distinction between a class law and its
particular generated instances. Compiled examples and source searches help test these boundaries;
they do not establish whole-runtime fidelity to C or replace independent approval.
