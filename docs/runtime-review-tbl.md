# Review: heap tables as `Tbl`, `upd` and `Space.modify`

Scope: `Runtime/Space.lean` (`Tbl`, `upd`, `Space.modify`), `Runtime/Ptr.lean`, `Runtime/Alloc.lean`,
`Runtime/Tables.lean`, the generated `Space` instances (`scripts/gen_schema.py`), the paragraph "Tables and in-place
update" of `docs/trusted-base.md`, and the audit locks. Every claim below was checked against the code; the Lean
snippets were compiled (Lean 4.35.0, the runtime modules built, one scratch file importing `ZlibF.Runtime.Alloc`).
No other file was changed. This is a review by reading and by compiling small examples; it is not a differential run.

## Result

No unsound behaviour was found. Every operation the proofs use (`get`, `put`, `upd`, `live`, `slotUsed`, `Fresh`, the
allocation and free rules) has the same meaning as with function tables, as far as the entry at a block number is
concerned. The differences are in what can be *stated* (equality of tables) and in resources. None of the findings
below can make a theorem false; F1 can make a statement that was provable unprovable.

## Checked and fine

* Reads beyond the array: `Tbl.get t k = t.arr.getD k default`, so `none` / `false` (`Tbl.get_empty_opt`,
  `get_empty_bool`; `default : Option _` is `none` and `default : Bool` is `false`, both by `rfl`).
* Writes beyond the array: `Tbl.set` pads with `default` and pushes; `get_set` is proved for both branches, including
  `k = size` and `k > size`. `set_set`, `set_self`, `modify_eq` (with `k < size`) are proved, as are `upd_same`,
  `upd_ne`, `upd_apply`, `upd_upd`, `upd_self`.
* `Array.modify` out of range is the identity (`#eval #[1,2,3].modify 5 (· + 1)` gives `#[1, 2, 3]`). `Tbl.modify`
  is only used through `Tbl.modify_opt`, which requires `t k = some a`, hence `k < size`.
* `Space.modify` against `put h r (f a)`: for `blk` of bytes and words, and for every nested struct-array kind, the
  generated `modify_eq` proof goes through `Tbl.modify_opt` and is kernel checked (the build passes). For the static
  and `str` kinds, `put` and `modify` are both `h`, `modify_eq` closes by `rfl`; the `try` in front of `rfl` cannot hide
  a failure because an unsolved goal would be a build error.
* Dead references. `modify` on a block that is `none` stays `none` (all kinds use `Option.map`, so nothing is
  resurrected). Checked: `Space.modify Heap.empty (BRef.blk 7) f` has `bytes` equal to `Heap.empty.bytes` by `rfl`; for
  every heap with `h.bytes 7 = none`, `(Space.modify h (BRef.blk 7) f).bytes 7 = none`; `Space.modify h (BRef.str 0) f = h`
  by `rfl`. For a struct-array kind the dead case is again `Option.map f none = none`. `Ptr.store`, `memcpy`, `memmove`
  and `fill` only call `modify` after `Space.get h r = some a`, and the `_ok` theorems use `modify_eq` with that fact.
* `modify` does not look at `ro`; every caller tests `Space.ro` first (as `put` never did).
* The statement locks: `Eq h'.streams h.streams`, `Eq h' {... bytes := upd h.bytes b none ...}` and the like are
  structural equalities and hold for the new definitions (the audit passes with the existing locks, per the repository's
  own record; not re-run here).
* Executed path (question 4). In `ZlibF` there is no `unsafe`, `implemented_by`, `extern`, `csimp`, `opaque` or
  `attribute [...]` on runtime definitions (searched all of `ZlibF`, `tests`, `tools`); the audit also rejects the first
  four. `@[inline]` occurs only on helpers of `deflate_base.c.lean` (`rd`, `wr`, `zrd`, `zwr`, `padd`, `psub`,
  `store_at`), which does not change results. The only unsafe code on the path is inside Lean core
  (`Array.modify` is implemented by core's `modifyMUnsafe`, `Array.set!`, `push`, `++`, `replicate`); it lies outside
  the audited namespace. Its in-range behaviour is the specification of `Array.modify`, and the out-of-range
  behaviour was checked above.

## Findings

### F1. Table equality is structural: function-equal tables are different values (low, completeness)

Location: `Tbl` (a structure with the single field `arr`), `Tbl.set`, `upd`.

Why: `upd t k default` with `k` beyond the array changes the array (it grows), and `Tbl.empty` is `⟨#[]⟩`. Two tables
that agree at every block number can be different values, and nothing proves them equal (there is no extensionality
lemma, and none can exist). With function tables, `funext` identified them. Consequences:

* A statement of the form `upd t k none = t` (when `t k = none`), or "heap after `allocB` then `freeB` equals the
  heap before", was provable and is now false. A proof or a goal of that shape must be stated through the entries
  (`∀ b, h'.bytes b = h.bytes b`), not through `=` on tables or heaps.
* A hypothesis that says `h.bytes = Tbl.empty` is narrower than "every entry of `h.bytes` is `none`". A theorem or a
  witness that writes a table equality as a precondition is silently narrower than before. A search of the Lean sources
  outside `Schema.lean` found no such hypothesis; `tests/audit/statements.lock` has table equalities only in conclusions
  (stronger than before, so true).
* This cannot make a theorem false or vacuous: a structural equality is a stronger claim than a function equality, and
  `Tbl.get` is the only way the translations read a table.

Checked (compiles):
```lean
theorem neq : upd (Tbl.empty : Tbl (Option Nat)) 3 none ≠ Tbl.empty := by
  intro h
  have := congrArg (fun t => t.arr.size) h
  simp [upd, Tbl.set, Tbl.empty] at this
example : ¬ ∀ (t : Tbl (Option Nat)) k, t k = none → upd t k none = t := by
  intro H; exact neq (H Tbl.empty 3 (by simp))
example : ¬ (∀ (a b : Tbl (Option Nat)), (∀ k, a k = b k) → a = b) := by
  intro H
  have := H (upd Tbl.empty 3 none) Tbl.empty
    (by intro k; by_cases k = 3 <;> simp_all [upd_apply])
  exact neq this
```
`(upd Tbl.empty 3 none).arr.size` evaluates to 4. After `allocBytes #[1]` followed by `freeB`, `h.bytes.arr.size` is
1 (checked), so the freed slot stays as a `none` entry.

Suggested: say in `trusted-base.md` that table equality is structural and that statements must compare entries.

### F2. A large block number makes `Tbl.set` allocate a proportional array (low)

Location: `Tbl.set`, branch `k >= size`: `(t.arr ++ Array.replicate (k - t.arr.size) default).push v`.

Why: the cost and memory of `upd t k v` is linear in `k`, whereas a function table costs nothing. Checked:
`((Tbl.empty).set 3000000 (some 1)).arr.size = 3000001`. The allocation primitives use `h.nextBlk`, which grows by one per
allocation, so a run that starts from `Heap.empty` stays bounded by the number of allocations (per table, at most
`nextBlk`). A heap built by hand with a huge `nextBlk` (a driver or a witness that sets `{h with nextBlk := n}`) and then
allocated into, or evaluated by `rfl`/`decide` in the kernel, would try to build an array of size about `n`. No proof is
affected; it is a denial-of-service hazard for tests and witnesses only. `nextBlk` is not bounded by an invariant.

### F3. Stale comments that still describe function tables (low, documentation)

* `ZlibF/Runtime/Space.lean`, header item "`upd`, the update of a table (a function from block numbers)".
* `tests/lean/Driver/Deflate.lean` ("the runtime's tables are closures built by `upd`"), `Inflate.lean` ("the heap is
  a function updated by closures"), `Infback.lean` (same driver step). The compaction (`tabulate`) and `flatten` steps they
  describe are now unnecessary for speed; they are harmless (they rebuild each table with `Array.ofFn` and
  keep every entry), but they produce a table that is function-equal and not structurally equal to the old one, which is
  fine for the drivers because they never compare tables.

### F4. `Space.modify_eq` constrains `modify` only for live references (info, unconfirmed need)

Location: `class Space`, field `modify_eq : get h r = some a → modify h r f = put h r (f a)`.

For a dead reference nothing in the class says `modify h r f = h`. The generated instances do satisfy it (checked above
for bytes, `str`, and the `Option.map` pattern), and no proof can use the missing fact, because `Ptr.store`, `memcpy`,
`memmove` and `fill` call `modify` only after `get = some _`. It only matters if a later primitive calls `modify` on a
reference it has not checked; then the class would give no information about the dead case. Adding the field
`get h r = none → modify h r f = h` (provable for every generated instance by the same case split) would remove the gap.
Not needed today.

### F5. The audit locks the new definitions; it has no cheat that targets them (low)

Covered by `tests/audit/trusted.lock`: `C.Tbl`, `Tbl.arr`, `Tbl.get`, `Tbl.set`, `Tbl.modify`, `Tbl.empty`, the coercion and
`Inhabited` instances, `C.upd`, `C.Space` with `Space.modify`, and every generated `C.instSpaceHeap...` (with its
`match_` auxiliaries). The lock hashes both type and value, so a change of any of them, and a change of the statement of
`modify_eq` (it is part of the type of `Space.mk`), differs from the lock. Theorems (`Tbl.get_set`, `upd_*`,
`Tbl.modify_eq`, ...) are not locked, by design of the audit: they are kernel-checked and the axiom check covers them.
What is missing is a self-test cheat in `tests/audit/cheats` for this part (for example changing `Tbl.get` to ignore the
array, or `Space.modify` to resurrect a dead block). The general `touch_runtime.mut` and `weaken_runtime.mut` cheats
exercise the mechanism but not these declarations. Unconfirmed: whether the lock detects such mutations was not run here.

### F6. Memory per table grows with the number of allocations (info)

A freed block stays as a `none` entry and block numbers are never reused, so each table that is allocated into holds
one slot per block number up to the largest one used. This is the same asymptotics as the old chain of closures (which
was worse) and is a property of the never-reuse rule, not of `Tbl`.

## Not done

The review uses source reading and the compiled examples above. It does not record independent baseline approval. The full audit, witness build and
differential tests were not re-run.
