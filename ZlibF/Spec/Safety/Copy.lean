import ZlibF.Spec.Public.Copy

/-!
# Copy: safety goals

Split from `ZlibF/Spec/Public/Copy.lean` without a change of statement or name
(`docs/design/safety-functional-split.md`). The namespace stays `ZlibF.Spec.Public`.
-/

namespace ZlibF.Spec.Public
open C

/-- **Safety of `deflateCopy`** (the safety content of `Goal.deflateCopy`). Null arguments are
refused. From every reachable source (`StreamInvariant .deflate` is `DGood` with the default
allocator) into a distinct, readable destination record, the call returns without a fault, with
`Z_OK` or `Z_MEM_ERROR`. It leaves the source record and its state unchanged and writes only the
destination record and new blocks. On `Z_MEM_ERROR` an allocation really failed, the destination
state is cleared and the live blocks are unchanged (no leak). On `Z_OK` the destination satisfies
the stream invariant (`StreamInvariant .deflate`, written out) and the live blocks grow by exactly the five new blocks it owns. The copied
contents (`copiedDeflate` and the prefix clauses) are left to `Goal.deflateCopy`. The last clause is
zlib.h's refusal of an inconsistent source ("such as zalloc being Z_NULL"): a source record with a
null `zalloc`, a null `zfree` or no state (as a never-initialised record has in the model) is
refused with `Z_STREAM_ERROR`, and the destination state is cleared. -/
def Goal.deflateCopy_safety : Prop :=
  (∀ h source, C.run (Zlib.Deflate.deflateCopy none source) h = .ok (Z_STREAM_ERROR, h)) ∧
  (∀ h dest z, dest.get h = some z →
    C.run (Zlib.Deflate.deflateCopy (some dest) none) h =
      .ok (Z_STREAM_ERROR, dest.put h { z with state := none })) ∧
  (∀ h source i z s dest oldDest,
    StreamReachable .deflate h source → Zlib.Deflate.Spec.DGood h source i z s →
    Zlib.Deflate.Spec.DefAlloc z → source ≠ dest → dest.get h = some oldDest →
    ∃ rc after,
      C.run (Zlib.Deflate.deflateCopy (some dest) (some source)) h = .ok (rc, after) ∧
      source.get after = some z ∧ after.dstates i = some s ∧ Frame h after (StreamRoot dest) ∧
      ((rc = Z_MEM_ERROR ∧ AllocationFailed h after ∧
        dest.get after = some { oldDest with state := none } ∧
        LiveChange h after (fun _ => False) (fun _ => False)) ∨
       (rc = Z_OK ∧ (∃ i' z' s', Zlib.Deflate.Spec.DGood after dest i' z' s' ∧ Zlib.Deflate.Spec.DefAlloc z') ∧
       ∃ copied,
         after.dstates h.nextBlk = some copied ∧
         (∀ b, DeflateOwned h.nextBlk copied b ↔ h.nextBlk ≤ b ∧ b < h.nextBlk + 5) ∧
         LiveChange h after (DeflateOwned h.nextBlk copied) (fun _ => False)))) ∧
  (∀ h source dest zs oldDest, source.get h = some zs → dest.get h = some oldDest →
    (zs.zalloc = .null ∨ zs.zfree = .null ∨ zs.state = none) →
    C.run (Zlib.Deflate.deflateCopy (some dest) (some source)) h =
      .ok (Z_STREAM_ERROR, dest.put h { oldDest with state := none }))

/-- `int inflateCopy(z_streamp dest, z_streamp source)`.
**Safety of `inflateCopy`** (the safety content of `Goal.inflateCopy`). Null arguments are
refused. From every reachable source into a distinct, readable destination record, the call
returns without a fault, with `Z_OK` or `Z_MEM_ERROR`. It leaves the source record and its state
unchanged and writes only the destination record and new blocks. On `Z_MEM_ERROR` an allocation
really failed, the destination state is cleared and the live blocks are unchanged (no leak). On
`Z_OK` the destination is a reachable stream (`StreamReachable.inflateCopy`) and the live blocks
grow by exactly the fresh blocks its new state owns. The copied contents are left to
`Goal.inflateCopy`. An inconsistent source is refused by `Goal.inflate_refusal`. -/
def Goal.inflateCopy_safety : Prop :=
  (∀ h source, C.run (Zlib.Inflate.inflateCopy none source) h = .ok (Z_STREAM_ERROR, h)) ∧
  (∀ h dest z, dest.get h = some z →
    C.run (Zlib.Inflate.inflateCopy (some dest) none) h =
      .ok (Z_STREAM_ERROR, dest.put h { z with state := none })) ∧
  (∀ h source i z s dest oldDest,
    StreamReachable .inflate h source → Zlib.Inflate.Spec.Good h source i z s →
    Zlib.Inflate.Spec.DefAlloc z → source ≠ dest → dest.get h = some oldDest →
    ∃ rc after,
      C.run (Zlib.Inflate.inflateCopy (some dest) (some source)) h = .ok (rc, after) ∧
      source.get after = some z ∧ after.istates i = some s ∧ Frame h after (StreamRoot dest) ∧
      ((rc = Z_MEM_ERROR ∧ AllocationFailed h after ∧
        dest.get after = some { oldDest with state := none } ∧
        LiveChange h after (fun _ => False) (fun _ => False)) ∨
       (rc = Z_OK ∧ StreamReachable .inflate after dest ∧
        ∃ copied, after.istates h.nextBlk = some copied ∧
          (∀ b, InflateOwned h.nextBlk copied b → h.nextBlk ≤ b) ∧
          LiveChange h after (InflateOwned h.nextBlk copied) (fun _ => False))))

end ZlibF.Spec.Public
