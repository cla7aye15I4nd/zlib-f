import ZlibF.Spec.Public.Copy

/-!
# Copy: functional goals and the definitions only they use

Split from `ZlibF/Spec/Public/Copy.lean` without a change of statement or name
(`docs/design/safety-functional-split.md`). The namespace stays `ZlibF.Spec.Public`.
-/

namespace ZlibF.Spec.Public
open C

/-- `int inflateCopy(z_streamp dest, z_streamp source)`.
Copy every decoder field, relocate internal table pointers, share application header pointers,
and copy the initialized window bytes. All new storage is independent; failure releases it. -/
def Goal.inflateCopy : Prop :=
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
       (rc = Z_OK ∧ ∃ copied,
         Zlib.Inflate.Spec.Good after dest h.nextBlk
           { z with state := some (.inflate h.nextBlk) } copied ∧
         copied = { s with
           strm := some dest, window := copied.window
           lencode := relocateCode i h.nextBlk s.lencode
           distcode := relocateCode i h.nextBlk s.distcode
           next := relocateCode i h.nextBlk s.next } ∧
         (s.window = .null ↔ copied.window = .null) ∧
         (s.window ≠ .null → SameBytePrefix h after s.window copied.window s.whave.toNat) ∧
         (∀ b, InflateOwned h.nextBlk copied b → h.nextBlk ≤ b) ∧
         LiveChange h after (InflateOwned h.nextBlk copied) (fun _ => False))))

/-- `int deflateCopy(z_streamp dest, z_streamp source)`.
Copy the initialized window, hash entries, pending bytes and symbols. Relocate the owned
buffers and tree descriptors. A failure clears destination state and releases every new block. -/
def Goal.deflateCopy : Prop :=
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
       (rc = Z_OK ∧ ∃ copied,
         Zlib.Deflate.Spec.DGood after dest h.nextBlk
           { z with state := some (.deflate h.nextBlk) } copied ∧
         copied = copiedDeflate dest h.nextBlk s copied ∧
         SameBytePrefix h after s.window copied.window s.high_water.toNat ∧
         SameWordPrefix h after s.head copied.head s.hash_size.toNat ∧
         SameWordPrefix h after s.prev copied.prev
           (if s.slid ≠ 0 ∨ s.strstart - s.insert > s.w_size then s.w_size.toNat
            else (s.strstart - s.insert).toNat) ∧
         SameBytePrefix h after s.pending_out copied.pending_out s.pending.toNat ∧
         SameBytePrefix h after s.sym_buf copied.sym_buf s.sym_next.toNat ∧
         (∀ b, DeflateOwned h.nextBlk copied b ↔ h.nextBlk ≤ b ∧ b < h.nextBlk + 5) ∧
         LiveChange h after (DeflateOwned h.nextBlk copied) (fun _ => False))))

end ZlibF.Spec.Public
