import ZlibF.Spec.Public.Streams

namespace ZlibF.Spec.Public
open C

def relocateCode (old fresh : Nat) : CodePtr → CodePtr
  | .ref (.istate_codes i) off => if i = old then .ref (.istate_codes fresh) off else .ref (.istate_codes i) off
  | p => p

def relocateByte (fresh old pointer : BPtr) : BPtr :=
  match fresh, old, pointer with
  | .ref r start, .ref _ base, .ref _ off => .ref r (start + off - base)
  | _, _, _ => .null

def SameBytePrefix (before after : Heap) (source dest : BPtr) (n : Nat) : Prop :=
  ∃ xs, Bytes before source n xs ∧ Bytes after dest n xs

def SameWordPrefix (before after : Heap) (source dest : WPtr) (n : Nat) : Prop :=
  ∃ r off a r' off' a', source = .ref r off ∧ dest = .ref r' off' ∧
    Space.get before r = some a ∧ Space.get after r' = some a' ∧
    off + n ≤ a.size ∧ off' + n ≤ a'.size ∧
    (a.toList.drop off).take n = (a'.toList.drop off').take n

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

def copiedDeflate (dest : ZStreamRef) (fresh : Nat) (old copied : DeflateState) : DeflateState :=
  { old with
    strm := some dest, window := copied.window, prev := copied.prev, head := copied.head
    pending_buf := copied.pending_buf
    pending_out := relocateByte copied.pending_buf old.pending_buf old.pending_out
    sym_buf := advance copied.pending_buf old.lit_bufsize.toNat
    l_desc := { old.l_desc with dyn_tree := .ref (.dstate_dyn_ltree fresh) 0 }
    d_desc := { old.d_desc with dyn_tree := .ref (.dstate_dyn_dtree fresh) 0 }
    bl_desc := { old.bl_desc with dyn_tree := .ref (.dstate_bl_tree fresh) 0 } }

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
