import ZlibF.Proof.«deflate.c.engine.generic-foreign-default-macro»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

theorem foreign_output_private_outside {h : Heap} {r : ZStreamRef} {ds pb owner oo x : Nat}
    {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (array : (h.bytes x).isSome ∨ (h.words x).isSome)
    (owned : DeflateOwned ds d x) (pendingNe : x ≠ pb) :
    ¬ (StreamRoot r x ∨ x = ds ∨ x = pb ∨ x = owner) := by
  have absent : h.streams x = none ∧ h.dstates x = none ∧ h.gzstates x = none := by
    rcases array with bytes | words
    · cases get : h.bytes x with
      | none => simp only [get, Option.isSome_none] at bytes; contradiction
      | some a =>
        have onlyBytes := good.uniq.bytes_only get
        exact ⟨onlyBytes.2.1, onlyBytes.2.2.2.1, onlyBytes.2.2.2.2.2⟩
    · cases get : h.words x with
      | none => simp only [get, Option.isSome_none] at words; contradiction
      | some a =>
        have onlyWords := good.uniq.words_only get
        exact ⟨onlyWords.2.1, onlyWords.2.2.2.1, onlyWords.2.2.2.2.2⟩
  have rootNe : ¬ StreamRoot r x := by
    cases r with
    | tab i =>
      intro eq
      change x = i at eq
      have getter := good.live.hz
      simp only [ZStreamRef.get, ← eq, absent.1] at getter
      contradiction
    | in_gzstate_strm i =>
      intro eq
      change x = i at eq
      have getter := good.live.hz
      simp only [ZStreamRef.get, ← eq, absent.2.2, Option.map_none] at getter
      contradiction
  have stateNe : x ≠ ds := by
    intro eq
    have live := good.live.hs
    rw [← eq, absent.2.1] at live
    contradiction
  have outputNe : x ≠ owner := by
    obtain ⟨z0, get0, _, caller, _⟩ := buffers
    have same : z0 = z := Option.some.inj (get0.symm.trans good.live.hz)
    subst z0
    rcases caller with null | ⟨_, _, unowned⟩
    · rw [pointer] at null
      contradiction
    · intro eq
      exact unowned x (by simp only [ByteRoot, pointer, eq]) ((stream_owned_deflate good x).mpr owned)
  exact fun change => change.elim rootNe (fun change => change.elim stateNe (fun change => change.elim pendingNe outputNe))

/-- Neither tree/output processing nor publication changes the concrete
window, prev or head arrays. Caller output can be zero or short. -/
theorem OutputStorage.foreign_private_arrays {h after : Heap} {r : ZStreamRef} {ds pb owner oo w p q : Nat}
    {z : ZStream} {d : DeflateState} {window : Array UInt8} {prev head : Array UInt16}
    (storage : OutputStorage h after r ds pb owner)
    (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some window)
    (prevPtr : d.prev = .ref (.blk p) 0) (getPrev : h.words p = some prev)
    (headPtr : d.head = .ref (.blk q) 0) (getHead : h.words q = some head)
    (pendingPtr : d.pending_buf = .ref (.blk pb) 0) :
    after.bytes w = some window ∧ after.words p = some prev ∧ after.words q = some head := by
  obtain ⟨w0, p0, q0, b0, blocks⟩ := good.inv.blocks
  have we : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
  have be : b0 = pb := by simpa only [pendingPtr, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.pbuf.symm
  subst w0 b0
  obtain ⟨pending, getPending, _⟩ := blocks.ba
  have noByteP := (good.uniq.words_only getPrev).1
  have noByteQ := (good.uniq.words_only getHead).1
  have pNe : p ≠ pb := by intro eq; rw [eq, getPending] at noByteP; contradiction
  have qNe : q ≠ pb := by intro eq; rw [eq, getPending] at noByteQ; contradiction
  have wOutside := foreign_output_private_outside good buffers pointer (Or.inl (by simp only [get, Option.isSome_some]))
    (Or.inr (Or.inl win)) blocks.wb
  have pOutside := foreign_output_private_outside good buffers pointer (Or.inr (by simp only [getPrev, Option.isSome_some]))
    (Or.inr (Or.inr (Or.inl prevPtr))) pNe
  have qOutside := foreign_output_private_outside good buffers pointer (Or.inr (by simp only [getHead, Option.isSome_some]))
    (Or.inr (Or.inr (Or.inr (Or.inl headPtr)))) qNe
  have wLive : h.live w := Or.inl (by rw [get]; exact Option.some_ne_none _)
  have pLive : h.live p := Or.inr (Or.inl (by rw [getPrev]; exact Option.some_ne_none _))
  have qLive : h.live q := Or.inr (Or.inl (by rw [getHead]; exact Option.some_ne_none _))
  obtain ⟨_, _, _, _, _, frame⟩ := storage.frame
  exact ⟨(frame w wLive wOutside).1.trans get,
    (frame p pLive pOutside).2.1.trans getPrev, (frame q qLive qOutside).2.1.trans getHead⟩

/-- Exact state and storage frames preserve the full hash-chain content
predicate, with the same logical frontier and bytes. -/
theorem foreign_flush_frames_chains {h after : Heap} {r : ZStreamRef} {ds pb owner oo top : Nat}
    {z : ZStream} {d result : DeflateState}
    (storage : OutputStorage h after r ds pb owner)
    (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (pendingPtr : d.pending_buf = .ref (.blk pb) 0)
    (frame : FlushWorkFrame { d with block_start := d.strstart.toUInt64.toInt64 } result)
    (chains : HeapChains h d top) : HeapChains after result top := by
  obtain ⟨w, p, q, wa, pa, qa, win, prev, head, get, getPrev, getHead, chain⟩ := chains
  obtain ⟨winA, prevA, headA⟩ := storage.foreign_private_arrays good buffers pointer win get prev getPrev head getHead pendingPtr
  refine ⟨w, p, q, wa, pa, qa, ?_, ?_, ?_, winA, prevA, headA, ?_⟩
  · rw [frame]; exact win
  · rw [frame]; exact prev
  · rw [frame]; exact head
  · rw [frame]; exact chain

end Zlib.Deflate.Engine.Proofs
