import ZlibF.Proof.«inflate.c.reachable»
import ZlibF.Proof.«inflate.c.copy-source-origin»
import ZlibF.Spec.Public.Copy

/-!
# inflate.c: `inflateCopy` on every reachable source

The six execution lemmas of `inflate.c.copy-*` give the exact heap after each
path of the copy: the first allocation fails, the window allocation fails, or
the copy succeeds with or without a window, from a dynamic or a fixed table.
This file adds the frame, the allocation ledger, the relocation form of the
copied state and the window prefix, for every source of a reachable history.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The tables of two heaps agree at one block. -/
def SameAt (after h : Heap) (b : Nat) : Prop :=
  after.bytes b = h.bytes b ∧ after.words b = h.words b ∧ after.streams b = h.streams b ∧
    after.gzheaders b = h.gzheaders b ∧ after.dstates b = h.dstates b ∧
    after.istates b = h.istates b ∧ after.gzstates b = h.gzstates b ∧ after.ro b = h.ro b

theorem SameAt.live {after h : Heap} {b : Nat} (same : SameAt after h b) : after.live b ↔ h.live b := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, _⟩ := same
  simp only [Heap.live, e1, e2, e3, e4, e5, e6, e7]

/-- A heap that changes no old block except the stream root is in the frame of the root. -/
theorem copy_frame {h after : Heap} {dest : ZStreamRef} (fresh : Fresh h)
    (static : after.static = h.static) (allocOk : after.allocOk = h.allocOk)
    (garbage : after.garbage = h.garbage) (next : h.nextBlk ≤ after.nextBlk)
    (count : h.nalloc ≤ after.nalloc)
    (low : ∀ b, b < h.nextBlk → ¬ StreamRoot dest b → SameAt after h b) :
    Frame h after (StreamRoot dest) := by
  refine ⟨static.symm, allocOk.symm, garbage.symm, next, count, ?_⟩
  intro b live root
  have bound : b < h.nextBlk := by
    by_cases small : b < h.nextBlk
    · exact small
    · exact False.elim (fresh b (by omega) live)
  exact low b bound root

/-- A stream write changes no block other than the stream root. -/
theorem put_other_block (h : Heap) (dest : ZStreamRef) (v : ZStream) {b : Nat}
    (root : ¬ StreamRoot dest b) :
    (dest.put h v).streams b = h.streams b ∧ (dest.put h v).gzstates b = h.gzstates b := by
  cases dest with
  | tab k =>
    have ne : b ≠ k := fun e => root (by simp [StreamRoot, e])
    simp only [ZStreamRef.put]
    split <;> simp [upd_ne _ _ _ _ ne]
  | in_gzstate_strm k =>
    have ne : b ≠ k := fun e => root (by simp [StreamRoot, e])
    simp only [ZStreamRef.put]
    split <;> simp [upd_ne _ _ _ _ ne]

/-- A stream reference that resolves names a live block. -/
theorem get_root_live {h : Heap} {dest : ZStreamRef} {z : ZStream} (get : dest.get h = some z)
    {b : Nat} (root : StreamRoot dest b) : h.live b := by
  cases dest with
  | tab k =>
    simp only [StreamRoot] at root
    subst root
    have e : h.streams b = some z := get
    simp [Heap.live, e]
  | in_gzstate_strm k =>
    simp only [StreamRoot] at root
    subst root
    cases e : h.gzstates b with
    | none => simp [ZStreamRef.get, e] at get
    | some g => simp [Heap.live, e]

/-- The window bytes of a decoder fit in its window block. -/
theorem whave_le_window {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (good : Good h r zs z s) : s.whave.toNat ≤ 2 ^ s.wbits.toNat := by
  have hv := good.inv.win.hv
  rcases good.inv.win.ws with small | full
  · have zero : s.whave.toNat = 0 := by omega
    rw [zero]
    exact Nat.zero_le _
  · rw [← full]
    exact hv

/-- The bytes a copy of `n` source bytes to the front of a fresh array keeps. -/
theorem copyRange_prefix (fresh source : Array UInt8) (n : Nat)
    (hd : n ≤ fresh.size) (hs : n ≤ source.size) :
    ((copyRange fresh source 0 0 n).toList.drop 0).take n = (source.toList.drop 0).take n := by
  simp only [List.drop_zero]
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_take, Array.getElem?_toList]
  by_cases small : j < n
  · rw [copyRange_getElem? fresh source 0 0 n (by omega) (by omega) j]
    simp [small]
  · simp [small]

/-- The common conclusion of a successful copy, from the facts each execution path gives. -/
theorem copy_success_conclusion {h after : Heap} {source dest : ZStreamRef} {zs : Nat}
    {z oldDest : ZStream} {s copied : InflateState}
    (current : InflateInv h source zs z s) (different : source ≠ dest)
    (destGet : dest.get h = some oldDest)
    (run : C.run (inflateCopy (some dest) (some source)) h = .ok (Z_OK, after))
    (destAfter : dest.get after = some { z with state := some (.inflate h.nextBlk) })
    (copiedGet : after.istates h.nextBlk = some copied)
    (relocated : copied = { s with
       strm := some dest, window := copied.window
       lencode := relocateCode zs h.nextBlk s.lencode
       distcode := relocateCode zs h.nextBlk s.distcode
       next := relocateCode zs h.nextBlk s.next })
    (windowNull : s.window = .null ↔ copied.window = .null)
    (windowBytes : s.window ≠ .null → SameBytePrefix h after s.window copied.window s.whave.toNat)
    (owned : ∀ b, InflateOwned h.nextBlk copied b → h.nextBlk ≤ b)
    (ledger : LiveChange h after (InflateOwned h.nextBlk copied) (fun _ => False)) :
    ∃ copied,
      Good after dest h.nextBlk { z with state := some (.inflate h.nextBlk) } copied ∧
      copied = { s with
        strm := some dest, window := copied.window
        lencode := relocateCode zs h.nextBlk s.lencode
        distcode := relocateCode zs h.nextBlk s.distcode
        next := relocateCode zs h.nextBlk s.next } ∧
      (s.window = .null ↔ copied.window = .null) ∧
      (s.window ≠ .null → SameBytePrefix h after s.window copied.window s.whave.toNat) ∧
      (∀ b, InflateOwned h.nextBlk copied b → h.nextBlk ≤ b) ∧
      LiveChange h after (InflateOwned h.nextBlk copied) (fun _ => False) := by
  obtain ⟨i', z', s', next, _⟩ := inflateCopy_invariant current different destGet run
  have sameStream : z' = { z with state := some (.inflate h.nextBlk) } :=
    Option.some.inj (next.good.live.hz.symm.trans destAfter)
  subst sameStream
  have sameIndex : i' = h.nextBlk := by
    have pointer := next.good.live.zst
    simp only at pointer
    cases pointer
    rfl
  subst sameIndex
  have sameState : s' = copied := Option.some.inj (next.good.live.hs.symm.trans copiedGet)
  subst sameState
  exact ⟨s', next.good, relocated, windowNull, windowBytes, owned, ledger⟩

/-- A live block of a fresh heap lies below `nextBlk`. -/
theorem live_lt_next {h : Heap} (fresh : Fresh h) {b : Nat} (live : h.live b) : b < h.nextBlk := by
  by_cases small : b < h.nextBlk
  · exact small
  · exact False.elim (fresh b (by omega) live)

/-- The heap of a successful copy without a window. -/
theorem copy_no_window_heap {h : Heap} {dest : ZStreamRef} {oldDest v : ZStream} {copied : InflateState}
    (destGet : dest.get h = some oldDest) (fresh : Fresh h) :
    Frame h (allocIstHeap (dest.put h v) copied) (StreamRoot dest) ∧
      ∀ b, (allocIstHeap (dest.put h v) copied).live b ↔ h.live b ∨ b = h.nextBlk := by
  constructor
  · refine copy_frame fresh (by simp [allocIstHeap]) (by simp [allocIstHeap]) (by simp [allocIstHeap])
      (by simp [allocIstHeap]) (by simp [allocIstHeap]) ?_
    intro b small root
    have ne : b ≠ h.nextBlk := by omega
    obtain ⟨streams, gzstates⟩ := put_other_block h dest v root
    refine ⟨by simp [allocIstHeap], by simp [allocIstHeap], by simpa [allocIstHeap] using streams,
      by simp [allocIstHeap], by simp [allocIstHeap], ?_, by simpa [allocIstHeap] using gzstates,
      by simp [allocIstHeap]⟩
    simp [allocIstHeap, upd_ne _ _ _ _ ne]
  · intro b
    have putLive := (shape_put destGet v).live b
    by_cases e : b = h.nextBlk
    · subst e
      constructor
      · intro _
        exact Or.inr rfl
      · intro _
        simp [Heap.live, allocIstHeap]
    · have same : SameAt (allocIstHeap (dest.put h v) copied) (dest.put h v) b := by
        refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl⟩
        simp [allocIstHeap, upd_ne _ _ _ _ e]
      rw [same.live, putLive]
      simp [e]

/-- The heap of a successful copy with a window. -/
theorem copy_window_heap {h : Heap} {dest : ZStreamRef} {z oldDest : ZStream} {s copied : InflateState}
    {sourceArray : Array UInt8} (destGet : dest.get h = some oldDest) (fresh : Fresh h) :
    Frame h (copiedWindowHeap h dest z s copied sourceArray) (StreamRoot dest) ∧
      ∀ b, (copiedWindowHeap h dest z s copied sourceArray).live b ↔
        h.live b ∨ b = h.nextBlk ∨ b = h.nextBlk + 1 := by
  let v : ZStream := { z with state := some (.inflate h.nextBlk) }
  constructor
  · refine copy_frame fresh
      (by simp [copiedWindowHeap, allocIstHeap, Zlib.Zutil.Proofs.allocHeap])
      (by simp [copiedWindowHeap, allocIstHeap, Zlib.Zutil.Proofs.allocHeap])
      (by simp [copiedWindowHeap, allocIstHeap, Zlib.Zutil.Proofs.allocHeap])
      (by simp [copiedWindowHeap, allocIstHeap, Zlib.Zutil.Proofs.allocHeap] <;> omega)
      (by simp [copiedWindowHeap, allocIstHeap, Zlib.Zutil.Proofs.allocHeap] <;> omega) ?_
    intro b small root
    have ne : b ≠ h.nextBlk := by omega
    have ne1 : b ≠ h.nextBlk + 1 := by omega
    obtain ⟨streams, gzstates⟩ := put_other_block h dest v root
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp [copiedWindowHeap, allocIstHeap, Zlib.Zutil.Proofs.allocHeap, upd_ne _ _ _ _ ne,
      upd_ne _ _ _ _ ne1]
    · exact streams
    · exact gzstates
  · intro b
    have putLive := (shape_put destGet v).live b
    by_cases e : b = h.nextBlk
    · subst e
      simp [Heap.live, copiedWindowHeap, allocIstHeap, Zlib.Zutil.Proofs.allocHeap]
    · by_cases e1 : b = h.nextBlk + 1
      · subst e1
        simp [Heap.live, copiedWindowHeap, allocIstHeap, Zlib.Zutil.Proofs.allocHeap]
      · have same : SameAt (copiedWindowHeap h dest z s copied sourceArray) (dest.put h v) b := by
          refine ⟨?_, rfl, rfl, rfl, rfl, ?_, rfl, ?_⟩
          all_goals simp [copiedWindowHeap, allocIstHeap, Zlib.Zutil.Proofs.allocHeap, v,
            upd_ne _ _ _ _ e, upd_ne _ _ _ _ e1]
        rw [same.live, putLive]
        simp [e, e1]

/-- The heap after the window allocation fails: the fresh state is freed again. -/
theorem copy_second_failure_heap {h : Heap} {dest : ZStreamRef} {oldDest v : ZStream}
    (destGet : dest.get h = some oldDest) (fresh : Fresh h) :
    let failed := { allocIstHeap h InflateState.zeroed with nalloc := (allocIstHeap h InflateState.zeroed).nalloc + 1 }
    Frame h (dest.put (freeIst failed h.nextBlk) v) (StreamRoot dest) ∧
      LiveChange h (dest.put (freeIst failed h.nextBlk) v) (fun _ => False) (fun _ => False) ∧
      (dest.put (freeIst failed h.nextBlk) v).nalloc = h.nalloc + 2 := by
  intro failed
  have none : h.istates h.nextBlk = none := by
    have dead := fresh h.nextBlk (Nat.le_refl _)
    simp only [Heap.live, not_or, ne_eq] at dead
    exact Classical.byContradiction dead.2.2.2.2.2.1
  have states : ∀ b, (freeIst failed h.nextBlk).istates b = h.istates b := by
    intro b
    by_cases e : b = h.nextBlk
    · subst e
      simp [freeIst, failed, allocIstHeap, none]
    · simp [freeIst, failed, allocIstHeap, upd_ne _ _ _ _ e]
  have middle : ∀ b, SameAt (freeIst failed h.nextBlk) h b := by
    intro b
    exact ⟨rfl, rfl, rfl, rfl, rfl, states b, rfl, rfl⟩
  have middleGet : dest.get (freeIst failed h.nextBlk) = some oldDest := by
    cases dest <;> simpa [ZStreamRef.get, freeIst, failed, allocIstHeap] using destGet
  refine ⟨?_, ?_, ?_⟩
  · refine copy_frame fresh (by simp [freeIst, failed, allocIstHeap]) (by simp [freeIst, failed, allocIstHeap])
      (by simp [freeIst, failed, allocIstHeap]) (by simp [freeIst, failed, allocIstHeap])
      (by simp [freeIst, failed, allocIstHeap]; omega) ?_
    intro b _ root
    obtain ⟨streams, gzstates⟩ := put_other_block (freeIst failed h.nextBlk) dest v root
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := middle b
    refine ⟨?_, ?_, streams.trans e3, ?_, ?_, ?_, gzstates.trans e7, ?_⟩
    · rw [ZStreamRef.put_bytes]; exact e1
    · rw [ZStreamRef.put_words]; exact e2
    · rw [ZStreamRef.put_gzheaders]; exact e4
    · rw [ZStreamRef.put_dstates]; exact e5
    · rw [ZStreamRef.put_istates]; exact e6
    · rw [ZStreamRef.put_ro]; exact e8
  · intro b
    have putLive := (shape_put middleGet v).live b
    rw [putLive, (middle b).live]
    simp
  · simp [freeIst, failed, allocIstHeap]

/-- `inflateCopy` with a null destination refuses and changes nothing. -/
theorem inflateCopy_null_dest (h : Heap) (source : ZStreamPtr) :
    C.run (inflateCopy none source) h = .ok (Z_STREAM_ERROR, h) := by
  simp [C.run, inflateCopy]

/-- `inflateCopy` with a null source refuses and clears the destination state. -/
theorem inflateCopy_null_source {h : Heap} {dest : ZStreamRef} {z : ZStream} (get : dest.get h = some z) :
    C.run (inflateCopy (some dest) none) h = .ok (Z_STREAM_ERROR, dest.put h { z with state := none }) := by
  simp [C.run, inflateCopy, inflateStateCheck, wrZ_eq, get]

/-- The C relocation of the three table pointers is `relocateCode`. -/
theorem copiedGeneric_relocated {dest : ZStreamRef} {zs fresh nextOff distOff : Nat} {window : BPtr}
    {s : InflateState} (nextPtr : s.next = .ref (.istate_codes zs) nextOff)
    (origin : (s.lencode = .ref (.istate_codes zs) 0 ∧ s.distcode = .ref (.istate_codes zs) distOff) ∨
      (s.lencode = .ref .st_lenfix 0 ∧ s.distcode = .ref .st_distfix 0)) :
    copiedGeneric dest zs fresh nextOff distOff window s = { s with
      strm := some dest, window := (copiedGeneric dest zs fresh nextOff distOff window s).window
      lencode := relocateCode zs fresh s.lencode
      distcode := relocateCode zs fresh s.distcode
      next := relocateCode zs fresh s.next } := by
  rcases origin with ⟨len, dist⟩ | ⟨len, dist⟩ <;>
    simp [copiedGeneric, relocateCode, len, dist, nextPtr]

/-- The window prefix of a successful windowed copy. -/
theorem copy_window_prefix {h : Heap} {r dest : ZStreamRef} {zs w : Nat} {z z' : ZStream}
    {s copied : InflateState} {sourceArray : Array UInt8}
    (good : Good h r zs z s) (ptr : s.window = .ref (.blk w) 0) (get : h.bytes w = some sourceArray)
    (copiedWindow : copied.window = .ref (.blk (h.nextBlk + 1)) 0) :
    SameBytePrefix h (copiedWindowHeap h dest z' s copied sourceArray) s.window copied.window
      s.whave.toNat := by
  have count := whave_le_window good
  have size : sourceArray.size = 2 ^ s.wbits.toNat := by
    rcases good.inv.win.block with empty | ⟨w', a, ptr', get', _, size'⟩
    · rw [ptr] at empty
      cases empty
    · have sameBlock : w' = w := by
        have e := ptr'.symm.trans ptr
        cases e
        rfl
      subst sameBlock
      have sameArray : a = sourceArray := Option.some.inj (get'.symm.trans get)
      subst sameArray
      exact size'
  let freshArray : Array UInt8 := Array.ofFn (n := 2 ^ s.wbits.toNat)
    (fun i => Junk.of (h.garbage (h.nalloc + 1) i.val))
  have freshSize : freshArray.size = 2 ^ s.wbits.toNat := by simp [freshArray]
  refine ⟨(sourceArray.toList.drop 0).take s.whave.toNat, Or.inr ⟨.blk w, 0, sourceArray, ptr,
    by simpa using get, by omega, rfl⟩, Or.inr ⟨.blk (h.nextBlk + 1), 0,
    copyRange freshArray sourceArray 0 0 s.whave.toNat, copiedWindow, ?_, ?_, ?_⟩⟩
  · simp [copiedWindowHeap, allocIstHeap, Zlib.Zutil.Proofs.allocHeap, freshArray]
  · rw [size_copyRange]
    omega
  · exact (copyRange_prefix freshArray sourceArray s.whave.toNat (by omega) (by omega)).symm

/-- A successful copy without a window, from either table origin. -/
theorem copy_no_window_success {h after : Heap} {source dest : ZStreamRef} {zs nextOff distOff : Nat}
    {z oldDest : ZStream} {s : InflateState}
    (current : InflateInv h source zs z s) (different : source ≠ dest)
    (destGet : dest.get h = some oldDest) (window : s.window = .null)
    (nextPtr : s.next = .ref (.istate_codes zs) nextOff)
    (origin : (s.lencode = .ref (.istate_codes zs) 0 ∧ s.distcode = .ref (.istate_codes zs) distOff) ∨
      (s.lencode = .ref .st_lenfix 0 ∧ s.distcode = .ref .st_distfix 0))
    (run : C.run (inflateCopy (some dest) (some source)) h = .ok (Z_OK, after))
    (destAfter : dest.get after = some { z with state := some (.inflate h.nextBlk) })
    (copiedGet : after.istates h.nextBlk = some (copiedGeneric dest zs h.nextBlk nextOff distOff .null s))
    (heapEq : after = allocIstHeap (dest.put h { z with state := some (.inflate h.nextBlk) })
      (copiedGeneric dest zs h.nextBlk nextOff distOff .null s)) :
    Frame h after (StreamRoot dest) ∧
    ∃ copied,
      Good after dest h.nextBlk { z with state := some (.inflate h.nextBlk) } copied ∧
      copied = { s with
        strm := some dest, window := copied.window
        lencode := relocateCode zs h.nextBlk s.lencode
        distcode := relocateCode zs h.nextBlk s.distcode
        next := relocateCode zs h.nextBlk s.next } ∧
      (s.window = .null ↔ copied.window = .null) ∧
      (s.window ≠ .null → SameBytePrefix h after s.window copied.window s.whave.toNat) ∧
      (∀ b, InflateOwned h.nextBlk copied b → h.nextBlk ≤ b) ∧
      LiveChange h after (InflateOwned h.nextBlk copied) (fun _ => False) := by
  obtain ⟨frame, live⟩ := copy_no_window_heap
    (v := { z with state := some (.inflate h.nextBlk) })
    (copied := copiedGeneric dest zs h.nextBlk nextOff distOff .null s) destGet current.good.fresh
  rw [← heapEq] at frame live
  refine ⟨frame, copy_success_conclusion current different destGet run destAfter copiedGet
    (copiedGeneric_relocated nextPtr origin) ?_ (fun nonnull => False.elim (nonnull window)) ?_ ?_⟩
  · simp [copiedGeneric, window]
  · intro b owned
    rcases owned with e | e
    · omega
    · simp [copiedGeneric] at e
  · intro b
    rw [live b]
    simp [InflateOwned, copiedGeneric]

/-- A successful copy with a window, from either table origin. -/
theorem copy_window_success {h after : Heap} {source dest : ZStreamRef} {zs nextOff distOff w : Nat}
    {z oldDest : ZStream} {s : InflateState} {sourceArray : Array UInt8}
    (current : InflateInv h source zs z s) (different : source ≠ dest)
    (destGet : dest.get h = some oldDest)
    (nextPtr : s.next = .ref (.istate_codes zs) nextOff)
    (origin : (s.lencode = .ref (.istate_codes zs) 0 ∧ s.distcode = .ref (.istate_codes zs) distOff) ∨
      (s.lencode = .ref .st_lenfix 0 ∧ s.distcode = .ref .st_distfix 0))
    (run : C.run (inflateCopy (some dest) (some source)) h = .ok (Z_OK, after))
    (destAfter : dest.get after = some { z with state := some (.inflate h.nextBlk) })
    (copiedGet : after.istates h.nextBlk =
      some (copiedGeneric dest zs h.nextBlk nextOff distOff (.ref (.blk (h.nextBlk + 1)) 0) s))
    (ptr : s.window = .ref (.blk w) 0) (get : h.bytes w = some sourceArray)
    (heapEq : after = copiedWindowHeap h dest z s
      (copiedGeneric dest zs h.nextBlk nextOff distOff (.ref (.blk (h.nextBlk + 1)) 0) s) sourceArray) :
    Frame h after (StreamRoot dest) ∧
    ∃ copied,
      Good after dest h.nextBlk { z with state := some (.inflate h.nextBlk) } copied ∧
      copied = { s with
        strm := some dest, window := copied.window
        lencode := relocateCode zs h.nextBlk s.lencode
        distcode := relocateCode zs h.nextBlk s.distcode
        next := relocateCode zs h.nextBlk s.next } ∧
      (s.window = .null ↔ copied.window = .null) ∧
      (s.window ≠ .null → SameBytePrefix h after s.window copied.window s.whave.toNat) ∧
      (∀ b, InflateOwned h.nextBlk copied b → h.nextBlk ≤ b) ∧
      LiveChange h after (InflateOwned h.nextBlk copied) (fun _ => False) := by
  obtain ⟨frame, live⟩ := copy_window_heap (z := z) (s := s)
    (copied := copiedGeneric dest zs h.nextBlk nextOff distOff (.ref (.blk (h.nextBlk + 1)) 0) s)
    (sourceArray := sourceArray) destGet current.good.fresh
  have windowPrefix := copy_window_prefix (dest := dest) (z' := z) current.good ptr get
    (copied := copiedGeneric dest zs h.nextBlk nextOff distOff (.ref (.blk (h.nextBlk + 1)) 0) s)
    (by simp [copiedGeneric])
  rw [← heapEq] at frame live windowPrefix
  refine ⟨frame, copy_success_conclusion current different destGet run destAfter copiedGet
    (copiedGeneric_relocated nextPtr origin) ?_ (fun _ => windowPrefix) ?_ ?_⟩
  · simp [copiedGeneric, ptr]
  · intro b owned
    rcases owned with e | e
    · omega
    · simp [copiedGeneric] at e
      omega
  · intro b
    rw [live b]
    simp only [InflateOwned, copiedGeneric]
    constructor
    · rintro (old | new | new)
      · exact Or.inl ⟨old, not_false⟩
      · exact Or.inr (Or.inl new)
      · exact Or.inr (Or.inr (by rw [new]))
    · rintro (⟨old, _⟩ | new | new)
      · exact Or.inl old
      · exact Or.inr (Or.inl new)
      · simp at new
        exact Or.inr (Or.inr new.symm)

end Zlib.Inflate.Proofs
