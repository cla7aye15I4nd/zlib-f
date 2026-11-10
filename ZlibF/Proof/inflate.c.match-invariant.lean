import ZlibF.Proof.«inflate.c.match-segment»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- Replacing an existing writable byte view preserves all live objects. -/
theorem byte_view_put_shape {h : Heap} {dest : BRef} {output : Array UInt8}
    (get : Space.get h dest = some output) (write : Space.ro h dest = false)
    (array : Array UInt8) : Shape h (Space.put h dest array) := by
  cases dest with
  | blk id => exact shape_setB get array
  | str id => simp [Space.ro] at write
  | dstate_depth id =>
    cases state : h.dstates id with
    | none => simp [Space.get, state] at get
    | some s =>
      intro b
      by_cases same : b = id
      · subst b
        simp [Shape, Space.put, state]
      · simp [Shape, Space.put, state, upd_ne _ _ _ _ same]
  | st_dist_code => simp [Space.ro] at write
  | st_length_code => simp [Space.ro] at write

theorem byte_view_put_nextBlk (h : Heap) (dest : BRef) (array : Array UInt8) :
    (Space.put h dest array).nextBlk = h.nextBlk := by
  cases dest <;> simp only [Space.put]
  split <;> rfl

theorem byte_view_put_ro (h : Heap) (dest : BRef) (array : Array UInt8) :
    (Space.put h dest array).ro = h.ro := by
  cases dest <;> simp only [Space.put]
  split <;> rfl

/-- Caller output writes preserve the representation invariant when the
output is separate from the stream's owned window. -/
theorem _root_.Zlib.Inflate.Spec.Good.byte_view_put {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (good : Good h r zs z s) {dest : BRef} {output : Array UInt8}
    (get : Space.get h dest = some output) (write : Space.ro h dest = false)
    (separate : ∀ w, s.window = .ref (.blk w) 0 → dest ≠ .blk w) (array : Array UInt8) :
    Good (Space.put h dest array) r zs z s := by
  have shape := byte_view_put_shape get write array
  refine ⟨⟨by rw [byte_view_put_stream]; exact good.live.hz,
      by rw [byte_view_put_istates]; exact good.live.hs,
      good.live.zst, good.live.back, good.live.mode, good.live.zalloc, good.live.zfree⟩,
    ⟨good.inv.wf, ?_, good.inv.reqbits, good.inv.bits, good.inv.ptr⟩,
    shape.uniq good.uniq, shape.fresh (byte_view_put_nextBlk h dest array) good.fresh⟩
  have win := good.inv.win
  refine ⟨win.wbits, ?_, win.nullws, win.ws, win.hv, win.wn, win.eq⟩
  rcases win.block with null | ⟨w, saved, ptr, savedGet, savedWrite, size⟩
  · exact Or.inl null
  · refine Or.inr ⟨w, saved, ptr, ?_, by rw [byte_view_put_ro]; exact savedWrite, size⟩
    have unchanged := byte_view_get_put_ne h (separate w ptr).symm array
    change (Space.get (Space.put h dest array) (BRef.blk w) : Option (Array UInt8)) = some saved
    rw [unchanged]
    exact savedGet

theorem byte_view_put_code (h : Heap) (dest : BRef) (array : Array UInt8) (ref : CodeRef) :
    (Space.get (Space.put h dest array) ref : Option (Array Code)) = Space.get h ref := by
  cases dest <;> cases ref <;> simp only [Space.put, Space.get]
  all_goals split <;> rfl

/-- Output byte writes preserve both installed decoder tables. -/
theorem _root_.Zlib.Inflate.Spec.DataTablesSafe.byte_view_put {h : Heap} {s : InflateState}
    (tables : DataTablesSafe h s) (dest : BRef) (array : Array UInt8) :
    DataTablesSafe (Space.put h dest array) s := by
  constructor
  · obtain ⟨ref, offset, codes, ptr, get, safe⟩ := tables.lengthTable
    exact ⟨ref, offset, codes, ptr, by rw [byte_view_put_code]; exact get, safe⟩
  · obtain ⟨ref, offset, codes, ptr, get, safe⟩ := tables.distanceTable
    exact ⟨ref, offset, codes, ptr, by rw [byte_view_put_code]; exact get, safe⟩

/-- A copied output interval preserves all unread input, including when
the caller uses disjoint slices of the same allocation. -/
theorem BitInv.match_copy {h : Heap} {l : IL} {bs : List UInt8} (B : BitInv h l bs)
    {dest : BRef} {output : Array UInt8}
    (get : Space.get h dest = some output) (write : Space.ro h dest = false)
    (same : Bool) (saved : Array UInt8) (count sourceOffset outOffset : Nat)
    (separate : ∀ i, l.next = .ref dest i → i + bs.length ≤ outOffset ∨ outOffset + count ≤ i) :
    BitInv (Space.put h dest (ZlibF.Math.InflateMatchCopy.copy same saved count sourceOffset outOffset output)) l bs := by
  let array := ZlibF.Math.InflateMatchCopy.copy same saved count sourceOffset outOffset output
  refine ⟨B.have_eq, ?_, B.hold_lt⟩
  rcases B.next with empty | ⟨ref, input, off, ptr, inputGet, bound, contents⟩
  · exact Or.inl empty
  · by_cases sameRef : ref = dest
    · subst ref
      have inputEq : input = output := Option.some.inj (inputGet.symm.trans get)
      subst input
      refine Or.inr ⟨dest, array, off, ptr, byte_view_get_put get write array, ?_, ?_⟩
      · simpa only [array, ZlibF.Math.InflateMatchCopy.copy_size] using bound
      · exact contents.trans (ZlibF.Math.InflateMatchCopy.copy_slice same saved count sourceOffset outOffset output off bs.length bound (separate off ptr)).symm
    · refine Or.inr ⟨ref, input, off, ptr, ?_, bound, contents⟩
      rw [byte_view_get_put_ne h sameRef array]
      exact inputGet

/-- Empty input needs no positional separation. Nonempty input may share
the output allocation when its occupied interval is disjoint. -/
theorem BitInv.match_copy_ranges {h : Heap} {l : IL} {bs : List UInt8} (B : BitInv h l bs)
    {dest : BRef} {output : Array UInt8}
    (get : Space.get h dest = some output) (write : Space.ro h dest = false)
    (same : Bool) (saved : Array UInt8) (count sourceOffset outOffset : Nat)
    (separate : bs = [] ∨ ∀ i, l.next = .ref dest i → i + bs.length ≤ outOffset ∨ outOffset + count ≤ i) :
    BitInv (Space.put h dest (ZlibF.Math.InflateMatchCopy.copy same saved count sourceOffset outOffset output)) l bs := by
  rcases separate with empty | separate
  · exact ⟨B.have_eq, Or.inl empty, B.hold_lt⟩
  · exact B.match_copy get write same saved count sourceOffset outOffset separate

end Zlib.Inflate.Proofs
