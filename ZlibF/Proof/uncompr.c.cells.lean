import ZlibF.Proof.«uncompr.c.entry»

/-!
# Exact scalar cells used by uncompress

The real load64 decodes LengthCell's eight little-endian bytes. The real store64
replaces exactly those eight bytes while preserving both surrounding slices.
All admitted byte views and offsets are included. No callee contract is assumed.
-/

namespace Zlib.Uncompr.Proof.Cells
open C Zlib.Gzguts
theorem word64_roundtrip (n : UInt64) :
    n.toUInt8.toUInt64 ||| (n >>> 8).toUInt8.toUInt64 <<< 8 |||
      (n >>> 16).toUInt8.toUInt64 <<< 16 ||| (n >>> 24).toUInt8.toUInt64 <<< 24 |||
      (n >>> 32).toUInt8.toUInt64 <<< 32 ||| (n >>> 40).toUInt8.toUInt64 <<< 40 |||
      (n >>> 48).toUInt8.toUInt64 <<< 48 ||| (n >>> 56).toUInt8.toUInt64 <<< 56 = n := by
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [UInt8.toBitVec_toUInt64, UInt64.toBitVec_toUInt8,
    UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight,
    BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', UInt64.toBitVec_ofNat, BitVec.toNat_umod, BitVec.toNat_ofNat,
    BitVec.getLsbD_or, BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
    i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨
    i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨
    i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨
    i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨
    i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 ∨ i = 47 ∨
    i = 48 ∨ i = 49 ∨ i = 50 ∨ i = 51 ∨ i = 52 ∨ i = 53 ∨ i = 54 ∨ i = 55 ∨
    i = 56 ∨ i = 57 ∨ i = 58 ∨ i = 59 ∨ i = 60 ∨ i = 61 ∨ i = 62 ∨ i = 63) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

open ZlibF.Spec.Public

theorem uint64_bytes (v : UInt64) :
    lengthBytes v = [v.toUInt8, (v >>> 8).toUInt8, (v >>> 16).toUInt8,
      (v >>> 24).toUInt8, (v >>> 32).toUInt8, (v >>> 40).toUInt8,
      (v >>> 48).toUInt8, (v >>> 56).toUInt8] := by
  have hr : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := by decide
  rw [lengthBytes, hr]
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true,
    Nat.pow_zero, Nat.reducePow, Nat.div_one]
  repeat' constructor
  all_goals apply UInt8.toNat_inj.mp
  all_goals simp [UInt8.toNat_ofNat', UInt64.toNat_toUInt8, UInt64.toNat_shiftRight,
    Nat.shiftRight_eq_div_pow]

theorem load64_encoded (h : Heap) (r : BRef) (off : Nat) (a : Array UInt8) (v : UInt64)
    (hg : Space.get h r = some a) (hb : off + 8 ≤ a.size)
    (contents : (a.toList.drop off).take 8 = lengthBytes v) :
    load64 (.ref r off) h = .ok (v,h) := by
  have hd (i : Nat) (hi : i < 8) : a[off + i]! = (lengthBytes v)[i]! := by
    have hlen : i < ((a.toList.drop off).take 8).length := by
      simp only [List.length_take, List.length_drop, Array.length_toList]
      omega
    have he := congrArg (fun xs : List UInt8 => xs[i]!) contents
    rw [getElem!_pos ((a.toList.drop off).take 8) i hlen, List.getElem_take, List.getElem_drop, Array.getElem_toList] at he
    simpa only [getElem!_pos a (off + i) (by omega)] using he
  have hi (i : Nat) (hh : i < 8) :
      index8 (.ref r off) i h = .ok ((lengthBytes v)[i]!, h) := by
    have hp := Ptr.index_ok (h := h) (off := off) (i := i) hg (by omega)
    simpa only [OkOn, getElem!_pos a (off+i) (by omega), ← hd i hh] using hp
  have h0 := hi 0 (by decide)
  have h1 := hi 1 (by decide)
  have h2 := hi 2 (by decide)
  have h3 := hi 3 (by decide)
  have h4 := hi 4 (by decide)
  have h5 := hi 5 (by decide)
  have h6 := hi 6 (by decide)
  have h7 := hi 7 (by decide)
  simp [uint64_bytes] at h0 h1 h2 h3 h4 h5 h6 h7
  simpa [load64, List.range', h0, h1, h2, h3, h4, h5, h6, h7] using
    congrArg (fun word : UInt64 => (Except.ok (word, h) : Except Fault (UInt64 × Heap)))
      (word64_roundtrip v)


theorem load64_lengthCell (h : Heap) (p : BPtr) (v : UInt64)
    (cell : LengthCell h p v) : C.run (load64 p) h = .ok (v,h) := by
  rcases cell.1 with null | ⟨r, off, a, pointer, get, room, values⟩
  · simp at null
  · subst p
    exact load64_encoded h r off a v get room values.symm


private theorem byte_get_put {h : Heap} {r : BRef} {a : Array UInt8}
    (hg : Space.get h r = some a) (hro : Space.ro h r = false) (b : Array UInt8) :
    Space.get (Space.put h r b) r = some b := by
  cases r with
  | blk id => simp [Space.get, Space.put]
  | str id => simp [Space.ro] at hro
  | dstate_depth id =>
    cases hs : h.dstates id with
    | none => simp [Space.get, hs] at hg
    | some s => simp [Space.get, Space.put, hs]
  | st_dist_code => simp [Space.ro] at hro
  | st_length_code => simp [Space.ro] at hro

private theorem byte_ro_put (h : Heap) (r : BRef) (a : Array UInt8) :
    Space.ro (Space.put h r a) r = Space.ro h r := by
  cases r <;> simp [Space.put, Space.ro]

private theorem byte_put_put {h : Heap} {r : BRef} {a : Array UInt8}
    (hg : Space.get h r = some a) (hro : Space.ro h r = false) (b c : Array UInt8) :
    Space.put (Space.put h r b) r c = Space.put h r c := by
  cases r with
  | blk id => simp [Space.put, upd_upd]
  | str id => simp [Space.ro] at hro
  | dstate_depth id =>
    cases hs : h.dstates id with
    | none => simp [Space.get, hs] at hg
    | some s => simp [Space.put, hs, upd_upd]
  | st_dist_code => simp [Space.ro] at hro
  | st_length_code => simp [Space.ro] at hro


private def storedWordAt (a : Array UInt8) (off : Nat) (v : UInt64) : Array UInt8 :=
  (List.range 8).foldl (fun a i => a.set! (off + i) (v >>> (8 * i).toUInt64).toUInt8) a

theorem store64_view_run (h : Heap) (r : BRef) (a : Array UInt8) (off : Nat) (v : UInt64)
    (hg : Space.get h r = some a) (hro : Space.ro h r = false) (hfit : off + 8 ≤ a.size) :
    store64 (.ref r off) v h = .ok ((), Space.put h r (storedWordAt a off v)) := by
  have add0 : (Ptr.ref r off).add (0 : Int) h = .ok (.ref r (off + 0), h) := by
    simpa [OkOn] using Ptr.add_nat_ok (h := h) (off := off) (n := 0) hg (by omega)
  let a1 := a.set! (off + 0) v.toUInt8
  let h1 := Space.put h r a1
  have st0 : store8 (.ref r (off + 0)) v.toUInt8 h = .ok ((), h1) := by
    have step := Ptr.store_ok (h := h) (off := off + 0) (v := v.toUInt8) hg hro (by omega)
    simpa [h1, a1, byte_put_put hg hro] using step
  have get1 : Space.get h1 r = some a1 := byte_get_put hg hro a1
  have ro1 : Space.ro h1 r = false := by simpa [h1, byte_ro_put] using hro
  have add1 : (Ptr.ref r off).add (1 : Int) h1 = .ok (.ref r (off + 1), h1) := by
    simpa [OkOn] using Ptr.add_nat_ok (h := h1) (off := off) (n := 1) get1 (by simp [a1] ; omega)
  let a2 := a1.set! (off + 1) (v >>> 8).toUInt8
  let h2 := Space.put h r a2
  have st1 : store8 (.ref r (off + 1)) (v >>> 8).toUInt8 h1 = .ok ((), h2) := by
    have step := Ptr.store_ok (h := h1) (off := off + 1) (v := (v >>> 8).toUInt8) get1 ro1 (by simp [a1]; omega)
    simpa [h1, h2, a2, byte_put_put hg hro] using step
  have get2 : Space.get h2 r = some a2 := byte_get_put hg hro a2
  have ro2 : Space.ro h2 r = false := by simpa [h2, byte_ro_put] using hro
  have add2 : (Ptr.ref r off).add (2 : Int) h2 = .ok (.ref r (off + 2), h2) := by
    simpa [OkOn] using Ptr.add_nat_ok (h := h2) (off := off) (n := 2) get2 (by simp [a1, a2] ; omega)
  let a3 := a2.set! (off + 2) (v >>> 16).toUInt8
  let h3 := Space.put h r a3
  have st2 : store8 (.ref r (off + 2)) (v >>> 16).toUInt8 h2 = .ok ((), h3) := by
    have step := Ptr.store_ok (h := h2) (off := off + 2) (v := (v >>> 16).toUInt8) get2 ro2 (by simp [a1, a2]; omega)
    simpa [h1, h2, h3, a3, byte_put_put hg hro] using step
  have get3 : Space.get h3 r = some a3 := byte_get_put hg hro a3
  have ro3 : Space.ro h3 r = false := by simpa [h3, byte_ro_put] using hro
  have add3 : (Ptr.ref r off).add (3 : Int) h3 = .ok (.ref r (off + 3), h3) := by
    simpa [OkOn] using Ptr.add_nat_ok (h := h3) (off := off) (n := 3) get3 (by simp [a1, a2, a3] ; omega)
  let a4 := a3.set! (off + 3) (v >>> 24).toUInt8
  let h4 := Space.put h r a4
  have st3 : store8 (.ref r (off + 3)) (v >>> 24).toUInt8 h3 = .ok ((), h4) := by
    have step := Ptr.store_ok (h := h3) (off := off + 3) (v := (v >>> 24).toUInt8) get3 ro3 (by simp [a1, a2, a3]; omega)
    simpa [h1, h2, h3, h4, a4, byte_put_put hg hro] using step
  have get4 : Space.get h4 r = some a4 := byte_get_put hg hro a4
  have ro4 : Space.ro h4 r = false := by simpa [h4, byte_ro_put] using hro
  have add4 : (Ptr.ref r off).add (4 : Int) h4 = .ok (.ref r (off + 4), h4) := by
    simpa [OkOn] using Ptr.add_nat_ok (h := h4) (off := off) (n := 4) get4 (by simp [a1, a2, a3, a4] ; omega)
  let a5 := a4.set! (off + 4) (v >>> 32).toUInt8
  let h5 := Space.put h r a5
  have st4 : store8 (.ref r (off + 4)) (v >>> 32).toUInt8 h4 = .ok ((), h5) := by
    have step := Ptr.store_ok (h := h4) (off := off + 4) (v := (v >>> 32).toUInt8) get4 ro4 (by simp [a1, a2, a3, a4]; omega)
    simpa [h1, h2, h3, h4, h5, a5, byte_put_put hg hro] using step
  have get5 : Space.get h5 r = some a5 := byte_get_put hg hro a5
  have ro5 : Space.ro h5 r = false := by simpa [h5, byte_ro_put] using hro
  have add5 : (Ptr.ref r off).add (5 : Int) h5 = .ok (.ref r (off + 5), h5) := by
    simpa [OkOn] using Ptr.add_nat_ok (h := h5) (off := off) (n := 5) get5 (by simp [a1, a2, a3, a4, a5] ; omega)
  let a6 := a5.set! (off + 5) (v >>> 40).toUInt8
  let h6 := Space.put h r a6
  have st5 : store8 (.ref r (off + 5)) (v >>> 40).toUInt8 h5 = .ok ((), h6) := by
    have step := Ptr.store_ok (h := h5) (off := off + 5) (v := (v >>> 40).toUInt8) get5 ro5 (by simp [a1, a2, a3, a4, a5]; omega)
    simpa [h1, h2, h3, h4, h5, h6, a6, byte_put_put hg hro] using step
  have get6 : Space.get h6 r = some a6 := byte_get_put hg hro a6
  have ro6 : Space.ro h6 r = false := by simpa [h6, byte_ro_put] using hro
  have add6 : (Ptr.ref r off).add (6 : Int) h6 = .ok (.ref r (off + 6), h6) := by
    simpa [OkOn] using Ptr.add_nat_ok (h := h6) (off := off) (n := 6) get6 (by simp [a1, a2, a3, a4, a5, a6] ; omega)
  let a7 := a6.set! (off + 6) (v >>> 48).toUInt8
  let h7 := Space.put h r a7
  have st6 : store8 (.ref r (off + 6)) (v >>> 48).toUInt8 h6 = .ok ((), h7) := by
    have step := Ptr.store_ok (h := h6) (off := off + 6) (v := (v >>> 48).toUInt8) get6 ro6 (by simp [a1, a2, a3, a4, a5, a6]; omega)
    simpa [h1, h2, h3, h4, h5, h6, h7, a7, byte_put_put hg hro] using step
  have get7 : Space.get h7 r = some a7 := byte_get_put hg hro a7
  have ro7 : Space.ro h7 r = false := by simpa [h7, byte_ro_put] using hro
  have add7 : (Ptr.ref r off).add (7 : Int) h7 = .ok (.ref r (off + 7), h7) := by
    simpa [OkOn] using Ptr.add_nat_ok (h := h7) (off := off) (n := 7) get7 (by simp [a1, a2, a3, a4, a5, a6, a7] ; omega)
  let a8 := a7.set! (off + 7) (v >>> 56).toUInt8
  let h8 := Space.put h r a8
  have st7 : store8 (.ref r (off + 7)) (v >>> 56).toUInt8 h7 = .ok ((), h8) := by
    have step := Ptr.store_ok (h := h7) (off := off + 7) (v := (v >>> 56).toUInt8) get7 ro7 (by simp [a1, a2, a3, a4, a5, a6, a7]; omega)
    simpa [h1, h2, h3, h4, h5, h6, h7, h8, a8, byte_put_put hg hro] using step
  simp only [Nat.add_zero] at add0 st0
  simp [store64, List.range', add0, add1, add2, add3, add4, add5, add6, add7, st0, st1, st2, st3, st4, st5, st6, st7]
  simp [h8, storedWordAt, List.range, List.range.loop, a8, a7, a6, a5, a4, a3, a2, a1]

/-- Eight byte writes replace exactly the selected slice. -/
theorem set_eight_slice (a : Array UInt8) (off : Nat) (hfit : off + 8 ≤ a.size)
    (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    ((((((((a.set! (off + 0) b0).set! (off + 1) b1).set! (off + 2) b2).set! (off + 3) b3).set! (off + 4) b4).set! (off + 5) b5).set! (off + 6) b6).set! (off + 7) b7) =
      a.extract 0 off ++ #[b0, b1, b2, b3, b4, b5, b6, b7] ++ a.extract (off + 8) a.size := by
  apply Array.ext_getElem?
  intro j
  simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds,
    Array.getElem?_append, Array.size_append, Array.size_extract]
  simp only [show (#[b0, b1, b2, b3, b4, b5, b6, b7] : Array UInt8).size = 8 from rfl]
  have hm : min off a.size = off := Nat.min_eq_left (by omega)
  have hlt0 : off < a.size := by omega
  have hlt1 : off + 1 < a.size := by omega
  have hlt2 : off + 2 < a.size := by omega
  have hlt3 : off + 3 < a.size := by omega
  have hlt4 : off + 4 < a.size := by omega
  have hlt5 : off + 5 < a.size := by omega
  have hlt6 : off + 6 < a.size := by omega
  have hlt7 : off + 7 < a.size := by omega
  by_cases h0 : j = off
  · subst j
    simp [hm, hlt0]
  · by_cases h1 : j = off + 1
    · subst j
      simp [ hm, hlt1, show ¬ off + 1 < off by omega]
    · by_cases h2 : j = off + 2
      · subst j
        simp [ hm, hlt2, show ¬ off + 2 < off by omega]
      · by_cases h3 : j = off + 3
        · subst j
          simp [ hm, hlt3, show ¬ off + 3 < off by omega]
        · by_cases h4 : j = off + 4
          · subst j
            simp [ hm, hlt4, show ¬ off + 4 < off by omega]
          · by_cases h5 : j = off + 5
            · subst j
              simp [ hm, hlt5, show ¬ off + 5 < off by omega]
            · by_cases h6 : j = off + 6
              · subst j
                simp [ hm, hlt6, show ¬ off + 6 < off by omega]
              · by_cases h7 : j = off + 7
                · subst j
                  simp [ hm, hlt7, show ¬ off + 7 < off by omega]
                · by_cases hbefore : j < off
                  · have hj8 : j < off + 8 := by omega
                    have hja : j < a.size := by omega
                    simp [ Ne.symm h0, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6, Ne.symm h7,
                      hbefore, hj8, hja, hm]
                  · have hafter : off + 8 ≤ j := by omega
                    have hj8 : ¬ j < off + 8 := by omega
                    have heq : off + 8 + (j - (off + 8)) = j := by omega
                    by_cases hja : j < a.size
                    · have htail : j - (off + 8) < a.size - (off + 8) := by omega
                      simp [ Ne.symm h0, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6, Ne.symm h7,
                        hj8, htail, hja, heq, hm]
                    · have htail : ¬ j - (off + 8) < a.size - (off + 8) := by omega
                      simp [ Ne.symm h0, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6, Ne.symm h7,
                        hj8, htail, hja, hm]


/-- The real eight-byte writer stores the specification's little-endian slice. -/
theorem store64_slice_run (h : Heap) (r : BRef) (a : Array UInt8) (off : Nat) (v : UInt64)
    (hg : Space.get h r = some a) (hro : Space.ro h r = false) (hfit : off + 8 ≤ a.size) :
    store64 (.ref r off) v h = .ok ((), Space.put h r
      (a.extract 0 off ++ (lengthBytes v).toArray ++ a.extract (off + 8) a.size)) := by
  have split := set_eight_slice a off hfit v.toUInt8 (v >>> 8).toUInt8 (v >>> 16).toUInt8
    (v >>> 24).toUInt8 (v >>> 32).toUInt8 (v >>> 40).toUInt8 (v >>> 48).toUInt8 (v >>> 56).toUInt8
  have encoding : storedWordAt a off v =
      a.extract 0 off ++ (lengthBytes v).toArray ++ a.extract (off + 8) a.size := by
    simpa [storedWordAt, List.range, List.range.loop, uint64_bytes] using split
  rw [store64_view_run h r a off v hg hro hfit, encoding]

/-- A valid scalar cell supports an exact writeback through the translated store64.
The post-heap is exactly Store's slice replacement, including both surrounding slices. -/
theorem store64_lengthCell (h : Heap) (p : BPtr) (old value : UInt64)
    (cell : LengthCell h p old) :
    ∃ after, C.run (store64 p value) h = .ok ((), after) ∧
      Store h p (lengthBytes value) after := by
  rcases cell with ⟨readable, writable⟩
  rcases readable with null | ⟨r, off, a, ptr, get, room, _⟩
  · simp at null
  · subst p
    rcases writable with null | ⟨r', off', a', ptr, get', ro, _⟩
    · simp at null
    · cases ptr
      have arrays : a' = a := Option.some.inj (get'.symm.trans get)
      subst a'
      refine ⟨_, store64_slice_run h r a off value get ro room, Or.inr ?_⟩
      refine ⟨r, off, a, rfl, get, ro, ?_, ?_⟩
      · simpa [uint64_bytes] using room
      · simp [uint64_bytes]

#print axioms load64_lengthCell
#print axioms store64_lengthCell

end Zlib.Uncompr.Proof.Cells
