import ZlibF.Spec.Public.GzControl
import ZlibF.Proof.«gzlib.c.base»

namespace ZlibF.Spec.Public.GzErrorProof
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzlib.Spec Zlib.Gzlib.Proofs

private def IsLit (r : BPtr) (t : String) : Prop :=
  ∃ i, r = .ref (.str i) 0 ∧ strTable[i]? = some t

private theorem gzerror_null_file (p : BPtr) (h : Heap) :
    Zlib.Gzlib.gzerror none p h = .ok (.null, h) := rfl

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
  cases r <;> simp [Space.get, Space.put, Space.ro]

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

/-- `void store32(int *p, int v)` writes the four little-endian bytes into an
existing writable array and changes no other heap object. -/
theorem store32_run {h : Heap} {r : BRef} {a : Array UInt8} {off : Nat}
    (hg : Space.get h r = some a) (hro : Space.ro h r = false)
    (hfit : off + 4 ≤ a.size) (v : Int32) :
    store32 (.ref r off) v h = .ok ((), Space.put h r
      ((((a.set! off v.toUInt32.toUInt8).set! (off + 1) (v.toUInt32 >>> 8).toUInt8).set! (off + 2) (v.toUInt32 >>> 16).toUInt8).set! (off + 3) (v.toUInt32 >>> 24).toUInt8)) := by
  have add0 := Ptr.add_nat_ok (h := h) (r := r) (a := a) (off := off) (n := 0) hg (by omega)
  have st0 := Ptr.store_ok (h := h) (r := r) (a := a) (off := off) (v := v.toUInt32.toUInt8) hg hro (by omega)
  let a0 := a.set! off v.toUInt32.toUInt8
  have hg0 := byte_get_put hg hro a0
  have hr0 : Space.ro (Space.put h r a0) r = false := by rw [byte_ro_put, hro]
  have add1 := Ptr.add_nat_ok (h := Space.put h r a0) (r := r) (a := a0) (off := off) (n := 1) hg0 (by simp [a0]; omega)
  have st1 := Ptr.store_ok (h := Space.put h r a0) (r := r) (a := a0) (off := off + 1)
    (v := (v.toUInt32 >>> 8).toUInt8) hg0 hr0 (by simp [a0]; omega)
  let a1 := a0.set! (off + 1) (v.toUInt32 >>> 8).toUInt8
  have hg1 : Space.get (Space.put (Space.put h r a0) r a1) r = some a1 := byte_get_put hg0 hr0 a1
  have hr1 : Space.ro (Space.put (Space.put h r a0) r a1) r = false := by rw [byte_ro_put, byte_ro_put, hro]
  have add2 := Ptr.add_nat_ok (h := Space.put (Space.put h r a0) r a1) (r := r) (a := a1) (off := off) (n := 2) hg1 (by simp [a1, a0]; omega)
  have st2 := Ptr.store_ok (h := Space.put (Space.put h r a0) r a1) (r := r) (a := a1) (off := off + 2)
    (v := (v.toUInt32 >>> 16).toUInt8) hg1 hr1 (by simp [a1, a0]; omega)
  let a2 := a1.set! (off + 2) (v.toUInt32 >>> 16).toUInt8
  have hg2 : Space.get (Space.put (Space.put (Space.put h r a0) r a1) r a2) r = some a2 := byte_get_put hg1 hr1 a2
  have hr2 : Space.ro (Space.put (Space.put (Space.put h r a0) r a1) r a2) r = false := by rw [byte_ro_put, byte_ro_put, byte_ro_put, hro]
  have add3 := Ptr.add_nat_ok (h := Space.put (Space.put (Space.put h r a0) r a1) r a2) (r := r) (a := a2) (off := off) (n := 3) hg2 (by simp [a2, a1, a0]; omega)
  have st3 := Ptr.store_ok (h := Space.put (Space.put (Space.put h r a0) r a1) r a2) (r := r) (a := a2) (off := off + 3)
    (v := (v.toUInt32 >>> 24).toUInt8) hg2 hr2 (by simp [a2, a1, a0]; omega)
  unfold OkOn at add0 add1 add2 add3
  have e0 : (Ptr.ref r off).add (0 : Int) h = .ok (.ref r off, h) := by simpa using add0
  have e1 : (Ptr.ref r off).add (1 : Int) (Space.put h r a0) =
      .ok (.ref r (off + 1), Space.put h r a0) := by simpa using add1
  have e2 : (Ptr.ref r off).add (2 : Int) (Space.put (Space.put h r a0) r a1) =
      .ok (.ref r (off + 2), Space.put (Space.put h r a0) r a1) := by simpa using add2
  have e3 : (Ptr.ref r off).add (3 : Int) (Space.put (Space.put (Space.put h r a0) r a1) r a2) =
      .ok (.ref r (off + 3), Space.put (Space.put (Space.put h r a0) r a1) r a2) := by simpa using add3
  simp only [a0, a1, a2] at e1 e2 e3 st1 st2 st3
  unfold store32
  simp only [bind_app, e0, st0, e1, st1, e2, st2, e3, st3, pure_app]
  simp only [a0, a1, a2] at *
  rw [byte_put_put hg hro, byte_put_put hg hro, byte_put_put hg hro]

/-- Four successive byte writes equal replacement of the corresponding array slice. -/
theorem set_four_slice (a : Array UInt8) (off : Nat) (hfit : off + 4 ≤ a.size)
    (b0 b1 b2 b3 : UInt8) :
    (((a.set! off b0).set! (off + 1) b1).set! (off + 2) b2).set! (off + 3) b3 =
      a.extract 0 off ++ #[b0, b1, b2, b3] ++ a.extract (off + 4) a.size := by
  apply Array.ext_getElem?
  intro j
  simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds,
    Array.getElem?_append, Array.size_append, Array.size_extract]
  simp only [show (#[b0, b1, b2, b3] : Array UInt8).size = 4 from rfl]
  have hm : min off a.size = off := Nat.min_eq_left (by omega)
  have hlt0 : off < a.size := by omega
  have hlt1 : off + 1 < a.size := by omega
  have hlt2 : off + 2 < a.size := by omega
  have hlt3 : off + 3 < a.size := by omega
  by_cases h0 : j = off
  · subst j
    simp [Array.getElem?_extract, hm, hlt0, hlt1, hlt2, hlt3]
  · by_cases h1 : j = off + 1
    · subst j
      simp [Array.getElem?_extract, hm, hlt0, hlt1, hlt2, hlt3,
        show ¬ off + 1 < off from by omega]
    · by_cases h2 : j = off + 2
      · subst j
        simp [Array.getElem?_extract, hm, hlt0, hlt1, hlt2, hlt3,
          show ¬ off + 2 < off from by omega]
      · by_cases h3 : j = off + 3
        · subst j
          simp [Array.getElem?_extract, hm, hlt0, hlt1, hlt2, hlt3,
            show ¬ off + 3 < off from by omega]
        · by_cases hbefore : j < off
          · have hj4 : j < off + 4 := by omega
            have hja : j < a.size := by omega
            simp [h0, h1, h2, h3, Ne.symm h0, Ne.symm h1, Ne.symm h2, Ne.symm h3,
              hbefore, hj4, hja, Array.getElem?_extract, hm, Array.getElem?_eq_getElem]
          · have hafter : off + 4 ≤ j := by omega
            have hj4 : ¬ j < off + 4 := by omega
            have heq : off + 4 + (j - (off + 4)) = j := by omega
            by_cases hja : j < a.size
            · have htail : j - (off + 4) < a.size - (off + 4) := by omega
              simp [h0, h1, h2, h3, Ne.symm h0, Ne.symm h1, Ne.symm h2, Ne.symm h3,
                hbefore, hj4, htail, hja, heq, Array.getElem?_extract, hm]
            · have htail : ¬ j - (off + 4) < a.size - (off + 4) := by omega
              simp [h0, h1, h2, h3, Ne.symm h0, Ne.symm h1, Ne.symm h2, Ne.symm h3,
                hbefore, hj4, htail, hja, Array.getElem?_extract, hm, Array.getElem?_eq_none]

/-- The little-endian four-byte store replaces exactly its requested slice. -/
theorem store32_slice_run {h : Heap} {r : BRef} {a : Array UInt8} {off : Nat}
    (hg : Space.get h r = some a) (hro : Space.ro h r = false)
    (hfit : off + 4 ≤ a.size) (v : Int32) :
    store32 (.ref r off) v h = .ok ((), Space.put h r
      (a.extract 0 off ++ #[v.toUInt32.toUInt8, (v.toUInt32 >>> 8).toUInt8,
        (v.toUInt32 >>> 16).toUInt8, (v.toUInt32 >>> 24).toUInt8] ++
        a.extract (off + 4) a.size)) := by
  rw [store32_run hg hro hfit v, set_four_slice a off hfit]

/-- The byte-shift expressions implement the mathematical little-endian encoding. -/
theorem int32_bytes (v : Int32) :
    (List.range 4).map (fun j => UInt8.ofNat (v.toUInt32.toNat / 256 ^ j % 256)) =
      [v.toUInt32.toUInt8, (v.toUInt32 >>> 8).toUInt8,
        (v.toUInt32 >>> 16).toUInt8, (v.toUInt32 >>> 24).toUInt8] := by
  have hr : List.range 4 = [0, 1, 2, 3] := by decide
  rw [hr]
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true,
    Nat.pow_zero, Nat.reducePow, Nat.div_one]
  repeat' constructor
  all_goals apply UInt8.toNat_inj.mp
  all_goals simp [UInt8.toNat_ofNat', UInt32.toNat_toUInt8, UInt32.toNat_shiftRight,
    Nat.shiftRight_eq_div_pow]

/-- The return-text part of `gzerror` after the optional error-code write. -/
def errorMessage (s : GzState) : M BPtr := do
  if s.err == Z_MEM_ERROR then Zlib.GzFs.strLit "out of memory"
  else if s.msg == .null then Zlib.GzFs.strLit ""
  else pure s.msg

/-- A valid-mode `gzerror` reads the state once, performs the optional write,
and returns the corresponding message. -/
theorem gzerror_split {h : Heap} {i : Nat} {s : GzState}
    (hs : h.gzstates i = some s) (hm : s.mode = GZ_READ ∨ s.mode = GZ_WRITE) (p : BPtr) :
    Zlib.Gzlib.gzerror (hnd i) p h =
      (do
        if p != (Ptr.null : BPtr) then store32 p s.err
        errorMessage s) h := by
  unfold Zlib.Gzlib.gzerror errorMessage
  rcases hm with hm | hm <;> gsimp [hs, hm, GZ_READ, GZ_WRITE]

/-- Returning an error message never changes the heap. Literal results identify
an actual static source string; otherwise the original message pointer is returned. -/
theorem errorMessage_run (h : Heap) (s : GzState) :
    ∃ p, errorMessage s h = .ok (p, h) ∧
      (if s.err = Z_MEM_ERROR then IsLit p "out of memory"
       else if s.msg = .null then IsLit p "" else p = s.msg) := by
  have lit : ∀ t : String, t ∈ strTable → ∃ p, Zlib.GzFs.strLit t h = .ok (p, h) ∧ IsLit p t := by
    intro t ht
    obtain ⟨i, hr, hi⟩ := strLitRef_of_mem (h := h) ht
    exact ⟨_, hr, i, rfl, hi⟩
  by_cases he : s.err = Z_MEM_ERROR
  · obtain ⟨p, hp, hl⟩ := lit "out of memory" (by decide +kernel)
    exact ⟨p, by simpa [errorMessage, he] using hp, by simpa [he] using hl⟩
  · by_cases hn : s.msg = .null
    · obtain ⟨p, hp, hl⟩ := lit "" (by decide +kernel)
      exact ⟨p, by simpa [errorMessage, he, hn] using hp, by simpa [he, hn] using hl⟩
    · exact ⟨s.msg, by simp [errorMessage, he, hn], by simp [he, hn]⟩


private theorem lit_static (h : Heap) (p : BPtr) (s : String) (hl : IsLit p s) :
    StaticString h p s := by
  obtain ⟨i, rfl, hi⟩ := hl
  exact ⟨i, rfl, by simp [hi, strBytes], rfl⟩

/-- `const char *gzerror(gzFile file, int *errnum)` returns the specified
message and writes the optional error number without accessing unrelated memory. -/
theorem gzerror : Goal.gzerror := by
  constructor
  · intro h p
    exact gzerror_null_file p h
  · intro h i s p hv hout
    have hs := hv.1
    have hm := hv.2.1
    by_cases hp : p = .null
    · subst p
      obtain ⟨q, hmsg, hdesc⟩ := errorMessage_run h s
      refine ⟨q, h, ?_, Or.inl ⟨rfl, rfl⟩, ?_⟩
      · change Zlib.Gzlib.gzerror (hnd i) .null h = .ok (q, h)
        rw [gzerror_split hs hm]
        simpa using hmsg
      · by_cases he : s.err = Z_MEM_ERROR
        · simp only [he, if_true] at hdesc ⊢
          exact lit_static h q _ hdesc
        · simp only [he, if_false] at hdesc ⊢
          by_cases hn : s.msg = .null
          · simp only [hn, if_true] at hdesc ⊢
            exact lit_static h q _ hdesc
          · simp only [hn, if_false] at hdesc ⊢
            exact hdesc
    · have hbuf := hout hp
      rcases hbuf with hn | ⟨_, hw, _⟩
      · omega
      · have hw' := hw rfl
        rcases hw' with ⟨hnull, _⟩ | ⟨r, off, a, hp', hg, hro, hfit⟩
        · exact (hp hnull).elim
        · subst p
          let arr := a.extract 0 off ++ #[s.err.toUInt32.toUInt8, (s.err.toUInt32 >>> 8).toUInt8,
            (s.err.toUInt32 >>> 16).toUInt8, (s.err.toUInt32 >>> 24).toUInt8] ++ a.extract (off + 4) a.size
          let after := Space.put h r arr
          have hstore : store32 (.ref r off) s.err h = .ok ((), after) :=
            store32_slice_run hg hro hfit s.err
          obtain ⟨q, hmsg, hdesc⟩ := errorMessage_run after s
          refine ⟨q, after, ?_, ?_, ?_⟩
          · change Zlib.Gzlib.gzerror (hnd i) (.ref r off) h = .ok (q, after)
            rw [gzerror_split hs hm]
            simp [bind_app, hstore, hmsg]
          · right
            refine ⟨r, off, a, rfl, hg, hro, ?_, ?_⟩
            · simpa [intBytes] using hfit
            · simp [intBytes, int32_bytes, after, arr]
          · by_cases he : s.err = Z_MEM_ERROR
            · simp only [he, if_true] at hdesc ⊢
              exact lit_static after q _ hdesc
            · simp only [he, if_false] at hdesc ⊢
              by_cases hn : s.msg = .null
              · simp only [hn, if_true] at hdesc ⊢
                exact lit_static after q _ hdesc
              · simp only [hn, if_false] at hdesc ⊢
                exact hdesc


#print axioms gzerror
end ZlibF.Spec.Public.GzErrorProof
