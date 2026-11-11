import ZlibF.Proof.«inflate.c.invariant»
import ZlibF.Proof.«public-inflate-init2»

/-!
# inflate.c: every successful initialization establishes the general invariant

The premises are exactly those of `StreamReachable.inflateInit`. The
returned state comes from the registered `Goal.inflateInit2_` result, so
this covers raw, zlib, gzip and automatic detection, every window width, and
windowBits 0. No object-size premise is used.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- `int inflateInit2_(z_streamp strm, int windowBits, const char *version, int stream_size)`.
A `Z_OK` return establishes `InflateInv` on the returned heap. -/
theorem inflateInit2_invariant_of {h after : Heap} {r : ZStreamRef} {z0 : ZStream}
    {version : BPtr} {wb : Int32}
    (fresh : Fresh h) (uniq : Uniq h) (globals : LibraryGlobals h) (get : r.get h = some z0)
    (null : DefaultOrNull z0) (value : VersionValue h version (some 49))
    (run : C.run (inflateInit2_ (some r) wb version 112) h = .ok (Z_OK, after)) :
    ∃ z s, InflateInv after r h.nextBlk z s := by
  obtain ⟨rc, after', run', _, outcome⟩ :=
    (ZlibF.Spec.Public.Proofs.InflateInit.inflate_init2_public wb).2.2
      h r z0 version fresh uniq globals get null value
  have same := Except.ok.inj (run.symm.trans run')
  cases same
  have allocation : h.allocOk h.nalloc = true := by
    cases failed : h.allocOk h.nalloc
    · rw [failed] at outcome
      simp only [↓reduceIte] at outcome
      exact absurd outcome.1 (by decide)
    · rfl
  rw [allocation] at outcome
  simp only [Bool.true_eq_false, ↓reduceIte] at outcome
  cases params : ZlibF.Spec.Api.inflWbits wb.toInt with
  | none =>
    rw [params] at outcome
    exact absurd outcome.1 (by decide)
  | some selected =>
    obtain ⟨wrap, bits⟩ := selected
    rw [params] at outcome
    obtain ⟨_, initial⟩ := outcome
    have initialCopy := initial
    obtain ⟨z, s, good, zalloc, zfree, head, window, wbitsEq, reqbitsEq, wrapEq, reqwrapEq,
      _, _, _, _, _, _, header, _, _, _, frame, _⟩ := initialCopy
    obtain ⟨nonnull, read⟩ := ZlibF.Spec.Public.Proofs.InflateInit.version_value_read value
    have parameters := ZlibF.Spec.Public.Proofs.InflateInit.params_equiv wb
    rw [params] at parameters
    change reset2Params wb =
      some (ZlibF.Spec.Public.Proofs.InflateInit.publicWrap wrap, Int32.ofInt bits) at parameters
    have actual := inflateInit2_success get fresh allocation null.1 null.2 nonnull read parameters
    have heapEq : after = initOkHeap h r z0
        (ZlibF.Spec.Public.Proofs.InflateInit.publicWrap wrap) (Int32.ofInt bits) := by
      have equality := run.symm.trans actual
      cases equality
      rfl
    have stateEq : s = resetKeepState h.nextBlk (resetPre (reset2Pre
        (ZlibF.Spec.Public.Proofs.InflateInit.publicWrap wrap) (Int32.ofInt bits)
        (initState r))) := by
      apply Option.some.inj
      rw [← good.live.hs, heapEq]
      simp [initOkHeap]
    have sane : s.sane = 1 := by rw [stateEq]; rfl
    have flags : s.flags = -1 := by rw [stateEq]; rfl
    have origin : CopyTableOrigin h.nextBlk s := by
      rw [stateEq]
      simp [CopyTableOrigin, resetKeepState, resetPre, reset2Pre, initState]
    have range : bits = 0 ∨ (8 ≤ bits ∧ bits ≤ 15) := by
      have key : ∀ n : Nat, n < 16 → badBits (Int32.ofInt (n : Int)) = false →
          n = 0 ∨ (8 ≤ n ∧ n ≤ 15) := by decide
      have upper := good.inv.win.wbits
      exact key bits (by omega) (reset2Params_bits parameters)
    have wrapValue : WrapValue s.wrap := by
      unfold WrapValue
      rw [wrapEq]
      cases wrap <;> decide
    refine ⟨z, s, good, ⟨zalloc, zfree⟩, dataTableInvariant_head head, ?_, ?_, ?_,
      inflate_initial_hold initial good, ?_, good.live.mode, ?_, origin, ?_⟩
    · refine ⟨sane, ?_, ?_, ?_, ?_⟩
      all_goals intro selected; rw [head] at selected; contradiction
    · intro active
      rw [head] at active
      contradiction
    · intro active
      rw [head] at active
      contradiction
    · refine ⟨wrapValue, by rw [reqwrapEq]; exact wrapValue, ?_,
        Or.inl (UInt32.toNat_inj.mp (reqbitsEq.trans wbitsEq.symm)), ?_, ?_, ?_,
        Or.inr (by rw [reqwrapEq])⟩
      · rcases range with zero | ⟨low, high⟩
        · exact Or.inr ⟨UInt32.toNat_inj.mp (by rw [wbitsEq, zero]; rfl), window, Or.inl head⟩
        · exact Or.inl ⟨by omega, by omega⟩
      · intro attached
        exact absurd header attached
      · intro zero
        rw [wrapEq] at zero
        cases wrap with
        | raw =>
          have := inflWbits_raw params
          intro widthZero
          rw [widthZero] at wbitsEq
          simp at wbitsEq
          omega
        | zlib => exact absurd zero (by decide)
        | gzip => exact absurd zero (by decide)
        | auto => exact absurd zero (by decide)
      · intro zero
        rw [reqwrapEq, wrapEq] at zero
        cases wrap with
        | raw =>
          have := inflWbits_raw params
          intro widthZero
          rw [widthZero] at reqbitsEq
          simp at reqbitsEq
          omega
        | zlib => exact absurd zero (by decide)
        | gzip => exact absurd zero (by decide)
        | auto => exact absurd zero (by decide)
    · exact ⟨Or.inl head, Or.inl flags, fun unread => absurd flags unread,
        fun low _ => absurd low (by rw [head]; decide)⟩
    · change after.static = _
      rw [← frame.1]
      exact globals

#print axioms inflateInit2_invariant_of

end Zlib.Inflate.Proofs
