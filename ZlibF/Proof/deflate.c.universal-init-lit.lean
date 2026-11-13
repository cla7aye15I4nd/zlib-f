import ZlibF.Proof.«deflate.c.universal-init»

/-!
# deflate.c: `deflateInit2_` with `memLevel ≥ 3` gives a symbol buffer of at least 512 entries

`init2_lit` follows `init2_inv` and reads `lit_bufsize = 2 ^ (memLevel + 6)` from the record the
success path builds (`resultState`): with `memLevel ≥ 3` it is at least 512, so the strategies
need no overlay hypothesis for that stream (`overlayAt_mid`).
-/

namespace Zlib.Deflate.Universal
open C Zlib.Deflate Zlib.Deflate.Spec ZlibF.Spec.Public Zlib.Deflate.Proofs.GeneralInit
open Zlib.Deflate.Proofs Zlib.Deflate.Proofs.DefaultInit
open ZlibF.Spec.Public.Proofs.DeflateInit (globals_trees)
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- **`deflateInit2_` with `memLevel ≥ 3`**: the invariant, and a symbol buffer of at least 512
entries. -/
theorem init2_lit {h after : Heap} {r : ZStreamRef} {z : ZStream} {version : BPtr}
    {level method wb mem strategy : Int32}
    (fresh : Fresh h) (uniq : Zlib.Deflate.Spec.Uniq h) (globals : LibraryGlobals h)
    (get : r.get h = some z) (allocators : DefaultOrNull z) (ver : VersionValue h version (some 49))
    (run : C.run (Zlib.Deflate.deflateInit2_ (some r) level method wb mem strategy version 112) h =
      .ok (Z_OK, after)) :
    ∃ ds z' d, DInv after r ds z' d ∧ (3 ≤ mem.toInt → 512 ≤ d.lit_bufsize.toNat) := by
  obtain ⟨rc, after', run', facts⟩ := init2_main level method wb mem strategy h r z version fresh uniq globals
    get allocators ver
  have same := run.symm.trans run'
  simp only [Except.ok.injEq, Prod.mk.injEq] at same
  obtain ⟨rcEq, afterEq⟩ := same
  subst afterEq
  subst rcEq
  let zp := preparedStream z
  let hp := r.put h zp
  have hshape := shape_put get zp
  have hfP : Fresh hp := hshape.fresh (by simp [hp]) fresh
  have huP : Uniq hp := hshape.uniq uniq
  have hzP : r.get hp = some zp := ZStreamRef.get_put_same get _
  have haP : DefAlloc zp := prepared_allocators allocators
  have entry : C.run (deflateInit2_ (some r) level method wb mem strategy version 112) h =
      (match ZlibF.Spec.Api.deflInit? level.toInt method.toInt wb.toInt mem.toInt strategy.toInt with
      | none => pure Z_STREAM_ERROR
      | some p => alloc (some r) (Int32.ofNat p.level) (wrapCode p.wrap) p.wbits p.memLevel method strategy) hp := by
    rw [C.run, GeneralInit.entry_run get ver, tail_params]
    rfl
  cases params : ZlibF.Spec.Api.deflInit? level.toInt method.toInt wb.toInt mem.toInt strategy.toInt with
  | none =>
    rw [params] at facts
    exact absurd facts.1 (by decide)
  | some p =>
    rw [params] at facts entry
    dsimp only at facts entry
    obtain ⟨m8, l9, w9, w15, m1, m9, mEq, s0, s4, sEq⟩ := params_ranges params
    have meth : method = 8 := Int32.toInt_inj.mp (by rw [m8]; rfl)
    subst meth
    by_cases first : h.allocOk h.nalloc = false
    · simp only [first, ite_true] at facts
      exact absurd facts.1 (by decide)
    · simp only [first, ite_false, Bool.false_eq_true] at facts
      by_cases all : (List.range 5).all (fun j => h.allocOk (h.nalloc + j)) = true
      · have allok : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true := by
          simpa only [List.all_eq_true, List.mem_range] using all
        let lev : Int32 := Int32.ofNat p.level
        have levInt : lev.toInt = p.level := Int32.toInt_ofNat_of_lt (by omega)
        have countP : ∀ j, j < 5 → hp.allocOk (hp.nalloc + j) = true := by
          intro j hj
          simpa [hp] using allok j hj
        have hw0 : 0 ≤ (wrapCode p.wrap).toInt := by cases p.wrap <;> decide
        obtain ⟨a1, a2, a3, qa, hsucc, good, bl, frequencies, -⟩ := allocate_success (wrapCode p.wrap)
          p.wbits p.memLevel hfP huP hzP haP (by simpa [hp] using globals_trees globals) countP lev strategy
          (by omega) (by omega) s0 s4 hw0 (by cases p.wrap <;> decide) w9 w15 m1 m9
        have eq := run.symm.trans (entry.trans hsucc)
        simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at eq
        subst eq
        refine ⟨_, _, _, success_dinv (wrapCode p.wrap) p.wbits p.memLevel good ?_ ?_ bl frequencies hw0 m1 m9,
          ?_⟩
        · exact ⟨by simpa [GeneralInit.resultStream, rkZ, GeneralInit.stateStream] using haP.1,
            by simpa [GeneralInit.resultStream, rkZ, GeneralInit.stateStream] using haP.2⟩
        · unfold LibraryGlobals at globals ⊢
          simpa [GeneralInit.successHeap, GeneralInit.readyHeap, GeneralInit.successfulBuffers, GeneralInit.publishedHeap, stateHeap, setW, setD, hp]
            using globals
        · intro three
          have mem3 : 3 ≤ p.memLevel := by omega
          have lit : (resultState (wrapCode p.wrap) p.wbits p.memLevel hp r lev strategy a1 a2 a3).lit_bufsize =
              UInt32.ofNat (2 ^ (p.memLevel + 6)) := rfl
          rw [lit]
          have lo : 2 ^ 9 ≤ 2 ^ (p.memLevel + 6) := Nat.pow_le_pow_right (by decide) (by omega)
          have hi : 2 ^ (p.memLevel + 6) ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) (by omega)
          have small : 2 ^ (p.memLevel + 6) < 2 ^ 32 := by
            have : (2 : Nat) ^ 15 < 2 ^ 32 := by decide
            omega
          have size : (2 : Nat) ^ 32 = 4294967296 := rfl
          rw [UInt32.toNat_ofNat_of_lt' (by unfold UInt32.size; omega)]
          have : (2 : Nat) ^ 9 = 512 := rfl
          omega
      · simp only [all, Bool.false_eq_true, ite_false] at facts
        exact absurd facts.2.1 (by decide)


end Zlib.Deflate.Universal
