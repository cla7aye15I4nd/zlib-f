import ZlibF.Proof.«inflate.c.meaning»
import ZlibF.Proof.«inflate.c.init-invariant»

/-!
# inflate.c: initialization establishes the format meaning

`meaning_init` (skeleton `inflate.c.format-trace`): after a successful
`inflateInit2_`, for every accepted windowBits (raw, zlib, gzip, automatic
detection, 0 and 8 to 15), the decoder stands at the start of the wrapper
header with nothing read and nothing held. The state comes from the
registered `Goal.inflateInit2_` result; the invariant from
`inflateInit2_invariant_of`.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Every configured layer has a complete header that the configuration
accepts: none for raw data, `78 01`-like `08 1D` (window 256, no dictionary)
for zlib, a minimal gzip header otherwise. -/
theorem wrapHeader_exists {wrap : Api.Wrap} {bits : Nat} (dict : List UInt8)
    (range : bits = 0 ∨ (8 ≤ bits ∧ bits ≤ 15)) :
    ∃ more bodyDict, WrapHeader wrap bits dict ([] ++ more) bodyDict ∧
      (more ≠ [] ∨ wrap = .raw) := by
  have zlibHeader : ∃ window, ZlibHeader bits dict [8, 29] window := by
    refine ⟨if bits = 0 then Zlib.windowSize 8 else 2 ^ bits, 8, 29, by decide, ?_, rfl,
      Or.inl ⟨by decide, rfl⟩⟩
    rcases range with zero | ⟨low, _⟩
    · exact Or.inl zero
    · exact Or.inr ⟨8, rfl, by simpa using low⟩
  have gzipHeader : GzipHeader (Gzip.header 0 [0, 0, 0, 0] 0 0 [] [] []) :=
    ⟨0, [0, 0, 0, 0], 0, 0, [], [], [], by decide, rfl, by decide, by simp, by simp,
      by simp⟩
  obtain ⟨window, zlibOk⟩ := zlibHeader
  cases wrap with
  | raw => exact ⟨[], _, ⟨rfl, rfl⟩, Or.inr rfl⟩
  | zlib => exact ⟨[8, 29], [], ⟨window, zlibOk, by simp⟩, Or.inl (by simp)⟩
  | gzip =>
    exact ⟨Gzip.header 0 [0, 0, 0, 0] 0 0 [] [] [], [], ⟨gzipHeader, rfl⟩,
      Or.inl (by simp [Gzip.header])⟩
  | auto => exact ⟨[8, 29], [], Or.inl ⟨window, zlibOk, by simp⟩, Or.inl (by simp)⟩

/-- `int inflateInit2_(z_streamp strm, int windowBits, const char *version, int stream_size)`:
a `Z_OK` return gives the format meaning of the empty epoch, with no
dictionary request pending. -/
theorem meaning_init {h after : Heap} {r : ZStreamRef} {version : BPtr} {wb : Int32}
    (domain : InitDomain h r version)
    (run : C.run (inflateInit2_ (some r) wb version 112) h = .ok (Z_OK, after)) :
    ParseMeaning wb r after {} false := by
  obtain ⟨fresh, uniq, globals, value, z0, get, null, _⟩ := domain
  obtain ⟨_, _, inv⟩ := inflateInit2_invariant_of fresh uniq globals get null value run
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
  cases params : Api.inflWbits wb.toInt with
  | none =>
    rw [params] at outcome
    exact absurd outcome.1 (by decide)
  | some selected =>
    obtain ⟨wrap, bits⟩ := selected
    rw [params] at outcome
    obtain ⟨_, z, s, good, _, _, mode, _, wbitsEq, reqbitsEq, wrapEq, reqwrapEq, _, _, _,
      hold, bitsEq, _, head, _⟩ := outcome
    have range := inflWbits_bits params
    refine ⟨wrap, bits, h.nextBlk, z, s, params, inv.of_good good, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, reqwrapEq, head, reqbitsEq, fun _ => wbitsEq⟩
      rw [wrapEq]
      cases wrap <;> rfl
    · intro error
      exact absurd error (by decide)
    · intro _ bad
      rw [mode] at bad
      exact absurd bad (by decide)
    · intro _ memory
      rw [mode] at memory
      exact absurd memory (by decide)
    · intro _ _ _ _
      refine ⟨[], [], .header [], by simp [bytesToBits], ⟨by simp [bitsEq], by simp [hold]⟩,
        ⟨by simp [bytesToBits], wrapHeader_exists _ range⟩, ?_, ?_, rfl, ?_⟩
      · show HEAD ≤ s.mode ∧ s.mode ≤ DICTID
        rw [mode]
        decide
      · refine ⟨fun _ => mode, fun _ => ⟨rfl, by simp [bitsEq]⟩, ?_, ?_, ?_⟩
        · intro dictid
          rw [mode] at dictid
          exact absurd dictid (by decide)
        · intro flags
          rw [mode] at flags
          exact absurd flags (by decide)
        · intro later
          rw [mode] at later
          exact absurd later (by decide)
      · simp

#print axioms wrapHeader_exists
#print axioms meaning_init

end Zlib.Inflate.Proofs
