import ZlibF.Spec.Api.Inflate
import ZlibF.Proof.Format.Wrapper
import ZlibF.Proof.«inffast.c.sig»

/-! Bit-prefix comparison for byte streams. No heap or execution hypothesis is used. -/

namespace ZlibF.Spec.Api.Proofs
open ZlibF.Spec

theorem bytesToBits_prefix {a b : List UInt8} (h : a <+: b) :
    bytesToBits a <+: bytesToBits b := by
  obtain ⟨tail, rfl⟩ := h
  exact ⟨bytesToBits tail, by simp [bytesToBits, List.flatMap_append]⟩

theorem bit_compatible_of_byte_compatible {pfx : List Bool} {input stream : List UInt8}
    (hp : pfx <+: bytesToBits input) (hc : input <+: stream ∨ stream <+: input) :
    Layer.BitCompatible pfx stream := by
  rcases hc with hc | hc
  · exact Or.inl (hp.trans (bytesToBits_prefix hc))
  · have hs := bytesToBits_prefix hc
    by_cases hl : pfx.length ≤ (bytesToBits stream).length
    · exact Or.inl (List.prefix_of_prefix_length_le hp hs hl)
    · exact Or.inr (List.prefix_of_prefix_length_le hs hp (by omega))

private theorem read_byte_bits (byte : UInt8) (tail : List Bool) :
    readBits 8 (byteBits byte ++ tail) = some (byte.toNat, tail) := by
  change readBits 8 (Zlib.Inffast.Proofs.bitsOfNat byte.toNat 8 ++ tail) = _
  simpa only [show 2 ^ 8 = (256 : Nat) from rfl, Nat.mod_eq_of_lt byte.toNat_lt,
    Nat.sub_self, Zlib.Inffast.Proofs.bitsOfNat_zero, List.nil_append] using
    Zlib.Inffast.Proofs.readBits_bitsOfNat 8 8 byte.toNat tail (by omega)

/-- Whole-byte prefix comparison is reflected by the bit encoding. -/
theorem bytesToBits_prefix_reflect {a b : List UInt8}
    (h : bytesToBits a <+: bytesToBits b) : a <+: b := by
  induction a generalizing b with
  | nil => exact List.nil_prefix
  | cons byte a ih =>
    cases b with
    | nil =>
      have hl := h.length_le
      simp [ZlibF.Spec.Proofs.bytesToBits_len] at hl
    | cons other b =>
      obtain ⟨tail, heq⟩ := h
      have hr := congrArg (readBits 8) heq
      change readBits 8 ((byteBits byte ++ bytesToBits a) ++ tail) =
        readBits 8 (byteBits other ++ bytesToBits b) at hr
      rw [List.append_assoc, read_byte_bits, read_byte_bits] at hr
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      have hbyte : byte = other := UInt8.toNat_inj.mp hr.1
      subst other
      obtain ⟨suffix, hs⟩ := ih ⟨tail, hr.2⟩
      exact ⟨suffix, by simp only [List.cons_append, hs]⟩


end ZlibF.Spec.Api.Proofs
