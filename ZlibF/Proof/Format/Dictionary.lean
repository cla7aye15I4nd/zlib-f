import ZlibF.Math.LZ77History
import ZlibF.Spec.Api.Basic

namespace ZlibF.Spec.Proofs
open ZlibF.Spec ZlibF.Math.LZ77History

/-- A match whose distance fits a retained suffix copies the same bytes if older dictionary
bytes are available. -/
private theorem copy_suffix {small large history : List UInt8} {dist n : Nat}
    (hs : small <:+ large) (hp : 0 < dist) (hd : dist ≤ (small ++ history).length) :
    copyBack large dist n history = copyBack small dist n history := by
  have he := retained_history_agrees large [] history small dist n (by simpa using hs) hp
    (by simpa [List.length_append] using hd)
  simpa using he

/-- Decoding symbols is stable when extra older dictionary bytes are prepended. -/
theorem symbols_dictionary_suffix {L D : List Nat} {small large history output : List UInt8}
    {input rest : List Bool} (hs : small <:+ large)
    (h : Symbols L D small history input rest output) : Symbols L D large history input rest output := by
  induction h with
  | eob hd => exact .eob hd
  | lit hd hlt _ ih => exact .lit hd hlt ih
  | @copy hist inp r1 r2 r3 r4 rest sym ds xl xd output hd h1 h2 hr1 hd2 h3 hr2 hb hcopy ih =>
    have hbase : 0 < distBases.getD ds 0 :=
      (by decide : ∀ i, i < 30 → 0 < distBases.getD i 0) ds (by omega)
    have hpos : 0 < distBases.getD ds 0 + xd := by omega
    have hfit : distBases.getD ds 0 + xd ≤ (small ++ hist).length := by omega
    have hsame := copy_suffix hs hpos hfit (n := lengthBases.getD (sym - 257) 0 + xl)
    have hlarge : xd + distBases.getD ds 0 ≤ (large ++ hist).length := by
      obtain ⟨older, he⟩ := hs
      rw [← he]
      simp only [List.length_append] at *
      omega
    apply Symbols.copy hd h1 h2 hr1 hd2 h3 hr2 hlarge
    rw [hsame]
    exact ih

/-- A block keeps its decoding when the dictionary grows by an older prefix. -/
theorem body_dictionary_suffix {small large history output : List UInt8} {bt : Nat}
    {input rest : List Bool} (hs : small <:+ large)
    (h : Body small bt history input rest output) : Body large bt history input rest output := by
  cases h with
  | stored h1 h2 h3 h4 => exact .stored h1 h2 h3 h4
  | fixed h => exact .fixed (symbols_dictionary_suffix hs h)
  | dynamic h1 h2 h3 hc h4 ha hl heob hL hD h =>
    exact .dynamic h1 h2 h3 hc h4 ha hl heob hL hD (symbols_dictionary_suffix hs h)

/-- A complete sequence of blocks has the same output with a larger dictionary. -/
theorem blocks_dictionary_suffix {small large history output : List UInt8} {input rest : List Bool}
    (hs : small <:+ large) (h : Blocks small history input rest output) :
    Blocks large history input rest output := by
  induction h with
  | last h1 h2 hb => exact .last h1 h2 (body_dictionary_suffix hs hb)
  | more h1 h2 hb _ ih => exact .more h1 h2 (body_dictionary_suffix hs hb) ih

/-- A complete raw deflate stream remains valid after prepending older dictionary bytes. -/
theorem deflate_dictionary_suffix {small large stream output : List UInt8}
    (hs : small <:+ large) (h : Deflate.Decodes small stream output) :
    Deflate.Decodes large stream output := by
  obtain ⟨rest, hb, hr⟩ := h
  exact ⟨rest, blocks_dictionary_suffix hs hb, hr⟩

/-- A stream valid for a smaller raw window is valid for the 32 KiB raw window. -/
theorem raw_full_window {dict stream output : List UInt8} {bits : Nat} (hb : bits ≤ 15)
    (h : Deflate.Decodes (dict.drop (dict.length - 2 ^ bits)) stream output) :
    ZlibF.Spec.Api.Layer.Decodes .raw 15 dict stream output := by
  have hpow : 2 ^ bits ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) hb
  have hi : dict.length - 2 ^ 15 ≤ dict.length - 2 ^ bits := by omega
  have hs := List.drop_suffix ((dict.length - 2 ^ bits) - (dict.length - 2 ^ 15))
    (dict.drop (dict.length - 2 ^ 15))
  have hs' : dict.drop (dict.length - 2 ^ bits) <:+ dict.drop (dict.length - 2 ^ 15) := by
    simpa only [List.drop_drop, Nat.add_sub_of_le hi] using hs
  exact deflate_dictionary_suffix hs' h

#print axioms deflate_dictionary_suffix
#print axioms raw_full_window
end ZlibF.Spec.Proofs
