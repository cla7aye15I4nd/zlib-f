import ZlibF.Zlib.«trees.c»

/-! A rejected proposed uniform extra-bit residual bound. The actual
compressor skips its base subtraction and send_bits call at width zero.
This is a counterexample to an auxiliary proof claim, not to zlib. -/

open Zlib.Trees

/-- Length 258 uses internal lc 255 and length code 28, with no extra bits.
The raw table base is zero; an unconditional residual-fit claim is false. -/
theorem deflate_length_residual_counterexample :
    length_code_tab[255]!.toNat = 28 ∧
    extra_lbits_tab[28]!.toInt = 0 ∧ base_length_tab[28]!.toInt = 0 ∧
    ¬ (255 - base_length_tab[28]!.toInt.toNat < 2 ^ extra_lbits_tab[28]!.toInt.toNat) := by
  decide +kernel
