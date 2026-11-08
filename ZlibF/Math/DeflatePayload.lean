import ZlibF.Proof.«trees.c.tally»
import ZlibF.Proof.«trees.c.runs»

/-! # The payload bit sequence of compress_block

This is the writer model. Its relation to the independent format grammar
is separate. Symbol-buffer distances use two little-endian bytes.
-/

namespace Zlib.Trees.Proofs.Out
open C Zlib.Trees

/-- The length-code table lookup for an internal length minus three. -/
def lcodeN (lc : Nat) : Nat := length_code_tab[lc]!.toNat

def payloadSymBits (lt dt : Nat → UInt16 × UInt16) (sym : Nat × Nat) : List Bool :=
  if sym.1 = 0 then codeBits lt sym.2 else
    let lc := lcodeN sym.2
    let dc := dcodeN (sym.1 - 1)
    codeBits lt (lc + 257) ++
      natBits (sym.2 - base_length_tab[lc]!.toInt.toNat) extra_lbits_tab[lc]!.toInt.toNat ++
      codeBits dt dc ++
      natBits (sym.1 - 1 - base_dist_tab[dc]!.toInt.toNat) extra_dbits_tab[dc]!.toInt.toNat

/-- One actual three-byte buffered symbol. -/
def payloadSymAt (buf : Array UInt8) (offset i : Nat) : Nat × Nat :=
  (buf[offset + 3 * i]!.toNat + 256 * buf[offset + 3 * i + 1]!.toNat,
    buf[offset + 3 * i + 2]!.toNat)

def payloadPrefixBits (lt dt : Nat → UInt16 × UInt16) (buf : Array UInt8) (offset n : Nat) : List Bool :=
  ((List.range n).map (payloadSymAt buf offset)).flatMap (payloadSymBits lt dt)

def payloadBits (lt dt : Nat → UInt16 × UInt16) (buf : Array UInt8) (offset n : Nat) : List Bool :=
  payloadPrefixBits lt dt buf offset n ++ codeBits lt 256

theorem payloadPrefixBits_succ (lt dt : Nat → UInt16 × UInt16) (buf : Array UInt8) (offset n : Nat) :
    payloadPrefixBits lt dt buf offset (n + 1) =
      payloadPrefixBits lt dt buf offset n ++ payloadSymBits lt dt (payloadSymAt buf offset n) := by
  simp [payloadPrefixBits, List.range_succ, List.flatMap_append]

theorem payloadPrefixBits_mono (lt dt : Nat → UInt16 × UInt16) (buf : Array UInt8) (offset : Nat)
    {i j : Nat} (hij : i ≤ j) :
    (payloadPrefixBits lt dt buf offset i).length ≤ (payloadPrefixBits lt dt buf offset j).length := by
  induction j with
  | zero => have hi : i = 0 := by omega
            subst i
            exact Nat.le_refl _
  | succ j ih =>
    by_cases he : i = j + 1
    · subst i; exact Nat.le_refl _
    · have hb := ih (by omega)
      rw [payloadPrefixBits_succ, List.length_append]
      omega

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- Distance-table intervals are checked on the 256 low entries and 254
high-byte intervals; arbitrary low seven bits are handled arithmetically. -/
theorem distance_payload_fields (d : Nat) (hd : d < 32768) :
    dcodeN d < 30 ∧ 0 ≤ extra_dbits_tab[dcodeN d]!.toInt ∧ extra_dbits_tab[dcodeN d]!.toInt ≤ 13 ∧
    0 ≤ base_dist_tab[dcodeN d]!.toInt ∧ base_dist_tab[dcodeN d]!.toInt.toNat ≤ d ∧
    d - base_dist_tab[dcodeN d]!.toInt.toNat < 2 ^ extra_dbits_tab[dcodeN d]!.toInt.toNat := by
  by_cases hs : d < 256
  · have ht : ∀ i : Fin 256,
        dcodeN i.val < 30 ∧ 0 ≤ extra_dbits_tab[dcodeN i.val]!.toInt ∧ extra_dbits_tab[dcodeN i.val]!.toInt ≤ 13 ∧
        0 ≤ base_dist_tab[dcodeN i.val]!.toInt ∧ base_dist_tab[dcodeN i.val]!.toInt.toNat ≤ i.val ∧
        i.val - base_dist_tab[dcodeN i.val]!.toInt.toNat < 2 ^ extra_dbits_tab[dcodeN i.val]!.toInt.toNat := by decide +kernel
    exact ht ⟨d, hs⟩
  · have hq : d / 128 < 256 := by omega
    have hq2 : 2 ≤ d / 128 := by omega
    have ht : ∀ i : Fin 256, 2 ≤ i.val →
        let c := dist_code_tab[256 + i.val]!.toNat
        c < 30 ∧ 0 ≤ extra_dbits_tab[c]!.toInt ∧ extra_dbits_tab[c]!.toInt ≤ 13 ∧
        0 ≤ base_dist_tab[c]!.toInt ∧ base_dist_tab[c]!.toInt.toNat ≤ 128 * i.val ∧
        128 * (i.val + 1) ≤ base_dist_tab[c]!.toInt.toNat + 2 ^ extra_dbits_tab[c]!.toInt.toNat := by decide +kernel
    have hv := ht ⟨d / 128, hq⟩ hq2
    simp only [dcodeN, ite_eq_right hs]
    dsimp only at hv
    obtain ⟨hc, h0, h13, hb0, hb, hr⟩ := hv
    refine ⟨hc, h0, h13, hb0, by omega, ?_⟩
    omega

end Zlib.Trees.Proofs.Out
