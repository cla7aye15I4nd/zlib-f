import ZlibF.Math.«overlay-lp-cert-data-1»
import ZlibF.Math.«overlay-lp-cert-data-2»
import ZlibF.Math.«overlay-lp-cert-data-3-m2»
import ZlibF.Math.«overlay-lp-cert-data-3-m1»
import ZlibF.Math.«overlay-lp-cert-data-3-m0»

/-!
# The memLevel 1–3 LP bounds, kernel-checked (`check_all.py` in Lean)

`docs/DEFLATE_OVERLAY.md` §8.4. For memLevel `ml ∈ {1, 2, 3}` and each distance-tree case
`c ∈ {M2, M1, M0}`, `check_all.py` uses the route *huff + ovf*: a block whose bit-length tree
does not overflow is a feasible point of the `huff` LP (`covf = 0`, cuts `huffCuts ml c`), one
whose bit-length tree overflows is a feasible point of the `ovf` LP (`covf = 1/4, 3/8, 2/5`,
cuts `ovfCuts ml c`). Both certificates bound `hd + E` by `lowmemB' ml = 943, 1636, 2784`
(`lp_bound`). At memLevel 3 the *crude* LP (every bit-length code length `≤ 7`, valid for every
block) alone gives the bound for `M1` and `M0` (`lp3_crude_bound`).

What is **not** here: that every real dynamic block is a feasible point of these LPs
(relaxation soundness: ov4, `OverlayLP*`), and the gen_bitlen overflow constant `covf`
(`ovf_cert_*.json`, `ovf_cert.py`). The cut codes are Kraft-valid (`cuts_kraft`), which is the
condition under which ov4's cut rows are valid.
-/

namespace Zlib.Trees.OverlayLP.Cert
open Zlib.Trees.OverlayLP

/-- The certified bound at memLevel `ml` (`= Emit.lowmemB`). -/
def lowmemB' : Nat → Int
  | 1 => 943
  | 2 => 1636
  | 3 => 2784
  | _ => 0

/-- `covf = p/q` of the overflow route: numerator. -/
def ovfP : Nat → Nat
  | 1 => 1 | 2 => 3 | _ => 2
/-- `covf = p/q` of the overflow route: denominator. -/
def ovfQ : Nat → Nat
  | 1 => 4 | 2 => 8 | _ => 5

/-- The cut codes of the `huff` certificates. -/
def huffCuts : Nat → DCase → List (List Nat)
  | 1, .M2 => lp1M2_huff_cuts
  | 1, .M1 => lp1M1_huff_cuts
  | 1, .M0 => lp1M0_huff_cuts
  | 2, .M2 => lp2M2_huff_cuts
  | 2, .M1 => lp2M1_huff_cuts
  | 2, .M0 => lp2M0_huff_cuts
  | 3, .M2 => lp3M2_huff_cuts
  | 3, .M1 => lp3M1_huff_cuts
  | 3, .M0 => lp3M0_huff_cuts
  | _, _ => []

/-- The cut codes of the `ovf` certificates. -/
def ovfCuts : Nat → DCase → List (List Nat)
  | 1, .M2 => lp1M2_ovf_cuts
  | 1, .M1 => lp1M1_ovf_cuts
  | 1, .M0 => lp1M0_ovf_cuts
  | 2, .M2 => lp2M2_ovf_cuts
  | 2, .M1 => lp2M1_ovf_cuts
  | 2, .M0 => lp2M0_ovf_cuts
  | 3, .M2 => lp3M2_ovf_cuts
  | 3, .M1 => lp3M1_ovf_cuts
  | 3, .M0 => lp3M0_ovf_cuts
  | _, _ => []

/-- Every cut code used is a Kraft-valid code on the 19 bit-length symbols. -/
theorem cuts_kraft (ml : Nat) (c : DCase) (h1 : 1 ≤ ml) (h3 : ml ≤ 3) :
    cutsKraft (huffCuts ml c) = true ∧ cutsKraft (ovfCuts ml c) = true := by
  rcases (show ml = 1 ∨ ml = 2 ∨ ml = 3 by omega) with rfl | rfl | rfl <;> cases c <;>
    first
    | exact ⟨lp1M2_huff_kraft, lp1M2_ovf_kraft⟩
    | exact ⟨lp1M1_huff_kraft, lp1M1_ovf_kraft⟩
    | exact ⟨lp1M0_huff_kraft, lp1M0_ovf_kraft⟩
    | exact ⟨lp2M2_huff_kraft, lp2M2_ovf_kraft⟩
    | exact ⟨lp2M1_huff_kraft, lp2M1_ovf_kraft⟩
    | exact ⟨lp2M0_huff_kraft, lp2M0_ovf_kraft⟩
    | exact ⟨lp3M2_huff_kraft, lp3M2_ovf_kraft⟩
    | exact ⟨lp3M1_huff_kraft, lp3M1_ovf_kraft⟩
    | exact ⟨lp3M0_huff_kraft, lp3M0_ovf_kraft⟩

/-- **The memLevel 1–3 LP bound** (kernel-checked dual certificates): every feasible point of
the `huff` LP or of the `ovf` LP of memLevel `ml` and case `c` has `hd + E ≤ lowmemB' ml`. -/
theorem lp_bound (ml : Nat) (c : DCase) (h1 : 1 ≤ ml) (h3 : ml ≤ 3) (x : Var → Int)
    (hx : Feasible (theLP ml c 0 1 (huffCuts ml c)) x ∨
      Feasible (theLP ml c (ovfP ml) (ovfQ ml) (ovfCuts ml c)) x) :
    x .hd + x .E ≤ lowmemB' ml := by
  rcases (show ml = 1 ∨ ml = 2 ∨ ml = 3 by omega) with rfl | rfl | rfl <;> cases c <;>
    rcases hx with hx | hx
  · have := lp1M2_huff_bound x hx; simp only [lowmemB']; omega
  · have := lp1M2_ovf_bound x hx; simp only [lowmemB']; omega
  · have := lp1M1_huff_bound x hx; simp only [lowmemB']; omega
  · have := lp1M1_ovf_bound x hx; simp only [lowmemB']; omega
  · have := lp1M0_huff_bound x hx; simp only [lowmemB']; omega
  · have := lp1M0_ovf_bound x hx; simp only [lowmemB']; omega
  · have := lp2M2_huff_bound x hx; simp only [lowmemB']; omega
  · have := lp2M2_ovf_bound x hx; simp only [lowmemB']; omega
  · have := lp2M1_huff_bound x hx; simp only [lowmemB']; omega
  · have := lp2M1_ovf_bound x hx; simp only [lowmemB']; omega
  · have := lp2M0_huff_bound x hx; simp only [lowmemB']; omega
  · have := lp2M0_ovf_bound x hx; simp only [lowmemB']; omega
  · have := lp3M2_huff_bound x hx; simp only [lowmemB']; omega
  · have := lp3M2_ovf_bound x hx; simp only [lowmemB']; omega
  · have := lp3M1_huff_bound x hx; simp only [lowmemB']; omega
  · have := lp3M1_ovf_bound x hx; simp only [lowmemB']; omega
  · have := lp3M0_huff_bound x hx; simp only [lowmemB']; omega
  · have := lp3M0_ovf_bound x hx; simp only [lowmemB']; omega

/-- At memLevel 3, cases `M1` and `M0`, the crude LP (bit-length code lengths `≤ 7`, no
overflow analysis) alone gives `hd + E ≤ 2784`. -/
theorem lp3_crude_bound (c : DCase) (hc : c ≠ .M2) (x : Var → Int)
    (hx : Feasible (theLP 3 c 0 1 [[7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7]]) x) :
    x .hd + x .E ≤ 2784 := by
  cases c
  · exact absurd rfl hc
  · have := lp3M1_crude_bound x hx; omega
  · have := lp3M0_crude_bound x hx; omega

end Zlib.Trees.OverlayLP.Cert
