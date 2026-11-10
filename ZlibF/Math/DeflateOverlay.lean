import ZlibF.Math.HuffmanFibPush

/-!
# Prefix accounting for the shared pending/symbol buffer

Each consumed symbol releases three bytes. Its encoded bit cost may exceed
24, so a whole-block excess budget bounds every prefix. The coefficient
6257/1000 and header bound 2283 are the targets of the reference FibPush
argument. This file proves their arithmetic consequences; it does not
assume a callee contract or claim that a translated block establishes them.
-/

namespace Zlib.Trees.Overlay
set_option autoImplicit false

/-- Total positive excess over the 24 bits released by one symbol. -/
def bitExcess (costs : List Nat) : Nat :=
  (costs.map (fun bits => bits - 24)).sum

/-- A prefix costs no more than 24 bits per consumed symbol plus the
whole block's excess. No bound on an individual symbol is needed. -/
theorem prefix_bits_le (costs : List Nat) :
    ∀ k, (costs.take k).sum ≤ 24 * k + bitExcess costs := by
  induction costs with
  | nil => intro k; simp [bitExcess]
  | cons bits rest ih =>
    intro k
    cases k with
    | zero => simp
    | succ k =>
      have bound := ih k
      simp only [List.take_succ_cons, List.sum_cons]
      simp only [bitExcess, List.map_cons, List.sum_cons]
      rw [Nat.mul_succ]
      unfold bitExcess at bound
      omega

/-- With a drained block-entry state, the reference excess and header
bounds leave at least fifteen bits before every unread-symbol boundary.
The numeric domain includes memLevel 6 through 9. The bounds remain data
premises until established from actual tallies, tree construction and
emission; this is not a public compressor theorem. -/
theorem large_overlay_prefix (capacity start header : Nat) (costs : List Nat)
    (capacity_min : 4096 ≤ capacity) (start_max : start ≤ 7)
    (header_max : header ≤ 2283) (symbols_fit : costs.length + 1 ≤ capacity)
    (excess : 1000 * bitExcess costs ≤ 6257 * (costs.length + 1)) (k : Nat) :
    start + 3 + header + (costs.take k).sum + 15 ≤ 8 * (capacity + 3 * k) := by
  have prefix_bound := prefix_bits_le costs k
  omega

/-- The default memLevel 8 uses lit_bufsize = 16384. This is a concrete
instance of the prefix budget, not a restriction on the public API. -/
theorem default_overlay_prefix (start header : Nat) (costs : List Nat)
    (start_max : start ≤ 7) (header_max : header ≤ 2283)
    (symbols_fit : costs.length + 1 ≤ 16384)
    (excess : 1000 * bitExcess costs ≤ 6257 * (costs.length + 1)) (k : Nat) :
    start + 3 + header + (costs.take k).sum + 15 ≤ 8 * (16384 + 3 * k) :=
  large_overlay_prefix 16384 start header costs (by decide) start_max header_max symbols_fit excess k

end Zlib.Trees.Overlay
