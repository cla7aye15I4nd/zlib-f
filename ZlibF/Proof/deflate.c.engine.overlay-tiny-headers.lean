import ZlibF.Proof.«deflate.c.engine.overlay-mem1»

/-!
# deflate.c: `TinyOverlay` from the two header bounds

Below 512, `lit_bufsize` is 128 or 256 (`memLevel` 1 or 2). The overlay room holds at 256 from
`HeaderRefBound Δ₂` with `Δ₂ ≤ 171` (`dynamic_overlay_256`) and at 128 from `HeaderRefBound128 Δ₁`
with `Δ₁ ≤ 132` (`dynamic_overlay_128`). So `TinyOverlay`, the one open hypothesis of the deflate
proofs, follows from the two header bounds (batch 1's open pieces).
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Universal.Block (TinyOverlay)
set_option autoImplicit false

/-- `lit_bufsize` is a power of two of at least 128, so below 512 it is 128 or 256. -/
theorem lit_bufsize_tiny {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (upper : d.lit_bufsize.toNat < 512) :
    d.lit_bufsize.toNat = 128 ∨ d.lit_bufsize.toNat = 256 := by
  have lit := good.inv.lit
  have size := good.inv.hsize
  have bitsMax := good.inv.hbits_hi
  have bitsMin := good.inv.hbits_lo
  generalize d.hash_bits.toNat = k at size bitsMax bitsMin
  rw [size] at lit
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;>
    (try simp only [Nat.reduceAdd, Nat.reducePow] at lit) <;> omega

/-- **`TinyOverlay` from the two header bounds.** -/
theorem tiny_overlay_of_headers {Δ₁ Δ₂ : Nat} (small₁ : Δ₁ ≤ 132) (header₁ : HeaderRefBound128 Δ₁)
    (small₂ : Δ₂ ≤ 171) (header₂ : HeaderRefBound Δ₂) : TinyOverlay := by
  intro h r ds pb z d buf xs good trees ledger clear pending bits tiny z'
  rcases lit_bufsize_tiny good tiny with size | size
  · exact dynamic_overlay_128 small₁ header₁ good trees ledger clear pending bits size z'
  · exact dynamic_overlay_256 small₂ header₂ good trees ledger clear pending bits size z'

#print axioms tiny_overlay_of_headers

end Zlib.Deflate.Engine.Proofs
