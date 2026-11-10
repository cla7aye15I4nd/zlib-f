import ZlibF.Proof.«deflate.c.engine.tally-literal»

/-! # Distance-code reads and frequency writes of the inline match tally

The strategy uses a UInt16 distance, while trees.c uses UInt32. This
bridge checks the actual strategy macro rather than assuming a call to
the translated _tr_tally function.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Trees.Proofs.Out (TreesBase TreesStatic bumpFc dcodeN)
set_option autoImplicit false

theorem distance_code_run {h : Heap} (static : TreesStatic h.static)
    (dist : UInt16) (bound : dist.toNat < 32768) :
    ∃ c : UInt8, Zlib.Deflate.d_code dist h = .ok (c, h) ∧
      c.toNat = dcodeN dist.toNat ∧ c.toNat ≤ 29 := by
  have get : Space.get h BRef.st_dist_code = some Zlib.Trees.dist_code_tab := by
    simp [Space.get, static.dist_code]
  let i := if dist.toNat < 256 then dist.toNat else 256 + dist.toNat / 128
  have fit : i < Zlib.Trees.dist_code_tab.size := by
    rw [Zlib.Trees.Proofs.Out.dist_code_tab_size]
    unfold i
    split <;> omega
  have read : index8 (.ref BRef.st_dist_code 0) i h =
      .ok (Zlib.Trees.dist_code_tab[i]!, h) := by
    simpa [OkOn, fit] using Ptr.index_ok (off := 0) (i := i) get (by omega)
  have run : Zlib.Deflate.d_code dist h = .ok (Zlib.Trees.dist_code_tab[i]!, h) := by
    have shift : (dist >>> 7).toNat = dist.toNat / 128 := by
      rw [UInt16.toNat_shiftRight]
      simp [Nat.shiftRight_eq_div_pow]
    unfold Zlib.Deflate.d_code
    by_cases small : dist.toNat < 256
    · simpa only [small, if_true, i] using read
    · simpa only [small, if_false, shift, i, Int.natCast_add] using read
  refine ⟨_, run, ?_, ?_⟩
  · unfold dcodeN i
    split <;> rfl
  · have fi : i < 512 := by simpa only [Zlib.Trees.Proofs.Out.dist_code_tab_size] using fit
    simpa [fit] using Zlib.Trees.Proofs.Out.dist_code_le i fi

theorem increment_distance_frequency {h : Heap} {ds : Nat} {d : DeflateState} {i : Nat}
    (state : h.dstates ds = some d) (bound : i < d.dyn_dtree.size) :
    freq_inc (.dstate_dyn_dtree ds) i h =
      .ok ((), setD h ds { d with dyn_dtree := bumpFc d.dyn_dtree i }) := by
  have get := CtDataRef.get_dstate_dyn_dtree state
  have add : padd (.ref (.dstate_dyn_dtree ds) 0 : CtDataPtr) i h =
      .ok (.ref (.dstate_dyn_dtree ds) i, h) := by
    simpa only [OkOn, padd, Nat.zero_add] using Ptr.add_nat_ok (off := 0) (n := i) get (by omega)
  have load := Ptr.load_ok (off := i) get bound
  have put := Ptr.store_ok (off := i) (v := { d.dyn_dtree[i] with fc := d.dyn_dtree[i].fc + 1 })
    get (by rfl) bound
  unfold freq_inc
  rw [bind_app, add]
  simp only [Nat.zero_add]
  rw [bind_app, load]
  simp only []
  rw [put, CtDataRef.put_dstate_dyn_dtree state]
  simp [setD, bumpFc, bound]

/-- The source's narrowing and pre-decrement keep the distance-code
index in range for a legal DEFLATE distance. The cast does not lose bits. -/
theorem match_distance_index (distance : UInt32)
    (positive : 1 ≤ distance.toNat) (bound : distance.toNat ≤ 32768) :
    distance.toUInt16.toNat = distance.toNat ∧
      (distance.toUInt16 - 1).toNat = distance.toNat - 1 ∧
      (distance.toUInt16 - 1).toNat < 32768 := by
  have narrow : distance.toUInt16.toNat = distance.toNat := by
    rw [UInt32.toNat_toUInt16]
    exact Nat.mod_eq_of_lt (by omega)
  have sub : (distance.toUInt16 - 1).toNat = distance.toUInt16.toNat - 1 := by
    rw [UInt16.toNat_sub_of_le _ _ (by rw [UInt16.le_iff_toNat_le]; simpa [narrow] using positive)]
    rfl
  rw [narrow] at sub
  exact ⟨narrow, sub, by rw [sub]; omega⟩

end Zlib.Deflate.Engine.Proofs
