import ZlibF.Proof.«deflate.c.engine.fill-prime»

/-! # Priming a resumed window with no deferred insertions -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

def resumePrimeState (d : DeflateState) (wa : Array UInt8) : DeflateState :=
  if d.lookahead ≥ 3 then
    { d with ins_h := updHash d.hash_shift d.hash_mask wa[d.strstart.toNat]!.toUInt32 wa[d.strstart.toNat + 1]! }
  else d

/-- The actual source fragment at an arbitrary current position. The
private window bound makes the UInt32 byte-index additions exact. -/
theorem fill_prime_resume {h : Heap} {ds w : Nat} {d : DeflateState} {wa : Array UInt8}
    (state : h.dstates ds = some d) (win : d.window = .ref (.blk w) 0)
    (get : h.bytes w = some wa) (insert : d.insert = 0)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ wa.size) (size : wa.size ≤ 65536)
    (shift : d.hash_shift < 32) :
    fillPrime (some (.tab ds)) h = .ok ((), setD h ds (resumePrimeState d wa)) := by
  by_cases large : d.lookahead ≥ (3 : UInt32)
  · have la : 3 ≤ d.lookahead.toNat := UInt32.le_iff_toNat_le.mp large
    have fit0 : d.strstart.toNat < wa.size := by omega
    have fit1 : d.strstart.toNat + 1 < wa.size := by omega
    have next : (d.strstart + 1).toNat = d.strstart.toNat + 1 := by
      rw [UInt32.toNat_add]
      simp only [show (1 : UInt32).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (by omega)
    let c0 := wa[d.strstart.toNat]!
    let c1 := wa[d.strstart.toNat + 1]!
    let d0 := { d with ins_h := c0.toUInt32 }
    let h0 := setD h ds d0
    let df := { d with ins_h := updHash d.hash_shift d.hash_mask c0.toUInt32 c1 }
    let hf := setD h ds df
    have read0 : index8 d.window d.strstart.toNat h = .ok (c0, h) := by
      rw [win]
      simpa [OkOn, fit0, c0] using index8_ok (off := 0) (i := d.strstart.toNat) get (by omega)
    have write0 : wr (some (.tab ds)) (fun d => { d with ins_h := c0.toUInt32 }) h = .ok ((), h0) := by
      simp [wrD_eq, state, h0, d0]
    have read1 : index8 d.window (d.strstart.toNat + 1) h0 = .ok (c1, h0) := by
      rw [win]
      simpa [OkOn, fit1, c1] using index8_ok (h := h0) (off := 0)
        (i := d.strstart.toNat + 1) (by simpa [h0] using get) (by omega)
    have update : UPDATE_HASH (some (.tab ds)) c1 h0 = .ok ((), hf) := by
      have run := UPDATE_HASH_ok (h := h0) (sr := ds) (d := d0) c1 (by simp [h0]) shift
      simpa [h0, hf, d0, df, setD, upd_upd] using run
    have loops := empty_insert_loop (h := hf) (ds := ds) (d := df)
      (by simp [hf]) (by simpa [df] using insert)
    have enter : d.lookahead + d.insert ≥ MIN_MATCH_u := by simpa [insert, MIN_MATCH_u] using large
    unfold fillPrime
    rw [bind_app, ldDeflateState_tab state]
    simp only []
    rw [if_pos enter]
    simp only [insert, UInt32.sub_zero, next, bind_app, read0, write0]
    change (do
      UPDATE_HASH (some (.tab ds)) (← index8 d.window (d.strstart.toNat + 1))
      let (_, _) ← cwhile _ _ (d.strstart, false)
      pure ()) h0 = _
    simp only [bind_app, read1, update, loops, pure_app, resumePrimeState, large, if_true]
    rfl
  · simp [fillPrime, bind_app, ldDeflateState_tab state, insert, MIN_MATCH_u, large,
      resumePrimeState, setD_self state]

theorem resume_prime_form {d : DeflateState} {wa : Array UInt8}
    (params : HashParams d.hash_size d.hash_shift d.hash_mask)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ wa.size) (large : d.lookahead ≥ 3) :
    InsHForm d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat (resumePrimeState d wa).ins_h := by
  have la : 3 ≤ d.lookahead.toNat := UInt32.le_iff_toNat_le.mp large
  have fit0 : d.strstart.toNat < wa.size := by omega
  have fit1 : d.strstart.toNat + 1 < wa.size := by omega
  simpa [resumePrimeState, large, bfn, Array.getD_eq_getD_getElem?, fit0, fit1] using
    form_init params (bfn wa) d.strstart.toNat

theorem resume_prime_record (d : DeflateState) (wa : Array UInt8) :
    ∃ key, resumePrimeState d wa = { d with ins_h := key } := by
  unfold resumePrimeState
  split
  · exact ⟨_, rfl⟩
  · exact ⟨d.ins_h, rfl⟩

end Zlib.Deflate.Engine.Proofs
