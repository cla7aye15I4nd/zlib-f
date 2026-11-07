import ZlibF.Proof.«deflate.c.engine.fill-source»

/-! # Priming the first window without deferred insertions -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

theorem while_stops {α : Type} {cond : α → M (Bool × α)} {body : α → M α}
    {h g : Heap} {a b : α} (stop : cond a h = .ok ((false, b), g)) :
    cwhile cond body a h = .ok (b, g) := by
  unfold cwhile
  change cwhile.go cond body (18446744073709551615 + 1) a h = _
  rw [cwhile.go, bind_app, stop]
  rfl

theorem empty_insert_loop {h : Heap} {ds : Nat} {d : DeflateState}
    (state : h.dstates ds = some d) (insert : d.insert = 0)
    (body : UInt32 × Bool → M (UInt32 × Bool)) (str : UInt32) :
    cwhile (fun (str, brk) => do
        let ins ← rd (some (.tab ds)) (·.insert)
        pure (ins != 0 && !brk, (str, brk))) body (str, false) h = .ok ((str, false), h) := by
  apply while_stops
  simp [bind_app, rdD_eq, state, insert]

def primeState (d : DeflateState) (wa : Array UInt8) : DeflateState :=
  if d.lookahead ≥ 3 then
    { d with ins_h := updHash d.hash_shift d.hash_mask wa[0]!.toUInt32 wa[1]! }
  else d

/-- The actual priming and insertion fragment when no insertion is
deferred. Fewer than three valid bytes take the source's no-op branch. -/
theorem fill_prime_initial {h : Heap} {ds w : Nat} {d : DeflateState} {wa : Array UInt8}
    (state : h.dstates ds = some d) (win : d.window = .ref (.blk w) 0)
    (get : h.bytes w = some wa) (ss : d.strstart = 0) (insert : d.insert = 0)
    (valid : d.lookahead.toNat ≤ wa.size) (shift : d.hash_shift < 32) :
    fillPrime (some (.tab ds)) h = .ok ((), setD h ds (primeState d wa)) := by
  by_cases large : d.lookahead ≥ (3 : UInt32)
  · have la : 3 ≤ d.lookahead.toNat := by simpa [UInt32.le_iff_toNat_le] using large
    have b0 : 0 < wa.size := by omega
    have b1 : 1 < wa.size := by omega
    let d0 := { d with ins_h := wa[0]!.toUInt32 }
    let h0 := setD h ds d0
    let df := { d with ins_h := updHash d.hash_shift d.hash_mask wa[0]!.toUInt32 wa[1]! }
    let hf := setD h ds df
    have read0 : index8 d.window 0 h = .ok (wa[0]!, h) := by
      rw [win]
      simpa [OkOn, b0] using index8_ok (off := 0) (i := 0) get (by omega)
    have write0 : wr (some (.tab ds)) (fun d => { d with ins_h := wa[0]!.toUInt32 }) h =
        .ok ((), h0) := by simp [wrD_eq, state, h0, d0]
    have read1 : index8 d.window 1 h0 = .ok (wa[1]!, h0) := by
      rw [win]
      simpa [OkOn, b1] using index8_ok (h := h0) (off := 0) (i := 1)
        (by simpa [h0] using get) (by omega)
    have update : UPDATE_HASH (some (.tab ds)) wa[1]! h0 = .ok ((), hf) := by
      have run := UPDATE_HASH_ok (h := h0) (sr := ds) (d := d0) wa[1]!
        (by simp [h0]) shift
      simpa [h0, hf, d0, df, setD, upd_upd] using run
    have loops := empty_insert_loop (h := hf) (ds := ds) (d := df)
      (by simp [hf]) (by simpa [df] using insert)
    have enter : d.lookahead + d.insert ≥ MIN_MATCH_u := by simpa [insert, MIN_MATCH_u] using large
    unfold fillPrime
    rw [bind_app, ldDeflateState_tab state]
    simp only []
    rw [if_pos enter]
    simp only [ss, insert, UInt32.sub_self, show (0 : UInt32).toNat = 0 from rfl,
      show ((0 : Nat) : Int) = 0 from rfl,
      bind_app, read0, write0]
    simp only [show (0 : UInt32) + 1 = 1 from rfl, show (1 : UInt32).toNat = 1 from rfl,
      show ((1 : Nat) : Int) = 1 from rfl]
    change (do
      UPDATE_HASH (some (.tab ds)) (← index8 d.window 1)
      let (_, _) ← cwhile _ _ ((0 : UInt32), false)
      pure ()) h0 = _
    simp only [bind_app, read1, update, loops, pure_app]
    simp only [primeState, large, if_true]
    rfl
  · simp [fillPrime, bind_app, ldDeflateState_tab state, insert, MIN_MATCH_u, large,
      primeState, setD_self state]

/-- After priming, the next INSERT_STRING reads the same first two bytes.
The hash starts from actual copied data, independently of old ins_h. -/
theorem primeState_form {d : DeflateState} {wa : Array UInt8}
    (params : HashParams d.hash_size d.hash_shift d.hash_mask)
    (valid : d.lookahead.toNat ≤ wa.size) (large : d.lookahead ≥ 3) :
    InsHForm d.hash_shift d.hash_mask (bfn wa) 0 (primeState d wa).ins_h := by
  have la : 3 ≤ d.lookahead.toNat := by simpa [UInt32.le_iff_toNat_le] using large
  have b0 : 0 < wa.size := by omega
  have b1 : 1 < wa.size := by omega
  simpa [primeState, large, bfn, Array.getD_eq_getD_getElem?, b0, b1] using form_init params (bfn wa) 0

end Zlib.Deflate.Engine.Proofs
