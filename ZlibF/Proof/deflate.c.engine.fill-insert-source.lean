import ZlibF.Proof.«deflate.c.engine.fill-source»
import ZlibF.Proof.«deflate.c.engine.insert-chains»

/-! # The real deferred-insertion loop in fill_window -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

def fillInsertCond (s : DeflateStatePtr) (cursor : UInt32 × Bool) : M (Bool × (UInt32 × Bool)) := do
  let ins ← rd s (·.insert)
  pure (ins != 0 && !cursor.2, cursor)

def fillInsertBody (s : DeflateStatePtr) (cursor : UInt32 × Bool) : M (UInt32 × Bool) := do
  let _ ← INSERT_STRING s cursor.1
  let str := cursor.1 + 1
  wr s (fun d => { d with insert := d.insert - 1 })
  let d ← ldDeflateState s
  pure (str, d.lookahead + d.insert < MIN_MATCH_u)

def fillInsertSeed (s : DeflateStatePtr) (window : BPtr) (str : UInt32) : M Unit := do
  let c0 ← index8 window str.toNat
  wr s (fun d => { d with ins_h := c0.toUInt32 })
  UPDATE_HASH s (← index8 window (str + 1).toNat)

/-- The helper insertion expands to exactly the source's hash update and
two word stores. The unused return from INSERT_STRING has no heap effect. -/
theorem fill_prime_pending_source (s : DeflateStatePtr) : fillPrime s = (do
    let d ← ldDeflateState s
    if d.lookahead + d.insert ≥ MIN_MATCH_u then
      let str := d.strstart - d.insert
      fillInsertSeed s d.window str
      let (_, _) ← cwhile (fillInsertCond s) (fillInsertBody s) (str, false)
      pure ()) := by
  unfold fillPrime fillInsertSeed fillInsertCond fillInsertBody INSERT_STRING
  simp only [M_bind_assoc, M_pure_bind]

def insertSeedState (d : DeflateState) (wa : Array UInt8) (str : UInt32) : DeflateState :=
  { d with ins_h := updHash d.hash_shift d.hash_mask wa[str.toNat]!.toUInt32 wa[str.toNat + 1]! }

/-- The seed reads exactly two valid bytes at the pending frontier. -/
theorem fill_insert_seed_run {h : Heap} {ds w : Nat} {d : DeflateState} {wa : Array UInt8}
    (state : h.dstates ds = some d) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (str : UInt32) (fit : str.toNat + 2 ≤ wa.size) (size : wa.size ≤ 65536) (shift : d.hash_shift < 32) :
    fillInsertSeed (some (.tab ds)) d.window str h = .ok ((), setD h ds (insertSeedState d wa str)) := by
  let c0 := wa[str.toNat]!
  let c1 := wa[str.toNat + 1]!
  let d0 := { d with ins_h := c0.toUInt32 }
  let h0 := setD h ds d0
  let df := insertSeedState d wa str
  have next : (str + 1).toNat = str.toNat + 1 := by
    rw [UInt32.toNat_add]
    simp only [show (1 : UInt32).toNat = 1 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  have read0 : index8 d.window str.toNat h = .ok (c0, h) := by
    rw [win]
    simpa [OkOn, c0, show str.toNat < wa.size by omega] using
      index8_ok (off := 0) (i := str.toNat) get (by omega)
  have write0 : wr (some (.tab ds)) (fun d => { d with ins_h := c0.toUInt32 }) h = .ok ((), h0) := by
    simp [wrD_eq, state, h0, d0]
  have read1 : index8 d.window (str.toNat + 1) h0 = .ok (c1, h0) := by
    rw [win]
    simpa [OkOn, c1, show str.toNat + 1 < wa.size by omega] using
      index8_ok (h := h0) (off := 0) (i := str.toNat + 1) (by simpa [h0] using get) (by omega)
  have update : UPDATE_HASH (some (.tab ds)) c1 h0 = .ok ((), setD h ds df) := by
    have run := UPDATE_HASH_ok (h := h0) (sr := ds) (d := d0) c1 (by simp [h0]) shift
    simpa [h0, d0, df, insertSeedState, setD, upd_upd] using run
  unfold fillInsertSeed
  simp only [bind_app, read0, write0, next, Int.natCast_add_one, read1, update]
  rfl

theorem insert_seed_form {d : DeflateState} {wa : Array UInt8} {str : UInt32}
    (params : HashParams d.hash_size d.hash_shift d.hash_mask) (fit : str.toNat + 2 ≤ wa.size) :
    InsHForm d.hash_shift d.hash_mask (bfn wa) str.toNat (insertSeedState d wa str).ins_h := by
  simpa [insertSeedState, bfn, Array.getD_eq_getD_getElem?,
    show str.toNat < wa.size by omega, show str.toNat + 1 < wa.size by omega] using
    form_init params (bfn wa) str.toNat

end Zlib.Deflate.Engine.Proofs
