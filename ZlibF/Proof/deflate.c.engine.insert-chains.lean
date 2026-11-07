import ZlibF.Proof.«deflate.c.engine.initial»

/-! # Actual hash insertion preserves the heap chain invariant -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec
set_option autoImplicit false

/-- `INSERT_STRING(s, str, hash_head)`.
The existing execution proof and mathematical insertion proof describe
the same two array writes. The primed rolling hash advances by one byte.
The explicit position conditions belong to the caller's window invariant.
-/
theorem insert_string_chains {h : Heap} {sr wb hb pb top bits : Nat}
    {d : DeflateState} {wa : Array UInt8} {ha pa : Array UInt16}
    (hd : h.dstates sr = some d) (env : HashEnv h d wb hb pb wa ha pa)
    (chains : HashChains (wfn ha) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat top (d.strstart.toNat + d.lookahead.toNat))
    (str : UInt32) (ws : d.w_size.toNat = 2 ^ bits)
    (mask : d.w_mask.toNat = d.w_size.toNat - 1)
    (ordered : top ≤ str.toNat)
    (data : str.toNat + 3 ≤ d.strstart.toNat + d.lookahead.toNat)
    (window : d.strstart.toNat + d.lookahead.toNat ≤ wa.size)
    (position : str.toNat < 65536)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) str.toNat d.ins_h) :
    ∃ key : UInt32,
      let d' := { d with ins_h := key }
      let h' := { h with
        dstates := upd h.dstates sr (some d')
        words := upd (upd h.words pb (some (pa.set! (str &&& d.w_mask).toNat (wfn ha key.toNat))))
          hb (some (ha.set! key.toNat str.toUInt16)) }
      INSERT_STRING (some (.tab sr)) str h = .ok ((wfn ha key.toNat).toUInt32, h') ∧
      HeapChains h' d' (str.toNat + 1) ∧
      InsHForm d.hash_shift d.hash_mask (bfn wa) (str.toNat + 1) key := by
  have fit : str.toNat + 2 < wa.size := by omega
  obtain ⟨key, keyEq, keyBound, run⟩ := INSERT_STRING_ok hd env str fit (by omega)
  have byte : wa[str.toNat + 2]! = bfn wa (str.toNat + 2) := by
    simp [bfn, Array.getD_eq_getD_getElem?, fit]
  have hash : key = hkey d.hash_shift d.hash_mask (bfn wa) str.toNat := by
    rw [keyEq, byte]
    exact hkey_of_form env.params form
  have s16 : str.toUInt16.toNat = str.toNat := by
    rw [UInt32.toNat_toUInt16, Nat.mod_eq_of_lt position]
  have slot : (str &&& d.w_mask).toNat < pa.size := by
    rw [UInt32.toNat_and]
    have bound := Nat.and_le_right (n := str.toNat) (m := d.w_mask.toNat)
    have size := env.wsize
    have small := env.wmask
    omega
  have headFit : key.toNat < ha.size := by have size := env.hsize; omega
  have H := chains_insert chains ws ordered data
    (show (hkey d.hash_shift d.hash_mask (bfn wa) str.toNat).toNat = key.toNat by rw [hash])
    keyBound s16
    (fun i => wfn_set ha key.toNat str.toUInt16 headFit i)
    (fun i => by
      simpa only [UInt32.toNat_and, mask] using
        wfn_set pa (str &&& d.w_mask).toNat (wfn ha key.toNat) slot i)
  refine ⟨key, run, ?_, ?_⟩
  · refine ⟨wb, pb, hb, wa, pa.set! (str &&& d.w_mask).toNat (wfn ha key.toNat),
      ha.set! key.toNat str.toUInt16, env.win, env.prevp, env.headp, ?_, ?_, ?_, ?_⟩
    · exact env.wbytes
    · simp [upd_ne _ _ _ _ env.hne.symm]
    · simp
    · simpa only [UInt32.toNat_and, mask] using H
  · rw [keyEq, byte]
    exact form_next form

/-- The same actual insertion preserves both representation and chains.
This is the combined caller boundary needed by the engine loop. -/
theorem insert_string_good_chains {h : Heap} {r : ZStreamRef} {sr wb hb pb top bits : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {ha pa : Array UInt16}
    (good : DGood h r sr z d) (env : HashEnv h d wb hb pb wa ha pa)
    (chains : HashChains (wfn ha) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat top (d.strstart.toNat + d.lookahead.toNat))
    (str : UInt32) (ws : d.w_size.toNat = 2 ^ bits)
    (mask : d.w_mask.toNat = d.w_size.toNat - 1)
    (ordered : top ≤ str.toNat)
    (data : str.toNat + 3 ≤ d.strstart.toNat + d.lookahead.toNat)
    (window : d.strstart.toNat + d.lookahead.toNat ≤ wa.size)
    (position : str.toNat < 65536)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) str.toNat d.ins_h) :
    ∃ key after, INSERT_STRING (some (.tab sr)) str h =
        .ok ((wfn ha key.toNat).toUInt32, after) ∧
      DGood after r sr z { d with ins_h := key } ∧
      HeapChains after { d with ins_h := key } (str.toNat + 1) ∧
      InsHForm d.hash_shift d.hash_mask (bfn wa) (str.toNat + 1) key := by
  obtain ⟨key, run, H, primed⟩ := insert_string_chains good.live.hs env chains str ws mask
    ordered data window position form
  let pa' := pa.set! (str &&& d.w_mask).toNat (wfn ha key.toNat)
  let ha' := ha.set! key.toNat str.toUInt16
  have prevGood := good.words_set pb pa' pa env.pwords (by simp [pa'])
  have headGood := prevGood.words_set hb ha' ha
    (by simpa [env.hne] using env.hwords) (by simp [ha'])
  have inv : DStInv _ sr { d with ins_h := key } :=
    { headGood.inv with blocks := headGood.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  have updated := headGood.setD' (d' := { d with ins_h := key }) rfl good.live.status inv (by trkeep)
  refine ⟨key, _, run, ?_, H, primed⟩
  exact updated

end Zlib.Deflate.Engine.Proofs
