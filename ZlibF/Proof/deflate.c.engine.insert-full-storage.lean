import ZlibF.Proof.«deflate.c.engine.full-storage»

/-! # Complete heap effects of actual hash insertion -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Proofs.DefaultInit
set_option autoImplicit false

/-- The actual hash insertion changes only the state and the two private
word arrays. Its complete object ledger and allocation counters are retained. -/
theorem insert_string_run_full_storage {h after : Heap} {r : ZStreamRef} {ds w q p : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {ha pa : Array UInt16}
    (good : DGood h r ds z d) (env : HashEnv h d w q p wa ha pa)
    (str : UInt32) (room : str.toNat + 2 < wa.size) (small : str.toNat + 2 < 2 ^ 32)
    {value : UInt32} (run : INSERT_STRING (some (.tab ds)) str h = .ok (value, after)) :
    Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨key, _hash, _bound, expected⟩ := INSERT_STRING_ok good.live.hs env str room small
  have eq := (Prod.mk.inj (Except.ok.inj (expected.symm.trans run))).2
  rw [← eq]
  let linked := setW h p (pa.set! (str &&& d.w_mask).toNat (wfn ha key.toNat))
  let headed := setW linked q (ha.set! key.toNat str.toUInt16)
  have shapeP : Shape h linked := shape_setW env.pwords _
  have getQ : linked.words q = some ha := by
    simp only [linked, setW, upd_ne _ _ _ _ env.hne]
    exact env.hwords
  have shapeQ : Shape linked headed := shape_setW getQ _
  have getD : headed.dstates ds = some d := good.live.hs
  have shapeD := shape_setD getD {d with ins_h := key}
  have frameP : Frame h linked (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := by
    apply full_frame_weaken (word_store_full_frame h p _)
    intro b same
    subst b
    exact Or.inr (Or.inr (Or.inr (Or.inl env.prevp)))
  have frameQ : Frame linked headed (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := by
    apply full_frame_weaken (word_store_full_frame linked q _)
    intro b same
    subst b
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl env.headp))))
  have frameD : Frame headed (setD headed ds {d with ins_h := key})
      (fun b => StreamRoot r b ∨ DeflateOwned ds d b) :=
    full_frame_weaken (state_store_full_frame headed ds _) (fun _ same => Or.inr (Or.inl same))
  have shape := (shapeP.trans shapeQ).trans shapeD
  have frame := full_frame_trans_shape (full_frame_trans_shape frameP frameQ shapeP) frameD (shapeP.trans shapeQ)
  exact ⟨shape, frame, full_shape_live_change shape, rfl, rfl⟩

/-- A deferred insertion retains its complete heap frame, not only its byte slots. -/
theorem fill_insert_step_full_storage {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} (str : UInt32) (brk : Bool)
    (good : DGood h r ds z d) (chains : HeapChains h d str.toNat)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (cursor : str.toNat + d.insert.toNat = d.strstart.toNat)
    (positive : 1 ≤ d.insert.toNat) (ready : 3 ≤ d.lookahead.toNat + d.insert.toNat)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) str.toNat d.ins_h) :
    ∃ key after,
      let result := pendingInsertState d key
      fillInsertBody (some (.tab ds)) (str, brk) h =
        .ok ((str + 1, result.lookahead + result.insert < MIN_MATCH_u), after) ∧
      DGood after r ds z result ∧ HeapChains after result (str.toNat + 1) ∧ after.bytes = h.bytes ∧
      (str + 1).toNat = str.toNat + 1 ∧ result.insert.toNat = d.insert.toNat - 1 ∧
      InsHForm result.hash_shift result.hash_mask (bfn wa) (str.toNat + 1) result.ins_h ∧ ByteFrame h after (fun i => i = ds) ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨w0, p, q, bytes, pa, qa, env, H⟩ := heap_chains_environment good chains
  have windowId : w0 = w := by
    simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using env.win.symm
  subst w0
  have arrayId : bytes = wa := Option.some.inj (env.wbytes.symm.trans get)
  subst bytes
  have extent := window_extent good win get
  have data : str.toNat + 3 ≤ d.strstart.toNat + d.lookahead.toNat := by omega
  obtain ⟨key, hi, insertRun, goodI, chainsI, formI⟩ := insert_string_good_chains good env H str
    good.inv.wsize good.inv.wmask (Nat.le_refl _) data (by omega) (by omega) form
  obtain ⟨other, _, _, exactRun⟩ := INSERT_STRING_ok good.live.hs env str (by omega) (by omega)
  have pair := Except.ok.inj (insertRun.symm.trans exactRun)
  have byteFrame : hi.bytes = h.bytes := congrArg (fun x => x.2.bytes) pair
  have stored : ByteFrame h hi (fun i => i = ds) := by
    have heapEq := congrArg Prod.snd pair
    change hi = _ at heapEq
    rw [heapEq]
    exact ⟨rfl, fun _ _ => rfl,
      fun i outside => by simp [upd_ne _ _ _ _ outside], fun _ _ => rfl⟩
  obtain ⟨shapeI, frameI, _liveI, allocI, nextI⟩ :=
    insert_string_run_full_storage good env str (by omega) (by omega) insertRun
  let result := pendingInsertState d key
  let after := setD hi ds result
  have inv : DStInv hi ds result :=
    { goodI.inv with blocks := goodI.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  have goodA : DGood after r ds z result := goodI.setD' rfl goodI.live.status inv (by trkeep)
  have chainsA : HeapChains after result (str.toNat + 1) := by
    obtain ⟨wb, pb, qb, a, pa0, qa0, hw, hp, hq, ha, hpa, hqa, hs⟩ := chainsI
    exact ⟨wb, pb, qb, a, pa0, qa0, hw, hp, hq, ha, hpa, hqa, hs⟩
  have next : (str + 1).toNat = str.toNat + 1 := by
    rw [UInt32.toNat_add]
    simp only [show (1 : UInt32).toNat = 1 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  have count : result.insert.toNat = d.insert.toNat - 1 := u32_sub_one positive
  have write : wr (some (.tab ds)) (fun state => { state with insert := state.insert - 1 }) hi =
      .ok ((), after) := by
    simp [wrD_eq, goodI.live.hs, after, result, pendingInsertState]
  have shapeD := shape_setD goodI.live.hs result
  have shapeA := shapeI.trans shapeD
  have frameD : Frame hi after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) :=
    full_frame_weaken (state_store_full_frame hi ds result) (fun _ same => Or.inr (Or.inl same))
  have frameA := full_frame_trans_shape frameI frameD shapeI
  refine ⟨key, after, ?_, goodA, chainsA, byteFrame, next, count, formI,
    stored.trans (byte_frame_setD hi ds result), shapeA, frameA, full_shape_live_change shapeA, allocI, nextI⟩
  unfold fillInsertBody
  simp only [bind_app, insertRun, write, ldDeflateState_tab goodA.live.hs, pure_app]
  rfl

end Zlib.Deflate.Engine.Proofs
