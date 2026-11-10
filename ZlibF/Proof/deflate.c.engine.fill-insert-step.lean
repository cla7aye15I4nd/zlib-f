import ZlibF.Proof.«deflate.c.engine.fill-insert-source»
import ZlibF.Proof.«deflate.c.engine.caller-frame»

/-! # One actual deferred insertion at the pending hash frontier -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

def pendingInsertState (d : DeflateState) (key : UInt32) : DeflateState :=
  { d with ins_h := key, insert := d.insert - 1 }

theorem pending_sum_nat {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (pending : d.insert.toNat ≤ d.strstart.toNat) :
    (d.lookahead + d.insert).toNat = d.lookahead.toNat + d.insert.toNat := by
  have extent := window_extent good win get
  rw [UInt32.toNat_add, Nat.mod_eq_of_lt (by omega)]

/-- The loop's cursor is before strstart, not the current match position.
The lower-frontier chain invariant justifies inserting exactly this cursor.
All non-word storage and all record fields except insert/ins_h are retained.
-/
theorem fill_insert_step_storage {h : Heap} {r : ZStreamRef} {ds w : Nat}
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
      InsHForm result.hash_shift result.hash_mask (bfn wa) (str.toNat + 1) result.ins_h ∧ ByteFrame h after (fun i => i = ds) := by
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
  refine ⟨key, after, ?_, goodA, chainsA, byteFrame, next, count, formI, stored.trans (byte_frame_setD hi ds result)⟩
  unfold fillInsertBody
  simp only [bind_app, insertRun, write, ldDeflateState_tab goodA.live.hs, pure_app]
  rfl

/-- The original step statement follows from the same actual execution,
which additionally retains external byte storage. -/
theorem fill_insert_step {h : Heap} {r : ZStreamRef} {ds w : Nat}
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
      InsHForm result.hash_shift result.hash_mask (bfn wa) (str.toNat + 1) result.ins_h := by
  obtain ⟨key, after, run, goodA, chainsA, bytesA, next, count, formA, _⟩ :=
    fill_insert_step_storage str brk good chains win get range cursor positive ready form
  exact ⟨key, after, run, goodA, chainsA, bytesA, next, count, formA⟩

end Zlib.Deflate.Engine.Proofs
