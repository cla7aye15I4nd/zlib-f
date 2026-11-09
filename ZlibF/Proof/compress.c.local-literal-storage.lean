import ZlibF.Proof.«compress.c.local-literal»
import ZlibF.Proof.«deflate.c.engine.full-storage»

/-! # Complete typed effects of the actual local nonfull literal decision

The packed symbol bytes and literal frequency are written before the input
position advances. The same resulting heap preserves the owned root pointers
and every represented slot outside the private footprint. No output is written.
-/
namespace ZlibF.Spec.Public.Proofs.CompressLocalLiteralStorage
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalInit
open ZlibF.Spec.Public.Proofs.CompressLocalLiteral
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false
set_option maxRecDepth 100000

theorem local_slow_literal_full_storage {h : Heap} {r : ZStreamRef} {cutoff ds w top : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : LocalState h cutoff r ds z d) (chains : HeapChains h d top)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (positive : 1 ≤ d.lookahead.toNat) (previousByte : 1 ≤ d.strstart.toNat)
    (literalBranch : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = false)
    (available : d.match_available ≠ 0)
    (space : d.sym_next.toNat + 3 < d.sym_end.toNat)
    (flush : Int32) (st : LoopS) (hash_head : UInt32) :
    let c := wa[d.strstart.toNat - 1]!
    ∃ after,
      slowDecision (some (.tab ds)) flush st hash_head h =
        .ok ((if z.avail_out == 0 then { st with hash_head, bflush := false, ret := some need_more }
          else { st with hash_head, bflush := false }), after) ∧
      LocalState after cutoff r ds z (advanceOne (literalState d c)) ∧
      HeapChains after (advanceOne (literalState d c)) top ∧
      (advanceOne (literalState d c)).strstart.toNat + (advanceOne (literalState d c)).lookahead.toNat ≤
        (advanceOne (literalState d c)).window_size.toNat ∧
      after.bytes w = some wa ∧
      (advanceOne (literalState d c)).sym_next.toNat < (advanceOne (literalState d c)).sym_end.toNat ∧
      SlowRecordFrame d (advanceOne (literalState d c)) ∧
      (advanceOne (literalState d c)).window = d.window ∧
      (advanceOne (literalState d c)).prev = d.prev ∧
      (advanceOne (literalState d c)).head = d.head ∧
      (advanceOne (literalState d c)).pending_buf = d.pending_buf ∧
      Shape h after ∧ Frame h after (fun key => StreamRoot r key ∨ DeflateOwned ds d key) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk ∧
      ∃ b buf, TreesInvAt h ds d b buf ∧
        after = setD (setD (Zlib.Trees.Proofs.Out.setB h b (literalBytes buf d c)) ds
          (literalState d c)) ds (advanceOne (literalState d c)) := by
  let c := wa[d.strstart.toNat - 1]!
  obtain ⟨d0, b, buf, trees⟩ := good.trees
  have same : d0 = d := Option.some.inj (trees.base.dstate.symm.trans good.live.hs)
  subst d0
  have strict : d.sym_next.toNat < d.sym_end.toNat := by omega
  have room := literal_room good.inv strict
  let ht := setD (Zlib.Trees.Proofs.Out.setB h b (literalBytes buf d c)) ds (literalState d c)
  have goodT : LocalState ht cutoff r ds z (literalState d c) := local_literal_after good trees c room
  have chainsT : HeapChains ht (literalState d c) top :=
    local_pending_write_chains good chains trees.base.pbuf _ c
  have count := literal_count trees.base room c
  have flag : (d.sym_next + 3 == d.sym_end) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro eq
    have num := congrArg UInt32.toNat eq
    change (literalState d c).sym_next.toNat = d.sym_end.toNat at num
    rw [count] at num
    omega
  have tally : tally_lit (some (.tab ds)) c h = .ok (false, ht) := by
    simpa only [flag] using tally_literal_run trees.base c room
  obtain ⟨w0, p, q, b0, blocks⟩ := good.inv.blocks
  have wid : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
  subst w0
  obtain ⟨wa0, get0, size⟩ := blocks.wa
  have array : wa0 = wa := Option.some.inj (get0.symm.trans get)
  subst wa0
  have fit : d.strstart.toNat - 1 < wa.size := by rw [good.inv.wsz] at range; omega
  have sub : (d.strstart - 1).toNat = d.strstart.toNat - 1 := u32_sub_one previousByte
  have read : index8 d.window (d.strstart - 1).toNat h = .ok (c, h) := by
    rw [win, sub]
    simpa [OkOn, fit, c] using index8_ok (off := 0)
      (i := d.strstart.toNat - 1) get (by omega)
  have advanced := local_advance_one goodT chainsT range positive
  let after := setD ht ds (advanceOne (literalState d c))
  have write : wr (some (.tab ds)) advanceOne ht = .ok ((), after) := by
    simp [wrD_eq, goodT.live.hs, after]
  have output : zrd (some r) (·.avail_out) after = .ok (z.avail_out, after) := by
    have getter : r.get after = some z := advanced.1.live.hz
    simp only [zrd_eq, getter]
  have storage : OutputStorage h ht r ds b b := output_bits_storage good.live.hs trees.base.bytes
  have shape := storage.shape.trans (shape_setD goodT.live.hs (advanceOne (literalState d c)))
  have frameT : Frame h ht (fun key => StreamRoot r key ∨ DeflateOwned ds d key) := by
    apply full_frame_weaken storage.frame
    intro key changed
    rcases changed with root | same | same | same
    · exact Or.inl root
    · exact Or.inr (Or.inl same)
    · subst key; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
    · subst key; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
  have frameD : Frame ht after (fun key => StreamRoot r key ∨ DeflateOwned ds d key) :=
    full_frame_weaken (state_store_full_frame ht ds _) (fun _ same => Or.inr (Or.inl same))
  refine ⟨after, ?_, advanced.1, advanced.2.1, advanced.2.2, ?_, literal_not_full trees c room flag,
    rfl, rfl, rfl, rfl, rfl, shape, full_frame_trans_shape frameT frameD storage.shape,
    full_shape_live_change shape, rfl, rfl, b, buf, trees, rfl⟩
  · unfold slowDecision
    simp only [bind_app, ldDeflateState_tab good.live.hs, literalBranch, Bool.false_eq_true, ite_false]
    have hasLiteral : (d.match_available != 0) = true := by simpa using available
    simp only [hasLiteral, ite_true, bind_app, read, tally, Bool.false_eq_true, ite_false]
    change (do
      wr (some (.tab ds)) advanceOne
      if (← zrd d.strm (·.avail_out)) == 0 then
        return { st with hash_head, bflush := false, ret := some need_more }
      return { st with hash_head, bflush := false }) ht = _
    rw [bind_app, write]
    simp only [good.live.back, bind_app, output]
    by_cases full : (z.avail_out == 0) = true <;> simp [full]
  · exact local_pending_window_frame good win trees.base.pbuf get (literalBytes buf d c)
      (advanceOne (literalState d c))

end ZlibF.Spec.Public.Proofs.CompressLocalLiteralStorage
