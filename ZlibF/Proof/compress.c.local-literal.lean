import ZlibF.Proof.«compress.c.local-hash»
import ZlibF.Proof.«deflate.c.engine.slow-literal»
import ZlibF.Proof.«deflate.c.engine.symbol-ledger»
import ZlibF.Proof.«deflate.c.engine.slow-symbols»

/-! # Actual deferred literal emission with local private representation

The original previous-byte read, packed symbol stores, frequency increment
and byte advance execute in order. The full-buffer branch remains separate.
-/
namespace ZlibF.Spec.Public.Proofs.CompressLocalLiteral
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalInit ZlibF.Spec.Public.Proofs.CompressLocalHeader
open ZlibF.Spec.Public.Proofs.CompressLocalHash
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 100000

theorem local_advance_one {h : Heap} {r : ZStreamRef} {cutoff ds top : Nat} {z : ZStream} {d : DeflateState}
    (good : LocalState h cutoff r ds z d) (chains : HeapChains h d top)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (positive : 1 ≤ d.lookahead.toNat) :
    LocalState (setD h ds (advanceOne d)) cutoff r ds z (advanceOne d) ∧
      HeapChains (setD h ds (advanceOne d)) (advanceOne d) top ∧
      (advanceOne d).strstart.toNat + (advanceOne d).lookahead.toNat ≤ (advanceOne d).window_size.toNat := by
  have counts := advance_one_counts good.inv range positive
  have inv : DStInv h ds (advanceOne d) :=
    { good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  refine ⟨local_state_setD good (d' := advanceOne d) rfl good.live.status inv (by trkeep), ?_, ?_⟩
  · obtain ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, H⟩ := chains
    refine ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, ?_⟩
    change HashChains (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask d.w_size.toNat top
      ((advanceOne d).strstart.toNat + (advanceOne d).lookahead.toNat)
    rw [counts.2.2]
    exact H
  · rw [counts.2.2]
    exact range

theorem local_literal_after {h : Heap} {r : ZStreamRef} {cutoff ds b : Nat} {z : ZStream}
    {d : DeflateState} {buf : Array UInt8} (good : LocalState h cutoff r ds z d)
    (trees : TreesInvAt h ds d b buf) (c : UInt8) (room : d.sym_next.toNat + 3 ≤ d.sym_end.toNat) :
    LocalState (setD (Zlib.Trees.Proofs.Out.setB h b (literalBytes buf d c)) ds (literalState d c))
      cutoff r ds z (literalState d c) := by
  have treeResult := tally_literal_trees trees c room
  let hb := Zlib.Trees.Proofs.Out.setB h b (literalBytes buf d c)
  let dt := literalState d c
  have goodB : LocalState hb cutoff r ds z d := local_state_bytes_set good b (literalBytes buf d c) buf trees.base.bytes
    (by simp [literalBytes])
  have inv : DStInv hb ds dt :=
    { goodB.inv with
      wf := treeResult.base.wf
      blocks := goodB.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      sym := ⟨goodB.inv.sym.1, goodB.inv.sym.2.1, treeResult.run.sym_next_le, treeResult.run.sym_next_mod⟩ }
  have shape := shape_setD goodB.live.hs dt
  refine ⟨?_, DStInv.congr (h := hb) (h' := setD hb ds dt) rfl rfl rfl rfl inv,
    goodB.newUnique.shape shape, shape.fresh rfl goodB.fresh, ⟨dt, b, literalBytes buf d c, treeResult⟩⟩
  exact ⟨by simpa only [ZStreamRef.get_setD] using goodB.live.hz, by simp, good.live.zst,
    good.live.back, good.live.status, good.live.zalloc, good.live.zfree⟩

theorem local_pending_write_chains {h : Heap} {r : ZStreamRef} {cutoff ds top b : Nat}
    {z : ZStream} {d : DeflateState} (good : LocalState h cutoff r ds z d) (chains : HeapChains h d top)
    (pending : d.pending_buf = .ref (.blk b) 0) (buf : Array UInt8) (c : UInt8) :
    HeapChains (setD (Zlib.Trees.Proofs.Out.setB h b buf) ds (literalState d c)) (literalState d c) top := by
  obtain ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, H⟩ := chains
  obtain ⟨w0, p0, q0, b0, blocks⟩ := good.inv.blocks
  have we : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
  have be : b0 = b := by simpa only [pending, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.pbuf.symm
  subst w0 b0
  exact ⟨w, p, q, wa, pa, qa, win, prev, head,
    by simpa [Zlib.Trees.Proofs.Out.setB, upd_ne _ _ _ _ blocks.wb] using hw,
    hp, hq, H⟩

theorem local_pending_window_frame {h : Heap} {r : ZStreamRef} {cutoff ds w b : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : LocalState h cutoff r ds z d) (win : d.window = .ref (.blk w) 0)
    (pending : d.pending_buf = .ref (.blk b) 0) (get : h.bytes w = some wa)
    (buf : Array UInt8) (state : DeflateState) :
    (setD (Zlib.Trees.Proofs.Out.setB h b buf) ds state).bytes w = some wa := by
  obtain ⟨w0, p, q, b0, blocks⟩ := good.inv.blocks
  have wid : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
  have bid : b0 = b := by simpa only [pending, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.pbuf.symm
  subst w0 b0
  simpa [Zlib.Trees.Proofs.Out.setB, upd_ne _ _ _ _ blocks.wb] using get

theorem local_slow_literal_boundary {h : Heap} {r : ZStreamRef} {cutoff ds w top : Nat}
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
      (advanceOne (literalState d c)).sym_next.toNat < (advanceOne (literalState d c)).sym_end.toNat := by
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
  refine ⟨after, ?_, advanced.1, advanced.2.1, advanced.2.2, ?_, literal_not_full trees c room flag⟩
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

/-- The actual packed stores and literal-frequency increment extend the
same semantic symbol ledger. No callee contract is assumed. The ledger is
an internal representation fact, not an added public API condition. -/
theorem local_tally_literal_semantics {h : Heap} {r : ZStreamRef} {cutoff ds b : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (state : LocalState h cutoff r ds z d) (trees : TreesInvAt h ds d b buf)
    (ledger : SymbolLedger buf d xs) (room : d.sym_next.toNat+3 ≤ d.sym_end.toNat) (c : UInt8) :
    let after := setD (Zlib.Trees.Proofs.Out.setB h b (literalBytes buf d c)) ds (literalState d c)
    tally_lit (some (.tab ds)) c h = .ok (d.sym_next+3 == d.sym_end,after) ∧
      LocalState after cutoff r ds z (literalState d c) ∧
      SymbolLedger (literalBytes buf d c) (literalState d c) (xs++[⟨0,c.toNat⟩]) ∧
      Shape h after ∧ Frame h after (fun owner => owner = ds ∨ owner = b) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  have actual := tally_literal_ledger trees.base ledger room c
  have bytesShape := shape_setB trees.base.bytes (literalBytes buf d c)
  have shape := bytesShape.trans (shape_setD (h := Zlib.Trees.Proofs.Out.setB h b (literalBytes buf d c))
    (by simpa using state.live.hs) (literalState d c))
  have byteFrame : Frame h (Zlib.Trees.Proofs.Out.setB h b (literalBytes buf d c))
      (fun owner => owner = ds ∨ owner = b) :=
    full_frame_weaken (byte_store_full_frame h b _) (fun _ same => Or.inr same)
  have stateFrame : Frame (Zlib.Trees.Proofs.Out.setB h b (literalBytes buf d c))
      (setD (Zlib.Trees.Proofs.Out.setB h b (literalBytes buf d c)) ds (literalState d c))
      (fun owner => owner = ds ∨ owner = b) :=
    full_frame_weaken (state_store_full_frame _ ds _) (fun _ same => Or.inl same)
  exact ⟨actual.1,local_literal_after state trees c room,actual.2,shape,
    full_frame_trans_shape byteFrame stateFrame bytesShape,full_shape_live_change shape,rfl,rfl⟩

theorem local_trees_at_buffer {h : Heap} {r : ZStreamRef} {cutoff ds b : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : LocalState h cutoff r ds z d)
    (pending : d.pending_buf = .ref (.blk b) 0) (get : h.bytes b = some buf) : TreesInvAt h ds d b buf := by
  obtain ⟨d0, b0, buf0, trees⟩ := good.trees
  have state : d0 = d := Option.some.inj (trees.base.dstate.symm.trans good.live.hs)
  subst d0
  have block : b0 = b := by simpa only [pending, Ptr.ref.injEq, BRef.blk.injEq, and_true] using trees.base.pbuf.symm
  subst b0
  have array : buf0 = buf := Option.some.inj (trees.base.bytes.symm.trans get)
  subst buf0
  exact trees

theorem local_symbol_boundary_of_ledger {h : Heap} {r : ZStreamRef} {cutoff ds b : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : LocalState h cutoff r ds z d) (pending : d.pending_buf = .ref (.blk b) 0) (get : h.bytes b = some buf)
    (ledger : SymbolLedger buf d xs) (balance : BlockBalance d xs (deferredCredit d)) :
    SymbolBoundary h ds d xs := ⟨b, buf, local_trees_at_buffer good pending get, ledger, balance⟩


/-- The complete actual deferred-literal decision preserves the packed
symbols, exact leaf frequencies and consumed/deferred-byte balance together. -/
theorem local_slow_literal_symbol_storage {h : Heap} {r : ZStreamRef} {cutoff ds w top : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {xs : List Symbol}
    (good : LocalState h cutoff r ds z d) (symbol : SymbolBoundary h ds d xs) (chains : HeapChains h d top)
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
      SymbolBoundary after ds (advanceOne (literalState d c)) (xs ++ [emittedLiteral d wa]) ∧
      SlowRecordFrame d (advanceOne (literalState d c)) ∧ ByteFrame h after (DeflateOwned ds d) := by
  let c := wa[d.strstart.toNat - 1]!
  obtain ⟨b, buf, trees, ledger, balance⟩ := symbol
  have credit : deferredCredit d = 1 := by simp [deferredCredit, available]
  rw [credit] at balance
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
  have ledgerT : SymbolLedger (literalBytes buf d c) (literalState d c) (xs ++ [emittedLiteral d wa]) :=
    ledger_literal trees.base ledger room c
  have ledgerA : SymbolLedger (literalBytes buf d c) (advanceOne (literalState d c))
      (xs ++ [emittedLiteral d wa]) := ledgerT.keep rfl rfl rfl rfl
  have creditA : deferredCredit (advanceOne (literalState d c)) = 1 := by
    simp [deferredCredit, advanceOne, literalState, available]
  have balanceA : BlockBalance (advanceOne (literalState d c)) (xs ++ [emittedLiteral d wa])
      (deferredCredit (advanceOne (literalState d c))) := by
    rw [creditA]
    exact balance_advance_one goodT.inv range positive (balance_literal balance c)
  have getA : after.bytes b = some (literalBytes buf d c) := by simp [after, ht]
  have symbolA := local_symbol_boundary_of_ledger advanced.1 trees.base.pbuf getA ledgerA balanceA
  have storageA : ByteFrame h after (DeflateOwned ds d) :=
    (pending_state_byte_frame h ds b d (literalState d c) (literalBytes buf d c) trees.base.pbuf).trans
      ((byte_frame_setD ht ds (advanceOne (literalState d c))).weaken (fun _ equal => Or.inl equal))
  refine ⟨after, ?_, advanced.1, advanced.2.1, advanced.2.2, ?_, literal_not_full trees c room flag, symbolA, rfl, storageA⟩
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


end ZlibF.Spec.Public.Proofs.CompressLocalLiteral
