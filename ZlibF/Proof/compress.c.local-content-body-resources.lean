import ZlibF.Proof.«compress.c.local-content»
import ZlibF.Proof.«compress.c.local-match-full-storage»
import ZlibF.Proof.«compress.c.local-literal-storage»

/-! # Typed resource observations of every ordinary local-content body

The actual insertion/search and all three ordinary decisions are composed
on the observed returned heap. The internal content invariant comes from
actual initialization/refills. No global caller uniqueness is required.
Full symbol-buffer publication and the refill branch remain separate.
-/
namespace ZlibF.Spec.Public.Proofs.CompressLocalContentBodyResources
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalInit ZlibF.Spec.Public.Proofs.CompressLocalHash
open ZlibF.Spec.Public.Proofs.CompressLocalSearch ZlibF.Spec.Public.Proofs.CompressLocalContent
open ZlibF.Spec.Public.Proofs.CompressLocalLiteral
open ZlibF.Spec.Public.Proofs.CompressLocalMatchFullStorage
open ZlibF.Spec.Public.Proofs.CompressLocalLiteralStorage
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

/-- On the same real body execution, insertion/search followed by defer,
literal or a selected match preserves the complete typed footprint,
object occupancy and allocation counters. The lookahead and symbol room
are internal ordinary-body conditions, not added public caller premises. -/
theorem local_content_body_resources {h after : Heap} {r : ZStreamRef}
    {cutoff ds origin base : Nat} {z za : ZStream} {d da : DeflateState}
    {input : Nat → UInt8} {xs : List Symbol} {next : LoopS}
    (boundary : LocalContent h cutoff r ds z d input origin base xs)
    (lookahead : 262 ≤ d.lookahead.toNat) (space : d.sym_next.toNat + 3 < d.sym_end.toNat)
    (flush : Int32) (st : LoopS)
    (actual : deflate_slow_body (some (.tab ds)) flush st h = .ok (next,after))
    (returned : DLive after r ds za da) :
    SlowRecordFrame d da ∧ DeflateOwned ds da = DeflateOwned ds d ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨_, producedHeap, producedState, _, producedRun, producedBoundary, producedRecord, _⟩ :=
    local_content_body boundary lookahead space flush st
  have heapEq : producedHeap = after :=
    congrArg Prod.snd (Except.ok.inj (producedRun.symm.trans actual))
  rw [heapEq] at producedBoundary
  have sameStream : z = za :=
    Option.some.inj (producedBoundary.state.live.hz.symm.trans returned.hz)
  subst za
  have sameState : producedState = da :=
    Option.some.inj (producedBoundary.state.live.hs.symm.trans returned.hs)
  have record : SlowRecordFrame d da := by simpa only [sameState] using producedRecord
  have owned : DeflateOwned ds da = DeflateOwned ds d := by
    unfold SlowRecordFrame at record
    rw [record]
    rfl
  obtain ⟨w,p,q,wa,pa,qa,env,chains⟩ :=
    local_heap_chains_environment boundary.state boundary.chains
  obtain ⟨w0,wa0,win,get,_view,form⟩ := boundary.data
  have sameWindow : w0 = w := by
    simpa only [env.win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using win.symm
  subst w0
  have sameArray : wa0 = wa := Option.some.inj (get.symm.trans env.wbytes)
  subst wa0
  have range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat := boundary.range
  obtain ⟨key,found,pos,len,search,goodF,chainsF,_lengthF,_clippedF,_quality,bytesF,
      formF,_byteFrameF,shapeF,frameF,_liveF,allocF,nextF⟩ :=
    local_slow_search_room boundary.state env chains (Nat.le_refl _) range
      (by omega) (by omega) boundary.history.1 (form (by omega))
  let df := matchState (lazyPrepare {d with ins_h := key}) pos len
  let candidate := (wfn qa key.toNat).toUInt32
  have getF : found.bytes w = some wa := by rw [bytesF]; exact env.wbytes
  have previousF : PreviousHistory input origin df := logical_prepare_history boundary.history key
  have symbolF : SymbolBoundary found ds df xs := by
    obtain ⟨b,buf,trees,ledger,balance⟩ := boundary.symbols
    have getB : found.bytes b = some buf := by rw [bytesF];exact trees.base.bytes
    have ledgerF : SymbolLedger buf df xs := ledger.keep rfl rfl rfl rfl
    exact local_symbol_boundary_of_ledger goodF trees.base.pbuf getB ledgerF balance
  have enough : ¬d.lookahead < MIN_LOOKAHEAD_u := by
    rw [UInt32.lt_iff_toNat_lt]
    change ¬d.lookahead.toNat < 262
    omega
  have decision : slowDecision (some (.tab ds)) flush st candidate found = .ok (next,after) := by
    rw [slow_body_source] at actual
    simpa only [bind_app,rdD_eq,boundary.state.live.hs,enough,ite_false,search] using actual
  have effects : Shape found after ∧
      Frame found after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      after.nalloc = found.nalloc ∧ after.nextBlk = found.nextBlk := by
    by_cases selected : (df.prev_length ≥ MIN_MATCH_u && df.match_length ≤ df.prev_length) = true
    · obtain ⟨_record,_owned,shape,frame,_live,alloc,nextBlk⟩ :=
        local_match_decision_run_full_storage goodF symbolF chainsF env.win getF previousF
          selected lookahead boundary.range formF space decision returned
      exact ⟨shape,frame,alloc,nextBlk⟩
    · have branch : (df.prev_length ≥ MIN_MATCH_u && df.match_length ≤ df.prev_length) = false :=
        Bool.eq_false_iff.mpr selected
      by_cases available : df.match_available = 0
      · have expected := slow_defer_branch goodF.live.hs branch available flush st candidate
        have heaps : setD found ds (deferOne df) = after :=
          congrArg Prod.snd (Except.ok.inj (expected.symm.trans decision))
        have shape := shape_setD goodF.live.hs (deferOne df)
        have frame : Frame found (setD found ds (deferOne df))
            (fun b => StreamRoot r b ∨ DeflateOwned ds d b) :=
          full_frame_weaken (state_store_full_frame found ds _)
            (fun _ same => Or.inr (Or.inl same))
        rw [←heaps]
        exact ⟨shape,frame,rfl,rfl⟩
      · have previousByte : 1 ≤ df.strstart.toNat := boundary.deferred available
        obtain ⟨expected,decisionL,_stateL,_chainsL,_rangeL,_getL,_countL,_recordL,
            _winL,_prevL,_headL,_pendingL,shapeL,frameL,_liveL,allocL,nextL,_canonicalL⟩ :=
          local_slow_literal_full_storage goodF chainsF env.win getF boundary.range
            (by change 1 ≤ d.lookahead.toNat;omega) previousByte branch available space flush st candidate
        have heaps : expected = after :=
          congrArg Prod.snd (Except.ok.inj (decisionL.symm.trans decision))
        rw [heaps] at shapeL frameL allocL nextL
        exact ⟨shapeL,frameL,allocL,nextL⟩
  have shape := shapeF.trans effects.1
  exact ⟨record,owned,shape,full_frame_trans_shape frameF effects.2.1 shapeF,
    full_shape_live_change shape,effects.2.2.1.trans allocF,effects.2.2.2.trans nextF⟩

#print axioms local_content_body_resources
end ZlibF.Spec.Public.Proofs.CompressLocalContentBodyResources
