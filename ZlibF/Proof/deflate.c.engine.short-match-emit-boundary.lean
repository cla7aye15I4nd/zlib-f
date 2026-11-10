import ZlibF.Proof.«deflate.c.engine.short-match-words»
import ZlibF.Proof.«deflate.c.engine.short-match-frontier»
import ZlibF.Proof.«deflate.c.engine.short-literal-full-boundary»

/-! # The actual selected match prefix at every remaining-input length -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The source tally and match consumption, before the optional flush. -/
def slowMatchEmit (s : DeflateStatePtr) (hash_head : UInt32) : M (Bool × UInt32) := do
  let d ← ldDeflateState s
  let bflush ← tally_dist s (d.strstart - 1 - d.prev_match) (d.prev_length - MIN_MATCH_u)
  let head ← slowMatchAdvance s (d.strstart + d.lookahead - MIN_MATCH_u) hash_head
  pure (bflush, head)

/-- The actual selected decision uses this prefix in source order. -/
theorem slow_decision_match_source {h : Heap} {ds : Nat} {d : DeflateState}
    (live : h.dstates ds = some d)
    (selected : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = true)
    (flush : Int32) (st : LoopS) (candidate : UInt32) :
    slowDecision (some (.tab ds)) flush st candidate h = (do
      let (bflush, head) ← slowMatchEmit (some (.tab ds)) candidate
      if bflush then
        if let some r := (← FLUSH_BLOCK (some (.tab ds)) 0) then
          return { st with hash_head := head, bflush, ret := some r }
      return { st with hash_head := head, bflush }) h := by
  unfold slowDecision slowMatchEmit
  simp only [M_bind_assoc, M_pure_bind]
  simp only [bind_app, ldDeflateState_tab live, selected, ite_true]
  rfl

set_option maxHeartbeats 1500000 in
/-- Real selected-match tally and consumption restore the content and EOF
boundaries even at two remaining bytes. If a short path has pending
positions, its no-word-write execution preserves their earlier frontier.
The following optional publication is a separate source cutpoint. -/
theorem slow_match_emit_search_boundary {h : Heap} {r : ZStreamRef} {ds w origin base : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r)
    (selected : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = true)
    (strict : d.sym_next.toNat < d.sym_end.toNat) (hash_head : UInt32) :
    ∃ candidate after result,
      slowMatchEmit (some (.tab ds)) hash_head h =
        .ok ((d.sym_next + 3 == d.sym_end, candidate), after) ∧
      ContentBoundary after r ds z result input origin base (xs ++ [emittedMatch d]) ∧
      EndFrontier after result ∧ StreamBuffers after r ∧ SlowRecordFrame d result ∧
      result.match_available = 0 ∧ result.strstart.toNat = d.strstart.toNat + (d.prev_length.toNat - 1) ∧
      result.lookahead.toNat = d.lookahead.toNat - (d.prev_length.toNat - 1) ∧ fillEnd result = fillEnd d ∧
      result.sym_next.toNat = d.sym_next.toNat + 3 ∧ result.sym_end = d.sym_end ∧
      ByteFrame h after (DeflateOwned ds d) := by
  have previous : 3 ≤ d.prev_length.toNat := by
    have guard := selected
    simp only [Bool.and_eq_true, decide_eq_true_eq] at guard
    exact UInt32.le_iff_toNat_le.mp guard.1
  have past := cut.previous.2 previous
  have oldStart := past.1
  have available := past.2.1
  have window : d.w_size.toNat ≤ 32768 := by
    rw [cut.good.inv.wsize]
    exact Nat.pow_le_pow_right (by decide) cut.good.inv.wbits_hi
  have bounds := logical_previous_tally_bounds cut.previous previous window
  let distance := d.strstart - 1 - d.prev_match
  let length := d.prev_length - MIN_MATCH_u
  have distancePositive : 1 ≤ distance.toNat := bounds.1
  have lengthBound : length.toNat ≤ 255 := bounds.2.2.2.1
  obtain ⟨b, buf, trees, ledger, balance⟩ := cut.symbols
  have credit : deferredCredit d = 1 := by simp only [deferredCredit, available, ite_false]
  rw [credit] at balance
  have room := literal_room cut.good.inv strict
  let packed := matchBytes buf d distance.toUInt16 length.toUInt8
  let dt := matchSymbolState d distance length
  let ht := setD (Zlib.Trees.Proofs.Out.setB h b packed) ds dt
  have goodT : DGood ht r ds z dt := match_good_after cut.good trees distance length room
  have chainsT : HeapChains ht dt (min (d.strstart.toNat + 1) (fillEnd d - 2)) :=
    pending_write_chains cut.good cut.end_frontier trees.base.pbuf packed 0
  have pendingT : HeapChains ht dt (d.strstart.toNat + 1 - d.insert.toNat) :=
    pending_write_chains cut.good cut.frontier trees.base.pbuf packed 0
  have getT : ht.bytes w = some wa := pending_window_frame cut.good cut.window trees.base.pbuf cut.bytes packed dt
  have count : dt.sym_next.toNat = d.sym_next.toNat + 3 := literal_count trees.base room 0
  have tally : tally_dist (some (.tab ds)) distance length h = .ok (d.sym_next + 3 == d.sym_end, ht) :=
    tally_match_run trees.base distance length bounds.1 bounds.2.1 room
  have endPositive : 3 ≤ d.strstart.toNat + d.lookahead.toNat := by
    have remaining := bounds.2.2.2.2
    omega
  obtain ⟨candidate, after, result, advance, goodA, chainsA, endA, winA, bytesA, flagA, lenA, _prevA,
      startA, lookA, endpoint, rangeA, formA, keep, _high, bytesFrame, blockFrame, literalFrame, distanceFrame, recordA, storageA⟩ :=
    slow_match_advance_frontier goodT chainsT cut.window getT previous cut.previous.1 bounds.2.2.2.2
      endPositive cut.range (by intro enough; apply cut.primed; change d.strstart.toNat + 1 ≤ d.strstart.toNat + d.lookahead.toNat - 3 at enough; omega) hash_head
  change result.strstart.toNat = d.strstart.toNat + (d.prev_length.toNat - 1) at startA
  change result.lookahead.toNat = d.lookahead.toNat - (d.prev_length.toNat - 1) at lookA
  change fillEnd result = fillEnd d at endpoint
  change result.block_start = d.block_start at blockFrame
  have frame : SlowRecordFrame d result := by
    unfold SlowRecordFrame
    rw [recordA]
    rfl
  have insertA : result.insert = d.insert := by rw [frame]
  have countA : result.sym_next.toNat = d.sym_next.toNat + 3 := by
    have equal : result.sym_next = dt.sym_next := keep.2.2.2.2.2.2.2.2.2.2
    rw [equal]; exact count
  have endCount : result.sym_end = d.sym_end := by rw [frame]
  have pendingA : HeapChains after result (result.strstart.toNat - result.insert.toNat) := by
    by_cases ready : 3 ≤ d.lookahead.toNat
    · have zero := cut.ready ready
      simpa only [insertA, zero, show (0 : UInt32).toNat = 0 from rfl, Nat.sub_zero] using chainsA
    · have remaining := bounds.2.2.2.2
      have threePrev : d.prev_length.toNat = 3 := by omega
      have twoLook : d.lookahead.toNat = 2 := by omega
      have words := slow_match_two_remaining_words goodT cut.window getT cut.range oldStart
        (UInt32.toNat_inj.mp threePrev) (UInt32.toNat_inj.mp twoLook) advance
      have retained : HeapChainsAt after result (d.strstart.toNat + 1 - d.insert.toNat) (fillEnd d) :=
        pendingT.at.keep bytesFrame words
          (by rw [recordA]) (by rw [recordA]) (by rw [recordA])
          (by rw [recordA]) (by rw [recordA]) (by rw [recordA]) (by rw [recordA])
      have collapsed : HeapChains after result (d.strstart.toNat + 1 - d.insert.toNat) :=
        retained.collapse endpoint.symm
      apply heap_chains_raise collapsed
      rw [insertA, startA]
      omega
  have ledgerT : SymbolLedger packed dt (xs ++ [emittedMatch d]) :=
    ledger_match trees.base ledger room distance length bounds.1 bounds.2.1 (by omega)
  have ledgerA : SymbolLedger packed result (xs ++ [emittedMatch d]) :=
    ledgerT.keep keep.2.2.2.2.2.2.2.2.2.2 keep.2.2.2.1 literalFrame distanceFrame
  have getPacked : after.bytes b = some packed := by rw [bytesFrame]; simp [ht]
  have representedMatch : (emittedMatch d).bytes = d.prev_length.toNat := by
    change (if distance.toNat = 0 then 1 else length.toNat + 3) = _
    rw [if_neg (by omega)]
    have exactLength : length.toNat = d.prev_length.toNat - 3 := bounds.2.2.1
    omega
  have balanceA : BlockBalance result (xs ++ [emittedMatch d]) (deferredCredit result) := by
    simp only [deferredCredit, flagA, ite_true]
    unfold BlockBalance at balance ⊢
    rw [represented_snoc, representedMatch, blockFrame, startA]
    omega
  have pendingBufA : result.pending_buf = .ref (.blk b) 0 := keep.1.trans trees.base.pbuf
  have symbolsA := symbol_boundary_of_ledger goodA pendingBufA getPacked ledgerA balanceA
  let retained : DeflateState := { d with match_start := d.prev_match, match_length := d.prev_length }
  have oldHistory : LazyHistory input origin retained := cut.previous
  have meaning := retained_match_input_meaning oldHistory window previous
  change (emittedMatch d).Meaning input (origin + d.strstart.toNat - 1) at meaning
  have accounted : base + represented xs + 1 = origin + d.strstart.toNat := by
    simpa only [pendingCredit, available, ite_false] using cut.accounted
  have oldEnd : base + represented xs = origin + d.strstart.toNat - 1 := by omega
  rw [← oldEnd] at meaning
  have traceA := cut.trace.snoc meaning
  have storage := (pending_state_byte_frame h ds b d dt packed trees.base.pbuf).trans
    (storageA.weaken (fun _ equal => Or.inl equal))
  have owned := stream_owned_keys cut.good goodA
    (by rw [frame]) (by rw [frame]) (by rw [frame]) (by rw [frame])
  have buffersA := stream_buffers_private_read cut.good.live.hz goodA.live.hz buffers storage
    (fun k own => (stream_owned_deflate cut.good k).mpr own) owned (stream_accounting_zero z)
  refine ⟨candidate, after, result, ?_, ?_, endA, buffersA, frame, flagA, startA, lookA,
    endpoint, countA, endCount, storage⟩
  · have advance' : slowMatchAdvance (some (.tab ds)) (d.strstart + d.lookahead - MIN_MATCH_u) hash_head ht =
        .ok (candidate, after) := advance
    dsimp only [distance, length] at tally
    unfold slowMatchEmit
    simp only [bind_app, ldDeflateState_tab cut.good.live.hs, tally, advance', pure_app]
  · refine ⟨⟨⟨goodA, chainsA, rangeA, logical_history_initial lenA input origin, ?_, symbolsA, ?_⟩,
      ?_, pendingA, ?_⟩, traceA, ?_⟩
    · intro has; exact False.elim (has flagA)
    · refine ⟨w, wa, winA, bytesA, ?_, formA⟩
      intro i fit; rw [endpoint] at fit; exact cut.view i fit
    · rw [insertA, startA]
      have bound := cut.insert_le
      omega
    · intro enough
      rw [insertA]
      apply cut.ready
      rw [lookA] at enough
      omega
    · simp only [pendingCredit, flagA, ite_true, Nat.add_zero]
      rw [represented_snoc, representedMatch, startA]
      omega

end Zlib.Deflate.Engine.Proofs
