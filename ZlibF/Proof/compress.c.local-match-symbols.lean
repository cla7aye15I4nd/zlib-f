import ZlibF.Proof.«compress.c.local-match-ordinary»
import ZlibF.Proof.«compress.c.local-match-tally»

/-! # Actual selected-match decision using the local private representation -/
namespace ZlibF.Spec.Public.Proofs.CompressLocalMatchSymbols
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalInit ZlibF.Spec.Public.Proofs.CompressLocalLiteral
open ZlibF.Spec.Public.Proofs.CompressLocalMatchTally ZlibF.Spec.Public.Proofs.CompressLocalMatchOrdinary
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2500000

/-- The complete actual ordinary selected-match branch includes the real
distance/length tally and the entire bounded insertion/consumption loop.
PreviousHistory is an internal logical-history invariant, not a new caller
precondition of the public utility goal. Establishing it on the complete
Fresh streaming history remains a separate integration step. This theorem
returns the explicit byte frame; a full typed resource frame is not claimed. -/
theorem local_match_symbol_storage {h : Heap} {r : ZStreamRef} {cutoff ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    {input : Nat → UInt8} {origin : Nat} {xs : List Symbol}
    (good : LocalState h cutoff r ds z d) (symbol : SymbolBoundary h ds d xs)
    (chains : HeapChains h d (d.strstart.toNat + 1))
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (history : PreviousHistory input origin d)
    (selected : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = true)
    (lookahead : 262 ≤ d.lookahead.toNat)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) (d.strstart.toNat + 1) d.ins_h)
    (space : d.sym_next.toNat + 3 < d.sym_end.toNat)
    (flush : Int32) (st : LoopS) (hash_head : UInt32) :
    ∃ candidate after result,
      slowDecision (some (.tab ds)) flush st hash_head h =
        .ok ({ st with hash_head := candidate, bflush := false }, after) ∧
      LocalState after cutoff r ds z result ∧ HeapChains after result result.strstart.toNat ∧
      result.window = .ref (.blk w) 0 ∧ after.bytes w = some wa ∧
      result.match_available = 0 ∧ result.match_length = 2 ∧ result.prev_length = 0 ∧
      result.strstart.toNat = d.strstart.toNat + (d.prev_length.toNat - 1) ∧
      result.lookahead.toNat = d.lookahead.toNat - (d.prev_length.toNat - 1) ∧
      result.strstart.toNat + result.lookahead.toNat = d.strstart.toNat + d.lookahead.toNat ∧
      result.strstart.toNat + result.lookahead.toNat ≤ result.window_size.toNat ∧
      InsHForm result.hash_shift result.hash_mask (bfn wa) result.strstart.toNat result.ins_h ∧
      result.sym_next.toNat < result.sym_end.toNat ∧ LazyHistory input origin result ∧
      SymbolBoundary after ds result (xs ++ [emittedMatch d]) ∧ SlowRecordFrame d result ∧ ByteFrame h after (DeflateOwned ds d) := by
  have previous : 3 ≤ d.prev_length.toNat := by
    have guard := selected
    simp only [Bool.and_eq_true, decide_eq_true_eq] at guard
    exact UInt32.le_iff_toNat_le.mp guard.1
  have window : d.w_size.toNat ≤ 32768 := by
    rw [good.inv.wsize]
    calc 2 ^ d.w_bits.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) good.inv.wbits_hi
         _ = 32768 := by decide
  have bounds := logical_previous_tally_bounds history previous window
  let distance := d.strstart - 1 - d.prev_match
  let length := d.prev_length - MIN_MATCH_u
  have distancePositive : 1 ≤ distance.toNat := bounds.1
  have lengthBound : length.toNat ≤ 255 := bounds.2.2.2.1
  obtain ⟨b, buf, trees, ledger, balance⟩ := symbol
  have available : d.match_available ≠ 0 := (history.2 previous).2.1
  have credit : deferredCredit d = 1 := by simp [deferredCredit, available]
  rw [credit] at balance
  have room : d.sym_next.toNat + 3 ≤ d.sym_end.toNat := by omega
  let bytes := matchBytes buf d distance.toUInt16 length.toUInt8
  let dt := matchSymbolState d distance length
  let ht := setD (Zlib.Trees.Proofs.Out.setB h b bytes) ds dt
  obtain ⟨tallyRun,goodT,_treesT,tallyLedger,_tallyCount,_notFull,_tallyRecord,_shapeT,_frameT,_liveT,_allocT,_nextT,
      chainsKeep,_balanceT⟩ := local_tally_match_storage good trees ledger distance length bounds.1 bounds.2.1
    (by omega) room
  have chainsT : HeapChains ht dt (d.strstart.toNat+1) := chainsKeep _ chains
  have getT : ht.bytes w = some wa := local_pending_window_frame good win trees.base.pbuf get bytes dt
  have count : (d.sym_next + 3).toNat = d.sym_next.toNat + 3 := literal_count trees.base room 0
  have flag : (d.sym_next + 3 == d.sym_end) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro eq
    have num := congrArg UInt32.toNat eq
    rw [count] at num
    omega
  have tally : tally_dist (some (.tab ds)) distance length h = .ok (false, ht) := by
    simpa only [flag] using tallyRun
  obtain ⟨candidate, after, result, advance, goodA, chainsA, winA, bytesA, availableA, lengthA,
      previousA, startA, lookA, endpoint, rangeA, formA, keep, _, bytesFrame, blockFrame, literalFrame, distanceFrame, recordFrame, storageAdvance⟩ :=
    local_match_advance_storage goodT chainsT win getT previous history.1 lookahead range form hash_head
  have nextCount : result.sym_next.toNat < result.sym_end.toNat := by
    have next := literal_not_full trees 0 room flag
    have nextEq := keep.2.2.2.2.2.2.2.2.2.2
    have endEq := keep.2.2.2.2.1
    rw [nextEq, endEq]
    exact next
  have ledgerT : SymbolLedger bytes dt (xs ++ [emittedMatch d]) :=
    by simpa only [emittedMatch] using tallyLedger
  have ledgerA : SymbolLedger bytes result (xs ++ [emittedMatch d]) :=
    ledgerT.keep keep.2.2.2.2.2.2.2.2.2.2 keep.2.2.2.1 literalFrame distanceFrame
  have pendingA : result.pending_buf = .ref (.blk b) 0 := keep.1.trans trees.base.pbuf
  have dataA : after.bytes b = some bytes := by rw [bytesFrame]; simp [ht,bytes]
  have emittedSize : (emittedMatch d).bytes = d.prev_length.toNat := by
    change (if distance.toNat = 0 then 1 else length.toNat + 3) = _
    rw [ite_eq_right (by omega)]
    have len : length.toNat = d.prev_length.toNat - 3 := bounds.2.2.1
    omega
  have balanceA : BlockBalance result (xs ++ [emittedMatch d]) (deferredCredit result) := by
    have availableZero : deferredCredit result = 0 := by simp [deferredCredit, availableA]
    rw [availableZero]
    unfold BlockBalance at balance ⊢
    rw [represented_snoc, emittedSize]
    change result.block_start = d.block_start at blockFrame
    change result.strstart.toNat = d.strstart.toNat + (d.prev_length.toNat - 1) at startA
    rw [blockFrame, startA]
    omega
  have symbolA := local_symbol_boundary_of_ledger goodA pendingA dataA ledgerA balanceA
  have recordA : SlowRecordFrame d result := by
    unfold SlowRecordFrame
    rw [recordFrame]
    rfl
  have storageA : ByteFrame h after (DeflateOwned ds d) :=
    (pending_state_byte_frame h ds b d dt bytes trees.base.pbuf).trans
      (storageAdvance.weaken (fun _ equal => Or.inl equal))
  refine ⟨candidate, after, result, ?_, goodA, chainsA, winA, bytesA, availableA, lengthA,
    previousA, startA, lookA, endpoint, rangeA, formA, nextCount,
    logical_history_initial lengthA input origin, symbolA, recordA, storageA⟩
  have advance' : slowMatchAdvance (some (.tab ds)) (d.strstart + d.lookahead - MIN_MATCH_u)
      hash_head ht = .ok (candidate, after) := advance
  dsimp only [distance, length] at tally
  unfold slowDecision
  simp only [bind_app, ldDeflateState_tab good.live.hs, selected, ite_true, tally]
  change (do
    let head ← slowMatchAdvance (some (.tab ds)) (d.strstart + d.lookahead - MIN_MATCH_u) hash_head
    pure { st with hash_head := head, bflush := false }) ht = _
  rw [bind_app, advance']
  rfl

end ZlibF.Spec.Public.Proofs.CompressLocalMatchSymbols
