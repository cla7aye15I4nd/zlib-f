import ZlibF.Proof.«deflate.c.engine.slow-match»
import ZlibF.Proof.«deflate.c.engine.slow-literal»
import ZlibF.Proof.«deflate.c.engine.symbol-boundary»

/-! # Symbol and block-balance preservation by the real slow decisions -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

def emittedMatch (d : DeflateState) : Symbol :=
  ⟨(d.strstart - 1 - d.prev_match).toNat, (d.prev_length - MIN_MATCH_u).toNat⟩

def emittedLiteral (d : DeflateState) (wa : Array UInt8) : Symbol :=
  ⟨0, wa[d.strstart.toNat - 1]!.toNat⟩

set_option maxHeartbeats 2500000 in
/-- The selected-match branch preserves the whole symbol boundary on
its actual returned heap. Its represented byte count repays the tally
credit after the complete source match-consumption loop. -/
theorem slow_match_symbol_storage {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    {input : Nat → UInt8} {origin : Nat} {xs : List Symbol}
    (good : DGood h r ds z d) (symbol : SymbolBoundary h ds d xs)
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
      DGood after r ds z result ∧ HeapChains after result result.strstart.toNat ∧
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
  have goodT : DGood ht r ds z dt := match_good_after good trees distance length room
  have chainsT : HeapChains ht dt (d.strstart.toNat + 1) := by
    obtain ⟨wb, p, q, a, pa, qa, hw, hp, hq, ha, hpa, hqa, H⟩ :=
      pending_write_chains good chains trees.base.pbuf bytes 0
    exact ⟨wb, p, q, a, pa, qa, hw, hp, hq, ha, hpa, hqa, H⟩
  have getT : ht.bytes w = some wa := pending_window_frame good win trees.base.pbuf get bytes dt
  have count : (d.sym_next + 3).toNat = d.sym_next.toNat + 3 := literal_count trees.base room 0
  have flag : (d.sym_next + 3 == d.sym_end) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro eq
    have num := congrArg UInt32.toNat eq
    rw [count] at num
    omega
  have tally : tally_dist (some (.tab ds)) distance length h = .ok (false, ht) := by
    simpa only [flag, ht, dt, bytes, matchSymbolState] using tally_match_run trees.base distance length bounds.1 bounds.2.1 room
  obtain ⟨candidate, after, result, advance, goodA, chainsA, winA, bytesA, availableA, lengthA,
      previousA, startA, lookA, endpoint, rangeA, formA, keep, _, bytesFrame, blockFrame, literalFrame, distanceFrame, recordFrame, storageAdvance⟩ :=
    slow_match_advance_storage goodT chainsT win getT previous history.1 lookahead range form hash_head
  have nextCount : result.sym_next.toNat < result.sym_end.toNat := by
    have next := literal_not_full trees 0 room flag
    have nextEq := keep.2.2.2.2.2.2.2.2.2.2
    have endEq := keep.2.2.2.2.1
    rw [nextEq, endEq]
    exact next
  have ledgerT : SymbolLedger bytes dt (xs ++ [emittedMatch d]) :=
    ledger_match trees.base ledger room distance length distancePositive bounds.2.1 (by omega)
  have ledgerA : SymbolLedger bytes result (xs ++ [emittedMatch d]) :=
    ledgerT.keep keep.2.2.2.2.2.2.2.2.2.2 keep.2.2.2.1 literalFrame distanceFrame
  have pendingA : result.pending_buf = .ref (.blk b) 0 := keep.1.trans trees.base.pbuf
  have dataA : after.bytes b = some bytes := by rw [bytesFrame]; simp [ht]
  have emittedSize : (emittedMatch d).bytes = d.prev_length.toNat := by
    change (if distance.toNat = 0 then 1 else length.toNat + 3) = _
    rw [if_neg (by omega)]
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
  have symbolA := symbol_boundary_of_ledger goodA pendingA dataA ledgerA balanceA
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
  simp only [bind_app, ldDeflateState_tab good.live.hs, selected, if_true, tally]
  change (do
    let head ← slowMatchAdvance (some (.tab ds)) (d.strstart + d.lookahead - MIN_MATCH_u) hash_head
    pure { st with hash_head := head, bflush := false }) ht = _
  rw [bind_app, advance']
  rfl

/-- The existing match-symbol statement retains its exact scope. -/
theorem slow_match_symbol_boundary {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    {input : Nat → UInt8} {origin : Nat} {xs : List Symbol}
    (good : DGood h r ds z d) (symbol : SymbolBoundary h ds d xs)
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
      DGood after r ds z result ∧ HeapChains after result result.strstart.toNat ∧
      result.window = .ref (.blk w) 0 ∧ after.bytes w = some wa ∧
      result.match_available = 0 ∧ result.match_length = 2 ∧ result.prev_length = 0 ∧
      result.strstart.toNat = d.strstart.toNat + (d.prev_length.toNat - 1) ∧
      result.lookahead.toNat = d.lookahead.toNat - (d.prev_length.toNat - 1) ∧
      result.strstart.toNat + result.lookahead.toNat = d.strstart.toNat + d.lookahead.toNat ∧
      result.strstart.toNat + result.lookahead.toNat ≤ result.window_size.toNat ∧
      InsHForm result.hash_shift result.hash_mask (bfn wa) result.strstart.toNat result.ins_h ∧
      result.sym_next.toNat < result.sym_end.toNat ∧ LazyHistory input origin result ∧
      SymbolBoundary after ds result (xs ++ [emittedMatch d]) ∧ SlowRecordFrame d result := by
  obtain ⟨candidate, after, result, run, goodA, chainsA, winA, bytesA, availableA, lengthA,
      previousA, startA, lookA, endpoint, rangeA, formA, countA, historyA, symbolA, fields, _⟩ :=
    slow_match_symbol_storage good symbol chains win get history selected lookahead range form space flush st hash_head
  exact ⟨candidate, after, result, run, goodA, chainsA, winA, bytesA, availableA, lengthA,
    previousA, startA, lookA, endpoint, rangeA, formA, countA, historyA, symbolA, fields⟩


/-- The actual deferred-literal branch retains its packed-symbol and block balance facts. -/
theorem slow_literal_symbol_storage {h : Heap} {r : ZStreamRef} {ds w top : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (symbol : SymbolBoundary h ds d xs) (chains : HeapChains h d top)
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
      DGood after r ds z (advanceOne (literalState d c)) ∧
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
  have goodT : DGood ht r ds z (literalState d c) := literal_good_after good trees c room
  have chainsT : HeapChains ht (literalState d c) top :=
    pending_write_chains good chains trees.base.pbuf _ c
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
  have advanced := advance_one_good goodT chainsT range positive
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
  have symbolA := symbol_boundary_of_ledger advanced.1 trees.base.pbuf getA ledgerA balanceA
  have storageA : ByteFrame h after (DeflateOwned ds d) :=
    (pending_state_byte_frame h ds b d (literalState d c) (literalBytes buf d c) trees.base.pbuf).trans
      ((byte_frame_setD ht ds (advanceOne (literalState d c))).weaken (fun _ equal => Or.inl equal))
  refine ⟨after, ?_, advanced.1, advanced.2.1, advanced.2.2, ?_, literal_not_full trees c room flag, symbolA, rfl, storageA⟩
  · unfold slowDecision
    simp only [bind_app, ldDeflateState_tab good.live.hs, literalBranch, Bool.false_eq_true, if_false]
    have hasLiteral : (d.match_available != 0) = true := by simpa using available
    simp only [hasLiteral, if_true, bind_app, read, tally, Bool.false_eq_true, if_false]
    change (do
      wr (some (.tab ds)) advanceOne
      if (← zrd d.strm (·.avail_out)) == 0 then
        return { st with hash_head, bflush := false, ret := some need_more }
      return { st with hash_head, bflush := false }) ht = _
    rw [bind_app, write]
    simp only [good.live.back, bind_app, output]
    by_cases full : (z.avail_out == 0) = true <;> simp [full]
  · exact pending_window_frame good win trees.base.pbuf get (literalBytes buf d c)
      (advanceOne (literalState d c))

/-- The earlier literal-symbol statement follows from the storage result. -/
theorem slow_literal_symbol_boundary {h : Heap} {r : ZStreamRef} {ds w top : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (symbol : SymbolBoundary h ds d xs) (chains : HeapChains h d top)
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
      DGood after r ds z (advanceOne (literalState d c)) ∧
      HeapChains after (advanceOne (literalState d c)) top ∧
      (advanceOne (literalState d c)).strstart.toNat + (advanceOne (literalState d c)).lookahead.toNat ≤
        (advanceOne (literalState d c)).window_size.toNat ∧
      after.bytes w = some wa ∧
      (advanceOne (literalState d c)).sym_next.toNat < (advanceOne (literalState d c)).sym_end.toNat ∧
      SymbolBoundary after ds (advanceOne (literalState d c)) (xs ++ [emittedLiteral d wa]) ∧
      SlowRecordFrame d (advanceOne (literalState d c)) := by
  obtain ⟨after, run, goodA, chainsA, rangeA, bytesA, countA, symbolA, fields, _⟩ :=
    slow_literal_symbol_storage good symbol chains win get range positive previousByte literalBranch available space flush st hash_head
  exact ⟨after, run, goodA, chainsA, rangeA, bytesA, countA, symbolA, fields⟩

/-- Deferring a byte adds one unit of credit and does not emit a symbol. -/
theorem slow_defer_symbol_boundary {h : Heap} {r : ZStreamRef} {ds top : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol}
    (good : DGood h r ds z d) (symbol : SymbolBoundary h ds d xs) (chains : HeapChains h d top)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (positive : 1 ≤ d.lookahead.toNat)
    (branch : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = false)
    (available : d.match_available = 0) (flush : Int32) (st : LoopS) (candidate : UInt32) :
    slowDecision (some (.tab ds)) flush st candidate h =
      .ok ({ st with hash_head := candidate, bflush := false }, setD h ds (deferOne d)) ∧
    SymbolBoundary (setD h ds (deferOne d)) ds (deferOne d) xs ∧ SlowRecordFrame d (deferOne d) := by
  obtain ⟨b, buf, trees, ledger, balance⟩ := symbol
  have credit : deferredCredit d = 0 := by simp [deferredCredit, available]
  rw [credit] at balance
  have goodA := (defer_one_good good chains range positive).1
  have ledgerA : SymbolLedger buf (deferOne d) xs := ledger.keep rfl rfl rfl rfl
  have creditA : deferredCredit (deferOne d) = 1 := by simp [deferredCredit, deferOne]
  have balanceA : BlockBalance (deferOne d) xs (deferredCredit (deferOne d)) := by
    rw [creditA]
    exact balance_advance_one good.inv range positive balance
  exact ⟨slow_defer_branch good.live.hs branch available flush st candidate,
    symbol_boundary_of_ledger goodA trees.base.pbuf trees.base.bytes ledgerA balanceA, rfl⟩

end Zlib.Deflate.Engine.Proofs
