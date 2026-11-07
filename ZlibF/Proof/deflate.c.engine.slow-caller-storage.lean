import ZlibF.Proof.«deflate.c.engine.fill-caller-storage»
import ZlibF.Proof.«deflate.c.engine.content-refill»

/-! # Real slow coding retains external storage and public caller buffers -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- All three real decisions preserve the decoded meaning of the exact
stored symbols as well as the actual heap boundary. Search and tally
are executed; their specifications are not caller assumptions. -/
theorem slow_body_content_buffers_reason {h : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (lookahead : 262 ≤ d.lookahead.toNat) (space : d.sym_next.toNat + 3 < d.sym_end.toNat)
    (buffers : StreamBuffers h r) (flush : Int32) (st : LoopS) :
    ∃ next after result ys,
      deflate_slow_body (some (.tab ds)) flush st h = .ok (next, after) ∧
      ContentBoundary after r ds z result input origin base ys ∧
      SlowRecordFrame d result ∧ d.strstart.toNat < result.strstart.toNat ∧
      result.lookahead.toNat < d.lookahead.toNat ∧ fillEnd result = fillEnd d ∧
      (ys = xs ∨ ∃ symbol, ys = xs ++ [symbol]) ∧
      result.sym_next.toNat < result.sym_end.toNat ∧ next.brk = st.brk ∧
      (next.ret = st.ret ∨ next.ret = some need_more) ∧
      StreamBuffers after r ∧ ByteFrame h after (DeflateOwned ds d) ∧
      (next.ret = some need_more → st.ret = some need_more ∨ z.avail_out = 0) := by
  obtain ⟨w, p, q, wa, pa, qa, env, chains⟩ := heap_chains_environment boundary.good boundary.chains
  obtain ⟨w0, wa0, win, get, view, form⟩ := boundary.data
  have sameWindow : w0 = w := by
    simpa only [env.win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using win.symm
  subst w0
  have sameArray : wa0 = wa := Option.some.inj (get.symm.trans env.wbytes)
  subst wa0
  obtain ⟨next, after, result, ys, run, goodA, chainsA, winA, bytesA, rangeA, endpoint,
      advance, less, formA, historyA, deferredA, countA, brkA, retA, symbolsA, step, frameA, values, storageA, reasonA⟩ :=
    slow_body_with_symbol_storage_reason boundary.good boundary.symbols env chains (Nat.le_refl _)
      boundary.range lookahead boundary.history boundary.deferred view (form (by omega)) space flush st
  change fillEnd result = fillEnd d at endpoint
  have core : SlowBoundary after r ds z result input origin ys :=
    ⟨goodA, chainsA, rangeA, historyA, deferredA, symbolsA, w, wa, winA, bytesA,
      (fun i bound => view i (by rw [← endpoint]; exact bound)), fun _ => formA⟩
  have insert : result.insert = 0 :=
    (congrArg (·.insert) frameA).trans (boundary.ready (by omega))
  have pending : PendingBoundary after r ds z result input origin ys :=
    ⟨core, by simp [insert], by simpa only [insert, show (0 : UInt32).toNat = 0 from rfl, Nat.sub_zero] using chainsA,
      fun _ => insert⟩
  have owned := stream_owned_keys boundary.good goodA
    (congrArg (·.window) frameA) (congrArg (·.prev) frameA) (congrArg (·.head) frameA) (congrArg (·.pending_buf) frameA)
  have buffersA := stream_buffers_private_read boundary.good.live.hz goodA.live.hz buffers storageA
    (fun b mine => (stream_owned_deflate boundary.good b).mpr mine) owned (stream_accounting_zero z)
  obtain ⟨_, _, _, _, balance⟩ := boundary.symbols
  obtain ⟨_, _, _, _, balanceA⟩ := symbolsA
  refine ⟨next, after, result, ys, run,
    ⟨pending, slow_value_trace boundary view values,
      content_accounted_body balance balanceA frameA boundary.accounted⟩,
    frameA, advance, less, endpoint, ?_, countA, brkA, retA, buffersA, storageA, reasonA⟩
  rcases step with same | literal | matched
  · exact Or.inl same
  · exact Or.inr ⟨_, literal⟩
  · exact Or.inr ⟨_, matched⟩

/-- The earlier complete coding boundary remains unchanged. -/
theorem slow_body_content_buffers {h : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (lookahead : 262 ≤ d.lookahead.toNat) (space : d.sym_next.toNat + 3 < d.sym_end.toNat)
    (buffers : StreamBuffers h r) (flush : Int32) (st : LoopS) :
    ∃ next after result ys,
      deflate_slow_body (some (.tab ds)) flush st h = .ok (next, after) ∧
      ContentBoundary after r ds z result input origin base ys ∧
      SlowRecordFrame d result ∧ d.strstart.toNat < result.strstart.toNat ∧
      result.lookahead.toNat < d.lookahead.toNat ∧ fillEnd result = fillEnd d ∧
      (ys = xs ∨ ∃ symbol, ys = xs ++ [symbol]) ∧
      result.sym_next.toNat < result.sym_end.toNat ∧ next.brk = st.brk ∧
      (next.ret = st.ret ∨ next.ret = some need_more) ∧
      StreamBuffers after r ∧ ByteFrame h after (DeflateOwned ds d) := by
  obtain ⟨next, after, result, ys, run, boundaryA, fields, advance, less, endpoint, symbols,
      countA, brkA, retA, buffersA, storageA, _⟩ :=
    slow_body_content_buffers_reason boundary lookahead space buffers flush st
  exact ⟨next, after, result, ys, run, boundaryA, fields, advance, less, endpoint, symbols,
    countA, brkA, retA, buffersA, storageA⟩


/-- Exact union of the record fields written by refill and slow coding. -/
def SlowIterationFrame (before after : DeflateState) : Prop :=
  after = { before with
    strstart := after.strstart, lookahead := after.lookahead, ins_h := after.ins_h,
    match_start := after.match_start, match_length := after.match_length,
    prev_match := after.prev_match, prev_length := after.prev_length, match_available := after.match_available,
    sym_next := after.sym_next, dyn_ltree := after.dyn_ltree, dyn_dtree := after.dyn_dtree,
    block_start := after.block_start, insert := after.insert, high_water := after.high_water, slid := after.slid }

theorem SlowIterationFrame.trans {a b c : DeflateState} (first : SlowIterationFrame a b)
    (second : SlowIterationFrame b c) : SlowIterationFrame a c := by
  unfold SlowIterationFrame at *
  rw [second, first]

theorem iteration_frame_fill {d result : DeflateState} (frame : FillRecordFrame d result) :
    SlowIterationFrame d result := by
  unfold FillRecordFrame at frame
  unfold SlowIterationFrame
  rw [frame]

theorem iteration_frame_slow {d result : DeflateState} (frame : SlowRecordFrame d result) :
    SlowIterationFrame d result := by
  unfold SlowRecordFrame at frame
  unfold SlowIterationFrame
  rw [frame]

theorem fill_owned_frame {d result : DeflateState} (frame : FillRecordFrame d result) (ds : Nat) :
    DeflateOwned ds result = DeflateOwned ds d := by
  unfold FillRecordFrame at frame
  rw [frame]
  rfl

/-- One complete real slow-strategy iteration for Z_NO_FLUSH when a tally
will leave symbol room. Refilling is executed and proved, including
sliding and deferred insertions. An exhausted short read returns
need_more before search; otherwise the existing complete body advances.
-/
theorem slow_no_flush_content_buffers_reason {h : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List ZlibF.Math.DeflateSymbols.Symbol}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (space : d.sym_next.toNat + 3 < d.sym_end.toNat)
    (wrap : d.wrap = 1) (buffers : StreamBuffers h r)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) (st : LoopS) :
    ∃ used next after z' result ys extended nextOrigin,
      deflate_slow_body (some (.tab ds)) Z_NO_FLUSH st h = .ok (next, after) ∧
      ContentBoundary after r ds z' result extended nextOrigin base ys ∧ StreamAccounting z z' used 0 ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧
      (ys = xs ∨ ∃ symbol, ys = xs ++ [symbol]) ∧
      result.sym_next.toNat < result.sym_end.toNat ∧ next.brk = st.brk ∧
      (next.ret = some need_more ∨ origin + d.strstart.toNat < nextOrigin + result.strstart.toNat) ∧
      StreamBuffers after r ∧ ByteFrame h after (DeflateOwned ds d) ∧ SlowIterationFrame d result ∧
      (next.ret = st.ret ∨ next.ret = some need_more) ∧
      (next.ret = some need_more → st.ret = some need_more ∨
        (z'.avail_in = 0 ∧ result.lookahead.toNat < 262) ∨ z'.avail_out = 0) := by
  by_cases short : d.lookahead.toNat < 262
  · obtain ⟨used, filledHeap, z', filled, extended, nextOrigin, fillRun, boundaryF, account, buffersF, storageF,
        startF, lookF, _, _, prefixF, stoppedF, fieldsF⟩ :=
      fill_window_content_buffers boundary short wrap buffers inputValid
    have symNext : filled.sym_next = d.sym_next := congrArg (·.sym_next) fieldsF
    have symEnd : filled.sym_end = d.sym_end := congrArg (·.sym_end) fieldsF
    have roomF : filled.sym_next.toNat + 3 < filled.sym_end.toNat := by rw [symNext, symEnd]; exact space
    have endpointF : nextOrigin + fillEnd filled = origin + fillEnd d + used := by
      dsimp only [fillEnd]
      omega
    by_cases ready : 262 ≤ filled.lookahead.toNat
    · obtain ⟨next, after, result, ys, run, boundaryA, fieldsA, advance, _, endpoint, symbols, countA, brkA, retA, buffersA, storageA, reasonA⟩ :=
        slow_body_content_buffers_reason boundaryF ready roomF buffersF Z_NO_FLUSH st
      have prefixRun := slow_body_fill_ready boundary.good.live.hs boundaryF.good.live.hs short ready fillRun Z_NO_FLUSH st
      rw [fill_owned_frame fieldsF ds] at storageA
      refine ⟨used, next, after, z', result, ys, extended, nextOrigin,
        prefixRun.trans run, boundaryA, account, prefixF, ?_, symbols, countA, brkA, Or.inr ?_, buffersA, storageF.trans storageA,
        (iteration_frame_fill fieldsF).trans (iteration_frame_slow fieldsA), retA,
        fun returned => (reasonA returned).elim Or.inl (fun empty => Or.inr (Or.inr empty))⟩
      · rw [endpoint]
        exact endpointF
      · omega
    · have shortF : filled.lookahead.toNat < 262 := by omega
      refine ⟨used, { st with ret := some need_more }, filledHeap, z', filled, xs, extended, nextOrigin,
        slow_body_fill_wait boundary.good.live.hs boundaryF.good.live.hs short shortF fillRun st,
        boundaryF, account, prefixF, endpointF, Or.inl rfl, by omega, rfl, Or.inl rfl, buffersF, storageF, iteration_frame_fill fieldsF, Or.inr rfl,
        fun _ => Or.inr (Or.inl ⟨stoppedF.resolve_left (by omega), shortF⟩)⟩
  · have ready : 262 ≤ d.lookahead.toNat := by omega
    obtain ⟨next, after, result, ys, run, boundaryA, fieldsA, advance, _, endpoint, symbols, countA, brkA, retA, buffersA, storageA, reasonA⟩ :=
      slow_body_content_buffers_reason boundary ready space buffers Z_NO_FLUSH st
    have account : StreamAccounting z z 0 0 := by
      refine ⟨by omega, by omega, by omega, by omega, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
      · cases z.next_in <;> rfl
      · cases z.next_out <;> rfl
    refine ⟨0, next, after, z, result, ys, input, origin, run, boundaryA, account,
      fun _ _ => rfl, ?_, symbols, countA, brkA, Or.inr (by omega), buffersA, storageA, iteration_frame_slow fieldsA, retA,
      fun returned => (reasonA returned).elim Or.inl (fun empty => Or.inr (Or.inr empty))⟩
    rw [endpoint, Nat.add_zero]

/-- The previous streaming iteration statement follows from the same
execution with its source-level stop reason retained. -/
theorem slow_no_flush_content_buffers {h : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List ZlibF.Math.DeflateSymbols.Symbol}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (space : d.sym_next.toNat + 3 < d.sym_end.toNat)
    (wrap : d.wrap = 1) (buffers : StreamBuffers h r)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) (st : LoopS) :
    ∃ used next after z' result ys extended nextOrigin,
      deflate_slow_body (some (.tab ds)) Z_NO_FLUSH st h = .ok (next, after) ∧
      ContentBoundary after r ds z' result extended nextOrigin base ys ∧ StreamAccounting z z' used 0 ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧
      (ys = xs ∨ ∃ symbol, ys = xs ++ [symbol]) ∧
      result.sym_next.toNat < result.sym_end.toNat ∧ next.brk = st.brk ∧
      (next.ret = some need_more ∨ origin + d.strstart.toNat < nextOrigin + result.strstart.toNat) ∧
      StreamBuffers after r ∧ ByteFrame h after (DeflateOwned ds d) ∧ SlowIterationFrame d result ∧
      (next.ret = st.ret ∨ next.ret = some need_more) := by
  obtain ⟨used, next, after, z', result, ys, extended, nextOrigin, run, boundaryA, account,
      agrees, endpoint, symbols, countA, brkA, progress, buffersA, storageA, fields, retA, _⟩ :=
    slow_no_flush_content_buffers_reason boundary space wrap buffers inputValid st
  exact ⟨used, next, after, z', result, ys, extended, nextOrigin, run, boundaryA, account,
    agrees, endpoint, symbols, countA, brkA, progress, buffersA, storageA, fields, retA⟩

end Zlib.Deflate.Engine.Proofs
