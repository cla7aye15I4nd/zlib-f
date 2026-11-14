import ZlibF.Proof.«deflate.c.engine.pending-boundary»
import ZlibF.Proof.«deflate.c.engine.fill-slow-boundary»
import ZlibF.Spec.Functional.Checksums

/-! # Deferred-insertion refill preserves the initialized engine boundary -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

set_option maxHeartbeats 3500000 in
/-- The real read, deferred insertions and padding preserve both the
logical symbol boundary and the earlier hash frontier. No insert=0
premise is used. The source path has no slide and uses wrapper 1.
-/
theorem fill_window_pending_boundary_read {h : Heap} {r : ZStreamRef} {ds origin io : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol}
    {ref : BRef} {ia : Array UInt8}
    (boundary : PendingBoundary h r ds z d input origin xs)
    (short : d.lookahead.toNat < 262)
    (noSlide : ¬ d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u))
    (wrap : d.wrap = 1) (pointer : z.next_in = .ref ref io)
    (data : Space.get h ref = some ia) (inputBound : io + z.avail_in.toNat ≤ ia.size)
    (nonempty : z.avail_in ≠ 0)
    (separate : ∀ w, d.window = .ref (.blk w) 0 → BRef.blk w ≠ ref) :
    ∃ used after z' result extended,
      fill_window (some (.tab ds)) h = .ok ((), after) ∧
      PendingBoundary after r ds z' result extended origin xs ∧ StreamAccounting z z' used 0 ∧
      result.strstart = d.strstart ∧ result.lookahead.toNat = d.lookahead.toNat + used ∧
      result.insert.toNat = min d.insert.toNat (2 - result.lookahead.toNat) ∧ result.wrap = 1 ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      (262 ≤ result.lookahead.toNat ∨ z'.avail_in = 0) ∧
      result = { d with
        lookahead := result.lookahead, ins_h := result.ins_h, insert := result.insert, high_water := result.high_water } := by
  obtain ⟨w, wa, win, get, view, _⟩ := boundary.data
  obtain ⟨b, buf, trees, ledger, balance⟩ := boundary.symbols
  let n := rbLen z.avail_in (fillMore d)
  let copied := copyRange wa ia (fillEnd d) io n.toNat
  let z' := readStream z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat))
  let extended := extendInput input (origin + fillEnd d) ia io
  obtain ⟨after, result, output, run, goodA, frontierA, winA, bytesA, rangeA, _, formA, fields,
      countA, outside, prefixA, stopped⟩ :=
    fill_window_pending_complete boundary.good boundary.frontier boundary.insert_le win get boundary.range
      short noSlide wrap pointer data inputBound nonempty (separate w win)
  have fieldsA : result = { d with
      lookahead := d.lookahead + n, ins_h := result.ins_h, insert := result.insert, high_water := result.high_water } := fields
  have counts := resume_read_counts boundary.good win get boundary.range
  have inputCount : n.toNat = min z.avail_in.toNat (fillMore d).toNat := rbLen_nat _ _
  have startA : result.strstart = d.strstart := by rw [fieldsA]
  have lookA : result.lookahead.toNat = d.lookahead.toNat + n.toNat := by rw [fieldsA]; exact counts.2.1
  have endpoint : fillEnd result = fillEnd d + n.toNat := by
    dsimp only [fillEnd]
    rw [startA, lookA]
    omega
  have distinct := window_pending_separate boundary.good win trees.base.pbuf
  have pendingA : result.pending_buf = .ref (.blk b) 0 := by rw [fieldsA]; exact trees.base.pbuf
  have dataA : after.bytes b = some buf := (outside b distinct.symm).trans trees.base.bytes
  have ledgerA : SymbolLedger buf result xs := by rw [fieldsA]; exact ledger.keep rfl rfl rfl rfl
  have balanceA : BlockBalance result xs (deferredCredit result) := by rw [fieldsA]; exact balance
  have symbolsA := symbol_boundary_of_ledger goodA pendingA dataA ledgerA balanceA
  have historyOld : LazyHistory extended origin d := logical_history_extend boundary.history (by
    intro i before
    simp only [extended, extendInput, before, if_true])
  have historyA : LazyHistory extended origin result := by
    rw [fieldsA]
    refine ⟨historyOld.1, ?_⟩
    intro large
    obtain ⟨start, available, room, distance, positive, bound, machine, earlier, bytes⟩ := historyOld.2 large
    refine ⟨start, available, ?_, distance, positive, bound, machine, earlier, bytes⟩
    change d.match_length.toNat ≤ (d.lookahead + n).toNat + 1
    rw [counts.2.1]
    omega
  have deferredA : DeferredByte result := by rw [fieldsA]; exact boundary.deferred
  have extent := window_extent boundary.good win get
  have fit : fillEnd d + n.toNat ≤ wa.size := by
    have valid := boundary.range
    have more : (fillMore d).toNat = d.window_size.toNat - fillEnd d := fill_more_nat boundary.good win get boundary.range
    omega
  have viewA : ∀ i, i < fillEnd result → bfn output i = extended (origin + i) := by
    intro i before
    rw [prefixA i before]
    apply resumed_input_view fit (by omega) view i
    rw [endpoint] at before
    exact before
  have insertA : result.insert.toNat ≤ result.strstart.toNat := by
    have old := boundary.insert_le
    rw [startA]
    omega
  have core : SlowBoundary after r ds z' result extended origin xs :=
    ⟨goodA, heap_chains_raise frontierA (Nat.sub_le _ _), rangeA, historyA, deferredA, symbolsA,
      w, output, winA, bytesA, viewA, fun large => (formA large).2⟩
  refine ⟨n.toNat, after, z', result, extended, run,
    ⟨core, insertA, frontierA, fun large => (formA large).1⟩,
    read_stream_accounting z n ref io _ pointer (by omega), startA, lookA, countA, ?_, ?_, stopped, ?_⟩
  · rw [fieldsA]
    exact wrap
  · intro i before
    simp only [extended, extendInput, before, if_true]
  · rw [fieldsA]

/-- Public buffer storage supplies the readable source and disjointness.
Pending insertion is an established representation fact of the boundary. -/
theorem fill_window_pending_boundary {h : Heap} {r : ZStreamRef} {ds origin io : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol} {ref : BRef}
    (boundary : PendingBoundary h r ds z d input origin xs)
    (short : d.lookahead.toNat < 262)
    (noSlide : ¬ d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u))
    (wrap : d.wrap = 1) (buffers : StreamBuffers h r)
    (pointer : z.next_in = .ref ref io) (nonempty : z.avail_in ≠ 0) :
    ∃ used after z' result extended,
      fill_window (some (.tab ds)) h = .ok ((), after) ∧
      PendingBoundary after r ds z' result extended origin xs ∧ StreamAccounting z z' used 0 ∧
      result.strstart = d.strstart ∧ result.lookahead.toNat = d.lookahead.toNat + used ∧
      result.insert.toNat = min d.insert.toNat (2 - result.lookahead.toNat) ∧ result.wrap = 1 ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      (262 ≤ result.lookahead.toNat ∨ z'.avail_in = 0) ∧
      result = { d with
        lookahead := result.lookahead, ins_h := result.ins_h, insert := result.insert, high_water := result.high_water } := by
  obtain ⟨ia, data, bound⟩ := caller_input_array boundary.good buffers pointer
  exact fill_window_pending_boundary_read boundary short noSlide wrap pointer data bound nonempty
    (fun _ win => caller_input_window_separate boundary.good buffers win pointer)

end Zlib.Deflate.Engine.Proofs
