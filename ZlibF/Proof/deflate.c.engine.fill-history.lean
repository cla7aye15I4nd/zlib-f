import ZlibF.Proof.«deflate.c.engine.fill-resume»
import ZlibF.Proof.«deflate.c.engine.slow-body»

/-! # Resumed input extends the same logical matching history -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

def extendInput (old : Nat → UInt8) (limit : Nat) (incoming : Array UInt8) (offset : Nat) : Nat → UInt8 :=
  fun i => if i < limit then old i else bfn incoming (offset + (i - limit))

theorem logical_history_extend {input extended : Nat → UInt8} {origin : Nat} {d : DeflateState}
    (history : LazyHistory input origin d)
    (agree : ∀ i, i < origin + fillEnd d → extended i = input i) : LazyHistory extended origin d := by
  refine ⟨history.1, ?_⟩
  intro large
  obtain ⟨start, available, room, distance, positive, bound, machine, earlier, bytes⟩ := history.2 large
  refine ⟨start, available, room, distance, positive, bound, machine, earlier, ?_⟩
  intro j hj
  have target : origin + d.strstart.toNat - 1 + j < origin + fillEnd d := by
    dsimp only [fillEnd]
    omega
  have source : origin + d.strstart.toNat - 1 - distance + j < origin + fillEnd d := by omega
  rw [agree _ source, agree _ target]
  exact bytes j hj

theorem copy_range_inside (destination source : Array UInt8) (offset sourceOffset count i : Nat)
    (fit : offset + count ≤ destination.size) (inside : offset ≤ i ∧ i < offset + count)
    (sourceFit : sourceOffset + (i - offset) < source.size) :
    bfn (copyRange destination source offset sourceOffset count) i = bfn source (sourceOffset + (i - offset)) := by
  unfold bfn
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    getElem?_copyRange destination source offset sourceOffset count i fit]
  simp [inside, sourceFit]

theorem resumed_input_view {d : DeflateState} {wa ia : Array UInt8} {input : Nat → UInt8}
    {origin io n : Nat} (fit : fillEnd d + n ≤ wa.size) (sourceFit : io + n ≤ ia.size)
    (view : ∀ i, i < fillEnd d → bfn wa i = input (origin + i)) :
    ∀ i, i < fillEnd d + n →
      bfn (copyRange wa ia (fillEnd d) io n) i = extendInput input (origin + fillEnd d) ia io (origin + i) := by
  intro i hi
  by_cases before : i < fillEnd d
  · rw [copy_range_prefix wa ia (fillEnd d) io n fit i before, view i before]
    simp only [extendInput, show origin + i < origin + fillEnd d from by omega, if_true]
  · rw [copy_range_inside wa ia (fillEnd d) io n i fit (by omega) (by omega)]
    simp only [extendInput, show ¬ origin + i < origin + fillEnd d from by omega, if_false]
    congr 2
    omega

theorem resume_read_history {h : Heap} {r : ZStreamRef} {ds w io origin : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {wa ia : Array UInt8} {input : Nat → UInt8}
    (good : DGood h r ds z d) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : fillEnd d ≤ d.window_size.toNat) (history : LazyHistory input origin d) :
    let n := rbLen z.avail_in (fillMore d)
    let copied := copyRange wa ia (fillEnd d) io n.toNat
    LazyHistory (extendInput input (origin + fillEnd d) ia io) origin (resumeReadState d n copied) := by
  let n := rbLen z.avail_in (fillMore d)
  let copied := copyRange wa ia (fillEnd d) io n.toNat
  have old := logical_history_extend history (extended := extendInput input (origin + fillEnd d) ia io)
    (by intro i hi; simp only [extendInput, hi, if_true])
  have counts := resume_read_counts good win get range
  have add : (d.lookahead + n).toNat = d.lookahead.toNat + n.toNat := counts.2.1
  obtain ⟨key, fields⟩ := resume_read_record d n copied
  change LazyHistory (extendInput input (origin + fillEnd d) ia io) origin (resumeReadState d n copied)
  rw [fields]
  refine ⟨old.1, ?_⟩
  intro large
  obtain ⟨start, available, room, distance, positive, bound, machine, earlier, bytes⟩ := old.2 large
  refine ⟨start, available, ?_, distance, positive, bound, machine, earlier, bytes⟩
  change d.match_length.toNat ≤ (d.lookahead + n).toNat + 1
  rw [add]
  omega

set_option maxHeartbeats 1200000 in
/-- The logical input is extended only at the old valid endpoint.
Earlier match witnesses are retained. The actual copied/padded window
represents the extended input, so the next slow iteration can use it.
-/
theorem resumed_fill_history {h : Heap} {r : ZStreamRef} {ds w io origin : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {wa ia : Array UInt8} {input : Nat → UInt8}
    (good : DGood h r ds z d) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : fillEnd d ≤ d.window_size.toNat) (inputBound : io + z.avail_in.toNat ≤ ia.size)
    (history : LazyHistory input origin d) (deferred : DeferredByte d)
    (view : ∀ i, i < fillEnd d → bfn wa i = input (origin + i)) :
    let n := rbLen z.avail_in (fillMore d)
    let copied := copyRange wa ia (fillEnd d) io n.toNat
    let dr := resumeReadState d n copied
    let final := resumedFillState d n copied
    let output := fillRange copied (paddingStart dr) (paddingCount dr) 0
    let extended := extendInput input (origin + fillEnd d) ia io
    LazyHistory extended origin final ∧ DeferredByte final ∧
      ∀ i, i < fillEnd final → bfn output i = extended (origin + i) := by
  let n := rbLen z.avail_in (fillMore d)
  let copied := copyRange wa ia (fillEnd d) io n.toNat
  let dr := resumeReadState d n copied
  let hr := resumeReadHeap h r ds w z d ref io ia wa
  obtain ⟨key, fields⟩ := resume_read_record d n copied
  change dr = _ at fields
  have counts := resume_read_counts good win get range
  have add : (d.lookahead + n).toNat = d.lookahead.toNat + n.toNat := counts.2.1
  have goodR := resume_read_good (ref := ref) (io := io) (ia := ia) good get
  have getR : hr.bytes w = some copied := by simp [hr, resumeReadHeap, n, copied]
  have winR : dr.window = .ref (.blk w) 0 := by rw [fields]; exact win
  have rangeR : fillEnd dr ≤ dr.window_size.toNat := by rw [fields]; exact counts.2.2
  have endpoint : fillEnd dr = fillEnd d + n.toNat := by
    rw [fields]
    change d.strstart.toNat + (d.lookahead + n).toNat = _
    rw [add]
    dsimp only [fillEnd]
    omega
  have historyR : LazyHistory (extendInput input (origin + fillEnd d) ia io) origin dr :=
    resume_read_history (ref := ref) good win get range history
  refine ⟨historyR, ?_, ?_⟩
  · change DeferredByte dr
    rw [fields]
    exact deferred
  · intro i hi
    change i < fillEnd dr at hi
    have kept := padded_prefix goodR winR getR rangeR i hi
    change bfn (fillRange copied (paddingStart dr) (paddingCount dr) 0) i = _ at kept ⊢
    rw [kept]
    have extent := window_extent good win get
    have count : n.toNat = min z.avail_in.toNat (d.window_size.toNat - fillEnd d) := counts.1
    apply resumed_input_view (by omega : fillEnd d + n.toNat ≤ wa.size) (by omega : io + n.toNat ≤ ia.size) view
    rw [endpoint] at hi
    exact hi

end Zlib.Deflate.Engine.Proofs
