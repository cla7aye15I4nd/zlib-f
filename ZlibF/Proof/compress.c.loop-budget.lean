import ZlibF.Proof.«compress.c.wrapper-prefix»
import ZlibF.Proof.«deflate.c.engine.guarded-ordinary-progress»

/-! # Strict byte budget for every real nonterminal compressor iteration -/
namespace ZlibF.Spec.Public.Proofs.CompressPrefix
open C Zlib.Compress Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs
open ZlibF.Spec.Public.Proofs.CompressLoop ZlibF.Spec.Public.Proofs.CompressCaller
set_option autoImplicit false
set_option maxRecDepth 100000

def byteBudget (z : ZStream) (left sourceLen : UInt64) : Nat :=
  z.avail_in.toNat + sourceLen.toNat + z.avail_out.toNat + left.toNat

private theorem trace_calls {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : DefaultDataTrace r h log) : DeflateCore.Calls r h := by
  induction history with
  | init domain actual => exact .init domain actual
  | caller _ edit ih => exact .caller ih edit
  | step _ get raw observed ih =>
    obtain ⟨z, _z', getZ, _getA, buffers, _active, _snapshot, _used, _written, run⟩ := observed
    have same : z = _ := Option.some.inj (getZ.symm.trans get)
    subst z
    exact .step ih get buffers raw run

/-- Every real OK iteration strictly decreases unread-input plus unused-
output bytes. It reuses the frozen engine progress theorem on the same
actual execution and includes the exhausted-output refusal case. -/
theorem body_ok_budget_decreases {h after : Heap} {slot ob oo : Nat}
    {log : DataLog} {z z' : ZStream} {old : Int32} {left sourceLen nextLeft nextSourceLen : UInt64}
    {source : List UInt8}
    (history : DefaultDataTrace (.tab slot) h log) (get : h.streams slot = some z)
    (ranges : Ranges h (.tab slot) z left sourceLen source)
    (pointer : z.next_out = .ref (.blk ob) oo)
    (actual : body (some (.tab slot)) (old, left, sourceLen) h = .ok ((Z_OK, nextLeft, nextSourceLen), after))
    (getA : after.streams slot = some z') :
    byteBudget z' nextLeft nextSourceLen < byteBudget z left sourceLen := by
  obtain ⟨ds, current, d, config, boundary⟩ := history.protocol
  have same : current = z := Option.some.inj (boundary.good.live.hz.symm.trans get)
  subst current
  have globals := ZlibF.Spec.Public.Proofs.DeflateCore.calls_globals (trace_calls history)
  have edit := prepare_rebuffer boundary.good globals left sourceLen
  obtain ⟨zp, getP, boundaryP⟩ := boundary.rebuffer edit
  have sameP : zp = CompressLoop.preparedStream z left sourceLen :=
    Option.some.inj (getP.symm.trans (prepare_get h slot z left sourceLen get))
  subst zp
  have rangesP := prepare_ranges boundary.good ranges
  obtain ⟨buffersP, snapshotP⟩ := ranges_current getP rangesP
  have pointerP : (CompressLoop.preparedStream z left sourceLen).next_out = .ref (.blk ob) oo := pointer
  let flush := if (prepare h slot z left sourceLen).2.1 != 0 then Z_NO_FLUSH else Z_FINISH
  have flag : flush = Z_NO_FLUSH ∨ flush = Z_FINISH := by unfold flush; split <;> simp
  obtain ⟨used, written, rc, computed, returned, result, engineRun, stateA, _buffersA, goodA,
    account, _bytesA, _tin, _tout, _allowed, _errors, _bad, _ended, _shape, _frame, _live, _count, _next⟩ :=
    boundaryP.all_scalar_request_contract flush buffersP (Or.inr ⟨ob, oo, pointerP⟩)
  have bodyRun : body (some (.tab slot)) (old, left, sourceLen) h =
      .ok ((rc, (prepare h slot z left sourceLen).1, (prepare h slot z left sourceLen).2.1), computed) := by
    rw [body_prepare h slot z old left sourceLen get]
    change deflate (some (.tab slot))
      (if (prepare h slot z left sourceLen).2.1 != 0 then Z_NO_FLUSH else Z_FINISH)
      (prepare h slot z left sourceLen).2.2 = .ok (rc, computed) at engineRun
    rcases eq : prepare h slot z left sourceLen with ⟨l, n, prepared⟩
    simp only [eq] at engineRun ⊢
    simp only [bind_app, engineRun, pure_app]
  obtain ⟨locals, heaps⟩ := Prod.mk.inj (Except.ok.inj (bodyRun.symm.trans actual))
  subst computed
  have code : rc = Z_OK := congrArg Prod.fst locals
  have leftEq : (prepare h slot z left sourceLen).1 = nextLeft := congrArg (fun st : Locals => st.2.1) locals
  have sourceEq : (prepare h slot z left sourceLen).2.1 = nextSourceLen := congrArg (fun st : Locals => st.2.2) locals
  subst rc nextLeft nextSourceLen
  have streams : returned = z' := Option.some.inj (goodA.live.hz.symm.trans getA)
  subst returned
  have counts := prepare_counts h slot z left sourceLen
  change (prepare h slot z left sourceLen).1.toNat +
    (CompressLoop.preparedStream z left sourceLen).avail_out.toNat = _ ∧
    (prepare h slot z left sourceLen).2.1.toNat +
    (CompressLoop.preparedStream z left sourceLen).avail_in.toNat = _ at counts
  have positive : 0 < (CompressLoop.preparedStream z left sourceLen).avail_out.toNat := by
    apply Nat.pos_of_ne_zero
    intro emptyNat
    have empty : (CompressLoop.preparedStream z left sourceLen).avail_out = 0 :=
      UInt32.toNat_inj.mp emptyNat
    have low : 0 ≤ flush.toInt := by rcases flag with eq | eq <;> rw [eq] <;> decide
    have high : flush.toInt ≤ 5 := by rcases flag with eq | eq <;> rw [eq] <;> decide
    obtain ⟨err, other, otherZ, allowed, refusal, _rest⟩ :=
      boundaryP.entry_refusals flush buffersP low high (Or.inr (Or.inr (Or.inr empty)))
    have code : err = Z_OK := (Prod.mk.inj (Except.ok.inj (refusal.symm.trans engineRun))).1
    rcases allowed with bad | bad
    · exact (by decide : Z_STREAM_ERROR ≠ Z_OK) (bad.symm.trans code)
    · exact (by decide : Z_BUF_ERROR ≠ Z_OK) (bad.symm.trans code)
  have valid := ZlibF.Spec.Public.Proofs.DeflateCore.snapshot_input_valid snapshotP
  have guard : flush = Z_NO_FLUSH → (CompressLoop.preparedStream z left sourceLen).avail_in ≠ 0 := by
    intro ordinary
    apply prepare_no_flush_input h slot z left sourceLen
    intro empty
    have finish : flush = Z_FINISH := by simp [flush, empty]
    exact (by decide : Z_NO_FLUSH ≠ Z_FINISH) (ordinary.symm.trans finish)
  have progress := boundaryP.ordinary_run_byte_progress buffersP pointerP positive valid flag guard
    engineRun goodA.live.hz account rfl
  have inputCount := account.2.2.1
  have outputCount := account.2.2.2.1
  unfold byteBudget
  rcases progress with consumed | delivered <;> omega

/-- A byte budget smaller than the real remaining fuel forces the actual
loop to return. Zero output stops through the actual refusal path; OK
iterations decrease the budget using the frozen engine progress result. -/
theorem loop_go_total {slot ob oo steps : Nat} {h : Heap} {log : DataLog} {z : ZStream}
    {old : Int32} {left sourceLen : UInt64} {source : List UInt8}
    (history : DefaultDataTrace (.tab slot) h log) (get : h.streams slot = some z)
    (ranges : Ranges h (.tab slot) z left sourceLen source)
    (pointer : z.next_out = .ref (.blk ob) oo)
    (room : byteBudget z left sourceLen < steps) :
    ∃ last after, cdoWhile.go (body (some (.tab slot))) condition steps (old, left, sourceLen) h =
      .ok (last, after) ∧ last.1 ≠ Z_OK := by
  induction steps generalizing h log z old left sourceLen source oo with
  | zero => omega
  | succ steps ih =>
    obtain ⟨used, written, rc, after, z', run, traceA, getA, rangesA, _inputCount, _outputCount,
      _inputPtr, outputPtr, _outputBytes, _effect, _ended⟩ :=
      body_observed_step history get old left sourceLen source ranges pointer
    by_cases ok : rc = Z_OK
    · subst rc
      have decrease := body_ok_budget_decreases history get ranges pointer run getA
      have pointerA : z'.next_out = .ref (.blk ob) (oo + written.length) := by rw [outputPtr, pointer]; rfl
      obtain ⟨last, final, tail, stopped⟩ := ih (old := Z_OK) traceA getA rangesA pointerA (by omega)
      refine ⟨last, final, ?_, stopped⟩
      rw [cdoWhile.go]
      simp only [bind_app, run, condition, pure_app, beq_self_eq_true, ite_true]
      exact tail
    · refine ⟨(rc, (prepare h slot z left sourceLen).1, (prepare h slot z left sourceLen).2.1), after, ?_, ok⟩
      simp [cdoWhile.go, run, condition, ok]

/-- This is the real cdoWhile fuel used by compress2_z_unfold. -/
theorem actual_loop_total {slot ob oo : Nat} {h : Heap} {log : DataLog} {z : ZStream}
    {old : Int32} {left sourceLen : UInt64} {source : List UInt8}
    (history : DefaultDataTrace (.tab slot) h log) (get : h.streams slot = some z)
    (ranges : Ranges h (.tab slot) z left sourceLen source)
    (pointer : z.next_out = .ref (.blk ob) oo)
    (room : byteBudget z left sourceLen < fuel) :
    ∃ last after, loop (some (.tab slot)) (old, left, sourceLen) h = .ok (last, after) ∧ last.1 ≠ Z_OK :=
  loop_go_total history get ranges pointer room

private theorem readable_size_bound {h : Heap} {p : BPtr} {n : Nat} {xs : List UInt8}
    (objects : ZlibF.PlatformMemory.ByteObjectsFit h) (bytes : Bytes h p n xs) : n < 2 ^ 63 := by
  rcases bytes with ⟨_, rfl, _⟩ | ⟨ref, off, a, _, get, bound, _⟩
  · decide
  · have size := objects ref a get
    change a.size < 2 ^ 63 at size
    omega

private theorem writable_size_bound {h : Heap} {p : BPtr} {n : Nat}
    (objects : ZlibF.PlatformMemory.ByteObjectsFit h) (writable : Writable h p n) : n < 2 ^ 63 := by
  rcases writable with ⟨_, rfl⟩ | ⟨ref, off, a, _, get, _, bound⟩
  · decide
  · have size := objects ref a get
    change a.size < 2 ^ 63 at size
    omega

/-- The authorized per-object size premise supplies enough ACTUAL loop
fuel for one wrapper call. The real loop always returns after successful
default init, and any END return encodes the complete original source.
This internal Uniq/raw-output milestone does not assert END for an
insufficient capacity, the compressBound guarantee, or post-loop cleanup. -/
theorem original_buffers_loop_total {h initialized : Heap} {dest source : BPtr}
    {ob oo : Nat} {capacity sourceLen : UInt64} {xs : List UInt8}
    (fresh : Fresh h) (unique : Zlib.Inflate.Spec.Uniq h) (globals : LibraryGlobals h)
    (objects : ZlibF.PlatformMemory.ByteObjectsFit h)
    (bytes : Bytes h source sourceLen.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source sourceLen.toNat dest capacity.toNat)
    (pointer : dest = .ref (.blk ob) oo)
    (actualInit : C.run (deflateInit_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION
      (.ref (.str 57) 0) 112) (localHeap h) = .ok (Z_OK, initialized)) :
    ∃ ready last after,
      C.run (zwr (some (.tab h.nextBlk)) (fun s => bindings s dest source)) initialized = .ok ((), ready) ∧
      loop (some (.tab h.nextBlk)) (Z_OK, capacity, sourceLen) ready = .ok (last, after) ∧
      last.1 ≠ Z_OK ∧
      (last.1 = Z_STREAM_END →
        ∃ output, Bytes after dest output.length output ∧ ZlibF.Spec.Zlib.Valid xs output) := by
  obtain ⟨ready, z, setup, history, get, ranges, out, _in, outAvail, inAvail⟩ :=
    successful_default_seed fresh unique globals bytes writable separate actualInit
  have inputBound := readable_size_bound objects bytes
  have outputBound := writable_size_bound objects writable
  have room : byteBudget z capacity sourceLen < fuel := by
    simp only [byteBudget, inAvail, outAvail, UInt32.toNat_zero, Nat.zero_add]
    change sourceLen.toNat + capacity.toNat < 18446744073709551616
    change sourceLen.toNat < 9223372036854775808 at inputBound
    change capacity.toNat < 9223372036854775808 at outputBound
    omega
  have raw : z.next_out = .ref (.blk ob) oo := out.trans pointer
  obtain ⟨last, after, run, stopped⟩ := actual_loop_total (old := Z_OK) history get ranges raw room
  refine ⟨ready, last, after, setup, run, stopped, ?_⟩
  rcases last with ⟨rc, finalLeft, finalSourceLen⟩
  intro ended
  change rc = Z_STREAM_END at ended
  subst rc
  obtain ⟨output, actualBytes, valid⟩ := actual_loop_end_encoding history get ranges raw run
  exact ⟨output, by simpa only [out] using actualBytes, valid⟩

end ZlibF.Spec.Public.Proofs.CompressPrefix
