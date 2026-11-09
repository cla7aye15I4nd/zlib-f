import ZlibF.Proof.«compress.c.tail»

/-! # The actual wrapper loop retains its exact five private allocation keys -/
namespace ZlibF.Spec.Public.Proofs.CompressTail
open C Zlib.Compress Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs Zlib.Deflate.Proofs.DefaultInit
open ZlibF.Spec.Public.Proofs.CompressLoop ZlibF.Spec.Public.Proofs.CompressCaller
open ZlibF.Spec.Public.Proofs.CompressPrefix
set_option autoImplicit false
set_option maxRecDepth 100000

def configOwned (ds : Nat) (config : EngineConfig) (b : Nat) : Prop :=
  b = ds ∨ config.window = .ref (.blk b) 0 ∨ config.prev = .ref (.blk b) 0 ∨
    config.head = .ref (.blk b) 0 ∨ config.pending = .ref (.blk b) 0

/-- Every phase of the actual default protocol retains the same private
keys. Negating wrap during finishing changes none of these keys. -/
theorem boundary_owned_config {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : DefaultFinishBoundary h r ds z d config) :
    DeflateOwned ds d = configOwned ds config := by
  have keys : d.window = config.window ∧ d.prev = config.prev ∧
      d.head = config.head ∧ d.pending_buf = config.pending := by
    rcases boundary.phase with ⟨i, o, b, start, buffered⟩ | ⟨i, o, b, xs, buffered, _status⟩ | finishing
    · exact ⟨congrArg EngineConfig.window buffered.configuration, congrArg EngineConfig.prev buffered.configuration,
        congrArg EngineConfig.head buffered.configuration, congrArg EngineConfig.pending buffered.configuration⟩
    · exact ⟨congrArg EngineConfig.window buffered.configuration, congrArg EngineConfig.prev buffered.configuration,
        congrArg EngineConfig.head buffered.configuration, congrArg EngineConfig.pending buffered.configuration⟩
    · exact ⟨congrArg EngineConfig.window finishing.configuration, congrArg EngineConfig.prev finishing.configuration,
        congrArg EngineConfig.head finishing.configuration, congrArg EngineConfig.pending finishing.configuration⟩
  funext b
  simp only [DeflateOwned, configOwned, keys.1, keys.2.1, keys.2.2.1, keys.2.2.2]

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

/-- A real body preserves all live-object presence, allocation indices
and the fixed private keys in the same initialized protocol. -/
theorem body_resources {h after : Heap} {slot ds ob oo : Nat} {z : ZStream} {d : DeflateState}
    {config : EngineConfig} {old : Int32} {left sourceLen : UInt64} {source : List UInt8} {last : Locals}
    (boundary : DefaultFinishBoundary h (.tab slot) ds z d config) (globals : LibraryGlobals h)
    (ranges : Ranges h (.tab slot) z left sourceLen source) (pointer : z.next_out = .ref (.blk ob) oo)
    (actual : body (some (.tab slot)) (old, left, sourceLen) h = .ok (last, after)) :
    ∃ z' result, DefaultFinishBoundary after (.tab slot) ds z' result config ∧ Shape h after ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  have get : h.streams slot = some z := boundary.good.live.hz
  have edit := prepare_rebuffer boundary.good globals left sourceLen
  obtain ⟨zp, getP, boundaryP⟩ := boundary.rebuffer edit
  have sameP : zp = CompressLoop.preparedStream z left sourceLen :=
    Option.some.inj (getP.symm.trans (prepare_get h slot z left sourceLen get))
  subst zp
  have rangesP := prepare_ranges boundary.good ranges
  obtain ⟨buffersP, _snapshotP⟩ := ranges_current getP rangesP
  have pointerP : (CompressLoop.preparedStream z left sourceLen).next_out = .ref (.blk ob) oo := pointer
  let flush := if (prepare h slot z left sourceLen).2.1 != 0 then Z_NO_FLUSH else Z_FINISH
  obtain ⟨used, written, rc, computed, z', result, engineRun, boundaryA, _buffersA, _goodA,
    _account, _bytesA, _tin, _tout, _allowed, _errors, _bad, _ended, shape, _frame, _live, count, next⟩ :=
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
  have heaps : computed = after := (Prod.mk.inj (Except.ok.inj (bodyRun.symm.trans actual))).2
  subst computed
  have preparedShape : Shape h (prepare h slot z left sourceLen).2.2 := by
    rw [prepare_eq_put h slot z left sourceLen get]
    exact shape_put boundary.good.live.hz _
  refine ⟨z', result, boundaryA, preparedShape.trans shape, ?_, ?_⟩
  · rw [count, prepare_eq_put h slot z left sourceLen get, ZStreamRef.put_nalloc]
  · rw [next, prepare_eq_put h slot z left sourceLen get, ZStreamRef.put_nextBlk]

/-- A finite prefix retains the initialized configuration, all live-object
presence and both allocation indices. This uses actual body executions;
caller rebuffer histories are not substituted for the concrete loop. -/
theorem prefix_resources {slot ds ob oo k : Nat} {start after : Heap} {last : Locals}
    {first : ZStream} {d : DeflateState} {config : EngineConfig}
    {left sourceLen : UInt64} {source : List UInt8}
    (history : DefaultDataTrace (.tab slot) start {})
    (initial : DefaultFinishBoundary start (.tab slot) ds first d config)
    (ranges : Ranges start (.tab slot) first left sourceLen source)
    (pointer : first.next_out = .ref (.blk ob) oo)
    (execution : ActualPrefix slot start (Z_OK, left, sourceLen) k after last) :
    ∃ z' result, DefaultFinishBoundary after (.tab slot) ds z' result config ∧ Shape start after ∧
      after.nalloc = start.nalloc ∧ after.nextBlk = start.nextBlk := by
  induction execution with
  | nil => exact ⟨first, d, initial, Shape.refl start, rfl, rfl⟩
  | @step k h after current next previous _guard actual ih =>
    obtain ⟨currentZ, currentD, currentBoundary, shapeBefore, countBefore, nextBefore⟩ := ih
    obtain ⟨used, log, observedZ, known⟩ :=
      actual_prefix_sound history initial.good.live.hz ranges pointer previous
    have same : currentZ = observedZ := Option.some.inj (currentBoundary.good.live.hz.symm.trans known.get)
    subst currentZ
    have globals := ZlibF.Spec.Public.Proofs.DeflateCore.calls_globals (trace_calls known.history)
    have currentPointer : observedZ.next_out = .ref (.blk ob) (oo + log.output.length) := by
      rw [known.outputPtr, pointer]
      rfl
    rcases current with ⟨old, l, n⟩
    obtain ⟨z', result, boundaryA, shapeAfter, countAfter, nextAfter⟩ :=
      body_resources currentBoundary globals known.remaining currentPointer actual
    exact ⟨z', result, boundaryA, shapeBefore.trans shapeAfter, countAfter.trans countBefore,
      nextAfter.trans nextBefore⟩

end ZlibF.Spec.Public.Proofs.CompressTail
