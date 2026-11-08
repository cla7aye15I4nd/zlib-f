import ZlibF.Proof.«deflate.c.engine.public-first-finish-encoding»
import ZlibF.Proof.«deflate.c.engine.public-header-finish-encoding»
import ZlibF.Proof.«deflate.c.engine.public-first-input»
import ZlibF.Proof.«deflate.c.engine.public-header-resume-input»
import ZlibF.Proof.«deflate.c.engine.all-scalar-history»

/-! # Actual initialized states carry the observed input and output history -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Encoding for exactly the observed accepted input and cumulative
output. The phase alternatives retain their physical state together with
their independent format meaning. Published bytes are observations, so
legal caller edits may reuse old output storage. Actual initialization and
execution establish this invariant; it is not a callee contract. -/
structure DefaultEncodingState (h : Heap) (r : ZStreamRef) (ds : Nat)
    (z : ZStream) (d : DeflateState) (config : EngineConfig) (accepted observed : List UInt8) : Prop where
  protocol : DefaultFinishBoundary h r ds z d config
  checksum : z.adler = (ZlibF.Spec.adler32 accepted).toUInt64
  phase :
    (accepted = [] ∧ observed = [] ∧ ∃ input,
      EngineStart h r ds z d ∧ BufferedBoundary h r ds z d input 0 0 [] config) ∨
    (accepted = [] ∧ observed = [120] ∧ ∃ input,
      BufferedBoundary h r ds z d input 0 0 [] config ∧ d.status = BUSY_STATE ∧ HeaderPending h d [120]) ∨
    (∃ input origin base xs published, observed = [120,156] ++ published ∧
      BufferedBoundary h r ds z d input origin base xs config ∧ d.status = BUSY_STATE ∧
      RawPrefix h d input base published ∧ inputPrefix input (origin + fillEnd d) = accepted) ∨
    (∃ published, observed = [120,156] ++ published ∧
      FinishingPhase d config ∧ FinishedEncoding h d accepted published)

/-- A proved actual run determines the same protocol state returned by
the complete all-scalar execution theorem. This attaches the structural
history facts to the exact heap and state used by encoding refinements. -/
theorem default_request_protocol_of_run {h after : Heap} {r : ZStreamRef} {ds : Nat}
    {z z' : ZStream} {d result : DeflateState} {config : EngineConfig} {flush rc : Int32}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (raw : z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo)
    (run : deflate (some r) flush h = .ok (rc, after)) (goodA : DGood after r ds z' result) :
    DefaultFinishBoundary after r ds z' result config := by
  obtain ⟨_used, _produced, _rc, other, otherZ, otherD, otherRun, stateA, _buffersA, _account, _allowed⟩ :=
    boundary.all_scalar_request buffers raw flush
  have heaps : other = after := (Prod.mk.inj (Except.ok.inj (otherRun.symm.trans run))).2
  subst other
  have sameZ : otherZ = z' := Option.some.inj (stateA.good.live.hz.symm.trans goodA.live.hz)
  have sameD : otherD = result := Option.some.inj (stateA.good.live.hs.symm.trans goodA.live.hs)
  subst otherZ otherD
  exact stateA

/-- Legal caller replacement retains the observed accepted and emitted
byte lists and every initialized/header/working/finished encoding phase. -/
theorem DefaultEncodingState.rebuffer {h g : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {accepted observed : List UInt8}
    (state : DefaultEncodingState h r ds z d config accepted observed) (edit : Rebuffer h g r) :
    ∃ zg, r.get g = some zg ∧ DefaultEncodingState g r ds zg d config accepted observed := by
  obtain ⟨zg, getG, protocolG⟩ := state.protocol.rebuffer edit
  have header := state.protocol.no_header
  have checksumG : zg.adler = (ZlibF.Spec.adler32 accepted).toUInt64 := by
    have originalEdit := edit
    obtain ⟨_fresh, _uniq, _globals, _frame, old, next, oldGet, nextGet, fields⟩ := originalEdit
    have oldEq : old = z := Option.some.inj (oldGet.symm.trans state.protocol.good.live.hz)
    have nextEq : next = zg := Option.some.inj (nextGet.symm.trans getG)
    subst old next
    rw [fields]
    exact state.checksum
  refine ⟨zg, getG, protocolG, checksumG, ?_⟩
  rcases state.phase with ⟨emptyInput, emptyOutput, input, start, boundary⟩ |
      ⟨emptyInput, headerOutput, input, boundary, status, encoding⟩ |
      ⟨input, origin, base, xs, published, outputEq, boundary, status, encoding, inputEq⟩ |
      ⟨published, outputEq, phase, encoding⟩
  · obtain ⟨zs, startG⟩ := rebuffer_engine_start start edit header
    obtain ⟨zb, getB, boundaryG⟩ := rebuffer_buffered_boundary boundary edit header
    have sameS : zs = zg := Option.some.inj (startG.good.live.hz.symm.trans getG)
    have sameB : zb = zg := Option.some.inj (getB.symm.trans getG)
    subst zs zb
    exact Or.inl ⟨emptyInput, emptyOutput, input, startG, boundaryG⟩
  · obtain ⟨zb, getB, boundaryG⟩ := rebuffer_buffered_boundary boundary edit header
    have sameB : zb = zg := Option.some.inj (getB.symm.trans getG)
    subst zb
    exact Or.inr (Or.inl ⟨emptyInput, headerOutput, input, boundaryG, status,
      encoding.rebuffer state.protocol.good edit⟩)
  · obtain ⟨zb, getB, boundaryG⟩ := rebuffer_buffered_boundary boundary edit header
    have sameB : zb = zg := Option.some.inj (getB.symm.trans getG)
    subst zb
    exact Or.inr (Or.inr (Or.inl ⟨input, origin, base, xs, published, outputEq, boundaryG,
      status, encoding.rebuffer state.protocol.good edit, inputEq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨published, outputEq, phase, encoding.rebuffer state.protocol.good edit⟩))

/-- A physically drained finished state has independent zlib validity for
the complete observed output and exactly the observed accepted input. -/
theorem DefaultEncodingState.drained {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {accepted observed : List UInt8}
    (state : DefaultEncodingState h r ds z d config accepted observed)
    (status : d.status = FINISH_STATE) (wrap : d.wrap = -1) (pending : d.pending = 0) :
    ZlibF.Spec.Zlib.Valid accepted observed := by
  rcases state.phase with ⟨_emptyInput, _emptyOutput, _input, start, _boundary⟩ |
      ⟨_emptyInput, _headerOutput, _input, _boundary, busy, _encoding⟩ |
      ⟨_input, _origin, _base, _xs, _published, _outputEq, _boundary, busy, _encoding, _inputEq⟩ |
      ⟨published, outputEq, _phase, encoding⟩
  · exact False.elim ((by decide : INIT_STATE ≠ FINISH_STATE) (start.status.symm.trans status))
  · exact False.elim ((by decide : BUSY_STATE ≠ FINISH_STATE) (busy.symm.trans status))
  · exact False.elim ((by decide : BUSY_STATE ≠ FINISH_STATE) (busy.symm.trans status))
  · rw [outputEq]
    exact encoding.drained wrap pending

end Zlib.Deflate.Engine.Proofs
