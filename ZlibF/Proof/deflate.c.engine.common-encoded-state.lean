import ZlibF.Proof.«deflate.c.engine.common-header-drain-encoding»
import ZlibF.Proof.«deflate.c.engine.common-finished-encoding»
import ZlibF.Proof.«deflate.c.engine.common-no-flush-total»
import ZlibF.Proof.«deflate.c.engine.common-finish-total»
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
legal caller edits may reuse old output storage. Actual split-header initialization and
execution establish this invariant; it is not a callee contract. -/
structure CommonEncodingState (h : Heap) (r : ZStreamRef) (ds : Nat)
    (z : ZStream) (d : DeflateState) (config : EngineConfig) (accepted observed : List UInt8) : Prop where
  protocol : CommonSlowFinishBoundary h r ds z d config
  checksum : z.adler = (ZlibF.Spec.adler32 accepted).toUInt64
  phase :
    (accepted = [] ∧ observed = [120] ∧ ∃ input,
      BufferedBoundary h r ds z d input 0 0 [] config ∧ d.status = BUSY_STATE ∧ CommonHeaderPending h d config.level [120]) ∨
    (∃ input origin base xs published, observed = levelHeaderPrefix config.level ++ published ∧
      BufferedBoundary h r ds z d input origin base xs config ∧ d.status = BUSY_STATE ∧
      RawPrefix h d input base published ∧ inputPrefix input (origin + fillEnd d) = accepted) ∨
    (∃ published, observed = levelHeaderPrefix config.level ++ published ∧
      FinishingPhase d config ∧ CommonFinishedEncoding h d config.level accepted published)

/-- A proved actual run determines the same protocol state returned by
the complete NO_FLUSH/FINISH execution theorem. This attaches the structural
history facts to the exact heap and state used by encoding refinements. -/
theorem common_request_protocol_of_run {h after : Heap} {r : ZStreamRef} {ds : Nat}
    {z z' : ZStream} {d result : DeflateState} {config : EngineConfig} {flush rc : Int32}
    (boundary : CommonSlowFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (raw : z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo)
    (ordinary : flush = Z_NO_FLUSH ∨ flush = Z_FINISH)
    (run : deflate (some r) flush h = .ok (rc, after)) (goodA : DGood after r ds z' result) :
    CommonSlowFinishBoundary after r ds z' result config := by
  obtain ⟨_used, _produced, _rc, other, otherZ, otherD, otherRun, stateA, _buffersA, _account, _allowed⟩ :=
    (show ∃ used produced rc after z' result,
      deflate (some r) flush h = .ok (rc, after) ∧
      CommonSlowFinishBoundary after r ds z' result config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧ (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_STREAM_ERROR ∨ rc = Z_BUF_ERROR) from by
      rcases ordinary with eq | eq
      · subst flush
        obtain ⟨used, produced, rc, after, z', result, run, stateA, buffersA, accountA, allowed⟩ := boundary.no_flush_total buffers raw
        exact ⟨used, produced, rc, after, z', result, run, stateA, buffersA, accountA,
          allowed.elim Or.inl (fun other => Or.inr (Or.inr other))⟩
      · subst flush
        exact boundary.finish_total buffers raw)
  have heaps : other = after := (Prod.mk.inj (Except.ok.inj (otherRun.symm.trans run))).2
  subst other
  have sameZ : otherZ = z' := Option.some.inj (stateA.good.live.hz.symm.trans goodA.live.hz)
  have sameD : otherD = result := Option.some.inj (stateA.good.live.hs.symm.trans goodA.live.hs)
  subst otherZ otherD
  exact stateA

/-- Legal caller replacement retains the observed accepted and emitted
byte lists and every post-header/working/finished encoding phase. -/
theorem CommonEncodingState.rebuffer {h g : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {accepted observed : List UInt8}
    (state : CommonEncodingState h r ds z d config accepted observed) (edit : Rebuffer h g r) :
    ∃ zg, r.get g = some zg ∧ CommonEncodingState g r ds zg d config accepted observed := by
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
  rcases state.phase with ⟨emptyInput, headerOutput, input, boundary, status, encoding⟩ |
      ⟨input, origin, base, xs, published, outputEq, boundary, status, encoding, inputEq⟩ |
      ⟨published, outputEq, phase, encoding⟩
  · obtain ⟨zb, getB, boundaryG⟩ := rebuffer_buffered_boundary boundary edit header
    have sameB : zb = zg := Option.some.inj (getB.symm.trans getG)
    subst zb
    exact Or.inl ⟨emptyInput, headerOutput, input, boundaryG, status,
      encoding.rebuffer state.protocol.good edit⟩
  · obtain ⟨zb, getB, boundaryG⟩ := rebuffer_buffered_boundary boundary edit header
    have sameB : zb = zg := Option.some.inj (getB.symm.trans getG)
    subst zb
    exact Or.inr (Or.inl ⟨input, origin, base, xs, published, outputEq, boundaryG,
      status, encoding.rebuffer state.protocol.good edit, inputEq⟩)
  · exact Or.inr (Or.inr ⟨published, outputEq, phase, encoding.rebuffer state.protocol.good edit⟩)

/-- A physically drained finished state has independent zlib validity for
the complete observed output and exactly the observed accepted input. -/
theorem CommonEncodingState.drained {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {accepted observed : List UInt8}
    (state : CommonEncodingState h r ds z d config accepted observed)
    (status : d.status = FINISH_STATE) (wrap : d.wrap = -1) (pending : d.pending = 0) :
    ZlibF.Spec.Zlib.Valid accepted observed := by
  rcases state.phase with ⟨_emptyInput, _headerOutput, _input, _boundary, busy, _encoding⟩ |
      ⟨_input, _origin, _base, _xs, _published, _outputEq, _boundary, busy, _encoding, _inputEq⟩ |
      ⟨published, outputEq, _phase, encoding⟩
  · exact False.elim ((by decide : BUSY_STATE ≠ FINISH_STATE) (busy.symm.trans status))
  · exact False.elim ((by decide : BUSY_STATE ≠ FINISH_STATE) (busy.symm.trans status))
  · rw [outputEq]
    exact encoding.drained wrap pending

end Zlib.Deflate.Engine.Proofs
