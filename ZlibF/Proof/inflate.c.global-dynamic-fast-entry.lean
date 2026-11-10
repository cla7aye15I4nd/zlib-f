import ZlibF.Proof.«inflate.c.global-dynamic-payload-composition»
import ZlibF.Proof.«inflate.c.global-fast-prefix-ready»

namespace Zlib.Inflate.Proofs.FunctionalEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inftrees SlowTokenPath
set_option autoImplicit false
set_option maxRecDepth 10000

/-- The actual initial dynamic payload performs its literal LEN_ write and
RESTORE, then produces the real fast callee prelude and future-aware loop
entry. Every table, saved-history and output-prefix fact comes from the
header packet; the only branch selection is the actual fast C guard. The
original same-call mainwhile remains available through ready.packet.main. -/
theorem DynamicPayloadReady.fast_entry
    {h : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog}
    {input : List UInt8} {flush : Int32} {future rest : List Bool} {decoded : List UInt8}
    (ready : DynamicPayloadReady h r zs log input flush future rest decoded)
    (fast : (ready.packet.boundary.regs.have_ >= 6 && ready.packet.boundary.regs.left >= 258 &&
      ready.packet.boundary.regs.bits < 8) = true) :
    let p := ready.packet
    let regs := {p.boundary.regs with ret := 0}
    let state := p.boundary.state
    let payloadHeap := setI p.codeHeap zs state
    let lengthState := {state with mode := LEN}
    let lengthHeap := setI payloadHeap zs lengthState
    let restoredHeap := setI (r.put lengthHeap (leaveStream p.codeZ regs)) zs (leaveState lengthState regs)
    let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
    ∃ (ctx : FastLoopContext) (q : Zlib.Inffast.L),
      runX (inflate_LEN_ c) regs payloadHeap =
        runX (do Zlib.Inffast.inflate_fast (some r) regs.out_; inflateAfterFast c) regs restoredHeap ∧
      C.run (fastEntryPrefix (some r) regs.out_) restoredHeap = .ok ((ctx.c, q), restoredHeap) ∧
      ctx.r = r ∧ ctx.zs = zs ∧ ctx.z = leaveStream p.codeZ regs ∧
      ctx.s = leaveState lengthState regs ∧ q.broke = false ∧
      FastFutureReady ctx (p.decoded.take p.codeState.nlen.toNat) (p.decoded.drop p.codeState.nlen.toNat)
        [] future rest decoded restoredHeap q := by
  dsimp only
  let p := ready.packet
  let regs := {p.boundary.regs with ret := 0}
  let state := p.boundary.state
  let payloadHeap := setI p.codeHeap zs state
  let lengthState := {state with mode := LEN}
  let lengthHeap := setI payloadHeap zs lengthState
  let restoredHeap := setI (r.put lengthHeap (leaveStream p.codeZ regs)) zs (leaveState lengthState regs)
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have initial := ready.representation
  obtain ⟨_bound, origin, _buffers, _bits, _next, _have, _put, _left, noOutput, window, mode, symbols, _dispatch⟩ := p.endpoint
  have dictionary := initial.2.2.2.2
  have retained := dictionary_zero_window_empty origin.good window dictionary
  have size := congrArg List.length retained
  simp only [List.length_drop, List.length_nil] at size
  change (log.dictionary ++ log.output).length -
    ((log.dictionary ++ log.output).length - 2 ^ state.wbits.toNat) = 0 at size
  have capacity := Nat.two_pow_pos state.wbits.toNat
  have emptyHistory : log.dictionary ++ log.output = [] := List.length_eq_zero_iff.mp (by omega)
  obtain ⟨emptyDictionary, emptyOutput⟩ := List.append_eq_nil_iff.mp emptyHistory
  have parsed : Symbols (p.decoded.take p.codeState.nlen.toNat) (p.decoded.drop p.codeState.nlen.toNat)
      [] [] (stream regs (input.drop (p.headerUsed + p.boundary.used)) ++ future) rest decoded := by
    simpa only [emptyDictionary, emptyOutput] using symbols
  have env : Env c payloadHeap r zs p.codeZ state := ⟨rfl, rfl, origin.good.live.hz, origin.good.live.hs⟩
  have lengthRepresentation := initial.len_start mode
  have lengthOrigin := lengthRepresentation.1
  have lengthEnv : Env c lengthHeap r zs p.codeZ lengthState :=
    ⟨rfl, rfl, lengthOrigin.good.live.hz, lengthOrigin.good.live.hs⟩
  obtain ⟨restoreRun, restoredRepresentation⟩ := lengthRepresentation.restore lengthEnv
  obtain ⟨restoredOrigin, restoredBuffers, _restoredBits, restoredTables, _restoredDictionary⟩ := restoredRepresentation
  have flags : ∀ (ref : CodeRef) (offset : Nat) (codes : Array Code),
      (leaveState lengthState regs).distcode = .ref ref offset → Space.get restoredHeap ref = some codes →
      Zlib.Inftrees.Spec.FastTableFlags.QueryCompatible DISTS codes offset (leaveState lengthState regs).distbits.toNat := by
    intro ref offset codes pointer get
    have actualPointer : (leaveState lengthState regs).distcode = .ref (.istate_codes zs) p.boundary.offset := p.boundary.distPtr
    have same := actualPointer.symm.trans pointer
    cases same
    have actualGet : Space.get restoredHeap (CodeRef.istate_codes zs) = some (leaveState lengthState regs).codes :=
      CodeRef.get_istate_codes restoredOrigin.good.live.hs
    have sameCodes : codes = (leaveState lengthState regs).codes := Option.some.inj (get.symm.trans actualGet)
    subst codes
    exact packet_distance_fast_flags p
  obtain ⟨ctx, q, prefixRun, sameR, sameIndex, sameZ, sameS, _lenWidth, _distWidth,
    _lengthPointer, _distancePointer, notBroken, semantic⟩ :=
    fastEntryPrefix_future_zero_window restoredOrigin.toDefaultStateJ restoredBuffers
      (by change DataTableMode LEN; unfold DataTableMode; decide)
      rfl rfl rfl rfl rfl rfl restoredTables flags window noOutput parsed fast
  refine ⟨ctx, q, ?_, prefixRun, sameR, sameIndex, sameZ, sameS, notBroken, semantic⟩
  have beginRun : runX (inflate_LEN_ c) regs payloadHeap = runX (inflate_LEN c) regs lengthHeap := by
    unfold inflate_LEN_
    rw [runX_bind, runX_setMode env]
  rw [beginRun]
  unfold inflate_LEN
  rw [runX_bind, runX_get]
  simp only []
  have fastGuard : (regs.have_ >= 6 && regs.left >= 258 && regs.bits < 8) = true := fast
  rw [fastGuard]
  simp only [ite_true]
  rw [runX_bind, restoreRun]
  rfl

def DynamicPayloadReady.fastRegs
    {h : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog}
    {input : List UInt8} {flush : Int32} {future rest : List Bool} {decoded : List UInt8}
    (ready : DynamicPayloadReady h r zs log input flush future rest decoded) : IL :=
  {ready.packet.boundary.regs with ret := 0}

def DynamicPayloadReady.fastHeap
    {h : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog}
    {input : List UInt8} {flush : Int32} {future rest : List Bool} {decoded : List UInt8}
    (ready : DynamicPayloadReady h r zs log input flush future rest decoded) : Heap :=
  let p := ready.packet
  let state := {p.boundary.state with mode := LEN}
  let heap := setI (setI p.codeHeap zs p.boundary.state) zs state
  setI (r.put heap (leaveStream p.codeZ ready.fastRegs)) zs (leaveState state ready.fastRegs)

/-- Complete finite actual fast-loop execution, produced from the same
dynamic source packet. Its source caller/RESTORE and callee-entry cuts are
retained beside the physical budgets and exact independent continuation. -/
structure DynamicFastExecution
    {h : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog}
    {input : List UInt8} {flush : Int32} {future rest : List Bool} {decoded : List UInt8}
    (ready : DynamicPayloadReady h r zs log input flush future rest decoded) where
  ctx : FastLoopContext
  initial : Zlib.Inffast.L
  result : Zlib.Inffast.L
  after : Heap
  startOff : Nat
  prefixRun : C.run (fastEntryPrefix (some r) ready.fastRegs.out_) ready.fastHeap =
    .ok ((ctx.c, initial), ready.fastHeap)
  caller : runX (inflate_LEN_ ⟨some r, some (.tab zs), syncBuf h, flush⟩)
      ready.fastRegs (setI ready.packet.codeHeap zs ready.packet.boundary.state) =
    runX (do Zlib.Inffast.inflate_fast (some r) ready.fastRegs.out_
             inflateAfterFast ⟨some r, some (.tab zs), syncBuf h, flush⟩) ready.fastRegs ready.fastHeap
  actual : C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c) (fastLoopCond ctx) initial)
    ready.fastHeap = .ok (result, after)
  semantic : FastFutureExit ctx (ready.packet.decoded.take ready.packet.codeState.nlen.toNat)
    (ready.packet.decoded.drop ready.packet.codeState.nlen.toNat) [] future rest decoded after result
  inputBudget : FastLoopInputBudget ctx startOff initial.bits.toNat result
  outputRange : FastLoopOutputRange ctx after result
  inputLimit : FastLoopInputLimit ctx result
  byteSizes : ByteViewSizes ready.fastHeap after
  stream : ctx.r = r
  state : ctx.zs = zs
  notBroken : initial.broke = false

theorem DynamicPayloadReady.fast_run
    {h : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog}
    {input : List UInt8} {flush : Int32} {future rest : List Bool} {decoded : List UInt8}
    (ready : DynamicPayloadReady h r zs log input flush future rest decoded)
    (fast : (ready.packet.boundary.regs.have_ >= 6 && ready.packet.boundary.regs.left >= 258 &&
      ready.packet.boundary.regs.bits < 8) = true) : Nonempty (DynamicFastExecution ready) := by
  obtain ⟨ctx, initial, caller, prefixRun, stream, state, _z, _s, notBroken, semantic⟩ := ready.fast_entry fast
  obtain ⟨startOff, result, after, run, exited, budget, output, limit, sizes⟩ := semantic.run_entry_accounted
  exact ⟨⟨ctx, initial, result, after, startOff, prefixRun, caller, run, exited, budget,
    output, limit, sizes, stream, state, notBroken⟩⟩

#print axioms DynamicPayloadReady.fast_entry
#print axioms DynamicPayloadReady.fast_run
end Zlib.Inflate.Proofs.FunctionalEpoch
