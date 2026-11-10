import ZlibF.Proof.«inflate.c.header-payload-code-packet»
namespace Zlib.Inflate.Proofs.PayloadPhaseView
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
open Zlib.Inftrees.Spec.DecodeTableStability
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- A same-call dynamic payload handoff. Construction provenance belongs
to its actual private source heap. The outer loop and inline LEN_ suffix
remain the translated program, including Z_TREES. -/
structure Packet (h : Heap) (r : ZStreamRef) (zs : Nat) (input : List UInt8) (flush : Int32)
    (future rest : List Bool) (dict prior decodedOutput : List UInt8) where
  originalZ : ZStream
  codeZ : ZStream
  codeState : InflateState
  codeHeap : Heap
  codeRegs : IL
  headerUsed : Nat
  decoded : List Nat
  alphabet : List Nat
  payloadInput : List Bool
  loopRegs : IL
  loopHeap : Heap
  originalGet : r.get h = some originalZ
  headerBound : headerUsed ≤ input.length
  codeCursor : codeRegs.next = inputAdvance originalZ.next_in headerUsed
  codeCount : codeRegs.have_.toNat + headerUsed = originalZ.avail_in.toNat
  codePut : codeRegs.put = originalZ.next_out
  codeLeft : codeRegs.left = originalZ.avail_out
  codeOut : codeRegs.out_ = codeRegs.left
  codeBits : codeRegs.bits.toNat ≤ 39
  codeWindow : codeState.wsize = 0
  sourceParser : CodeLens alphabet (codeState.nlen.toNat + codeState.ndist.toNat) (actualLengthPrefix codeState) (stream codeRegs (input.drop headerUsed) ++ future) payloadInput decoded
  symbols : Symbols (decoded.take codeState.nlen.toNat) (decoded.drop codeState.nlen.toNat) dict prior payloadInput rest decodedOutput
  boundary : CodeBoundary ⟨some r, some (.tab zs), syncBuf h, flush⟩ codeHeap r zs codeZ codeState codeRegs (input.drop headerUsed) decoded future payloadInput
  main : runX (inflate_run ⟨some r, some (.tab zs), syncBuf h, flush⟩) IL.init (syncAlloc h) =
    runX (xwhile (pure true) (inflate_dispatch ⟨some r, some (.tab zs), syncBuf h, flush⟩)) loopRegs loopHeap
  dispatch : runX (inflate_dispatch ⟨some r, some (.tab zs), syncBuf h, flush⟩) loopRegs loopHeap =
    runX (inflate_CODELENS ⟨some r, some (.tab zs), syncBuf h, flush⟩) codeRegs codeHeap

/-- Flatten the representation, cursor, global input remainder and exact
stable-table/source facts needed by the payload owner. -/
theorem Packet.endpoint
    {h : Heap} {r : ZStreamRef} {zs : Nat} {input : List UInt8} {flush : Int32}
    {future rest : List Bool} {dict prior decodedOutput : List UInt8}
    (p : Packet h r zs input flush future rest dict prior decodedOutput) :
    let state := p.boundary.state
    let regs := {p.boundary.regs with ret := 0}
    let heap := setI p.codeHeap zs state
    let sourceUsed := p.headerUsed + p.boundary.used
    sourceUsed ≤ input.length ∧ DefaultOriginState heap r zs p.codeZ state ∧
      DispatchBuffers heap r regs (input.drop sourceUsed) ∧ regs.bits.toNat ≤ 39 ∧
      regs.next = inputAdvance p.originalZ.next_in sourceUsed ∧
      regs.have_.toNat + sourceUsed = p.originalZ.avail_in.toNat ∧
      regs.put = p.originalZ.next_out ∧ regs.left = p.originalZ.avail_out ∧ regs.out_ = regs.left ∧
      state.wsize = 0 ∧ state.mode = LEN_ ∧
      Symbols (p.decoded.take p.codeState.nlen.toNat) (p.decoded.drop p.codeState.nlen.toNat) dict prior
        (stream regs (input.drop sourceUsed) ++ future) rest decodedOutput ∧
      runX (inflate_dispatch ⟨some r, some (.tab zs), syncBuf h, flush⟩) p.loopRegs p.loopHeap =
        if flush = Z_TREES then .ok ((.error Ex.leave, regs), heap)
        else runX (inflate_LEN_ ⟨some r, some (.tab zs), syncBuf h, flush⟩) regs heap := by
  dsimp only
  have headerBound := p.headerBound
  have bound := p.boundary.bound
  simp only [List.length_drop] at bound
  have packet := p.boundary.buffers
  rw [List.drop_drop] at packet
  refine ⟨by omega, p.boundary.origin, packet, by have := p.boundary.bits; have := p.codeBits; change p.boundary.regs.bits.toNat ≤ 39; omega,
    ?_, ?_, ?_, ?_, ?_, p.boundary.window.trans p.codeWindow, p.boundary.mode, ?_, ?_⟩
  · change p.boundary.regs.next = _
    rw [p.boundary.cursor, p.codeCursor, inputAdvance_add]
  · change p.boundary.regs.have_.toNat + _ = _
    have := p.boundary.count
    have := p.codeCount
    omega
  · exact p.boundary.put.trans p.codePut
  · exact p.boundary.left.trans p.codeLeft
  · change p.boundary.regs.out_ = p.boundary.regs.left
    rw [p.boundary.out, p.boundary.left]
    exact p.codeOut
  · have source := p.boundary.source
    rw [List.drop_drop] at source
    change Symbols _ _ _ _ ((natBits p.boundary.regs.bits.toNat p.boundary.regs.hold.toNat ++ bytesBits _) ++ future) _ _
    change stream p.boundary.regs (input.drop (p.headerUsed + p.boundary.used)) = _ at source
    have residual := p.boundary.residual
    rw [← source] at residual
    change Symbols _ _ _ _ (stream p.boundary.regs (input.drop (p.headerUsed + p.boundary.used)) ++ future) _ _
    rw [residual]
    exact p.symbols
  · exact p.dispatch.trans p.boundary.actual

#print axioms Packet.endpoint
end Zlib.Inflate.Proofs.PayloadPhaseView
