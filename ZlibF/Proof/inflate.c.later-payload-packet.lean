import ZlibF.Proof.«inflate.c.later-table-entry»
namespace Zlib.Inflate.Proofs.LaterHeader
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WrapperGlue Zlib.Inflate.Proofs.CumulativeParser
open ZlibF.Math.InflateHuffmanBodyContext
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- A later dynamic-block payload packet. The caller's pre-existing
output and saved dictionary are retained. Source Header has no Symbols
or complete-future premise. Actual constructor provenance remains nested
in boundary.construction; both stable tables are the final actual array. -/
structure GeneralPayloadPacket (c : Ctx) (h callHeap : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream)
    (s : InflateState) (l : IL) (bs : List UInt8) (future payload : List Bool) (L D : List Nat)
    (credited history : List UInt8) where
  entry : TableCodeEntry c h r zs z s l bs future payload L D
  boundary : PayloadPhaseView.CodeBoundary c (setI h zs entry.state) r zs z entry.state entry.regs (bs.drop entry.used) entry.decoded future payload
  allocator : DefAlloc z
  incoming : l.bits.toNat ≤ 39
  credit : AdlerCredit z boundary.state credited
  dictionary : InflateDictionary (setI h zs boundary.state) boundary.state history
  frame : HeaderFrame s boundary.state
  last : boundary.state.last = s.last
  header : Header 2 (stream l bs) L D boundary.payload
  main : runX (inflate_run c) IL.init callHeap = runX (xwhile (pure true) (inflate_dispatch c)) l h
  actual : runX (inflate_TABLE c) l h = if c.flush = Z_TREES then
    .ok ((.error Ex.leave, {boundary.regs with ret := 0}), setI h zs boundary.state)
    else runX (inflate_LEN_ c) {boundary.regs with ret := 0} (setI h zs boundary.state)

/-- A partial real CODELENS read retains a semantic continuation and all
incoming metadata. Neither a desired after-state nor a reader leave is a
premise of the producer below. -/
structure GeneralCodeWait (c : Ctx) (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream)
    (s : InflateState) (l : IL) (bs : List UInt8) (future payload : List Bool) (L D : List Nat)
    (credited history : List UInt8) where
  entry : TableCodeEntry c h r zs z s l bs future payload L D
  allocator : DefAlloc z
  incoming : l.bits.toNat ≤ 39
  regs : IL
  state : InflateState
  readUsed : Nat
  consumed : List Bool
  readFrame : state = {entry.state with lens := state.lens, «have» := state.«have»}
  readRun : runX (clRead c) entry.regs (setI h zs entry.state) = .ok ((.error Ex.leave, regs), setI (setI h zs entry.state) zs state)
  bound : readUsed ≤ (bs.drop entry.used).length
  origin : DefaultOriginState (setI h zs state) r zs z state
  buffers : DispatchBuffers (setI h zs state) r regs (bs.drop (entry.used + readUsed))
  credit : AdlerCredit z state credited
  dictionary : InflateDictionary (setI h zs state) state history
  frame : HeaderFrame s state
  last : state.last = s.last
  mode : state.mode = CODELENS
  bits : regs.bits.toNat ≤ max l.bits.toNat 21
  cursor : regs.next = inputAdvance l.next (entry.used + readUsed)
  count : regs.have_.toNat + (entry.used + readUsed) = l.have_.toNat
  put : regs.put = l.put
  left : regs.left = l.left
  out : regs.out_ = l.out_
  parsed : CodeLens entry.alphabet (entry.state.nlen.toNat + entry.state.ndist.toNat) (actualLengthPrefix state)
    (stream regs (bs.drop (entry.used + readUsed)) ++ future) payload entry.decoded
  sourceTrace : stream entry.regs (bs.drop entry.used) = consumed ++ stream regs (bs.drop (entry.used + readUsed))
  trace : ExactTrace entry.alphabet (entry.state.nlen.toNat + entry.state.ndist.toNat) (actualLengthPrefix entry.state) consumed (actualLengthPrefix state)
  actual : runX (inflate_TABLE c) l h = .ok ((.error Ex.leave, regs), setI h zs state)

theorem TableCodeEntry.payload_packet
    {c : Ctx} {h callHeap : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {future payload : List Bool} {L D : List Nat} {credited history : List UInt8}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (e : TableCodeEntry c h r zs z s l bs future payload L D)
    (allocator : DefAlloc z) (credit : AdlerCredit z s credited) (dictionary : InflateDictionary h s history)
    (incoming : l.bits.toNat ≤ 39)
    (main : runX (inflate_run c) IL.init callHeap = runX (xwhile (pure true) (inflate_dispatch c)) l h)
    (b : PayloadPhaseView.CodeBoundary c (setI h zs e.state) r zs z e.state e.regs (bs.drop e.used) e.decoded future payload) :
    Nonempty (GeneralPayloadPacket c h callHeap r zs z s l bs future payload L D credited history) := by
  have codeFrame : HeaderFrame e.state b.state := by unfold HeaderFrame; rw [b.metadata, b.readFrame]
  have frame := e.frame.trans codeFrame
  have last : b.state.last = s.last := by rw [b.metadata, b.readFrame]; exact e.last
  refine ⟨⟨e, b, allocator, incoming, frame.credit credit, frame.dictionary origin.good dictionary, frame, last,
    e.completed_header E b, main, ?_⟩⟩
  simpa only [setI_setI] using e.actual.trans b.actual

/-- Valid independent header syntax drives the actual reader to a genuine
partial wait or a complete later-block payload packet. Saved window,
allocator and arbitrary already-produced output are never reset. -/
theorem TableCodeEntry.wait_or_payload
    {c : Ctx} {h callHeap : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {future payload : List Bool} {L D : List Nat} {credited history : List UInt8}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (e : TableCodeEntry c h r zs z s l bs future payload L D)
    (allocator : DefAlloc z) (credit : AdlerCredit z s credited) (dictionary : InflateDictionary h s history)
    (incoming : l.bits.toNat ≤ 39)
    (main : runX (inflate_run c) IL.init callHeap = runX (xwhile (pure true) (inflate_dispatch c)) l h) :
    Nonempty (GeneralCodeWait c h r zs z s l bs future payload L D credited history) ∨
    Nonempty (GeneralPayloadPacket c h callHeap r zs z s l bs future payload L D credited history) := by
  have codeE : Env c (setI h zs e.state) r zs z e.state := ⟨E.strm, E.st, e.origin.good.live.hz, e.origin.good.live.hs⟩
  have parsed : CodeLens e.alphabet (e.state.nlen.toNat + e.state.ndist.toNat) (actualLengthPrefix e.state)
      (stream e.regs (bs.drop e.used) ++ future) payload e.decoded := by rw [e.emptyPrefix]; exact e.parsed
  rcases PayloadPhaseView.code_future_packet codeE e.origin e.buffers e.mode e.contents e.ordinary parsed e.eob e.validL e.validD with wait | complete
  · obtain ⟨regs, state, readUsed, readRun, _get, codeMode, readFrame, readBound, readB⟩ := wait
    obtain ⟨observedUsed, observedBound, current, packet, cursor, count, put, left, out, bits⟩ :=
      code_read_observed_packet codeE e.origin e.buffers e.mode readRun
    have sameUsed : observedUsed = readUsed := by
      have a := packet.bits.have_eq
      have d := readB.have_eq
      have prefixBound := e.bound
      simp only [List.length_drop] at a d observedBound readBound
      omega
    subst observedUsed
    have readHeaderFrame : HeaderFrame e.state state := by unfold HeaderFrame; rw [readFrame]
    have frame := e.frame.trans readHeaderFrame
    obtain ⟨consumed, causalSource, trace, remaining⟩ := code_wait_parse codeE e.origin e.buffers e.mode e.contents e.ordinary parsed readRun codeMode readBound readB
    apply Or.inl
    refine ⟨⟨e, allocator, incoming, regs, state, readUsed, consumed, readFrame, readRun, readBound, ?_, ?_, frame.credit credit, frame.dictionary origin.good dictionary,
      frame, ?_, codeMode, ?_, ?_, ?_, put.trans e.put, left.trans e.left, out.trans e.out, ?_, ?_, trace, ?_⟩⟩
    · simpa only [setI_setI] using current
    · simpa only [setI_setI, List.drop_drop] using packet
    · rw [readFrame]; exact e.last
    · have bound := e.bits
      omega
    · rw [cursor, e.cursor, inputAdvance_add]
    · have sourceCount := e.count
      omega
    · simpa only [List.drop_drop] using remaining
    · simpa only [List.drop_drop] using causalSource
    · rw [e.actual, inflate_CODELENS_eq, runX_bind, readRun]
      simp only [setI_setI]
  · obtain ⟨b⟩ := complete
    exact Or.inr (e.payload_packet E origin allocator credit dictionary incoming main b)

/-- Consumer geometry of the general packet, retaining arbitrary put,
left and out_ and both allocator callbacks on the same source stream. -/
theorem GeneralPayloadPacket.endpoint
    {c : Ctx} {h callHeap : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {future payload : List Bool} {L D : List Nat} {credited history : List UInt8}
    (p : GeneralPayloadPacket c h callHeap r zs z s l bs future payload L D credited history) :
    let state := p.boundary.state
    let regs := {p.boundary.regs with ret := 0}
    let used := p.entry.used + p.boundary.used
    used ≤ bs.length ∧ DefaultOriginState (setI h zs state) r zs z state ∧
      DispatchBuffers (setI h zs state) r regs (bs.drop used) ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧
      regs.bits.toNat ≤ max l.bits.toNat 21 ∧ state.mode = LEN_ ∧
      DefAlloc z ∧ AdlerCredit z state credited ∧ InflateDictionary (setI h zs state) state history ∧
      state.last = s.last ∧ Header 2 (stream l bs) L D p.boundary.payload := by
  dsimp only
  have bound := p.boundary.bound
  have prefixBound := p.entry.bound
  simp only [List.length_drop] at bound
  have packet := p.boundary.buffers
  rw [setI_setI, List.drop_drop] at packet
  have current := p.boundary.origin
  rw [setI_setI] at current
  refine ⟨by omega, current, packet, ?_, ?_, p.boundary.put.trans p.entry.put,
    p.boundary.left.trans p.entry.left, p.boundary.out.trans p.entry.out, ?_, p.boundary.mode,
    p.allocator, p.credit, p.dictionary, p.last, p.header⟩
  · change p.boundary.regs.next = _
    rw [p.boundary.cursor, p.entry.cursor, inputAdvance_add]
  · change p.boundary.regs.have_.toNat + _ = _
    have := p.boundary.count
    have := p.entry.count
    omega
  · change p.boundary.regs.bits.toNat ≤ _
    have := p.boundary.bits
    have := p.entry.bits
    omega

#print axioms TableCodeEntry.payload_packet
#print axioms TableCodeEntry.wait_or_payload
#print axioms GeneralPayloadPacket.endpoint
end Zlib.Inflate.Proofs.LaterHeader
