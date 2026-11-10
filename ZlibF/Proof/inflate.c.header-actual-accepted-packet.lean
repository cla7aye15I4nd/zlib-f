import ZlibF.Proof.«inflate.c.header-actual-prefix-history»
namespace Zlib.Inflate.Proofs.ActualHeader
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WrapperGlue Zlib.Inflate.Proofs.LaterHeader
open ZlibF.Math.InflateHuffmanBodyContext
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem retained_dictionary_header_put
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z streamZ : ZStream} {s state : InflateState} {history : List UInt8}
    (good : Good h r zs z s) (frame : HeaderFrame s state) (dictionary : InflateDictionary h s history) :
    InflateDictionary (setI (r.put h streamZ) zs state) state history := by
  rcases dictionary with ⟨zero, empty⟩ | ⟨ref, off, a, window, get, bound, values⟩
  · exact Or.inl ⟨by rw [frame]; exact zero, empty⟩
  · rcases good.inv.win.block with null | ⟨b, bytes, ptr, _get, _ro, _size⟩
    · rw [null] at window; cases window
    · rw [ptr] at window
      cases window
      refine Or.inr ⟨.blk b, 0, a, ?_, ?_, ?_, ?_⟩
      · rw [frame]; exact ptr
      · rw [byte_view_get_setI, byte_view_get_stream_put]
        exact get
      · rw [frame]; exact bound
      · rw [frame]; exact values

/-- Accepted dynamic-header payload handoff produced from actual branch
observations and a causal source-prefix ledger. No valid future/Header/
Symbols oracle appears. Constructor PairTrace and final stable tables are
retained by ready.tables, with callbacks, credit, saved window and true
same-call continuation on the same concrete heap. -/
structure AcceptedPacket (c : Ctx) (h callHeap : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream)
    (s : InflateState) (l : IL) (bs : List UInt8) (alphabet : List Nat) (credited history : List UInt8) where
  prefixData : HeaderSourcePrefix s l bs alphabet
  observation : CodeReadObservation c h r zs z s l bs alphabet
  normal : observation.outcome = .ok ()
  mode : observation.state.mode = CODELENS
  ready : TailReady c observation.heap r zs observation.streamZ observation.state observation.regs (bs.drop observation.used)
  allocator : DefAlloc observation.streamZ
  zalloc : observation.streamZ.zalloc = z.zalloc
  zfree : observation.streamZ.zfree = z.zfree
  credit : AdlerCredit observation.streamZ ready.tables.state credited
  dictionary : InflateDictionary (setI observation.heap zs ready.tables.state) ready.tables.state history
  last : ready.tables.state.last = s.last
  liveBits : observation.regs.bits.toNat ≤ 39
  header : Header 2 prefixData.bodyInput
    ((actualLengthPrefix observation.state).take observation.state.nlen.toNat)
    ((actualLengthPrefix observation.state).drop observation.state.nlen.toNat)
    (stream observation.regs (bs.drop observation.used))
  main : runX (inflate_run c) IL.init callHeap = runX (xwhile (pure true) (inflate_dispatch c)) l h
  actual : runX (inflate_dispatch c) l h = if c.flush = Z_TREES then
    .ok ((.error Ex.leave, {observation.regs with ret := 0}), setI observation.heap zs ready.tables.state)
    else runX (inflate_LEN_ c) {observation.regs with ret := 0} (setI observation.heap zs ready.tables.state)

/-- Select the accepted branch of the automatic source classifiers.
Every accepted after-fact is derived from those exact runs; the causal
prefix is initialized by actual reads and advanced by actual Trace outputs. -/
theorem accepted_packet_from_observations
    {c : Ctx} {h callHeap : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs credited history : List UInt8} {alphabet : List Nat}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s) (mode : s.mode = CODELENS)
    (allocator : DefAlloc z) (credit : AdlerCredit z s credited) (dictionary : InflateDictionary h s history)
    (incoming : l.bits.toNat ≤ 39)
    (main : runX (inflate_run c) IL.init callHeap = runX (xwhile (pure true) (inflate_dispatch c)) l h)
    (prefixData : HeaderSourcePrefix s l bs alphabet)
    (observation : CodeReadObservation c h r zs z s l bs alphabet)
    (normal : observation.outcome = .ok ()) (code : observation.state.mode = CODELENS)
    (ready : TailReady c observation.heap r zs observation.streamZ observation.state observation.regs (bs.drop observation.used)) :
    Nonempty (AcceptedPacket c h callHeap r zs z s l bs alphabet credited history) := by
  obtain ⟨state0, _used0, get0, _bound0, _B0, _shape, _bits, readFrame, _size, _have, _values, _modes, _done⟩ := observation.full.1
  have stateEq : state0 = observation.state := Option.some.inj (get0.symm.trans observation.origin.good.live.hs)
  rw [stateEq] at readFrame
  obtain ⟨stream0, getZ, streamFrame, heapState, heapEq⟩ := observation.full.2
  have streamEq : stream0 = observation.streamZ := Option.some.inj (getZ.symm.trans observation.origin.good.live.hz)
  subst stream0
  have heapStateEq : heapState = observation.state := by
    have get : observation.heap.istates zs = some heapState := by rw [heapEq]; exact setI_istates_same ..
    exact Option.some.inj (get.symm.trans observation.origin.good.live.hs)
  subst heapState
  have frameRead : HeaderFrame s observation.state := by unfold HeaderFrame; rw [readFrame]
  have frameTables : HeaderFrame observation.state ready.tables.state := by unfold HeaderFrame; rw [ready.tables.frame]
  have frame := frameRead.trans frameTables
  have frameCredit : AdlerCredit observation.streamZ s credited := by rw [streamFrame]; exact credit
  have saved := retained_dictionary_header_put (streamZ := observation.streamZ) origin.good frame dictionary
  have finalHeap : setI observation.heap zs ready.tables.state = setI (r.put h observation.streamZ) zs ready.tables.state :=
    (congrArg (fun base => setI base zs ready.tables.state) heapEq).trans (setI_setI ..)
  have finalDictionary : InflateDictionary (setI observation.heap zs ready.tables.state) ready.tables.state history := by rw [finalHeap]; exact saved
  have readNormal : runX (clRead c) l h = .ok ((.ok (), observation.regs), observation.heap) := by simpa only [normal] using observation.read
  have source : runX (inflate_CODELENS c) l h = runX (clTail c) observation.regs observation.heap := by rw [inflate_CODELENS_eq, runX_bind, readNormal]
  refine ⟨⟨prefixData, observation, normal, code, ready, ?_, ?_, ?_, frame.credit frameCredit, finalDictionary, ?_, ?_,
    accepted_header_from_source_prefix prefixData observation normal code ready, main,
    (inflate_dispatch_CODELENS E l mode).trans (source.trans ready.actual)⟩⟩
  · rw [streamFrame]; exact allocator
  · rw [streamFrame]
  · rw [streamFrame]
  · have first := congrArg InflateState.last ready.tables.frame
    have second := congrArg InflateState.last readFrame
    exact first.trans second
  · have := observation.bits
    omega

#print axioms retained_dictionary_header_put
#print axioms accepted_packet_from_observations
end Zlib.Inflate.Proofs.ActualHeader
