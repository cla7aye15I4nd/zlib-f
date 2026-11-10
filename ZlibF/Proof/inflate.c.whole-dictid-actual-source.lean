import ZlibF.Proof.«inflate.c.whole-dictid-wire-phase»
namespace Zlib.Inflate.Proofs.WholeWrapper
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WholeEpoch
set_option autoImplicit false
set_option maxHeartbeats 2000000

def dictRegs (regs : IL) : IL := {regs with hold := 0, bits := 0}
def dictState (s : InflateState) (id : UInt32) (regs : IL) : InflateState :=
  leaveState {s with check := id.toUInt64, mode := DICT} (dictRegs regs)
def dictStream (z : ZStream) (id : UInt32) (regs : IL) : ZStream :=
  dictWaitStream {z with adler := id.toUInt64} (dictRegs regs)
def dictHeap (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream) (s : InflateState) (id : UInt32) (regs : IL) : Heap :=
  setI (r.put h (dictStream z id regs)) zs (dictState s id regs)

/-- Real DICTID completion and direct NEED_DICT return on one heap.
The wire identifier and saved state.check are produced together. -/
structure DictIdReady (c : Ctx) (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream) (s : InflateState)
    (l : IL) (bs : List UInt8) (log : DataLog) (cmf flg : UInt8)
    (event : ByteWordRead h l bs log.input (bytesBits [cmf, flg]) 32) where
  identifier : UInt32
  swap : ZSWAP32 event.regs.hold = identifier.toUInt64
  word : natBits event.regs.bits.toNat event.regs.hold.toNat = bytesBits (be32 identifier.toNat)
  actual : runX (inflate_DICTID c) l h = .ok ((.error (Ex.ret Z_NEED_DICT), dictRegs event.regs),
    dictHeap h r zs z s identifier event.regs)
  origin : DefaultOriginState (dictHeap h r zs z s identifier event.regs) r zs
    (dictStream z identifier event.regs) (dictState s identifier event.regs)
  allocator : DefAlloc (dictStream z identifier event.regs)
  origins : WrapperOrigins (dictState s identifier event.regs)
  buffers : DispatchBuffers (dictHeap h r zs z s identifier event.regs) r (dictRegs event.regs) (bs.drop event.used)
  phase : SourcePhase (sourceLog (readLog log bs event.used)) (dictState s identifier event.regs)
    (bytesBits ([cmf, flg] ++ be32 identifier.toNat))
  credited : CausalInput.Credited (readLog log bs event.used).input
    (bytesBits ([cmf, flg] ++ be32 identifier.toNat)) 0 0
  views : ByteViewSizes h (dictHeap h r zs z s identifier event.regs)

/-- Derive every completed word fact from the real pull and the closed
DICT execution. No successful call or returned invariant is an input. -/
theorem dictid_ready_source
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {log : DataLog} {cmf flg : UInt8}
    (E : Env c h r zs z s) (before : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (origins : WrapperOrigins s) (buffers : DispatchBuffers h r l bs) (mode : s.mode = DICTID)
    (valid : Zlib.HeaderOK cmf flg) (flag : flg.toNat / 32 % 2 = 1) (empty : log.output = [])
    (event : ByteWordRead h l bs log.input (bytesBits [cmf, flg]) 32) (normal : event.outcome = .ok ()) :
    Nonempty (DictIdReady c h r zs z s l bs log cmf flg event) := by
  have missing : s.havedict = 0 := origins.missing (Or.inr mode)
  obtain ⟨identifier, swap, word, credited, phase⟩ := dictid_complete_phase valid flag empty missing event normal
  obtain ⟨phase⟩ := phase
  let ready := {s with check := identifier.toUInt64, mode := DICT}
  let stream := {z with adler := identifier.toUInt64}
  let heap := setI (r.put h stream) zs ready
  let regs := dictRegs event.regs
  have current : DefaultStateJ heap r zs stream ready := before.toDefaultStateJ.prepare_dictionary (Or.inl mode) _ _ (Or.inl rfl)
  have origin : DefaultOriginState heap r zs stream ready := before.of_fields current rfl rfl rfl
  have env : Env c heap r zs stream ready := ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
  have packet0 : DispatchBuffers h r event.regs (bs.drop event.used) :=
    buffers.consume before.good before.good rfl (fun _ => rfl) (fun _ => rfl) (by rw [event.shape]; rfl) event.cursor event.bound event.inv
  have packet : DispatchBuffers heap r regs (bs.drop event.used) :=
    (packet0.byte_views before.good current.good rfl
      (fun _ => by rw [byte_view_get_setI, byte_view_get_stream_put])
      (fun _ => by rw [byte_view_ro_setI, byte_view_ro_stream_put])).clear_bits
  obtain ⟨actualDict, good, tables, pending, finalPacket, sizes, static, held, _totalOut, _total⟩ :=
    inflate_DICT_wait_boundary env current.good current.pending packet rfl missing (by change 0 ≤ 39; decide)
  have finalJ := current.dictionary_update (Or.inr rfl) good tables pending (by rfl) (Or.inl rfl) held sizes static
  have finalOrigin := origin.of_fields finalJ rfl rfl rfl
  have cut := inflate_DICTID_parsed_cut E l event.regs (by simpa only [normal] using event.actual)
  rw [swap] at cut
  have actual := cut.trans actualDict
  have heapEq : setI (r.put heap (dictWaitStream stream regs)) zs (leaveState ready regs) =
      dictHeap h r zs z s identifier event.regs := by
    simp only [heap, dictHeap, dictStream, dictState, ZStreamRef.put_setI, ZStreamRef.put_put, setI_setI]
    rfl
  rw [heapEq] at actual finalOrigin finalPacket sizes
  refine ⟨⟨identifier, swap, word, actual, finalOrigin, ?_, ?_, finalPacket, phase, credited, ?_⟩⟩
  · exact allocator
  · refine ⟨origins.wrapped, ?_, ?_⟩
    · intro selected; rcases selected with impossible | impossible <;> cases impossible
    · intro _; exact origins.last (Or.inr (Or.inl mode))
  · exact (by intro ref; rw [byte_view_get_setI, byte_view_get_stream_put] : ByteViewSizes h heap).trans sizes

#print axioms dictid_ready_source
end Zlib.Inflate.Proofs.WholeWrapper
