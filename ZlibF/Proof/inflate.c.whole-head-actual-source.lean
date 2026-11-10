import ZlibF.Proof.«inflate.c.whole-wrapper-header-bytes»
import ZlibF.Proof.«inflate.c.whole-dictid-wire-phase»
namespace Zlib.Inflate.Proofs.WholeWrapper
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WholeEpoch Zlib.Inflate.Proofs.WrapperGlue
set_option autoImplicit false
set_option maxHeartbeats 2200000

def headRegs (regs : IL) : IL := {headWindowRegs regs with hold := 0, bits := 0}
def headHeap (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream) (s : InflateState) (regs : IL) : Heap :=
  setI (r.put h {z with adler := 1}) zs (headDefaultState s regs)

theorem head_read_source_cut
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l regs : IL}
    (E : Env c h r zs z s) (wrap : s.wrap = 5) (header : s.head = none)
    (pull : runX (NEEDBITS 16) l h = .ok ((.ok (), regs), h)) :
    runX (inflate_HEAD c) l h = runX (headDefaultCheck c s regs) regs h := by
  unfold inflate_HEAD
  rw [runX_bind, runX_rdS E]
  simp only [wrap, show ((5 : Int32) == 0) = false from rfl, Bool.false_eq_true, ite_false]
  rw [runX_bind, pull]
  simp only []
  rw [runX_bind, runX_get]
  simp only []
  rw [runX_bind, runX_ldS E]
  simp only [wrap, show (((5 : Int32) &&& 2) != 0) = false from rfl, Bool.false_and,
    Bool.false_eq_true, ite_false, header, bne_self_eq_false]
  unfold headDefaultCheck
  simp only [wrap]

/-- All accepted two-byte zlib headers produce their true TYPE/DICTID
phase and initial output Adler. Prior partial reads are represented by
actual cumulative credited bytes, with no chosen header witness. -/
structure HeadReady (c : Ctx) (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream) (s : InflateState)
    (l : IL) (bs : List UInt8) (log : DataLog) (cmf flg : UInt8)
    (event : ByteWordRead h l bs log.input [] 16) where
  normal : event.outcome = .ok ()
  word : event.regs.hold.toNat = cmf.toNat + 256 * flg.toNat
  bytes : log.input ++ bs.take event.used = [cmf, flg]
  valid : Zlib.HeaderOK cmf flg
  actual : runX (inflate_dispatch c) l h = .ok ((.ok (), headRegs event.regs), headHeap h r zs z s event.regs)
  origin : DefaultOriginState (headHeap h r zs z s event.regs) r zs {z with adler := 1} (headDefaultState s event.regs)
  allocator : DefAlloc {z with adler := 1}
  origins : WrapperOrigins (headDefaultState s event.regs)
  buffers : DispatchBuffers (headHeap h r zs z s event.regs) r (headRegs event.regs) (bs.drop event.used)
  phase : SourcePhase (sourceLog (readLog log bs event.used))
    (leaveState (headDefaultState s event.regs) (headRegs event.regs)) (bytesBits [cmf, flg])
  credited : CausalInput.Credited (readLog log bs event.used).input (bytesBits [cmf, flg]) 0 0
  adler : AdlerCredit {z with adler := 1} (headDefaultState s event.regs) []
  views : ByteViewSizes h (headHeap h r zs z s event.regs)

 theorem head_ready_source
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {log : DataLog} {cmf flg : UInt8}
    (E : Env c h r zs z s) (before : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (origins : WrapperOrigins s) (buffers : DispatchBuffers h r l bs) (mode : s.mode = HEAD)
    (incoming : l.bits.toNat ≤ 39) (empty : log.output = []) (dictionary : log.dictionary = [])
    (event : ByteWordRead h l bs log.input [] 16) (normal : event.outcome = .ok ())
    (bytes : log.input ++ bs.take event.used = [cmf, flg])
    (word : event.regs.hold.toNat = cmf.toNat + 256 * flg.toNat) (valid : Zlib.HeaderOK cmf flg) :
    Nonempty (HeadReady c h r zs z s l bs log cmf flg event) := by
  obtain ⟨header, method, window, defaultMode⟩ := valid_header_guards valid origins.wrapped word
  have actual := (inflate_dispatch_HEAD E l mode).trans
    ((head_read_source_cut E origins.wrapped before.header (by simpa only [normal] using event.actual)).trans
      (headDefaultCheck_accept E event.regs header method window before.window))
  obtain ⟨exit, regs0, after0, stream0, state0, used0, _made, _bound0, run0, current, packet,
    _sizes, _next, count0, _put, _left, _bits, _rank⟩ :=
    inflate_dispatch_default_origin_state_rank E before buffers incoming
  rw [actual] at run0
  cases run0
  have count : event.regs.have_.toNat + event.used = l.have_.toNat := by
    rw [event.inv.have_eq, buffers.bits.have_eq, List.length_drop]
    have := event.bound
    omega
  change event.regs.have_.toNat + used0 = l.have_.toNat at count0
  have sameUsed : used0 = event.used := by omega
  subst used0
  have expectedZ : r.get (headHeap h r zs z s event.regs) = some {z with adler := 1} := by
    rw [headHeap, ZStreamRef.get_setI]
    exact ZStreamRef.get_put_same E.hz _
  have sameStream : stream0 = {z with adler := 1} := Option.some.inj (current.good.live.hz.symm.trans expectedZ)
  subst stream0
  have sameState : state0 = headDefaultState s event.regs := Option.some.inj (current.good.live.hs.symm.trans (setI_istates_same ..))
  subst state0
  have width : event.regs.bits.toNat = 16 := event.normal normal
  have credited : CausalInput.Credited (readLog log bs event.used).input (bytesBits [cmf, flg]) 0 0 := by
    simp only [CausalInput.Credited, readLog, bytes, UInt32.toNat_zero, natBits, List.append_nil]
  let w : Wrapper (sourceLog (readLog log bs event.used)).dictionary := ⟨cmf, flg, valid, fun _ => dictionary⟩
  have phase : Nonempty (SourcePhase (sourceLog (readLog log bs event.used))
      (leaveState (headDefaultState s event.regs) (headRegs event.regs)) (bytesBits [cmf, flg])) := by
    by_cases flag : flg.toNat / 32 % 2 = 1
    · refine ⟨SourcePhase.dictid (log := sourceLog (readLog log bs event.used)) cmf flg ?_ valid flag rfl empty dictionary ?_⟩
      · change headDefaultMode event.regs = DICTID
        rw [defaultMode, ite_eq_left flag]
      · change (0 : UInt32).toNat < 32
        decide
    · refine ⟨SourcePhase.tag (log := sourceLog (readLog log bs event.used)) w [] ?_ ?_ ?_ ?_⟩
      · left
        change headDefaultMode event.regs = TYPE
        rw [defaultMode, ite_eq_right flag]
      · exact origins.last (Or.inl mode)
      · simpa only [sourceLog, readLog, empty] using BlocksPrefix.initial w.dictionary
      · simp only [Wrapper.bytes, w, flag, ite_false, List.append_nil]
  obtain ⟨phase⟩ := phase
  refine ⟨⟨normal, word, bytes, valid, actual, current, allocator, ?_, packet, phase, credited, ?_, ?_⟩⟩
  · exact ⟨origins.wrapped, fun _ => origins.missing (Or.inl mode), fun _ => origins.last (Or.inl mode)⟩
  · exact (head_accept_adler_base E event.regs origins.wrapped header method window before.window).2
  · intro ref
    rw [headHeap, byte_view_get_setI, byte_view_get_stream_put]

#print axioms head_read_source_cut
#print axioms head_ready_source
end Zlib.Inflate.Proofs.WholeWrapper
