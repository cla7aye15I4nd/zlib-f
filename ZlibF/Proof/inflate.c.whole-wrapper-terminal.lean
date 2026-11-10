import ZlibF.Proof.«inflate.c.whole-head-call-cut»
import ZlibF.Proof.«inflate.c.whole-dictid-actual-source»
namespace Zlib.Inflate.Proofs.WholeWrapper
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WholeEpoch Zlib.Inflate.Proofs.FunctionalTrailer
set_option autoImplicit false
set_option maxHeartbeats 2200000

/-- Real wrapper exit packet. A direct return is not restarted as a live mainwhile. -/
structure WrapperTerminal (c : Ctx) (entryHeap h : Heap) (r : ZStreamRef) (zs : Nat)
    (entryZ z : ZStream) (s : InflateState) (l : IL) (base : DataLog) (raw : List UInt8) (exit : Ex) where
  used : Nat
  usedBound : used ≤ raw.length
  emitted : List UInt8
  word : List Bool
  env : Env c h r zs z s
  origin : DefaultOriginState h r zs z s
  allocator : DefAlloc z
  wrapperOrigins : WrapperOrigins s
  main : runX (inflate_run c) IL.init entryHeap =
    .ok ((.error exit, l), h)
  buffers : DispatchBuffers h r l (raw.drop used)
  bits : l.bits.toNat ≤ 39
  next : l.next = inputAdvance entryZ.next_in used
  haveCount : l.have_.toNat + used = entryZ.avail_in.toNat
  put : l.put = inputAdvance entryZ.next_out emitted.length
  leftCount : l.left.toNat + emitted.length = entryZ.avail_out.toNat
  credited : CausalInput.Credited (base.input ++ raw.take used) word l.bits l.hold
  phase : SourcePhase (sourceLog (callLog base raw used emitted)) (leaveState s l) word
  tables : phase.Materialized h
  window : s.mode < CHECK → InflateDictionary h s
    ((base.dictionary ++ base.output).drop
      ((base.dictionary ++ base.output).length - 2 ^ s.wbits.toNat))
  physical : ∀ (dest : BRef) (off : Nat) (array : Array UInt8),
    l.put = .ref dest off → Space.get h dest = some array →
      ZlibF.Math.LZ77Copy.writtenBytes array off emitted.length = emitted
  checksum : TYPE ≤ s.mode → s.mode ≤ DONE →
    ∃ count, OutputCredit h z s l base.output emitted count

  registers : WrapperRegOrigins entryZ s l

/-- Match the closed real mainwhile with a genuine immediate switch exit. -/
theorem wrapper_loop_terminal
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l regs : IL} {bs : List UInt8} {exit : Ex}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39)
    (actual : runX (inflate_dispatch c) l h = .ok ((.error exit, regs), after)) :
    runX (xwhile (pure true) (inflate_dispatch c)) l h = .ok ((.error exit, regs), after) := by
  obtain ⟨exit0, regs0, after0, _z, _s, _used, _made, _bound, whole, _current,
    _packet, _bits, _sizes, _next, _count, _put, _left, trace⟩ := HeaderSourceTrace.loop_actual_trace E origin buffers bits
  have terminal : HeaderSourceTrace.DispatchExit c l h exit regs after := ⟨l, h, .begin, actual⟩
  obtain ⟨rfl, rfl, rfl⟩ := HeaderSourceTrace.DispatchExit.unique trace terminal
  exact whole

/-- Exhausted HEAD/DICTID pulls preserve all current call observations
and expose the real leave terminal, with no artificial public pause. -/
theorem wrapper_wait_terminal
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8} {width : UInt32}
    (before : FramedCallCut c entryHeap h r zs entryZ z s l base raw)
    (modes : s.mode = HEAD ∨ s.mode = DICTID)
    (event : ByteWordRead h l (raw.drop before.cut.used)
      (sourceLog (callLog base raw before.cut.used before.cut.emitted)).input before.cut.word width)
    (waiting : event.outcome = .error Ex.leave) (widthBound : width.toNat ≤ 40)
    (actual : runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, event.regs), h))
    (phase : SourcePhase (sourceLog (readLog (sourceLog (callLog base raw before.cut.used before.cut.emitted))
      (raw.drop before.cut.used) event.used)) (leaveState s event.regs) before.cut.word) :
    Nonempty (WrapperTerminal c entryHeap h r zs entryZ z s event.regs base raw Ex.leave) := by
  have bound : before.cut.used + event.used ≤ raw.length := by
    have more := event.bound; rw [List.length_drop] at more; have old := before.cut.usedBound; omega
  have packet := before.cut.buffers.consume before.cut.origin.good before.cut.origin.good rfl
    (fun _ => rfl) (fun _ => rfl) (by rw [event.shape]; rfl) event.cursor event.bound event.inv
  have packet0 : DispatchBuffers h r event.regs (raw.drop (before.cut.used + event.used)) := by
    simpa only [List.drop_drop, Nat.add_comm] using packet
  have low : (leaveState s event.regs).mode ≤ TYPE := by rcases modes with mode | mode <;> rw [show (leaveState s event.regs).mode = s.mode from rfl, mode] <;> decide
  let nextPhase := phase.reindex (read_log_join base raw before.cut.used event.used before.cut.emitted).symm
  have count : event.regs.have_.toNat + event.used = l.have_.toNat := by
    rw [event.inv.have_eq, before.cut.buffers.bits.have_eq, List.length_drop]
    have := event.bound
    omega
  have bits : event.regs.bits.toNat ≤ 39 := by
    have upper := (event.wait waiting).2.2
    omega
  refine ⟨⟨before.cut.used + event.used, bound, before.cut.emitted, before.cut.word, before.cut.env,
    before.cut.origin, before.cut.allocator, before.cut.wrapperOrigins,
    before.cut.main.trans (wrapper_loop_terminal before.cut.env before.cut.origin before.cut.buffers before.cut.bits actual),
    packet0, bits, ?_, ?_, ?_, ?_, ?_, nextPhase, low_materialized nextPhase low,
    before.cut.window, ?_, ?_, ?_⟩⟩
  · rw [event.cursor, before.cut.next, inputAdvance_add]
  · have old := before.cut.haveCount; omega
  · rw [event.shape]; exact before.cut.put
  · rw [event.shape]; exact before.cut.leftCount
  · simpa only [readLog, sourceLog, callLog, List.take_add, List.append_assoc] using event.credited
  · intro dest off array pointer get
    have put : event.regs.put = l.put := by rw [event.shape]
    exact before.cut.physical dest off array (by rw [← put]; exact pointer) get
  · intro lower _upper
    rcases modes with head | id
    · rw [head] at lower; exact False.elim ((by decide : ¬ TYPE ≤ HEAD) lower)
    · rw [id] at lower; exact False.elim ((by decide : ¬ TYPE ≤ DICTID) lower)
  · refine ⟨?_, ?_⟩
    · rw [event.shape]; exact before.registers.inputStart
    · intro _selected
      have fresh := before.registers.noHeaderOutput (by rcases modes with m | m; exact Or.inl m; exact Or.inr (Or.inl m))
      rw [event.shape]
      exact fresh

#print axioms wrapper_loop_terminal
#print axioms wrapper_wait_terminal
end Zlib.Inflate.Proofs.WholeWrapper
