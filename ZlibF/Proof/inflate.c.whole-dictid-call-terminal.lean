import ZlibF.Proof.«inflate.c.whole-wrapper-terminal»
namespace Zlib.Inflate.Proofs.WholeWrapper
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WholeEpoch
set_option autoImplicit false
set_option maxHeartbeats 2200000

/-- A completed actual dictionary identifier yields the real direct
return of the original mainwhile, with the same cumulative wire/cursors.
The already-returned DICT computation is never restarted as a live loop. -/
theorem dictid_ready_call_terminal
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8} {cmf flg : UInt8}
    (before : FramedCallCut c entryHeap h r zs entryZ z s l base raw) (mode : s.mode = DICTID)
    (event : ByteWordRead h l (raw.drop before.cut.used)
      (sourceLog (callLog base raw before.cut.used before.cut.emitted)).input (bytesBits [cmf, flg]) 32)
    (ready : DictIdReady c h r zs z s l (raw.drop before.cut.used)
      (sourceLog (callLog base raw before.cut.used before.cut.emitted)) cmf flg event) :
    Nonempty (WrapperTerminal c entryHeap (dictHeap h r zs z s ready.identifier event.regs) r zs entryZ
      (dictStream z ready.identifier event.regs) (dictState s ready.identifier event.regs)
      (dictRegs event.regs) base raw (Ex.ret Z_NEED_DICT)) := by
  have bound : before.cut.used + event.used ≤ raw.length := by
    have more := event.bound; rw [List.length_drop] at more; have old := before.cut.usedBound; omega
  have packet : DispatchBuffers (dictHeap h r zs z s ready.identifier event.regs) r (dictRegs event.regs)
      (raw.drop (before.cut.used + event.used)) := by simpa only [List.drop_drop, Nat.add_comm] using ready.buffers
  have actual := (inflate_dispatch_DICTID before.cut.env l mode).trans ready.actual
  have main := before.cut.main.trans
    (wrapper_loop_terminal before.cut.env before.cut.origin before.cut.buffers before.cut.bits actual)
  have count : (dictRegs event.regs).have_.toNat + event.used = l.have_.toNat := by
    change event.regs.have_.toNat + event.used = l.have_.toNat
    rw [event.inv.have_eq, before.cut.buffers.bits.have_eq, List.length_drop]
    have := event.bound
    omega
  have put : (dictRegs event.regs).put = l.put := by change event.regs.put = l.put; rw [event.shape]
  have left : (dictRegs event.regs).left = l.left := by change event.regs.left = l.left; rw [event.shape]
  have out : (dictRegs event.regs).out_ = l.out_ := by change event.regs.out_ = l.out_; rw [event.shape]
  have fresh : (dictRegs event.regs).out_ = (dictRegs event.regs).left := by
    rw [out, left]
    exact before.registers.noHeaderOutput (Or.inr (Or.inl mode))
  let phase := ready.phase.reindex (read_log_join base raw before.cut.used event.used before.cut.emitted).symm
  have dictionary := before.cut.window (by rw [mode]; decide)
  have saved : InflateDictionary (dictHeap h r zs z s ready.identifier event.regs) (dictState s ready.identifier event.regs)
      ((base.dictionary ++ base.output).drop ((base.dictionary ++ base.output).length - 2 ^ s.wbits.toNat)) :=
    WindowHistory.dictionary_transport dictionary rfl rfl rfl rfl
      (fun ref => by rw [dictHeap, byte_view_get_setI, byte_view_get_stream_put])
  have env : Env c (dictHeap h r zs z s ready.identifier event.regs) r zs
      (dictStream z ready.identifier event.regs) (dictState s ready.identifier event.regs) :=
    ⟨before.cut.env.strm, before.cut.env.st, ready.origin.good.live.hz, ready.origin.good.live.hs⟩
  refine ⟨⟨before.cut.used + event.used, bound, before.cut.emitted,
    bytesBits ([cmf, flg] ++ be32 ready.identifier.toNat), env, ready.origin, ready.allocator, ready.origins,
    main, packet, by change 0 ≤ 39; decide, ?_, ?_, ?_, ?_, ?_, phase,
    low_materialized phase (by change DICT ≤ TYPE; decide), fun _ => saved, ?_, ?_, ?_⟩⟩
  · change event.regs.next = inputAdvance entryZ.next_in (before.cut.used + event.used)
    rw [event.cursor, before.cut.next, inputAdvance_add]
  · have old := before.cut.haveCount
    omega
  · rw [put]; exact before.cut.put
  · rw [left]; exact before.cut.leftCount
  · simpa only [dictRegs, readLog, sourceLog, callLog, List.take_add, List.append_assoc] using ready.credited
  · intro dest off array pointer get
    apply before.cut.physical dest off array (by rw [← put]; exact pointer)
    rw [dictHeap, byte_view_get_setI, byte_view_get_stream_put] at get
    exact get
  · intro lower _upper
    change TYPE ≤ DICT at lower
    exact False.elim ((by decide : ¬ TYPE ≤ DICT) lower)
  · refine ⟨?_, fun _ => fresh⟩
    change event.regs.in_ = entryZ.avail_in
    rw [event.shape]
    exact before.registers.inputStart

#print axioms dictid_ready_call_terminal
end Zlib.Inflate.Proofs.WholeWrapper
