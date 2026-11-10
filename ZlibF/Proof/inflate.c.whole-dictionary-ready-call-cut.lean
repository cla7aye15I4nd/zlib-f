import ZlibF.Proof.«inflate.c.whole-wrapper-inline-loop»
namespace Zlib.Inflate.Proofs.WholeWrapper
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WholeEpoch Zlib.Inflate.Proofs.FunctionalTrailer Zlib.Inflate.Proofs.WrapperGlue
set_option autoImplicit false
set_option maxHeartbeats 2200000

def readyDictHeap (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream) (s : InflateState) : Heap :=
  setI (r.put h {z with adler := 1}) zs {s with check := 1, mode := TYPE}

/-- Actual installed-DICT reset continues through TYPE in the identical
fuelled loop. No public pause or restarted direct return is introduced. -/
theorem dictionary_ready_call_cut
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : FramedCallCut c entryHeap h r zs entryZ z s l base raw) (mode : s.mode = DICT)
    (present : s.havedict ≠ 0) :
    Nonempty (FramedCallCut c entryHeap (readyDictHeap h r zs z s) r zs entryZ
      {z with adler := 1} {s with check := 1, mode := TYPE} l base raw) := by
  obtain ⟨w, identifier, flag, wire, output, _bits, _check, installed⟩ := dictionary_phase_fields before.cut.phase mode
  have identifierEq := installed present
  change base.output ++ before.cut.emitted = [] at output
  have emptyBase : base.output = [] := (List.append_eq_nil_iff.mp output).1
  have emptyMade : before.cut.emitted = [] := (List.append_eq_nil_iff.mp output).2
  have flags : s.flags = 0 := by
    rcases before.cut.origin.dictionary_format (Or.inr mode) with raw | flags
    · rw [before.cut.wrapperOrigins.wrapped] at raw; cases raw
    · exact flags
  have stateJ := before.cut.origin.toDefaultStateJ.prepare_dictionary (Or.inr mode) 1 TYPE (Or.inr rfl)
  have current : DefaultOriginState (readyDictHeap h r zs z s) r zs {z with adler := 1} {s with check := 1, mode := TYPE} :=
    before.cut.origin.of_fields stateJ rfl rfl rfl
  have env : Env c (readyDictHeap h r zs z s) r zs {z with adler := 1} {s with check := 1, mode := TYPE} :=
    ⟨before.cut.env.strm, before.cut.env.st, current.good.live.hz, current.good.live.hs⟩
  have packet : DispatchBuffers (readyDictHeap h r zs z s) r l (raw.drop before.cut.used) :=
    before.cut.buffers.byte_views before.cut.origin.good current.good rfl
      (fun ref => by rw [readyDictHeap, byte_view_get_setI, byte_view_get_stream_put])
      (fun ref => by rw [readyDictHeap, byte_view_ro_setI, byte_view_ro_stream_put])
  have source := dictionary_ready_adler_base before.cut.env l before.cut.wrapperOrigins.wrapped flags present
  have newDispatch : runX (inflate_dispatch c) l (readyDictHeap h r zs z s) =
      runX (inflate_TYPE c) l (readyDictHeap h r zs z s) := by
    rw [inflate_dispatch_block_type env l (Or.inl rfl), ite_eq_left rfl]
  have same : runX (inflate_dispatch c) l h = runX (inflate_dispatch c) l (readyDictHeap h r zs z s) :=
    (inflate_dispatch_DICT before.cut.env l mode).trans (source.1.trans newDispatch.symm)
  have main := before.cut.main.trans (wrapper_loop_first_eq same)
  have phase : SourcePhase (sourceLog (callLog base raw before.cut.used before.cut.emitted))
      (leaveState {s with check := 1, mode := TYPE} l) before.cut.word := by
    refine .tag w [] (Or.inl rfl) (before.cut.wrapperOrigins.last (Or.inr (Or.inr mode))) ?_ ?_
    · simpa only [sourceLog, callLog, emptyBase, emptyMade, List.append_nil] using BlocksPrefix.initial w.dictionary
    · rw [wire, identifierEq]
      simp only [Wrapper.bytes, flag, ite_true, List.append_nil]
  have window := before.cut.window (by rw [mode]; decide)
  have saved : InflateDictionary (readyDictHeap h r zs z s) {s with check := 1, mode := TYPE}
      ((base.dictionary ++ base.output).drop ((base.dictionary ++ base.output).length - 2 ^ s.wbits.toNat)) :=
    WindowHistory.dictionary_transport window rfl rfl rfl rfl
      (fun ref => by rw [readyDictHeap, byte_view_get_setI, byte_view_get_stream_put])
  have fresh := before.registers.noHeaderOutput (Or.inr (Or.inr mode))
  refine ⟨⟨⟨before.cut.used, before.cut.usedBound, before.cut.emitted, before.cut.word, env, current,
    before.cut.allocator, ?_, main, packet, before.cut.bits, before.cut.next, before.cut.haveCount,
    before.cut.put, before.cut.leftCount, before.cut.credited, phase,
    low_materialized phase (by change TYPE ≤ TYPE; decide), fun _ => saved, ?_, ?_⟩,
    ⟨before.registers.inputStart, fun _ => fresh⟩⟩⟩
  · refine ⟨before.cut.wrapperOrigins.wrapped, ?_, ?_⟩
    · intro selected
      rcases selected with bad | bad <;> cases bad
    · intro _
      exact before.cut.wrapperOrigins.last (Or.inr (Or.inr mode))
  · intro dest off array ptr get
    apply before.cut.physical dest off array ptr
    rw [readyDictHeap, byte_view_get_setI, byte_view_get_stream_put] at get
    exact get
  · intro _lower _upper
    refine ⟨0, ?_⟩
    rw [emptyBase, emptyMade]
    exact OutputCredit.start current.good packet fresh source.2

#print axioms dictionary_ready_call_cut
end Zlib.Inflate.Proofs.WholeWrapper
