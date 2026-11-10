import ZlibF.Proof.«inflate.c.whole-epoch-dispatch-interface-v4»
import ZlibF.Proof.«inflate.c.whole-head-call-exhaustive»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FunctionalTrailer Zlib.Inflate.Proofs.WrapperGlue
open Zlib.Inflate.Proofs.WholeWrapper
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000

/-- Wrapper modes exclude the newly added internal STORED/MATCH/MEM
cases, so their exact previous source phase is available. -/
theorem SourcePhase4.legacy_of_wrapper
    {log : DataLog} {s : InflateState} {wire : List Bool}
    (phase : SourcePhase4 log s wire) (mode : s.mode = HEAD ∨ s.mode = DICTID ∨ s.mode = DICT) :
    ∃ previous : SourcePhase log s wire, phase = .legacy previous := by
  cases phase with
  | legacy previous => exact ⟨previous, rfl⟩
  | _ => rcases mode with mode | mode | mode <;> simp_all [STORED, MATCH, MEM, HEAD, DICTID, DICT]

/-- Reattach the source-produced scalar origins to an existing complete
legacy call cut. These are internal field equalities, not callee contracts. -/
def FramedCallCut.epoch4_of_origins
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (framed : FramedCallCut c entryHeap h r zs entryZ z s l base raw)
    (outputStart : l.out_ = entryZ.avail_out) (normalRet : l.ret = Z_OK)
    (oracle : h.allocOk = entryHeap.allocOk) (noCodes : s.mode ≠ CODELENS) :
    EpochCallCut4 c entryHeap h r zs entryZ z s l base raw :=
  (show EpochCallCut c entryHeap h r zs entryZ z s l base raw from
    ⟨framed, fun _ => outputStart, fun _ => normalRet, oracle⟩).upgrade
      (framed.cut.phase.reversible_of_not_codes noCodes)

/-- A literal return remains a literal return while its three causal
scalar origins and inactive parser-inverse attachment are transported. -/
def wrapper_exit4_of_origins
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8} {exit : Ex}
    (terminal : WrapperTerminal c entryHeap h r zs entryZ z s l base raw exit)
    (outputStart : l.out_ = entryZ.avail_out) (normalRet : l.ret = Z_OK)
    (oracle : h.allocOk = entryHeap.allocOk) (noCodes : s.mode ≠ CODELENS) :
    EpochCallExit4 c entryHeap h r zs entryZ z s l base raw exit :=
  (show EpochCallExit c entryHeap h r zs entryZ z s l base raw exit from
    ⟨terminal, fun _ => outputStart, fun _ => normalRet, oracle⟩).upgrade
      (terminal.phase.reversible_of_not_codes noCodes)

/-- Exhaustive actual default HEAD: short waits, invalid bytes to BAD,
and accepted headers to TYPE or DICTID all construct the real v4 result. -/
theorem EpochCallCut4.head_dispatch
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = HEAD) : Nonempty (DispatchResult4 before) := by
  obtain ⟨previous, phaseEq⟩ := before.phase.legacy_of_wrapper (Or.inl mode)
  have tables : previous.Materialized h := by
    have materialized := before.materialized
    rw [phaseEq] at materialized
    exact materialized.1
  let old := before.facts.with_legacy previous tables
  obtain ⟨event, waiting, normal⟩ := head_call_exhaustive old.framed mode
  have out0 := before.facts.outputStart (by rw [mode]; decide)
  have ret0 := before.facts.normalRet (by rw [mode]; decide)
  rcases event.kinds with completed | exhausted
  · obtain ⟨result⟩ := normal completed
    cases result with
    | accepted cmf flg bytes word valid framed =>
      obtain ⟨_source, empty, dictionary, _short⟩ := head_phase_fields old.framed.cut.phase mode
      obtain ⟨ready⟩ := head_ready_source old.framed.cut.env old.framed.cut.origin old.framed.cut.allocator
        old.framed.cut.wrapperOrigins old.framed.cut.buffers mode old.framed.cut.bits empty dictionary
        event completed bytes word valid
      have noCodes : (headDefaultState s event.regs).mode ≠ CODELENS := by
        change headDefaultMode event.regs ≠ CODELENS
        unfold headDefaultMode
        split <;> decide
      have next := framed.epoch4_of_origins
        (by change event.regs.out_ = _; rw [event.shape]; exact out0)
        (by change event.regs.ret = _; rw [event.shape]; exact ret0)
        (by simp only [headHeap, setI, ZStreamRef.put_allocOk]; exact before.facts.allocationOracle)
        noCodes
      exact ⟨.progress _ _ _ _ ready.actual next⟩
    | rejected source framed =>
      have next := framed.epoch4_of_origins
        (by rw [source.frame, event.shape]; exact out0)
        (by rw [source.frame, event.shape]; exact ret0)
        (by simp only [badHeap, setI, ZStreamRef.put_allocOk]; exact before.facts.allocationOracle)
        (by change BAD ≠ CODELENS; decide)
      exact ⟨.progress _ _ _ _ source.actual next⟩
  · obtain ⟨terminal⟩ := waiting exhausted
    have actual := (inflate_dispatch_HEAD old.framed.cut.env l mode).trans
      (head_wait_source_cut old.framed.cut.env old.framed.cut.wrapperOrigins.wrapped
        (by simpa only [exhausted] using event.actual))
    have next := wrapper_exit4_of_origins terminal
      (by rw [event.shape]; exact out0) (by rw [event.shape]; exact ret0)
      before.facts.allocationOracle (by rw [mode]; decide)
    exact ⟨.stopped _ _ _ _ Ex.leave actual next⟩

#print axioms SourcePhase4.legacy_of_wrapper
#print axioms EpochCallCut4.head_dispatch
/-- Every cumulative actual DICTID word either waits or directly returns
NEED_DICT with its computed identifier. No direct return is restarted as
a live dispatch loop, and no desired identifier is assumed. -/
theorem EpochCallCut4.dictid_dispatch
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = DICTID) : Nonempty (DispatchResult4 before) := by
  obtain ⟨previous, phaseEq⟩ := before.phase.legacy_of_wrapper (Or.inr (Or.inl mode))
  have tables : previous.Materialized h := by
    have materialized := before.materialized
    rw [phaseEq] at materialized
    exact materialized.1
  let old := before.facts.with_legacy previous tables
  obtain ⟨cmf, flg, valid, flag, word, empty, dictionary, short⟩ := dictid_phase_fields old.framed.cut.phase mode
  have credit := old.framed.cut.credited
  rw [word] at credit
  obtain ⟨event⟩ := byte_word_read (width := 32) old.framed.cut.buffers.bits credit
    (by rw [bytesBits_length]; simp) (by decide) (by decide) short
  have out0 := before.facts.outputStart (by rw [mode]; decide)
  have ret0 := before.facts.normalRet (by rw [mode]; decide)
  rcases event.kinds with completed | exhausted
  · obtain ⟨ready⟩ := dictid_ready_source old.framed.cut.env old.framed.cut.origin old.framed.cut.allocator
      old.framed.cut.wrapperOrigins old.framed.cut.buffers mode valid flag empty event completed
    obtain ⟨terminal⟩ := dictid_ready_call_terminal old.framed mode event ready
    have actual := (inflate_dispatch_DICTID old.framed.cut.env l mode).trans ready.actual
    have next := wrapper_exit4_of_origins terminal
      (by change event.regs.out_ = _; rw [event.shape]; exact out0)
      (by change event.regs.ret = _; rw [event.shape]; exact ret0)
      (by simp only [dictHeap, setI, ZStreamRef.put_allocOk]; exact before.facts.allocationOracle)
      (by change DICT ≠ CODELENS; decide)
    exact ⟨.stopped _ _ _ _ (Ex.ret Z_NEED_DICT) actual next⟩
  · have actual := (inflate_dispatch_DICTID old.framed.cut.env l mode).trans
      (inflate_DICTID_wait (c := c) (by simpa only [exhausted] using event.actual))
    obtain ⟨phase⟩ := dictid_wait_phase mode valid flag empty dictionary event exhausted
    let reworded := event.reword word
    have phase0 : SourcePhase (sourceLog (readLog (sourceLog (callLog base raw old.framed.cut.used old.framed.cut.emitted))
        (raw.drop old.framed.cut.used) event.used)) (leaveState s reworded.regs) old.framed.cut.word := by
      change SourcePhase (sourceLog (readLog (sourceLog (callLog base raw old.framed.cut.used old.framed.cut.emitted))
        (raw.drop old.framed.cut.used) event.used)) (leaveState s event.regs) old.framed.cut.word
      rw [word]
      exact phase
    obtain ⟨terminal⟩ := wrapper_wait_terminal old.framed (Or.inr mode) reworded exhausted (by decide) actual phase0
    have next := wrapper_exit4_of_origins terminal
      (by change event.regs.out_ = _; rw [event.shape]; exact out0)
      (by change event.regs.ret = _; rw [event.shape]; exact ret0)
      before.facts.allocationOracle (by rw [mode]; decide)
    exact ⟨.stopped _ _ _ _ Ex.leave actual next⟩

#print axioms EpochCallCut4.dictid_dispatch

/-- A missing installed dictionary causes the literal direct NEED_DICT
return. RESTORE and public total_in writes are part of this same actual
trip; no restarted loop or public pause is fabricated. -/
theorem EpochCallCut4.dictionary_missing
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = DICT) (missing : s.havedict = 0) : Nonempty (DispatchResult4 before) := by
  obtain ⟨previous, phaseEq⟩ := before.phase.legacy_of_wrapper (Or.inr (Or.inr mode))
  have tables : previous.Materialized h := by
    have materialized := before.materialized
    rw [phaseEq] at materialized
    exact materialized.1
  let old := before.facts.with_legacy previous tables
  let cut := old.framed.cut
  let stream := dictWaitStream z l
  let state := leaveState s l
  let after := setI (r.put h stream) zs state
  have actual : runX (inflate_dispatch c) l h = .ok ((.error (Ex.ret Z_NEED_DICT), l), after) :=
    (inflate_dispatch_DICT cut.env l mode).trans (inflate_DICT_wait_run cut.env l missing)
  have getZ : r.get after = some stream := by rw [ZStreamRef.get_setI]; exact ZStreamRef.get_put_same cut.env.hz _
  have getS : after.istates zs = some state := by dsimp only [after]; rw [setI_istates_same]
  obtain ⟨origin, packet⟩ := FunctionalTrailerSplits.origin_packet_of_actual cut.env cut.origin cut.buffers cut.bits actual getZ getS
  have packet0 : DispatchBuffers after r l (raw.drop cut.used) := by
    simpa only [Nat.sub_self, List.drop_zero] using packet
  have env : Env c after r zs stream state := ⟨cut.env.strm, cut.env.st, getZ, getS⟩
  have saved : InflateDictionary after state
      ((base.dictionary ++ base.output).drop ((base.dictionary ++ base.output).length - 2 ^ s.wbits.toNat)) :=
    WindowHistory.dictionary_transport (cut.window (by rw [mode]; decide)) rfl rfl rfl rfl
      (fun ref => by rw [byte_view_get_setI, byte_view_get_stream_put])
  let phase : SourcePhase (sourceLog (callLog base raw cut.used cut.emitted)) (leaveState state l) cut.word := cut.phase
  let terminal : WrapperTerminal c entryHeap after r zs entryZ stream state l base raw (Ex.ret Z_NEED_DICT) := {
    used := cut.used
    usedBound := cut.usedBound
    emitted := cut.emitted
    word := cut.word
    env := env
    origin := origin
    allocator := cut.allocator
    wrapperOrigins := cut.wrapperOrigins.locals l
    main := before.facts.exit_main actual
    buffers := packet0
    bits := cut.bits
    next := cut.next
    haveCount := cut.haveCount
    put := cut.put
    leftCount := cut.leftCount
    credited := cut.credited
    phase := phase
    tables := low_materialized phase (by change s.mode ≤ TYPE; rw [mode]; decide)
    window := fun _ => saved
    physical := by
      intro dest off array pointer get
      apply cut.physical dest off array pointer
      rw [byte_view_get_setI, byte_view_get_stream_put] at get
      exact get
    checksum := by
      intro lower _upper
      change TYPE ≤ s.mode at lower
      rw [mode] at lower
      exact False.elim ((by decide : ¬ TYPE ≤ DICT) lower)
    registers := ⟨old.framed.registers.inputStart, fun selected => old.framed.registers.noHeaderOutput selected⟩
  }
  have next := wrapper_exit4_of_origins terminal
    (before.facts.outputStart (by rw [mode]; decide))
    (before.facts.normalRet (by rw [mode]; decide))
    (by simp only [after, setI, ZStreamRef.put_allocOk]; exact before.facts.allocationOracle)
    (by change s.mode ≠ CODELENS; rw [mode]; decide)
  exact ⟨.stopped after stream state l (Ex.ret Z_NEED_DICT) actual next⟩

#print axioms EpochCallCut4.dictionary_missing

/-- Installed DICT really falls through TYPE in the same dispatcher
trip. The intermediate ready cut is justified by an identical actual
first-switch execution, not a fabricated normal return at TYPE. -/
theorem EpochCallCut4.dictionary_ready_type_prefix
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = DICT) (present : s.havedict ≠ 0) :
    ∃ _next : EpochCallCut4 c entryHeap (readyDictHeap h r zs z s) r zs entryZ
        {z with adler := 1} {s with check := 1, mode := TYPE} l base raw,
      runX (inflate_dispatch c) l h = runX (inflate_dispatch c) l (readyDictHeap h r zs z s) ∧
      ({s with check := 1, mode := TYPE} : InflateState).last = 0 := by
  obtain ⟨previous, phaseEq⟩ := before.phase.legacy_of_wrapper (Or.inr (Or.inr mode))
  have tables : previous.Materialized h := by
    have materialized := before.materialized
    rw [phaseEq] at materialized
    exact materialized.1
  let old := before.facts.with_legacy previous tables
  obtain ⟨framed⟩ := dictionary_ready_call_cut old.framed mode present
  let next := framed.epoch4_of_origins
    (before.facts.outputStart (by rw [mode]; decide))
    (before.facts.normalRet (by rw [mode]; decide))
    (by simp only [readyDictHeap, setI, ZStreamRef.put_allocOk]; exact before.facts.allocationOracle)
    (by change TYPE ≠ CODELENS; decide)
  have selected : runX (inflate_dispatch c) l (readyDictHeap h r zs z s) =
      runX (inflate_TYPE c) l (readyDictHeap h r zs z s) := by
    rw [inflate_dispatch_block_type framed.cut.env l (Or.inl rfl), ite_eq_left rfl]
  have firstTrip := (inflate_dispatch_DICT old.framed.cut.env l mode).trans
    (inflate_DICT_ready_cut old.framed.cut.env l present)
  exact ⟨next, firstTrip.trans selected.symm, before.facts.wrapperOrigins.last (Or.inr (Or.inr mode))⟩

#print axioms EpochCallCut4.dictionary_ready_type_prefix

end Zlib.Inflate.Proofs.WholeEpoch
