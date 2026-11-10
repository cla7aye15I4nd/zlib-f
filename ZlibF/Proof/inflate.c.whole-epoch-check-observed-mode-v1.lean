import ZlibF.Proof.«inflate.c.whole-epoch-check-source-v1»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FunctionalTrailer Zlib.Inflate.Proofs.WrapperGlue
open Zlib.Inflate.Proofs.WholeWrapper
set_option autoImplicit false

/-- Read the actual post-mode of CHECK on the same observed dispatcher
execution. This supplies causal metadata erased by DispatchResult without
assuming a successor invariant or a callee contract. -/
theorem EpochCallCut.check_observed_mode
    {c : Ctx} {entryHeap h after : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s state : InflateState} {l regs : IL} {base : DataLog} {raw : List UInt8}
    {outcome : Except Ex Unit}
    (before : EpochCallCut c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = CHECK)
    (actual : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (stored : after.istates zs = some state) :
    state.mode = CHECK ∨ state.mode = DONE ∨ state.mode = BAD := by
  let cut := before.framed.cut
  obtain ⟨data, _last, _aligned, empty⟩ := cut.phase.trailer_of_check mode
  obtain ⟨event⟩ := check_word_read cut.buffers.bits cut.credited (data.word_aligned empty) cut.bits
  rcases event.kinds with normal | waiting
  · obtain ⟨count, ledger⟩ := cut.checksum (by rw [mode]; decide) (by rw [mode]; decide)
    have classify := CHECK_after_pull cut.env ledger (by simpa only [normal] using event.actual)
      (by rw [event.shape]) (by rw [event.shape]) (by rw [event.shape])
    by_cases matched : ZSWAP32 event.regs.hold = (adler32 (base.output ++ cut.emitted)).toUInt64
    · have expected := (inflate_dispatch_CHECK cut.env l mode).trans (classify.1 matched)
      have same := xrun_state_eq expected actual (by rw [setI_istates_same]) stored
      right; left
      rw [← same]
    · obtain ⟨message, _literal, rejected⟩ := classify.2 matched
      have expected := (inflate_dispatch_CHECK cut.env l mode).trans rejected
      have same := xrun_state_eq expected actual (by unfold tcBadHeap; rw [setI_istates_same]) stored
      right; right
      rw [← same]
  · have expected := (inflate_dispatch_CHECK cut.env l mode).trans
      (CHECK_wait_cut cut.env l event.regs (by rw [cut.wrapperOrigins.wrapped]; decide)
        (by simpa only [waiting] using event.actual))
    have same := xrun_state_eq expected actual cut.env.hs stored
    left
    exact (congrArg InflateState.mode same).symm.trans mode

/-- The same actual mode observation excludes CODELENS at either kind of
CHECK result, including a waiting ordinary leave. -/
theorem EpochCallCut.check_observed_not_codelens
    {c : Ctx} {entryHeap h after : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s state : InflateState} {l regs : IL} {base : DataLog} {raw : List UInt8}
    {outcome : Except Ex Unit}
    (before : EpochCallCut c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = CHECK)
    (actual : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (stored : after.istates zs = some state) : state.mode ≠ CODELENS := by
  rcases before.check_observed_mode mode actual stored with selected | selected | selected <;>
    rw [selected] <;> decide

#print axioms EpochCallCut.check_observed_mode
#print axioms EpochCallCut.check_observed_not_codelens
end Zlib.Inflate.Proofs.WholeEpoch
