import ZlibF.Proof.«inflate.c.whole-epoch-wrapper-dispatch-v4-v1»
import ZlibF.Proof.«inflate.c.whole-epoch-source-routes»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- The actual default HEAD suffix can only wait or select its literal
BAD/TYPE/DICTID branches, so CODE routing is inactive on its post-state. -/
theorem EpochCallCut4.head_observed_not_codes
    {c : Ctx} {entryHeap h after : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s state : InflateState} {l regs : IL} {base : DataLog} {raw : List UInt8} {outcome : Except Ex Unit}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw) (mode : s.mode = HEAD)
    (actual : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (stored : after.istates zs = some state) : state.mode ≠ CODELENS := by
  obtain ⟨exit, regs0, heap0, stream0, state0, used, _bound, source, current, _tables,
    _pending, _packet, _sizes, _next, _have, _put, _left, _bits, _static, kinds⟩ :=
    inflate_HEAD_default_boundary before.facts.env before.facts.origin.good before.facts.origin.pending
      before.facts.buffers mode before.facts.wrapperOrigins.wrapped before.facts.origin.header before.facts.origin.window
  have expected := (inflate_dispatch_HEAD before.facts.env l mode).trans source
  have same := xrun_state_eq expected actual current.live.hs stored
  rw [← same]
  rcases kinds with ⟨_waiting, sameState⟩ | ⟨_normal, selected⟩
  · rw [sameState, mode]; decide
  · rcases selected with selected | selected | selected <;> rw [selected] <;> decide

/-- A real default DICTID completion must call the missing-DICT branch,
not an invented normal continuation. Waiting retains DICTID. -/
theorem EpochCallCut4.dictid_observed_not_codes
    {c : Ctx} {entryHeap h after : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s state : InflateState} {l regs : IL} {base : DataLog} {raw : List UInt8} {outcome : Except Ex Unit}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw) (mode : s.mode = DICTID)
    (actual : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (stored : after.istates zs = some state) : state.mode ≠ CODELENS := by
  obtain ⟨exit, current, used, pull, _bound, _inv, _source, _count, _shape,
    _upper, _identity, _full, _wait, kinds, _cursor⟩ := NEEDBITS_run_cursor before.facts.buffers.bits 32 (by decide)
  rcases kinds with normal | waiting
  · let ready := {s with check := ZSWAP32 current.hold, mode := DICT}
    let stream := {z with adler := ZSWAP32 current.hold}
    let heap := setI (r.put h stream) zs ready
    have getZ : r.get heap = some stream := by rw [ZStreamRef.get_setI]; exact ZStreamRef.get_put_same before.facts.env.hz _
    have getS : heap.istates zs = some ready := by dsimp only [heap]; rw [setI_istates_same]
    have env : Env c heap r zs stream ready := ⟨before.facts.env.strm, before.facts.env.st, getZ, getS⟩
    have missing : ready.havedict = 0 := before.facts.wrapperOrigins.missing (Or.inr mode)
    have parsed := inflate_DICTID_parsed_cut before.facts.env l current (by simpa only [normal] using pull)
    have expected := (inflate_dispatch_DICTID before.facts.env l mode).trans
      (parsed.trans (inflate_DICT_wait_run env {current with hold := 0, bits := 0} missing))
    have same := xrun_state_eq expected actual (by rw [setI_istates_same]) stored
    rw [← same]
    change DICT ≠ CODELENS
    decide
  · have expected := (inflate_dispatch_DICTID before.facts.env l mode).trans
      (inflate_DICTID_wait (c := c) (by simpa only [waiting] using pull))
    have same := xrun_state_eq expected actual before.facts.env.hs stored
    rw [← same, mode]
    decide

/-- The literal missing-DICT return keeps its actual private mode. -/
theorem EpochCallCut4.dictionary_missing_observed_not_codes
    {c : Ctx} {entryHeap h after : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s state : InflateState} {l regs : IL} {base : DataLog} {raw : List UInt8} {outcome : Except Ex Unit}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = DICT) (missing : s.havedict = 0)
    (actual : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (stored : after.istates zs = some state) : state.mode ≠ CODELENS := by
  have expected := (inflate_dispatch_DICT before.facts.env l mode).trans (inflate_DICT_wait_run before.facts.env l missing)
  have same := xrun_state_eq expected actual (by rw [setI_istates_same]) stored
  rw [← same]
  change s.mode ≠ CODELENS
  rw [mode]
  decide

/-- Exhaustive HEAD supplies the shared source-fold envelope together
with the routed post-phase, derived from its actual resulting mode. -/
theorem SourceCallCut.head_dispatch
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : SourceCallCut c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = HEAD) : Nonempty (SourceDispatch before) := by
  obtain ⟨result⟩ := before.core.head_dispatch mode
  cases result with
  | progress after stream state regs actual next =>
    exact ⟨⟨.progress after stream state regs actual next,
      next.phase.routed_of_not_codes (before.core.head_observed_not_codes (state := state) mode actual next.facts.env.hs)⟩⟩
  | stopped after stream state regs exit actual next =>
    exact ⟨⟨.stopped after stream state regs exit actual next,
      next.phase.routed_of_not_codes (before.core.head_observed_not_codes (state := state) mode actual next.facts.env.hs)⟩⟩

theorem SourceCallCut.dictid_dispatch
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : SourceCallCut c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = DICTID) : Nonempty (SourceDispatch before) := by
  obtain ⟨result⟩ := before.core.dictid_dispatch mode
  cases result with
  | progress after stream state regs actual next =>
    exact ⟨⟨.progress after stream state regs actual next,
      next.phase.routed_of_not_codes (before.core.dictid_observed_not_codes (state := state) mode actual next.facts.env.hs)⟩⟩
  | stopped after stream state regs exit actual next =>
    exact ⟨⟨.stopped after stream state regs exit actual next,
      next.phase.routed_of_not_codes (before.core.dictid_observed_not_codes (state := state) mode actual next.facts.env.hs)⟩⟩

theorem SourceCallCut.dictionary_missing
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : SourceCallCut c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = DICT) (missing : s.havedict = 0) : Nonempty (SourceDispatch before) := by
  obtain ⟨result⟩ := before.core.dictionary_missing mode missing
  cases result with
  | progress after stream state regs actual next =>
    exact ⟨⟨.progress after stream state regs actual next,
      next.phase.routed_of_not_codes (before.core.dictionary_missing_observed_not_codes (state := state) mode missing actual next.facts.env.hs)⟩⟩
  | stopped after stream state regs exit actual next =>
    exact ⟨⟨.stopped after stream state regs exit actual next,
      next.phase.routed_of_not_codes (before.core.dictionary_missing_observed_not_codes (state := state) mode missing actual next.facts.env.hs)⟩⟩

#print axioms EpochCallCut4.head_observed_not_codes
#print axioms EpochCallCut4.dictid_observed_not_codes
#print axioms EpochCallCut4.dictionary_missing_observed_not_codes
#print axioms SourceCallCut.head_dispatch
#print axioms SourceCallCut.dictid_dispatch
#print axioms SourceCallCut.dictionary_missing
end Zlib.Inflate.Proofs.WholeEpoch
