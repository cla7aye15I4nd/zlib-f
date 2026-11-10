import ZlibF.Proof.«inflate.c.header-public-observer»
import ZlibF.Proof.«inflate.c.entry-public-chain»
namespace Zlib.Inflate.Proofs.HeaderPhaseView
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public Zlib.Inffast.Proofs
open Zlib.Inflate.Proofs
set_option autoImplicit false

theorem View.readBits_prefix {width value : Nat} {credited remaining : List Bool}
    (read : readBits width (credited ++ remaining) = some (value, remaining)) :
    View (readBits width) value credited [] := by
  obtain ⟨bound, word⟩ := ZlibF.Math.CodeLengthPrefix.read_word read
  have source : credited = bitsOfNat value width := List.append_inj_left' word rfl
  intro future
  rw [source]
  simpa only [List.nil_append, Nat.mod_eq_of_lt bound, Nat.sub_self, bitsOfNat_zero] using
    readBits_bitsOfNat width width value future (Nat.le_refl _)

/-- The actual normal HEAD trip followed by TYPE's flush leave is the same
source while loop, using its live registers. -/
theorem head_pause_main_run
    {c : Ctx} {h headHeap : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {headRegs : IL} (E : Env c h r zs z s) (mode : s.mode = HEAD)
    (headRun : runX (inflate_dispatch c) (dispatchRegs z s) h = .ok ((.ok (), headRegs), headHeap))
    (pauseRun : runX (inflate_dispatch c) headRegs headHeap = .ok ((.error Ex.leave, headRegs), headHeap)) :
    runX (inflate_run c) IL.init h = .ok ((.error Ex.leave, headRegs), headHeap) := by
  let locals : Nat → IL := fun j => if j = 0 then dispatchRegs z s else headRegs
  let heaps : Nat → Heap := fun j => if j = 0 then h else headHeap
  have steps : ∀ j, j < 1 → runX (inflate_dispatch c) (locals j) (heaps j) =
      .ok ((.ok (), locals (j + 1)), heaps (j + 1)) := by
    intro j bound
    have zero : j = 0 := by omega
    subst j
    simpa only [locals, heaps, ite_true, Nat.zero_add, show ¬ (1 : Nat) = 0 from by decide, ite_false] using headRun
  have stop : runX (inflate_dispatch c) (locals 1) (heaps 1) =
      .ok ((.error Ex.leave, headRegs), headHeap) := by
    simpa only [locals, heaps, show ¬ (1 : Nat) = 0 from by decide, ite_false] using pauseRun
  have loop := xwhile_run_chain (inflate_dispatch c) locals heaps 1 (by unfold fuel; decide)
    Ex.leave headRegs headHeap steps stop
  have entry : runX (inflate_run c) IL.init h =
      runX (xwhile (pure true) (inflate_dispatch c)) (dispatchRegs z s) h := by
    unfold inflate_run
    rw [runX_bind, runX_rdS E]
    have noType : s.mode ≠ TYPE := by rw [mode]; decide
    simp only [noType, beq_iff_eq, ite_false, runX_bind]
    rw [LOAD_run E]
    simp only []
    rw [runX_modify]
    rfl
  exact entry.trans loop

/-- Source-complete HEAD pauses at TYPE for Z_BLOCK or Z_TREES, crediting
exactly the cumulative two wrapper bytes through actual alloc/body/leave/free.
The explicit guards select the real accepted no-dictionary source branch. -/
theorem Meaning.head_complete_pause
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog}
    {flush rc : Int32} {input output : List UInt8} {used : Nat}
    (history : InflateDataTrace 15 r h log) (scope : HeaderDataTrace.PlatformScope history)
    (before : Meaning .head h r zs log)
    (observed : DataStep .inflate h after r flush rc input output used)
    (pause : flush = Z_BLOCK ∨ flush = Z_TREES)
    (enough : 2 ≤ log.input.length + input.length)
    (accepted : ∀ stream0, r.get h = some stream0 → stream0.next_out ≠ .null ∧
      (stream0.next_in = .null → stream0.avail_in = 0)) :
    ∃ (stream0 : ZStream) (state : InflateState) (pulled : IL) (headerUsed : Nat),
      r.get h = some stream0 ∧ h.istates zs = some state ∧
      runX (NEEDBITS 16) (dispatchRegs stream0 state) (syncAlloc h) = .ok ((.ok (), pulled), syncAlloc h) ∧
      headerUsed ≤ input.length ∧ log.input.length + headerUsed = 2 ∧
      (headHeaderRejected state pulled = false → headMethodRejected pulled = false →
        (headWindowRegs pulled).len.toNat ≤ 15 → headDefaultMode pulled = TYPE →
        used = headerUsed ∧ Meaning .block after r zs (credit log input output used rc)) := by
  obtain ⟨z, s, initial, allocator, window, empty, mode, last, wrap, below, count, word, prefixBound⟩ := before
  have getZ := initial.good.live.hz
  have getS := initial.good.live.hs
  obtain ⟨nonnull, inputValid⟩ := accepted z getZ
  obtain ⟨z0, returned, get0, get1, buffers, activeHeader, inputBytes, usedEq, outputBytes, actual⟩ := observed
  have sameZ : z0 = z := Option.some.inj (get0.symm.trans getZ)
  subst z0
  have source := header_input_view_of_bytes (s := s) inputBytes initial.held
  have allocated := default_origin_syncAlloc initial
  have input0 : BitInv (syncAlloc h) (dispatchRegs z s) input := by
    refine ⟨source.have_eq, ?_, source.hold_lt⟩
    rcases source.next with none | ⟨ref, array, off, pointer, get, bound, values⟩
    · exact Or.inl none
    · exact Or.inr ⟨ref, array, off, pointer, (byte_view_syncAlloc initial.good.fresh get).1, bound, values⟩
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have env : Env c (syncAlloc h) r zs z s := ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  have output0 := dispatchRegs_output env.hz (streamBuffers_syncAlloc initial.good.fresh buffers) nonnull s
  obtain ⟨z1, gz1, rangeIn, _rangeOut, separate⟩ := streamBuffers_syncAlloc initial.good.fresh buffers
  have sameZ1 : z1 = z := Option.some.inj (gz1.symm.trans env.hz)
  subst z1
  have packet : DispatchBuffers (syncAlloc h) r (dispatchRegs z s) input := ⟨rangeIn, output0, separate, input0⟩
  obtain ⟨pulled, headerUsed, pull, bound, inv, usedCount, read, finish⟩ :=
    EntryPath.HeadHistory.complete_head_type_origin_entry env allocated packet mode (Or.inr wrap) count word prefixBound enough
  refine ⟨z, s, pulled, headerUsed, getZ, getS, pull, bound, usedCount, ?_⟩
  intro header method windowSize noDict
  obtain ⟨headRun, headCurrent, headPacket, headMode, headLast, _headBits⟩ := finish header method windowSize noDict
  let headRegs : IL := { headWindowRegs pulled with hold := 0, bits := 0 }
  let headState := headDefaultState s pulled
  let headHeap := setI (r.put (syncAlloc h) { z with adler := 1 }) zs headState
  have headEnv : Env c headHeap r zs { z with adler := 1 } headState := ⟨rfl, rfl, headCurrent.good.live.hz, headCurrent.good.live.hs⟩
  have selected := inflate_dispatch_block_type headEnv headRegs (Or.inl headMode)
  rw [if_pos headMode] at selected
  have pauseRun : runX (inflate_dispatch c) headRegs headHeap = .ok ((.error Ex.leave, headRegs), headHeap) :=
    selected.trans (inflate_TYPE_leave c headRegs headHeap pause)
  have mainRun := head_pause_main_run env mode headRun pauseRun
  obtain ⟨_put, left, out⟩ := CumulativeTableBoundary.needbits_output_fields input0 (by decide : (16 : UInt32).toNat ≤ 49) pull
  have noOutput : headRegs.out_ = headRegs.left := by
    change pulled.out_ = pulled.left
    rw [left, out]
    rfl
  have headWindow : headState.wsize = 0 := window
  obtain ⟨nextZ, nextS, next, nextAllocator, frame, nextIn, nextAvail, nextOut, nextLeft⟩ :=
    HeaderPublicObserver.actual_wait_from_init history scope
      ⟨z, returned, getZ, get1, buffers, activeHeader, inputBytes, usedEq, outputBytes, actual⟩
      getZ initial.good.live.zst getS nonnull inputValid mainRun headCurrent.good.live.hs headWindow noOutput
  have sameReturned : returned = nextZ := Option.some.inj (get1.symm.trans next.good.live.hz)
  subst returned
  have avail : pulled.have_.toNat = (input.drop headerUsed).length := inv.have_eq
  have originalAvail : z.avail_in.toNat = input.length := source.have_eq
  have usedSame : used = headerUsed := by
    rw [usedEq, nextAvail]
    change z.avail_in.toNat - pulled.have_.toNat = headerUsed
    rw [originalAvail, avail, List.length_drop]
    omega
  have noBytes : output = [] := by
    have outputLength := header_observed_bytes_length outputBytes
    rw [nextLeft] at outputLength
    change output.length = z.avail_out.toNat - pulled.left.toNat at outputLength
    rw [left] at outputLength
    change output.length = z.avail_out.toNat - z.avail_out.toNat at outputLength
    rw [Nat.sub_self] at outputLength
    exact List.length_eq_zero_iff.mp outputLength
  have wrapper : View (readBits 16) (pulled.hold.toNat % 2 ^ 16)
      (bytesBits (log.input ++ input.take headerUsed)) [] := by
    apply View.readBits_prefix (remaining := bytesBits (input.drop headerUsed))
    have split : bytesBits (log.input ++ input) =
        bytesBits (log.input ++ input.take headerUsed) ++ bytesBits (input.drop headerUsed) := by
      rw [← bytesBits_append, List.append_assoc, List.take_append_drop]
    rw [← split]
    exact read
  refine ⟨usedSame, nextZ, nextS, next, nextAllocator, ?_, ?_, ?_⟩
  · rw [frame]; exact headWindow
  · simp only [credit, empty, noBytes, List.nil_append]
  · refine ⟨Or.inl ?_, ?_, ?_, ?_, pulled.hold.toNat % 2 ^ 16, ?_⟩
    · rw [frame]; exact headMode
    · rw [frame]; exact headLast.trans last
    · rw [frame]; rfl
    · rw [frame]; rfl
    · simpa only [credit, usedSame] using wrapper

/-- Source-only selection of successful primitive HEAD reading and its
literal C guards. It contains neither an invariant nor a parser postcondition. -/
inductive PlainHeadSource (h : Heap) (r : ZStreamRef) (zs : Nat) : Prop where
  | observed (z : ZStream) (s : InflateState) (pulled : IL)
      (getZ : r.get h = some z) (getS : h.istates zs = some s)
      (pull : runX (NEEDBITS 16) (dispatchRegs z s) (syncAlloc h) = .ok ((.ok (), pulled), syncAlloc h))
      (header : headHeaderRejected s pulled = false) (method : headMethodRejected pulled = false)
      (window : (headWindowRegs pulled).len.toNat ≤ 15) (plain : headDefaultMode pulled = TYPE) :
      PlainHeadSource h r zs

theorem Meaning.head_pause
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog}
    {flush rc : Int32} {input output : List UInt8} {used : Nat}
    (history : InflateDataTrace 15 r h log) (scope : HeaderDataTrace.PlatformScope history)
    (before : Meaning .head h r zs log)
    (observed : DataStep .inflate h after r flush rc input output used)
    (pause : flush = Z_BLOCK ∨ flush = Z_TREES)
    (enough : 2 ≤ log.input.length + input.length)
    (accepted : ∀ stream0, r.get h = some stream0 → stream0.next_out ≠ .null ∧
      (stream0.next_in = .null → stream0.avail_in = 0))
    (source : PlainHeadSource h r zs) :
    Meaning .block after r zs (credit log input output used rc) := by
  obtain ⟨z, s, pulled, headerUsed, getZ, getS, pull, _bound, _count, complete⟩ :=
    before.head_complete_pause history scope observed pause enough accepted
  cases source with
  | observed sourceZ sourceS sourceRegs observedZ observedS actual header method window plain =>
    have sameZ : sourceZ = z := Option.some.inj (observedZ.symm.trans getZ)
    have sameS : sourceS = s := Option.some.inj (observedS.symm.trans getS)
    subst sourceZ sourceS
    rw [pull] at actual
    cases actual
    exact (complete header method window plain).2

#print axioms View.readBits_prefix
#print axioms head_pause_main_run
#print axioms Meaning.head_complete_pause
#print axioms Meaning.head_pause
end Zlib.Inflate.Proofs.HeaderPhaseView
