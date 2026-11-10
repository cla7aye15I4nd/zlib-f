import ZlibF.Proof.«inflate.c.stored-block-context»
import ZlibF.Proof.«inflate.c.header-table-cursor-continuation»
import ZlibF.Proof.«inflate.c.header-dynamic-future-entry»

namespace Zlib.Inflate.Proofs.StoredBlockProducer
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.StoredHistory Zlib.Inflate.Proofs.WrapperGlue
open Zlib.Inflate.Proofs.StoredGeneric Zlib.Inflate.Proofs.HeaderSourceTrace
open Zlib.Inflate.Proofs.HeaderPhaseView
set_option autoImplicit false

/-- Actual initialization and earlier split HEAD calls produce the plain
TYPE source packet and empty checksum/window ledger. The current HEAD
completion uses arbitrary output space and flush. The unconsumed current
bytes plus arbitrary future bytes equal the independent body source.
This is the complete-header branch; the existing HEAD wait proof handles
fewer than two cumulative header bytes. No successful public return or
stored state is assumed. -/
theorem head_plain_type_source_entry
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog}
    {history : InflateDataTrace 15 r h log}
    {flush rc : Int32} {input output future bodyBytes : List UInt8} {used : Nat} {cmf flg : UInt8}
    (selected : Epoch r zs .head history)
    (observed : DataStep .inflate h after r flush rc input output used)
    (accepted : ∀ z, r.get h = some z → z.next_out ≠ .null ∧ (z.next_in = .null → z.avail_in = 0))
    (allBytes : (log.input ++ input) ++ future = [cmf, flg] ++ bodyBytes)
    (valid : Zlib.HeaderOK cmf flg) (plain : flg.toNat / 32 % 2 = 0)
    (enough : 2 ≤ log.input.length + input.length) :
    ∃ z state regs heap headerUsed,
      r.get h = some z ∧ headerUsed ≤ input.length ∧ log.input.length + headerUsed = 2 ∧
      DefaultOriginState heap r zs {z with adler := 1} state ∧ DefAlloc {z with adler := 1} ∧
      state.mode = TYPE ∧ state.last = 0 ∧ state.wsize = 0 ∧
      DispatchBuffers heap r regs (input.drop headerUsed) ∧ regs.bits = 0 ∧ regs.hold = 0 ∧
      AdlerCredit {z with adler := 1} state [] ∧ InflateDictionary heap state [] ∧
      regs.put = z.next_out ∧ regs.left = z.avail_out ∧ regs.out_ = regs.left ∧
      regs.have_.toNat + headerUsed = z.avail_in.toNat ∧
      runX (inflate_run ⟨some r, some (.tab zs), syncBuf h, flush⟩) IL.init (syncAlloc h) =
        runX (xwhile (pure true) (inflate_dispatch ⟨some r, some (.tab zs), syncBuf h, flush⟩)) regs heap ∧
      stream regs (input.drop headerUsed) ++ bytesBits future = bytesBits bodyBytes := by
  have before := selected.checked.2
  have before0 := before
  obtain ⟨z, s, initial, allocator, window, _empty, mode, last, wrap, below, count, word, prefixBound⟩ := before
  have getZ := initial.good.live.hz
  obtain ⟨nonnull, inputValid⟩ := accepted z getZ
  have original := observed
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
  have currentEnough : 2 ≤ (log.input ++ input).length := by simp only [List.length_append]; exact enough
  have headerPrefix : (log.input ++ input).take 2 = [cmf, flg] := by
    have initialPrefix := congrArg (List.take 2) allBytes
    rw [List.take_append_of_le_length currentEnough] at initialPrefix
    simpa using initialPrefix
  have currentPrefix : log.input ++ input = [cmf, flg] ++ (log.input ++ input).drop 2 := by
    rw [← headerPrefix, List.take_append_drop]
  have futureSplit : (log.input ++ input).drop 2 ++ future = bodyBytes := by
    have suffix := congrArg (List.drop 2) allBytes
    rw [List.drop_append_of_le_length currentEnough] at suffix
    simpa using suffix
  obtain ⟨pulled, headerUsed, pull, bound, inv, usedCount, read, finish⟩ :=
    EntryPath.HeadHistory.complete_head_type_origin_entry env allocated packet mode (Or.inr wrap)
      count word prefixBound enough
  have guardSource := before0.plain_header_source original currentPrefix valid plain
  have guards : headHeaderRejected s pulled = false ∧ headMethodRejected pulled = false ∧
      (headWindowRegs pulled).len.toNat ≤ 15 ∧ headDefaultMode pulled = TYPE := by
    cases guardSource with
    | observed sourceZ sourceS sourceRegs observedZ observedS sourcePull header method windowSize noDict =>
      have sameZ : sourceZ = z := Option.some.inj (observedZ.symm.trans getZ)
      have sameS : sourceS = s := Option.some.inj (observedS.symm.trans initial.good.live.hs)
      subst sourceZ sourceS
      rw [pull] at sourcePull
      cases sourcePull
      exact ⟨header, method, windowSize, noDict⟩
  obtain ⟨headRun, headCurrent, headPacket, headMode, headLast, _headBits⟩ :=
    finish guards.1 guards.2.1 guards.2.2.1 guards.2.2.2
  let headRegs : IL := {headWindowRegs pulled with hold := 0, bits := 0}
  let headState := headDefaultState s pulled
  let headHeap := setI (r.put (syncAlloc h) {z with adler := 1}) zs headState
  have headEnv : Env c headHeap r zs {z with adler := 1} headState :=
    ⟨rfl, rfl, headCurrent.good.live.hz, headCurrent.good.live.hs⟩
  have entry : runX (inflate_run c) IL.init (syncAlloc h) =
      runX (xwhile (pure true) (inflate_dispatch c)) (dispatchRegs z s) (syncAlloc h) := by
    unfold inflate_run
    rw [runX_bind, runX_rdS env]
    have noType : s.mode ≠ TYPE := by rw [mode]; decide
    simp only [noType, beq_iff_eq, ite_false, runX_bind]
    rw [LOAD_run env]
    simp only []
    rw [runX_modify]
    rfl
  have continuation := entry.trans (loop_prefix_continuation env allocated packet
    (by change s.bits.toNat ≤ 39; omega) headEnv headCurrent headPacket
    (by change (0 : UInt32).toNat ≤ 39; decide) (.step .begin headRun))
  have readHeader := read_wrapper_bytes cmf flg ((log.input ++ input).drop 2)
  rw [currentPrefix, readHeader] at read
  have bodySource : bytesBits (input.drop headerUsed) = bytesBits ((log.input ++ input).drop 2) :=
    (congrArg Prod.snd (Option.some.inj read)).symm
  have headStream : stream headRegs (input.drop headerUsed) ++ bytesBits future = bytesBits bodyBytes := by
    unfold stream
    simp only [headRegs, UInt32.toNat_zero, natBits, List.nil_append]
    rw [bodySource, ← bytesBits_append, futureSplit]
  have headWindow : headState.wsize = 0 := window
  have windowCount := headCurrent.good.inv.win.hv
  rw [headWindow] at windowCount
  have windowZero : headState.whave = 0 := UInt32.toNat_inj.mp (by simpa using Nat.eq_zero_of_le_zero windowCount)
  obtain ⟨_put, leftField, outField⟩ := CumulativeTableBoundary.needbits_output_fields input0
    (by decide : (16 : UInt32).toNat ≤ 49) pull
  have outputCount : headRegs.have_.toNat + headerUsed = z.avail_in.toNat := by
    have a := inv.have_eq
    have b := packet.bits.have_eq
    change z.avail_in.toNat = input.length at b
    simp only [List.length_drop] at a
    change pulled.have_.toNat + headerUsed = z.avail_in.toNat
    omega
  refine ⟨z, headState, headRegs, headHeap, headerUsed, getZ, bound, usedCount,
    headCurrent, allocator, headMode, headLast.trans last, headWindow, headPacket,
    rfl, rfl, ⟨wrap, rfl, rfl, rfl⟩, Or.inl ⟨windowZero, rfl⟩, ?_, ?_, ?_, outputCount,
    continuation, headStream⟩
  · exact _put
  · exact leftField
  · change pulled.out_ = pulled.left
    rw [outField, leftField]
    rfl

#print axioms head_plain_type_source_entry
end Zlib.Inflate.Proofs.StoredBlockProducer

namespace Zlib.Inflate.Proofs.StoredBlockProducer
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.StoredHistory Zlib.Inflate.Proofs.WrapperGlue
open Zlib.Inflate.Proofs.StoredGeneric Zlib.Inflate.Proofs.HeaderSourceTrace
open Zlib.Inflate.Proofs.HeaderPhaseView
set_option autoImplicit false

/-- Actual whole-main wait or stored same-call continuation, with the
exact source-derived packet and payload observation. This bundles the
proved internal result; no public history constructor assumes it. -/
def StoredMainObservation (c : Ctx) (start h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream)
    (l : IL) (bs future dictionary prior payload logical credited : List UInt8)
    (final : Nat) (rest : List Bool) : Prop :=
  (∃ pulled used, used ≤ bs.length ∧
    runX (inflate_run c) IL.init start = .ok ((.error Ex.leave, pulled), h) ∧
    DispatchBuffers h r pulled (bs.drop used) ∧ pulled.bits.toNat ≤ 39 ∧
    stream pulled (bs.drop used) = stream l bs ∧
    pulled.next = inputAdvance l.next used ∧ pulled.have_.toNat + used = l.have_.toNat ∧
    pulled.put = l.put ∧ pulled.left = l.left ∧ pulled.in_ = l.in_ ∧ pulled.out_ = l.out_) ∨
  (∃ regs after state used,
    used ≤ bs.length ∧ runX (inflate_dispatch c) l h = .ok ((.ok (), regs), after) ∧
    runX (inflate_run c) IL.init start = runX (xwhile (pure true) (inflate_dispatch c)) regs after ∧
    DefaultOriginState after r zs z state ∧ state.mode = STORED ∧ state.last = u2i final.toUInt32 ∧
    DispatchBuffers after r regs (bs.drop used) ∧ regs.bits.toNat ≤ 39 ∧
    AdlerCredit z state credited ∧
    InflateDictionary after state (logical.drop (logical.length - 2 ^ state.wbits.toNat)) ∧
    regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
    regs.put = l.put ∧ regs.left = l.left ∧ regs.in_ = l.in_ ∧ regs.out_ = l.out_ ∧
    StoredHeaderObservation c after r zs z state regs (bs.drop used) future dictionary prior payload credited rest)

/-- From the unchanged actual initialized header epoch, a valid first
stored block gives the real source consumer, including split tags and
LEN/NLEN, arbitrary current/future bytes, arbitrary output capacity and
all flush choices. BFINAL can be either zero or one. No initial J, Adler
credit, desired after-mode or callee contract is a caller premise.
This ends at the actual same-call payload/next-block continuation; it is
not an assertion of public completion or the unrestricted sequence goal. -/
theorem head_plain_stored_main_consumer
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog}
    {history : InflateDataTrace 15 r h log}
    {flush rc : Int32} {input output future bodyBytes payload : List UInt8}
    {used final : Nat} {cmf flg : UInt8} {middle bodyInput rest : List Bool}
    (selected : Epoch r zs .head history)
    (observed : DataStep .inflate h after r flush rc input output used)
    (accepted : ∀ z, r.get h = some z → z.next_out ≠ .null ∧ (z.next_in = .null → z.avail_in = 0))
    (allBytes : (log.input ++ input) ++ future = [cmf, flg] ++ bodyBytes)
    (valid : Zlib.HeaderOK cmf flg) (plain : flg.toNat / 32 % 2 = 0)
    (enough : 2 ≤ log.input.length + input.length)
    (first : readBits 1 (bytesBits bodyBytes) = some (final, middle))
    (second : readBits 2 middle = some (0, bodyInput))
    (body : Body [] 0 [] bodyInput rest payload) :
    ∃ z state regs heap headerUsed,
      r.get h = some z ∧ headerUsed ≤ input.length ∧ log.input.length + headerUsed = 2 ∧ log.output = [] ∧
      DefaultOriginState heap r zs {z with adler := 1} state ∧ DefAlloc {z with adler := 1} ∧
      state.mode = TYPE ∧ state.last = 0 ∧ state.wsize = 0 ∧
      DispatchBuffers heap r regs (input.drop headerUsed) ∧ AdlerCredit {z with adler := 1} state [] ∧
      InflateDictionary heap state [] ∧
      regs.put = z.next_out ∧ regs.left = z.avail_out ∧ regs.out_ = regs.left ∧
      regs.have_.toNat + headerUsed = z.avail_in.toNat ∧
      StoredMainObservation ⟨some r, some (.tab zs), syncBuf h, flush⟩ (syncAlloc h) heap r zs
        {z with adler := 1} regs (input.drop headerUsed) future [] [] payload [] [] final rest := by
  obtain ⟨z, state, regs, heap, headerUsed, getZ, bound, headerCount,
    origin, allocator, mode, last, window, packet, bits, _hold, credit, saved,
    put, left, out_, haveCount, mainCut, source⟩ :=
    head_plain_type_source_entry selected observed accepted allBytes valid plain enough
  have currentEnv : Env ⟨some r, some (.tab zs), syncBuf h, flush⟩ heap r zs {z with adler := 1} state :=
    ⟨rfl, rfl, origin.good.live.hz, origin.good.live.hs⟩
  have firstCurrent : readBits 1 (stream regs (input.drop headerUsed) ++ bytesBits future) = some (final, middle) := by
    rw [source]; exact first
  have currentSaved : InflateDictionary heap state (([] : List UInt8).drop (0 - 2 ^ state.wbits.toNat)) := by
    simpa only [List.drop_nil] using saved
  have observedMain := stored_source_main_consumer (logical := []) currentEnv origin packet (Or.inl mode) last
    (by rw [bits]; decide) credit currentSaved mainCut firstCurrent second body
  obtain ⟨_z, _s, _j, _a, _window, empty, _phase⟩ := selected.checked.2
  exact ⟨z, state, regs, heap, headerUsed, getZ, bound, headerCount, empty,
    origin, allocator, mode, last, window, packet, credit, saved,
    put, left, out_, haveCount, observedMain⟩

#print axioms head_plain_stored_main_consumer
end Zlib.Inflate.Proofs.StoredBlockProducer

namespace Zlib.Inflate.Proofs.StoredBlockProducer
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.StoredHistory Zlib.Inflate.Proofs.WrapperGlue
open Zlib.Inflate.Proofs.StoredGeneric Zlib.Inflate.Proofs.HeaderSourceTrace
open Zlib.Inflate.Proofs.HeaderPhaseView
set_option autoImplicit false

/-- Arbitrary current input at the actual initialized plain-header epoch:
HEAD remains a real public wait when incomplete; otherwise the same call
has the complete generic stored source observation. No current input size,
output size, flush or BFINAL value is excluded from this case split. -/
theorem head_plain_stored_arbitrary_main_consumer
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog}
    {history : InflateDataTrace 15 r h log}
    {flush rc : Int32} {input output future bodyBytes payload : List UInt8}
    {used final : Nat} {cmf flg : UInt8} {middle bodyInput rest : List Bool}
    (selected : Epoch r zs .head history)
    (observed : DataStep .inflate h after r flush rc input output used)
    (accepted : ∀ z, r.get h = some z → z.next_out ≠ .null ∧ (z.next_in = .null → z.avail_in = 0))
    (allBytes : (log.input ++ input) ++ future = [cmf, flg] ++ bodyBytes)
    (valid : Zlib.HeaderOK cmf flg) (plain : flg.toNat / 32 % 2 = 0)
    (first : readBits 1 (bytesBits bodyBytes) = some (final, middle))
    (second : readBits 2 middle = some (0, bodyInput))
    (body : Body [] 0 [] bodyInput rest payload) :
    HeaderPhaseView.Meaning .head after r zs (HeaderPhaseView.credit log input output used rc) ∨
    (∃ z state regs heap headerUsed,
      r.get h = some z ∧ headerUsed ≤ input.length ∧ log.input.length + headerUsed = 2 ∧ log.output = [] ∧
      DefaultOriginState heap r zs {z with adler := 1} state ∧ DefAlloc {z with adler := 1} ∧
      state.mode = TYPE ∧ state.last = 0 ∧ state.wsize = 0 ∧
      DispatchBuffers heap r regs (input.drop headerUsed) ∧ AdlerCredit {z with adler := 1} state [] ∧
      InflateDictionary heap state [] ∧
      regs.put = z.next_out ∧ regs.left = z.avail_out ∧ regs.out_ = regs.left ∧
      regs.have_.toNat + headerUsed = z.avail_in.toNat ∧
      StoredMainObservation ⟨some r, some (.tab zs), syncBuf h, flush⟩ (syncAlloc h) heap r zs
        {z with adler := 1} regs (input.drop headerUsed) future [] [] payload [] [] final rest) := by
  by_cases short : log.input.length + input.length < 2
  · exact Or.inl ((selected.head_short_input (actual := observed) short).checked.2)
  · exact Or.inr (head_plain_stored_main_consumer selected observed accepted allBytes valid plain (by omega) first second body)

#print axioms head_plain_stored_arbitrary_main_consumer
end Zlib.Inflate.Proofs.StoredBlockProducer

namespace Zlib.Inflate.Proofs.StoredBlockProducer
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.HeaderPhaseView
set_option autoImplicit false

/-- The unchanged successful default initializer itself supplies the
source-only HEAD epoch used above. Allocation success is derived from
that actual run, rather than imposed as an extra public precondition. -/
theorem initialized_head_epoch
    {before initialized : Heap} {r : ZStreamRef} {version : BPtr}
    (domain : InitDomain before r version) (platform : ZlibF.PlatformMemory.ByteObjectsFit before)
    (actual : C.run (inflateInit2_ (some r) 15 version 112) before = .ok (Z_OK, initialized)) :
    Epoch r before.nextBlk .head (.init domain actual) := by
  have allocation : before.allocOk before.nalloc = true := by
    apply Classical.byContradiction
    intro failed
    obtain ⟨_fresh, _uniq, _globals, validVersion, z, get, allocators, _null⟩ := domain
    obtain ⟨nonnull, first⟩ := ZlibF.Spec.Public.Proofs.InflateInit.version_value_read validVersion
    have refuse := inflateInit2_memfail (w := 15) get _fresh failed allocators.1 allocators.2 nonnull first
    change inflateInit2_ (some r) 15 version 112 before = .ok (Z_OK, initialized) at actual
    rw [actual] at refuse
    cases refuse
  exact .head (.init (domain := domain) (actual := actual) platform allocation)

#print axioms initialized_head_epoch
end Zlib.Inflate.Proofs.StoredBlockProducer
