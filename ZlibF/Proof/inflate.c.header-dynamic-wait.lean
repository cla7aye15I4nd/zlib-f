import ZlibF.Proof.«inflate.c.header-block-consumer»
namespace Zlib.Inflate.Proofs.HeaderPhaseView
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public Zlib.Inffast.Proofs
open Zlib.Inflate.Proofs
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The first dynamic block header can cross from a real public TYPE
boundary into a stored TABLE wait. The one- or two-byte source condition
selects exactly the branch which cannot yet fill TABLE's fourteen bits. -/
theorem Meaning.block_dynamic_wait
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog}
    {flush rc : Int32} {input output : List UInt8} {used : Nat}
    (history : InflateDataTrace 15 r h log) (scope : HeaderDataTrace.PlatformScope history)
    (before : Meaning .block h r zs log)
    (observed : DataStep .inflate h after r flush rc input output used)
    (nonempty : 1 ≤ input.length) (short : input.length ≤ 2)
    (flushing : flush ≠ Z_BLOCK ∧ flush ≠ Z_TREES)
    (accepted : ∀ stream0, r.get h = some stream0 → stream0.next_out ≠ .null ∧
      (stream0.next_in = .null → stream0.avail_in = 0)) :
    ∃ (stream0 : ZStream) (original : InflateState) (entryHeap : Heap) (entryS : InflateState) (pulled : IL),
      r.get h = some stream0 ∧ h.istates zs = some original ∧
      entryS = (if original.mode = TYPE then { original with mode := TYPEDO } else original) ∧
      entryHeap = setI (syncAlloc h) zs entryS ∧
      entryHeap.istates zs = some entryS ∧
      runX (NEEDBITS 3) (dispatchRegs stream0 entryS) entryHeap = .ok ((.ok (), pulled), entryHeap) ∧
      ((pulled.hold >>> 1).toNat % 4 = 2 → Meaning .table after r zs (credit log input output used rc)) := by
  obtain ⟨z, s, initial, allocator, window, empty, modes, last, bits0, hold0, header, view⟩ := before
  obtain ⟨nonnull, inputValid⟩ := accepted z initial.good.live.hz
  obtain ⟨z0, returned, get0, get1, buffers, active, inputBytes, usedEq, outputBytes, run⟩ := observed
  have sameZ : z0 = z := Option.some.inj (get0.symm.trans initial.good.live.hz)
  subst z0
  have allocated := default_origin_syncAlloc initial
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have env : Env c (syncAlloc h) r zs z s := ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  obtain ⟨entryHeap, entryS, bs, entryRun, entryJ, entryEnv, packet0, entryBits, _sizes, frame, heapEq, stateEq⟩ :=
    block_entry_source env allocated.toDefaultStateJ (streamBuffers_syncAlloc initial.good.fresh buffers) nonnull inputValid
  have entryOrigin := allocated.decode_update entryJ frame
  have entryLast : entryS.last = 0 := by rw [frame]; exact last
  have entryZero : entryS.bits = 0 := by rw [frame]; exact bits0
  have entryHold : entryS.hold = 0 := by rw [frame]; exact hold0
  have entryWindow : entryS.wsize = 0 := by rw [frame]; exact window
  have entryMode : entryS.mode = TYPEDO := by
    rw [stateEq]
    rcases modes with mode | mode
    · simp only [mode, ↓reduceIte]
    · have noType : s.mode ≠ TYPE := by rw [mode]; decide
      rw [if_neg noType]; exact mode
  have source := header_input_view_of_bytes (s := s) inputBytes initial.held
  have input0 : BitInv entryHeap (dispatchRegs z entryS) input := by
    refine ⟨source.have_eq, ?_, ?_⟩
    · rcases source.next with none | ⟨ref, array, off, pointer, get, bound, values⟩
      · exact Or.inl none
      · refine Or.inr ⟨ref, array, off, pointer, ?_, bound, values⟩
        rw [heapEq, byte_view_get_setI]
        exact (byte_view_syncAlloc initial.good.fresh get).1
    · change entryS.hold.toNat < 2 ^ entryS.bits.toNat
      rw [frame]; exact source.hold_lt
  have packet : DispatchBuffers entryHeap r (dispatchRegs z entryS) input := ⟨packet0.input, packet0.output, packet0.separate, input0⟩
  obtain ⟨outcome, pulled, blockUsed, pull, bound, inv, acceptedBlock⟩ :=
    EntryPath.dynamic_block_origin_entry entryEnv entryOrigin packet (Or.inr entryMode) flushing entryLast entryBits
  obtain ⟨outcome0, pulled0, used0, pull0, bound0, inv0, source0, bitCount, shape,
    _max, _same, full, wait, kinds, cursor⟩ := NEEDBITS_run_cursor input0 3 (by decide)
  rw [pull] at pull0
  cases pull0
  have normal : outcome = .ok () := by
    rcases kinds with normal | leave
    · exact normal
    · obtain ⟨all, _none, below⟩ := wait leave
      have count0 := bitCount
      change pulled.bits.toNat = entryS.bits.toNat + 8 * used0 at count0
      rw [entryZero, UInt32.toNat_zero, Nat.zero_add, all] at count0
      change pulled.bits.toNat < 3 at below
      omega
  refine ⟨z, s, entryHeap, entryS, pulled, initial.good.live.hz, initial.good.live.hs, stateEq, heapEq, entryEnv.hs, ?_, ?_⟩
  · simpa only [normal] using pull
  intro dynamic
  obtain ⟨blockRun, dynamicOrigin, dynamicPacket, readLast, readKind, _rest, dynamicBits⟩ := acceptedBlock normal dynamic
  let first : IL := { pulled with hold := pulled.hold >>> 1, bits := pulled.bits - 1 }
  let regs : IL := { first with hold := first.hold >>> 2, bits := first.bits - 2 }
  let dynState := { entryS with last := u2i (pulled.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1)), mode := TABLE }
  let dynHeap := setI entryHeap zs dynState
  have dynEnv : Env c dynHeap r zs z dynState := ⟨rfl, rfl, dynamicOrigin.good.live.hz, dynamicOrigin.good.live.hs⟩
  obtain ⟨tableOutcome, finalRegs, tableUsed, tablePull, tableBound, finalInv, tableSource, tableWait, _tableNormal⟩ :=
    inflate_TABLE_run dynEnv.strm dynEnv.st dynEnv.hz dynEnv.hs dynamicPacket.bits
  have blockUsedSame : blockUsed = used0 := by
    have a := inv.have_eq
    have b := inv0.have_eq
    rw [List.length_drop] at a b
    omega
  subst used0
  have blockBits : pulled.bits.toNat = 8 * blockUsed := by
    simpa only [dispatchRegs, entryZero, UInt32.toNat_zero, Nat.zero_add] using bitCount
  have full3 : 3 ≤ pulled.bits.toNat := full normal
  have finalBits : regs.bits.toNat = 8 * blockUsed - 3 := by
    obtain ⟨inv1, _source1, firstBits⟩ := DROPBITS_inv inv 1 (by change 1 ≤ pulled.bits.toNat; omega) (by decide)
    change (pulled.bits - 1).toNat = pulled.bits.toNat - 1 at firstBits
    obtain ⟨_inv2, _source2, secondBits⟩ := DROPBITS_inv inv1 2 (by change 2 ≤ (pulled.bits - 1).toNat; omega) (by decide)
    change (pulled.bits - 1 - 2).toNat = (pulled.bits - 1).toNat - 2 at secondBits
    change (pulled.bits - 1 - 2).toNat = _
    rw [secondBits, firstBits, blockBits]; omega
  obtain ⟨tableOutcome0, finalRegs0, tableUsed0, tablePull0, tableBound0, _finalInv0, _sourceTable0, tableBitCount, _tableShape, _maxTable, _sameTable, tableFull, _waitTable, tableKinds, _cursorTable⟩ :=
    NEEDBITS_run_cursor dynamicPacket.bits 14 (by decide)
  rw [tablePull] at tablePull0
  cases tablePull0
  have tableError : tableOutcome = .error Ex.leave := by
    rcases tableKinds with normalTable | leave
    · have enough : 14 ≤ finalRegs.bits.toNat := tableFull normalTable
      change finalRegs.bits.toNat = regs.bits.toNat + 8 * tableUsed0 at tableBitCount
      rw [finalBits] at tableBitCount
      rw [List.length_drop] at tableBound0
      omega
    · exact leave
  obtain ⟨finalHave, _allTable, _below, tableRun⟩ := tableWait tableError
  have tableDispatch := (inflate_dispatch_TABLE dynEnv regs rfl).trans tableRun
  let locals : Nat → IL := fun j => if j = 0 then dispatchRegs z entryS else regs
  let heaps : Nat → Heap := fun j => if j = 0 then entryHeap else dynHeap
  have steps : ∀ j, j < 1 → runX (inflate_dispatch c) (locals j) (heaps j) = .ok ((.ok (), locals (j + 1)), heaps (j + 1)) := by
    intro j small
    have zero : j = 0 := by omega
    subst j
    simpa only [locals, heaps, ite_true, Nat.zero_add, show ¬ (1 : Nat) = 0 from by decide, ite_false] using blockRun
  have stop : runX (inflate_dispatch c) (locals 1) (heaps 1) = .ok ((.error Ex.leave, finalRegs), dynHeap) := by
    simpa only [locals, heaps, show ¬ (1 : Nat) = 0 from by decide, ite_false] using tableDispatch
  have loop := xwhile_run_chain (inflate_dispatch c) locals heaps 1 (by unfold fuel; decide) Ex.leave finalRegs dynHeap steps stop
  have mainRun := entryRun.trans loop
  have blockOutput : regs.out_ = regs.left := by
    change pulled.out_ = pulled.left
    rw [shape]
    rfl
  have noOutput : finalRegs.out_ = finalRegs.left := by
    rw [_tableShape]
    exact blockOutput
  have dynWindow : dynState.wsize = 0 := entryWindow
  obtain ⟨nextZ, nextS, next, nextAllocator, metadata, _nextIn, nextAvail, _nextOut, nextLeft⟩ :=
    HeaderPublicObserver.actual_wait_from_init history scope
      ⟨z, returned, initial.good.live.hz, get1, buffers, active, inputBytes, usedEq, outputBytes, run⟩
      initial.good.live.hz initial.good.live.zst initial.good.live.hs nonnull inputValid mainRun dynEnv.hs dynWindow noOutput
  have sameReturned : returned = nextZ := Option.some.inj (get1.symm.trans next.good.live.hz)
  subst returned
  have allUsed : used = input.length := by
    rw [usedEq, nextAvail, finalHave, UInt32.toNat_zero, Nat.sub_zero]
    exact source.have_eq
  have noBytes : output = [] := by
    have length := header_observed_bytes_length outputBytes
    rw [nextLeft, _tableShape, shape] at length
    change output.length = z.avail_out.toNat - z.avail_out.toNat at length
    rw [Nat.sub_self] at length
    exact List.length_eq_zero_iff.mp length
  have allRemaining : (input.drop blockUsed).drop tableUsed = [] := by
    have count := finalInv.have_eq
    rw [finalHave, UInt32.toNat_zero] at count
    exact List.length_eq_zero_iff.mp count.symm
  have remainingSource : stream regs (input.drop blockUsed) = natBits finalRegs.bits.toNat finalRegs.hold.toNat := by
    rw [← tableSource, allRemaining]
    unfold stream
    simp only [bytesBits, List.flatMap_nil, List.append_nil]
  have entryStream : stream (dispatchRegs z entryS) input = bytesBits input := by
    unfold stream
    simp only [dispatchRegs, entryZero, UInt32.toNat_zero, natBits, List.range_zero, List.map_nil, List.nil_append]
  have wrapper : View readBlock ⟨header, pulled.hold.toNat % 2⟩
      (bytesBits (log.input ++ input)) (natBits finalRegs.bits.toNat finalRegs.hold.toNat) := by
    rw [bytesBits_append]
    intro future
    unfold readBlock
    rw [List.append_assoc, view (bytesBits input ++ future)]
    simp only [List.nil_append]
    dsimp only [Bind.bind, Option.bind]
    rw [← entryStream]
    rw [CumulativeTableBoundary.readBits_append readLast future]
    dsimp only [Bind.bind, Option.bind]
    rw [CumulativeTableBoundary.readBits_append readKind future]
    dsimp only [Bind.bind, Option.bind]
    simp only [ite_true]
    rw [remainingSource]
  refine ⟨nextZ, nextS, next, nextAllocator, ?_, ?_, ?_⟩
  · rw [metadata]; exact dynWindow
  · simp only [credit, empty, noBytes, List.nil_append]
  · refine ⟨?_, ⟨header, pulled.hold.toNat % 2⟩, Nat.mod_lt _ (by decide), ?_, ?_⟩
    · rw [metadata]; rfl
    · rw [metadata]; exact block_last_bit pulled
    · rw [metadata]
      simpa only [credit, allUsed, List.take_length, leaveState] using wrapper

/-- Actual normalized entry plus the literal dynamic-kind source guard. -/
inductive DynamicBlockSource (h : Heap) (r : ZStreamRef) (zs : Nat) : Prop where
  | observed (z : ZStream) (s entryS : InflateState) (pulled : IL)
      (getZ : r.get h = some z) (getS : h.istates zs = some s)
      (normalize : entryS = (if s.mode = TYPE then { s with mode := TYPEDO } else s))
      (pull : runX (NEEDBITS 3) (dispatchRegs z entryS) (setI (syncAlloc h) zs entryS) =
        .ok ((.ok (), pulled), setI (syncAlloc h) zs entryS))
      (dynamic : (pulled.hold >>> 1).toNat % 4 = 2) : DynamicBlockSource h r zs

theorem Meaning.block_dynamic
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog}
    {flush rc : Int32} {input output : List UInt8} {used : Nat}
    (history : InflateDataTrace 15 r h log) (scope : HeaderDataTrace.PlatformScope history)
    (before : Meaning .block h r zs log)
    (observed : DataStep .inflate h after r flush rc input output used)
    (nonempty : 1 ≤ input.length) (short : input.length ≤ 2)
    (flushing : flush ≠ Z_BLOCK ∧ flush ≠ Z_TREES)
    (accepted : ∀ stream0, r.get h = some stream0 → stream0.next_out ≠ .null ∧
      (stream0.next_in = .null → stream0.avail_in = 0))
    (source : DynamicBlockSource h r zs) : Meaning .table after r zs (credit log input output used rc) := by
  obtain ⟨z, s, entryHeap, entryS, pulled, getZ, getS, stateEq, heapEq, _entryGet, pull, finish⟩ :=
    before.block_dynamic_wait history scope observed nonempty short flushing accepted
  cases source with
  | observed sourceZ sourceS sourceEntry sourceRegs observedZ observedS normalize actual dynamic =>
    have sameZ : sourceZ = z := Option.some.inj (observedZ.symm.trans getZ)
    have sameS : sourceS = s := Option.some.inj (observedS.symm.trans getS)
    subst sourceZ sourceS
    have sameEntry : sourceEntry = entryS := normalize.trans stateEq.symm
    rw [sameEntry, ← heapEq, pull] at actual
    cases actual
    exact finish dynamic

#print axioms Meaning.block_dynamic_wait
#print axioms Meaning.block_dynamic
end Zlib.Inflate.Proofs.HeaderPhaseView
