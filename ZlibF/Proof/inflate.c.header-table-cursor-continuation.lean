import ZlibF.Proof.«inflate.c.header-table-packet-prefix»
namespace Zlib.Inflate.Proofs.HeaderPhaseView
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public Zlib.Inffast.Proofs
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.HeaderSourceTrace
set_option autoImplicit false
set_option maxHeartbeats 1600000

def TableCursorContinuation (h : Heap) (r : ZStreamRef) (zs : Nat) (log : DataLog)
    (input : List UInt8) (flush : Int32) (bodyRest : List Bool) : Prop :=
  ∃ (z tableZ : ZStream) (s tableState : InflateState) (tableRegs : IL) (tableHeap : Heap) (sourceUsed : Nat) (record : BlockMeta),
      r.get h = some z ∧ h.istates zs = some s ∧ z.state = some (.inflate zs) ∧
      DefaultOriginState tableHeap r zs tableZ tableState ∧
      DispatchBuffers tableHeap r tableRegs (input.drop sourceUsed) ∧
      sourceUsed ≤ input.length ∧ stream tableRegs (input.drop sourceUsed) = bodyRest ∧ tableRegs.bits.toNat ≤ 39 ∧ tableState.mode = TABLE ∧ tableState.wsize = 0 ∧
      record.last < 2 ∧ tableState.last.toInt = (record.last : Int) ∧
      View readBlock record (bytesBits (log.input ++ input.take sourceUsed)) (natBits tableRegs.bits.toNat tableRegs.hold.toNat) ∧
      tableRegs.put = z.next_out ∧ tableRegs.left = z.avail_out ∧ tableRegs.out_ = tableRegs.left ∧
      tableRegs.next = inputAdvance z.next_in sourceUsed ∧
      tableRegs.have_.toNat + sourceUsed = z.avail_in.toNat ∧
      runX (inflate_run ⟨some r, some (.tab zs), syncBuf h, flush⟩) IL.init (syncAlloc h) =
        runX (xwhile (pure true) (inflate_dispatch ⟨some r, some (.tab zs), syncBuf h, flush⟩)) tableRegs tableHeap


theorem TableCursorContinuation.erase {h : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog}
    {input : List UInt8} {flush : Int32} {bodyRest : List Bool}
    (entry : TableCursorContinuation h r zs log input flush bodyRest) : TableContinuation h r zs log input flush bodyRest := by
  obtain ⟨z, tableZ, s, state, regs, heap, sourceUsed, record, getZ, getS, ptr, origin, buffers, bound, source,
    bits, mode, window, lastBound, last, view, put, left, out, _next, count, main⟩ := entry
  exact ⟨z, tableZ, s, state, regs, heap, sourceUsed, record, getZ, getS, ptr, origin, buffers, bound, source,
    bits, mode, window, lastBound, last, view, put, left, out, count, main⟩

/-- Resume a real public TYPE boundary, normalize to TYPEDO, and continue
into private TABLE on arbitrary current input. A valid independent three
bit prefix supplies the dynamic-kind guard. The remaining real loop may
continue through payload during this same call. -/
theorem Meaning.block_dynamic_cursor_continuation
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog}
    {flush rc : Int32} {input output : List UInt8} {used value : Nat} {bodyRest : List Bool}
    (before : Meaning .block h r zs log)
    (observed : DataStep .inflate h after r flush rc input output used)
    (nonempty : 1 ≤ input.length) (flushing : flush ≠ Z_BLOCK ∧ flush ≠ Z_TREES)
    (accepted : ∀ z, r.get h = some z → z.next_out ≠ .null ∧ (z.next_in = .null → z.avail_in = 0))
    (parse : readBits 3 (bytesBits input) = some (value, bodyRest)) (kind : value / 2 = 2) :
    TableCursorContinuation h r zs log input flush bodyRest := by
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
  obtain ⟨outcome, pulled, blockUsed, pull, _bound, inv, blockSource, bitCount, _shape,
    _max, _same, full, wait, kinds, _cursor⟩ := NEEDBITS_run_cursor input0 3 (by decide)
  have normal : outcome = .ok () := by
    rcases kinds with normal | leave
    · exact normal
    · obtain ⟨all, _none, below⟩ := wait leave
      change pulled.bits.toNat < 3 at below
      change pulled.bits.toNat = entryS.bits.toNat + 8 * blockUsed at bitCount
      rw [entryZero, UInt32.toNat_zero, Nat.zero_add, all] at bitCount
      omega
  have heldRead := readBits_held_stream pulled (input.drop blockUsed) 3 (full normal)
  rw [blockSource] at heldRead
  have entryStream : stream (dispatchRegs z entryS) input = bytesBits input := by
    unfold stream
    simp only [dispatchRegs, entryZero, UInt32.toNat_zero, natBits, List.nil_append]
  rw [entryStream, parse] at heldRead
  have lowWord : value = pulled.hold.toNat % 8 := congrArg Prod.fst (Option.some.inj heldRead)
  have dynamic : (pulled.hold >>> 1).toNat % 4 = 2 := by
    simp only [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    change pulled.hold.toNat / 2 % 4 = 2
    omega
  obtain ⟨outcome2, pulled2, used2, pull2, bound2, inv2, ready⟩ :=
    EntryPath.dynamic_block_origin_entry entryEnv entryOrigin packet (Or.inr entryMode) flushing entryLast entryBits
  rw [pull] at pull2
  cases pull2
  have sameUsed : used2 = blockUsed := by
    have a := inv.have_eq
    have b := inv2.have_eq
    rw [List.length_drop] at a b
    omega
  subst used2
  obtain ⟨blockRun, tableCurrent, tablePacket, readLast, readKind, sourceTail, tableBits⟩ := ready normal dynamic
  let first : IL := { pulled with hold := pulled.hold >>> 1, bits := pulled.bits - 1 }
  let tableRegs : IL := { first with hold := first.hold >>> 2, bits := first.bits - 2 }
  let tableState := { entryS with last := u2i (pulled.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1)), mode := TABLE }
  let tableHeap := setI entryHeap zs tableState
  have tableEnv : Env c tableHeap r zs z tableState := ⟨rfl, rfl, tableCurrent.good.live.hz, tableCurrent.good.live.hs⟩
  have steps : DispatchPrefix c (dispatchRegs z entryS) entryHeap tableRegs tableHeap := .step .begin blockRun
  have continuation := entryRun.trans (loop_prefix_continuation entryEnv entryOrigin packet entryBits tableEnv tableCurrent tablePacket tableBits steps)
  have tablePut : tableRegs.put = z.next_out := by change pulled.put = z.next_out; rw [_shape]; rfl
  have tableLeft : tableRegs.left = z.avail_out := by change pulled.left = z.avail_out; rw [_shape]; rfl
  have tableOut : tableRegs.out_ = tableRegs.left := by change pulled.out_ = pulled.left; rw [_shape]; rfl
  have haveIn : tableRegs.have_.toNat + blockUsed = z.avail_in.toNat := by
    have finalCount := tablePacket.bits.have_eq
    change tableRegs.have_.toNat = (input.drop blockUsed).length at finalCount
    have initialCount : z.avail_in.toNat = input.length := source.have_eq
    rw [List.length_drop] at finalCount
    omega
  have firstWord := ZlibF.Math.CodeLengthPrefix.read_word readLast
  have secondWord := ZlibF.Math.CodeLengthPrefix.read_word readKind
  have bodyWord : bytesBits input =
      (bitsOfNat (pulled.hold.toNat % 2) 1 ++ bitsOfNat 2 2 ++ natBits tableRegs.bits.toNat tableRegs.hold.toNat) ++ bytesBits (input.drop blockUsed) := by
    have word := firstWord.2
    rw [secondWord.2] at word
    change stream (dispatchRegs z entryS) input = bitsOfNat (pulled.hold.toNat % 2) 1 ++ bitsOfNat 2 2 ++ stream tableRegs (input.drop blockUsed) at word
    rw [entryStream] at word
    simpa only [stream, List.append_assoc] using word
  have creditedWord : bytesBits (input.take blockUsed) =
      bitsOfNat (pulled.hold.toNat % 2) 1 ++ bitsOfNat 2 2 ++ natBits tableRegs.bits.toNat tableRegs.hold.toNat := by
    have split := bytesBits_append (input.take blockUsed) (input.drop blockUsed)
    rw [List.take_append_drop, bodyWord] at split
    exact (List.append_inj_left' split rfl).symm
  have formatView : View readBlock ⟨header, pulled.hold.toNat % 2⟩ (bytesBits (log.input ++ input.take blockUsed))
      (natBits tableRegs.bits.toNat tableRegs.hold.toNat) := by
    rw [bytesBits_append]
    intro future
    unfold readBlock
    rw [List.append_assoc, view (bytesBits (input.take blockUsed) ++ future)]
    simp only [List.nil_append]
    dsimp only [Bind.bind, Option.bind]
    rw [creditedWord, List.append_assoc, List.append_assoc]
    have read1 : readBits 1
        (bitsOfNat (pulled.hold.toNat % 2) 1 ++ (bitsOfNat 2 2 ++ (natBits tableRegs.bits.toNat tableRegs.hold.toNat ++ future))) =
          some (pulled.hold.toNat % 2, bitsOfNat 2 2 ++ (natBits tableRegs.bits.toNat tableRegs.hold.toNat ++ future)) := by
      simpa only [Nat.mod_mod, Nat.sub_self, bitsOfNat_zero, List.nil_append] using
        readBits_bitsOfNat 1 1 (pulled.hold.toNat % 2) (bitsOfNat 2 2 ++ (natBits tableRegs.bits.toNat tableRegs.hold.toNat ++ future)) (Nat.le_refl _)
    rw [read1]
    dsimp only
    have read2 : readBits 2 (bitsOfNat 2 2 ++ (natBits tableRegs.bits.toNat tableRegs.hold.toNat ++ future)) =
        some (2, natBits tableRegs.bits.toNat tableRegs.hold.toNat ++ future) := by
      simpa only [Nat.sub_self, bitsOfNat_zero, List.nil_append] using
        readBits_bitsOfNat 2 2 2 (natBits tableRegs.bits.toNat tableRegs.hold.toNat ++ future) (Nat.le_refl _)
    rw [read2]
    rfl
  have remaining : stream tableRegs (input.drop blockUsed) = bodyRest := by
    have word := ZlibF.Math.CodeLengthPrefix.read_word parse
    have dropRead : (bytesBits input).drop 3 = bodyRest := by
      rw [word.2, List.drop_append_of_le_length (by rw [bitsOfNat_length]; exact Nat.le_refl _)]
      rw [List.drop_eq_nil_of_le (by rw [bitsOfNat_length]; exact Nat.le_refl _)]
      rfl
    change stream tableRegs (input.drop blockUsed) = (stream (dispatchRegs z entryS) input).drop 3 at sourceTail
    rwa [entryStream, dropRead] at sourceTail
  exact ⟨z, z, s, tableState, tableRegs, tableHeap, blockUsed, ⟨header, pulled.hold.toNat % 2⟩,
    initial.good.live.hz, initial.good.live.hs, initial.good.live.zst, tableCurrent, tablePacket, _bound, remaining, tableBits, rfl, entryWindow,
    Nat.mod_lt _ (by decide), block_last_bit pulled, formatView, tablePut, tableLeft, tableOut, (by change pulled.next = inputAdvance z.next_in blockUsed; exact _cursor), haveIn, continuation⟩

theorem Epoch.head_dynamic_cursor_entry
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog} {history : InflateDataTrace 15 r h log}
    {flush rc : Int32} {input output : List UInt8} {used value : Nat} {cmf flg : UInt8} {bodyBytes : List UInt8} {bodyRest : List Bool}
    (selected : Epoch r zs .head history)
    (observed : DataStep .inflate h after r flush rc input output used)
    (flushing : flush ≠ Z_BLOCK ∧ flush ≠ Z_TREES)
    (accepted : ∀ z, r.get h = some z → z.next_out ≠ .null ∧ (z.next_in = .null → z.avail_in = 0))
    (prefixBytes : log.input ++ input = [cmf, flg] ++ bodyBytes)
    (valid : Zlib.HeaderOK cmf flg) (plain : flg.toNat / 32 % 2 = 0)
    (parseBlock : readBits 3 (bytesBits bodyBytes) = some (value, bodyRest)) (dynamic : value / 2 = 2) :
    TableCursorContinuation h r zs log input flush bodyRest := by
  have before := selected.checked.2
  have before0 := before
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
  have enough : 2 ≤ log.input.length + input.length := by
    have length := congrArg List.length prefixBytes
    simp only [List.length_append, List.length_cons, List.length_nil] at length
    omega
  obtain ⟨pulled, headerUsed, pull, bound, inv, usedCount, read, finish⟩ :=
    EntryPath.HeadHistory.complete_head_type_origin_entry env allocated packet mode (Or.inr wrap) count word prefixBound enough
  have read0 := read
  have guardSource := before0.plain_header_source
    ⟨z, returned, getZ, get1, buffers, activeHeader, inputBytes, usedEq, outputBytes, actual⟩ prefixBytes valid plain
  have guards : headHeaderRejected s pulled = false ∧ headMethodRejected pulled = false ∧
      (headWindowRegs pulled).len.toNat ≤ 15 ∧ headDefaultMode pulled = TYPE := by
    cases guardSource with
    | observed sourceZ sourceS sourceRegs observedZ observedS sourcePull header method windowSize noDict =>
      have sameZ : sourceZ = z := Option.some.inj (observedZ.symm.trans getZ)
      have sameS : sourceS = s := Option.some.inj (observedS.symm.trans getS)
      subst sourceZ sourceS
      rw [pull] at sourcePull
      cases sourcePull
      exact ⟨header, method, windowSize, noDict⟩
  obtain ⟨headRun, headCurrent, headPacket, headMode, headLast, _headBits⟩ := finish guards.1 guards.2.1 guards.2.2.1 guards.2.2.2
  let headRegs : IL := { headWindowRegs pulled with hold := 0, bits := 0 }
  let headState := headDefaultState s pulled
  let headHeap := setI (r.put (syncAlloc h) { z with adler := 1 }) zs headState
  have headEnv : Env c headHeap r zs { z with adler := 1 } headState := ⟨rfl, rfl, headCurrent.good.live.hz, headCurrent.good.live.hs⟩
  have readHeader := read_wrapper_bytes cmf flg bodyBytes
  rw [prefixBytes, readHeader] at read
  have bodySource : bytesBits (input.drop headerUsed) = bytesBits bodyBytes := (congrArg Prod.snd (Option.some.inj read)).symm
  have headStream : stream headRegs (input.drop headerUsed) = bytesBits bodyBytes := by
    unfold stream
    simp only [headRegs, UInt32.toNat_zero, natBits, List.nil_append]
    exact bodySource
  obtain ⟨outcome, blockPulled, blockUsed, blockPull, blockBound, blockInv, blockReady⟩ :=
    EntryPath.dynamic_block_origin_entry headEnv headCurrent headPacket (Or.inl headMode) flushing (headLast.trans last) (by change (0 : UInt32).toNat ≤ 39; decide)
  obtain ⟨outcome0, blockPulled0, used0, pull0, bound0, inv0, blockSource, blockCount, blockShape,
    _blockMax, _blockSame, full, wait, kinds, blockCursor⟩ := NEEDBITS_run_cursor headPacket.bits 3 (by decide)
  rw [blockPull] at pull0
  cases pull0
  have normal : outcome = .ok () := by
    rcases kinds with normal | leave
    · exact normal
    · obtain ⟨all, _none, below⟩ := wait leave
      have enoughParse := ZlibF.Math.CodeLengthPrefix.read_word parseBlock
      have lengths := congrArg List.length enoughParse.2
      rw [← headStream] at lengths
      simp only [stream, List.length_append, natBits_length, headRegs, UInt32.toNat_zero, Nat.zero_add, bytesBits_length, bitsOfNat_length, List.length_drop] at lengths
      change blockPulled.bits.toNat = 0 + 8 * used0 at blockCount
      change blockPulled.bits.toNat < 3 at below
      rw [all, List.length_drop] at blockCount
      omega
  have actualRead := readBits_held_stream blockPulled ((input.drop headerUsed).drop used0) 3 (full normal)
  rw [blockSource, headStream, parseBlock] at actualRead
  have sourceWord : value = blockPulled.hold.toNat % 8 := congrArg Prod.fst (Option.some.inj actualRead)
  have dynamicGuard : (blockPulled.hold >>> 1).toNat % 4 = 2 := by
    simp only [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    change blockPulled.hold.toNat / 2 % 4 = 2
    omega
  obtain ⟨blockRun, tableCurrent, tablePacket, readLast, readKind, _sourceTail, tableBits⟩ := blockReady normal dynamicGuard
  let first : IL := { blockPulled with hold := blockPulled.hold >>> 1, bits := blockPulled.bits - 1 }
  let tableRegs : IL := { first with hold := first.hold >>> 2, bits := first.bits - 2 }
  let tableState := { headState with last := u2i (blockPulled.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1)), mode := TABLE }
  let tableHeap := setI headHeap zs tableState
  have tableEnv : Env c tableHeap r zs { z with adler := 1 } tableState := ⟨rfl, rfl, tableCurrent.good.live.hz, tableCurrent.good.live.hs⟩
  have blockSameUsed : used0 = blockUsed := by
    have left := blockInv.have_eq
    have right := inv0.have_eq
    rw [List.length_drop] at left right
    omega
  subst used0
  have sourceBound : headerUsed + blockUsed ≤ input.length := by rw [List.length_drop] at blockBound; omega
  have actualPrefix : DispatchPrefix c (dispatchRegs z s) (syncAlloc h) tableRegs tableHeap :=
    .step (.step .begin headRun) blockRun
  have entry : runX (inflate_run c) IL.init (syncAlloc h) = runX (xwhile (pure true) (inflate_dispatch c)) (dispatchRegs z s) (syncAlloc h) := by
    unfold inflate_run
    rw [runX_bind, runX_rdS env]
    have noType : s.mode ≠ TYPE := by rw [mode]; decide
    simp only [noType, beq_iff_eq, ite_false, runX_bind]
    rw [LOAD_run env]
    simp only []
    rw [runX_modify]
    rfl
  have continuation := entry.trans (loop_prefix_continuation env allocated packet (by change s.bits.toNat ≤ 39; omega) tableEnv tableCurrent tablePacket tableBits actualPrefix)
  obtain ⟨_headPut, headLeft, headOut⟩ := CumulativeTableBoundary.needbits_output_fields input0 (by decide : (16 : UInt32).toNat ≤ 49) pull
  have tablePut : tableRegs.put = z.next_out := by
    change blockPulled.put = z.next_out
    rw [blockShape]
    exact _headPut
  have tableLeft : tableRegs.left = z.avail_out := by
    change blockPulled.left = z.avail_out
    rw [blockShape]
    exact headLeft
  have tableOut : tableRegs.out_ = tableRegs.left := by
    change blockPulled.out_ = blockPulled.left
    rw [blockShape]
    change pulled.out_ = pulled.left
    rw [headOut, headLeft]
    rfl
  have cursor : tableRegs.have_.toNat + (headerUsed + blockUsed) = z.avail_in.toNat := by
    have initialCount := source.have_eq
    have tableCount := tablePacket.bits.have_eq
    rw [List.length_drop, List.length_drop] at tableCount
    change tableRegs.have_.toNat = _ at tableCount
    change z.avail_in.toNat = input.length at initialCount
    omega
  have headView : View (readBits 16) (pulled.hold.toNat % 2 ^ 16)
      (bytesBits (log.input ++ input.take headerUsed)) [] := by
    apply View.readBits_prefix (remaining := bytesBits (input.drop headerUsed))
    have split : bytesBits (log.input ++ input) = bytesBits (log.input ++ input.take headerUsed) ++ bytesBits (input.drop headerUsed) := by
      rw [← bytesBits_append, List.append_assoc, List.take_append_drop]
    rw [← split]
    exact read0
  have firstWord := ZlibF.Math.CodeLengthPrefix.read_word readLast
  have secondWord := ZlibF.Math.CodeLengthPrefix.read_word readKind
  have bodyWord : bytesBits (input.drop headerUsed) =
      (bitsOfNat (blockPulled.hold.toNat % 2) 1 ++ bitsOfNat 2 2 ++ natBits tableRegs.bits.toNat tableRegs.hold.toNat) ++
        bytesBits ((input.drop headerUsed).drop blockUsed) := by
    have sourceWord := firstWord.2
    rw [secondWord.2] at sourceWord
    change stream headRegs (input.drop headerUsed) =
      bitsOfNat (blockPulled.hold.toNat % 2) 1 ++ bitsOfNat 2 2 ++ stream tableRegs ((input.drop headerUsed).drop blockUsed) at sourceWord
    change natBits 0 0 ++ bytesBits (input.drop headerUsed) = _ at sourceWord
    simpa only [natBits, List.nil_append, stream, List.append_assoc] using sourceWord
  have creditedWord : bytesBits ((input.drop headerUsed).take blockUsed) =
      bitsOfNat (blockPulled.hold.toNat % 2) 1 ++ bitsOfNat 2 2 ++ natBits tableRegs.bits.toNat tableRegs.hold.toNat := by
    have split := bytesBits_append ((input.drop headerUsed).take blockUsed) ((input.drop headerUsed).drop blockUsed)
    rw [List.take_append_drop, bodyWord] at split
    exact (List.append_inj_left' split rfl).symm
  have formatView : View readBlock ⟨pulled.hold.toNat % 2 ^ 16, blockPulled.hold.toNat % 2⟩
      (bytesBits (log.input ++ input.take (headerUsed + blockUsed))) (natBits tableRegs.bits.toNat tableRegs.hold.toNat) := by
    rw [List.take_add, ← List.append_assoc, bytesBits_append]
    intro future
    unfold readBlock
    rw [List.append_assoc, headView (bytesBits ((input.drop headerUsed).take blockUsed) ++ future)]
    simp only [List.nil_append]
    dsimp only [Bind.bind, Option.bind]
    rw [creditedWord, List.append_assoc, List.append_assoc]
    have readFirst := readBits_bitsOfNat 1 1 (blockPulled.hold.toNat % 2)
      (bitsOfNat 2 2 ++ natBits tableRegs.bits.toNat tableRegs.hold.toNat ++ future) (Nat.le_refl _)
    have firstRead : readBits 1
        (bitsOfNat (blockPulled.hold.toNat % 2) 1 ++ (bitsOfNat 2 2 ++ (natBits tableRegs.bits.toNat tableRegs.hold.toNat ++ future))) =
          some (blockPulled.hold.toNat % 2, bitsOfNat 2 2 ++ (natBits tableRegs.bits.toNat tableRegs.hold.toNat ++ future)) := by
      simpa only [Nat.mod_mod, Nat.sub_self, bitsOfNat_zero, List.nil_append, List.append_assoc] using readFirst
    rw [firstRead]
    dsimp only
    have secondRead : readBits 2 (bitsOfNat 2 2 ++ (natBits tableRegs.bits.toNat tableRegs.hold.toNat ++ future)) =
        some (2, natBits tableRegs.bits.toNat tableRegs.hold.toNat ++ future) := by
      simpa only [Nat.sub_self, bitsOfNat_zero, List.nil_append] using
        readBits_bitsOfNat 2 2 2 (natBits tableRegs.bits.toNat tableRegs.hold.toNat ++ future) (Nat.le_refl _)
    rw [secondRead]
    rfl
  have remaining : stream tableRegs (input.drop (headerUsed + blockUsed)) = bodyRest := by
    have exactRead := ZlibF.Math.CodeLengthPrefix.read_word parseBlock
    have dropRead : (bytesBits bodyBytes).drop 3 = bodyRest := by
      rw [exactRead.2, List.drop_append_of_le_length (by rw [bitsOfNat_length]; exact Nat.le_refl _)]
      rw [List.drop_eq_nil_of_le (by rw [bitsOfNat_length]; exact Nat.le_refl _)]
      rfl
    change stream tableRegs ((input.drop headerUsed).drop blockUsed) = (stream headRegs (input.drop headerUsed)).drop 3 at _sourceTail
    rw [headStream, dropRead, List.drop_drop] at _sourceTail
    exact _sourceTail
  have headCursor : pulled.next = inputAdvance z.next_in headerUsed := by
    obtain ⟨outcome0, pulled0, used0, pull0, _bound0, inv0, _source0, _count0, _shape0, _upper0, _same0, _full0, _wait0, _kinds0, cursor0⟩ := NEEDBITS_run_cursor input0 16 (by decide)
    rw [pull] at pull0
    cases pull0
    have same : used0 = headerUsed := by
      have a := inv0.have_eq
      have b := inv.have_eq
      simp only [List.length_drop] at a b
      omega
    subst used0
    exact cursor0
  have tableNext : tableRegs.next = inputAdvance z.next_in (headerUsed + blockUsed) := by
    change blockPulled.next = _
    rw [blockCursor]
    change inputAdvance pulled.next blockUsed = _
    rw [headCursor, inputAdvance_add]
  refine ⟨z, {z with adler := 1}, s, tableState, tableRegs, tableHeap, headerUsed + blockUsed,
    ⟨pulled.hold.toNat % 2 ^ 16, blockPulled.hold.toNat % 2⟩, getZ, getS, initial.good.live.zst, tableCurrent, ?_, sourceBound, remaining, tableBits, rfl, ?_, Nat.mod_lt _ (by decide), ?_, formatView, tablePut, tableLeft, tableOut, tableNext, cursor, continuation⟩
  · simpa only [List.drop_drop] using tablePacket
  · change headState.wsize = 0
    exact window
  · exact block_last_bit blockPulled

#print axioms TableCursorContinuation.erase
#print axioms Meaning.block_dynamic_cursor_continuation
#print axioms Epoch.head_dynamic_cursor_entry
end Zlib.Inflate.Proofs.HeaderPhaseView
