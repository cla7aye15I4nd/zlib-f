import ZlibF.Proof.«inflate.c.header-loop-continuation»
namespace Zlib.Inflate.Proofs.HeaderPhaseView
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public Zlib.Inffast.Proofs
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.HeaderSourceTrace
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- Actual allocated same-call TABLE entry and its unchanged remaining
loop. Stored hold/bits are not substituted for the live local registers. -/
def SameCallTableEntry (h : Heap) (r : ZStreamRef) (zs : Nat) (log : DataLog)
    (input : List UInt8) (flush : Int32) (bodyRest : List Bool) : Prop :=
  ∃ (z : ZStream) (s tableState : InflateState) (tableRegs : IL) (tableHeap : Heap) (sourceUsed : Nat) (record : BlockMeta),
      r.get h = some z ∧ h.istates zs = some s ∧ z.state = some (.inflate zs) ∧
      DefaultOriginState tableHeap r zs { z with adler := 1 } tableState ∧
      DispatchBuffers tableHeap r tableRegs (input.drop sourceUsed) ∧
      sourceUsed ≤ input.length ∧ stream tableRegs (input.drop sourceUsed) = bodyRest ∧ tableRegs.bits.toNat ≤ 39 ∧ tableState.mode = TABLE ∧ tableState.wsize = 0 ∧
      record.last < 2 ∧ tableState.last.toInt = (record.last : Int) ∧
      View readBlock record (bytesBits (log.input ++ input.take sourceUsed)) (natBits tableRegs.bits.toNat tableRegs.hold.toNat) ∧
      tableRegs.put = z.next_out ∧ tableRegs.left = z.avail_out ∧ tableRegs.out_ = tableRegs.left ∧
      tableRegs.have_.toNat + sourceUsed = z.avail_in.toNat ∧
      DispatchPrefix ⟨some r, some (.tab zs), syncBuf h, flush⟩ (dispatchRegs z s) (syncAlloc h) tableRegs tableHeap ∧
      runX (inflate_run ⟨some r, some (.tab zs), syncBuf h, flush⟩) IL.init (syncAlloc h) =
        runX (xwhile (pure true) (inflate_dispatch ⟨some r, some (.tab zs), syncBuf h, flush⟩)) tableRegs tableHeap

/-- An independent first dynamic block header enters the real private
TABLE loop in the same ordinary public call after cumulative HEAD input.
The remaining loop is unchanged and may wait, build tables or emit payload;
there is no caller-output or final-mode restriction and no buffer-size cap. -/
theorem Epoch.head_dynamic_loop_entry
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog} {history : InflateDataTrace 15 r h log}
    {flush rc : Int32} {input output : List UInt8} {used value : Nat} {cmf flg : UInt8} {bodyBytes : List UInt8} {bodyRest : List Bool}
    (selected : Epoch r zs .head history)
    (observed : DataStep .inflate h after r flush rc input output used)
    (flushing : flush ≠ Z_BLOCK ∧ flush ≠ Z_TREES)
    (accepted : ∀ z, r.get h = some z → z.next_out ≠ .null ∧ (z.next_in = .null → z.avail_in = 0))
    (prefixBytes : log.input ++ input = [cmf, flg] ++ bodyBytes)
    (valid : Zlib.HeaderOK cmf flg) (plain : flg.toNat / 32 % 2 = 0)
    (parseBlock : readBits 3 (bytesBits bodyBytes) = some (value, bodyRest)) (dynamic : value / 2 = 2) :
    SameCallTableEntry h r zs log input flush bodyRest := by
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
  refine ⟨z, s, tableState, tableRegs, tableHeap, headerUsed + blockUsed,
    ⟨pulled.hold.toNat % 2 ^ 16, blockPulled.hold.toNat % 2⟩, getZ, getS, initial.good.live.zst, tableCurrent, ?_, sourceBound, remaining, tableBits, rfl, ?_, Nat.mod_lt _ (by decide), ?_, formatView, tablePut, tableLeft, tableOut, cursor, actualPrefix, continuation⟩
  · simpa only [List.drop_drop] using tablePacket
  · change headState.wsize = 0
    exact window
  · exact block_last_bit blockPulled

#print axioms Epoch.head_dynamic_loop_entry
end Zlib.Inflate.Proofs.HeaderPhaseView
