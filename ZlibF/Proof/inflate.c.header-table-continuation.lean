import ZlibF.Proof.«inflate.c.header-dynamic-future-entry»
namespace Zlib.Inflate.Proofs.HeaderPhaseView
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public Zlib.Inffast.Proofs
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.HeaderSourceTrace
set_option autoImplicit false
set_option maxHeartbeats 800000

def TableContinuation (h : Heap) (r : ZStreamRef) (zs : Nat) (log : DataLog)
    (input : List UInt8) (flush : Int32) (bodyRest : List Bool) : Prop :=
  ∃ (z tableZ : ZStream) (s tableState : InflateState) (tableRegs : IL) (tableHeap : Heap) (sourceUsed : Nat) (record : BlockMeta),
      r.get h = some z ∧ h.istates zs = some s ∧ z.state = some (.inflate zs) ∧
      DefaultOriginState tableHeap r zs tableZ tableState ∧
      DispatchBuffers tableHeap r tableRegs (input.drop sourceUsed) ∧
      sourceUsed ≤ input.length ∧ stream tableRegs (input.drop sourceUsed) = bodyRest ∧ tableRegs.bits.toNat ≤ 39 ∧ tableState.mode = TABLE ∧ tableState.wsize = 0 ∧
      record.last < 2 ∧ tableState.last.toInt = (record.last : Int) ∧
      View readBlock record (bytesBits (log.input ++ input.take sourceUsed)) (natBits tableRegs.bits.toNat tableRegs.hold.toNat) ∧
      tableRegs.put = z.next_out ∧ tableRegs.left = z.avail_out ∧ tableRegs.out_ = tableRegs.left ∧
      tableRegs.have_.toNat + sourceUsed = z.avail_in.toNat ∧
      runX (inflate_run ⟨some r, some (.tab zs), syncBuf h, flush⟩) IL.init (syncAlloc h) =
        runX (xwhile (pure true) (inflate_dispatch ⟨some r, some (.tab zs), syncBuf h, flush⟩)) tableRegs tableHeap


theorem SameCallTableEntry.to_continuation {h : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog}
    {input : List UInt8} {flush : Int32} {bodyRest : List Bool} (entry : SameCallTableEntry h r zs log input flush bodyRest) :
    TableContinuation h r zs log input flush bodyRest := by
  obtain ⟨z, s, t, l, heap, sourceUsed, record, getZ, getS, pointer, current, packet, bound, source, bits, mode, window,
    lastBound, last, view, put, left, out, haveIn, _trace, run⟩ := entry
  exact ⟨z, { z with adler := 1 }, s, t, l, heap, sourceUsed, record, getZ, getS, pointer, current, packet, bound, source, bits, mode, window,
    lastBound, last, view, put, left, out, haveIn, run⟩

/-- Resume a real public TYPE boundary, normalize to TYPEDO, and continue
into private TABLE on arbitrary current input. A valid independent three
bit prefix supplies the dynamic-kind guard. The remaining real loop may
continue through payload during this same call. -/
theorem Meaning.block_dynamic_continuation
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog}
    {flush rc : Int32} {input output : List UInt8} {used value : Nat} {bodyRest : List Bool}
    (before : Meaning .block h r zs log)
    (observed : DataStep .inflate h after r flush rc input output used)
    (nonempty : 1 ≤ input.length) (flushing : flush ≠ Z_BLOCK ∧ flush ≠ Z_TREES)
    (accepted : ∀ z, r.get h = some z → z.next_out ≠ .null ∧ (z.next_in = .null → z.avail_in = 0))
    (parse : readBits 3 (bytesBits input) = some (value, bodyRest)) (kind : value / 2 = 2) :
    TableContinuation h r zs log input flush bodyRest := by
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
    Nat.mod_lt _ (by decide), block_last_bit pulled, formatView, tablePut, tableLeft, tableOut, haveIn, continuation⟩

#print axioms SameCallTableEntry.to_continuation
#print axioms Meaning.block_dynamic_continuation
end Zlib.Inflate.Proofs.HeaderPhaseView
