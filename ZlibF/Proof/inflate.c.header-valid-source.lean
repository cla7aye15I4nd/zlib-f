import ZlibF.Proof.«inflate.c.header-epoch»
namespace Zlib.Inflate.Proofs.HeaderPhaseView
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public Zlib.Inffast.Proofs
open Zlib.Inflate.Proofs
set_option autoImplicit false

theorem read_wrapper_bytes (cmf flg : UInt8) (rest : List UInt8) :
    readBits 16 (bytesBits ([cmf, flg] ++ rest)) = some (cmf.toNat + 256 * flg.toNat, bytesBits rest) := by
  have word : bytesBits [cmf, flg] = natBits 16 (cmf.toNat + 256 * flg.toNat) := by
    have append := natBits_pull 8 cmf.toNat flg.toNat cmf.toNat_lt flg.toNat_lt
    simpa only [bytesBits_cons, bytesBits_nil, List.append_nil, Nat.mul_comm] using append.symm
  rw [bytesBits_append, word]
  have small : cmf.toNat + 256 * flg.toNat < 2 ^ 16 := by have a := cmf.toNat_lt; have b := flg.toNat_lt; omega
  simpa only [natBits_testBit, bitsOfNat, Nat.mod_eq_of_lt small, Nat.sub_self, bitsOfNat_zero, List.range_zero, List.map_nil, List.nil_append] using
    readBits_bitsOfNat 16 16 (cmf.toNat + 256 * flg.toNat) (bytesBits rest) (Nat.le_refl _)

/-- Independent RFC1950 validity of the real cumulative byte prefix
produces actual HEAD guard observations, including partial prior calls. -/
theorem Meaning.plain_header_source {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog}
    {flush rc : Int32} {input output : List UInt8} {used : Nat} {cmf flg : UInt8} {rest : List UInt8}
    (before : Meaning .head h r zs log)
    (actual : DataStep .inflate h after r flush rc input output used)
    (prefixBytes : log.input ++ input = [cmf, flg] ++ rest)
    (valid : Zlib.HeaderOK cmf flg) (plain : flg.toNat / 32 % 2 = 0) : PlainHeadSource h r zs := by
  obtain ⟨z, s, initial, _allocator, _window, _empty, _mode, _last, wrap, _below, count, word, bound⟩ := before
  obtain ⟨z0, _returned, get0, _get1, _buffers, _active, bytes, _usedEq, _output, _run⟩ := actual
  have sameZ : z0 = z := Option.some.inj (get0.symm.trans initial.good.live.hz)
  subst z0
  have source := header_input_view_of_bytes (s := s) bytes initial.held
  have input0 : BitInv (syncAlloc h) (dispatchRegs z s) input := by
    refine ⟨source.have_eq, ?_, source.hold_lt⟩
    rcases source.next with none | ⟨ref, array, off, pointer, get, inside, values⟩
    · exact Or.inl none
    · exact Or.inr ⟨ref, array, off, pointer, (byte_view_syncAlloc initial.good.fresh get).1, inside, values⟩
  have enough : 2 ≤ log.input.length + input.length := by
    have lengths := congrArg List.length prefixBytes
    simp only [List.length_append, List.length_cons, List.length_nil] at lengths
    omega
  obtain ⟨pulled, _readUsed, pull, _usedBound, inv, bits16, _count, read⟩ :=
    EntryPath.HeadHistory.head_complete_bits input0 count word bound enough
  have actualRead := read_wrapper_bytes cmf flg rest
  rw [prefixBytes, actualRead] at read
  have value := congrArg Prod.fst (Option.some.inj read)
  have holdBound := inv.hold_lt
  rw [bits16] at holdBound
  have exactWord : pulled.hold.toNat = cmf.toNat + 256 * flg.toNat := by
    rw [Nat.mod_eq_of_lt holdBound] at value
    exact value.symm
  obtain ⟨header, method, window, plainMode⟩ := HeaderSource.valid_plain_guards valid plain wrap exactWord
  exact .observed z s pulled initial.good.live.hz initial.good.live.hs pull header method window plainMode

/-- Produce the original-trace phase constructor from independent validity
of its observed bytes; initial J and the desired block phase are derived. -/
theorem Epoch.pause_valid {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog}
    {prior : InflateDataTrace 15 r h log} {flush rc : Int32} {input output : List UInt8} {used : Nat}
    {actual : DataStep .inflate h after r flush rc input output used} {cmf flg : UInt8} {rest : List UInt8}
    (selected : Epoch r zs .head prior) (pause : flush = Z_BLOCK ∨ flush = Z_TREES)
    (accepted : ∀ z, r.get h = some z → z.next_out ≠ .null ∧ (z.next_in = .null → z.avail_in = 0))
    (prefixBytes : log.input ++ input = [cmf, flg] ++ rest)
    (valid : Zlib.HeaderOK cmf flg) (plain : flg.toNat / 32 % 2 = 0) : Epoch r zs .block (.step prior actual) := by
  have enough : 2 ≤ log.input.length + input.length := by
    have lengths := congrArg List.length prefixBytes
    simp only [List.length_append, List.length_cons, List.length_nil] at lengths
    omega
  exact .pause (actual := actual) selected pause enough accepted (selected.checked.2.plain_header_source actual prefixBytes valid plain)

/-- An independent three-bit parse produces the literal actual dynamic
kind observation at the normalized public entry. -/
theorem Meaning.dynamic_header_source {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog}
    {flush rc : Int32} {input output : List UInt8} {used value : Nat} {rest : List Bool}
    (before : Meaning .block h r zs log)
    (observed : DataStep .inflate h after r flush rc input output used)
    (nonempty : 1 ≤ input.length)
    (accepted : ∀ z, r.get h = some z → z.next_out ≠ .null ∧ (z.next_in = .null → z.avail_in = 0))
    (parse : readBits 3 (bytesBits input) = some (value, rest)) (kind : value / 2 = 2) :
    DynamicBlockSource h r zs := by
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
  obtain ⟨outcome, pulled, readUsed, pull, _bound, inv, sameSource, bitCount, _shape,
    _max, _same, full, wait, kinds, _cursor⟩ := NEEDBITS_run_cursor input0 3 (by decide)
  have normal : outcome = .ok () := by
    rcases kinds with normal | leave
    · exact normal
    · obtain ⟨all, _none, below⟩ := wait leave
      change pulled.bits.toNat < 3 at below
      change pulled.bits.toNat = entryS.bits.toNat + 8 * readUsed at bitCount
      rw [entryZero, UInt32.toNat_zero, Nat.zero_add, all] at bitCount
      omega
  have heldRead := readBits_held_stream pulled (input.drop readUsed) 3 (full normal)
  rw [sameSource] at heldRead
  have entryStream : stream (dispatchRegs z entryS) input = bytesBits input := by
    unfold stream
    simp only [dispatchRegs, entryZero, UInt32.toNat_zero, natBits, List.nil_append]
  rw [entryStream, parse] at heldRead
  have lowWord : value = pulled.hold.toNat % 8 := congrArg Prod.fst (Option.some.inj heldRead)
  have dynamic : (pulled.hold >>> 1).toNat % 4 = 2 := by
    simp only [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    change pulled.hold.toNat / 2 % 4 = 2
    omega
  refine .observed z s entryS pulled initial.good.live.hz initial.good.live.hs stateEq ?_ dynamic
  rw [← heapEq]
  simpa only [normal] using pull

/-- Independent bit validity produces the original DataStep constructor;
no dynamic-state postcondition or initialized representation is an input. -/
theorem Epoch.dynamic_valid {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog}
    {prior : InflateDataTrace 15 r h log} {flush rc : Int32} {input output : List UInt8} {used value : Nat} {rest : List Bool}
    {actual : DataStep .inflate h after r flush rc input output used}
    (selected : Epoch r zs .block prior) (nonempty : 1 ≤ input.length) (short : input.length ≤ 2)
    (flushing : flush ≠ Z_BLOCK ∧ flush ≠ Z_TREES)
    (accepted : ∀ z, r.get h = some z → z.next_out ≠ .null ∧ (z.next_in = .null → z.avail_in = 0))
    (parse : readBits 3 (bytesBits input) = some (value, rest)) (kind : value / 2 = 2) :
    Epoch r zs .table (.step prior actual) := by
  exact .dynamic (actual := actual) selected nonempty short flushing accepted
    (selected.checked.2.dynamic_header_source actual nonempty accepted parse kind)

#print axioms read_wrapper_bytes
#print axioms Meaning.plain_header_source
#print axioms Epoch.pause_valid
#print axioms Meaning.dynamic_header_source
#print axioms Epoch.dynamic_valid
end Zlib.Inflate.Proofs.HeaderPhaseView
