import ZlibF.Proof.«inflate.c.header-table-count-source»
namespace Zlib.Inflate.Proofs.HeaderPhaseView
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.CumulativeBoundary Zlib.Inflate.Proofs.CumulativeTableBoundary
set_option autoImplicit false

theorem lenlens_waiting_source {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState} {l : IL}
    {input : List UInt8} {received : List Bool}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s) (wf : s.WellFormed)
    (ncode : s.ncode.toNat ≤ 19) (haveBound : s.«have».toNat ≤ s.ncode.toNat)
    (B : BitInv h l input) (progress : LenlensProgress s l.hold l.bits received)
    (short : (stream l input).length < 3 * (s.ncode.toNat - s.«have».toNat)) :
    ∃ (regs : IL) (count readUsed : Nat),
      runX (inflate_LENLENS c) l h =
        .ok ((.error Ex.leave, regs), setI h zs (llSt s (stream l input) count)) ∧
      readUsed ≤ input.length ∧ BitInv h regs (input.drop readUsed) ∧ TcRegShape l regs ∧
      LenlensProgress (llSt s (stream l input) count) regs.hold regs.bits
        (received ++ bytesBits (input.take readUsed)) := by
  obtain ⟨outcome, regs, readUsed, count, countEq, readRun, readBound, _readB, nextProgress⟩ :=
    ll1_header_progress hc hs wf.1 ncode haveBound B progress
  obtain ⟨outcome0, regs0, used0, readRun0, bound0, inv0, _remaining, regShape, wait, _complete⟩ :=
    ll1_run hc hs wf.1 ncode haveBound B
  rw [← countEq, readRun] at readRun0
  cases readRun0
  have shortCount : count < s.ncode.toNat - s.«have».toNat := by rw [countEq]; omega
  obtain ⟨leave, _haveZero, _allUsed, _below⟩ := wait (by rw [← countEq]; exact shortCount)
  subst outcome
  have sameUsed : used0 = readUsed := by
    have a := inv0.have_eq
    have b := _readB.have_eq
    simp only [List.length_drop] at a b
    omega
  have finalB : BitInv h regs (input.drop readUsed) := by rw [← sameUsed]; exact inv0
  refine ⟨regs, count, readUsed, ?_, readBound, finalB, regShape, nextProgress⟩
  rw [inflate_LENLENS_eq, runX_bind, readRun]

/-- Technical composition of an actual private LENLENS source cut with
the real public DataStep. All private premises are produced by the TABLE
source theorem in the public wrapper below. -/
private theorem lens_prefix_wait_public
    {h after privateHeap : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog}
    {z : ZStream} {s t : InflateState} {l : IL} {headerUsed : Nat} {record : CountMeta}
    {flush rc : Int32} {input output : List UInt8} {used : Nat}
    (initial : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (observed : DataStep .inflate h after r flush rc input output used)
    (nonnull : z.next_out ≠ .null) (inputValid : z.next_in = .null → z.avail_in = 0)
    (noType : s.mode ≠ TYPE) (empty : log.output = [])
    (prefixBound : headerUsed ≤ input.length)
    (privateGet : privateHeap.istates zs = some t) (wf : t.WellFormed)
    (mode : t.mode = LENLENS) (window : t.wsize = 0)
    (ncode : t.ncode.toNat ≤ 19) (haveBound : t.«have».toNat ≤ t.ncode.toNat)
    (B : BitInv privateHeap l (input.drop headerUsed))
    (progress : LenlensProgress t l.hold l.bits (natBits l.bits.toNat l.hold.toNat))
    (lastBound : record.last < 2) (last : t.last.toInt = (record.last : Int))
    (litCount : t.nlen.toNat = record.lit + 257) (distCount : t.ndist.toNat = record.dist + 1)
    (codeCount : t.ncode.toNat = record.code + 4)
    (view : View readCounts record (bytesBits (log.input ++ input.take headerUsed)) (natBits l.bits.toNat l.hold.toNat))
    (put : l.put = z.next_out) (left : l.left = z.avail_out) (out : l.out_ = l.left)
    (cut : runX (inflate_dispatch ⟨some r, some (.tab zs), syncBuf h, flush⟩) (dispatchRegs z s) (syncAlloc h) =
      runX (inflate_LENLENS ⟨some r, some (.tab zs), syncBuf h, flush⟩) l privateHeap)
    (short : (stream l (input.drop headerUsed)).length < 3 * (t.ncode.toNat - t.«have».toNat)) :
    Meaning .lens after r zs (credit log input output used rc) := by
  obtain ⟨regs, count, readUsed, readRun, readBound, readB, shape, nextProgress⟩ :=
    lenlens_waiting_source (c := ⟨some r, some (.tab zs), syncBuf h, flush⟩) rfl privateGet wf ncode haveBound B progress short
  have dispatch : runX (inflate_dispatch ⟨some r, some (.tab zs), syncBuf h, flush⟩) (dispatchRegs z s) (syncAlloc h) =
      .ok ((.error Ex.leave, regs), setI privateHeap zs (llSt t (stream l (input.drop headerUsed)) count)) := cut.trans readRun
  obtain ⟨z0, returned, get0, get1, buffers, _header, bytes, usedEq, outputBytes, actual⟩ := observed
  have sameZ : z0 = z := Option.some.inj (get0.symm.trans initial.good.live.hz)
  subst z0
  obtain ⟨rc0, heap0, nextZ, nextS, publicRun, nextJ, nextAllocator, _freed, frame, _nextIn, availIn, _nextOut, availOut⟩ :=
    header_dispatch_wait_public (readState := llSt t (stream l (input.drop headerUsed)) count) initial allocator buffers nonnull inputValid noType
      dispatch (by rw [setI_istates_same]) window
      (by rw [shape]; exact out) (by rw [shape]; exact put) (by rw [shape]; exact left)
  have same := Except.ok.inj (publicRun.symm.trans actual)
  cases same
  have sameReturned : returned = nextZ := Option.some.inj (get1.symm.trans nextJ.good.live.hz)
  subst returned
  have totalUsed : headerUsed + readUsed = used := by
    have initialHave := header_observed_bytes_length bytes
    have finalHave := readB.have_eq
    rw [usedEq, availIn]
    simp only [List.length_drop] at finalHave readBound
    omega
  have noOutput : output = [] := by
    have length := header_observed_bytes_length outputBytes
    rw [availOut, Nat.sub_self] at length
    exact List.length_eq_zero_iff.mp length
  refine ⟨nextZ, nextS, nextJ, nextAllocator, ?_, ?_, ?_, record,
    natBits l.bits.toNat l.hold.toNat ++ bytesBits ((input.drop headerUsed).take readUsed), lastBound, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [frame]; exact window
  · simp only [credit, empty, noOutput, List.nil_append]
  · rw [frame]; exact mode
  · rw [frame]; exact last
  · have advanced := view.advance (bytesBits ((input.drop headerUsed).take readUsed))
    simpa only [credit, bytesBits_append, ← totalUsed, List.take_add, List.append_assoc] using advanced
  · rw [frame]; exact litCount
  · rw [frame]; exact distCount
  · rw [frame]; exact codeCount
  · rw [frame]; exact nextProgress


/-- One real public TABLE call consumes the actual counts and exhausts in
LENLENS. The independent count source, BFINAL, initialized private prefix
and public held-word restoration all follow from the translated path. -/
theorem Meaning.table_lens_wait
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog}
    {flush rc : Int32} {input output : List UInt8} {used : Nat}
    {stream0 : ZStream} {observedState : InflateState}
    (before : Meaning .table h r zs log) (getZ : r.get h = some stream0) (getS : h.istates zs = some observedState)
    (nonnull : stream0.next_out ≠ .null) (inputValid : stream0.next_in = .null → stream0.avail_in = 0)
    (actual : DataStep .inflate h after r flush rc input output used) :
    ∃ (outcome : Except Ex Unit) (pulled : IL) (tableUsed : Nat),
      runX (NEEDBITS 14) (dispatchRegs stream0 observedState) (syncAlloc h) = .ok ((outcome, pulled), syncAlloc h) ∧
      tableUsed ≤ input.length ∧
      (outcome = .ok () → ¬ ((tableCounts observedState pulled.hold).nlen > 286 ∨ (tableCounts observedState pulled.hold).ndist > 30) →
        (stream (tableRegs pulled) (input.drop tableUsed)).length < 3 * (tableCounts observedState pulled.hold).ncode.toNat →
        Meaning .lens after r zs (credit log input output used rc)) := by
  have before0 := before
  obtain ⟨z, state, current, allocator, window, empty, mode, _record, _lastBound, _last, _blockView⟩ := before
  have sameZ : stream0 = z := Option.some.inj (getZ.symm.trans current.good.live.hz)
  have sameS : observedState = state := Option.some.inj (getS.symm.trans current.good.live.hs)
  subst stream0 observedState
  obtain ⟨outcome, pulled, tableUsed, pull, tableBound, ready⟩ :=
    before0.table_counts_prefix getZ getS nonnull actual
  refine ⟨outcome, pulled, tableUsed, pull, tableBound, ?_⟩
  intro normal valid short
  obtain ⟨record, lastBound, last, litCount, distCount, codeCount, countView, nextJ, nextPacket, seed, cut⟩ := ready normal valid
  let nextS := { tableCounts state pulled.hold with «have» := 0, mode := LENLENS }
  obtain ⟨ncode, haveBound, _nlen, _ndist, _good⟩ := nextJ.headerLengths rfl
  have actual0 := actual
  obtain ⟨z0, _returned, get0, _get1, _buffers, _header, bytes, _usedEq, _outputBytes, _actualRun⟩ := actual
  have sameZ : z0 = z := Option.some.inj (get0.symm.trans current.good.live.hz)
  subst z0
  have view := header_input_view_of_bytes (s := state) bytes current.held
  have view0 : BitInv (syncAlloc h) (dispatchRegs z state) input := by
    refine ⟨view.have_eq, ?_, view.hold_lt⟩
    rcases view.next with null | ⟨ref, array, off, pointer, get, bound, values⟩
    · exact Or.inl null
    · exact Or.inr ⟨ref, array, off, pointer, (byte_view_syncAlloc current.good.fresh get).1, bound, values⟩
  have fields := needbits_output_fields view0 (by decide : (14 : UInt32).toNat ≤ 49) (by simpa only [normal] using pull)
  apply lens_prefix_wait_public current allocator actual0 nonnull inputValid (by rw [mode]; decide) empty tableBound
    (t := nextS) (by rw [setI_istates_same]) nextJ.good.inv.wf rfl window ncode haveBound nextPacket.bits seed
    lastBound last litCount distCount codeCount countView
    (by exact fields.1) (by exact fields.2.1) (by change pulled.out_ = pulled.left; rw [fields.2.2, fields.2.1]; rfl) cut
  simpa only [nextS, UInt32.toNat_zero, Nat.sub_zero] using short

#print axioms lenlens_waiting_source
#print axioms Meaning.table_lens_wait
end Zlib.Inflate.Proofs.HeaderPhaseView
