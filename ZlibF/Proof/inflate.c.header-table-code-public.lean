import ZlibF.Proof.«inflate.c.header-constructor-deterministic-source»
namespace Zlib.Inflate.Proofs.HeaderPhaseView
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.CumulativeBoundary Zlib.Inflate.Proofs.CumulativeTableBoundary
set_option autoImplicit false

/-- Technical source-prefix composition; every private premise is produced
by the actual TABLE source in the public wrapper below. -/
theorem lenlens_prefix_constructor_wait
    {h after privateHeap : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog}
    {z : ZStream} {s t : InflateState} {l : IL} {sourceUsed : Nat} {record : CountMeta}
    {flush rc : Int32} {input output : List UInt8} {used : Nat}
    (initial : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (actual : DataStep .inflate h after r flush rc input output used)
    (nonnull : z.next_out ≠ .null) (inputValid : z.next_in = .null → z.avail_in = 0)
    (noType : s.mode ≠ TYPE) (empty : log.output = []) (sourceBound : sourceUsed ≤ input.length)
    (privateJ : DefaultOriginState privateHeap r zs z t) (mode : t.mode = LENLENS) (window : t.wsize = 0)
    (packet : DispatchBuffers privateHeap r l (input.drop sourceUsed))
    (progress : LenlensProgress t l.hold l.bits (natBits l.bits.toNat l.hold.toNat))
    (lastBound : record.last < 2) (last : t.last.toInt = (record.last : Int))
    (litCount : t.nlen.toNat = record.lit + 257) (distCount : t.ndist.toNat = record.dist + 1)
    (codeCount : t.ncode.toNat = record.code + 4)
    (countView : View readCounts record (bytesBits (log.input ++ input.take sourceUsed)) (natBits l.bits.toNat l.hold.toNat))
    (sourcePut : l.put = z.next_out) (sourceLeft : l.left = z.avail_out) (sourceOut : l.out_ = l.left)
    (sourceCut : runX (inflate_dispatch ⟨some r, some (.tab zs), syncBuf h, flush⟩) (dispatchRegs z s) (syncAlloc h) =
      runX (inflate_LENLENS ⟨some r, some (.tab zs), syncBuf h, flush⟩) l privateHeap)
    (enough : 3 * (t.ncode.toNat - t.«have».toNat) ≤ (stream l (input.drop sourceUsed)).length) :
    ∃ (headerRegs : IL) (headerUsed : Nat) (filled : InflateState) (ret : Int32)
      (next : CodePtr) (root : UInt32) (work : Array UInt16) (codes : Array Code),
      headerUsed ≤ (input.drop sourceUsed).length ∧
      runX (do
        (do xwhile (llCond ⟨some r, some (.tab zs), syncBuf h, flush⟩) (llBody ⟨some r, some (.tab zs), syncBuf h, flush⟩)
            xwhile (lzCond ⟨some r, some (.tab zs), syncBuf h, flush⟩) (lzBody ⟨some r, some (.tab zs), syncBuf h, flush⟩))
        llInstall ⟨some r, some (.tab zs), syncBuf h, flush⟩) l privateHeap =
        .ok ((.ok ret, { headerRegs with ret := ret }),
          setI privateHeap zs { llPre zs filled with next := next, lenbits := root, work := work, codes := codes }) ∧
      (ret = 0 →
        ¬ (∀ value ∈ Zlib.Inftrees.Proofs.lensOf (fun k => (filled.lens.getD k 0).toNat) 19, value = 0) →
        let codeState := { llPre zs filled with next := next, lenbits := root, work := work, codes := codes, «have» := 0, mode := CODELENS }
        ∀ (regs : IL) (readHeap : Heap) (readState : InflateState),
          runX (clRead ⟨some r, some (.tab zs), syncBuf h, flush⟩) { headerRegs with ret := 0 }
            (setI privateHeap zs codeState) = .ok ((.error Ex.leave, regs), readHeap) →
          readHeap.istates zs = some readState → readState.mode = CODELENS →
          Meaning .code after r zs (credit log input output used rc)) := by
  have actual0 := actual
  obtain ⟨z0, returned, get0, get1, _buffers, _header, bytes, usedEq, _outputBytes, _run⟩ := actual
  have sameZ : z0 = z := Option.some.inj (get0.symm.trans initial.good.live.hz)
  subst z0
  obtain ⟨ncode, haveBound, nlen, ndist, good⟩ := privateJ.headerLengths mode
  obtain ⟨headerRegs, headerUsed, filled, ret, next, root, work, codes, headerBound, _inputB,
    headerRun, install, _kinds, _successIff, alphabetRead, ready⟩ :=
    lenlens_constructor_boundary_ready_source (c := ⟨some r, some (.tab zs), syncBuf h, flush⟩) rfl privateJ.good.live.hs privateJ.good.inv.wf ncode haveBound good packet.bits progress nlen ndist enough
  refine ⟨headerRegs, headerUsed, filled, ret, next, root, work, codes, headerBound, ?_, ?_⟩
  · rw [runX_bind, headerRun]
    exact install
  intro success nonempty
  dsimp only
  intro regs readHeap readState readRun readGet readMode
  obtain ⟨wf, inv, contents, emptyPrefix, code, lit, dist, savedLast, put, left, out, codeWindow, codeB, cut⟩ := ready success
  let codeState := { llPre zs filled with next := next, lenbits := root, work := work, codes := codes, «have» := 0, mode := CODELENS }
  let alphabet := Zlib.Inftrees.Proofs.lensOf (fun k => (filled.lens.getD k 0).toNat) 19
  have ordinary : ∀ index, index < 2 ^ codeState.lenbits.toNat → ∃ entry, codeState.codes[index]? = some entry ∧ entry.op = 0 := by
    rcases contents.layout with emptyRoot | ordinaryRoot
    · exact False.elim (nonempty emptyRoot.2.1)
    · simpa only [Nat.zero_add] using ordinaryRoot
  have prefixCut := sourceCut.trans cut
  obtain ⟨nextZ, nextS, readUsed, nextJ, nextAllocator, noOutput, availIn, stateMode, stateWindow,
    finalCode, finalLit, finalDist, finalLast, finalContents, finalOrdinary, readBound, readB, nextProgress⟩ :=
    phase_to_codelens_observed_seed_with_last initial allocator actual0 nonnull inputValid noType prefixCut
      (by simpa using privateJ.good.live.hz) (by rw [setI_istates_same]) wf rfl inv contents ordinary codeB emptyPrefix (codeWindow.trans window)
      (by change headerRegs.out_ = headerRegs.left; rw [out, left]; exact sourceOut) (put.trans sourcePut) (left.trans sourceLeft) readRun readGet readMode
  have returnedEq : returned = nextZ := Option.some.inj (get1.symm.trans nextJ.good.live.hz)
  subst returned
  have actualUse : sourceUsed + headerUsed + readUsed = used := by
    have before := header_observed_bytes_length bytes
    have finalHave := readB.have_eq
    rw [usedEq, availIn]
    simp only [List.length_drop] at finalHave readBound headerBound
    omega
  have alphabetView : View readAlphabet ⟨record, alphabet⟩
      (bytesBits (log.input ++ input.take sourceUsed) ++ bytesBits ((input.drop sourceUsed).take headerUsed))
      (natBits headerRegs.bits.toNat headerRegs.hold.toNat) := by
    apply countView.alphabet_of_counts
    rw [← codeCount]
    exact alphabetRead
  have wholeView := alphabetView.advance (bytesBits (((input.drop sourceUsed).drop headerUsed).take readUsed))
  refine ⟨nextZ, nextS, nextJ, nextAllocator, stateWindow, ?_, stateMode, ⟨record, alphabet⟩,
    natBits headerRegs.bits.toNat headerRegs.hold.toNat ++ bytesBits (((input.drop sourceUsed).drop headerUsed).take readUsed),
    lastBound, ?_, ?_, ?_, ?_, ?_, finalContents, finalOrdinary, ?_⟩
  · simp only [credit, empty, noOutput, List.nil_append]
  · rw [finalLast, savedLast]; exact last
  · simpa only [credit, bytesBits_append, ← actualUse, List.take_add, List.append_assoc, List.drop_drop] using wholeView
  · rw [finalLit, lit]; exact litCount
  · rw [finalDist, dist]; exact distCount
  · rw [finalCode, code]; exact codeCount
  · simpa only [finalLit, finalDist] using nextProgress





/-- A deterministic actual TABLE header, LENLENS header/CODES constructor
and exhausted clRead select this whole public crossing. The original log
credits both header prefixes and clRead consumption on the real final heap. -/
theorem Meaning.table_constructor_observed
    {h after prefixHeap readHeap : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog}
    {flush rc : Int32} {input output : List UInt8} {used : Nat}
    {stream0 : ZStream} {observedState installed readState : InflateState} {pulled prefixRegs regs : IL}
    (before : Meaning .table h r zs log) (getZ : r.get h = some stream0) (getS : h.istates zs = some observedState)
    (nonnull : stream0.next_out ≠ .null) (inputValid : stream0.next_in = .null → stream0.avail_in = 0)
    (actual : DataStep .inflate h after r flush rc input output used)
    (pull : runX (NEEDBITS 14) (dispatchRegs stream0 observedState) (syncAlloc h) = .ok ((.ok (), pulled), syncAlloc h))
    (valid : ¬ ((tableCounts observedState pulled.hold).nlen > 286 ∨ (tableCounts observedState pulled.hold).ndist > 30))
    (enough : 3 * (tableCounts observedState pulled.hold).ncode.toNat ≤ pulled.bits.toNat - 14 + 8 * pulled.have_.toNat)
    (prefixRun : runX (do
      (do xwhile (llCond ⟨some r, some (.tab zs), syncBuf h, flush⟩) (llBody ⟨some r, some (.tab zs), syncBuf h, flush⟩)
          xwhile (lzCond ⟨some r, some (.tab zs), syncBuf h, flush⟩) (lzBody ⟨some r, some (.tab zs), syncBuf h, flush⟩))
      llInstall ⟨some r, some (.tab zs), syncBuf h, flush⟩) (tableRegs pulled)
        (setI (syncAlloc h) zs { tableCounts observedState pulled.hold with «have» := 0, mode := LENLENS }) =
        .ok ((.ok 0, prefixRegs), prefixHeap))
    (prefixGet : prefixHeap.istates zs = some installed)
    (nonempty : ¬ (∀ value ∈ Zlib.Inftrees.Proofs.lensOf (fun k => (installed.lens.getD k 0).toNat) 19, value = 0))
    (readRun : runX (clRead ⟨some r, some (.tab zs), syncBuf h, flush⟩) prefixRegs
      (setI prefixHeap zs { installed with «have» := 0, mode := CODELENS }) = .ok ((.error Ex.leave, regs), readHeap))
    (readGet : readHeap.istates zs = some readState) (readMode : readState.mode = CODELENS) :
    Meaning .code after r zs (credit log input output used rc) := by
  have before0 := before
  obtain ⟨z, state, current, allocator, window, empty, mode, _record, _lastBound, _last, _blockView⟩ := before
  have sameZ : stream0 = z := Option.some.inj (getZ.symm.trans current.good.live.hz)
  have sameS : observedState = state := Option.some.inj (getS.symm.trans current.good.live.hs)
  subst stream0 observedState
  obtain ⟨outcome, pulled0, tableUsed, pull0, tableBound, ready⟩ :=
    before0.table_counts_prefix getZ getS nonnull actual
  have same := Except.ok.inj (pull0.symm.trans pull)
  cases same
  obtain ⟨record, lastBound, last, litCount, distCount, codeCount, countView, nextJ, nextPacket, seed, cut⟩ := ready rfl valid
  let nextS := { tableCounts state pulled.hold with «have» := 0, mode := LENLENS }
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
  have fields := needbits_output_fields view0 (by decide : (14 : UInt32).toNat ≤ 49) pull
  obtain ⟨outcome1, pulled1, used1, run1, _bound1, _B1, _source1, _count1, _shape1, _max1, _noPull1, full, _wait1, _kinds1, _cursor1⟩ :=
    NEEDBITS_run_cursor view0 14 (by decide)
  rw [pull] at run1
  cases run1
  have enoughBits : 14 ≤ pulled.bits.toNat := full rfl
  have enough0 : 3 * (nextS.ncode.toNat - nextS.«have».toNat) ≤ (stream (tableRegs pulled) (input.drop tableUsed)).length := by
    rw [tcStream_length nextPacket.bits]
    have haveEq := nextPacket.bits.have_eq
    change pulled.have_.toNat = (input.drop tableUsed).length at haveEq
    change 3 * ((tableCounts state pulled.hold).ncode.toNat - 0) ≤ (pulled.bits - 14).toNat + 8 * (input.drop tableUsed).length
    rw [UInt32.toNat_sub_of_le pulled.bits 14 (UInt32.le_iff_toNat_le.mpr enoughBits), ← haveEq]
    exact enough
  obtain ⟨headerRegs, headerUsed, filled, ret, next, root, work, codes, _bound, computed, branch⟩ :=
    lenlens_prefix_constructor_wait current allocator actual0 nonnull inputValid (by rw [mode]; decide) empty tableBound
      nextJ rfl window nextPacket seed lastBound last litCount distCount codeCount countView
      fields.1 fields.2.1 (by change pulled.out_ = pulled.left; rw [fields.2.2, fields.2.1]; rfl) cut enough0
  have same := Except.ok.inj (computed.symm.trans prefixRun)
  cases same
  simp only [setI_istates_same] at prefixGet
  have sameInstalled := Option.some.inj prefixGet
  subst installed
  apply branch rfl nonempty regs readHeap readState
  · simpa only [setI_setI] using readRun
  · exact readGet
  · exact readMode

#print axioms lenlens_prefix_constructor_wait
#print axioms Meaning.table_constructor_observed
end Zlib.Inflate.Proofs.HeaderPhaseView
