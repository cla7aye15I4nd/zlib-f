import ZlibF.Proof.«inflate.c.header-entry-public-wait»
namespace Zlib.Inflate.Proofs.HeaderPhaseView
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- A contextual source cut transports a real private exhausted execution
into the unchanged whole main call. It states only actual run equality;
it contains no parser invariant, success contract or desired postcondition. -/
def WaitEmbedding (c : Ctx) (start : Heap) (program : X Unit) (l : IL) (heap : Heap) : Prop :=
  ∀ (regs : IL) (after : Heap), runX program l heap = .ok ((.error Ex.leave, regs), after) →
    runX (inflate_run c) IL.init start = .ok ((.error Ex.leave, regs), after)

/-- The actual remaining main loop transports any exhausted fall-through
in its first real dispatch. This also applies after several normal HEAD
and TYPE trips; those trips are already included in mainCut. -/
theorem wait_embedding_of_main_cut {c : Ctx} {start heap privateHeap : Heap} {l privateRegs : IL} {program : X Unit}
    (mainCut : runX (inflate_run c) IL.init start = runX (xwhile (pure true) (inflate_dispatch c)) l heap)
    (sourceCut : runX (inflate_dispatch c) l heap = runX program privateRegs privateHeap) :
    WaitEmbedding c start program privateRegs privateHeap := by
  intro regs after actual
  have dispatch := sourceCut.trans actual
  have loop := xwhile_run_chain (inflate_dispatch c) (fun _ => l) (fun _ => heap) 0 (by unfold fuel; decide)
    Ex.leave regs after (by intro j impossible; omega) dispatch
  exact mainCut.trans loop

/-- A second exact private source cut composes inside the same original
call without inserting LOAD, RESTORE or a new public allocation. -/
theorem WaitEmbedding.comp {c : Ctx} {start heap privateHeap : Heap} {program next : X Unit} {l regs : IL}
    (embedding : WaitEmbedding c start program l heap)
    (cut : runX program l heap = runX next regs privateHeap) : WaitEmbedding c start next regs privateHeap := by
  intro final after actual
  exact embedding final after (cut.trans actual)

/-- The actual partial LENLENS reader, metadata suffix and free establish
the public stored phase. All private representation/source facts below
are produced by the preceding real count/header producer. -/
theorem lenlens_embedded_wait_public
    {h after privateHeap : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog} {history : InflateDataTrace 15 r h log}
    {z : ZStream} {s t : InflateState} {l : IL} {headerUsed : Nat} {record : CountMeta}
    {flush rc : Int32} {input output : List UInt8} {used : Nat}
    (scope : HeaderDataTrace.PlatformScope history)
    (observed : DataStep .inflate h after r flush rc input output used)
    (getZ : r.get h = some z) (getS : h.istates zs = some s) (pointer : z.state = some (.inflate zs))
    (nonnull : z.next_out ≠ .null) (inputValid : z.next_in = .null → z.avail_in = 0)
    (empty : log.output = []) (prefixBound : headerUsed ≤ input.length)
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
    (embedding : WaitEmbedding ⟨some r, some (.tab zs), syncBuf h, flush⟩ (syncAlloc h)
      (inflate_LENLENS ⟨some r, some (.tab zs), syncBuf h, flush⟩) l privateHeap)
    (short : (stream l (input.drop headerUsed)).length < 3 * (t.ncode.toNat - t.«have».toNat)) :
    Meaning .lens after r zs (credit log input output used rc) := by
  obtain ⟨regs, count, readUsed, readRun, readBound, readB, shape, nextProgress⟩ :=
    lenlens_waiting_source (c := ⟨some r, some (.tab zs), syncBuf h, flush⟩) rfl privateGet wf ncode haveBound B progress short
  have mainRun := embedding regs _ readRun
  have actual0 := observed
  obtain ⟨z0, returned, get0, get1, _buffers, _active, bytes, usedEq, outputBytes, _run⟩ := observed
  have sameZ : z0 = z := Option.some.inj (get0.symm.trans getZ)
  subst z0
  obtain ⟨nextZ, nextS, nextJ, nextAllocator, frame, _nextIn, availIn, _nextOut, availOut⟩ :=
    HeaderPublicObserver.actual_wait_from_init (readState := llSt t (stream l (input.drop headerUsed)) count) history scope actual0 getZ pointer getS nonnull inputValid mainRun
      (by rw [setI_istates_same]) window (by rw [shape]; exact out)
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
    rw [availOut, shape] at length
    change output.length = z.avail_out.toNat - l.left.toNat at length
    rw [left, Nat.sub_self] at length
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

#print axioms wait_embedding_of_main_cut
#print axioms WaitEmbedding.comp
#print axioms lenlens_embedded_wait_public
end Zlib.Inflate.Proofs.HeaderPhaseView
