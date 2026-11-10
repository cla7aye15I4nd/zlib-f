import ZlibF.Proof.«inflate.c.header-code-causal-prefix»
namespace Zlib.Inflate.Proofs.HeaderPhaseView
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.CumulativeParser
set_option autoImplicit false

/-- The original public call contains the actual ordinary CODELENS wait
at any private source prefix. The same-read frame and exact residual trace
establish the returned stored phase and cumulative parser continuation. -/
theorem codelens_embedded_wait_public
    {h after codeHeap readHeap : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog} {history : InflateDataTrace 15 r h log}
    {z codeZ : ZStream} {s codeState readState : InflateState} {codeRegs regs : IL} {headerUsed : Nat} {record : AlphabetMeta}
    {flush rc : Int32} {input output : List UInt8} {used : Nat}
    (scope : HeaderDataTrace.PlatformScope history)
    (observed : DataStep .inflate h after r flush rc input output used)
    (getZ : r.get h = some z) (getS : h.istates zs = some s) (pointer : z.state = some (.inflate zs))
    (nonnull : z.next_out ≠ .null) (inputValid : z.next_in = .null → z.avail_in = 0)
    (empty : log.output = []) (prefixBound : headerUsed ≤ input.length)
    (codeGetZ : r.get codeHeap = some codeZ) (codeGet : codeHeap.istates zs = some codeState)
    (wf : codeState.WellFormed) (mode : codeState.mode = CODELENS) (stateInv : CodeLengthInvariant zs codeState)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents codeState.codes 0 codeState.lenbits.toNat record.alphabet)
    (ordinary : ∀ index, index < 2 ^ codeState.lenbits.toNat → ∃ entry, codeState.codes[index]? = some entry ∧ entry.op = 0)
    (B : BitInv codeHeap codeRegs (input.drop headerUsed)) (emptyPrefix : actualLengthPrefix codeState = [])
    (window : codeState.wsize = 0) (put : codeRegs.put = z.next_out) (left : codeRegs.left = z.avail_out) (out : codeRegs.out_ = codeRegs.left)
    (lastBound : record.last < 2) (last : codeState.last.toInt = (record.last : Int))
    (litCount : codeState.nlen.toNat = record.lit + 257) (distCount : codeState.ndist.toNat = record.dist + 1)
    (codeCount : codeState.ncode.toNat = record.code + 4)
    (view : View readAlphabet record (bytesBits (log.input ++ input.take headerUsed)) (natBits codeRegs.bits.toNat codeRegs.hold.toNat))
    (embedding : WaitEmbedding ⟨some r, some (.tab zs), syncBuf h, flush⟩ (syncAlloc h)
      (clRead ⟨some r, some (.tab zs), syncBuf h, flush⟩) codeRegs codeHeap)
    (readRun : runX (clRead ⟨some r, some (.tab zs), syncBuf h, flush⟩) codeRegs codeHeap = .ok ((.error Ex.leave, regs), readHeap))
    (readGet : readHeap.istates zs = some readState) (readMode : readState.mode = CODELENS) :
    Meaning .code after r zs (credit log input output used rc) := by
  have actual0 := observed
  obtain ⟨z0, returned, get0, get1, _buffers, _active, bytes, usedEq, outputBytes, _run⟩ := observed
  have sameZ : z0 = z := Option.some.inj (get0.symm.trans getZ)
  subst z0
  obtain ⟨outcome, regs0, heap0, state0, readUsed, run0, full, getState, bound, readB, causal⟩ :=
    clRead_exact_consumed_input (c := ⟨some r, some (.tab zs), syncBuf h, flush⟩) rfl rfl codeGetZ codeGet wf.1 mode stateInv contents ordinary B
  rw [readRun] at run0
  cases run0
  have sameState : state0 = readState := Option.some.inj (getState.symm.trans readGet)
  subst state0
  have notBad : readState.mode ≠ BAD := by rw [readMode]; decide
  obtain ⟨consumed, source, trace⟩ := causal notBad
  rw [emptyPrefix] at trace
  obtain ⟨state0, _used0, get0, _bound0, _inv0, shape, _bits, readFrame, _remaining⟩ := full.1
  have sameState : state0 = readState := Option.some.inj (get0.symm.trans readGet)
  subst state0
  have mainRun := embedding regs readHeap readRun
  have readWindow : readState.wsize = 0 := by rw [readFrame]; exact window
  have noOutput : regs.out_ = regs.left := by rw [shape]; exact out
  obtain ⟨nextZ, nextS, next, allocator, frame, _nextIn, availIn, _nextOut, availOut⟩ :=
    HeaderPublicObserver.actual_wait_from_init history scope actual0 getZ pointer getS nonnull inputValid mainRun readGet readWindow noOutput
  have sameReturned : returned = nextZ := Option.some.inj (get1.symm.trans next.good.live.hz)
  subst returned
  have totalUsed : headerUsed + readUsed = used := by
    have initialHave := header_observed_bytes_length bytes
    have finalHave := readB.have_eq
    rw [usedEq, availIn]
    simp only [List.length_drop] at finalHave bound
    omega
  have noBytes : output = [] := by
    have length := header_observed_bytes_length outputBytes
    rw [availOut, shape] at length
    change output.length = z.avail_out.toNat - codeRegs.left.toNat at length
    rw [left, Nat.sub_self] at length
    exact List.length_eq_zero_iff.mp length
  have codes : nextS.codes = codeState.codes := by rw [frame, readFrame]; rfl
  have root : nextS.lenbits = codeState.lenbits := by rw [frame, readFrame]; rfl
  refine ⟨nextZ, nextS, next, allocator, ?_, ?_, ?_, record,
    natBits codeRegs.bits.toNat codeRegs.hold.toNat ++ bytesBits ((input.drop headerUsed).take readUsed), lastBound,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, consumed, ?_, ?_⟩
  · rw [frame]; exact readWindow
  · simp only [credit, empty, noBytes, List.nil_append]
  · rw [frame]; exact readMode
  · rw [frame, readFrame]; exact last
  · have advanced := view.advance (bytesBits ((input.drop headerUsed).take readUsed))
    simpa only [credit, bytesBits_append, ← totalUsed, List.take_add, List.append_assoc] using advanced
  · rw [frame, readFrame]; exact litCount
  · rw [frame, readFrame]; exact distCount
  · rw [frame, readFrame]; exact codeCount
  · rw [codes, root]; exact contents
  · rw [codes, root]; exact ordinary
  · rw [frame]; exact source
  · rw [frame, readFrame]; exact trace

#print axioms codelens_embedded_wait_public
end Zlib.Inflate.Proofs.HeaderPhaseView

namespace Zlib.Inflate.Proofs.HeaderPhaseView
open C Zlib.Inflate
open Zlib.Inflate.Proofs
set_option autoImplicit false

theorem WaitEmbedding.code_read {c : Ctx} {start heap : Heap} {l : IL}
    (embedding : WaitEmbedding c start (inflate_CODELENS c) l heap) : WaitEmbedding c start (clRead c) l heap := by
  intro regs after actual
  apply embedding regs after
  rw [inflate_CODELENS_eq, runX_bind, actual]

#print axioms WaitEmbedding.code_read
end Zlib.Inflate.Proofs.HeaderPhaseView
