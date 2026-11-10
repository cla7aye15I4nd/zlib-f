import ZlibF.Proof.«inflate.c.dynamic-empty-observed-source»
namespace Zlib.Inflate.Proofs.DynamicRejects
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.ActualHeader Zlib.Inflate.Proofs.WholeEpoch
set_option autoImplicit false
set_option maxHeartbeats 2200000

theorem rejection_append {log : DataLog} {bs : List UInt8} {used : Nat}
    (rejected : Rejects log) : Rejects (WholeWrapper.readLog log bs used) := by
  intro future decoded valid
  apply rejected (bs.take used++future) decoded
  simpa only [WholeWrapper.readLog,List.append_assoc] using valid

/-- A real empty-root read preserves the explicit exceptional phase and
exact held-source credit over any current buffer, including repeated
exhaustions. Completion still hands off to the actual inline tail. -/
theorem empty_phase_read_advance
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {log : DataLog} {wire : List Bool}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode=CODELENS)
    (data : EmptyCodeHeader log (leaveState s l) wire)
    (credit : CausalInput.Credited log.input wire l.bits l.hold)
    (event : CodeReadObservation c h r zs z s l bs data.alphabet) :
    event.state.mode=CODELENS ∧ ∃word,
      natBits l.bits.toNat l.hold.toNat++bytesBits (bs.take event.used)=word++natBits event.regs.bits.toNat event.regs.hold.toNat ∧
      CausalInput.Credited (log.input++bs.take event.used) (wire++word) event.regs.bits event.regs.hold ∧
      Nonempty (EmptyCodeHeader (WholeWrapper.readLog log bs event.used) (leaveState event.state event.regs) (wire++word)) := by
  obtain ⟨code,zeros,word,source⟩ := observed_empty_read_source E origin buffers mode data.contents data.allZero data.zeros event
  obtain ⟨saved,_used,get,_bound,_B,_shape,_bits,frame,_size,_have,_values,_modes,_done⟩ := event.full.1
  have stateEq : saved=event.state := Option.some.inj (get.symm.trans event.origin.good.live.hs)
  subst saved
  have lit : event.state.nlen=s.nlen := by rw [frame]
  have dist : event.state.ndist=s.ndist := by rw [frame]
  have ncode : event.state.ncode=s.ncode := by rw [frame]
  let counts : CountReadSource (leaveState event.state event.regs) data.alphabetWord [] :=
    {data.counts with
      literalCount:=by change event.state.nlen.toNat=_;rw [lit];exact data.counts.literalCount
      distanceCount:=by change event.state.ndist.toNat=_;rw [dist];exact data.counts.distanceCount
      codeCount:=by change event.state.ncode.toNat=_;rw [ncode];exact data.counts.codeCount}
  have alphabetRead : readCodeLenLens (leaveState event.state event.regs).ncode.toNat data.alphabetWord=some (data.alphabet,[]) := by
    change readCodeLenLens event.state.ncode.toNat data.alphabetWord=_
    rw [ncode]
    exact data.readAlphabet
  have contents : Zlib.Inftrees.Proofs.CodeLengthContents (leaveState event.state event.regs).codes 0
      (leaveState event.state event.regs).lenbits.toNat data.alphabet := by
    change Zlib.Inftrees.Proofs.CodeLengthContents event.state.codes 0 event.state.lenbits.toNat data.alphabet
    rw [frame]
    exact data.contents
  refine ⟨code,word,source,credit.append source,⟨⟨data.block,data.dynamic,?_,data.alphabet,data.countWord,data.alphabetWord,
    data.consumed++word,counts,data.countAnchor,alphabetRead,data.allZero,contents,zeros,data.output,?_,rejection_append data.rejected⟩⟩⟩
  · change event.state.last=Int32.ofNat data.block.last
    rw [frame];exact data.last
  · calc
      wire++word=(data.block.prefix++data.countWord++data.alphabetWord++data.consumed)++word :=
        congrArg (fun value=>value++word) data.anchor
      _ = _ := by simp only [List.append_assoc];rfl

#print axioms rejection_append
#print axioms empty_phase_read_advance
end Zlib.Inflate.Proofs.DynamicRejects
