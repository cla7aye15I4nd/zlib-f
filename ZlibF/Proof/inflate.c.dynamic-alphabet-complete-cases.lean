import ZlibF.Proof.«inflate.c.dynamic-alphabet-reject-anchored»
namespace Zlib.Inflate.Proofs.DynamicRejects
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.ActualHeader Zlib.Inflate.Proofs.WholeEpoch
set_option autoImplicit false
set_option maxHeartbeats 2400000

structure AlphabetBadSource (c : Ctx) (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream)
    (s : InflateState) (l : IL) (bs : List UInt8) (log : DataLog) (wire : List Bool)
    (header : AlphabetHeader log (leaveState s l) wire) where
  regs : IL
  used : Nat
  state : InflateState
  heap : Heap
  message : Nat
  bound : used≤bs.length
  actual : runX (inflate_LENLENS c) l h=.ok ((.ok (),{regs with ret:= -1}),tcBadHeap heap r zs z state message)
  word : List Bool
  source : bytesBits (log.input++bs.take used)=header.block.prefix++word++natBits regs.bits.toNat regs.hold.toNat
  credited : CausalInput.Credited (log.input++bs.take used) (header.block.prefix++word) regs.bits regs.hold
  rejected : Rejects (WholeWrapper.readLog log bs used)

/-- Actual complete alphabet classification with a source-backed refusal.
The accepted branch is the original actual AlphabetSeed, including empty
roots. No constructor success or after-phase is an incoming premise. -/
theorem alphabet_complete_source_cases
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {log : DataLog} {wire : List Bool}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode=LENLENS)
    (header : AlphabetHeader log (leaveState s l) wire)
    (credit : CausalInput.Credited log.input wire l.bits l.hold)
    (enough : 3*(s.ncode.toNat-s.«have».toNat)≤(stream l bs).length) :
    Nonempty (AlphabetBadSource c h r zs z s l bs log wire header) ∨
      Nonempty (AlphabetSeed c h r zs z s l bs header.received) := by
  have progress : LenlensProgress s l.hold l.bits header.received := header.progress
  obtain ⟨regs,used,filled,ret,next,root,work,codes,bound,headerRun,install,cut,kinds,precise,read,good⟩ :=
    lenlens_constructor_cases_source E origin buffers mode progress enough
  rcases kinds with success | rejected
  · obtain ⟨current,packet,_sizes,_wf,_frame,_ncode,lit,dist,last,_ptr,contents,empty,
      _cursor,_count,_put,_left,_out,_bits,_budget,actual⟩ := good success
    refine Or.inr ⟨⟨regs,used,filled,next,root,work,codes,
      {llPre zs filled with next:=next,lenbits:=root,work:=work,codes:=codes,«have»:=0,mode:=CODELENS},
      rfl,bound,headerRun,?_,current,packet,lit,dist,last,read,precise.mp success,empty,contents,actual⟩⟩
    simpa only [success] using install
  · have invalid : ¬Acceptable .codeLength (Zlib.Inftrees.Proofs.lensOf (fun k=>(filled.lens.getD k 0).toNat) 19) := by
      intro valid
      have zero:=precise.mpr valid
      rw [rejected] at zero
      cases zero
    obtain ⟨word,source,credited,reject⟩ := alphabet_header_rejects header credit rfl read (Or.inl invalid)
    obtain ⟨i,actual⟩ := rejected_codes_source E cut (by simpa only [rejected] using install)
    exact Or.inl ⟨⟨regs,used,_,_,i,bound,actual,word,source,credited,reject⟩⟩

#print axioms alphabet_complete_source_cases
end Zlib.Inflate.Proofs.DynamicRejects
