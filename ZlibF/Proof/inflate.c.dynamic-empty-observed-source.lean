import ZlibF.Proof.«inflate.c.dynamic-empty-reader-source»
namespace Zlib.Inflate.Proofs.DynamicRejects
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.ActualHeader Zlib.Inflate.Proofs.WholeEpoch Zlib.Inffast.Proofs
set_option autoImplicit false
set_option maxHeartbeats 2200000

theorem zero_contents_layout {ca : Array Code} {offset root : Nat} {alphabet : List Nat}
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents ca offset root alphabet)
    (zero : ∀length∈alphabet,length=0) :
    root=1 ∧ ca[offset]?=some (⟨64,1,0⟩:Code) ∧ ca[offset+1]?=some (⟨64,1,0⟩:Code) := by
  rcases contents.layout with empty|ordinary
  · exact ⟨empty.1,empty.2.2⟩
  · have inside : 0<2^root := Nat.two_pow_pos _
    obtain ⟨entry,cell,op⟩ := ordinary 0 inside
    have cell0 : ca[offset]?=some entry := by simpa only [Nat.add_zero] using cell
    have stored : ca.getD (offset+0) default=entry := by
      simp only [Array.getD_eq_getD_getElem?,Nat.add_zero,cell0,Option.getD_some]
    have bounds:=contents.safe.2.2.2 0 inside
    rw [stored] at bounds
    obtain ⟨suffix,query⟩ := ZlibF.Math.InflateHeldBits.padded_query (value:=0) (width:=8) (root:=root) (by decide)
      (by have:=contents.safe.2.1;omega)
    simp only [Nat.zero_mod] at query
    obtain ⟨symbol,_small,_value,_width,decoded⟩ := contents.sound _ _ _ _ query cell op
      (by rw [bitsOfNat_length];have:=contents.safe.2.1;omega)
    exact False.elim (zero_alphabet_decode_impossible zero decoded)

/-- The actual exceptional empty-root reader has the exact same held
source accounting as the ordinary reader, while only appending zeros. -/
theorem observed_empty_read_source
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {alphabet : List Nat}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode=CODELENS)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat alphabet)
    (zero : ∀length∈alphabet,length=0) (zeros : actualLengthPrefix s=List.replicate s.«have».toNat 0)
    (event : CodeReadObservation c h r zs z s l bs alphabet) :
    event.state.mode=CODELENS ∧ actualLengthPrefix event.state=List.replicate event.state.«have».toNat 0 ∧
      ∃word,natBits l.bits.toNat l.hold.toNat++bytesBits (bs.take event.used)=word++natBits event.regs.bits.toNat event.regs.hold.toNat := by
  obtain ⟨root,first,second⟩ := zero_contents_layout contents zero
  obtain ⟨outcome,regs,after,state,used,read,get,bound,B,source⟩ := clRead_empty_stream_source E.strm E.st E.hz E.hs
    origin.good.inv.wf.1 mode origin.lengths contents root first second buffers.bits
  rw [event.read] at read
  cases read
  have stateEq : state=event.state := Option.some.inj (get.symm.trans event.origin.good.live.hs)
  subst state
  have usedEq : used=event.used := by
    have a:=B.have_eq;have b:=event.buffers.bits.have_eq;simp only [List.length_drop] at a b
    have more:=event.bound;omega
  subst used
  obtain ⟨word,source⟩ := source
  obtain ⟨outcome0,regs0,after0,state0,used0,read0,get0,_bound0,_B0,code,values,_complete⟩ :=
    clRead_empty_root E.st E.hs origin.good.inv.wf.1 mode origin.lengths root first second zeros buffers.bits
  rw [event.read] at read0
  cases read0
  have stateEq : state0=event.state := Option.some.inj (get0.symm.trans event.origin.good.live.hs)
  subst state0
  refine ⟨code,values,word,?_⟩
  apply (List.append_left_inj (bytesBits (bs.drop event.used))).mp
  have split : bytesBits bs=bytesBits (bs.take event.used)++bytesBits (bs.drop event.used) := by
    rw [←bytesBits_append,List.take_append_drop]
  simpa only [stream,split,List.append_assoc] using source

#print axioms zero_contents_layout
#print axioms observed_empty_read_source
end Zlib.Inflate.Proofs.DynamicRejects
