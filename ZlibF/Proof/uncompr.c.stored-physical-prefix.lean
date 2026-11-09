import ZlibF.Math.UncompressStoredWire
import ZlibF.Proof.«uncompr.c.stored-zlib-header»
import ZlibF.Proof.«uncompr.c.stored-tag»
import ZlibF.Proof.«uncompr.c.stored-length-entry»

namespace Zlib.Uncompr.Proof.StoredPhysicalPrefix
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false
set_option maxRecDepth 100000

def preparedState (s : InflateState) (payload : List UInt8) : InflateState :=
  {s with dmax:=32768,flags:=0,check:=1,mode:=COPY,last:=1,length:=UInt32.ofNat payload.length}

/-- A trace of the actual first two mode steps and the complete third
mode's fall-through to COPY. All states refer to this same physical wire. -/
structure Prefix (c : Ctx) (h : Heap) (r : ZStreamRef) (zs : Nat)
    (z : ZStream) (s : InflateState) (l : IL) (payload : List UInt8)
    (h1 : Heap) (l1 : IL) (h2 : Heap) (l2 ready : IL) : Prop where
  head : runX (inflate_dispatch c) l h=.ok ((.ok (),l1),h1)
  tag : runX (inflate_dispatch c) l1 h1=.ok ((.ok (),l2),h2)
  stored : runX (inflate_dispatch c) l2 h2=
    runX (inflate_COPY c) ready (setI h2 zs (preparedState s payload))
  env : Env c (setI h2 zs (preparedState s payload)) r zs {z with adler:=1} (preparedState s payload)
  input : BitInv (setI h2 zs (preparedState s payload)) ready (payload++be32 (adler32 payload).toNat)
  cursor : ready.next=inputAdvance l.next 7
  put : ready.put=l.put
  left : ready.left=l.left
  out : ready.out_=l.out_
  bits : ready.bits=0
  hold : ready.hold=0
  views : ∀ref : BRef,Space.get (setI h2 zs (preparedState s payload)) ref=Space.get h ref
  readonly : ∀ref : BRef,Space.ro (setI h2 zs (preparedState s payload)) ref=Space.ro h ref

theorem physical_prefix {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL)
    (payload : List UInt8) (small : payload.length<65536)
    (input : BitInv h l (StoredWire.wire payload)) (mode : s.mode=HEAD)
    (last : s.last=0) (wrap : s.wrap=5) (header : s.head=none) (wbits : s.wbits=15)
    (bits : l.bits=0) (hold : l.hold=0) (flush : c.flush=Z_NO_FLUSH) :
    ∃h1 l1 h2 l2 ready,Prefix c h r zs z s l payload h1 l1 h2 l2 ready := by
  let tail := payload++be32 (adler32 payload).toNat
  let lens := le16 payload.length++le16 (65535-payload.length)
  have wire : StoredWire.wire payload=[0x78,0x01]++(1::(lens++tail)) := by
    simp only [StoredWire.wire,lens,tail,List.append_assoc,List.cons_append,List.nil_append]
  have packet := input
  rw [wire] at packet
  obtain ⟨a,headRun,headInput,headCursor,headShape⟩ :=
    StoredZlibHeader.head_run E l (1::(lens++tail)) packet bits hold wrap header wbits
  let z1 := {z with adler:=1}
  let s1 := {s with dmax:=32768,flags:=0,check:=1,mode:=TYPE}
  let h1 := setI (r.put h z1) zs s1
  let l1 := {a with hold:=0,bits:=0,len:=15}
  have E1 : Env c h1 r zs z1 s1 :=
    ⟨E.strm,E.st,by simp [h1,ZStreamRef.get_put_same E.hz],by simp [h1]⟩
  obtain ⟨b,tagRun,tagInput,tagCursor,tagShape⟩ :=
    StoredTag.type_run E1 l1 (lens++tail) headInput rfl rfl last flush
  let s2 := {s1 with last:=1,mode:=STORED}
  let h2 := setI h1 zs s2
  let l2 := {b with hold:=0,bits:=5}
  have E2 : Env c h2 r zs z1 s2 :=
    ⟨E.strm,E.st,by simpa [h2] using E1.hz,by simp [h2]⟩
  obtain ⟨d,storedRun,storedInput,storedCursor,storedShape⟩ :=
    StoredLengthEntry.stored_entry E2 l2 payload.length small tail tagInput rfl rfl flush
  let ready := {d with hold:=0,bits:=0}
  let s3 := preparedState s payload
  have env : Env c (setI h2 zs s3) r zs z1 s3 :=
    ⟨E.strm,E.st,by simpa only [ZStreamRef.get_setI] using E2.hz,by simp⟩
  refine ⟨h1,l1,h2,l2,ready,⟨?_,?_,?_,env,storedInput,?_,?_,?_,?_,rfl,rfl,?_,?_⟩⟩
  · unfold inflate_dispatch
    rw [runX_bind,runX_rdS E]
    simp only [mode]
    exact headRun
  · unfold inflate_dispatch
    rw [runX_bind,runX_rdS E1]
    change runX (inflate_TYPE c) l1 h1=_
    exact tagRun
  · unfold inflate_dispatch
    rw [runX_bind,runX_rdS E2]
    change runX (inflate_STORED c) l2 h2=_
    exact storedRun
  · change d.next=inputAdvance l.next 7
    rw [storedCursor]
    change inputAdvance b.next 4=_
    rw [tagCursor]
    change inputAdvance (inputAdvance a.next 1) 4=_
    rw [headCursor,inputAdvance_add,inputAdvance_add]
  · change d.put=l.put
    rw [storedShape]
    change b.put=l.put
    rw [tagShape]
    change a.put=l.put
    rw [headShape]
  · change d.left=l.left
    rw [storedShape]
    change b.left=l.left
    rw [tagShape]
    change a.left=l.left
    rw [headShape]
  · change d.out_=l.out_
    rw [storedShape]
    change b.out_=l.out_
    rw [tagShape]
    change a.out_=l.out_
    rw [headShape]
  · intro ref
    simp only [h2,h1,byte_view_get_setI,byte_view_get_stream_put]
  · intro ref
    simp only [h2,h1,byte_view_ro_setI,byte_view_ro_stream_put]

#print axioms physical_prefix
end Zlib.Uncompr.Proof.StoredPhysicalPrefix
