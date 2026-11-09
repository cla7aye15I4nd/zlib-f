import ZlibF.Proof.«compress.c.local-content-body-step»
import ZlibF.Proof.«compress.c.local-content-body-resources»

/-! # Finite actual ordinary-loop execution to its next source checkpoint -/
namespace ZlibF.Spec.Public.Proofs.CompressLocalContentLoop
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalContent ZlibF.Spec.Public.Proofs.CompressLocalContentBodyStep
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

/-- A finite prefix records only executions of the original body and its
original continuing loop condition. It does not replace the source loop. -/
inductive ActualOrdinaryPrefix (ds : Nat) (flush : Int32) : Nat → LoopS → Heap → LoopS → Heap → Prop
  | nil (st : LoopS) (heap : Heap) : ActualOrdinaryPrefix ds flush 0 st heap st heap
  | step {n : Nat} {st mid final : LoopS} {heap next after : Heap}
      (ordinary : ∃ d, heap.dstates ds=some d ∧ 262≤d.lookahead.toNat ∧ d.sym_next.toNat+3<d.sym_end.toNat)
      (unbroken : st.brk=false) (running : st.ret=none)
      (body : deflate_slow_body (some (.tab ds)) flush st heap=.ok (mid,next))
      (rest : ActualOrdinaryPrefix ds flush n mid next final after) :
      ActualOrdinaryPrefix ds flush (n+1) st heap final after

/-- Exact unfolding of the original fuelled C loop through the observed
prefix. The same remaining fuel and same returned heap enter its continuation. -/
theorem ActualOrdinaryPrefix.continuation {ds n : Nat} {flush : Int32}
    {st final : LoopS} {heap after : Heap}
    (prefixRun : ActualOrdinaryPrefix ds flush n st heap final after) (remaining : Nat) :
    cwhile.go forever (deflate_slow_body (some (.tab ds)) flush) (n+remaining) st heap=
      cwhile.go forever (deflate_slow_body (some (.tab ds)) flush) remaining final after := by
  induction prefixRun with
  | nil => simp only [Nat.zero_add]
  | @step n st mid final heap next after ordinary unbroken running body rest ih =>
    rw [Nat.succ_add,cwhile.go]
    simp only [forever,pure_app,bind_app,unbroken,running,Option.isSome_none,Bool.false_or,Bool.not_false,
      ite_true,body]
    exact ih

/-- Fold the full typed resource observer over the same actual ordinary
prefix. Old caller collisions remain admitted on every intermediate heap. -/
theorem ActualOrdinaryPrefix.resources {h after : Heap} {r : ZStreamRef} {cutoff ds origin base n : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol}
    {st final : LoopS} {flush : Int32}
    (prefixRun : ActualOrdinaryPrefix ds flush n st h final after)
    (boundary : LocalContent h cutoff r ds z d input origin base xs) :
    Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      after.nalloc=h.nalloc ∧ after.nextBlk=h.nextBlk := by
  induction prefixRun generalizing d xs with
  | nil =>
    exact ⟨Shape.refl _,⟨rfl,rfl,rfl,Nat.le_refl _,Nat.le_refl _,fun _ _ _ => ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩,rfl,rfl⟩
  | @step n st mid final heap next after ordinary unbroken running body rest ih =>
    obtain ⟨observed,get,look,room⟩ := ordinary
    have stateEq : observed=d := Option.some.inj (get.symm.trans boundary.state.live.hs)
    subst observed
    obtain ⟨expected,expectedHeap,nextD,nextYs,run,content,_⟩ := local_content_body boundary look room flush st
    have same := Prod.mk.inj (Except.ok.inj (run.symm.trans body))
    rw [same.2] at content
    obtain ⟨record,owned,shape,frame,_live,alloc,ids⟩ :=
      CompressLocalContentBodyResources.local_content_body_resources boundary look room flush st body content.state.live
    obtain ⟨shapeA,frameA,allocA,idsA⟩ := ih content
    rw [owned] at frameA
    exact ⟨shape.trans shapeA,full_frame_trans_shape frame frameA shape,allocA.trans alloc,idsA.trans ids⟩

/-- The next source checkpoint is either a short lookahead requiring
fill_window or entry to the last-symbol-slot/full-buffer handling branch.
This predicate does not claim that the latter branch has already executed. -/
def OrdinaryCheckpoint (d : DeflateState) : Prop :=
  d.lookahead.toNat<262 ∨ d.sym_end.toNat≤d.sym_next.toNat+3

/-- Consume actual ordinary bodies until a definite source checkpoint.
Every body strictly reduces buffered lookahead, so the execution count is
bounded by the starting lookahead. Matching consumption and symbol traces
are accumulated on the same actual heaps with one fixed logical input. -/
theorem ordinary_prefix_bounded (budget : Nat) {h : Heap} {r : ZStreamRef} {cutoff ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol}
    (boundary : LocalContent h cutoff r ds z d input origin base xs)
    (bound : d.lookahead.toNat≤budget) (output : z.avail_out≠0)
    (flush : Int32) (st : LoopS) (running : st.ret=none) (unbroken : st.brk=false) :
    ∃ n final after result ys,
      ActualOrdinaryPrefix ds flush n st h final after ∧
      LocalContent after cutoff r ds z result input origin base ys ∧
      n≤d.lookahead.toNat ∧ d.strstart.toNat+n≤result.strstart.toNat ∧
      fillEnd result=fillEnd d ∧ SlowRecordFrame d result ∧ xs<+:ys ∧
      ByteFrame h after (DeflateOwned ds d) ∧ final.ret=none ∧ final.brk=false ∧ OrdinaryCheckpoint result := by
  induction budget generalizing h d xs st with
  | zero =>
    have checkpoint : OrdinaryCheckpoint d := Or.inl (by omega)
    exact ⟨0,st,h,d,xs,.nil st h,boundary,Nat.zero_le _,by omega,rfl,rfl,List.prefix_refl xs,
      ByteFrame.refl h _,running,unbroken,checkpoint⟩
  | succ k ih =>
    by_cases checkpoint : OrdinaryCheckpoint d
    · exact ⟨0,st,h,d,xs,.nil st h,boundary,Nat.zero_le _,by omega,rfl,rfl,List.prefix_refl xs,
        ByteFrame.refl h _,running,unbroken,checkpoint⟩
    · have look : 262≤d.lookahead.toNat := by unfold OrdinaryCheckpoint at checkpoint;omega
      have room : d.sym_next.toNat+3<d.sym_end.toNat := by unfold OrdinaryCheckpoint at checkpoint;omega
      obtain ⟨next,nextHeap,nextD,nextYs,body,content,record,advance,less,endpoint,symbols,storage,ret,brk⟩ :=
        local_content_running_body boundary look room output flush st running unbroken
      obtain ⟨n,final,after,result,ys,trace,contentA,count,startA,endpointA,recordA,symbolsA,storageA,retA,brkA,checkpointA⟩ :=
        ih content (by omega) next ret brk
      rw [record_owned record ds] at storageA
      exact ⟨n+1,final,after,result,ys,.step ⟨d,boundary.state.live.hs,look,room⟩ unbroken running body trace,contentA,by omega,by omega,
        endpointA.trans endpoint,record.trans recordA,symbols.trans symbolsA,storage.trans storageA,retA,brkA,checkpointA⟩

/-- This is a prefix of the real full-fuel strategy loop, not an arbitrary
scheduler. Its endpoint must be short lookahead or the last symbol slot,
and the original remaining loop fuel is explicit in the exact continuation. -/
theorem local_content_ordinary_checkpoint {h : Heap} {r : ZStreamRef} {cutoff ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol}
    (boundary : LocalContent h cutoff r ds z d input origin base xs)
    (output : z.avail_out≠0) (flush : Int32) :
    ∃ n final after result ys,
      ActualOrdinaryPrefix ds flush n {} h final after ∧
      LocalContent after cutoff r ds z result input origin base ys ∧
      n≤d.lookahead.toNat ∧ d.strstart.toNat+n≤result.strstart.toNat ∧
      fillEnd result=fillEnd d ∧ SlowRecordFrame d result ∧ xs<+:ys ∧
      ByteFrame h after (DeflateOwned ds d) ∧ final.ret=none ∧ final.brk=false ∧ OrdinaryCheckpoint result ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc=h.nalloc ∧ after.nextBlk=h.nextBlk ∧
      cwhile forever (deflate_slow_body (some (.tab ds)) flush) {} h=
        cwhile.go forever (deflate_slow_body (some (.tab ds)) flush) (fuel-n) final after ∧
      expandSymbols ys (inputPrefix input base)=inputPrefix input (origin+result.strstart.toNat-pendingCredit result) := by
  obtain ⟨n,final,after,result,ys,trace,content,count,start,endpoint,record,symbols,storage,ret,brk,checkpoint⟩ :=
    ordinary_prefix_bounded d.lookahead.toNat boundary (Nat.le_refl _) output flush {} rfl rfl
  obtain ⟨shape,frame,alloc,ids⟩ := trace.resources boundary
  have maxLook := UInt32.toNat_lt d.lookahead
  have enoughFuel : n≤fuel := by change n≤2^64;omega
  have restoreFuel : n+(fuel-n)=fuel := by omega
  have continuation := trace.continuation (fuel-n)
  rw [restoreFuel] at continuation
  exact ⟨n,final,after,result,ys,trace,content,count,start,endpoint,record,symbols,storage,ret,brk,checkpoint,shape,frame,full_shape_live_change shape,alloc,ids,
    continuation,content.expands⟩

end ZlibF.Spec.Public.Proofs.CompressLocalContentLoop
