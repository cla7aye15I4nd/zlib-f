import ZlibF.Proof.«compress.c.local-slide-content»

/-! # Same-execution ordinary-body storage and loop control -/
namespace ZlibF.Spec.Public.Proofs.CompressLocalContentBodyStep
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalInit ZlibF.Spec.Public.Proofs.CompressLocalHash
open ZlibF.Spec.Public.Proofs.CompressLocalContent ZlibF.Spec.Public.Proofs.CompressLocalBodyHistory
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Recover byte effects and the exact stop reason on any observed same
ordinary body execution. This invokes the proved actual body, then equates
its result with the observation; it assumes no callee contract. -/
theorem local_body_observed_control {h after : Heap} {r : ZStreamRef} {cutoff ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol} {next : LoopS}
    (boundary : LocalContent h cutoff r ds z d input origin base xs)
    (look : 262≤d.lookahead.toNat) (room : d.sym_next.toNat+3<d.sym_end.toNat)
    (flush : Int32) (st : LoopS)
    (actual : deflate_slow_body (some (.tab ds)) flush st h=.ok (next,after)) :
    ByteFrame h after (DeflateOwned ds d) ∧
      (next.ret=some need_more → st.ret=some need_more ∨ z.avail_out=0) := by
  obtain ⟨w,p,q,wa,pa,qa,env,chains⟩ := local_heap_chains_environment boundary.state boundary.chains
  obtain ⟨wb,bytes,win,get,view,form⟩ := boundary.data
  have wid : wb=w := BRef.blk.inj (Ptr.ref.inj (win.symm.trans env.win)).1
  subst wb
  have array : bytes=wa := Option.some.inj (get.symm.trans env.wbytes)
  subst bytes
  obtain ⟨expected,expectedHeap,result,ys,run,_state,_chains,_win,_bytes,_range,_endpoint,
      _advance,_less,_form,_history,_deferred,_strict,_brk,_ret,_symbols,_step,_record,_values,frame,reason⟩ :=
    local_body_history_symbols boundary.state boundary.symbols env chains (Nat.le_refl _)
      boundary.range look boundary.history boundary.deferred view (form (by omega)) room flush st
  have same := Prod.mk.inj (Except.ok.inj (run.symm.trans actual))
  rw [same.2] at frame
  rw [same.1] at reason
  exact ⟨frame,reason⟩

/-- Nonfull ordinary bodies cannot return need_more while the unchanged
output offer is positive. All three actual decision branches are covered. -/
theorem local_content_running_body {h : Heap} {r : ZStreamRef} {cutoff ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol}
    (boundary : LocalContent h cutoff r ds z d input origin base xs)
    (look : 262≤d.lookahead.toNat) (room : d.sym_next.toNat+3<d.sym_end.toNat)
    (output : z.avail_out≠0) (flush : Int32) (st : LoopS) (running : st.ret=none) (unbroken : st.brk=false) :
    ∃ next after result ys,
      deflate_slow_body (some (.tab ds)) flush st h=.ok (next,after) ∧
      LocalContent after cutoff r ds z result input origin base ys ∧ SlowRecordFrame d result ∧
      d.strstart.toNat<result.strstart.toNat ∧ result.lookahead.toNat<d.lookahead.toNat ∧
      fillEnd result=fillEnd d ∧ xs<+:ys ∧
      ByteFrame h after (DeflateOwned ds d) ∧ next.ret=none ∧ next.brk=false := by
  obtain ⟨next,after,result,ys,run,content,record,start,less,endpoint,symbols,_strict,brk,ret⟩ :=
    local_content_body boundary look room flush st
  obtain ⟨storage,reason⟩ := local_body_observed_control boundary look room flush st run
  have nextRunning : next.ret=none := by
    rcases ret with same | returned
    · exact same.trans running
    · rcases reason returned with impossible | zero
      · rw [running] at impossible;cases impossible
      · exact False.elim (output zero)
  have prefixSymbols : xs<+:ys := by
    rcases symbols with same | ⟨symbol,appended⟩
    · rw [same];exact List.prefix_refl xs
    · rw [appended];exact List.prefix_append xs [symbol]
  exact ⟨next,after,result,ys,run,content,record,start,less,endpoint,prefixSymbols,storage,nextRunning,brk.trans unbroken⟩

theorem record_owned {d result : DeflateState} (record : SlowRecordFrame d result) (ds : Nat) :
    DeflateOwned ds result=DeflateOwned ds d := by
  unfold SlowRecordFrame at record
  rw [record]
  rfl

end ZlibF.Spec.Public.Proofs.CompressLocalContentBodyStep
