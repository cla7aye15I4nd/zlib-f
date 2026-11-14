import ZlibF.Proof.«gz.read-decomp»
import ZlibF.Proof.«inflate.c.stored-call»
import ZlibF.Proof.«inflate.c.terminal-dispatch»
import ZlibF.Proof.«inflate.c.leave-cause-run»
import ZlibF.Proof.«inflate.c.completes-blocked»
import ZlibF.Proof.«inflate.c.completes-observe-avail»

/-!
# inflate.c: a call from `BAD` or `MEM` moves no buffer

From `Good` alone. The entry checks refuse with `Z_STREAM_ERROR` and change no stream. Past them, `inflate_run`
computes exactly: `LOAD` copies the stream counts into the registers, and the first trip of the switch is
`case BAD: ret = Z_DATA_ERROR; goto inf_leave;` or `case MEM: return Z_MEM_ERROR;`.

* `MEM`: the direct return leaves the heap of the entry (with the local `hbuf`), so the stream is unchanged.
* `BAD`: `inf_leave` writes back the registers (`Avail.inflate_leave_avail`), which are the entry counts, and returns
  `Z_MEM_ERROR`, `ret = Z_DATA_ERROR`, or `Z_BUF_ERROR` only when `ret == Z_OK` (`inflate_leave_ret`).

Freeing `hbuf` changes no stream record (`freeB_tables`).
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- `inflate_run` from `BAD`: `LOAD`, then `ret = Z_DATA_ERROR; goto inf_leave;`, with the heap unchanged. -/
theorem stuck_inflate_run_BAD {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (bad : s.mode = BAD) :
    runX (inflate_run c) IL.init h =
      .ok ((.error Ex.leave, { dispatchRegs z s with ret := Z_DATA_ERROR }), h) := by
  unfold inflate_run
  rw [runX_bind, runX_rdS E]
  simp only [bad]
  change runX (do
    LOAD c.strm c.st
    modify fun l => { l with in_ := l.have_, out_ := l.left, ret := Z_OK }
    xwhile (pure true) (inflate_dispatch c)) IL.init h = _
  rw [runX_bind, LOAD_run E]
  simp only []
  rw [runX_bind, runX_modify]
  exact xwhile_run_chain (inflate_dispatch c) (fun _ => dispatchRegs z s) (fun _ => h) 0 (by decide)
    Ex.leave _ _ (fun j hj => absurd hj (Nat.not_lt_zero j)) (inflate_dispatch_BAD_leave E _ bad)

/-- `inflate_run` from `MEM`: `LOAD`, then `return Z_MEM_ERROR;`, with the heap unchanged. -/
theorem stuck_inflate_run_MEM {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (mem : s.mode = MEM) :
    runX (inflate_run c) IL.init h = .ok ((.error (Ex.ret Z_MEM_ERROR), dispatchRegs z s), h) := by
  have terminal : TerminalMode s.mode := Or.inr (Or.inr (Or.inl mem))
  have step := inflate_dispatch_terminal_run E (dispatchRegs z s) terminal
  have exitEq : terminalExit s.mode = .error (Ex.ret Z_MEM_ERROR) := by
    rw [mem]
    unfold terminalExit
    rw [if_neg (by decide), if_pos rfl]
  have regsEq : terminalRegs s.mode (dispatchRegs z s) = dispatchRegs z s := by
    rw [mem]
    unfold terminalRegs
    rw [if_neg (by decide), if_neg (by decide)]
  rw [exitEq, regsEq] at step
  unfold inflate_run
  rw [runX_bind, runX_rdS E]
  simp only [mem]
  change runX (do
    LOAD c.strm c.st
    modify fun l => { l with in_ := l.have_, out_ := l.left, ret := Z_OK }
    xwhile (pure true) (inflate_dispatch c)) IL.init h = _
  rw [runX_bind, LOAD_run E]
  simp only []
  rw [runX_bind, runX_modify]
  exact xwhile_run_chain (inflate_dispatch c) (fun _ => dispatchRegs z s) (fun _ => h) 0 (by decide)
    (Ex.ret Z_MEM_ERROR) _ _ (fun j hj => absurd hj (Nat.not_lt_zero j)) step

end Zlib.Inflate.Proofs

namespace ZlibF.Spec.Public.GzRead
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

theorem inflateStuckNoOutput_holds : InflateStuckNoOutput := by
  intro h r k z st good mode rc after z' run hz
  have live' := Live.syncAlloc good.live
  unfold C.run Zlib.Inflate.inflate at run
  obtain ⟨hbuf, h1, ealloc, run1⟩ := Zlib.Inflate.KeepProofs.bind_ok run
  rw [allocLocalB_run h good.fresh] at ealloc
  cases ealloc
  obtain ⟨res, h2, ebody, run2⟩ := Zlib.Inflate.KeepProofs.bind_ok run1
  obtain ⟨u, h3, efree, run3⟩ := Zlib.Inflate.KeepProofs.bind_ok run2
  cases run3
  obtain ⟨_, str, gzs⟩ := freeB_tables efree
  have getSame : r.get after = r.get h2 := by
    cases r <;> simp [ZStreamRef.get, str, gzs]
  rw [getSame] at hz
  by_cases accepted : (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = false
  · simp only [bind_app, stateCheck_live live', bne_self_eq_false, Bool.false_eq_true, ite_false,
      ldZStream_ok live'.hz, accepted, live'.zst, castI] at ebody
    let c : Ctx := ⟨some r, some (.tab k), syncBuf h, Z_NO_FLUSH⟩
    have E : Env c (syncAlloc h) r k z st := ⟨rfl, rfl, live'.hz, live'.hs⟩
    generalize hR : (ExceptT.run (inflate_run c)).run IL.init (syncAlloc h) = R at ebody
    have erun : runX (inflate_run c) IL.init (syncAlloc h) = R := hR
    rcases mode with bad | mem
    · rw [stuck_inflate_run_BAD E bad] at erun
      subst erun
      dsimp only at ebody
      obtain ⟨z2, get2, availIn, availOut⟩ := Avail.inflate_leave_avail r c rfl _ ebody
      have retCode := inflate_leave_ret c _ _ rc h2 ebody
      rw [get2] at hz
      cases hz
      refine ⟨availIn, availOut, ?_⟩
      rcases retCode with memory | same | ⟨_, ok⟩
      · exact Or.inr (Or.inl memory)
      · exact Or.inl same
      · exact absurd ok (by show Z_DATA_ERROR ≠ Z_OK; decide)
    · rw [stuck_inflate_run_MEM E mem] at erun
      subst erun
      simp only [pure_app] at ebody
      cases ebody
      rw [live'.hz] at hz
      cases hz
      exact ⟨rfl, rfl, Or.inr (Or.inl rfl)⟩
  · have refused : (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = true := by
      cases e : (z.next_out == .null || (z.next_in == .null && z.avail_in != 0))
      · exact absurd e accepted
      · rfl
    simp only [bind_app, stateCheck_live live', bne_self_eq_false, Bool.false_eq_true, ite_false,
      ldZStream_ok live'.hz, refused, ite_true, pure_app] at ebody
    cases ebody
    rw [live'.hz] at hz
    cases hz
    exact ⟨rfl, rfl, Or.inr (Or.inr rfl)⟩

#print axioms Zlib.Inflate.Proofs.stuck_inflate_run_BAD
#print axioms Zlib.Inflate.Proofs.stuck_inflate_run_MEM
#print axioms inflateStuckNoOutput_holds

end ZlibF.Spec.Public.GzRead
