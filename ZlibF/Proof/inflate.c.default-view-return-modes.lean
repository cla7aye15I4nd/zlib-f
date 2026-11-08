import ZlibF.Proof.«inflate.c.default-view-return-codes»
import ZlibF.Proof.«inflate.c.return-mode-run»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

def ReturnedModes (code : Int32) (state : InflateState) : Prop :=
  (code = Z_STREAM_END → state.mode = DONE) ∧
  (code = Z_NEED_DICT → state.mode = DICT) ∧
  (code = Z_DATA_ERROR → state.mode = BAD) ∧
  (code = Z_MEM_ERROR → state.mode = MEM)

theorem ReturnedModes.direct {code : Int32} {state : InflateState}
    (direct : DirectInflateCode code) (needed : code = Z_NEED_DICT → state.mode = DICT)
    (memory : code = Z_MEM_ERROR → state.mode = MEM) : ReturnedModes code state := by
  refine ⟨?_, needed, ?_, memory⟩
  · intro ended
    rcases direct with need | mem | stream
    · exact False.elim ((by decide : Z_STREAM_END ≠ Z_NEED_DICT) (ended.symm.trans need))
    · exact False.elim ((by decide : Z_STREAM_END ≠ Z_MEM_ERROR) (ended.symm.trans mem))
    · exact False.elim ((by decide : Z_STREAM_END ≠ Z_STREAM_ERROR) (ended.symm.trans stream))
  · intro error
    rcases direct with need | mem | stream
    · exact False.elim ((by decide : Z_DATA_ERROR ≠ Z_NEED_DICT) (error.symm.trans need))
    · exact False.elim ((by decide : Z_DATA_ERROR ≠ Z_MEM_ERROR) (error.symm.trans mem))
    · exact False.elim ((by decide : Z_DATA_ERROR ≠ Z_STREAM_ERROR) (error.symm.trans stream))

theorem ReturnedModes.memory {state : InflateState} (mode : state.mode = MEM) : ReturnedModes Z_MEM_ERROR state :=
  ReturnedModes.direct (Or.inr (Or.inl rfl))
    (fun impossible => False.elim ((by decide : Z_MEM_ERROR ≠ Z_NEED_DICT) impossible)) (fun _ => mode)

theorem leave_return_original_ret {rc : Int32} {l : IL} {flush : Int32}
    (selected : rc = if ((l.in_ - l.have_ == 0 && l.out_ - l.left == 0 || flush == Z_FINISH) &&
      l.ret == Z_OK) then Z_BUF_ERROR else l.ret) (notBuffer : rc ≠ Z_BUF_ERROR) : rc = l.ret := by
  split at selected
  · exact False.elim (notBuffer selected)
  · exact selected

theorem ReturnedModes.ordinary {rc : Int32} {l : IL} {flush : Int32} {state : InflateState}
    (ordinary : OrdinaryPublicCode rc)
    (selected : rc = if ((l.in_ - l.have_ == 0 && l.out_ - l.left == 0 || flush == Z_FINISH) &&
      l.ret == Z_OK) then Z_BUF_ERROR else l.ret)
    (ended : l.ret = Z_STREAM_END → state.mode = DONE)
    (error : l.ret = Z_DATA_ERROR → state.mode = BAD) : ReturnedModes rc state := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro code
    have notBuffer : rc ≠ Z_BUF_ERROR := by rw [code]; decide
    exact ended ((leave_return_original_ret selected notBuffer).symm.trans code)
  · intro need
    rcases ordinary with rfl | rfl | rfl | rfl
    all_goals exact False.elim (by revert need; decide)
  · intro code
    have notBuffer : rc ≠ Z_BUF_ERROR := by rw [code]; decide
    exact error ((leave_return_original_ret selected notBuffer).symm.trans code)
  · intro memory
    exact False.elim (ordinary.not_memory memory)

/-- The complete actual returning body has the public terminal mode
clauses, including genuine window allocation failure into MEM. -/
theorem inflate_default_view_local_return_modes
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {block : Nat} {array : Array UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (localGet : h.bytes block = some array) (localSize : array.size = 4) (localRo : h.ro block = false) :
    ∃ rc after stream state bytes used made,
      (do
        let (result, regs) ← runX (inflate_run c) IL.init
        match result with
        | .error (.ret value) => pure value
        | _ => inflate_leave c regs) h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧
      after.bytes block = some bytes ∧ bytes.size = 4 ∧ after.ro block = false ∧
      used ≤ z.avail_in.toNat ∧ made ≤ z.avail_out.toNat ∧ StreamAccounting z stream used made ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_DATA_ERROR ∨ rc = Z_BUF_ERROR →
        stream.total_in = z.total_in + UInt64.ofNat used) ∧
      (rc = Z_OK → used ≠ 0 ∨ made ≠ 0) ∧ PublicInflateCode rc ∧
      (rc = Z_MEM_ERROR → stream.total_in = z.total_in) ∧ ReturnedModes rc state := by
  obtain ⟨rc, after, stream, state, bytes, used, made, bodyRun, final, finalAllocator,
    get, size, ro, usedBound, madeBound, accounting, totals, progress, codes, memoryInput⟩ :=
    inflate_default_view_local_return_codes E invariant allocator buffers nonnull inputValid
      localGet localSize localRo
  refine ⟨rc, after, stream, state, bytes, used, made, bodyRun, final, finalAllocator,
    get, size, ro, usedBound, madeBound, accounting, totals, progress, codes, memoryInput, ?_⟩
  obtain ⟨otherRc, otherHeap, otherZ, otherS, _, exit, regs, loopHeap, loopZ, loopS,
    used2, made2, source, otherFinal, _, _, _, _, run, current, _, _, _, _, _, trace⟩ :=
    inflate_default_view_local_return_trace E invariant allocator buffers nonnull inputValid
      localGet localSize localRo
  have same := Except.ok.inj (source.symm.trans bodyRun)
  cases same
  have sameS : otherS = state :=
    Option.some.inj (otherFinal.good.live.hs.symm.trans final.good.live.hs)
  subst otherS
  obtain ⟨returned, privateGet, needMode, memoryMode, leaveModes⟩ :=
    inflate_run_return_modes E invariant buffers nonnull inputValid run
  have stateEq : returned = loopS := Option.some.inj (privateGet.symm.trans current.good.live.hs)
  subst returned
  cases exit with
  | ret value =>
    obtain ⟨sameRc, _, _, sameState, direct⟩ := trace
    rw [sameRc, sameState]
    exact ReturnedModes.direct direct (fun code => needMode (congrArg Ex.ret code))
      (fun code => memoryMode (congrArg Ex.ret code))
  | leave =>
    obtain ⟨_, _, _, _, outcome⟩ := trace
    rcases outcome with success | failure
    · obtain ⟨ended, error⟩ := leaveModes rfl
      have ordinary := leave_return_ordinary_code regs c.flush
        (inflate_run_leave_ret_codes E invariant buffers nonnull inputValid run)
      have selected : OrdinaryPublicCode rc := success.1.symm ▸ ordinary
      apply ReturnedModes.ordinary selected success.1
      · intro code
        rw [success.2.2]
        exact ended code
      · intro code
        rw [success.2.2]
        exact error code
    · rw [failure.1]
      exact ReturnedModes.memory failure.2.1

#print axioms inflate_default_view_local_return_modes
end Zlib.Inflate.Proofs
