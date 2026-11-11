import ZlibF.Proof.«inflate.c.default-view-input-progress»
import ZlibF.Proof.«inflate.c.ret-loop»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

def OrdinaryPublicCode (code : Int32) : Prop :=
  code = Z_OK ∨ code = Z_STREAM_END ∨ code = Z_DATA_ERROR ∨ code = Z_BUF_ERROR

def PublicInflateCode (code : Int32) : Prop :=
  code = Z_OK ∨ code = Z_STREAM_END ∨ code = Z_NEED_DICT ∨ code = Z_STREAM_ERROR ∨
    code = Z_DATA_ERROR ∨ code = Z_MEM_ERROR ∨ code = Z_BUF_ERROR

theorem OrdinaryPublicCode.public {code : Int32} (ordinary : OrdinaryPublicCode code) : PublicInflateCode code := by
  rcases ordinary with ok | ended | data | buffer
  · exact Or.inl ok
  · exact Or.inr (Or.inl ended)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl data))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr buffer)))))

theorem OrdinaryPublicCode.not_memory {code : Int32} (ordinary : OrdinaryPublicCode code) : code ≠ Z_MEM_ERROR := by
  rcases ordinary with rfl | rfl | rfl | rfl
  all_goals decide

theorem leave_return_ordinary_code (l : IL) (flush : Int32) (ret : PublicLeaveRet l) :
    OrdinaryPublicCode (if ((l.in_ - l.have_ == 0 && l.out_ - l.left == 0 || flush == Z_FINISH) &&
      l.ret == Z_OK) then Z_BUF_ERROR else l.ret) := by
  split
  · exact Or.inr (Or.inr (Or.inr rfl))
  · rcases ret with ok | ended | data
    · exact Or.inl ok
    · exact Or.inr (Or.inl ended)
    · exact Or.inr (Or.inr (Or.inl data))

/-- The complete actual body returns only public API codes. Memory errors
retain the original input total, including genuine late window failure.
The output-total timing remains a separate obligation. -/
theorem inflate_default_view_local_return_codes
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {block : Nat} {array : Array UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (local_ : HeaderLocal c h r s (dispatchRegs z s))
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
      (rc = Z_MEM_ERROR → stream.total_in = z.total_in) := by
  obtain ⟨rc, after, stream, state, bytes, used, made, bodyRun, final, finalAllocator,
    get, size, ro, usedBound, madeBound, accounting, totals, progress⟩ :=
    inflate_default_view_local_input_progress E invariant allocator buffers nonnull inputValid local_
      localGet localSize localRo
  refine ⟨rc, after, stream, state, bytes, used, made, bodyRun, final, finalAllocator,
    get, size, ro, usedBound, madeBound, accounting, totals, progress, ?_⟩
  obtain ⟨otherRc, otherHeap, otherZ, otherS, _, exit, regs, loopHeap, loopZ, loopS,
    used2, made2, source, otherFinal, _, _, _, _, run, current, _, _, _, _, _, trace⟩ :=
    inflate_default_view_local_return_trace E invariant allocator buffers nonnull inputValid local_
      localGet localSize localRo
  have same := Except.ok.inj (source.symm.trans bodyRun)
  cases same
  have sameZ : otherZ = stream :=
    Option.some.inj (otherFinal.good.live.hz.symm.trans final.good.live.hz)
  subst otherZ
  cases exit with
  | ret value =>
    obtain ⟨sameRc, _, streamEq, _, direct⟩ := trace
    constructor
    · rw [sameRc]
      rcases direct with needed | memory | refused
      · exact Or.inr (Or.inr (Or.inl needed))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl memory)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl refused)))
    · intro memory
      have valueEq : value = Z_MEM_ERROR := sameRc.symm.trans memory
      obtain ⟨original, _, _⟩ :=
        inflate_run_terminal_direct E invariant buffers nonnull inputValid local_ run (Or.inl valueEq)
      have originalEq : loopZ = z := Option.some.inj (current.good.live.hz.symm.trans original)
      rw [streamEq, originalEq]
  | leave =>
    obtain ⟨_, _, _, _, outcome⟩ := trace
    have ret := inflate_run_leave_ret_codes E invariant buffers nonnull inputValid local_ run
    have selected := leave_return_ordinary_code regs c.flush ret
    rcases outcome with success | failure
    · have ordinary : OrdinaryPublicCode rc := success.1.symm ▸ selected
      exact ⟨ordinary.public, fun memory => False.elim (ordinary.not_memory memory)⟩
    · constructor
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl failure.1)))))
      · intro _
        rw [failure.2.2]
        change loopZ.total_in = z.total_in
        exact InputCounter.inflate_run_leave_input_total E.strm E.st
          invariant.good.live.hz current.good.live.hz run

#print axioms inflate_default_view_local_return_codes
end Zlib.Inflate.Proofs
