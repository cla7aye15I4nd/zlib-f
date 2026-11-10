import ZlibF.Proof.«inflate.c.output-invariant»
import ZlibF.Proof.«inflate.c.stored-call»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual registers after LOAD and the call's initial counter assignments. -/
def dispatchRegs (z : ZStream) (s : InflateState) : IL :=
  { IL.init with put := z.next_out, left := z.avail_out, next := z.next_in, have_ := z.avail_in, hold := s.hold, bits := s.bits, in_ := z.avail_in, out_ := z.avail_out, ret := Z_OK }

/-- The public buffer premise establishes the output clause at LOAD. -/
theorem dispatchRegs_output {h : Heap} {r : ZStreamRef} {z : ZStream} (get : r.get h = some z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null) (s : InflateState) :
    OutputCursorInvariant h r (dispatchRegs z s) := by
  obtain ⟨stream, streamGet, _, output, _⟩ := buffers
  have eq : stream = z := Option.some.inj (streamGet.symm.trans get)
  subst stream
  exact ⟨output, nonnull, Nat.le_refl _, by intro ref off ptr; simp [dispatchRegs]⟩

/-- The returning dispatch loop is the actual source continuation after
TYPE normalization, LOAD and initial counters. Its output invariant is
produced from the public buffer domain on the same returned heap. -/
theorem inflate_run_output_entry_frame_state {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (good : Good h r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null) :
    ∃ after state,
      runX (inflate_run c) IL.init h =
        runX (xwhile (pure true) (inflate_dispatch c)) (dispatchRegs z state) after ∧
      Good after r zs z state ∧ Env c after r zs z state ∧
      OutputCursorInvariant after r (dispatchRegs z state) ∧
      ByteViewSizes h after ∧ DecodeStateFrame s state ∧ after = setI h zs state ∧
      state = (if s.mode = TYPE then { s with mode := TYPEDO } else s) := by
  by_cases type : s.mode = TYPE
  · let state := { s with mode := TYPEDO }
    let after := setI h zs state
    have finalGood : Good after r zs z state := good.decode_update (by rfl)
      (by change HEAD ≤ TYPEDO ∧ TYPEDO ≤ SYNC; decide)
    have env : Env c after r zs z state := ⟨E.strm, E.st, finalGood.live.hz, finalGood.live.hs⟩
    have finalBuffers : StreamBuffers after r := by
      obtain ⟨stream, streamGet, input, output, separate⟩ := buffers
      have eq : stream = z := Option.some.inj (streamGet.symm.trans good.live.hz)
      subst stream
      refine ⟨z, finalGood.live.hz, ?_, ?_, separate⟩
      · exact callerRange_transport good finalGood rfl (fun ref => byte_view_get_setI h zs state ref)
          (fun ref => byte_view_ro_setI h zs state ref) input
      · exact callerRange_transport good finalGood rfl (fun ref => byte_view_get_setI h zs state ref)
          (fun ref => byte_view_ro_setI h zs state ref) output
    refine ⟨after, state, ?_, finalGood, env,
      dispatchRegs_output finalGood.live.hz finalBuffers nonnull state, byte_view_sizes_setI h zs state, by rfl, rfl, by simp only [type, ↓reduceIte]; rfl⟩
    unfold inflate_run
    rw [runX_bind, runX_rdS E]
    simp only [type, beq_self_eq_true, ↓reduceIte]
    rw [runX_bind, runX_setMode E]
    simp only []
    rw [runX_bind, LOAD_run env]
    simp only []
    rw [runX_bind, runX_modify]
    rfl
  · refine ⟨h, s, ?_, good, E, dispatchRegs_output good.live.hz buffers nonnull s,
      ByteViewSizes.refl h, by rfl, by simp [setI, upd_self _ _ _ good.live.hs], by simp only [type, ↓reduceIte]⟩
    unfold inflate_run
    rw [runX_bind, runX_rdS E]
    simp only [type, beq_iff_eq, ↓reduceIte, runX_bind, runX_pure]
    rw [LOAD_run E]
    simp only []
    rw [runX_modify]
    rfl

/-- Projection retaining the previous boundary. -/
theorem inflate_run_output_entry_frame {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (good : Good h r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null) :
    ∃ after state,
      runX (inflate_run c) IL.init h =
        runX (xwhile (pure true) (inflate_dispatch c)) (dispatchRegs z state) after ∧
      Good after r zs z state ∧ Env c after r zs z state ∧
      OutputCursorInvariant after r (dispatchRegs z state) ∧
      ByteViewSizes h after ∧ DecodeStateFrame s state ∧ after = setI h zs state := by
  obtain ⟨after, state, run, finalGood, env, output, sizes, frame, heapEq, _⟩ :=
    inflate_run_output_entry_frame_state E good buffers nonnull
  exact ⟨after, state, run, finalGood, env, output, sizes, frame, heapEq⟩

/-- Projection retaining the initial output-clause boundary. -/
theorem inflate_run_output_entry {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (good : Good h r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null) :
    ∃ after state,
      runX (inflate_run c) IL.init h =
        runX (xwhile (pure true) (inflate_dispatch c)) (dispatchRegs z state) after ∧
      Good after r zs z state ∧ Env c after r zs z state ∧
      OutputCursorInvariant after r (dispatchRegs z state) ∧
      ByteViewSizes h after ∧ DecodeStateFrame s state := by
  obtain ⟨after, state, run, finalGood, env, output, sizes, frame, _⟩ :=
    inflate_run_output_entry_frame E good buffers nonnull
  exact ⟨after, state, run, finalGood, env, output, sizes, frame⟩

/-- Actual readable input supplies the bit-source view after LOAD. The
private held-bit bound belongs to the stream invariant; NULL input with a
nonzero count is rejected by the outer entry before this point. -/
theorem dispatchRegs_input {h : Heap} {r : ZStreamRef} {z : ZStream} {s : InflateState}
    (get : r.get h = some z) (buffers : StreamBuffers h r)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (hold : s.hold.toNat < 2 ^ s.bits.toNat) :
    ∃ bs, BitInv h (dispatchRegs z s) bs ∧
      Separate (dispatchRegs z s).next (dispatchRegs z s).have_.toNat
        (dispatchRegs z s).put (dispatchRegs z s).left.toNat := by
  obtain ⟨stream, streamGet, input, _, separate⟩ := buffers
  have eq : stream = z := Option.some.inj (streamGet.symm.trans get)
  subst stream
  have finishEmpty : z.avail_in = 0 → ∃ bs, BitInv h (dispatchRegs z s) bs ∧
      Separate (dispatchRegs z s).next (dispatchRegs z s).have_.toNat
        (dispatchRegs z s).put (dispatchRegs z s).left.toNat := by
    intro zero
    exact ⟨[], ⟨by change z.avail_in.toNat = 0; rw [zero]; rfl, Or.inl rfl, hold⟩, separate⟩
  rcases input with null | ⟨⟨bytes, readable⟩, _, _⟩
  · exact finishEmpty (inputValid null)
  · rcases readable with ⟨_, zero, _⟩ | ⟨ref, off, array, ptr, arrayGet, fit, contents⟩
    · apply finishEmpty
      exact UInt32.toNat_inj.mp zero
    · have length : bytes.length = z.avail_in.toNat := by
        rw [contents]
        simp only [List.length_take, List.length_drop, Array.length_toList]
        omega
      exact ⟨bytes, ⟨length.symm, Or.inr ⟨ref, array, off, ptr, arrayGet, by omega,
        by simpa only [length] using contents⟩, hold⟩, separate⟩

/-- Both input and output dispatch clauses are established by the real
entry prefix. No loop-body or callee execution contract is assumed. -/
theorem inflate_run_buffers_entry {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (good : Good h r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (hold : s.hold.toNat < 2 ^ s.bits.toNat) :
    ∃ after state bs,
      runX (inflate_run c) IL.init h =
        runX (xwhile (pure true) (inflate_dispatch c)) (dispatchRegs z state) after ∧
      Good after r zs z state ∧ Env c after r zs z state ∧
      OutputCursorInvariant after r (dispatchRegs z state) ∧ BitInv after (dispatchRegs z state) bs ∧
      Separate (dispatchRegs z state).next (dispatchRegs z state).have_.toNat
        (dispatchRegs z state).put (dispatchRegs z state).left.toNat ∧
      ByteViewSizes h after ∧ DecodeStateFrame s state ∧ after = setI h zs state := by
  obtain ⟨after, state, run, finalGood, env, output, sizes, frame, heapEq⟩ :=
    inflate_run_output_entry_frame E good buffers nonnull
  have currentBuffers : StreamBuffers after r := by
    obtain ⟨stream, streamGet, input, out, separate⟩ := buffers
    have eq : stream = z := Option.some.inj (streamGet.symm.trans good.live.hz)
    subst stream
    refine ⟨z, finalGood.live.hz, ?_, ?_, separate⟩
    · apply callerRange_transport good finalGood (by rw [frame]) _ _ input
      · intro ref
        rw [heapEq, byte_view_get_setI]
      · intro ref
        rw [heapEq, byte_view_ro_setI]
    · apply callerRange_transport good finalGood (by rw [frame]) _ _ out
      · intro ref
        rw [heapEq, byte_view_get_setI]
      · intro ref
        rw [heapEq, byte_view_ro_setI]
  obtain ⟨bs, inv, separate⟩ := dispatchRegs_input (s := state) finalGood.live.hz currentBuffers inputValid (by rw [frame]; exact hold)
  exact ⟨after, state, bs, run, finalGood, env, output, inv, separate, sizes, frame, heapEq⟩

/-- The actual entry prefix establishes the same complete buffer relation
which literal and match dispatch steps preserve. -/
theorem inflate_run_dispatch_entry {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (good : Good h r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (hold : s.hold.toNat < 2 ^ s.bits.toNat) :
    ∃ after state bs,
      runX (inflate_run c) IL.init h =
        runX (xwhile (pure true) (inflate_dispatch c)) (dispatchRegs z state) after ∧
      Good after r zs z state ∧ Env c after r zs z state ∧
      DispatchBuffers after r (dispatchRegs z state) bs ∧
      ByteViewSizes h after ∧ DecodeStateFrame s state ∧ after = setI h zs state := by
  obtain ⟨after, state, bs, run, finalGood, env, output, inv, separate, sizes, frame, heapEq⟩ :=
    inflate_run_buffers_entry E good buffers nonnull inputValid hold
  obtain ⟨stream, streamGet, input, _, _⟩ := buffers
  have eq : stream = z := Option.some.inj (streamGet.symm.trans good.live.hz)
  subst stream
  have currentInput : CallerRange after r z.next_in z.avail_in.toNat false := by
    apply callerRange_transport good finalGood (by rw [frame]) _ _ input
    · intro ref
      rw [heapEq, byte_view_get_setI]
    · intro ref
      rw [heapEq, byte_view_ro_setI]
  exact ⟨after, state, bs, run, finalGood, env, ⟨currentInput, output, separate, inv⟩, sizes, frame, heapEq⟩

end Zlib.Inflate.Proofs
