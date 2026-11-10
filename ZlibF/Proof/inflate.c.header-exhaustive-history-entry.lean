import ZlibF.Proof.«inflate.c.header-exhaustive-stored-lens»
namespace Zlib.Inflate.Proofs.HeaderPhaseView
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The public header phases or the actual private payload continuation.
This common outcome never forces a payload-running call to remain in a
header mode or to produce no public output. -/
def HeaderProgress (h after : Heap) (r : ZStreamRef) (zs : Nat) (log : DataLog)
    (input output : List UInt8) (used : Nat) (flush rc : Int32) (future rest : List Bool)
    (dict prior decoded : List UInt8) : Prop :=
  Meaning .head after r zs (credit log input output used rc) ∨
  Meaning .block after r zs (credit log input output used rc) ∨
  Meaning .table after r zs (credit log input output used rc) ∨
  Meaning .lens after r zs (credit log input output used rc) ∨
  Meaning .code after r zs (credit log input output used rc) ∨
  PayloadConstructionCut h r zs input flush future rest dict prior decoded

/-- Actual from-init cumulative HEAD history plus independent valid plain
first-dynamic syntax exhaustively drives any ordinary accepted public call.
All waiting modes and both-table completion are produced by the source;
there is no caller premise about the actual reader's outcome or after mode. -/
theorem Epoch.head_dynamic_call_exhaustive
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog} {history : InflateDataTrace 15 r h log}
    {flush rc : Int32} {input output futureBytes bodyBytes : List UInt8} {used last : Nat} {cmf flg : UInt8}
    {middle bodyInput rest : List Bool} {dict prior decoded : List UInt8}
    (selected : Epoch r zs .head history)
    (observed : DataStep .inflate h after r flush rc input output used)
    (flushing : flush ≠ Z_BLOCK ∧ flush ≠ Z_TREES)
    (accepted : ∀ z, r.get h = some z → z.next_out ≠ .null ∧ (z.next_in = .null → z.avail_in = 0))
    (allBytes : (log.input ++ input) ++ futureBytes = [cmf, flg] ++ bodyBytes)
    (valid : Zlib.HeaderOK cmf flg) (plain : flg.toNat / 32 % 2 = 0)
    (first : readBits 1 (bytesBits bodyBytes) = some (last, middle))
    (second : readBits 2 middle = some (2, bodyInput))
    (body : Body dict 2 prior bodyInput rest decoded) :
    HeaderProgress h after r zs log input output used flush rc (bytesBits futureBytes) rest dict prior decoded := by
  rcases selected.head_dynamic_arbitrary_boundary observed flushing accepted allBytes valid plain first second body with
    head | block | ⟨currentRest, entry, currentBody⟩
  · exact Or.inl head
  · exact Or.inr (Or.inl block)
  · have empty : log.output = [] := by obtain ⟨_z, _s, _current, _alloc, _window, empty, _data⟩ := selected.checked.2; exact empty
    exact Or.inr (Or.inr (entry.to_continuation.exhaustive_header selected.checked.1 observed accepted empty currentBody))

/-- A real TYPE boundary resumes with the same exhaustive header outcome
on arbitrary current input and any valid future dynamic continuation. -/
theorem Meaning.block_dynamic_call_exhaustive
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog} {history : InflateDataTrace 15 r h log}
    {flush rc : Int32} {input output : List UInt8} {used last : Nat}
    {future middle bodyInput rest : List Bool} {dict prior decoded : List UInt8}
    (scope : HeaderDataTrace.PlatformScope history) (before : Meaning .block h r zs log)
    (observed : DataStep .inflate h after r flush rc input output used)
    (flushing : flush ≠ Z_BLOCK ∧ flush ≠ Z_TREES)
    (accepted : ∀ z, r.get h = some z → z.next_out ≠ .null ∧ (z.next_in = .null → z.avail_in = 0))
    (first : readBits 1 (bytesBits input ++ future) = some (last, middle))
    (second : readBits 2 middle = some (2, bodyInput))
    (body : Body dict 2 prior bodyInput rest decoded) :
    HeaderProgress h after r zs log input output used flush rc future rest dict prior decoded := by
  rcases before.block_dynamic_arbitrary_boundary scope observed flushing accepted first second body with block | ⟨currentRest, entry, currentBody⟩
  · exact Or.inr (Or.inl block)
  · have empty : log.output = [] := by obtain ⟨_z, _s, _current, _alloc, _window, empty, _data⟩ := before; exact empty
    exact Or.inr (Or.inr (entry.exhaustive_header scope observed accepted empty currentBody))

/-- The stored TABLE phase establishes the actual live continuation at
LOAD, retaining its held word and all original count/block provenance. -/
theorem Meaning.table_actual_continuation
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog} {flush rc : Int32}
    {input output : List UInt8} {used : Nat}
    (before : Meaning .table h r zs log) (observed : DataStep .inflate h after r flush rc input output used)
    (accepted : ∀ z, r.get h = some z → z.next_out ≠ .null ∧ (z.next_in = .null → z.avail_in = 0)) :
    ∃ (z : ZStream) (s : InflateState), r.get h = some z ∧ h.istates zs = some s ∧
      TableContinuation h r zs log input flush (stream (dispatchRegs z s) input) := by
  obtain ⟨z, s, current, _allocator, window, _empty, mode, record, lastBound, last, view⟩ := before
  obtain ⟨nonnull, inputValid⟩ := accepted z current.good.live.hz
  obtain ⟨z0, _returned, get0, _get1, buffers, _active, bytes, _usedEq, _output, _run⟩ := observed
  have sameZ : z0 = z := Option.some.inj (get0.symm.trans current.good.live.hz)
  subst z0
  have B := header_input_view_of_bytes (s := s) bytes current.held
  have allocated := default_origin_syncAlloc current
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have env : Env c (syncAlloc h) r zs z s := ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  have output0 := dispatchRegs_output env.hz (streamBuffers_syncAlloc current.good.fresh buffers) nonnull s
  obtain ⟨z1, get1, range, _outRange, separate⟩ := streamBuffers_syncAlloc current.good.fresh buffers
  have sameZ1 : z1 = z := Option.some.inj (get1.symm.trans env.hz)
  subst z1
  have input0 : BitInv (syncAlloc h) (dispatchRegs z s) input := by
    refine ⟨B.have_eq, ?_, B.hold_lt⟩
    rcases B.next with none | ⟨ref, array, off, pointer, get, bound, values⟩
    · exact Or.inl none
    · exact Or.inr ⟨ref, array, off, pointer, (byte_view_syncAlloc current.good.fresh get).1, bound, values⟩
  refine ⟨z, s, current.good.live.hz, current.good.live.hs, z, z, s, s, dispatchRegs z s, syncAlloc h, 0, record,
    current.good.live.hz, current.good.live.hs, current.good.live.zst, allocated, ?_, Nat.zero_le _, rfl,
    current.good.inv.bits, mode, window, lastBound, last, ?_, rfl, rfl, rfl, ?_, main_loop_entry_not_type env (by rw [mode]; decide)⟩
  · simpa only [List.drop_zero] using (show DispatchBuffers (syncAlloc h) r (dispatchRegs z s) input from ⟨range, output0, separate, input0⟩)
  · simpa only [List.take_zero, List.append_nil, dispatchRegs] using view
  · simp only [dispatchRegs, Nat.add_zero]

/-- Every valid future Body at the stored TABLE cursor is now classified
without a desired reader/constructor outcome as a premise. -/
theorem Meaning.table_public_future_exhaustive
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog} {history : InflateDataTrace 15 r h log}
    {flush rc : Int32} {input output : List UInt8} {used : Nat}
    (scope : HeaderDataTrace.PlatformScope history) (before : Meaning .table h r zs log)
    (observed : DataStep .inflate h after r flush rc input output used)
    (accepted : ∀ z, r.get h = some z → z.next_out ≠ .null ∧ (z.next_in = .null → z.avail_in = 0)) :
    ∃ (z : ZStream) (s : InflateState), r.get h = some z ∧ h.istates zs = some s ∧
      ∀ (future rest : List Bool) (dict prior decoded : List UInt8),
        Body dict 2 prior (stream (dispatchRegs z s) input ++ future) rest decoded →
        HeaderProgress h after r zs log input output used flush rc future rest dict prior decoded := by
  obtain ⟨z, s, getZ, getS, entry⟩ := before.table_actual_continuation observed accepted
  refine ⟨z, s, getZ, getS, ?_⟩
  intro future rest dict prior decoded valid
  have empty : log.output = [] := by obtain ⟨_z, _s, _current, _alloc, _window, empty, _data⟩ := before; exact empty
  exact Or.inr (Or.inr (entry.exhaustive_header scope observed accepted empty valid))

#print axioms Epoch.head_dynamic_call_exhaustive
#print axioms Meaning.block_dynamic_call_exhaustive
#print axioms Meaning.table_actual_continuation
#print axioms Meaning.table_public_future_exhaustive
end Zlib.Inflate.Proofs.HeaderPhaseView
