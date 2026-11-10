import ZlibF.Proof.«inflate.c.metadata-mode-output-frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual stream/state update leaves every caller byte view unchanged.
Its metadata frame permits monotone allocation counters. -/
theorem RecordFrame.stream_state {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (hz : r.get h = some z) (hs : h.istates zs = some s)
    (stream : ZStream) (state : InflateState) :
    RecordFrame r (some (.tab zs)) h (Zlib.Inflate.Spec.setI (r.put h stream) zs state) := by
  have get : (r.put h stream).istates zs = some s := by simpa using hs
  exact (RecordFrame.put_stream hz (some (.tab zs)) stream).trans (RecordFrame.setI r zs get state)

/-- Attach the exact heap image already proved for the real CODELENS
reading loop. Safety and termination are established by its existing run. -/
theorem clRead_record_frame {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l regs : IL} {bs : List UInt8} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CODELENS)
    (run : runX (clRead c) l h = .ok ((outcome, regs), after)) :
    RecordFrame r (some (.tab zs)) h after := by
  obtain ⟨outcome2, regs2, after2, run2, full, _⟩ :=
    clRead_run_full_cursor E.strm E.st E.hz E.hs invariant.good.inv.wf.1 mode invariant.lengths buffers.bits
  rw [run] at run2
  cases run2
  obtain ⟨stream, _, _, state, heapEq⟩ := full.2
  rw [heapEq]
  exact RecordFrame.stream_state E.hz E.hs stream state

/-- Both actual constructors and their refusal branches have the private
record frame before the real LEN_ continuation. -/
theorem clTail_default_record_boundary {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (modes : s.mode = BAD ∨ s.mode = CODELENS)
    (done : s.mode = CODELENS → s.«have».toNat = s.nlen.toNat + s.ndist.toNat)
    (format : s.wrap = 0 ∨ s.flags = 0) :
    (∃ ret after stream state,
      runX (clTail c) l h = .ok ((.ok (), { l with ret := ret }), after) ∧
      DefaultStateJ after r zs stream state ∧ DefaultConfigFrame s state ∧
      RecordFrame r (some (.tab zs)) h after ∧ state.mode = BAD ∧
      DispatchBuffers after r { l with ret := ret } bs ∧ ByteViewSizes h after ∧ after.static = h.static) ∨
    (∃ after state, DefaultStateJ after r zs z state ∧ DefaultConfigFrame s state ∧
      RecordFrame r (some (.tab zs)) h after ∧ state.mode = LEN_ ∧
      DispatchBuffers after r { l with ret := 0 } bs ∧ ByteViewSizes h after ∧ after.static = h.static ∧
      (runX (clTail c) l h = if c.flush = Z_TREES then .ok ((.error Ex.leave, { l with ret := 0 }), after)
        else runX (inflate_LEN_ c) { l with ret := 0 } after)) := by
  rcases clTail_buffers E invariant.good invariant.pending buffers modes invariant.lengths done with bad | ready
  · obtain ⟨ret, after, stream, state, run, current, mode, tables, pending, packet, sizes, static, update⟩ := bad
    have base := invariant.toDefaultDecodeJ.table_update current tables pending sizes static update (Or.inl mode)
    have config : DefaultConfigFrame s state := by rw [update.2.2]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    have frame : RecordFrame r (some (.tab zs)) h after := by
      rw [update.1]
      exact RecordFrame.stream_state E.hz E.hs stream state
    exact Or.inl ⟨ret, after, stream, state, run,
      invariant.config_update base config format, config, frame, mode, packet, sizes, static⟩
  · obtain ⟨after, state, current, mode, tables, pending, packet, sizes, static, run, update⟩ := ready
    have base := invariant.toDefaultDecodeJ.table_update current tables pending sizes static update (Or.inr mode)
    have config : DefaultConfigFrame s state := by rw [update.2.2]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    have frame : RecordFrame r (some (.tab zs)) h after := by
      rw [update.1]
      exact RecordFrame.stream_state E.hz E.hs z state
    exact Or.inr ⟨after, state, invariant.config_update base config format, config, frame, mode, packet, sizes, static, run⟩

end Zlib.Inflate.Proofs
