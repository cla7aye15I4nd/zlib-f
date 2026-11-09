import ZlibF.Proof.«uncompr.c.buffers»
import ZlibF.Proof.«inflate.c.local-public-return-codes»

namespace Zlib.Uncompr.Proof.LocalLoop
open C ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.Loop Zlib.Uncompr.Proof.Buffers
set_option autoImplicit false

theorem refilledLocalStateJ (h : Heap) (cutoff b zs : Nat) (z : ZStream) (l : UncLoop)
    (s : InflateState)
    (invariant : LocalStateJ h cutoff (.tab b) zs z s) :
    LocalStateJ (refilledHeap h b z l) cutoff (.tab b) zs (refilledStream z l) s := by
  have hz : h.streams b = some z := invariant.good.live.hz
  have shape := Zlib.Inflate.Proofs.shape_put invariant.good.live.hz (refilledStream z l)
  have put : ZStreamRef.put h (.tab b) (refilledStream z l) = refilledHeap h b z l := by
    simp [ZStreamRef.put, hz, refilledHeap]
  rw [put] at shape
  have win : Zlib.Inflate.Spec.WinInv (refilledHeap h b z l) s := by
    refine { invariant.good.inv.win with block := ?_ }
    simpa only [refilledHeap] using invariant.good.inv.win.block
  have inv : Zlib.Inflate.Spec.StInv (refilledHeap h b z l) zs s :=
    { invariant.good.inv with win := win }
  have tables : Zlib.Inflate.Spec.DataTableInvariant (refilledHeap h b z l) s := by
    intro mode
    exact Zlib.Inflate.Proofs.dataTablesSafe_of_state_static
      (before := h) (after := refilledHeap h b z l) invariant.good.inv.ptr
      rfl rfl (invariant.tables mode)
  have good : LocalGood (refilledHeap h b z l) cutoff (.tab b) zs (refilledStream z l) s := by
    refine ⟨?_, inv, shape.fresh (by rfl) invariant.good.fresh,
      invariant.good.unique.of_shape shape⟩
    exact ⟨by simp [refilledHeap, ZStreamRef.get], invariant.good.live.hs,
      invariant.good.live.zst, invariant.good.live.back, invariant.good.live.mode,
      invariant.good.live.zalloc, invariant.good.live.zfree⟩
  have platform : ZlibF.PlatformMemory.ByteObjectsFit (refilledHeap h b z l) := by
    intro ref a get
    apply invariant.platform ref a
    cases ref <;> simpa only [Space.get, refilledHeap] using get
  exact ⟨⟨good, tables, invariant.pending, invariant.lengths,
    invariant.headerLengths, invariant.held, invariant.window, invariant.wrapper,
    invariant.header, invariant.modes, invariant.trailer, invariant.globals, platform⟩,
    invariant.requestedBits, invariant.requestedWrap, invariant.phase, invariant.roots⟩

/-- The source refill and actual inflate share the same heap and execution.
All returned codes retain exact consumption and production, including late
memory failure. An OK result strictly decreases the outer finite remainder.
This endpoint does not yet claim next-iteration ranges or allocation cleanup. -/
theorem loop_iteration_accounting (h : Heap) (cutoff b zs : Nat) (z : ZStream) (l : UncLoop)
    (s : InflateState) (invariant : LocalStateJ h cutoff (.tab b) zs z s)
    (allocator : DefAlloc z)
    (input : CallerRange h (.tab b) z.next_in (l.len.toNat + z.avail_in.toNat) false)
    (output : CallerRange h (.tab b) z.next_out (l.left.toNat + z.avail_out.toNat) true)
    (separate : Separate z.next_in (l.len.toNat + z.avail_in.toNat)
      z.next_out (l.left.toNat + z.avail_out.toNat)) :
    ∃ rc after stream state used made,
      C.run (loopBody (some (.tab b)) l) h =
        .ok ({ refilledLocals z l with err := rc }, after) ∧
      LocalStateJ after cutoff (.tab b) zs stream state ∧ DefAlloc stream ∧
      StreamAccounting (refilledStream z l) stream used made ∧ PublicInflateCode rc ∧
      (refilledLocals z l).len.toNat + stream.avail_in.toNat + used =
        l.len.toNat + z.avail_in.toNat ∧
      (refilledLocals z l).left.toNat + stream.avail_out.toNat + made =
        l.left.toNat + z.avail_out.toNat ∧
      (rc = Z_OK → used ≠ 0 ∨ made ≠ 0) ∧
      (rc = Z_OK →
        (refilledLocals z l).len.toNat + stream.avail_in.toNat +
          (refilledLocals z l).left.toNat + stream.avail_out.toNat <
          l.len.toNat + z.avail_in.toNat + l.left.toNat + z.avail_out.toNat) := by
  have filledJ := refilledLocalStateJ h cutoff b zs z l s invariant
  have buffers := refilled_stream_buffers h b z l invariant.good.live.hz input output separate
  obtain ⟨rc, after, stream, state, used, made, run, current, finalAllocator,
    localFree, usedBound, madeBound, account, totals, progress, codes, memoryInput⟩ :=
    inflate_default_view_public_return_codes filledJ allocator buffers Z_NO_FLUSH
  have run' := run
  simp only [C.run, refilledHeap] at run'
  have body := loopBody_run h b z l invariant.good.live.hz
  rw [run'] at body
  refine ⟨rc, after, stream, state, used, made, body, current, finalAllocator,
    account, codes, ?_, ?_, progress, ?_⟩
  · have refill := refill_input_count z l
    have count := account.2.2.1
    omega
  · have refill := refill_output_count z l
    have count := account.2.2.2.1
    omega
  · intro ok
    exact iteration_strict_progress z l stream used made account.2.2.1 account.2.2.2.1 (progress ok)

#print axioms refilledLocalStateJ
#print axioms loop_iteration_accounting
end Zlib.Uncompr.Proof.LocalLoop
