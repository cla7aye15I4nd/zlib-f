import ZlibF.Proof.«inflate.c.live-frame-leave»
import ZlibF.Proof.«inflate.c.default-view-return»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Attach the actual main-loop and leave ledgers to an actual complete
returning body. Safety and termination are supplied by the existing real
default execution theorem; this argument assumes no callee contract. -/
theorem inflate_default_view_local_live_public
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} {rc : Int32}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (run : (do
      let (result, regs) ← runX (inflate_run c) IL.init
      match result with
      | .error (.ret value) => pure value
      | _ => inflate_leave c regs) h = .ok (rc, after))
    (final : Good after r zs stream state) :
    LiveChange h after (fun b => InflateOwned zs state b ∧ ¬ h.live b) (fun _ => False) := by
  obtain ⟨bs, exit, regs, heap0, stream0, state0, _, _, _, loop, current,
    packet, bits, _, _, _, _, _, _, currentAllocator⟩ :=
    inflate_run_default_view_framed E invariant allocator buffers nonnull inputValid
  have live0 : heap0.live = h.live := congrArg (fun x => x.2.2.2.2.2.2)
    (fastMemoryMetaFrameX_inflate_run r c E.strm IL.init h (.error exit) regs heap0 loop)
  rw [bind_app, loop] at run
  cases exit with
  | ret value =>
    change Except.ok (value, heap0) = Except.ok (rc, after) at run
    cases run
    exact good_live_change_of_eq final live0
  | leave =>
    change inflate_leave c regs heap0 = .ok (rc, after) at run
    have env0 : Env c heap0 r zs stream0 state0 :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    have ledger := inflate_leave_live_public env0 current currentAllocator packet bits run final
    simpa only [LiveChange, live0] using ledger

/-- Freeing an existing unique byte allocation removes exactly its block. -/
theorem live_free_local_iff {h : Heap} {block : Nat} {array : Array UInt8}
    (uniq : Uniq h) (get : h.bytes block = some array) (b : Nat) :
    (freeWin h (.ref (.blk block) 0)).live b ↔ h.live b ∧ b ≠ block := by
  by_cases same : b = block
  · subst b
    obtain ⟨words, streams, headers, dstates, istates, gzstates⟩ := Uniq.bytes_only uniq get
    simp [Heap.live, freeWin, words, streams, headers, dstates, istates, gzstates]
  · simp only [Heap.live, freeWin, upd_ne _ _ _ _ same]
    simp [same]

/-- Cancel the actual temporary local allocation and free. The decoder's
returned owned state/window cannot be that four-byte temporary object. -/
theorem public_live_cancel_local {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {stream : ZStream} {state : InflateState} {array : Array UInt8}
    (fresh : Fresh h) (invariant : DefaultStateJ after r zs stream state)
    (get : after.bytes h.nextBlk = some array) (size : array.size = 4)
    (ledger : LiveChange (syncAlloc h) after
      (fun b => InflateOwned zs state b ∧ ¬ (syncAlloc h).live b) (fun _ => False)) :
    LiveChange h (freeWin after (syncBuf h))
      (fun b => InflateOwned zs state b ∧ ¬ h.live b) (fun _ => False) := by
  have outside := default_local_outside invariant.good get size invariant.window.1
  have notOwned : ¬ InflateOwned zs state h.nextBlk := fun owned => outside (Or.inr owned)
  have dead : ¬ h.live h.nextBlk := fresh h.nextBlk (Nat.le_refl _)
  intro b
  have freed := live_free_local_iff invariant.good.uniq get b
  have allocated := live_syncAlloc (h := h) b
  have accounted := ledger b
  change (freeWin after (.ref (.blk h.nextBlk) 0)).live b ↔
    (h.live b ∧ ¬ False) ∨ (InflateOwned zs state b ∧ ¬ h.live b)
  rw [freed]
  by_cases same : b = h.nextBlk
  · subst b
    simp [dead, notOwned]
  · have oldEq : (syncAlloc h).live b ↔ h.live b := by simpa only [same, or_false] using allocated
    have clean : after.live b ↔ h.live b ∨ (InflateOwned zs state b ∧ ¬ h.live b) := by
      simpa only [LiveChange, oldEq, not_false_eq_true, and_true] using ledger b
    simp only [not_false_eq_true, and_true]
    exact (show after.live b ∧ b ≠ h.nextBlk ↔ after.live b from
      ⟨And.left, fun alive => ⟨alive, same⟩⟩).trans clean

#print axioms inflate_default_view_local_live_public
#print axioms public_live_cancel_local
end Zlib.Inflate.Proofs
