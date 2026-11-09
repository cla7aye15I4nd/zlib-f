import ZlibF.Proof.«inflate.c.local-public-resources-live-body»
import ZlibF.Proof.«inflate.c.window-pointer-run»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual loop does not allocate. Its optional leave creates only
one fresh window; early direct returns make no allocation attempt. -/
theorem inflate_default_view_local_origins
    {c : Ctx} {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} {rc : Int32}
    (E : Env c h r zs z s) (invariant : LocalStateJ h cutoff r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (run : (do
      let (result, regs) ← runX (inflate_run c) IL.init
      match result with
      | .error (.ret value) => pure value
      | _ => inflate_leave c regs) h = .ok (rc, after))
    (final : LocalGood after cutoff r zs stream state) :
    ∃ didUpdate : Bool,
      after.nextBlk = h.nextBlk + (if didUpdate = true ∧ s.window = .null ∧ h.allocOk h.nalloc = true then 1 else 0) ∧
      after.nalloc = h.nalloc + (if didUpdate = true ∧ s.window = .null then 1 else 0) ∧
      (state.window = s.window ∨ (s.window = .null ∧ state.window = .ref (.blk h.nextBlk) 0)) := by
  obtain ⟨bs, exit, regs, heap0, stream0, state0, _, _, _, loop, current,
    packet, bits, _, _, _, _, _, _, currentAllocator⟩ :=
    inflate_run_default_view_framed E invariant allocator buffers nonnull inputValid
  have metadata := fastMemoryMetaFrameX_inflate_run r c E.strm IL.init h (.error exit) regs heap0 loop
  have next : heap0.nextBlk = h.nextBlk := congrArg (fun x => x.2.1) metadata
  have alloc : heap0.nalloc = h.nalloc := congrArg (fun x => x.2.2.1) metadata
  have oracle : heap0.allocOk = h.allocOk := congrArg (fun x => x.2.2.2.2.1) metadata
  have window := inflate_run_window_unchanged E.strm E.hs current.good.live.hs loop
  rw [bind_app, loop] at run
  cases exit with
  | ret value =>
    change Except.ok (value, heap0) = Except.ok (rc, after) at run
    cases run
    have states : state = state0 := Option.some.inj (final.live.hs.symm.trans current.good.live.hs)
    exact ⟨false, by simpa using next, by simpa using alloc, Or.inl (states ▸ window)⟩
  | leave =>
    change inflate_leave c regs heap0 = .ok (rc, after) at run
    have env0 : Env c heap0 r zs stream0 state0 :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    have effect := inflate_leave_effects_local env0 current currentAllocator packet bits run final
    let didUpdate := (state0.wsize != 0 || (regs.out_ != regs.left && state0.mode < BAD &&
      (state0.mode < CHECK || c.flush != Z_FINISH)))
    exact ⟨didUpdate, by simpa only [didUpdate, next, alloc, oracle, window] using effect⟩

/-- Fresh returned windows cannot capture a pre-existing caller object.
This relation is about exactly the live incoming objects. -/
theorem local_owned_old_iff_of_origin {h : Heap} {zs : Nat} {s state : InflateState}
    (fresh : Fresh h)
    (origin : state.window = s.window ∨ (s.window = .null ∧ state.window = .ref (.blk h.nextBlk) 0)) :
    ∀ b, h.live b → (InflateOwned zs state b ↔ InflateOwned zs s b) := by
  intro b live
  rcases origin with old | ⟨null, window⟩
  · simp only [InflateOwned, old]
  · have different : b ≠ h.nextBlk := by
      intro same
      subst b
      exact fresh _ (Nat.le_refl _) live
    simp [InflateOwned, window, null, Ne.symm different]

#print axioms inflate_default_view_local_origins
#print axioms local_owned_old_iff_of_origin
end Zlib.Inflate.Local
