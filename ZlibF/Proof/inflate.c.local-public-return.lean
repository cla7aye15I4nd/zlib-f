import ZlibF.Proof.«inflate.c.local-run»
import ZlibF.Proof.«inflate.c.local-public-storage»
import ZlibF.Proof.«inflate.c.local-leave-resources»
import ZlibF.Proof.«inflate.c.default-view-return»

/-! Complete actual body/leave and public temporary-storage return boundary. -/
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

theorem default_local_outside {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} {block : Nat} {array : Array UInt8} (good : LocalGood h cutoff r zs z s) (roots : LocalRoots cutoff r zs s)
    (get : h.bytes block = some array) (size : array.size = 4) (bits : s.wbits = 15) :
    ¬ (StreamRoot r block ∨ InflateOwned zs s block) := by
  have notState : block ≠ zs := by
    intro same
    subst block
    have unique := good.unique zs roots.state
    simp only [get, good.live.hs, cnt_some] at unique
    omega
  have notRoot : ¬ StreamRoot r block := by
    cases r with
    | tab index =>
      intro same
      change block = index at same
      subst block
      have unique := good.unique index (roots.stream index rfl)
      have hz : h.streams index = some z := good.live.hz
      simp only [get, hz, cnt_some] at unique
      omega
    | in_gzstate_strm index =>
      intro same
      change block = index at same
      subst block
      obtain ⟨g, gzGet, eq⟩ := Option.map_eq_some_iff.mp good.live.hz
      have unique := good.unique index (roots.stream index rfl)
      simp only [get, gzGet, cnt_some] at unique
      omega
  rintro (root | (state | window))
  · exact notRoot root
  · exact notState state
  · exact default_local_not_window good get size bits window

theorem inflate_run_default_view_framed
    {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s)
    (invariant : LocalStateJ h cutoff r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0) :
    ∃ (bs : List UInt8), ∃ exit regs after stream state used made, used ≤ bs.length ∧
      runX (inflate_run c) IL.init h = .ok ((.error exit, regs), after) ∧
      LocalStateJ after cutoff r zs stream state ∧ DispatchBuffers after r regs (bs.drop used) ∧
      regs.bits.toNat ≤ 39 ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance z.next_in used ∧ regs.have_.toNat + used = z.avail_in.toNat ∧
      regs.put = inputAdvance z.next_out made ∧ regs.left.toNat + made = z.avail_out.toNat ∧
      StreamRootFrame r h after ∧ DefAlloc stream := by
  obtain ⟨bs, exit, regs, after, stream, state, used, made, bound, run, final,
    packet, bits, sizes, next, count, put, left⟩ :=
    inflate_run_default_view E invariant buffers nonnull inputValid
  have frame := streamFrameX_inflate_run r c E.strm IL.init h (.error exit) regs after run
  exact ⟨bs, exit, regs, after, stream, state, used, made, bound, run, final,
    packet, bits, sizes, next, count, put, left, frame,
    frame.allocator invariant.good.live.hz final.good.live.hz allocator⟩


/-- The actual full mode loop and each actual leave/direct return preserve
the full local relation and the live four-byte public-call temporary. -/
theorem inflate_default_view_local_state_return
    {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {block : Nat} {array : Array UInt8}
    (E : Env c h r zs z s) (invariant : LocalStateJ h cutoff r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (localGet : h.bytes block = some array) (localSize : array.size = 4) (localRo : h.ro block = false) :
    ∃ rc after stream state bytes,
      (do
        let (result, regs) ← runX (inflate_run c) IL.init
        match result with
        | .error (.ret value) => pure value
        | _ => inflate_leave c regs) h = .ok (rc, after) ∧
      LocalStateJ after cutoff r zs stream state ∧ DefAlloc stream ∧
      after.bytes block = some bytes ∧ bytes.size = 4 ∧ after.ro block = false := by
  obtain ⟨bs, exit, regs, heap0, stream0, state0, used, made, bound, run, current,
    packet, bits, sizes, next, count, put, left, fixed, currentAllocator⟩ :=
    inflate_run_default_view_framed E invariant allocator buffers nonnull inputValid
  obtain ⟨bytes, byteGet, byteSize⟩ := sizes.view (ref := .blk block) localGet
  change heap0.bytes block = some bytes at byteGet
  have byteSize4 : bytes.size = 4 := byteSize.trans localSize
  have metadata := memoryMetaFrameX_inflate_run r c E.strm IL.init h (.error exit) regs heap0 run
  have roEq : heap0.ro = h.ro := congrArg Prod.fst metadata
  have ro0 : heap0.ro block = false := by rw [roEq]; exact localRo
  cases exit with
  | ret value =>
    refine ⟨value, heap0, stream0, state0, bytes, ?_, current, currentAllocator,
      byteGet, byteSize4, ro0⟩
    rw [bind_app, run]
    rfl
  | leave =>
    have currentEnv : Env c heap0 r zs stream0 state0 :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    obtain ⟨rc, after, stream, state, leaveRun, final, finalAllocator,
      frame, ledger, effects⟩ :=
      inflate_leave_local_resources currentEnv current currentAllocator packet bits
    have live : heap0.live block := Or.inl (by rw [byteGet]; simp)
    have slot := frame.2.2.2.2.2 block live
      (default_local_outside current.good current.roots byteGet byteSize4 current.window)
    refine ⟨rc, after, stream, state, bytes, ?_, final, finalAllocator,
      slot.1.trans byteGet, byteSize4, slot.2.2.2.2.2.2.2.trans ro0⟩
    rw [bind_app, run]
    exact leaveRun

#print axioms default_local_outside
#print axioms inflate_run_default_view_framed
#print axioms inflate_default_view_local_state_return
end Zlib.Inflate.Local
