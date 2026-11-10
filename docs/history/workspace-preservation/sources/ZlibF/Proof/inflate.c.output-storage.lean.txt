import ZlibF.Proof.«inflate.c.default-mode-result»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A live raw byte object cannot also be the stream record. -/
theorem byte_object_not_stream_root {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {block : Nat} {array : Array UInt8}
    (good : Good h r zs z s) (get : h.bytes block = some array) :
    ¬ StreamRoot r block := by
  cases r with
  | tab index =>
    intro same
    change block = index at same
    subst block
    have unique := good.uniq index
    have hz : h.streams index = some z := good.live.hz
    simp only [get, hz, cnt_some] at unique
    omega
  | in_gzstate_strm index =>
    intro same
    change block = index at same
    subst block
    obtain ⟨g, gzGet, eq⟩ := Option.map_eq_some_iff.mp good.live.hz
    have unique := good.uniq index
    simp only [get, gzGet, cnt_some] at unique
    omega

/-- The actual complete body retains the original raw output allocation
and its extent, on every return class. The mode loop may change its bytes.
RESTORE, the window operation and metadata suffix leave those final bytes
unchanged, including on window allocation failure. -/
theorem inflate_body_default_output_storage
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {block offset : Nat} {array : Array UInt8} {rc : Int32}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (allocator : DefAlloc z) (buffers : StreamBuffers h r)
    (raw : RawFastIO (dispatchRegs z s))
    (output : z.next_out = .ref (.blk block) offset) (get : h.bytes block = some array)
    (executed : (do
      let (result, regs) ← runX (inflate_run c) IL.init
      match result with
      | .error (.ret value) => pure value
      | _ => inflate_leave c regs) h = .ok (rc, after)) :
    ∃ bytes, after.bytes block = some bytes ∧ bytes.size = array.size := by
  have nonnull : z.next_out ≠ .null := by rw [output]; simp
  have inputValid : z.next_in = .null → z.avail_in = 0 := by
    obtain ⟨ib, io, ob, oo, input, _, _⟩ := raw
    change z.next_in = .ref (.blk ib) io at input
    rw [input]
    intro impossible
    cases impossible
  obtain ⟨bs, exit, regs, heap0, stream0, state0, used, made, bound, run, current,
    packet, currentRaw, bits, sizes, next, count, put, left, fixed, currentAllocator⟩ :=
    inflate_run_default_raw_framed E invariant allocator buffers nonnull inputValid raw
  obtain ⟨bytes, byteGet, byteSize⟩ := sizes.view (ref := .blk block) get
  cases exit with
  | ret value =>
    have body : (do
      let (result, regs) ← runX (inflate_run c) IL.init
      match result with
      | .error (.ret value) => pure value
      | _ => inflate_leave c regs) h = .ok (value, heap0) := by
      rw [bind_app, run]
      rfl
    have heaps : heap0 = after := congrArg Prod.snd (Except.ok.inj (body.symm.trans executed))
    exact ⟨bytes, heaps ▸ byteGet, byteSize⟩
  | leave =>
    have pointer : regs.put = .ref (.blk block) (offset + made) := by
      rw [put, output]
      rfl
    have unowned : ¬ InflateOwned zs state0 block := by
      intro owned
      rcases packet.output.range with null | ⟨_, _, outside⟩
      · rw [pointer] at null
        cases null
      · exact outside block (by rw [pointer]; rfl)
          ((current.good.streamOwned_iff block).mpr owned)
    have outside : ¬ (StreamRoot r block ∨ InflateOwned zs state0 block) := by
      rintro (root | owned)
      · exact byte_object_not_stream_root current.good byteGet root
      · exact unowned owned
    have currentEnv : Env c heap0 r zs stream0 state0 :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    have statics : Zlib.Crc32.Proofs.StaticsOK heap0 := by
      unfold Zlib.Crc32.Proofs.StaticsOK
      rw [current.globals]
      exact ⟨rfl, rfl⟩
    obtain ⟨value, heap1, stream, state, leaveRun, _, _, _, _, finalGet, _, _⟩ :=
      inflate_leave_local_boundary currentEnv current.good currentAllocator.1 statics
        packet current.tables current.pending bits byteGet outside
    have body : (do
      let (result, regs) ← runX (inflate_run c) IL.init
      match result with
      | .error (.ret value) => pure value
      | _ => inflate_leave c regs) h = .ok (value, heap1) := by
      rw [bind_app, run]
      exact leaveRun
    have heaps : heap1 = after := congrArg Prod.snd (Except.ok.inj (body.symm.trans executed))
    exact ⟨bytes, heaps ▸ finalGet, byteSize⟩

/-- `int inflate(z_streamp strm, int flush)`.
On the same actual public execution, the caller's raw output allocation
survives with its original capacity. All return classes and final local
cleanup are included. The explicit domain is initialized default J and
distinct raw buffers; this is not a caller frame or ownership theorem. -/
theorem inflate_default_raw_output_storage
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {block offset : Nat} {array : Array UInt8} {flush rc : Int32}
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (raw : RawFastIO (dispatchRegs z s))
    (output : z.next_out = .ref (.blk block) offset) (get : h.bytes block = some array)
    (executed : C.run (inflate (some r) flush) h = .ok (rc, after)) :
    ∃ bytes, after.bytes block = some bytes ∧ bytes.size = array.size := by
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have allocated := default_state_syncAlloc invariant
  have env : Env c (syncAlloc h) r zs z s :=
    ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  obtain ⟨value, heap1, stream, state, scratch, bodyRun, current, finalAllocator,
    localGet, localSize, localRo⟩ :=
    inflate_default_local_state_return env allocated allocator
      (streamBuffers_syncAlloc invariant.good.fresh buffers) raw
      (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn]) (syncAlloc_ro_buf h)
  have initialGet : (syncAlloc h).bytes block = some array :=
    (byte_view_syncAlloc invariant.good.fresh (ref := .blk block) get).1
  obtain ⟨bytes, finalGet, size⟩ := inflate_body_default_output_storage env allocated allocator
    (streamBuffers_syncAlloc invariant.good.fresh buffers) raw output initialGet bodyRun
  have different : block ≠ h.nextBlk := by
    intro same
    subst block
    have absent := (fresh_dead invariant.good.fresh (Nat.le_refl h.nextBlk)).1
    rw [get] at absent
    cases absent
  have freedGet : (freeWin heap1 (syncBuf h)).bytes block = some bytes := by
    simpa only [freeWin, syncBuf, upd_ne _ _ _ _ different] using finalGet
  have publicRun : C.run (inflate (some r) flush) h =
      .ok (value, freeWin heap1 (syncBuf h)) := by
    obtain ⟨ib, io, ob, oo, input, rawOutput, separate⟩ := raw
    have outBool : (z.next_out == .null) = false := by rw [output]; rfl
    have inBool : (z.next_in == .null) = false := by
      change z.next_in = .ref (.blk ib) io at input
      rw [input]
      rfl
    unfold C.run inflate
    rw [bind_app, allocLocalB_run h invariant.good.fresh]
    simp only []
    rw [bind_app]
    simp only [bind_app, stateCheck_live allocated.good.live, bne_self_eq_false,
      Bool.false_eq_true, ite_false, ldZStream_ok allocated.good.live.hz, outBool,
      inBool, Bool.false_and, Bool.false_or, allocated.good.live.zst, castI]
    rw [bind_app] at bodyRun
    unfold runX at bodyRun
    dsimp only [c] at bodyRun
    erw [bodyRun]
    simp only []
    change (do freeB (syncBuf h); pure value) heap1 = .ok (value, freeWin heap1 (syncBuf h))
    rw [bind_app]
    dsimp only [syncBuf]
    rw [freeBuf_run localGet localRo]
    rfl
  have heaps : freeWin heap1 (syncBuf h) = after :=
    congrArg Prod.snd (Except.ok.inj (publicRun.symm.trans executed))
  exact ⟨bytes, heaps ▸ freedGet, size⟩

/-- Every bounded prefix of the original caller output range is readable
after the actual public call. The bound is supplied by cursor accounting
when this is used for produced output; no byte contents are assumed. -/
theorem inflate_default_raw_output_bytes
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {flush rc : Int32} {made : Nat}
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (raw : RawFastIO (dispatchRegs z s))
    (executed : C.run (inflate (some r) flush) h = .ok (rc, after))
    (bound : made ≤ z.avail_out.toNat) :
    ∃ out, out.length = made ∧ Bytes after z.next_out made out := by
  obtain ⟨ib, io, ob, oo, input, output, separate⟩ := raw
  change z.next_out = .ref (.blk ob) oo at output
  have raw : RawFastIO (dispatchRegs z s) := ⟨ib, io, ob, oo, input, output, separate⟩
  have initialBuffers := buffers
  obtain ⟨stream, streamGet, _, range, _⟩ := buffers
  have sameStream : stream = z := Option.some.inj (streamGet.symm.trans invariant.good.live.hz)
  subst stream
  have writable : Writable h z.next_out z.avail_out.toNat := by
    rcases range with null | ⟨_, write, _⟩
    · rw [output] at null
      cases null
    · exact write rfl
  rcases writable with ⟨null, _⟩ | ⟨ref, offset, array, pointer, get, _, room⟩
  · rw [output] at null
    cases null
  · rw [output] at pointer
    cases pointer
    obtain ⟨bytes, finalGet, size⟩ :=
      inflate_default_raw_output_storage invariant allocator initialBuffers raw output get executed
    have capacity : oo + made ≤ bytes.size := by omega
    refine ⟨(bytes.toList.drop oo).take made, ?_, Or.inr ⟨.blk ob, oo, bytes, output, finalGet, capacity, rfl⟩⟩
    simp only [List.length_take, List.length_drop, Array.length_toList]
    omega

end Zlib.Inflate.Proofs
