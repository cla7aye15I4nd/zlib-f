import ZlibF.Proof.«inflate.c.local-good»
import ZlibF.Proof.«inflate.c.decode-state»
import ZlibF.Proof.«inflate.c.match-invariant»
import ZlibF.Proof.«inflate.c.dispatch-entry»
import ZlibF.Proof.«inflate.c.fast-entry»

/-! Local representation preservation for the actual decoder accesses.
Old caller table collisions are retained. This does not assert dispatch closure. -/
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Existing-object updates preserve uniqueness above the original allocation boundary. -/
theorem UniqueFrom.of_shape {h after : Heap} {first : Nat}
    (unique : UniqueFrom h first) (shape : Shape h after) : UniqueFrom after first := by
  intro b lower
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := shape b
  have bound := unique b lower
  simpa only [cnt, e1, e2, e3, e4, e5, e6, e7] using bound

/-- State and stream writes need no uniqueness of unrelated caller objects. -/
theorem LocalGood.setZI {h : Heap} {first : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (good : LocalGood h first r zs z s)
    {stream : ZStream} {state : InflateState}
    (pointer : stream.state = z.state) (alloc : stream.zalloc ≠ .null)
    (free : stream.zfree ≠ .null) (back : state.strm = s.strm)
    (mode : HEAD ≤ state.mode ∧ state.mode ≤ SYNC) (inv : StInv h zs state) :
    LocalGood (setI (r.put h stream) zs state) first r zs stream state := by
  have shape : Shape h (setI (r.put h stream) zs state) :=
    (shape_put good.live.hz stream).trans
      (shape_setI (by simpa using good.live.hs) state)
  refine ⟨⟨?_, by simp, pointer.trans good.live.zst, back.trans good.live.back,
    mode, alloc, free⟩, inv.congr (by simp) (by simp),
    shape.fresh (by simp) good.fresh, good.unique.of_shape shape⟩
  simp [ZStreamRef.get_put, good.live.hz]

/-- Updating the live scalar state preserves the local representation. -/
theorem LocalGood.state {h : Heap} {first : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} (good : LocalGood h first r zs z s)
    (back : state.strm = s.strm) (mode : HEAD ≤ state.mode ∧ state.mode ≤ SYNC)
    (inv : StInv h zs state) : LocalGood (setI h zs state) first r zs z state := by
  have updated := good.setZI rfl good.live.zalloc good.live.zfree back mode inv
  rwa [ZStreamRef.put_self good.live.hz] at updated

/-- Decoder mode and match-counter assignments keep the local storage invariant. -/
theorem LocalGood.decode_update {h : Heap} {first : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} (good : LocalGood h first r zs z s)
    (frame : DecodeStateFrame s state) (mode : HEAD ≤ state.mode ∧ state.mode ≤ SYNC) :
    LocalGood (setI h zs state) first r zs z state := by
  apply good.state (by rw [frame]) mode
  apply good.inv.of_fields
  all_goals rw [frame]
  exact good.inv.bits

/-- A genuine caller byte-view write preserves the private window when separate.
The view can share its block number with an unrelated old typed object. -/
theorem LocalGood.byte_view_put {h : Heap} {first : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (good : LocalGood h first r zs z s)
    {dest : BRef} {output : Array UInt8} (get : Space.get h dest = some output)
    (write : Space.ro h dest = false)
    (separate : ∀ w, s.window = .ref (.blk w) 0 → dest ≠ .blk w) (array : Array UInt8) :
    LocalGood (Space.put h dest array) first r zs z s := by
  have shape := byte_view_put_shape get write array
  refine ⟨⟨by rw [byte_view_put_stream]; exact good.live.hz,
    by rw [byte_view_put_istates]; exact good.live.hs,
    good.live.zst, good.live.back, good.live.mode, good.live.zalloc, good.live.zfree⟩,
    ⟨good.inv.wf, ?_, good.inv.reqbits, good.inv.bits, good.inv.ptr⟩,
    shape.fresh (byte_view_put_nextBlk h dest array) good.fresh,
    good.unique.of_shape shape⟩
  have win := good.inv.win
  refine ⟨win.wbits, ?_, win.nullws, win.ws, win.hv, win.wn, win.eq⟩
  rcases win.block with null | ⟨w, saved, ptr, savedGet, savedWrite, size⟩
  · exact Or.inl null
  · refine Or.inr ⟨w, saved, ptr, ?_, by rw [byte_view_put_ro]; exact savedWrite, size⟩
    change (Space.get (Space.put h dest array) (BRef.blk w) : Option (Array UInt8)) = some saved
    rw [byte_view_get_put_ne h (separate w ptr).symm array]
    exact savedGet

theorem LocalGood.streamOwned_iff {h : Heap} {first : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (good : LocalGood h first r zs z s) (b : Nat) :
    StreamOwned h r b ↔ InflateOwned zs s b := by
  constructor
  · rintro ⟨stream, get, cases⟩
    have sameStream : stream = z := Option.some.inj (get.symm.trans good.live.hz)
    subst stream
    rcases cases with ⟨i, state, kind, live, owned⟩ | ⟨i, state, kind, _, _⟩
    · have sameIndex : i = zs := by
        have eq := kind.symm.trans good.live.zst
        cases eq
        rfl
      subst i
      have sameState : state = s := Option.some.inj (live.symm.trans good.live.hs)
      rwa [sameState] at owned
    · have impossible := kind.symm.trans good.live.zst
      cases impossible
  · intro owned
    exact ⟨z, good.live.hz, Or.inl ⟨zs, s, good.live.zst, good.live.hs, owned⟩⟩

/-- A private decoder update preserves a caller range when its byte views
and window root are unchanged. This transports the public range across
scalar-mode transitions without assuming another API's contract. -/
theorem callerRange_local_transport {h after : Heap} {first : Nat} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState}
    (before : LocalGood h first r zs z s) (current : LocalGood after first r zs stream state)
    (window : state.window = s.window)
    (views : ∀ ref : BRef, (Space.get after ref : Option (Array UInt8)) = Space.get h ref)
    (readonly : ∀ ref : BRef, Space.ro after ref = Space.ro h ref)
    {pointer : BPtr} {size : Nat} {write : Bool} (range : CallerRange h r pointer size write) :
    CallerRange after r pointer size write := by
  rcases range with null | ⟨readable, writable, unowned⟩
  · exact Or.inl null
  · right
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨bytes, bytesRead⟩ := readable
      refine ⟨bytes, ?_⟩
      rcases bytesRead with null | ⟨ref, off, array, ptr, get, fit, contents⟩
      · exact Or.inl null
      · exact Or.inr ⟨ref, off, array, ptr, by rw [views]; exact get, fit, contents⟩
    · intro writing
      rcases writable writing with null | ⟨ref, off, array, ptr, get, ro, fit⟩
      · exact Or.inl null
      · exact Or.inr ⟨ref, off, array, ptr, by rw [views]; exact get,
          by rw [readonly]; exact ro, fit⟩
    · intro b root owned
      apply unowned b root
      rw [current.streamOwned_iff] at owned
      rw [before.streamOwned_iff]
      simpa only [InflateOwned, window] using owned

/-- The real state-mode assignment returns the same local representation. -/
theorem setMode_local {c : Ctx} {h : Heap} {first : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (env : Env c h r zs z s)
    (good : LocalGood h first r zs z s) (mode : UInt32)
    (valid : HEAD ≤ mode ∧ mode ≤ SYNC) (regs : IL) :
    runX (monadLift (setMode c.st mode) : X Unit) regs h =
      .ok ((.ok (), regs), setI h zs { s with mode }) ∧
      LocalGood (setI h zs { s with mode }) first r zs z { s with mode } := by
  exact ⟨runX_setMode env mode regs, good.decode_update (by rfl) valid⟩

/-- Real RESTORE writes the exact boundary counters and held bits. -/
theorem restore_local {c : Ctx} {h : Heap} {first : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (env : Env c h r zs z s)
    (good : LocalGood h first r zs z s) (regs : IL) (bits : regs.bits.toNat ≤ 39) :
    runX (RESTORE c.strm c.st) regs h =
      .ok ((.ok (), regs), setI (r.put h (leaveStream z regs)) zs (leaveState s regs)) ∧
      LocalGood (setI (r.put h (leaveStream z regs)) zs (leaveState s regs)) first
        r zs (leaveStream z regs) (leaveState s regs) := by
  refine ⟨RESTORE_pending_run env, good.setZI rfl good.live.zalloc good.live.zfree
    rfl good.live.mode ?_⟩
  exact good.inv.of_fields (st' := leaveState s regs) rfl rfl rfl rfl rfl rfl rfl rfl rfl bits rfl rfl rfl

/-- The actual TYPE normalization, LOAD and counter assignments reach the
unchanged whole dispatch loop. No loop execution contract is assumed. -/
theorem run_dispatch_entry_local {c : Ctx} {h : Heap} {first : Nat}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (env : Env c h r zs z s) (good : LocalGood h first r zs z s) :
    ∃ after state,
      runX (inflate_run c) IL.init h =
        runX (xwhile (pure true) (inflate_dispatch c)) (dispatchRegs z state) after ∧
      LocalGood after first r zs z state ∧ Env c after r zs z state ∧
      ByteViewSizes h after ∧ DecodeStateFrame s state ∧ after = setI h zs state ∧
      state = (if s.mode = TYPE then { s with mode := TYPEDO } else s) := by
  by_cases type : s.mode = TYPE
  · let state := { s with mode := TYPEDO }
    let after := setI h zs state
    have finalGood : LocalGood after first r zs z state :=
      good.decode_update (by rfl) (by change HEAD ≤ TYPEDO ∧ TYPEDO ≤ SYNC; decide)
    have current : Env c after r zs z state :=
      ⟨env.strm, env.st, finalGood.live.hz, finalGood.live.hs⟩
    refine ⟨after, state, ?_, finalGood, current, byte_view_sizes_setI h zs state,
      by rfl, rfl, by simp only [type, ↓reduceIte]; rfl⟩
    unfold inflate_run
    rw [runX_bind, runX_rdS env]
    simp only [type, beq_self_eq_true, ↓reduceIte]
    rw [runX_bind, runX_setMode env]
    simp only []
    rw [runX_bind, LOAD_run current]
    simp only []
    rw [runX_bind, runX_modify]
    rfl
  · refine ⟨h, s, ?_, good, env, ByteViewSizes.refl h, by rfl,
      by simp [setI, upd_self _ _ _ good.live.hs], by simp only [type, ↓reduceIte]⟩
    unfold inflate_run
    rw [runX_bind, runX_rdS env]
    simp only [type, beq_iff_eq, ↓reduceIte, runX_bind]
    rw [LOAD_run env]
    simp only []
    rw [runX_modify]
    rfl


/-- Real entry also produces the actual public buffer and bit-source premises
on that same heap; old caller typed collisions are immaterial. -/
theorem run_dispatch_buffers_entry_local {c : Ctx} {h : Heap} {first : Nat}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (env : Env c h r zs z s) (good : LocalGood h first r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (validInput : z.next_in = .null → z.avail_in = 0)
    (held : s.hold.toNat < 2 ^ s.bits.toNat) :
    ∃ after state bs,
      runX (inflate_run c) IL.init h =
        runX (xwhile (pure true) (inflate_dispatch c)) (dispatchRegs z state) after ∧
      LocalGood after first r zs z state ∧ Env c after r zs z state ∧
      StreamBuffers after r ∧ OutputCursorInvariant after r (dispatchRegs z state) ∧
      BitInv after (dispatchRegs z state) bs ∧
      Separate (dispatchRegs z state).next (dispatchRegs z state).have_.toNat
        (dispatchRegs z state).put (dispatchRegs z state).left.toNat ∧
      ByteViewSizes h after ∧ DecodeStateFrame s state ∧ after = setI h zs state := by
  obtain ⟨after, state, actual, current, currentEnv, sizes, frame, heapEq, _⟩ :=
    run_dispatch_entry_local env good
  have currentBuffers : StreamBuffers after r := by
    obtain ⟨stream, get, input, output, disjoint⟩ := buffers
    have same : stream = z := Option.some.inj (get.symm.trans good.live.hz)
    subst stream
    refine ⟨z, current.live.hz, ?_, ?_, disjoint⟩
    · apply callerRange_local_transport good current (by rw [frame]) _ _ input
      · intro ref; rw [heapEq]; exact byte_view_get_setI h zs state ref
      · intro ref; rw [heapEq]; exact byte_view_ro_setI h zs state ref
    · apply callerRange_local_transport good current (by rw [frame]) _ _ output
      · intro ref; rw [heapEq]; exact byte_view_get_setI h zs state ref
      · intro ref; rw [heapEq]; exact byte_view_ro_setI h zs state ref
  obtain ⟨bs, source, separate⟩ := dispatchRegs_input (s := state) current.live.hz currentBuffers
    validInput (by rw [frame]; exact held)
  exact ⟨after, state, bs, actual, current, currentEnv, currentBuffers,
    dispatchRegs_output current.live.hz currentBuffers nonnull state,
    source, separate, sizes, frame, heapEq⟩

#print axioms LocalGood.streamOwned_iff
#print axioms callerRange_local_transport
#print axioms run_dispatch_buffers_entry_local

#print axioms UniqueFrom.of_shape
#print axioms LocalGood.setZI
#print axioms LocalGood.state
#print axioms LocalGood.decode_update
#print axioms LocalGood.byte_view_put
#print axioms setMode_local
#print axioms restore_local
#print axioms run_dispatch_entry_local
end Zlib.Inflate.Local
