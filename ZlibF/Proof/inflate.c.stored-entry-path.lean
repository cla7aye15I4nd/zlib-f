import ZlibF.Proof.«inflate.c.wrapper-output-credit»
import ZlibF.Proof.«inflate.c.stored-output-exact-frame»
import ZlibF.Proof.«inflate.c.code-length-repeat-meaning»
import ZlibF.Proof.«infback.c.pure»
import ZlibF.Proof.«inflate.c.header-progress-observed»
import ZlibF.Proof.«inflate.c.default-public-output-bytes»
import ZlibF.Math.DeflateStoredBlock
import ZlibF.Proof.«inflate.c.output-frame-footprint-compose»
import ZlibF.Proof.«inflate.c.leave-default-public-accounting»
import ZlibF.Proof.«inflate.c.leave-zero-output-memory»
import ZlibF.Math.LZ77CopySpec
import ZlibF.Proof.«inflate.c.check-default-accounting»
import ZlibF.Math.DeflateChecksum

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Exact bytes in the interval written by the actual stored-block memcpy. -/
theorem stored_copyRange_slice (output input : Array UInt8) (oo io n : Nat)
    (outputFit : oo + n ≤ output.size) (inputFit : io + n ≤ input.size) :
    ((copyRange output input oo io n).toList.drop oo).take n =
      (input.toList.drop io).take n := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, Array.length_toList, size_copyRange]
    omega
  · intro k hk hk'
    have kn : k < n := by simp only [List.length_take] at hk; omega
    have target : oo + k < (copyRange output input oo io n).size := by rw [size_copyRange]; omega
    have source : io + k < input.size := by omega
    have value := copyRange_getElem? output input oo io n outputFit inputFit (oo + k)
    rw [ite_eq_left (by omega)] at value
    simp only [Nat.add_sub_cancel_left] at value
    rw [Array.getElem?_eq_getElem target, Array.getElem?_eq_getElem source] at value
    have eq := Option.some.inj value
    simpa only [List.getElem_take, List.getElem_drop, Array.getElem_toList] using eq

/-- A particular actual COPY execution writes precisely its consumed input
prefix, on every admitted byte-view combination, including disjoint slices
of one object. The run premise is an execution observation. -/
theorem stored_COPY_payload_of_run {c : Ctx} {l regs : IL} {h after : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    {outcome : Except Ex Unit} {made : Nat}
    (E : Env c h r zs z s) (good : Good h r zs z s)
    (buffers : DispatchBuffers h r l bs)
    (run : runX (inflate_COPY c) l h = .ok ((outcome, regs), after))
    (count : regs.left.toNat + made = l.left.toNat) :
    Bytes after l.put made (bs.take made) ∧
      (s.length ≠ 0 → made = (copyAmt s.length l.have_ l.left).toNat) ∧
      regs.have_.toNat + made = l.have_.toNat ∧
      ∀ state, after.istates zs = some state → state.length.toNat + made = s.length.toNat := by
  obtain ⟨dest, output, oo, put, outputGet, write, outputRoom, _, _, _⟩ :=
    callerRange_slow_output good l buffers.output.range buffers.output.nonnull
      buffers.output.count buffers.output.produced
  by_cases done : s.length = 0
  · have actual := inflate_COPY_done E l done
    have same := Except.ok.inj (actual.symm.trans run)
    cases same
    have zero : made = 0 := by change l.left.toNat + made = l.left.toNat at count; omega
    subst made
    refine ⟨Or.inr ⟨dest, oo, output, put, ?_, by omega, ?_⟩, ?_, ?_, ?_⟩
    · rw [byte_view_get_setI]
      exact outputGet
    · simp only [List.take_zero]
    · intro impossible; exact False.elim (impossible done)
    · rfl
    · intro state stateGet
      rw [setI_istates_same] at stateGet
      have sameState := Option.some.inj stateGet
      rw [← sameState]
      rfl
  · let n := copyAmt s.length l.have_ l.left
    obtain ⟨lengthBound, inputBound, outputBound⟩ := copyAmt_le s.length l.have_ l.left
    change n.toNat ≤ s.length.toNat at lengthBound
    change n.toNat ≤ l.have_.toNat at inputBound
    change n.toNat ≤ l.left.toNat at outputBound
    by_cases stall : n = 0
    · have actual := inflate_COPY_leave E l done stall
      have same := Except.ok.inj (actual.symm.trans run)
      cases same
      have zero : made = 0 := by change l.left.toNat + made = l.left.toNat at count; omega
      subst made
      refine ⟨Or.inr ⟨dest, oo, output, put, outputGet, by omega, by simp only [List.take_zero]⟩, ?_, rfl, ?_⟩
      · intro _; rw [show copyAmt s.length l.have_ l.left = 0 from stall]; rfl
      · intro state stateGet
        have sameState := Option.some.inj (E.hs.symm.trans stateGet)
        rw [← sameState]
        omega
    · have positive : 0 < n.toNat := by
        have nonzero : n.toNat ≠ 0 := fun zero => stall (UInt32.toNat_inj.mp zero)
        omega
      have nonempty : bs ≠ [] := by
        intro empty
        have eq := buffers.bits.have_eq
        rw [empty] at eq
        simp only [List.length_nil] at eq
        omega
      obtain ⟨source, input, io, next, inputGet, inputRoom, content⟩ := buffers.bits.next.resolve_left nonempty
      have inputFit : io + n.toNat ≤ input.size := by have eq := buffers.bits.have_eq; omega
      have outputFit : oo + n.toNat ≤ output.size := by omega
      have separate : dest ≠ source ∨ oo + n.toNat ≤ io ∨ io + n.toNat ≤ oo := by
        have sep := buffers.separate
        rw [next, put] at sep
        rcases sep with empty | empty | different | before | later
        · omega
        · omega
        · exact Or.inl (Ne.symm different)
        · exact Or.inr (Or.inr (by omega))
        · exact Or.inr (Or.inl (by omega))
      have actual := inflate_COPY_views_run E l done stall next put inputGet outputGet write
        inputFit outputFit separate
      have same := Except.ok.inj (actual.symm.trans run)
      cases same
      have madeEq : made = n.toNat := by
        change (l.left - n).toNat + made = l.left.toNat at count
        rw [UInt32.toNat_sub_of_le _ _ outputBound] at count
        omega
      subst made
      refine ⟨Or.inr ⟨dest, oo, copyRange output input oo io n.toNat, put, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
      · rw [byte_view_get_setI]
        exact byte_view_get_put outputGet write _
      · rw [size_copyRange]
        exact outputFit
      · rw [stored_copyRange_slice output input oo io n.toNat outputFit inputFit]
        rw [content]
        rw [List.take_take]
        have bound : n.toNat ≤ bs.length := by rw [← buffers.bits.have_eq]; exact inputBound
        rw [Nat.min_eq_left bound]
      · intro _; rfl
      · change (l.have_ - n).toNat + n.toNat = l.have_.toNat
        rw [UInt32.toNat_sub_of_le _ _ inputBound]
        omega
      · intro state stateGet
        rw [setI_istates_same] at stateGet
        have sameState := Option.some.inj stateGet
        rw [← sameState]
        change (s.length - n).toNat + n.toNat = s.length.toNat
        rw [UInt32.toNat_sub_of_le _ _ lengthBound]
        omega

#print axioms stored_copyRange_slice
#print axioms stored_COPY_payload_of_run
/-- Independent stored-byte reading follows the same finite input prefix. -/
theorem stored_readBytes_prefix (bytes : List UInt8) (made : Nat)
    (bound : made ≤ bytes.length) (future : List Bool) :
    ZlibF.Spec.readBytes made (ZlibF.Spec.bytesToBits bytes ++ future) = some
      (bytes.take made, ZlibF.Spec.bytesToBits (bytes.drop made) ++ future) := by
  have bits := congrArg ZlibF.Spec.bytesToBits (List.take_append_drop made bytes)
  simp only [ZlibF.Spec.bytesToBits, List.flatMap_append] at bits
  change ZlibF.Spec.bytesToBits (bytes.take made) ++ ZlibF.Spec.bytesToBits (bytes.drop made) =
    ZlibF.Spec.bytesToBits bytes at bits
  rw [← bits, List.append_assoc]
  have read := Zlib.Trees.Proofs.Out.readBytes_encoded (bytes.take made)
    (ZlibF.Spec.bytesToBits (bytes.drop made) ++ future)
  simpa only [List.length_take, Nat.min_eq_left bound] using read

/-- Closed actual COPY execution supplies the stored payload bytes,
independent byte-reader result, exact count and permitted write interval. -/
theorem stored_COPY_boundary_payload {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = COPY) :
    ∃ outcome regs after state made, made ≤ bs.length ∧
      runX (inflate_COPY c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs z state ∧ DispatchBuffers after r regs (bs.drop made) ∧
      regs.have_.toNat + made = l.have_.toNat ∧ regs.left.toNat + made = l.left.toNat ∧
      state.length.toNat + made = s.length.toNat ∧
      Bytes after l.put made (bs.take made) ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) [⟨l.put, made⟩] ∧
      ∀ future, ZlibF.Spec.readBytes made (ZlibF.Spec.bytesToBits bs ++ future) = some
        (bs.take made, ZlibF.Spec.bytesToBits (bs.drop made) ++ future) := by
  obtain ⟨outcome, regs, after, state, made, bound, run, current, _tables, _pending,
    packet, _sizes, _frame, _next, haveCount, _put, leftCount, _bits, _hold, _kind, _static, _shape⟩ :=
    inflate_COPY_boundary_frame E good pending buffers mode
  have payload := stored_COPY_payload_of_run E good buffers run leftCount
  exact ⟨outcome, regs, after, state, made, bound, run, current, packet, haveCount, leftCount,
    payload.2.2.2 state current.live.hs, payload.1,
    inflate_COPY_frame_of_run E good buffers run leftCount,
    stored_readBytes_prefix bs made bound⟩

/-- COPY_ performs its literal mode write and the same verified payload
copy. The count and remaining length refer to the original state. -/
theorem stored_COPY_start_payload_of_run {c : Ctx} {l regs : IL} {h after : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    {outcome : Except Ex Unit} {made : Nat}
    (E : Env c h r zs z s) (good : Good h r zs z s)
    (buffers : DispatchBuffers h r l bs)
    (run : runX (inflate_COPY_ c) l h = .ok ((outcome, regs), after))
    (count : regs.left.toNat + made = l.left.toNat) :
    Bytes after l.put made (bs.take made) ∧
      regs.have_.toNat + made = l.have_.toNat ∧
      ∀ state, after.istates zs = some state → state.length.toNat + made = s.length.toNat := by
  let ready := { s with mode := COPY }
  let heap0 := setI h zs ready
  have good0 : Good heap0 r zs z ready := good.decode_update (by rfl)
    (by change HEAD ≤ COPY ∧ COPY ≤ SYNC; decide)
  have env0 : Env c heap0 r zs z ready := ⟨E.strm, E.st, good0.live.hz, good0.live.hs⟩
  have packet0 := buffers.byte_views good good0 rfl (byte_view_get_setI h zs ready)
    (byte_view_ro_setI h zs ready)
  have actual : runX (inflate_COPY c) l heap0 = .ok ((outcome, regs), after) :=
    (inflate_COPY__eq E l).symm.trans run
  have payload := stored_COPY_payload_of_run env0 good0 packet0 actual count
  exact ⟨payload.1, payload.2.2.1, payload.2.2.2⟩

#print axioms stored_readBytes_prefix
#print axioms stored_COPY_boundary_payload
#print axioms stored_COPY_start_payload_of_run
theorem stored_copyAmt_short_exhausts (length have_ left : UInt32)
    (short : (copyAmt length have_ left).toNat < length.toNat) :
    (copyAmt length have_ left).toNat = have_.toNat ∨
      (copyAmt length have_ left).toNat = left.toNat := by
  by_cases first : length > have_
  · by_cases second : have_ > left
    · exact Or.inr (by simp [copyAmt, first, second])
    · exact Or.inl (by simp [copyAmt, first, second])
  · by_cases second : length > left
    · exact Or.inr (by simp [copyAmt, first, second])
    · simp [copyAmt, first, second] at short

/-- A partial stored COPY call consumes one finite prefix and then exits
its actual main loop on input/output exhaustion. No next-block execution
is hidden in this selected path. -/
theorem stored_COPY_short_loop {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = COPY)
    (short : (copyAmt s.length l.have_ l.left).toNat < s.length.toNat) :
    ∃ regs after state made, made ≤ bs.length ∧
      runX (xwhile (pure true) (inflate_dispatch c)) l h = .ok ((.error Ex.leave, regs), after) ∧
      DefaultOriginState after r zs z state ∧ DispatchBuffers after r regs (bs.drop made) ∧
      regs.have_.toNat + made = l.have_.toNat ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.next = inputAdvance l.next made ∧ regs.put = inputAdvance l.put made ∧
      regs.bits = l.bits ∧ state.length.toNat + made = s.length.toNat ∧
      Bytes after l.put made (bs.take made) := by
  obtain ⟨outcome, regs, after, state, made, bound, run, current, _tables, _pending,
    packet, _sizes, _frame, next, haveCount, put, leftCount, bits, _hold, kind, _static, _shape⟩ :=
    inflate_COPY_boundary_frame E initial.good initial.pending buffers mode
  have step := (inflate_dispatch_COPY E l mode).trans run
  have payload := stored_COPY_payload_of_run E initial.good buffers run leftCount
  obtain ⟨outcome0, regs0, after0, state0, actual0, currentJ, _modes⟩ :=
    inflate_COPY_default_state E initial.toDefaultStateJ buffers mode
  have same : ((outcome, regs), after) = ((outcome0, regs0), after0) := Except.ok.inj (run.symm.trans actual0)
  cases same
  have sameState : state = state0 := Option.some.inj (current.live.hs.symm.trans currentJ.good.live.hs)
  subst state0
  have origin := inflate_dispatch_default_origin_state E initial buffers step currentJ
  have nonempty : s.length ≠ 0 := by intro zero; rw [zero] at short; change _ < 0 at short; omega
  have amount := payload.2.1 nonempty
  have debt := payload.2.2.2 state current.live.hs
  rcases kind with waiting | completed | copied
  · obtain ⟨exit, zero, _sameState⟩ := waiting
    subst outcome
    have loop := xwhile_run_chain (inflate_dispatch c) (fun _ => l) (fun _ => h)
      0 (by unfold fuel; decide) Ex.leave regs after (by intro j impossible; omega) step
    exact ⟨regs, after, state, made, bound, loop, origin, packet, haveCount, leftCount,
      next, put, bits, debt, payload.1⟩
  · obtain ⟨exit, zero, _type⟩ := completed
    have none : copyAmt s.length l.have_ l.left = 0 := by
      apply UInt32.toNat_inj.mp
      change (copyAmt s.length l.have_ l.left).toNat = 0
      omega
    have actual := inflate_COPY_leave E l nonempty none
    rw [run, exit] at actual
    cases actual
  · obtain ⟨exit, positive, copying, _remaining⟩ := copied
    subst outcome
    have remains : state.length ≠ 0 := by intro zero; rw [zero] at debt; change 0 + made = _ at debt; omega
    have exhausted := stored_copyAmt_short_exhausts s.length l.have_ l.left short
    have stalled : copyAmt state.length regs.have_ regs.left = 0 := by
      have bounds := copyAmt_le state.length regs.have_ regs.left
      apply UInt32.toNat_inj.mp
      change (copyAmt state.length regs.have_ regs.left).toNat = 0
      rcases exhausted with noInput | noOutput <;> omega
    have env : Env c after r zs z state := ⟨E.strm, E.st, current.live.hz, current.live.hs⟩
    let last := { regs with copy := 0 }
    have stop : runX (inflate_dispatch c) regs after = .ok ((.error Ex.leave, last), after) := by
      rw [inflate_dispatch_COPY env regs copying]
      exact inflate_COPY_leave env regs remains stalled
    have loop := xwhile_run_chain (inflate_dispatch c)
      (fun j => if j = 0 then l else regs) (fun j => if j = 0 then h else after)
      1 (by unfold fuel; decide) Ex.leave last after
      (by
        intro j hj
        have zero : j = 0 := by omega
        subst j
        simpa using step)
      (by simpa only [Nat.one_ne_zero, ite_false] using stop)
    have finalPacket : DispatchBuffers after r last (bs.drop made) := by
      refine ⟨packet.input, ?_, packet.separate, ?_⟩
      · exact ⟨packet.output.range, packet.output.nonnull, packet.output.count, packet.output.produced⟩
      · exact ⟨packet.bits.have_eq, packet.bits.next, packet.bits.hold_lt⟩
    exact ⟨last, after, state, made, bound, by simpa only [ite_true] using loop,
      origin, finalPacket, haveCount, leftCount, next, put, bits, debt, payload.1⟩

#print axioms stored_copyAmt_short_exhausts
#print axioms stored_COPY_short_loop
/-- The actual complete metadata suffix preserves the stored remaining length. -/
theorem leaveFinalize_stored_length {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z current : ZStream} {s : InflateState} (E : Env c h r zs current s)
    (invariant : DefaultOriginState h r zs current s) (allocator : DefAlloc current)
    (output : LeaveOutputView h l) (cursor : z.next_out = l.put) (count : z.avail_out = l.left) :
    ∃ rc after stream state, leaveFinalize c l z h = .ok (rc, after) ∧
      DefaultOriginState after r zs stream state ∧ DefAlloc stream ∧
      state.length = s.length := by
  have statics : Zlib.Crc32.Proofs.StaticsOK h := by
    unfold Zlib.Crc32.Proofs.StaticsOK
    rw [invariant.globals]
    exact ⟨rfl, rfl⟩
  obtain ⟨rc, after, stream, state, run, good, frame, views, ret, codes, static⟩ :=
    leaveFinalize_all_wrappers_safe E invariant.good output statics cursor count
  have sizes : ByteViewSizes h after := by
    intro ref
    rw [views ref]
  have finalJ := invariant.toDefaultStateJ.leave_metadata good frame codes (sizes.platform invariant.platform) static
  have final := invariant.of_fields finalJ (by rw [frame]) (by rw [frame]) (by rw [frame])
  have fixed := streamFrameM_leaveFinalize r c l z E.strm h rc after run
  refine ⟨rc, after, stream, state, run, final,
    fixed.allocator invariant.good.live.hz good.live.hz allocator, ?_⟩
  rw [frame]

/-- Actual window success and allocation failure preserve the stored remaining length. -/
theorem leaveWithWindow_stored_length {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s)
    (invariant : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (output : OutputCursorInvariant h r l) (cursor : z.next_out = l.put) (count : z.avail_out = l.left) :
    ∃ rc after stream state, leaveWithWindow c l z h = .ok (rc, after) ∧
      DefaultOriginState after r zs stream state ∧ DefAlloc stream ∧
      state.length = s.length := by
  obtain ⟨ref, bytes, off, put, get, _, room, leftCount, produced, unowned⟩ :=
    callerRange_slow_output invariant.good l output.range output.nonnull output.count output.produced
  have amount : (l.out_ - z.avail_out).toNat = l.out_.toNat - l.left.toNat := by
    rw [count, UInt32.toNat_sub_of_le _ _ leftCount]
  have start : (l.out_ - z.avail_out).toNat ≤ off := by rw [amount]; exact produced
  have bound : off ≤ bytes.size := by omega
  have separate : Separate (.ref ref (off - (l.out_ - z.avail_out).toNat))
      (l.out_ - z.avail_out).toNat s.window (2 ^ s.wbits.toNat) := by
    rcases invariant.good.inv.win.block with null | ⟨w, a, win, _, _, _⟩
    · simp [Separate, null]
    · simp [Separate, win, unowned w win]
  obtain ⟨wr, heap1, state1, windowRun, good1, windowFrame, sourceView, codeViews, outcome⟩ :=
    updatewindow_decoder_boundary (copy := l.out_ - z.avail_out) invariant.good allocator.1 get start bound unowned
  obtain ⟨platform, static⟩ := updatewindow_platform_public invariant.good invariant.platform
    allocator.1 get start bound separate windowRun
  have currentJ := invariant.toDefaultStateJ.window_update good1 windowFrame codeViews platform static
  have current := invariant.window_update currentJ windowFrame
  rcases outcome with success | failure
  · subst wr
    have env1 : Env c heap1 r zs z state1 := ⟨E.strm, E.st, good1.live.hz, good1.live.hs⟩
    have view : LeaveOutputView heap1 l :=
      ⟨ref, off, bytes, put, sourceView, by rw [count] at start; exact start, bound⟩
    obtain ⟨rc, after, stream, state, finish, final, finalAllocator, finalProgress⟩ :=
      leaveFinalize_stored_length (z := z) env1 current allocator view cursor count
    refine ⟨rc, after, stream, state, ?_, final, finalAllocator, by rw [windowFrame] at finalProgress; exact finalProgress⟩
    unfold leaveWithWindow
    rw [bind_app, E.strm, cursor, put, windowRun]
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    exact finish
  · obtain ⟨eqrc, _, stateEq, heapEq⟩ := failure
    subst wr
    subst state1
    let state := { s with mode := MEM }
    have good : Good (setI heap1 zs state) r zs z state :=
      good1.decode_update (by rfl) (by change HEAD ≤ MEM ∧ MEM ≤ SYNC; decide)
    have finalJ := current.toDefaultStateJ.mem_update good (platform.with_istates _) rfl
    have final := current.of_fields finalJ rfl rfl rfl
    refine ⟨Z_MEM_ERROR, setI heap1 zs state, z, state, ?_, final, allocator, by rfl⟩
    unfold leaveWithWindow
    rw [bind_app, E.strm, cursor, put, windowRun]
    simp only [show ((1 : Int32) != 0) = true from rfl, ↓reduceIte, bind_app, E.st,
      setMode_tab good1.live.hs, pure_app]
    rfl

/-- The complete actual leave preserves the stored remaining length. -/
theorem inflate_leave_stored_length {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} (E : Env c h r zs z s)
    (invariant : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (buffers : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39) :
    ∃ rc after stream state, inflate_leave c l h = .ok (rc, after) ∧
      DefaultOriginState after r zs stream state ∧ DefAlloc stream ∧
      state.length = s.length := by
  let stream0 := leaveStream z l
  let state0 := leaveState s l
  let heap0 := setI (r.put h stream0) zs state0
  have currentJ := invariant.toDefaultStateJ.restore E buffers bits
  have current := invariant.of_fields currentJ rfl rfl rfl
  have env0 : Env c heap0 r zs stream0 state0 :=
    ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
  have views0 : ∀ ref : BRef, (Space.get heap0 ref : Option (Array UInt8)) = Space.get h ref := by
    intro ref
    rw [byte_view_get_setI, byte_view_get_stream_put]
  have output0 : OutputCursorInvariant heap0 r l :=
    ⟨callerRange_transport invariant.good current.good rfl views0 (by
      intro ref
      rw [byte_view_ro_setI, byte_view_ro_stream_put]) buffers.output.range,
      buffers.output.nonnull, buffers.output.count, buffers.output.produced⟩
  by_cases update : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
      (s.mode < CHECK || c.flush != Z_FINISH))) = true
  · obtain ⟨rc, after, stream, state, run, final, finalAllocator, finalProgress⟩ :=
      leaveWithWindow_stored_length env0 current allocator output0 rfl rfl
    refine ⟨rc, after, stream, state, ?_, final, finalAllocator, finalProgress⟩
    rw [inflate_leave_restore_cut E, leaveAfterRestore_window env0 update]
    exact run
  · have skip : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
      (s.mode < CHECK || c.flush != Z_FINISH))) = false := by
      cases eq : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
        (s.mode < CHECK || c.flush != Z_FINISH))) <;> simp_all
    obtain ⟨rc, after, stream, state, run, final, finalAllocator, finalProgress⟩ :=
      leaveFinalize_stored_length (z := stream0) env0 current allocator
        (leaveOutputView_of_cursor current.good output0) rfl rfl
    refine ⟨rc, after, stream, state, ?_, final, finalAllocator, finalProgress⟩
    rw [inflate_leave_restore_cut E, leaveAfterRestore_no_window env0 skip]
    exact run

#print axioms leaveFinalize_stored_length
#print axioms leaveWithWindow_stored_length
#print axioms inflate_leave_stored_length


/-- Actual LOAD, partial stored copy, optional window update and complete
leave preserve the copied byte prefix, its exact public counts and stored
remaining length. Genuine allocation failure is included in the return. -/
theorem stored_COPY_short_body_payload
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (allocator : DefAlloc z) (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (input : BitInv h (dispatchRegs z s) bs) (mode : s.mode = COPY)
    (short : (copyAmt s.length z.avail_in z.avail_out).toNat < s.length.toNat) :
    ∃ rc after stream0 state made, made ≤ bs.length ∧
      (do
        let (result, regs) ← runX (inflate_run c) IL.init
        match result with
        | .error (.ret value) => pure value
        | _ => inflate_leave c regs) h = .ok (rc, after) ∧
      DefaultOriginState after r zs stream0 state ∧ DefAlloc stream0 ∧
      state.length.toNat + made = s.length.toNat ∧
      stream0.next_in = inputAdvance z.next_in made ∧ stream0.avail_in.toNat + made = z.avail_in.toNat ∧
      stream0.next_out = inputAdvance z.next_out made ∧ stream0.avail_out.toNat + made = z.avail_out.toNat ∧
      Bytes after z.next_out made (bs.take made) := by
  have output := dispatchRegs_output E.hz buffers nonnull s
  obtain ⟨z0, get0, inputRange, _outputRange, separate⟩ := buffers
  have sameZ : z0 = z := Option.some.inj (get0.symm.trans E.hz)
  subst z0
  have packet : DispatchBuffers h r (dispatchRegs z s) bs := ⟨inputRange, output, separate, input⟩
  obtain ⟨regs, heap0, state0, made, bound, loop, current, packet0,
    haveCount, leftCount, next, put, bitsEq, debt, copied⟩ :=
    stored_COPY_short_loop E initial packet mode short
  have bits : regs.bits.toNat ≤ 39 := by rw [bitsEq]; exact initial.good.inv.bits
  have noType : s.mode ≠ TYPE := by rw [mode]; decide
  have entry : runX (inflate_run c) IL.init h =
      runX (xwhile (pure true) (inflate_dispatch c)) (dispatchRegs z s) h := by
    unfold inflate_run
    rw [runX_bind, runX_rdS E]
    simp only [noType, beq_iff_eq, ite_false, runX_bind]
    rw [LOAD_run E]
    simp only []
    rw [runX_modify]
    rfl
  have env0 : Env c heap0 r zs z state0 := ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
  obtain ⟨rc, after, stream0, state, leave, final, finalAllocator, lengthEq⟩ :=
    inflate_leave_stored_length env0 current allocator packet0 bits
  obtain ⟨rc1, after1, stream1, state1, leave1, final1, _allocator1,
    nextIn, availIn, nextOut, availOut, _outcome⟩ :=
    inflate_leave_default_public_accounting env0 current.toDefaultStateJ allocator packet0 bits
  have sameRun : (rc, after) = (rc1, after1) := Except.ok.inj (leave.symm.trans leave1)
  cases sameRun
  have streamEq : stream0 = stream1 := Option.some.inj (final.good.live.hz.symm.trans final1.good.live.hz)
  subst stream1
  refine ⟨rc, after, stream0, state, made, bound, ?_, final, finalAllocator, ?_,
    nextIn.trans next, ?_, nextOut.trans put, ?_, ?_⟩
  · rw [bind_app, entry, loop]
    exact leave
  · rw [lengthEq]
    exact debt
  · rw [availIn]
    exact haveCount
  · rw [availOut]
    exact leftCount
  · rcases copied with ⟨null, zero, empty⟩ | ⟨ref, off, array, pointer, get, room, values⟩
    · exact False.elim (nonnull null)
    · have currentPut : regs.put = .ref ref (off + made) := by rw [put, pointer]; rfl
      have unchanged := inflate_leave_output_view_unchanged env0 current.toDefaultStateJ allocator
        packet0 bits leave currentPut get
      exact Or.inr ⟨ref, off, array, pointer, unchanged.2.1, room, values⟩

#print axioms stored_COPY_short_body_payload
/-- Releasing the fresh local byte object retains every pre-existing
caller byte view, regardless of the view's payload after execution. -/
theorem stored_byte_view_free_local {h after : Heap} {ref : BRef} {old current : Array UInt8}
    (fresh : Fresh h) (original : Space.get h ref = some old)
    (get : Space.get after ref = some current) :
    Space.get (freeWin after (syncBuf h)) ref = some current := by
  cases ref with
  | blk block =>
    have different : block ≠ h.nextBlk := by
      intro same
      subst block
      have absent := (fresh_dead fresh (Nat.le_refl h.nextBlk)).1
      change h.bytes h.nextBlk = some old at original
      rw [original] at absent
      cases absent
    change (upd after.bytes h.nextBlk none) block = some current
    rw [upd_ne _ _ _ _ different]
    exact get
  | str _ | dstate_depth _ | st_dist_code | st_length_code => exact get

/-- A real accepted public partial COPY call returns the exact copied
prefix and retains its stored-byte debt, including real window failure.
The input view comes from observed bytes, not an assumed callee contract. -/
theorem stored_COPY_short_public_payload
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (initial : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (inputBytes : Bytes h z.next_in z.avail_in.toNat bs) (mode : s.mode = COPY)
    (short : (copyAmt s.length z.avail_in z.avail_out).toNat < s.length.toNat)
    (flush : Int32) :
    ∃ rc after stream0 state made, made ≤ bs.length ∧
      C.run (inflate (some r) flush) h = .ok (rc, after) ∧
      DefaultOriginState after r zs stream0 state ∧ DefAlloc stream0 ∧ after.bytes h.nextBlk = none ∧
      state.length.toNat + made = s.length.toNat ∧
      stream0.next_in = inputAdvance z.next_in made ∧ stream0.avail_in.toNat + made = z.avail_in.toNat ∧
      stream0.next_out = inputAdvance z.next_out made ∧ stream0.avail_out.toNat + made = z.avail_out.toNat ∧
      Bytes after z.next_out made (bs.take made) := by
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have allocated := default_origin_syncAlloc initial
  have env : Env c (syncAlloc h) r zs z s := ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  have input := header_input_view_of_bytes (s := s) inputBytes initial.held
  have input0 : BitInv (syncAlloc h) (dispatchRegs z s) bs := by
    refine ⟨input.have_eq, ?_, input.hold_lt⟩
    rcases input.next with empty | ⟨ref, array, off, pointer, get, bound, values⟩
    · exact Or.inl empty
    · exact Or.inr ⟨ref, array, off, pointer, (byte_view_syncAlloc initial.good.fresh get).1, bound, values⟩
  obtain ⟨rc, heap1, stream0, state, bytes, bodyRun, current, finalAllocator, localGet, localSize, localRo⟩ :=
    inflate_default_origin_local_state_return env allocated allocator
      (streamBuffers_syncAlloc initial.good.fresh buffers) nonnull inputValid
      (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn]) (syncAlloc_ro_buf h)
  obtain ⟨traceRc, traceHeap, traceStream, traceState, made, bound, traceRun, traceFinal,
    _traceAllocator, debt, nextIn, availIn, nextOut, availOut, copied⟩ :=
    stored_COPY_short_body_payload env allocated allocator
      (streamBuffers_syncAlloc initial.good.fresh buffers) nonnull input0 mode short
  have same : (rc, heap1) = (traceRc, traceHeap) := Except.ok.inj (bodyRun.symm.trans traceRun)
  cases same
  have sameZ : stream0 = traceStream := Option.some.inj (current.good.live.hz.symm.trans traceFinal.good.live.hz)
  have sameS : state = traceState := Option.some.inj (current.good.live.hs.symm.trans traceFinal.good.live.hs)
  subst traceStream traceState
  have final := current.free_local localGet localSize
  refine ⟨rc, freeWin heap1 (syncBuf h), stream0, state, made, bound,
    ?_, final, finalAllocator, ?_, debt, nextIn, availIn, nextOut, availOut, ?_⟩
  · have entry : (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = false := by
      by_cases null : z.next_in = .null
      · simp [nonnull, null, inputValid null]
      · simp [nonnull, null]
    unfold C.run inflate
    rw [bind_app, allocLocalB_run h initial.good.fresh]
    simp only []
    rw [bind_app]
    simp only [bind_app, stateCheck_live allocated.good.live,
      bne_self_eq_false, Bool.false_eq_true, ite_false, ldZStream_ok allocated.good.live.hz,
      entry, allocated.good.live.zst, castI]
    rw [bind_app] at bodyRun
    unfold runX at bodyRun
    dsimp only [c] at bodyRun
    erw [bodyRun]
    simp only []
    change (do freeB (syncBuf h); pure rc) heap1 = .ok (rc, freeWin heap1 (syncBuf h))
    rw [bind_app]
    dsimp only [syncBuf]
    rw [freeBuf_run localGet localRo]
    rfl
  · simp only [syncBuf, freeWin, upd_same]
  · obtain ⟨ref, old, off, pointer, original, _write, _room, _count, _produced, _private⟩ :=
      callerRange_slow_output initial.good (dispatchRegs z s)
        (dispatchRegs_output initial.good.live.hz buffers nonnull s).range nonnull
        (dispatchRegs_output initial.good.live.hz buffers nonnull s).count
        (dispatchRegs_output initial.good.live.hz buffers nonnull s).produced
    rcases copied with ⟨null, zero, empty⟩ | ⟨ref1, off1, array, pointer1, get, room, values⟩
    · exact False.elim (nonnull null)
    · have ptrEq : Ptr.ref ref off = Ptr.ref ref1 off1 := pointer.symm.trans pointer1
      cases ptrEq
      exact Or.inr ⟨ref, off, array, pointer,
        stored_byte_view_free_local initial.good.fresh original get, room, values⟩

#print axioms stored_byte_view_free_local
#print axioms stored_COPY_short_public_payload
/-- Two actual byte observations of the same range have equal contents. -/
theorem stored_observed_bytes_unique {h : Heap} {p : BPtr} {n : Nat} {xs ys : List UInt8}
    (first : Bytes h p n xs) (second : Bytes h p n ys) : xs = ys := by
  rcases first with ⟨null, zero, empty⟩ | ⟨ref, off, array, pointer, get, _room, values⟩
  · rcases second with ⟨_, _, empty1⟩ | ⟨ref, off, array, pointer, _get, _room, _values⟩
    · exact empty.trans empty1.symm
    · rw [null] at pointer
      cases pointer
  · rcases second with ⟨null, _, _⟩ | ⟨ref1, off1, array1, pointer1, get1, _room1, values1⟩
    · rw [null] at pointer
      cases pointer
    · have ptrEq : Ptr.ref ref off = Ptr.ref ref1 off1 := pointer.symm.trans pointer1
      cases ptrEq
      have eq : array = array1 := Option.some.inj (get.symm.trans get1)
      subst array1
      exact values.trans values1.symm

/-- The original public DataStep identifies the same consumed and copied
prefix. A null-output entry refusal contributes no bytes. No BitInv or
callee run is assumed beyond the actual DataStep observation. -/
theorem stored_dataStep_COPY_short_payload
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {flush rc : Int32} {input output : List UInt8} {used : Nat}
    (initial : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (observed : DataStep .inflate h after r flush rc input output used)
    (mode : s.mode = COPY)
    (short : (copyAmt s.length z.avail_in z.avail_out).toNat < s.length.toNat) :
    ∃ stream0 state, DefaultOriginState after r zs stream0 state ∧ DefAlloc stream0 ∧
      used ≤ input.length ∧ output = input.take used ∧
      state.length.toNat + used = s.length.toNat ∧
      stream0.next_in = inputAdvance z.next_in used ∧ stream0.avail_in.toNat + used = z.avail_in.toNat ∧
      stream0.next_out = inputAdvance z.next_out used ∧ stream0.avail_out.toNat + used = z.avail_out.toNat := by
  obtain ⟨z0, z1, get0, get1, buffers, _header, inputBytes, usedEq, outputBytes, actual⟩ := observed
  have sameZ : z0 = z := Option.some.inj (get0.symm.trans initial.good.live.hz)
  subst z0
  by_cases null : z.next_out = .null
  · have expected := inflate_default_null_output_run initial.toDefaultStateJ flush null
    have sameRun := Except.ok.inj (actual.symm.trans expected)
    cases sameRun
    have get : r.get (tmpFreed h) = some z := by
      simpa only [tmpFreed, ZStreamRef.get_freeWin, ZStreamRef.get_syncAlloc] using initial.good.live.hz
    have streamEq : z1 = z := Option.some.inj (get1.symm.trans get)
    subst z1
    have zero : used = 0 := by rw [usedEq]; omega
    clear usedEq
    subst used
    have length := header_observed_bytes_length outputBytes
    have empty : output = [] := by apply List.length_eq_zero_iff.mp; omega
    have allocated := default_origin_syncAlloc initial
    have final := allocated.free_local (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn])
    exact ⟨z, s, final, allocator, by omega, by simp only [empty, List.take_zero],
      by omega, (inputAdvance_zero _).symm, by omega, (inputAdvance_zero _).symm, by omega⟩
  · have inputValid : z.next_in = .null → z.avail_in = 0 := by
      intro nullIn
      rcases inputBytes with ⟨_, zero, _⟩ | ⟨ref, off, array, pointer, _get, _room, _values⟩
      · exact UInt32.toNat_inj.mp zero
      · rw [nullIn] at pointer
        cases pointer
    obtain ⟨rc0, heap0, stream0, state, made, bound, run, final, finalAllocator, _freed,
      debt, nextIn, availIn, nextOut, availOut, copied⟩ :=
      stored_COPY_short_public_payload initial allocator buffers null inputValid inputBytes mode short flush
    have sameRun : (rc0, heap0) = (rc, after) := Except.ok.inj (run.symm.trans actual)
    cases sameRun
    have streamEq : stream0 = z1 := Option.some.inj (final.good.live.hz.symm.trans get1)
    subst z1
    have madeEq : made = used := by rw [usedEq]; omega
    subst made
    have outputCount : z.avail_out.toNat - stream0.avail_out.toNat = used := by omega
    rw [outputCount] at outputBytes
    have equal := stored_observed_bytes_unique outputBytes copied
    exact ⟨stream0, state, final, finalAllocator, bound, equal, debt, nextIn, availIn, nextOut, availOut⟩

#print axioms stored_observed_bytes_unique
#print axioms stored_dataStep_COPY_short_payload
/-- A finite actual partial stored-copy segment. Constructors contain
only actual call observations, source-mode/amount guards and legal caller
edits. They do not assume byte equality or a post-state invariant. -/
inductive StoredCopyPartialTrace (start : Heap) (r : ZStreamRef) (zs : Nat) :
    Heap → List UInt8 → List UInt8 → Prop where
  | begin : StoredCopyPartialTrace start r zs start [] []
  | caller {h after input output} : StoredCopyPartialTrace start r zs h input output →
      Rebuffer h after r → ZlibF.PlatformMemory.ByteObjectsFit after →
      StoredCopyPartialTrace start r zs after input output
  | step {h after priorInput priorOutput z s flush rc input output used} :
      StoredCopyPartialTrace start r zs h priorInput priorOutput →
      r.get h = some z → h.istates zs = some s → s.mode = COPY →
      (copyAmt s.length z.avail_in z.avail_out).toNat < s.length.toNat →
      DataStep .inflate h after r flush rc input output used →
      StoredCopyPartialTrace start r zs after (priorInput ++ input.take used) (priorOutput ++ output)

/-- Every selected finite public segment copies exactly its cumulative
observed input. Caller rebuffering retains the original stored length
as copied bytes plus remaining debt. Initial stored-header provenance is
a separate producer obligation. -/
theorem StoredCopyPartialTrace.sound
    {start after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {input output : List UInt8}
    (initial : DefaultOriginState start r zs z s) (allocator : DefAlloc z)
    (history : StoredCopyPartialTrace start r zs after input output) :
    ∃ stream state, DefaultOriginState after r zs stream state ∧ DefAlloc stream ∧
      output = input ∧ state.length.toNat + input.length = s.length.toNat := by
  induction history with
  | begin => exact ⟨z, s, initial, allocator, rfl, by simp only [List.length_nil, Nat.add_zero]⟩
  | @caller before after inputs outputs prior edit platform ih =>
    obtain ⟨stream, state, current, currentAllocator, copied, debt⟩ := ih
    obtain ⟨nextStream, next⟩ := rebuffer_default_origin current edit platform
    obtain ⟨otherStream, fields, good⟩ := rebuffer_inflate_good current.good edit
    have same : otherStream = nextStream := Option.some.inj (good.live.hz.symm.trans next.good.live.hz)
    subst otherStream
    refine ⟨nextStream, state, next, ?_, copied, debt⟩
    rw [fields]
    exact currentAllocator
  | @step before after inputs outputs callerStream callerState flush rc freshInput freshOutput used
      prior streamGet stateGet mode short actual ih =>
    obtain ⟨stream, state, current, currentAllocator, copied, debt⟩ := ih
    have sameZ : callerStream = stream := Option.some.inj (streamGet.symm.trans current.good.live.hz)
    have sameS : callerState = state := Option.some.inj (stateGet.symm.trans current.good.live.hs)
    subst callerStream callerState
    obtain ⟨nextStream, nextState, next, nextAllocator, bound, bytes, remaining,
      _nextIn, _availIn, _nextOut, _availOut⟩ :=
      stored_dataStep_COPY_short_payload current currentAllocator actual mode short
    refine ⟨nextStream, nextState, next, nextAllocator, ?_, ?_⟩
    · rw [copied, bytes]
    · simp only [List.length_append, List.length_take, Nat.min_eq_left bound]
      omega

/-- The independent stored-byte reader agrees with all bytes produced by
an actual partial-copy history, for every trailing bit suffix. -/
theorem StoredCopyPartialTrace.reader
    {start after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {input output : List UInt8}
    (initial : DefaultOriginState start r zs z s) (allocator : DefAlloc z)
    (history : StoredCopyPartialTrace start r zs after input output) :
    ∃ stream state, DefaultOriginState after r zs stream state ∧ DefAlloc stream ∧
      state.length.toNat + input.length = s.length.toNat ∧
      ∀ future, ZlibF.Spec.readBytes input.length (ZlibF.Spec.bytesToBits input ++ future) =
        some (output, future) := by
  obtain ⟨stream, state, current, currentAllocator, copied, debt⟩ := history.sound initial allocator
  refine ⟨stream, state, current, currentAllocator, debt, ?_⟩
  intro future
  rw [copied]
  exact Zlib.Trees.Proofs.Out.readBytes_encoded input future

#print axioms StoredCopyPartialTrace.sound
#print axioms StoredCopyPartialTrace.reader
/-- A normalized actual stored header word supplies the two independent
16-bit field reads. The literal C complement check accepts exactly their
specified relation, and INITBITS retains precisely the unread bytes. -/
theorem stored_header_word_fields {h : Heap} {l : IL} {bs : List UInt8}
    (B : BitInv h l bs) (word : l.bits.toNat = 32) :
    ∃ len nlen firstRest,
      ZlibF.Spec.readBits 16 (stream l bs) = some (len, firstRest) ∧
      ZlibF.Spec.readBits 16 firstRest = some (nlen, bytesBits bs) ∧
      (l.hold.toUInt32 &&& 0xffff).toNat = len ∧ len < 65536 ∧ nlen < 65536 ∧
      ((((l.hold &&& (0xffff : UInt64)) != ((l.hold >>> 16) ^^^ (0xffff : UInt64))) = false) ↔
        nlen = 65535 - len) := by
  let first : IL := { l with hold := l.hold >>> 16, bits := l.bits - 16 }
  let second : IL := { first with hold := first.hold >>> 16, bits := first.bits - 16 }
  obtain ⟨firstInv, firstStream, firstBits⟩ := DROPBITS_inv B 16 (by change 16 ≤ l.bits.toNat; omega) (by decide)
  change BitInv h first bs at firstInv
  change stream first bs = (stream l bs).drop 16 at firstStream
  change first.bits.toNat = l.bits.toNat - 16 at firstBits
  have firstWord : first.bits.toNat = 16 := by omega
  obtain ⟨secondInv, secondStream, secondBits⟩ := DROPBITS_inv firstInv 16
    (by change 16 ≤ first.bits.toNat; omega) (by decide)
  change BitInv h second bs at secondInv
  change stream second bs = (stream first bs).drop 16 at secondStream
  change second.bits.toNat = first.bits.toNat - 16 at secondBits
  have emptyBits : second.bits.toNat = 0 := by omega
  have emptyHeld : second.hold.toNat = 0 := by
    have held := secondInv.hold_lt
    rw [emptyBits] at held
    omega
  have remaining : stream second bs = bytesBits bs := by simp only [stream, emptyBits, emptyHeld, natBits, List.nil_append]
  have lowRead := readBits_held_stream l bs 16 (by omega)
  rw [← firstStream] at lowRead
  have highRead := readBits_held_stream first bs 16 (by omega)
  rw [← secondStream, remaining] at highRead
  have heldBound : l.hold.toNat < 2 ^ 32 := by rw [← word]; exact B.hold_lt
  have highValue : first.hold.toNat = l.hold.toNat / 65536 := by
    change (l.hold >>> 16).toNat = _
    rw [UInt64.toNat_shiftRight]
    simp [Nat.shiftRight_eq_div_pow]
  have highBound : first.hold.toNat < 65536 := by rw [highValue]; omega
  rw [Nat.mod_eq_of_lt highBound] at highRead
  refine ⟨l.hold.toNat % 65536, first.hold.toNat, stream first bs,
    lowRead, highRead, Zlib.Infback.Proofs.stored_len_toNat _, Nat.mod_lt _ (by decide), highBound, ?_⟩
  have accepted := Zlib.Infback.Proofs.stored_check l.hold heldBound
  rw [highValue]
  constructor
  · intro pass
    have sum := accepted.mp pass
    omega
  · intro complement
    apply accepted.mpr
    omega

#print axioms stored_header_word_fields
/-- The actual byte alignment and NEEDBITS32 prefix produces the
independent LEN/NLEN fields. A valid complement establishes the real
COPY_ state, its exact length and live input packet before fall-through. -/
theorem stored_STORED_header_prefix
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = STORED) (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome current used,
      runX (do BYTEBITS; NEEDBITS 32) l h = .ok ((outcome, current), h) ∧
      used ≤ bs.length ∧ BitInv h current (bs.drop used) ∧
      stream current (bs.drop used) = (stream l bs).drop ((stream l bs).length % 8) ∧
      (outcome = .error Ex.leave →
        runX (inflate_STORED c) l h = .ok ((.error Ex.leave, current), h)) ∧
      (outcome = .ok () → current.bits.toNat = 32 ∧
        ∃ len nlen firstRest,
          ZlibF.Spec.readBits 16 ((stream l bs).drop ((stream l bs).length % 8)) = some (len, firstRest) ∧
          ZlibF.Spec.readBits 16 firstRest = some (nlen, bytesBits (bs.drop used)) ∧
          len < 65536 ∧ nlen < 65536 ∧
          ((((current.hold &&& (0xffff : UInt64)) != ((current.hold >>> 16) ^^^ (0xffff : UInt64))) = false) ↔
            nlen = 65535 - len) ∧
          (nlen = 65535 - len →
            let ready := { s with length := current.hold.toUInt32 &&& 0xffff, mode := COPY_ }
            let heap0 := setI h zs ready
            let regs := { current with hold := 0, bits := 0 }
            DefaultOriginState heap0 r zs z ready ∧ DispatchBuffers heap0 r regs (bs.drop used) ∧
            ready.length.toNat = len ∧
            runX (inflate_STORED c) l h =
              runX (if c.flush == Z_TREES then (throw Ex.leave : X Unit) else inflate_COPY_ c) regs heap0)) := by
  obtain ⟨aligned, alignment, byteAligned⟩ := BYTEBITS_inv buffers.bits
  have alignmentCount : (bytebits l).bits.toNat = l.bits.toNat - l.bits.toNat % 8 := by
    change (l.bits - (l.bits &&& 7)).toNat = _
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (and7_le l)), and7_toNat]
  have alignedBound : (bytebits l).bits.toNat ≤ 39 := by omega
  have alignByLength : (stream l bs).length % 8 = l.bits.toNat % 8 := by
    rw [tcStream_length buffers.bits]
    omega
  obtain ⟨outcome, current, used, pull, bound, inv, source, bitCount, shape,
    bitBound, _identity, full, _wait, _kinds, cursor⟩ := NEEDBITS_run_cursor aligned 32 (by decide)
  have source0 : stream current (bs.drop used) = (stream l bs).drop ((stream l bs).length % 8) := by
    rw [source, alignment, alignByLength]
  refine ⟨outcome, current, used, ?_, bound, inv, source0, ?_, ?_⟩
  · rw [runX_bind, BYTEBITS_run]
    exact pull
  · intro waiting
    exact inflate_STORED_wait l current h Ex.leave (by rwa [waiting] at pull)
  · intro normal
    have enough := full normal
    change 32 ≤ current.bits.toNat at enough
    have word : current.bits.toNat = 32 := by
      change current.bits.toNat ≤ max (bytebits l).bits.toNat 39 at bitBound
      omega
    obtain ⟨len, nlen, firstRest, readLen, readNlen, lowLen, lenBound, nlenBound, accepted⟩ :=
      stored_header_word_fields inv word
    rw [source0] at readLen
    refine ⟨word, len, nlen, firstRest, readLen, readNlen, lenBound, nlenBound, accepted, ?_⟩
    intro valid
    have pass := accepted.mpr valid
    have notBad : ¬ (((current.hold &&& (0xffff : UInt64)) !=
        ((current.hold >>> 16) ^^^ (0xffff : UInt64))) = true) := by rw [pass]; decide
    let ready := { s with length := current.hold.toUInt32 &&& 0xffff, mode := COPY_ }
    let heap0 := setI h zs ready
    let regs := { current with hold := 0, bits := 0 }
    have frame : DecodeStateFrame s ready := rfl
    have good0 : Good heap0 r zs z ready := initial.good.decode_update frame
      (by change HEAD ≤ COPY_ ∧ COPY_ ≤ SYNC; decide)
    have pending0 : DataPendingInvariant ready := by
      apply dataPendingInvariant_idle (s := ready) initial.pending.sane
      change COPY_ ≠ LENEXT ∧ COPY_ ≠ DIST ∧ COPY_ ≠ DISTEXT ∧ COPY_ ≠ MATCH
      decide
    have tables0 : DataTableInvariant heap0 ready :=
      dataTableInvariant_inactive (by change ¬ DataTableMode COPY_; unfold DataTableMode; decide)
    have state0 := initial.toDefaultStateJ.stored_update (Or.inl mode) good0 tables0 pending0 frame
      (Or.inr (Or.inl rfl)) (byte_view_sizes_setI h zs ready) rfl
    have origin : DefaultOriginState heap0 r zs z ready := initial.of_fields state0 rfl rfl rfl
    have inv0 : BitInv heap0 regs (bs.drop used) := (INITBITS_inv inv).1.decode_update zs ready
    have packet0 : DispatchBuffers heap0 r regs (bs.drop used) :=
      buffers.consume initial.good good0 rfl (byte_view_get_setI h zs ready)
        (byte_view_ro_setI h zs ready) (by dsimp only [regs]; rw [shape]; rfl) cursor bound inv0
    exact ⟨origin, packet0, lowLen, inflate_STORED_ok E l current (by rwa [normal] at pull) notBad⟩

#print axioms stored_STORED_header_prefix
theorem stored_copyAmt_complete (length have_ left : UInt32)
    (input : length.toNat ≤ have_.toNat) (output : length.toNat ≤ left.toNat) :
    copyAmt length have_ left = length := by
  unfold copyAmt
  simp only [gt_iff_lt, UInt32.lt_iff_toNat_lt, show ¬ have_.toNat < length.toNat by omega,
    show ¬ left.toNat < length.toNat by omega, ite_false]

/-- A nonempty complete stored copy and its zero-length COPY dispatch
form two actual source iterations ending in TYPE. The subsequent TYPE,
next-block and wrapper execution is left as a real continuation. -/
theorem stored_COPY_complete_dispatch_prefix
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = COPY)
    (nonempty : s.length ≠ 0)
    (enoughInput : s.length.toNat ≤ l.have_.toNat) (enoughOutput : s.length.toNat ≤ l.left.toNat) :
    ∃ firstRegs firstHeap firstState regs after state,
      runX (inflate_dispatch c) l h = .ok ((.ok (), firstRegs), firstHeap) ∧
      DefaultOriginState firstHeap r zs z firstState ∧ firstState.mode = COPY ∧ firstState.length = 0 ∧
      runX (inflate_dispatch c) firstRegs firstHeap = .ok ((.ok (), regs), after) ∧
      DefaultOriginState after r zs z state ∧ state.mode = TYPE ∧ state.length = 0 ∧
      DispatchBuffers after r regs (bs.drop s.length.toNat) ∧
      regs.next = inputAdvance l.next s.length.toNat ∧ regs.have_.toNat + s.length.toNat = l.have_.toNat ∧
      regs.put = inputAdvance l.put s.length.toNat ∧ regs.left.toNat + s.length.toNat = l.left.toNat ∧
      Bytes after l.put s.length.toNat (bs.take s.length.toNat) ∧
      ∀ future, ZlibF.Spec.readBytes s.length.toNat (ZlibF.Spec.bytesToBits bs ++ future) = some
        (bs.take s.length.toNat, ZlibF.Spec.bytesToBits (bs.drop s.length.toNat) ++ future) := by
  obtain ⟨outcome, firstRegs, firstHeap, firstState, made, bound, run, current, _tables, _pending,
    packet, _sizes, _frame, next, haveCount, put, leftCount, _bits, _hold, kind, _static, _shape⟩ :=
    inflate_COPY_boundary_frame E initial.good initial.pending buffers mode
  have payload := stored_COPY_payload_of_run E initial.good buffers run leftCount
  have amount := payload.2.1 nonempty
  rw [stored_copyAmt_complete s.length l.have_ l.left enoughInput enoughOutput] at amount
  subst made
  have positive : 0 < s.length.toNat := by
    have notZero : s.length.toNat ≠ 0 := fun zero => nonempty (UInt32.toNat_inj.mp zero)
    omega
  have normalAndMode : outcome = .ok () ∧ firstState.mode = COPY := by
    rcases kind with ⟨_wait, zero, _same⟩ | ⟨_done, zero, _type⟩ | ⟨normal, _positive, copying, _debt⟩
    · omega
    · omega
    · exact ⟨normal, copying⟩
  obtain ⟨normal, copying⟩ := normalAndMode
  subst outcome
  have remaining : firstState.length = 0 := by
    have debt := payload.2.2.2 firstState current.live.hs
    apply UInt32.toNat_inj.mp
    change firstState.length.toNat = 0
    omega
  have firstStep := (inflate_dispatch_COPY E l mode).trans run
  obtain ⟨outcome0, regs0, heap0, state0, actual0, currentJ, _modes⟩ :=
    inflate_COPY_default_state E initial.toDefaultStateJ buffers mode
  have same : ((Except.ok (), firstRegs), firstHeap) = ((outcome0, regs0), heap0) :=
    Except.ok.inj (run.symm.trans actual0)
  cases same
  have stateEq : firstState = state0 := Option.some.inj (current.live.hs.symm.trans currentJ.good.live.hs)
  subst state0
  have origin := inflate_dispatch_default_origin_state E initial buffers firstStep currentJ
  let regs := { firstRegs with copy := 0 }
  let state := { firstState with mode := TYPE }
  let after := setI firstHeap zs state
  have env : Env c firstHeap r zs z firstState := ⟨E.strm, E.st, current.live.hz, current.live.hs⟩
  have secondStep : runX (inflate_dispatch c) firstRegs firstHeap = .ok ((.ok (), regs), after) := by
    rw [inflate_dispatch_COPY env firstRegs copying]
    exact inflate_COPY_done env firstRegs remaining
  have frame : DecodeStateFrame firstState state := rfl
  have good2 : Good after r zs z state := current.decode_update frame
    (by change HEAD ≤ TYPE ∧ TYPE ≤ SYNC; decide)
  have pending2 : DataPendingInvariant state := by
    apply dataPendingInvariant_idle (s := state) origin.pending.sane
    change TYPE ≠ LENEXT ∧ TYPE ≠ DIST ∧ TYPE ≠ DISTEXT ∧ TYPE ≠ MATCH
    decide
  have tables2 : DataTableInvariant after state :=
    dataTableInvariant_inactive (by change ¬ DataTableMode TYPE; unfold DataTableMode; decide)
  have current2 := origin.toDefaultStateJ.stored_update (Or.inr (Or.inr copying)) good2 tables2 pending2 frame
    (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (byte_view_sizes_setI firstHeap zs state) rfl
  have origin2 : DefaultOriginState after r zs z state := origin.of_fields current2 rfl rfl rfl
  have moved := packet.byte_views current good2 rfl (byte_view_get_setI firstHeap zs state)
    (byte_view_ro_setI firstHeap zs state)
  have packet2 : DispatchBuffers after r regs (bs.drop s.length.toNat) := by
    refine ⟨moved.input, ?_, moved.separate, ?_⟩
    · exact ⟨moved.output.range, moved.output.nonnull, moved.output.count, moved.output.produced⟩
    · exact ⟨moved.bits.have_eq, moved.bits.next, moved.bits.hold_lt⟩
  have copied : Bytes after l.put s.length.toNat (bs.take s.length.toNat) := by
    rcases payload.1 with null | ⟨ref, off, array, pointer, get, room, values⟩
    · exact Or.inl null
    · exact Or.inr ⟨ref, off, array, pointer, (byte_view_get_setI firstHeap zs state ref).trans get, room, values⟩
  exact ⟨firstRegs, firstHeap, firstState, regs, after, state, firstStep, origin, copying, remaining,
    secondStep, origin2, rfl, remaining, packet2, next, haveCount, put, leftCount, copied,
    stored_readBytes_prefix bs s.length.toNat bound⟩

#print axioms stored_copyAmt_complete
#print axioms stored_COPY_complete_dispatch_prefix
/-- A completed independent fixed-width read retains every suffix. -/
theorem stored_readBits_append {n : Nat} {input rest : List Bool} {value : Nat}
    (read : ZlibF.Spec.readBits n input = some (value, rest)) (future : List Bool) :
    ZlibF.Spec.readBits n (input ++ future) = some (value, rest ++ future) := by
  induction n generalizing input value rest with
  | zero =>
    simp only [ZlibF.Spec.readBits] at read ⊢
    cases read
    rfl
  | succ n ih =>
    cases input with
    | nil => simp only [ZlibF.Spec.readBits] at read; cases read
    | cons bit input =>
      cases parsed : ZlibF.Spec.readBits n input with
      | none => simp only [ZlibF.Spec.readBits, parsed] at read; cases read
      | some pair =>
        obtain ⟨low, tail⟩ := pair
        simp only [ZlibF.Spec.readBits, parsed] at read
        cases read
        simpa only [List.cons_append, ZlibF.Spec.readBits, ih parsed]

/-- A real accepted stored header establishes the complete independent
Body grammar for every subsequent byte continuation. Payload bytes are
selected by the actual LEN, rather than supplied as an output premise. -/
theorem stored_STORED_independent_body
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = STORED) (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome current used,
      runX (do BYTEBITS; NEEDBITS 32) l h = .ok ((outcome, current), h) ∧
      used ≤ bs.length ∧ BitInv h current (bs.drop used) ∧
      (outcome = .ok () →
        ∃ len nlen,
          len < 65536 ∧ nlen < 65536 ∧
          (((current.hold &&& (0xffff : UInt64)) != ((current.hold >>> 16) ^^^ (0xffff : UInt64))) = false →
            (current.hold.toUInt32 &&& 0xffff).toNat = len ∧
            ∀ future dictionary history, len ≤ (bs.drop used ++ future).length →
              ZlibF.Spec.Body dictionary 0 history (stream l bs ++ bytesBits future)
                (bytesBits ((bs.drop used ++ future).drop len))
                (history ++ (bs.drop used ++ future).take len))) := by
  obtain ⟨outcome, current, used, prefixRun, bound, inv, _source, _waiting, completed⟩ :=
    stored_STORED_header_prefix E initial buffers mode incoming
  refine ⟨outcome, current, used, prefixRun, bound, inv, ?_⟩
  intro normal
  obtain ⟨_word, len, nlen, firstRest, readLen, readNlen, lenBound, nlenBound, accepted, ready⟩ := completed normal
  refine ⟨len, nlen, lenBound, nlenBound, ?_⟩
  intro pass
  have valid := accepted.mp pass
  obtain ⟨_origin, _packet, lengthEq, _cut⟩ := ready valid
  refine ⟨lengthEq, ?_⟩
  intro future dictionary history enough
  have futureAligned : (bytesBits future).length % 8 = 0 := by rw [bytesBits_length]; omega
  have alignment : (stream l bs ++ bytesBits future).length % 8 = (stream l bs).length % 8 := by
    rw [List.length_append]
    omega
  have drop : (stream l bs ++ bytesBits future).drop ((stream l bs ++ bytesBits future).length % 8) =
      (stream l bs).drop ((stream l bs).length % 8) ++ bytesBits future := by
    rw [alignment, List.drop_append_of_le_length (Nat.mod_le _ _)]
  have lenRead := stored_readBits_append readLen (bytesBits future)
  have nlenRead := stored_readBits_append readNlen (bytesBits future)
  rw [← bytesBits_append] at nlenRead
  have payloadRead := stored_readBytes_prefix (bs.drop used ++ future) len enough []
  simp only [List.append_nil, bytesBits_eq_bytesToBits] at payloadRead
  apply ZlibF.Spec.Body.stored (len := len) (nlen := nlen)
    (r1 := firstRest ++ bytesBits future) (r2 := bytesBits (bs.drop used ++ future))
  · rw [drop]
    exact lenRead
  · exact nlenRead
  · exact valid
  · exact payloadRead

#print axioms stored_readBits_append
#print axioms stored_STORED_independent_body
/-- Prefix membership identifies the exact fixed reference slice. -/
theorem stored_input_prefix_take {input payload : List UInt8} (source : input <+: payload) :
    input.length ≤ payload.length ∧ payload.take input.length = input := by
  obtain ⟨tail, same⟩ := source
  constructor
  · rw [← same, List.length_append]
    omega
  · rw [← same, List.take_append_of_le_length (Nat.le_refl _), List.take_length]

/-- An actual partial public-copy segment produces the reference payload
prefix and retains exactly the reference suffix length. The prefix premise
constrains input, never the desired output or an unproved callee. -/
theorem StoredCopyPartialTrace.payload_progress
    {start after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {input output payload : List UInt8}
    (initial : DefaultOriginState start r zs z s) (allocator : DefAlloc z)
    (length : s.length.toNat = payload.length)
    (history : StoredCopyPartialTrace start r zs after input output) (source : input <+: payload) :
    ∃ stream state, DefaultOriginState after r zs stream state ∧ DefAlloc stream ∧
      output = payload.take input.length ∧ state.length.toNat = (payload.drop input.length).length ∧
      output ++ payload.drop input.length = payload := by
  obtain ⟨stream, state, current, currentAllocator, copied, debt⟩ := history.sound initial allocator
  obtain ⟨bound, take⟩ := stored_input_prefix_take source
  refine ⟨stream, state, current, currentAllocator, copied.trans take.symm, ?_, ?_⟩
  · simp only [List.length_drop]
    omega
  · rw [copied]
    exact (congrArg (fun front => front ++ payload.drop input.length) take.symm).trans
      (List.take_append_drop input.length payload)

#print axioms stored_input_prefix_take
#print axioms StoredCopyPartialTrace.payload_progress
/-- Actual partial-copy history and the final complete-copy prefix
produce the reference Body's entire payload at its real TYPE boundary.
The following TYPE/trailer continuation is kept separate. -/
theorem StoredCopyPartialTrace.complete_body_to_type
    {start h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {input output payload dictionary before : List UInt8} {bodyBits rest : List Bool}
    (initial : DefaultOriginState start r zs z s) (allocator : DefAlloc z)
    (length : s.length.toNat = payload.length)
    (history : StoredCopyPartialTrace start r zs h input output) (source : input <+: payload)
    (format : ZlibF.Spec.Body dictionary 0 before bodyBits rest (before ++ payload)) :
    ∃ stream0 state0, DefaultOriginState h r zs stream0 state0 ∧ DefAlloc stream0 ∧
      state0.length.toNat = (payload.drop input.length).length ∧
      ∀ c nextBytes, c.strm = some r → c.st = some (.tab zs) →
        state0.mode = COPY → state0.length ≠ 0 → StreamBuffers h r → stream0.next_out ≠ .null →
        Bytes h stream0.next_in stream0.avail_in.toNat nextBytes →
        (payload.drop input.length) <+: nextBytes → state0.length.toNat ≤ stream0.avail_out.toNat →
        ∃ firstRegs firstHeap firstState regs after state,
          runX (inflate_dispatch c) (dispatchRegs stream0 state0) h = .ok ((.ok (), firstRegs), firstHeap) ∧
          DefaultOriginState firstHeap r zs stream0 firstState ∧ firstState.mode = COPY ∧ firstState.length = 0 ∧
          runX (inflate_dispatch c) firstRegs firstHeap = .ok ((.ok (), regs), after) ∧
          DefaultOriginState after r zs stream0 state ∧ state.mode = TYPE ∧ state.length = 0 ∧
          DispatchBuffers after r regs (nextBytes.drop state0.length.toNat) ∧
          regs.next = inputAdvance stream0.next_in state0.length.toNat ∧
          regs.have_.toNat + state0.length.toNat = stream0.avail_in.toNat ∧
          regs.put = inputAdvance stream0.next_out state0.length.toNat ∧
          regs.left.toNat + state0.length.toNat = stream0.avail_out.toNat ∧
          Bytes after stream0.next_out state0.length.toNat (payload.drop input.length) ∧
          output ++ payload.drop input.length = payload ∧
          ZlibF.Spec.Body dictionary 0 before bodyBits rest
            (before ++ (output ++ payload.drop input.length)) := by
  obtain ⟨stream0, state0, current, currentAllocator, _copied, remaining, complete⟩ :=
    history.payload_progress initial allocator length source
  refine ⟨stream0, state0, current, currentAllocator, remaining, ?_⟩
  intro c nextBytes root owner mode nonempty buffers nonnull bytes nextPrefix outputRoom
  have env : Env c h r zs stream0 state0 := ⟨root, owner, current.good.live.hz, current.good.live.hs⟩
  have view := header_input_view_of_bytes (s := state0) bytes current.held
  have outputView := dispatchRegs_output current.good.live.hz buffers nonnull state0
  obtain ⟨candidate, candidateGet, inputRange, _outputRange, separate⟩ := buffers
  have sameStream : candidate = stream0 := Option.some.inj (candidateGet.symm.trans current.good.live.hz)
  subst candidate
  have packet : DispatchBuffers h r (dispatchRegs stream0 state0) nextBytes :=
    ⟨inputRange, outputView, separate, view⟩
  obtain ⟨nextBound, nextTake⟩ := stored_input_prefix_take nextPrefix
  have enoughInput : state0.length.toNat ≤ stream0.avail_in.toNat := by
    have count := view.have_eq
    change stream0.avail_in.toNat = nextBytes.length at count
    omega
  obtain ⟨firstRegs, firstHeap, firstState, regs, after, state,
    firstStep, firstJ, firstMode, firstZero, secondStep, final, finalMode, finalZero,
    finalPacket, next, haveCount, put, leftCount, written, _reader⟩ :=
    stored_COPY_complete_dispatch_prefix env current packet mode nonempty enoughInput outputRoom
  have suffix : nextBytes.take state0.length.toNat = payload.drop input.length := by
    rw [remaining]
    exact nextTake
  rw [suffix] at written
  refine ⟨firstRegs, firstHeap, firstState, regs, after, state, firstStep, firstJ, firstMode, firstZero,
    secondStep, final, finalMode, finalZero, finalPacket, next, haveCount, put, leftCount,
    written, complete, ?_⟩
  rw [complete]
  exact format

#print axioms StoredCopyPartialTrace.complete_body_to_type
/-- Actual COPY dispatches retain the wrapper, checksum and last-block
fields in DecodeStateFrame, as well as bits and the output credit base. -/
theorem stored_dispatch_COPY_metadata
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s state : InflateState}
    {l regs : IL} {bs : List UInt8} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = COPY)
    (actual : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some state) :
    DecodeStateFrame s state ∧ regs.bits = l.bits ∧ regs.out_ = l.out_ := by
  obtain ⟨outcome0, regs0, after0, state0, made, _bound, run, current, _tables, _pending,
    _packet, _sizes, frame, _next, _haveCount, _put, _leftCount, bits, _hold, _kind, _static, _shape⟩ :=
    inflate_COPY_boundary_frame E initial.good initial.pending buffers mode
  have selected := (inflate_dispatch_COPY E l mode).symm.trans actual
  have same := Except.ok.inj (run.symm.trans selected)
  cases same
  have sameState : state0 = state := Option.some.inj (current.live.hs.symm.trans get)
  subst state0
  refine ⟨frame, bits, ?_⟩
  exact inflate_dispatch_output_base_noncheck E (by rw [mode]; decide) actual

/-- An empty remaining stored payload takes the real single COPY step
to TYPE. It writes zero bytes and keeps the entire unread input packet. -/
theorem stored_COPY_zero_dispatch_prefix
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = COPY) (zero : s.length = 0) :
    ∃ regs after state,
      runX (inflate_dispatch c) l h = .ok ((.ok (), regs), after) ∧
      DefaultOriginState after r zs z state ∧ state.mode = TYPE ∧ state.length = 0 ∧
      DispatchBuffers after r regs bs ∧ Bytes after l.put 0 [] := by
  let regs := { l with copy := 0 }
  let state := { s with mode := TYPE }
  let after := setI h zs state
  have actual : runX (inflate_COPY c) l h = .ok ((.ok (), regs), after) := inflate_COPY_done E l zero
  have step := (inflate_dispatch_COPY E l mode).trans actual
  obtain ⟨outcome0, regs0, after0, state0, run, current, _modes⟩ :=
    inflate_COPY_default_state E initial.toDefaultStateJ buffers mode
  have same := Except.ok.inj (run.symm.trans actual)
  cases same
  have get : after.istates zs = some state := by simp only [after, setI_istates_same]
  have sameState : state0 = state := Option.some.inj (current.good.live.hs.symm.trans get)
  subst state0
  have origin := inflate_dispatch_default_origin_state E initial buffers step current
  have moved := buffers.byte_views initial.good current.good rfl
    (byte_view_get_setI h zs state) (byte_view_ro_setI h zs state)
  have packet : DispatchBuffers after r regs bs := by
    refine ⟨moved.input, ?_, moved.separate, ?_⟩
    · exact ⟨moved.output.range, moved.output.nonnull, moved.output.count, moved.output.produced⟩
    · exact ⟨moved.bits.have_eq, moved.bits.next, moved.bits.hold_lt⟩
  obtain ⟨ref, array, off, pointer, oldGet, _write, room, _count, _produced, _private⟩ :=
    callerRange_slow_output initial.good l buffers.output.range buffers.output.nonnull
      buffers.output.count buffers.output.produced
  refine ⟨regs, after, state, step, origin, rfl, zero, packet, Or.inr ⟨ref, off, array, pointer, ?_, by omega, ?_⟩⟩
  · exact (byte_view_get_setI h zs state ref).trans oldGet
  · simp only [List.take_zero]

#print axioms stored_dispatch_COPY_metadata
#print axioms stored_COPY_zero_dispatch_prefix
/-- The zero-remaining counterpart completes the reference Body at the
real one-step COPY/TYPE boundary without attributing any new output. -/
theorem StoredCopyPartialTrace.zero_body_to_type
    {start h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {input output payload dictionary before : List UInt8} {bodyBits rest : List Bool}
    (initial : DefaultOriginState start r zs z s) (allocator : DefAlloc z)
    (length : s.length.toNat = payload.length)
    (history : StoredCopyPartialTrace start r zs h input output) (source : input <+: payload)
    (format : ZlibF.Spec.Body dictionary 0 before bodyBits rest (before ++ payload)) :
    ∃ stream0 state0, DefaultOriginState h r zs stream0 state0 ∧ DefAlloc stream0 ∧
      ∀ c nextBytes, c.strm = some r → c.st = some (.tab zs) →
        state0.mode = COPY → state0.length = 0 → StreamBuffers h r → stream0.next_out ≠ .null →
        Bytes h stream0.next_in stream0.avail_in.toNat nextBytes →
        ∃ regs after state,
          runX (inflate_dispatch c) (dispatchRegs stream0 state0) h = .ok ((.ok (), regs), after) ∧
          DefaultOriginState after r zs stream0 state ∧ state.mode = TYPE ∧ state.length = 0 ∧
          DispatchBuffers after r regs nextBytes ∧ Bytes after stream0.next_out 0 [] ∧ output = payload ∧
          ZlibF.Spec.Body dictionary 0 before bodyBits rest (before ++ output) := by
  obtain ⟨stream0, state0, current, currentAllocator, _copied, remaining, complete⟩ :=
    history.payload_progress initial allocator length source
  refine ⟨stream0, state0, current, currentAllocator, ?_⟩
  intro c nextBytes root owner mode zero buffers nonnull bytes
  have env : Env c h r zs stream0 state0 := ⟨root, owner, current.good.live.hz, current.good.live.hs⟩
  have view := header_input_view_of_bytes (s := state0) bytes current.held
  have outputView := dispatchRegs_output current.good.live.hz buffers nonnull state0
  obtain ⟨candidate, candidateGet, inputRange, _outputRange, separate⟩ := buffers
  have sameStream : candidate = stream0 := Option.some.inj (candidateGet.symm.trans current.good.live.hz)
  subst candidate
  have packet : DispatchBuffers h r (dispatchRegs stream0 state0) nextBytes :=
    ⟨inputRange, outputView, separate, view⟩
  obtain ⟨regs, after, state, step, final, finalMode, finalZero, finalPacket, written⟩ :=
    stored_COPY_zero_dispatch_prefix env current packet mode zero
  have empty : payload.drop input.length = [] := by
    apply List.length_eq_zero_iff.mp
    rw [zero] at remaining
    exact remaining.symm
  rw [empty, List.append_nil] at complete
  refine ⟨regs, after, state, step, final, finalMode, finalZero, finalPacket, written, complete, ?_⟩
  rw [complete]
  exact format

#print axioms StoredCopyPartialTrace.zero_body_to_type
end Zlib.Inflate.Proofs



namespace Zlib.Inflate.Proofs.StoredEnd
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WrapperGlue
set_option autoImplicit false

/-- Exact actual dispatch observations specialize the already-proved
memory boundary; post-state records are read from that same heap. -/
theorem origin_packet_of_actual
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat} {z stream0 : ZStream}
    {s state : InflateState} {l regs : IL} {bs : List UInt8} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (packet : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39)
    (actual : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (getZ : r.get after = some stream0) (getS : after.istates zs = some state) :
    DefaultOriginState after r zs stream0 state ∧
      DispatchBuffers after r regs (bs.drop (l.have_.toNat - regs.have_.toNat)) := by
  obtain ⟨exit, locals, heap0, stream1, state1, used, made, _bound, run, current,
    nextPacket, _sizes, _next, count, _put, _left, _bits, _rank⟩ :=
    inflate_dispatch_default_origin_state_rank E initial packet bits
  have same := Except.ok.inj (run.symm.trans actual)
  cases same
  have sameZ : stream1 = stream0 := Option.some.inj (current.good.live.hz.symm.trans getZ)
  have sameS : state1 = state := Option.some.inj (current.good.live.hs.symm.trans getS)
  subst stream1 state1
  have actualUse : used = l.have_.toNat - regs.have_.toNat := by omega
  rw [actualUse] at nextPacket
  exact ⟨current, nextPacket⟩

#print axioms origin_packet_of_actual
/-- The final complete stored-copy prefix retains the cumulative Adler
ledger while exposing its current uncredited output and real TYPE state. -/
theorem complete_copy_credit_to_type
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs credited : List UInt8}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (packet : DispatchBuffers h r l bs) (mode : s.mode = COPY) (nonempty : s.length ≠ 0)
    (enoughInput : s.length.toNat ≤ l.have_.toNat) (enoughOutput : s.length.toNat ≤ l.left.toNat)
    (credit : AdlerCredit z s credited) :
    ∃ firstRegs firstHeap firstState regs after state,
      runX (inflate_dispatch c) l h = .ok ((.ok (), firstRegs), firstHeap) ∧
      DefaultOriginState firstHeap r zs z firstState ∧ firstState.mode = COPY ∧ firstState.length = 0 ∧
      runX (inflate_dispatch c) firstRegs firstHeap = .ok ((.ok (), regs), after) ∧
      DefaultOriginState after r zs z state ∧ state.mode = TYPE ∧ state.length = 0 ∧
      DispatchBuffers after r regs (bs.drop s.length.toNat) ∧
      regs.next = inputAdvance l.next s.length.toNat ∧ regs.have_.toNat + s.length.toNat = l.have_.toNat ∧
      regs.put = inputAdvance l.put s.length.toNat ∧ regs.left.toNat + s.length.toNat = l.left.toNat ∧
      Bytes after l.put s.length.toNat (bs.take s.length.toNat) ∧
      DecodeStateFrame s state ∧ AdlerCredit z state credited ∧
      regs.bits = l.bits ∧ regs.out_ = l.out_ := by
  obtain ⟨firstRegs, firstHeap, firstState, regs, after, state,
    firstStep, firstJ, firstMode, firstZero, secondStep, final, finalMode, finalZero,
    finalPacket, next, haveCount, put, leftCount, copied, _reader⟩ :=
    stored_COPY_complete_dispatch_prefix E initial packet mode nonempty enoughInput enoughOutput
  have metadata := stored_dispatch_COPY_metadata E initial packet mode firstStep firstJ.good.live.hs
  have env1 : Env c firstHeap r zs z firstState := ⟨E.strm, E.st, firstJ.good.live.hz, firstJ.good.live.hs⟩
  have literal : runX (inflate_dispatch c) firstRegs firstHeap =
      .ok ((.ok (), { firstRegs with copy := 0 }), setI firstHeap zs { firstState with mode := TYPE }) := by
    rw [inflate_dispatch_COPY env1 firstRegs firstMode]
    exact inflate_COPY_done env1 firstRegs firstZero
  have same := Except.ok.inj (secondStep.symm.trans literal)
  cases same
  have get : (setI firstHeap zs { firstState with mode := TYPE }).istates zs =
      some { firstState with mode := TYPE } := by simp only [setI_istates_same]
  have sameState : state = { firstState with mode := TYPE } :=
    Option.some.inj (final.good.live.hs.symm.trans get)
  subst state
  have frame : DecodeStateFrame s { firstState with mode := TYPE } := metadata.1.trans rfl
  exact ⟨firstRegs, firstHeap, firstState, { firstRegs with copy := 0 }, _, _,
    firstStep, firstJ, firstMode, firstZero, secondStep, final, finalMode, finalZero,
    finalPacket, next, haveCount, put, leftCount, copied, frame, adlerCredit_decode credit frame,
    metadata.2.1, metadata.2.2⟩

#print axioms complete_copy_credit_to_type
/-- The last-block TYPE step uses the real TYPE/TYPEDO/BYTEBITS path.
With no held payload bits it reaches CHECK on the same unread bytes. -/
theorem last_type_to_check
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs credited : List UInt8}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (packet : DispatchBuffers h r l bs) (mode : s.mode = TYPE) (last : s.last ≠ 0)
    (flush : c.flush ≠ Z_BLOCK ∧ c.flush ≠ Z_TREES) (bits : l.bits = 0)
    (credit : AdlerCredit z s credited) :
    ∃ after state, runX (inflate_dispatch c) l h = .ok ((.ok (), l), after) ∧
      DefaultOriginState after r zs z state ∧ state.mode = CHECK ∧
      DispatchBuffers after r l bs ∧ AdlerCredit z state credited ∧
      ∀ ref : BRef, Space.get after ref = Space.get h ref := by
  let state := { s with mode := CHECK }
  let after := setI h zs state
  have aligned : bytebits l = l := by cases l; simp_all [bytebits]
  have actual : runX (inflate_dispatch c) l h = .ok ((.ok (), l), after) := by
    rw [inflate_dispatch_block_type E l (Or.inl mode), ite_eq_left mode,
      inflate_TYPE_go c l h flush, inflate_TYPEDO_last E l last, aligned]
  have getZ : r.get after = some z := by rw [ZStreamRef.get_setI]; exact E.hz
  have getS : after.istates zs = some state := by simp only [after, setI_istates_same]
  obtain ⟨current, packet0⟩ := origin_packet_of_actual E initial packet (by rw [bits]; decide) actual getZ getS
  rw [Nat.sub_self, List.drop_zero] at packet0
  exact ⟨after, state, actual, current, rfl, packet0, adlerCredit_decode credit rfl,
    byte_view_get_setI h zs state⟩

#print axioms last_type_to_check
/-- A real CHECK dispatch validates the independent trailer and commits
exactly the physical output suffix. It retains the unread packet and all
byte views; no success result or checksum callee contract is assumed. -/
theorem check_payload_dispatch
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs credited incoming : List UInt8} {future : List Bool}
    {ref : BRef} {off : Nat} {a : Array UInt8}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (packet : DispatchBuffers h r l bs) (mode : s.mode = CHECK)
    (bits : l.bits = 0) (credit : AdlerCredit z s credited)
    (nonempty : l.out_ - l.left ≠ 0)
    (pointer : l.put = .ref ref off) (get : Space.get h ref = some a)
    (start : (l.out_ - l.left).toNat ≤ off) (bound : off ≤ a.size)
    (written : ZlibF.Math.LZ77Copy.writtenBytes a off (l.out_ - l.left).toNat = incoming)
    (source : stream l bs = bytesBits (be32 (adler32 (credited ++ incoming)).toNat) ++ future) :
    ∃ regs after stream0 state used,
      runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, regs), after) ∧
      DefaultOriginState after r zs stream0 state ∧ state.mode = DONE ∧
      DispatchBuffers after r regs (bs.drop used) ∧ used ≤ bs.length ∧
      AdlerCredit stream0 state (credited ++ incoming) ∧
      stream0.zalloc = z.zalloc ∧ stream0.zfree = z.zfree ∧
      regs.out_ = regs.left ∧ regs.ret = Z_STREAM_END ∧ regs.bits = 0 ∧
      regs.put = l.put ∧ regs.left = l.left ∧
      stream regs (bs.drop used) = future ∧
      (∀ ref0 : BRef, Space.get after ref0 = Space.get h ref0) := by
  obtain ⟨pulled, used, pull, usedBound, inv, bits32, next, outField, leftField, putField,
    trailer, remainder⟩ := wrapper_NEEDBITS_valid_be32 packet.bits
      (by rw [bits]; decide) (by rw [bits]; decide) (adler32 (credited ++ incoming)) future source
  let stream0 : ZStream := { z with total_out := z.total_out + (l.out_ - l.left).toUInt64, adler := (adler32 (credited ++ incoming)).toUInt64 }
  let state : InflateState := { s with total := s.total + (l.out_ - l.left).toUInt64, check := (adler32 (credited ++ incoming)).toUInt64, mode := DONE }
  let after := setI (r.put h stream0) zs state
  let regs := { pulled with out_ := l.left, hold := 0, bits := 0, ret := Z_STREAM_END }
  have actual : runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, regs), after) := by
    rw [inflate_dispatch_CHECK E l mode]
    exact inflate_CHECK_zlib_output_append_cut E credit.1 credit.2.1 credit.2.2.1
      nonempty pointer get start bound written pull outField leftField putField trailer
  have getZ : r.get after = some stream0 := by
    rw [ZStreamRef.get_setI, ZStreamRef.get_put_same E.hz]
  have getS : after.istates zs = some state := by simp only [after, setI_istates_same]
  obtain ⟨current, nextPacket⟩ := origin_packet_of_actual E initial packet
    (by rw [bits]; decide) actual getZ getS
  have consumed : l.have_.toNat - regs.have_.toNat = used := by
    have old := packet.bits.have_eq
    have now := inv.have_eq
    dsimp only [regs]
    rw [List.length_drop] at now
    omega
  rw [consumed] at nextPacket
  have finalCredit : AdlerCredit stream0 state (credited ++ incoming) := by
    exact ⟨credit.1, credit.2.1, rfl, rfl⟩
  refine ⟨regs, after, stream0, state, used, actual, current, rfl, nextPacket, usedBound,
    finalCredit, rfl, rfl, ?_, rfl, rfl, putField, leftField, ?_, ?_⟩
  · exact leftField.symm
  · simpa only [regs, stream] using remainder
  · intro ref0
    rw [byte_view_get_setI, byte_view_get_stream_put]

#print axioms check_payload_dispatch
/-- A selected final stored payload runs through both COPY dispatches,
TYPE, and the valid zlib trailer to the real main-loop END exit. The
payload is an independent input packet, and output bytes are derived
from the actual copy, including same-allocation separated slices. -/
theorem last_stored_loop_end
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs credited payload tail : List UInt8}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (packet : DispatchBuffers h r l bs) (mode : s.mode = COPY) (last : s.last ≠ 0)
    (nonempty : s.length ≠ 0) (length : s.length.toNat = payload.length)
    (enoughOutput : s.length.toNat ≤ l.left.toNat) (bits : l.bits = 0)
    (freshOutput : l.out_ = l.left) (flush : c.flush ≠ Z_BLOCK ∧ c.flush ≠ Z_TREES)
    (credit : AdlerCredit z s credited)
    (source : bs = payload ++ be32 (adler32 (credited ++ payload)).toNat ++ tail) :
    ∃ regs after stream0 state remaining,
      runX (xwhile (pure true) (inflate_dispatch c)) l h = .ok ((.error Ex.leave, regs), after) ∧
      DefaultOriginState after r zs stream0 state ∧ state.mode = DONE ∧
      DispatchBuffers after r regs remaining ∧
      AdlerCredit stream0 state (credited ++ payload) ∧
      stream0.zalloc = z.zalloc ∧ stream0.zfree = z.zfree ∧
      regs.out_ = regs.left ∧ regs.ret = Z_STREAM_END ∧ regs.bits = 0 ∧
      regs.put = inputAdvance l.put payload.length ∧ regs.left.toNat + payload.length = l.left.toNat ∧
      Bytes after l.put payload.length payload ∧ stream regs remaining = bytesBits tail := by
  have enoughInput : s.length.toNat ≤ l.have_.toNat := by
    rw [packet.bits.have_eq, source, List.length_append, List.length_append, length]
    omega
  obtain ⟨firstRegs, firstHeap, firstState, typeRegs, typeHeap, typeState,
    copyStep, firstJ, firstMode, firstZero, zeroStep, typeJ, typeMode, typeZero,
    typePacket, typeNext, typeHave, typePut, typeLeft, copied, frame, typeCredit,
    typeBits, typeOut⟩ := complete_copy_credit_to_type E initial packet mode nonempty
      enoughInput enoughOutput credit
  have payloadTake : bs.take s.length.toNat = payload := by
    rw [source, length, List.append_assoc, List.take_left]
  rw [payloadTake, length] at copied
  have typeLast : typeState.last ≠ 0 := by rw [frame]; exact last
  have typeBits0 : typeRegs.bits = 0 := typeBits.trans bits
  have typeEnv : Env c typeHeap r zs z typeState :=
    ⟨E.strm, E.st, typeJ.good.live.hz, typeJ.good.live.hs⟩
  obtain ⟨checkHeap, checkState, typeStep, checkJ, checkMode, checkPacket, checkCredit, checkViews⟩ :=
    last_type_to_check typeEnv typeJ typePacket typeMode typeLast flush typeBits0 typeCredit
  have checkEnv : Env c checkHeap r zs z checkState :=
    ⟨E.strm, E.st, checkJ.good.live.hz, checkJ.good.live.hs⟩
  have count : (typeRegs.out_ - typeRegs.left).toNat = payload.length := by
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by rw [typeOut, freshOutput]; omega))]
    rw [typeOut, freshOutput]
    omega
  have outputNonempty : typeRegs.out_ - typeRegs.left ≠ 0 := by
    intro zero
    have count0 := congrArg UInt32.toNat zero
    have nonzero : s.length.toNat ≠ 0 := fun zero => nonempty (UInt32.toNat_inj.mp zero)
    rw [count] at count0
    simp only [UInt32.toNat_zero] at count0
    omega
  rcases copied with ⟨null, size0, empty⟩ | ⟨ref, off, a, ptr, get, room, values⟩
  · have nonzero : s.length.toNat ≠ 0 := fun zero => nonempty (UInt32.toNat_inj.mp zero)
    omega
  have checkGet : Space.get checkHeap ref = some a := (checkViews ref).trans get
  have currentPut : typeRegs.put = .ref ref (off + payload.length) := by
    rw [typePut, ptr, length]
    rfl
  have observed : ZlibF.Math.LZ77Copy.writtenBytes a (off + payload.length)
      (typeRegs.out_ - typeRegs.left).toNat = payload := by
    rw [count]
    simpa only [ZlibF.Math.LZ77Copy.writtenBytes, Nat.add_sub_cancel] using values.symm
  have sourceRest : bs.drop s.length.toNat = be32 (adler32 (credited ++ payload)).toNat ++ tail := by
    rw [source, length, List.append_assoc, List.drop_left]
  have bitSource : stream typeRegs (bs.drop s.length.toNat) =
      bytesBits (be32 (adler32 (credited ++ payload)).toNat) ++ bytesBits tail := by
    rw [stream, typeBits0]
    simp only [UInt32.toNat_zero, natBits, List.range_zero, List.map_nil, List.nil_append, sourceRest, bytesBits_append]
  obtain ⟨regs, after, stream0, state, used, checkStep, final, doneMode, finalPacket,
    usedBound, finalCredit, finalAlloc, finalFree, zeroOut, ended, finalBits, finalPut, finalLeft, remainder, byteViews⟩ :=
    check_payload_dispatch checkEnv checkJ checkPacket checkMode typeBits0 checkCredit
      outputNonempty currentPut checkGet (by rw [count]; omega) room observed bitSource
  let locals : Nat → IL := fun j => if j = 0 then l else if j = 1 then firstRegs else typeRegs
  let heaps : Nat → Heap := fun j => if j = 0 then h else if j = 1 then firstHeap else if j = 2 then typeHeap else checkHeap
  have steps : ∀ j, j < 3 → runX (inflate_dispatch c) (locals j) (heaps j) =
      .ok ((.ok (), locals (j + 1)), heaps (j + 1)) := by
    intro j bound
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · exact copyStep
    · exact zeroStep
    · exact typeStep
  have loop := xwhile_run_chain (inflate_dispatch c) locals heaps 3 (by decide) Ex.leave regs after steps checkStep
  have finalBytes : Bytes after l.put payload.length payload := by
    right
    exact ⟨ref, off, a, ptr, (byteViews ref).trans checkGet, room, values⟩
  exact ⟨regs, after, stream0, state, (bs.drop s.length.toNat).drop used,
    loop, final, doneMode, finalPacket, finalCredit, finalAlloc, finalFree, zeroOut, ended, finalBits,
    by rw [finalPut, typePut, length], by rw [finalLeft]; omega, finalBytes, remainder⟩

#print axioms last_stored_loop_end
/-- The loaded final stored path, including actual RESTORE/window/leave,
returns END and exactly the independent payload. Trailer validation has
already rebased output accounting, so leave cannot take its MEM branch. -/
theorem last_stored_body_end
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {bs credited payload tail : List UInt8}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (allocator : DefAlloc z) (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (input : BitInv h (dispatchRegs z s) bs) (mode : s.mode = COPY) (last : s.last ≠ 0)
    (nonempty : s.length ≠ 0) (length : s.length.toNat = payload.length)
    (enoughOutput : s.length.toNat ≤ z.avail_out.toNat) (bits : s.bits = 0)
    (flush : c.flush ≠ Z_BLOCK ∧ c.flush ≠ Z_TREES) (credit : AdlerCredit z s credited)
    (source : bs = payload ++ be32 (adler32 (credited ++ payload)).toNat ++ tail) :
    ∃ after stream0 state,
      (do let (result, regs) ← runX (inflate_run c) IL.init
          match result with
          | .error (.ret value) => pure value
          | _ => inflate_leave c regs) h = .ok (Z_STREAM_END, after) ∧
      r.get after = some stream0 ∧ after.istates zs = some state ∧
      AdlerCredit stream0 state (credited ++ payload) ∧
      Bytes after z.next_out payload.length payload := by
  have output := dispatchRegs_output E.hz buffers nonnull s
  obtain ⟨z0, zget, inputRange, outputRange, separate⟩ := buffers
  have sameZ : z0 = z := Option.some.inj (zget.symm.trans E.hz)
  subst z0
  have packet : DispatchBuffers h r (dispatchRegs z s) bs := ⟨inputRange, output, separate, input⟩
  obtain ⟨regs, checkHeap, current, checkState, remaining, loop, final, doneMode,
    finalPacket, finalCredit, finalAlloc, finalFree, zeroOut, ended, finalBits, finalPut,
    finalLeft, copied, remainder⟩ := last_stored_loop_end E initial packet mode last nonempty
      length enoughOutput bits rfl flush credit source
  have env1 : Env c checkHeap r zs current checkState :=
    ⟨E.strm, E.st, final.good.live.hz, final.good.live.hs⟩
  have alloc1 : DefAlloc current := ⟨finalAlloc.trans allocator.1, finalFree.trans allocator.2⟩
  obtain ⟨after, stream0, state, leave, getZ, getS, finalCredit0⟩ :=
    inflate_leave_after_CHECK_adler env1 final.good alloc1.1 final.pending finalPacket
      (by rw [finalBits]; decide) finalCredit zeroOut ended
  have body : runX (inflate_run c) IL.init h = .ok ((.error Ex.leave, regs), checkHeap) := by
    unfold inflate_run
    rw [runX_bind, runX_rdS E]
    simp only [mode]
    change runX (do
      LOAD c.strm c.st
      modify fun l => { l with in_ := l.have_, out_ := l.left, ret := Z_OK }
      xwhile (pure true) (inflate_dispatch c)) IL.init h = _
    rw [runX_bind, LOAD_run E]
    simp only []
    rw [runX_bind, runX_modify]
    exact loop
  have copied0 : Bytes after z.next_out payload.length payload := by
    rcases copied with ⟨null, size0, empty⟩ | ⟨ref, off, a, pointer, get, room, values⟩
    · exact False.elim (nonnull null)
    · have pointer0 : regs.put = .ref ref (off + payload.length) := by
        rw [finalPut, pointer]
        rfl
      have saved := inflate_leave_output_view_unchanged env1 final.toDefaultStateJ alloc1
        finalPacket (by rw [finalBits]; decide) leave pointer0 get
      exact Or.inr ⟨ref, off, a, pointer, saved.2.1, room, values⟩
  refine ⟨after, stream0, state, ?_, getZ, getS, finalCredit0, copied0⟩
  rw [bind_app, body]
  exact leave

#print axioms last_stored_body_end
/-- A real public call starting in a represented final stored COPY state
returns END after validating the independent trailer, with exact payload
bytes and cumulative Adler credit. The public temporary is actually freed.
This phase theorem does not assert initialization-to-COPY reachability. -/
theorem last_stored_public_end
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {bs credited payload tail : List UInt8} {flush : Int32}
    (initial : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (inputBytes : Bytes h z.next_in z.avail_in.toNat bs)
    (mode : s.mode = COPY) (last : s.last ≠ 0) (nonempty : s.length ≠ 0)
    (length : s.length.toNat = payload.length) (enoughOutput : s.length.toNat ≤ z.avail_out.toNat)
    (bits : s.bits = 0) (flushOK : flush ≠ Z_BLOCK ∧ flush ≠ Z_TREES)
    (credit : AdlerCredit z s credited)
    (source : bs = payload ++ be32 (adler32 (credited ++ payload)).toNat ++ tail) :
    ∃ after stream0 state,
      C.run (inflate (some r) flush) h = .ok (Z_STREAM_END, after) ∧
      DefaultStateJ after r zs stream0 state ∧ DefAlloc stream0 ∧
      AdlerCredit stream0 state (credited ++ payload) ∧
      Bytes after z.next_out payload.length payload ∧ after.bytes h.nextBlk = none := by
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have allocated := default_origin_syncAlloc initial
  have env : Env c (syncAlloc h) r zs z s :=
    ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  have input := header_input_view_of_bytes (s := s) inputBytes initial.held
  have input0 : BitInv (syncAlloc h) (dispatchRegs z s) bs := by
    refine ⟨input.have_eq, ?_, input.hold_lt⟩
    rcases input.next with empty | ⟨ref, array, off, pointer, get, bound, values⟩
    · exact Or.inl empty
    · exact Or.inr ⟨ref, array, off, pointer,
        (byte_view_syncAlloc initial.good.fresh get).1, bound, values⟩
  obtain ⟨bodyHeap, stream0, state, body, getZ, getS, finalCredit, copied⟩ :=
    last_stored_body_end env allocated allocator
      (streamBuffers_syncAlloc initial.good.fresh buffers) nonnull input0 mode last nonempty
      length enoughOutput bits flushOK credit source
  obtain ⟨run, final, finalAlloc, freed, finalCredit0⟩ :=
    inflate_public_close_body_adler initial.toDefaultStateJ allocator buffers nonnull inputValid
      body getZ getS finalCredit
  have copied0 : Bytes (freeWin bodyHeap (syncBuf h)) z.next_out payload.length payload := by
    obtain ⟨ref, old, off, pointer, original, _write, _room, _count, _produced, _private⟩ :=
      callerRange_slow_output initial.good (dispatchRegs z s)
        (dispatchRegs_output initial.good.live.hz buffers nonnull s).range nonnull
        (dispatchRegs_output initial.good.live.hz buffers nonnull s).count
        (dispatchRegs_output initial.good.live.hz buffers nonnull s).produced
    rcases copied with ⟨null, zero, empty⟩ | ⟨ref1, off1, array, pointer1, get, room, values⟩
    · exact False.elim (nonnull null)
    · have ptrEq : Ptr.ref ref off = Ptr.ref ref1 off1 := pointer.symm.trans pointer1
      cases ptrEq
      exact Or.inr ⟨ref, off, array, pointer,
        stored_byte_view_free_local initial.good.fresh original get, room, values⟩
  exact ⟨freeWin bodyHeap (syncBuf h), stream0, state, run, final, finalAlloc, finalCredit0, copied0, freed⟩

#print axioms last_stored_public_end
/-- The exact finite partial-call invariant supplies the stored byte debt
and independent Body meaning to a real public final call. Its current
Adler ledger is an explicit phase relation: MEM paths may not replace it
with all observed output, because their leave skips checksum credit. -/
theorem partial_trace_public_finish
    {start h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {input output payload dictionary before base : List UInt8} {bodyBits rest : List Bool}
    (initial : DefaultOriginState start r zs z s) (allocator : DefAlloc z)
    (length : s.length.toNat = payload.length)
    (history : StoredCopyPartialTrace start r zs h input output) (inputPrefix : input <+: payload)
    (format : ZlibF.Spec.Body dictionary 0 before bodyBits rest (before ++ payload)) :
    ∃ stream0 state0, DefaultOriginState h r zs stream0 state0 ∧ DefAlloc stream0 ∧
      state0.length.toNat = (payload.drop input.length).length ∧
      ∀ nextBytes tail flush, state0.mode = COPY → state0.last ≠ 0 → state0.length ≠ 0 →
        StreamBuffers h r → stream0.next_out ≠ .null →
        (stream0.next_in = .null → stream0.avail_in = 0) →
        Bytes h stream0.next_in stream0.avail_in.toNat nextBytes →
        state0.length.toNat ≤ stream0.avail_out.toNat → state0.bits = 0 →
        (flush ≠ Z_BLOCK ∧ flush ≠ Z_TREES) →
        AdlerCredit stream0 state0 (base ++ output) →
        nextBytes = payload.drop input.length ++ be32 (adler32 (base ++ payload)).toNat ++ tail →
        ∃ after stream1 state1,
          C.run (inflate (some r) flush) h = .ok (Z_STREAM_END, after) ∧
          DefaultStateJ after r zs stream1 state1 ∧ DefAlloc stream1 ∧
          AdlerCredit stream1 state1 (base ++ payload) ∧
          Bytes after stream0.next_out (payload.drop input.length).length (payload.drop input.length) ∧
          output ++ payload.drop input.length = payload ∧
          ZlibF.Spec.Body dictionary 0 before bodyBits rest (before ++ (output ++ payload.drop input.length)) := by
  obtain ⟨stream0, state0, current, currentAllocator, _copied, remaining, complete⟩ :=
    history.payload_progress initial allocator length inputPrefix
  refine ⟨stream0, state0, current, currentAllocator, remaining, ?_⟩
  intro nextBytes tail flush mode last nonempty buffers nonnull inputValid inputBytes enoughOutput bits flushOK credit source
  have ledger : (base ++ output) ++ payload.drop input.length = base ++ payload := by
    rw [List.append_assoc, complete]
  have packet : nextBytes = payload.drop input.length ++
      be32 (adler32 ((base ++ output) ++ payload.drop input.length)).toNat ++ tail := by
    rw [ledger]
    exact source
  obtain ⟨after, stream1, state1, run, final, finalAlloc, finalCredit, copied, _freed⟩ :=
    last_stored_public_end current currentAllocator buffers nonnull inputValid inputBytes
      mode last nonempty remaining enoughOutput bits flushOK credit packet
  rw [ledger] at finalCredit
  exact ⟨after, stream1, state1, run, final, finalAlloc, finalCredit, copied, complete,
    by rw [complete]; exact format⟩

#print axioms partial_trace_public_finish
end Zlib.Inflate.Proofs.StoredEnd

namespace Zlib.Inflate.Proofs.StoredHistory
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WrapperGlue Zlib.Inflate.Proofs.StoredEnd
set_option autoImplicit false

/-- The finite actual partial COPY loop also retains checksum/last fields,
the original held word, and the output-credit base. -/
theorem short_loop_metadata {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = COPY)
    (short : (copyAmt s.length l.have_ l.left).toNat < s.length.toNat) :
    ∃ regs after state made, made ≤ bs.length ∧
      runX (xwhile (pure true) (inflate_dispatch c)) l h = .ok ((.error Ex.leave, regs), after) ∧
      DefaultOriginState after r zs z state ∧ DispatchBuffers after r regs (bs.drop made) ∧
      regs.have_.toNat + made = l.have_.toNat ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.next = inputAdvance l.next made ∧ regs.put = inputAdvance l.put made ∧
      regs.bits = l.bits ∧ state.length.toNat + made = s.length.toNat ∧
      Bytes after l.put made (bs.take made) ∧ DecodeStateFrame s state ∧ regs.out_ = l.out_ ∧ regs.hold = l.hold := by
  obtain ⟨outcome, regs, after, state, made, bound, run, current, _tables, _pending,
    packet, _sizes, _frame, next, haveCount, put, leftCount, bits, held, kind, _static, _shape⟩ :=
    inflate_COPY_boundary_frame E initial.good initial.pending buffers mode
  have step := (inflate_dispatch_COPY E l mode).trans run
  have metadata := stored_dispatch_COPY_metadata E initial buffers mode step current.live.hs
  have payload := stored_COPY_payload_of_run E initial.good buffers run leftCount
  obtain ⟨outcome0, regs0, after0, state0, actual0, currentJ, _modes⟩ :=
    inflate_COPY_default_state E initial.toDefaultStateJ buffers mode
  have same : ((outcome, regs), after) = ((outcome0, regs0), after0) := Except.ok.inj (run.symm.trans actual0)
  cases same
  have sameState : state = state0 := Option.some.inj (current.live.hs.symm.trans currentJ.good.live.hs)
  subst state0
  have origin := inflate_dispatch_default_origin_state E initial buffers step currentJ
  have nonempty : s.length ≠ 0 := by intro zero; rw [zero] at short; change _ < 0 at short; omega
  have amount := payload.2.1 nonempty
  have debt := payload.2.2.2 state current.live.hs
  rcases kind with waiting | completed | copied
  · obtain ⟨exit, zero, _sameState⟩ := waiting
    subst outcome
    have loop := xwhile_run_chain (inflate_dispatch c) (fun _ => l) (fun _ => h)
      0 (by unfold fuel; decide) Ex.leave regs after (by intro j impossible; omega) step
    exact ⟨regs, after, state, made, bound, loop, origin, packet, haveCount, leftCount,
      next, put, bits, debt, payload.1, metadata.1, metadata.2.2, held⟩
  · obtain ⟨exit, zero, _type⟩ := completed
    have none : copyAmt s.length l.have_ l.left = 0 := by
      apply UInt32.toNat_inj.mp
      change (copyAmt s.length l.have_ l.left).toNat = 0
      omega
    have actual := inflate_COPY_leave E l nonempty none
    rw [run, exit] at actual
    cases actual
  · obtain ⟨exit, positive, copying, _remaining⟩ := copied
    subst outcome
    have remains : state.length ≠ 0 := by intro zero; rw [zero] at debt; change 0 + made = _ at debt; omega
    have exhausted := stored_copyAmt_short_exhausts s.length l.have_ l.left short
    have stalled : copyAmt state.length regs.have_ regs.left = 0 := by
      have bounds := copyAmt_le state.length regs.have_ regs.left
      apply UInt32.toNat_inj.mp
      change (copyAmt state.length regs.have_ regs.left).toNat = 0
      rcases exhausted with noInput | noOutput <;> omega
    have env : Env c after r zs z state := ⟨E.strm, E.st, current.live.hz, current.live.hs⟩
    let last := { regs with copy := 0 }
    have stop : runX (inflate_dispatch c) regs after = .ok ((.error Ex.leave, last), after) := by
      rw [inflate_dispatch_COPY env regs copying]
      exact inflate_COPY_leave env regs remains stalled
    have loop := xwhile_run_chain (inflate_dispatch c)
      (fun j => if j = 0 then l else regs) (fun j => if j = 0 then h else after)
      1 (by unfold fuel; decide) Ex.leave last after
      (by
        intro j hj
        have zero : j = 0 := by omega
        subst j
        simpa using step)
      (by simpa only [Nat.one_ne_zero, ite_false] using stop)
    have finalPacket : DispatchBuffers after r last (bs.drop made) := by
      refine ⟨packet.input, ?_, packet.separate, ?_⟩
      · exact ⟨packet.output.range, packet.output.nonnull, packet.output.count, packet.output.produced⟩
      · exact ⟨packet.bits.have_eq, packet.bits.next, packet.bits.hold_lt⟩
    exact ⟨last, after, state, made, bound, by simpa only [ite_true] using loop,
      origin, finalPacket, haveCount, leftCount, next, put, bits, debt, payload.1, metadata.1, metadata.2.2, held⟩

#print axioms short_loop_metadata
/-- A real partial stored public-body call commits precisely the copied
prefix to Adler on ordinary leave. A real window allocation failure keeps
the old ledger, even though the copied output bytes remain observable. -/
theorem short_body_adler
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs credited : List UInt8}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (allocator : DefAlloc z) (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (input : BitInv h (dispatchRegs z s) bs) (mode : s.mode = COPY)
    (short : (copyAmt s.length z.avail_in z.avail_out).toNat < s.length.toNat)
    (credit : AdlerCredit z s credited) :
    ∃ rc after stream0 state made, made ≤ bs.length ∧
      (do let (result, regs) ← runX (inflate_run c) IL.init
          match result with
          | .error (.ret value) => pure value
          | _ => inflate_leave c regs) h = .ok (rc, after) ∧
      DefaultOriginState after r zs stream0 state ∧ DefAlloc stream0 ∧
      state.length.toNat + made = s.length.toNat ∧
      stream0.next_in = inputAdvance z.next_in made ∧ stream0.avail_in.toNat + made = z.avail_in.toNat ∧
      stream0.next_out = inputAdvance z.next_out made ∧ stream0.avail_out.toNat + made = z.avail_out.toNat ∧
      Bytes after z.next_out made (bs.take made) ∧
      (AdlerCredit stream0 state (credited ++ bs.take made) ∨
        (rc = Z_MEM_ERROR ∧ state.mode = MEM ∧ AdlerCredit stream0 state credited)) := by
  have output := dispatchRegs_output E.hz buffers nonnull s
  obtain ⟨z0, get0, inputRange, outputRange, separate⟩ := buffers
  have sameZ : z0 = z := Option.some.inj (get0.symm.trans E.hz)
  subst z0
  have packet : DispatchBuffers h r (dispatchRegs z s) bs := ⟨inputRange, output, separate, input⟩
  obtain ⟨regs, heap0, state0, made, madeBound, loop, current, packet0,
    haveCount, leftCount, next, put, bitsEq, debt, copied, frame, outBase, held⟩ :=
    short_loop_metadata E initial packet mode short
  have bitsBound : regs.bits.toNat ≤ 39 := by rw [bitsEq]; exact initial.good.inv.bits
  have env0 : Env c heap0 r zs z state0 := ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
  have credit0 : AdlerCredit z state0 credited := adlerCredit_decode credit frame
  obtain ⟨rc, after, stream0, state, ref, off, a, incoming, leave, final, finalAlloc,
    pointer, get, view, written, incomingLength, observed, cursor, count, outcome⟩ :=
    inflate_leave_adler_observed env0 current.toDefaultStateJ allocator packet0 bitsBound credit0
  change regs.left.toNat + made = z.avail_out.toNat at leftCount
  have countMade : (regs.out_ - regs.left).toNat = made := by
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by rw [outBase]; exact Nat.le.intro leftCount))]
    rw [outBase]
    change z.avail_out.toNat - regs.left.toNat = made
    omega
  have inputCopy : incoming = bs.take made := by
    rcases copied with ⟨null, zero, empty⟩ | ⟨ref1, off1, a1, pointer1, get1, room, values⟩
    · exact False.elim (nonnull null)
    · have pointer0 : regs.put = .ref ref1 (off1 + made) := by rw [put, pointer1]; rfl
      have same := pointer0.symm.trans pointer
      injection same with sameRef sameOff
      subst ref off
      have sameArray : a1 = a := Option.some.inj (get1.symm.trans get)
      subst a1
      have physical : Bytes after z.next_out made (bs.take made) :=
        Or.inr ⟨ref1, off1, a, pointer1, view, room, values⟩
      rw [countMade] at incomingLength observed
      have observe0 : Bytes after z.next_out made incoming := by
        rw [show z.next_out = .ref ref1 off1 from pointer1]
        simpa only [incomingLength, Nat.add_sub_cancel] using observed
      exact wrapper_bytes_unique observe0 physical
  have entry : runX (inflate_run c) IL.init h =
      runX (xwhile (pure true) (inflate_dispatch c)) (dispatchRegs z s) h := by
    unfold inflate_run
    rw [runX_bind, runX_rdS E]
    have noType : s.mode ≠ TYPE := by rw [mode]; decide
    simp only [noType, beq_iff_eq, ite_false, runX_bind]
    rw [LOAD_run E]
    simp only []
    rw [runX_modify]
    rfl
  have body : (do
      let (result, regs) ← runX (inflate_run c) IL.init
      match result with
      | .error (.ret value) => pure value
      | _ => inflate_leave c regs) h = .ok (rc, after) := by
    rw [bind_app, entry, loop]
    exact leave
  obtain ⟨rc1, after1, stream1, state1, made1, bound1, body1, final1, alloc1,
    debt1, next1, have1, put1, left1, copied1⟩ := stored_COPY_short_body_payload E initial allocator
      ⟨z, E.hz, inputRange, outputRange, separate⟩ nonnull input mode short
  have same := Except.ok.inj (body.symm.trans body1)
  cases same
  have sameZ : stream1 = stream0 := Option.some.inj (final1.good.live.hz.symm.trans final.good.live.hz)
  have sameS : state1 = state := Option.some.inj (final1.good.live.hs.symm.trans final.good.live.hs)
  subst stream1 state1
  have madeEq : made1 = made := by rw [count] at left1; omega
  subst made1
  refine ⟨rc, after, stream0, state, made, madeBound, body, final1, alloc1,
    debt1, next1, have1, put1, left1, copied1, ?_⟩
  rcases outcome with ordinary | failure
  · exact Or.inl (by rw [inputCopy] at ordinary; exact ordinary.2)
  · exact Or.inr failure

#print axioms short_body_adler
/-- Public allocation and cleanup preserve the actual partial COPY
ledger observation, including the real MEM/old-ledger branch. -/
theorem short_public_adler
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {bs credited : List UInt8} {flush : Int32}
    (initial : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (inputBytes : Bytes h z.next_in z.avail_in.toNat bs) (mode : s.mode = COPY)
    (short : (copyAmt s.length z.avail_in z.avail_out).toNat < s.length.toNat)
    (credit : AdlerCredit z s credited) :
    ∃ rc after stream0 state made, made ≤ bs.length ∧
      C.run (inflate (some r) flush) h = .ok (rc, after) ∧
      DefaultOriginState after r zs stream0 state ∧ DefAlloc stream0 ∧
      state.length.toNat + made = s.length.toNat ∧
      stream0.next_in = inputAdvance z.next_in made ∧ stream0.avail_in.toNat + made = z.avail_in.toNat ∧
      stream0.next_out = inputAdvance z.next_out made ∧ stream0.avail_out.toNat + made = z.avail_out.toNat ∧
      Bytes after z.next_out made (bs.take made) ∧ after.bytes h.nextBlk = none ∧
      (AdlerCredit stream0 state (credited ++ bs.take made) ∨
        (rc = Z_MEM_ERROR ∧ state.mode = MEM ∧ AdlerCredit stream0 state credited)) := by
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have allocated := default_origin_syncAlloc initial
  have env : Env c (syncAlloc h) r zs z s :=
    ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  have input := header_input_view_of_bytes (s := s) inputBytes initial.held
  have input0 : BitInv (syncAlloc h) (dispatchRegs z s) bs := by
    refine ⟨input.have_eq, ?_, input.hold_lt⟩
    rcases input.next with empty | ⟨ref, array, off, pointer, get, bound, values⟩
    · exact Or.inl empty
    · exact Or.inr ⟨ref, array, off, pointer,
        (byte_view_syncAlloc initial.good.fresh get).1, bound, values⟩
  obtain ⟨rc, bodyHeap, stream0, state, made, madeBound, body, current, bodyAlloc,
    debt, next, haveCount, put, leftCount, copied, outcome⟩ := short_body_adler env allocated allocator
      (streamBuffers_syncAlloc initial.good.fresh buffers) nonnull input0 mode short credit
  obtain ⟨otherStream, otherState, run, final, finalAllocator, freed, getZ, getS⟩ :=
    inflate_public_close_body initial.toDefaultStateJ allocator buffers nonnull inputValid body
  have sameZ : otherStream = stream0 := Option.some.inj (getZ.symm.trans current.good.live.hz)
  have sameS : otherState = state := Option.some.inj (getS.symm.trans current.good.live.hs)
  subst otherStream otherState
  have finalOrigin := current.of_fields final rfl rfl rfl
  have copied0 : Bytes (freeWin bodyHeap (syncBuf h)) z.next_out made (bs.take made) := by
    obtain ⟨ref, old, off, pointer, original, _write, _room, _count, _produced, _private⟩ :=
      callerRange_slow_output initial.good (dispatchRegs z s)
        (dispatchRegs_output initial.good.live.hz buffers nonnull s).range nonnull
        (dispatchRegs_output initial.good.live.hz buffers nonnull s).count
        (dispatchRegs_output initial.good.live.hz buffers nonnull s).produced
    rcases copied with ⟨null, zero, empty⟩ | ⟨ref1, off1, array, pointer1, get, room, values⟩
    · exact False.elim (nonnull null)
    · have ptrEq : Ptr.ref ref off = Ptr.ref ref1 off1 := pointer.symm.trans pointer1
      cases ptrEq
      exact Or.inr ⟨ref, off, array, pointer,
        stored_byte_view_free_local initial.good.fresh original get, room, values⟩
  exact ⟨rc, freeWin bodyHeap (syncBuf h), stream0, state, made, madeBound, run,
    finalOrigin, finalAllocator, debt, next, haveCount, put, leftCount, copied0, freed, outcome⟩

#print axioms short_public_adler
/-- The original actual DataStep observation identifies the precise
copied Adler suffix. Null-output refusal contributes no output or credit. -/
theorem short_dataStep_adler
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {flush rc : Int32} {input output credited : List UInt8} {used : Nat}
    (initial : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (observed : DataStep .inflate h after r flush rc input output used)
    (mode : s.mode = COPY)
    (short : (copyAmt s.length z.avail_in z.avail_out).toNat < s.length.toNat)
    (credit : AdlerCredit z s credited) :
    ∃ stream0 state, DefaultOriginState after r zs stream0 state ∧ DefAlloc stream0 ∧
      used ≤ input.length ∧ output = input.take used ∧
      state.length.toNat + used = s.length.toNat ∧
      stream0.next_in = inputAdvance z.next_in used ∧ stream0.avail_in.toNat + used = z.avail_in.toNat ∧
      stream0.next_out = inputAdvance z.next_out used ∧ stream0.avail_out.toNat + used = z.avail_out.toNat ∧
      (AdlerCredit stream0 state (credited ++ output) ∨
        (rc = Z_MEM_ERROR ∧ state.mode = MEM ∧ AdlerCredit stream0 state credited)) := by
  obtain ⟨z0, z1, get0, get1, buffers, _header, inputBytes, usedEq, outputBytes, actual⟩ := observed
  have sameZ : z0 = z := Option.some.inj (get0.symm.trans initial.good.live.hz)
  subst z0
  by_cases null : z.next_out = .null
  · have expected := inflate_default_null_output_run initial.toDefaultStateJ flush null
    have sameRun := Except.ok.inj (actual.symm.trans expected)
    cases sameRun
    have get : r.get (tmpFreed h) = some z := by
      simpa only [tmpFreed, ZStreamRef.get_freeWin, ZStreamRef.get_syncAlloc] using initial.good.live.hz
    have streamEq : z1 = z := Option.some.inj (get1.symm.trans get)
    subst z1
    have zero : used = 0 := by rw [usedEq]; omega
    clear usedEq
    subst used
    have length := header_observed_bytes_length outputBytes
    have empty : output = [] := by apply List.length_eq_zero_iff.mp; omega
    have allocated := default_origin_syncAlloc initial
    have final := allocated.free_local (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn])
    exact ⟨z, s, final, allocator, by omega, by simp only [empty, List.take_zero],
      by omega, (inputAdvance_zero _).symm, by omega, (inputAdvance_zero _).symm, by omega, Or.inl (by simpa only [empty, List.append_nil] using credit)⟩
  · have inputValid : z.next_in = .null → z.avail_in = 0 := by
      intro nullIn
      rcases inputBytes with ⟨_, zero, _⟩ | ⟨ref, off, array, pointer, _get, _room, _values⟩
      · exact UInt32.toNat_inj.mp zero
      · rw [nullIn] at pointer
        cases pointer
    obtain ⟨rc0, heap0, stream0, state, made, bound, run, final, finalAllocator,
      debt, nextIn, availIn, nextOut, availOut, copied, _freed, outcome⟩ :=
      short_public_adler (flush := flush) initial allocator buffers null inputValid inputBytes mode short credit
    have sameRun : (rc0, heap0) = (rc, after) := Except.ok.inj (run.symm.trans actual)
    cases sameRun
    have streamEq : stream0 = z1 := Option.some.inj (final.good.live.hz.symm.trans get1)
    subst z1
    have madeEq : made = used := by rw [usedEq]; omega
    subst made
    have outputCount : z.avail_out.toNat - stream0.avail_out.toNat = used := by omega
    rw [outputCount] at outputBytes
    have equal := stored_observed_bytes_unique outputBytes copied
    rw [← equal] at outcome
    exact ⟨stream0, state, final, finalAllocator, bound, equal, debt, nextIn, availIn, nextOut, availOut, outcome⟩

#print axioms short_dataStep_adler
/-- With an empty held word, the actual three-bit block-header pull
loads exactly the first byte. Its value comes from the independent byte
reader on the same source packet. -/
theorem first_tag_pull
    {h : Heap} {l : IL} {byte : UInt8} {rest : List UInt8}
    (B : BitInv h l (byte :: rest)) (bits : l.bits = 0) :
    ∃ pulled, runX (NEEDBITS 3) l h = .ok ((.ok (), pulled), h) ∧
      BitInv h pulled rest ∧ pulled.bits = 8 ∧ pulled.hold = byte.toUInt64 ∧
      pulled.next = inputAdvance l.next 1 ∧ pulled.have_.toNat + 1 = l.have_.toNat ∧
      pulled = { l with next := pulled.next, have_ := pulled.have_, hold := pulled.hold, bits := pulled.bits } := by
  obtain ⟨outcome, pulled, used, pull, bound, inv, source, bitCount, shape,
    bitBound, identity, full, exhausted, kinds, cursor⟩ := NEEDBITS_run_cursor B 3 (by decide)
  have oldBits : l.bits.toNat = 0 := by rw [bits]; rfl
  have normal : outcome = .ok () := by
    rcases kinds with normal | waiting
    · exact normal
    · obtain ⟨all, empty, short⟩ := exhausted waiting
      change pulled.bits.toNat < 3 at short
      rw [oldBits, all, List.length_cons] at bitCount
      omega
  have enough := full normal
  change 3 ≤ pulled.bits.toNat at enough
  change pulled.bits.toNat ≤ max l.bits.toNat 10 at bitBound
  have usedOne : used = 1 := by omega
  have bits8 : pulled.bits = 8 := UInt32.toNat_inj.mp (by change pulled.bits.toNat = 8; omega)
  rw [usedOne] at inv cursor source
  simp only [List.drop_succ_cons, List.drop_zero] at inv source
  have read := readBits_held_stream pulled rest 8 (by rw [bits8]; decide)
  have stream0 : stream l (byte :: rest) = natBits 8 byte.toNat ++ bytesBits rest := by
    rw [stream, bits]
    simp only [UInt32.toNat_zero, natBits, List.range_zero, List.map_nil, List.nil_append, bytesBits_cons]
  rw [source, stream0] at read
  have expected := wrapper_readBits_byte byte (bytesBits rest)
  have same := congrArg Prod.fst (Option.some.inj (read.symm.trans expected))
  have holdBound := inv.hold_lt
  rw [bits8] at holdBound
  change pulled.hold.toNat < 256 at holdBound
  have word : pulled.hold = byte.toUInt64 := by
    apply UInt64.toNat_inj.mp
    change pulled.hold.toNat = byte.toNat
    change pulled.hold.toNat % 256 = byte.toNat at same
    rwa [Nat.mod_eq_of_lt holdBound] at same
  have count : pulled.have_.toNat + 1 = l.have_.toNat := by
    rw [inv.have_eq, B.have_eq, List.length_cons]
  exact ⟨pulled, by rwa [normal] at pull, inv, bits8, word, cursor, count, shape⟩

#print axioms first_tag_pull
end Zlib.Inflate.Proofs.StoredHistory

namespace Zlib.Inflate.Proofs.StoredHistory
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WrapperGlue Zlib.Inflate.Proofs.StoredEnd
set_option autoImplicit false
/-- Independent final/type-zero reads determine the actual TYPE branch.
Ignored upper padding bits of the first byte remain arbitrary. -/
theorem type_final_stored_prefix
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {byte : UInt8} {rest credited : List UInt8} {firstRest bodyBits : List Bool}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (packet : DispatchBuffers h r l (byte :: rest)) (mode : s.mode = TYPE) (last : s.last = 0)
    (bits : l.bits = 0) (flush : c.flush ≠ Z_BLOCK ∧ c.flush ≠ Z_TREES)
    (credit : AdlerCredit z s credited)
    (finalRead : readBits 1 (stream l (byte :: rest)) = some (1, firstRest))
    (typeRead : readBits 2 firstRest = some (0, bodyBits)) :
    ∃ regs after state,
      runX (inflate_dispatch c) l h = .ok ((.ok (), regs), after) ∧
      DefaultOriginState after r zs z state ∧ state.mode = STORED ∧ state.last = 1 ∧
      DispatchBuffers after r regs rest ∧ AdlerCredit z state credited ∧
      regs.bits = 5 ∧ regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧
      stream regs rest = bodyBits := by
  obtain ⟨pulled, pull, inv, bits8, word, cursor, count, shape⟩ := first_tag_pull packet.bits bits
  have preserved : stream pulled rest = stream l (byte :: rest) := by
    rw [stream, bits8, word, stream, bits, bytesBits_cons]
    change natBits 8 byte.toNat ++ bytesBits rest = [] ++ (natBits 8 byte.toNat ++ bytesBits rest)
    rfl
  have joined := wrapper_readBits_join finalRead typeRead
  have actualRead := readBits_held_stream pulled rest 3 (by rw [bits8]; decide)
  rw [preserved] at actualRead
  have joined0 : readBits 3 (stream l (byte :: rest)) = some (1, bodyBits) := by
    simpa only [Nat.add_zero, Nat.mul_zero] using joined
  have same := Option.some.inj (actualRead.symm.trans joined0)
  have low : pulled.hold.toNat % 8 = 1 := congrArg Prod.fst same
  have remaining : (stream l (byte :: rest)).drop 3 = bodyBits := congrArg Prod.snd same
  have bitOne : pulled.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1) = 1 := by
    apply UInt32.toNat_inj.mp
    rw [BITS_toNat pulled 1 (by decide)]
    change pulled.hold.toNat % 2 = 1
    omega
  let middle := { s with last := 1 }
  let first := { pulled with hold := pulled.hold >>> 1, bits := pulled.bits - 1 }
  let regs := { first with hold := first.hold >>> 2, bits := first.bits - 2 }
  let state := { middle with mode := STORED }
  let after := setI h zs state
  have env1 : Env c (setI h zs middle) r zs z middle :=
    ⟨E.strm, E.st, by rw [ZStreamRef.get_setI]; exact E.hz, by simp only [setI_istates_same]⟩
  have kind : first.hold.toNat % 4 = 0 := by
    have shifted := shr64_toNat pulled.hold 1 (by decide)
    change (pulled.hold >>> 1).toNat = pulled.hold.toNat / 2 at shifted
    change (pulled.hold >>> 1).toNat % 4 = 0
    rw [shifted]
    omega
  have actual : runX (inflate_dispatch c) l h = .ok ((.ok (), regs), after) := by
    rw [inflate_dispatch_block_type E l (Or.inl mode), ite_eq_left mode,
      inflate_TYPE_go c l h flush, inflate_TYPEDO_head E l pulled last pull, bitOne]
    change runX (typedoTail c) first (setI h zs middle) = _
    rw [typedoTail_stored env1 first kind]
    simp only [after, state, regs, setI_setI]
  have getZ : r.get after = some z := by rw [ZStreamRef.get_setI]; exact E.hz
  have getS : after.istates zs = some state := by simp only [after, setI_istates_same]
  obtain ⟨current, packet0⟩ := origin_packet_of_actual E initial packet
    (by rw [bits]; decide) actual getZ getS
  have haveRegs : regs.have_ = pulled.have_ := rfl
  have used : l.have_.toNat - regs.have_.toNat = 1 := by rw [haveRegs]; omega
  rw [used] at packet0
  simp only [List.drop_succ_cons, List.drop_zero] at packet0
  obtain ⟨inv1, stream1, count1⟩ := DROPBITS_inv inv 1 (by rw [bits8]; decide) (by decide)
  obtain ⟨inv2, stream2, count2⟩ := DROPBITS_inv inv1 2
    (by change 2 ≤ (pulled.bits - 1).toNat; rw [bits8]; decide) (by decide)
  change stream first rest = (stream pulled rest).drop 1 at stream1
  change stream regs rest = (stream first rest).drop 2 at stream2
  have source : stream regs rest = bodyBits := by
    rw [stream2, stream1, preserved, List.drop_drop]
    exact remaining
  refine ⟨regs, after, state, actual, current, rfl, rfl, packet0,
    ⟨credit.1, credit.2.1, credit.2.2⟩, ?_, ?_, ?_, ?_, source⟩
  · change pulled.bits - 1 - 2 = 5
    rw [bits8]
    rfl
  all_goals dsimp only [regs, first]; rw [shape]

#print axioms type_final_stored_prefix
end Zlib.Inflate.Proofs.StoredHistory

namespace Zlib.Inflate.Proofs.StoredHistory
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WrapperGlue Zlib.Inflate.Proofs.StoredEnd
set_option autoImplicit false
/-- Successful independent reads expose their exact input extent. -/
theorem readBits_extent {n value : Nat} {input rest : List Bool}
    (read : readBits n input = some (value, rest)) : input.length = n + rest.length := by
  induction n generalizing input value rest with
  | zero => simp only [readBits, Option.some.injEq, Prod.mk.injEq] at read; rw [read.2, Nat.zero_add]
  | succ n ih =>
    cases input with
    | nil => simp only [readBits, reduceCtorEq] at read
    | cons bit input =>
      cases tail : readBits n input with
      | none => simp only [readBits, tail, reduceCtorEq] at read
      | some pair =>
        rcases pair with ⟨v, next⟩
        simp only [readBits, tail, Option.some.injEq, Prod.mk.injEq] at read
        have extent := ih tail
        rw [read.2] at extent
        simp only [List.length_cons]
        omega

/-- A successful independent stored-byte read has precisely its stated
payload length. -/
theorem readBytes_extent {n : Nat} {input rest : List Bool} {bytes : List UInt8}
    (read : readBytes n input = some (bytes, rest)) : bytes.length = n := by
  induction n generalizing input bytes rest with
  | zero => simp only [readBytes, Option.some.injEq, Prod.mk.injEq] at read; rw [← read.1]; rfl
  | succ n ih =>
    cases first : readBits 8 input with
    | none => simp only [readBytes, first, reduceCtorEq] at read
    | some pair =>
      rcases pair with ⟨value, next⟩
      cases tail : readBytes n next with
      | none => simp only [readBytes, first, tail, reduceCtorEq] at read
      | some pair =>
        rcases pair with ⟨more, after⟩
        simp only [readBytes, first, tail, Option.some.injEq, Prod.mk.injEq] at read
        rw [← read.1, List.length_cons, ih tail]

#print axioms readBits_extent
#print axioms readBytes_extent
end Zlib.Inflate.Proofs.StoredHistory

namespace Zlib.Inflate.Proofs.StoredHistory
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WrapperGlue Zlib.Inflate.Proofs.StoredEnd
set_option autoImplicit false
/-- Inversion of the independent stored grammar provides all source
reads without assuming a result of the translated decoder. -/
theorem stored_body_reads {dictionary before output : List UInt8} {input rest : List Bool}
    (format : Body dictionary 0 before input rest output) :
    ∃ len nlen firstRest dataBits bytes,
      readBits 16 (input.drop (input.length % 8)) = some (len, firstRest) ∧
      readBits 16 firstRest = some (nlen, dataBits) ∧ nlen = 65535 - len ∧
      readBytes len dataBits = some (bytes, rest) ∧ output = before ++ bytes := by
  cases format with
  | stored first second valid bytes => exact ⟨_, _, _, _, _, first, second, valid, bytes, rfl⟩

/-- A valid independent stored body with nonempty payload and exhausted
output really reads LEN/NLEN, enters COPY, and leaves without copying.
The returned phase is produced by source execution, including alignment. -/
theorem stored_valid_zero_output_copy_entry
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs credited dictionary before payload : List UInt8} {restBits : List Bool}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (packet : DispatchBuffers h r l bs) (mode : s.mode = STORED) (bits : l.bits.toNat ≤ 39)
    (credit : AdlerCredit z s credited) (flush : c.flush ≠ Z_TREES) (noOutput : l.left = 0)
    (format : Body dictionary 0 before (stream l bs) restBits (before ++ payload))
    (nonempty : payload ≠ []) :
    ∃ regs after state used,
      runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, regs), after) ∧
      DefaultOriginState after r zs z state ∧ state.mode = COPY ∧
      state.length.toNat = payload.length ∧ state.last = s.last ∧ state.wsize = s.wsize ∧
      DispatchBuffers after r regs (bs.drop used) ∧ used ≤ bs.length ∧
      AdlerCredit z state credited ∧ regs.bits = 0 ∧ regs.hold = 0 ∧
      regs.put = l.put ∧ regs.left = 0 ∧ regs.out_ = l.out_ ∧
      readBytes payload.length (bytesBits (bs.drop used)) = some (payload, restBits) := by
  obtain ⟨len, nlen, firstRest, dataBits, bytes, readLen, readNlen, complement, readPayload, outputEq⟩ :=
    stored_body_reads format
  have payloadEq : payload = bytes := List.append_cancel_left outputEq
  subst bytes
  have payloadLength : payload.length = len := readBytes_extent readPayload
  have totalRead := wrapper_readBits_join readLen readNlen
  have enoughInput := readBits_extent totalRead
  obtain ⟨aligned, alignment, byteAligned⟩ := BYTEBITS_inv packet.bits
  have alignmentLength : (stream (bytebits l) bs).length =
      ((stream l bs).drop ((stream l bs).length % 8)).length := by
    have same : l.bits.toNat % 8 = (stream l bs).length % 8 := by
      rw [tcStream_length packet.bits]
      omega
    rw [alignment, same]
  obtain ⟨outcome0, current0, used0, directPull, usedBound0, inv0, source0, count0, shape0,
    bitBound0, identity0, full0, waiting0, kinds0, cursor0⟩ := NEEDBITS_run_cursor aligned 32 (by decide)
  have normal0 : outcome0 = .ok () := by
    rcases kinds0 with normal | waiting
    · exact normal
    · obtain ⟨all, zero, short⟩ := waiting0 waiting
      change current0.bits.toNat < 32 at short
      have sameLength := congrArg List.length source0
      rw [all, List.drop_length, stream, bytesBits_nil, List.append_nil, natBits_length] at sameLength
      rw [alignmentLength] at sameLength
      omega
  obtain ⟨outcome, current, used, pull, usedBound, inv, source, wait, ready⟩ :=
    stored_STORED_header_prefix E initial packet mode bits
  have direct : runX (do BYTEBITS; NEEDBITS 32) l h = .ok ((.ok (), current0), h) := by
    rw [runX_bind, BYTEBITS_run]
    rwa [normal0] at directPull
  have same := Except.ok.inj (pull.symm.trans direct)
  cases same
  obtain ⟨word, actualLen, actualNlen, actualRest, first, second, lenBound, nlenBound,
    accepted, enter⟩ := ready rfl
  have equalFirst := Option.some.inj (readLen.symm.trans first)
  have lenEq : len = actualLen := congrArg Prod.fst equalFirst
  have restEq : firstRest = actualRest := congrArg Prod.snd equalFirst
  subst actualLen actualRest
  have equalSecond := Option.some.inj (readNlen.symm.trans second)
  have nlenEq : nlen = actualNlen := congrArg Prod.fst equalSecond
  have bitsEq : dataBits = bytesBits (bs.drop used) := congrArg Prod.snd equalSecond
  subst actualNlen
  obtain ⟨readyJ, readyPacket, actualLength, sourceRun⟩ := enter complement
  let readyState := { s with length := current0.hold.toUInt32 &&& 0xffff, mode := COPY_ }
  let readyHeap := setI h zs readyState
  let readyRegs := { current0 with hold := 0, bits := 0 }
  let state := { readyState with mode := COPY }
  let after := setI readyHeap zs state
  let regs := { readyRegs with copy := 0 }
  have readyEnv : Env c readyHeap r zs z readyState :=
    ⟨E.strm, E.st, readyJ.good.live.hz, readyJ.good.live.hs⟩
  have env1 : Env c after r zs z state :=
    ⟨E.strm, E.st, by rw [ZStreamRef.get_setI]; exact readyEnv.hz, by dsimp only [after]; rw [setI_istates_same]⟩
  have lengthNonzero : state.length ≠ 0 := by
    intro zero
    have amount : state.length.toNat = len := actualLength
    rw [zero] at amount
    have empty : payload.length = 0 := by rw [payloadLength]; exact amount.symm
    exact nonempty (List.length_eq_zero_iff.mp empty)
  have currentLeft : current0.left = l.left := by
    rw [shape0]
    rfl
  have stalled : copyAmt state.length readyRegs.have_ readyRegs.left = 0 := by
    have outBound := (copyAmt_le state.length readyRegs.have_ readyRegs.left).2.2
    have outputZero : readyRegs.left.toNat = 0 := by
      change current0.left.toNat = 0
      rw [currentLeft, noOutput]
      rfl
    apply UInt32.toNat_inj.mp
    change (copyAmt state.length readyRegs.have_ readyRegs.left).toNat = 0
    omega
  have actual : runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, regs), after) := by
    rw [inflate_dispatch_STORED E l mode, sourceRun]
    simp only [flush, beq_iff_eq, ite_false]
    rw [inflate_COPY__eq readyEnv readyRegs]
    exact inflate_COPY_leave env1 readyRegs lengthNonzero stalled
  have getZ : r.get after = some z := env1.hz
  have getS : after.istates zs = some state := env1.hs
  obtain ⟨final, finalPacket⟩ := origin_packet_of_actual E initial packet bits actual getZ getS
  have consumed : l.have_.toNat - regs.have_.toNat = used := by
    have old := packet.bits.have_eq
    have now := inv.have_eq
    change current0.have_.toNat = (bs.drop used).length at now
    rw [List.length_drop] at now
    change l.have_.toNat - current0.have_.toNat = used
    omega
  rw [consumed] at finalPacket
  refine ⟨regs, after, state, used, actual, final, rfl, ?_, rfl, rfl,
    finalPacket, usedBound, adlerCredit_decode credit (by rfl), rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact actualLength.trans payloadLength.symm
  · change current0.put = l.put
    rw [shape0]
    rfl
  · change current0.left = 0
    exact currentLeft.trans noOutput
  · change current0.out_ = l.out_
    rw [shape0]
    rfl
  · rw [payloadLength, ← bitsEq]
    exact readPayload

#print axioms stored_body_reads
#print axioms stored_valid_zero_output_copy_entry
end Zlib.Inflate.Proofs.StoredHistory

namespace Zlib.Inflate.Proofs.StoredHistory
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WrapperGlue Zlib.Inflate.Proofs.StoredEnd
set_option autoImplicit false
/-- A complete valid independent stored body produces the real aligned
LEN/NLEN source cut and COPY_ packet. Empty payload is included. -/
theorem stored_valid_header_ready
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs credited dictionary before payload : List UInt8} {restBits : List Bool}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (packet : DispatchBuffers h r l bs) (mode : s.mode = STORED) (bits : l.bits.toNat ≤ 39)
    (credit : AdlerCredit z s credited)
    (format : Body dictionary 0 before (stream l bs) restBits (before ++ payload)) :
    ∃ (current : IL) (used : Nat), used ≤ bs.length ∧
      let state := { s with length := current.hold.toUInt32 &&& 0xffff, mode := COPY_ }
      let after := setI h zs state
      let regs := { current with hold := 0, bits := 0 }
      DefaultOriginState after r zs z state ∧ DispatchBuffers after r regs (bs.drop used) ∧
      state.length.toNat = payload.length ∧ AdlerCredit z state credited ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧
      runX (inflate_STORED c) l h =
        runX (if c.flush == Z_TREES then (throw Ex.leave : X Unit) else inflate_COPY_ c) regs after ∧
      readBytes payload.length (bytesBits (bs.drop used)) = some (payload, restBits) := by
  obtain ⟨len, nlen, firstRest, dataBits, bytes, readLen, readNlen, complement, readPayload, outputEq⟩ :=
    stored_body_reads format
  have payloadEq : payload = bytes := List.append_cancel_left outputEq
  subst bytes
  have payloadLength : payload.length = len := readBytes_extent readPayload
  have totalRead := wrapper_readBits_join readLen readNlen
  have enoughInput := readBits_extent totalRead
  obtain ⟨aligned, alignment, byteAligned⟩ := BYTEBITS_inv packet.bits
  have alignmentLength : (stream (bytebits l) bs).length =
      ((stream l bs).drop ((stream l bs).length % 8)).length := by
    have same : l.bits.toNat % 8 = (stream l bs).length % 8 := by
      rw [tcStream_length packet.bits]
      omega
    rw [alignment, same]
  obtain ⟨outcome0, current0, used0, directPull, usedBound0, inv0, source0, count0, shape0,
    bitBound0, identity0, full0, waiting0, kinds0, cursor0⟩ := NEEDBITS_run_cursor aligned 32 (by decide)
  have normal0 : outcome0 = .ok () := by
    rcases kinds0 with normal | waiting
    · exact normal
    · obtain ⟨all, zero, short⟩ := waiting0 waiting
      change current0.bits.toNat < 32 at short
      have sameLength := congrArg List.length source0
      rw [all, List.drop_length, stream, bytesBits_nil, List.append_nil, natBits_length] at sameLength
      rw [alignmentLength] at sameLength
      omega
  obtain ⟨outcome, current, used, pull, usedBound, inv, source, wait, ready⟩ :=
    stored_STORED_header_prefix E initial packet mode bits
  have direct : runX (do BYTEBITS; NEEDBITS 32) l h = .ok ((.ok (), current0), h) := by
    rw [runX_bind, BYTEBITS_run]
    rwa [normal0] at directPull
  have same := Except.ok.inj (pull.symm.trans direct)
  cases same
  obtain ⟨word, actualLen, actualNlen, actualRest, first, second, lenBound, nlenBound,
    accepted, enter⟩ := ready rfl
  have equalFirst := Option.some.inj (readLen.symm.trans first)
  have lenEq : len = actualLen := congrArg Prod.fst equalFirst
  have restEq : firstRest = actualRest := congrArg Prod.snd equalFirst
  subst actualLen actualRest
  have equalSecond := Option.some.inj (readNlen.symm.trans second)
  have nlenEq : nlen = actualNlen := congrArg Prod.fst equalSecond
  have bitsEq : dataBits = bytesBits (bs.drop used) := congrArg Prod.snd equalSecond
  subst actualNlen
  obtain ⟨readyJ, readyPacket, actualLength, sourceRun⟩ := enter complement
  refine ⟨current0, used, usedBound, readyJ, readyPacket,
    actualLength.trans payloadLength.symm, adlerCredit_decode credit (by rfl), ?_, ?_, ?_, sourceRun, ?_⟩
  · change current0.put = l.put
    rw [shape0]
    rfl
  · change current0.left = l.left
    rw [shape0]
    rfl
  · change current0.out_ = l.out_
    rw [shape0]
    rfl
  · rw [payloadLength, ← bitsEq]
    exact readPayload

#print axioms stored_valid_header_ready
end Zlib.Inflate.Proofs.StoredHistory

namespace Zlib.Inflate.Proofs.StoredHistory
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WrapperGlue Zlib.Inflate.Proofs.StoredEnd
set_option autoImplicit false
/-- A valid empty stored body falls through COPY_ and zero COPY to TYPE,
retaining the independent trailer source and writing no caller byte. -/
theorem stored_valid_empty_to_type
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs credited dictionary before : List UInt8} {restBits : List Bool}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (packet : DispatchBuffers h r l bs) (mode : s.mode = STORED) (bits : l.bits.toNat ≤ 39)
    (credit : AdlerCredit z s credited) (flush : c.flush ≠ Z_TREES)
    (format : Body dictionary 0 before (stream l bs) restBits (before ++ [])) :
    ∃ regs after state used,
      runX (inflate_dispatch c) l h = .ok ((.ok (), regs), after) ∧
      DefaultOriginState after r zs z state ∧ state.mode = TYPE ∧ state.length = 0 ∧
      state.last = s.last ∧ state.wsize = s.wsize ∧
      DispatchBuffers after r regs (bs.drop used) ∧ used ≤ bs.length ∧ AdlerCredit z state credited ∧
      regs.bits = 0 ∧ regs.hold = 0 ∧ regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧
      stream regs (bs.drop used) = restBits ∧
      (∀ ref : BRef, Space.get after ref = Space.get h ref) := by
  obtain ⟨current, used, usedBound, readyJ, readyPacket, length, readyCredit,
    put, left, outBase, sourceRun, reader⟩ := stored_valid_header_ready E initial packet mode bits credit format
  let readyState := { s with length := current.hold.toUInt32 &&& 0xffff, mode := COPY_ }
  let readyHeap := setI h zs readyState
  let readyRegs := { current with hold := 0, bits := 0 }
  let copyState := { readyState with mode := COPY }
  let copyHeap := setI readyHeap zs copyState
  let state := { copyState with mode := TYPE }
  let after := setI copyHeap zs state
  let regs := { readyRegs with copy := 0 }
  have zero : copyState.length = 0 := UInt32.toNat_inj.mp length
  have readyEnv : Env c readyHeap r zs z readyState :=
    ⟨E.strm, E.st, readyJ.good.live.hz, readyJ.good.live.hs⟩
  have copyEnv : Env c copyHeap r zs z copyState :=
    ⟨E.strm, E.st, by rw [ZStreamRef.get_setI]; exact readyEnv.hz,
      by dsimp only [copyHeap]; rw [setI_istates_same]⟩
  have actual : runX (inflate_dispatch c) l h = .ok ((.ok (), regs), after) := by
    rw [inflate_dispatch_STORED E l mode, sourceRun]
    simp only [flush, beq_iff_eq, ite_false]
    rw [inflate_COPY__eq readyEnv readyRegs]
    exact inflate_COPY_done copyEnv readyRegs zero
  have getZ : r.get after = some z := by rw [ZStreamRef.get_setI]; exact copyEnv.hz
  have getS : after.istates zs = some state := by dsimp only [after]; rw [setI_istates_same]
  obtain ⟨final, finalPacket⟩ := origin_packet_of_actual E initial packet bits actual getZ getS
  have consumed : l.have_.toNat - regs.have_.toNat = used := by
    have old := packet.bits.have_eq
    have now := readyPacket.bits.have_eq
    change current.have_.toNat = (bs.drop used).length at now
    rw [List.length_drop] at now
    change l.have_.toNat - current.have_.toNat = used
    omega
  rw [consumed] at finalPacket
  have remainder : stream regs (bs.drop used) = restBits := by
    change bytesBits (bs.drop used) = restBits
    exact congrArg Prod.snd (Option.some.inj reader)
  refine ⟨regs, after, state, used, actual, final, rfl, zero, rfl, rfl, finalPacket, usedBound,
    adlerCredit_decode credit (by rfl), rfl, rfl, put, left, outBase, remainder, ?_⟩
  intro ref
  dsimp only [after, copyHeap, readyHeap]
  rw [byte_view_get_setI, byte_view_get_setI, byte_view_get_setI]

#print axioms stored_valid_empty_to_type
end Zlib.Inflate.Proofs.StoredHistory
