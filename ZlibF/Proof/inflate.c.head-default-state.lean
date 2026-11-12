import ZlibF.Proof.«inflate.c.default-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The width before a header, from the default relation. -/
theorem DefaultDecodeJ.headWindow {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (current : DefaultDecodeJ h r zs z s) : HeadWindow s :=
  current.window.imp id (fun ⟨zero, null, _, _⟩ => ⟨zero, null⟩)

/-- An actual header is rejected into BAD with the flags kept, or accepted
with flags zero and a window width. -/
theorem headDefaultCheck_flags {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} {l regs : IL}
    (E : Env c h r zs z s) (wbits : HeadWindow s)
    (run : runX (headDefaultCheck c s l) l h = .ok ((.ok (), regs), after))
    (good : Good after r zs stream state) :
    (state.mode = BAD ∧ state.flags = s.flags) ∨
      (state.flags = 0 ∧ 8 ≤ state.wbits.toNat ∧ state.wbits.toNat ≤ 15) := by
  have rejected (out : IL) (i : Nat)
      (badRun : runX (headDefaultCheck c s l) l h = .ok ((.ok (), out), badHeap h r zs z s i)) :
      (state.mode = BAD ∧ state.flags = s.flags) ∨
        (state.flags = 0 ∧ 8 ≤ state.wbits.toNat ∧ state.wbits.toNat ≤ 15) := by
    have heapEq : after = badHeap h r zs z s i := congrArg Prod.snd (Except.ok.inj (run.symm.trans badRun))
    have get := good.live.hs
    rw [heapEq] at get
    simp only [badHeap, setI_istates_same] at get
    cases Option.some.inj get
    exact Or.inl ⟨rfl, rfl⟩
  have acceptedResult (width : (headWidth s l).toNat ≤ 15 ∧ 8 ≤ (headWidth s l).toNat)
      (acceptRun : runX (headDefaultCheck c s l) l h = .ok ((.ok (), { headWindowRegs l with hold := 0, bits := 0 }),
        setI (r.put h { z with adler := 1 }) zs (headDefaultState s l))) :
      (state.mode = BAD ∧ state.flags = s.flags) ∨
        (state.flags = 0 ∧ 8 ≤ state.wbits.toNat ∧ state.wbits.toNat ≤ 15) := by
    have heapEq : after = setI (r.put h { z with adler := 1 }) zs (headDefaultState s l) :=
      congrArg Prod.snd (Except.ok.inj (run.symm.trans acceptRun))
    have get := good.live.hs
    rw [heapEq, setI_istates_same] at get
    cases Option.some.inj get
    exact Or.inr ⟨rfl, width.2, width.1⟩
  by_cases header : headHeaderRejected s l = true
  · obtain ⟨i, badRun⟩ := headDefaultCheck_bad_header E l header
    exact rejected l i badRun
  have headerFalse : headHeaderRejected s l = false := by cases eq : headHeaderRejected s l <;> simp_all
  by_cases method : headMethodRejected l = true
  · obtain ⟨i, badRun⟩ := headDefaultCheck_bad_method E l headerFalse method
    exact rejected l i badRun
  have methodFalse : headMethodRejected l = false := by cases eq : headMethodRejected l <;> simp_all
  have lenBounds := headWindowRegs_len_bounds l
  by_cases zero : s.wbits = 0
  · by_cases big : 15 < (headWindowRegs l).len.toNat
    · obtain ⟨i, badRun⟩ := headDefaultCheck_bad_window_zero E l headerFalse methodFalse big
      exact rejected (headWindowRegs l) i badRun
    · have widthEq : headWidth s l = (headWindowRegs l).len := by simp only [headWidth, zero, ↓reduceIte]
      exact acceptedResult (by rw [widthEq]; omega)
        (headDefaultCheck_accept_zero E l headerFalse methodFalse zero (by omega))
  have range := wbits.resolve_right (fun e => zero e.1)
  have nonzero : s.wbits ≠ 0 := zero
  by_cases window : s.wbits.toNat < (headWindowRegs l).len.toNat
  · obtain ⟨i, badRun⟩ := headDefaultCheck_bad_window E l headerFalse methodFalse nonzero window
    exact rejected (headWindowRegs l) i badRun
  · have widthEq : headWidth s l = s.wbits := by simp only [headWidth, zero, ↓reduceIte]
    exact acceptedResult (by rw [widthEq]; omega)
      (headDefaultCheck_accept E l headerFalse methodFalse (by omega) range)

/-- The actual default header suffix establishes the full default state
relation, including its completed-header flag. -/
theorem RequestedBitsOK.with_width {reqbits wbits wbits' : UInt32} {reqwrap : Int32}
    (ok : RequestedBitsOK reqbits wbits reqwrap) (width : wbits' = wbits ∨ wbits = 0) :
    RequestedBitsOK reqbits wbits' reqwrap := by
  refine ⟨?_, ok.2⟩
  rcases width with same | zero
  · rw [same]
    exact ok.1
  · right
    rcases ok.1 with equal | none
    · rw [equal, zero]
    · exact none

theorem headDefaultCheck_default_state {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (full : 16 ≤ l.bits.toNat) :
    ∃ regs after stream state,
      runX (headDefaultCheck c s l) l h = .ok ((.ok (), regs), after) ∧
      DefaultStateJ after r zs stream state := by
  have headWindow := invariant.toDefaultDecodeJ.headWindow
  obtain ⟨regs, after, stream, state, run, current, tables, pending, _, sizes, _, _, modes,
    windowEq, width, static, frame, _⟩ :=
    headDefaultCheck_boundary_frame E invariant.good invariant.pending buffers full headWindow
  have flags := headDefaultCheck_flags E headWindow run current
  have guards : state.mode ≠ CODELENS ∧ state.mode ≠ LENLENS ∧ state.mode ≠ CHECK ∧ state.mode ≠ LENGTH ∧
      DICTID ≤ state.mode ∧ state.mode ≤ SYNC := by
    rcases modes with selected | selected | selected <;> rw [selected] <;> decide
  have wrapEq : state.wrap = s.wrap := by rw [frame]
  have reqbitsEq : state.reqbits = s.reqbits := by rw [frame]
  have reqwrapEq : state.reqwrap = s.reqwrap := by rw [frame]
  have windowField : (8 ≤ state.wbits.toNat ∧ state.wbits.toNat ≤ 15) ∨
      (state.wbits = 0 ∧ state.window = .null ∧ state.flags = -1 ∧ state.wrap ≠ 0) := by
    rcases flags with ⟨_, sameFlags⟩ | ⟨_, low, high⟩
    · rcases width with same | ⟨_, low, high⟩
      · rcases invariant.window with range | ⟨zero, null, unread, nonraw⟩
        · exact Or.inl (by rw [same]; exact range)
        · exact Or.inr ⟨by rw [same]; exact zero, by rw [windowEq]; exact null,
            by rw [sameFlags]; exact unread, by rw [wrapEq]; exact nonraw⟩
      · exact Or.inl ⟨low, high⟩
    · exact Or.inl ⟨low, high⟩
  have base : DefaultDecodeJ after r zs stream state := by
    refine ⟨current, tables, pending, ?_, ?_, ?_, windowField, ?_, ?_, Or.inr (Or.inl guards.2.2.2.2), ?_, ?_, sizes.platform invariant.platform⟩
    · intro active
      exact False.elim (guards.1 active)
    · intro active
      exact False.elim (guards.2.1 active)
    · rw [frame]
      exact invariant.held
    · rw [frame]
      exact invariant.wrapper
    · intro cause
      have headEq : state.head = s.head := by rw [frame]
      rw [wrapEq]
      rcases cause with attached | ⟨read, notZero⟩
      · exact invariant.header (Or.inl (by rwa [headEq] at attached))
      · rcases flags with ⟨_, sameFlags⟩ | ⟨zero, _⟩
        · exact invariant.header (Or.inr ⟨by rwa [sameFlags] at read, by rwa [sameFlags] at notZero⟩)
        · exact absurd zero notZero
    · rintro (active | active)
      · exact False.elim (guards.2.2.1 active)
      · exact False.elim (guards.2.2.2.1 active)
    · change after.static = _
      rw [static]
      exact invariant.globals
  refine ⟨regs, after, stream, state, run, ⟨base, ?_, ?_, ?_⟩⟩
  · rw [reqbitsEq, reqwrapEq]
    exact invariant.requestedBits.with_width (width.imp id (fun zero => zero.1))
  · rw [frame]
    exact invariant.requestedWrap
  · rcases flags with ⟨bad, _⟩ | ⟨flags, _⟩
    · exact Or.inr (Or.inl bad)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl flags))))))

/-- Actual zlib HEAD retains the full default state relation on both
partial input and the complete header suffix. -/
theorem inflate_HEAD_zlib_default_state {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (wrap : s.wrap = 1 ∨ s.wrap = 5) :
    ∃ outcome regs after stream state,
      runX (inflate_HEAD c) l h = .ok ((outcome, regs), after) ∧
      DefaultStateJ after r zs stream state := by
  obtain ⟨outcome, current, used, bound, bits, cursor, shape, _, kinds, full, cut, _⟩ :=
    inflate_HEAD_zlib_window_prefix_count E buffers.bits wrap (invariant.head_none wrap)
  have symbolShape : SymbolRegShape l current := by rw [shape]; rfl
  have packet := buffers.consume invariant.good invariant.good rfl (fun _ => rfl) (fun _ => rfl)
    symbolShape cursor bound bits
  rcases kinds with normal | wait
  · rw [normal] at cut
    obtain ⟨regs, after, stream, state, run, final⟩ :=
      headDefaultCheck_default_state E invariant packet (full normal)
    exact ⟨.ok (), regs, after, stream, state, cut.trans run, final⟩
  · rw [wait] at cut
    exact ⟨.error Ex.leave, current, h, z, s, cut, invariant⟩

/-- All zlib validation settings reached by default initialization retain
J, caller buffers and the strict common dispatch rank through actual HEAD. -/
theorem inflate_dispatch_HEAD_zlib_state_rank {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = HEAD)
    (wrap : s.wrap = 1 ∨ s.wrap = 5) (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state used, used ≤ bs.length ∧
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      DefaultStateJ after r zs stream state ∧ DispatchBuffers after r regs (bs.drop used) ∧
      ByteViewSizes h after ∧ regs.next = inputAdvance l.next used ∧
      regs.have_.toNat + used = l.have_.toNat ∧ regs.put = l.put ∧ regs.left = l.left ∧
      regs.bits.toNat ≤ 39 ∧ after.static = h.static ∧ HeaderStateFrame s state ∧ HeaderStreamFrame z stream ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) := by
  obtain ⟨outcome, regs, after, stream, state, run, final⟩ :=
    inflate_HEAD_zlib_default_state E invariant buffers wrap
  obtain ⟨otherOutcome, otherRegs, otherHeap, otherStream, otherState, used, bound, otherRun,
    good, _, _, packet, sizes, next, count, put, left, bits, static, frame, streamFrame, progress⟩ :=
    inflate_HEAD_zlib_window_rank E invariant.good invariant.pending buffers mode wrap (invariant.head_none wrap)
      invariant.toDefaultDecodeJ.headWindow incoming
  rw [run] at otherRun
  cases otherRun
  have streamEq : otherStream = stream := Option.some.inj (good.live.hz.symm.trans final.good.live.hz)
  have stateEq : otherState = state := Option.some.inj (good.live.hs.symm.trans final.good.live.hs)
  subst otherStream otherState
  exact ⟨outcome, regs, after, stream, state, used, bound, (inflate_dispatch_HEAD E l mode).trans run,
    final, packet, sizes, next, count, put, left, bits, static, frame, streamFrame, progress⟩

/-- The source raw-recovery HEAD branch changes only the mode. -/
theorem inflate_HEAD_raw_run {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL) (wrap : s.wrap = 0) :
    runX (inflate_HEAD c) l h = .ok ((.ok (), l), setI h zs { s with mode := TYPEDO }) := by
  unfold inflate_HEAD
  rw [runX_bind, runX_rdS E]
  simp only [wrap, beq_self_eq_true, ↓reduceIte]
  rw [runX_bind, runX_setMode E]
  simp only [wrap]
  rfl

/-- Every HEAD state admitted by the default relation, including raw
recovery, retains the full relation and decreases the same dispatch rank. -/
theorem inflate_dispatch_HEAD_state_rank {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = HEAD) (notGzip : ¬ GzipAllowed s.wrap)
    (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state used, used ≤ bs.length ∧
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      DefaultStateJ after r zs stream state ∧ DispatchBuffers after r regs (bs.drop used) ∧
      ByteViewSizes h after ∧ regs.next = inputAdvance l.next used ∧
      regs.have_.toNat + used = l.have_.toNat ∧ regs.put = l.put ∧ regs.left = l.left ∧
      regs.bits.toNat ≤ 39 ∧ after.static = h.static ∧ HeaderStateFrame s state ∧ HeaderStreamFrame z stream ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) := by
  rcases invariant.wrapper with raw | wrapped
  · let state := { s with mode := TYPEDO }
    let after := setI h zs state
    have current : Good after r zs z state := invariant.good.decode_update (by rfl)
      (by change HEAD ≤ TYPEDO ∧ TYPEDO ≤ SYNC; decide)
    have tables : DataTableInvariant after state :=
      dataTableInvariant_inactive (by change ¬ DataTableMode TYPEDO; unfold DataTableMode; decide)
    have pending : DataPendingInvariant state := by
      apply dataPendingInvariant_idle (s := state) invariant.pending.sane
      change TYPEDO ≠ LENEXT ∧ TYPEDO ≠ DIST ∧ TYPEDO ≠ DISTEXT ∧ TYPEDO ≠ MATCH
      decide
    have sizes := byte_view_sizes_setI h zs state
    have base := invariant.toDefaultDecodeJ.block_update current tables pending (by rfl)
      (Or.inr (Or.inl rfl)) (Or.inl raw) sizes rfl
    have final : DefaultStateJ after r zs z state := ⟨base, invariant.requestedBits, invariant.requestedWrap,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl raw)))))⟩
    have packet := buffers.byte_views invariant.good current rfl (fun ref => byte_view_get_setI h zs state ref)
      (fun ref => byte_view_ro_setI h zs state ref)
    have decreases : dispatchRank l state.mode < dispatchRank l s.mode := by
      apply dispatchRank_advance (used := 0) (made := 0) (by rfl) (by rfl) (by omega)
      right
      change dispatchCredit TYPEDO < dispatchCredit s.mode
      rw [mode]
      decide
    exact ⟨.ok (), l, after, z, state, 0, by omega,
      (inflate_dispatch_HEAD E l mode).trans (inflate_HEAD_raw_run E l raw), final,
      by simpa only [List.drop_zero] using packet, sizes,
      (inputAdvance_zero l.next).symm, by omega, rfl, rfl, incoming, rfl, by rfl, by rfl,
      Or.inr ⟨rfl, decreases⟩⟩
  · rcases wrapped with w | w | w | w | w | w
    · exact inflate_dispatch_HEAD_zlib_state_rank E invariant buffers mode (Or.inl w) incoming
    · exact absurd (Or.inl w) notGzip
    · exact absurd (Or.inr (Or.inl w)) notGzip
    · exact inflate_dispatch_HEAD_zlib_state_rank E invariant buffers mode (Or.inr w) incoming
    · exact absurd (Or.inr (Or.inr (Or.inl w))) notGzip
    · exact absurd (Or.inr (Or.inr (Or.inr w))) notGzip

end Zlib.Inflate.Proofs
