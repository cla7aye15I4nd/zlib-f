import ZlibF.Proof.«inflate.c.default-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- An actual accepted default header writes flags zero. Rejected headers
are BAD; neither fact is assumed from the header's desired contract. -/
theorem headDefaultCheck_flags {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} {l regs : IL}
    (E : Env c h r zs z s) (wbits : 8 ≤ s.wbits.toNat ∧ s.wbits.toNat ≤ 15)
    (run : runX (headDefaultCheck c s l) l h = .ok ((.ok (), regs), after))
    (good : Good after r zs stream state) : state.mode = BAD ∨ state.flags = 0 := by
  have rejected (out : IL) (i : Nat)
      (badRun : runX (headDefaultCheck c s l) l h = .ok ((.ok (), out), badHeap h r zs z s i)) :
      state.mode = BAD ∨ state.flags = 0 := by
    have heapEq : after = badHeap h r zs z s i := congrArg Prod.snd (Except.ok.inj (run.symm.trans badRun))
    have get := good.live.hs
    rw [heapEq] at get
    simp only [badHeap, setI_istates_same] at get
    cases Option.some.inj get
    exact Or.inl rfl
  by_cases header : headHeaderRejected s l = true
  · obtain ⟨i, badRun⟩ := headDefaultCheck_bad_header E l header
    exact rejected l i badRun
  have headerFalse : headHeaderRejected s l = false := by cases eq : headHeaderRejected s l <;> simp_all
  by_cases method : headMethodRejected l = true
  · obtain ⟨i, badRun⟩ := headDefaultCheck_bad_method E l headerFalse method
    exact rejected l i badRun
  have methodFalse : headMethodRejected l = false := by cases eq : headMethodRejected l <;> simp_all
  have nonzero : s.wbits ≠ 0 := by
    intro zero
    have low := wbits.1
    rw [zero] at low
    simp at low
  by_cases window : s.wbits.toNat < (headWindowRegs l).len.toNat
  · obtain ⟨i, badRun⟩ := headDefaultCheck_bad_window E l headerFalse methodFalse nonzero window
    exact rejected (headWindowRegs l) i badRun
  · have accepted := headDefaultCheck_accept E l headerFalse methodFalse (by omega) wbits
    have heapEq : after = setI (r.put h { z with adler := 1 }) zs (headDefaultState s l) :=
      congrArg Prod.snd (Except.ok.inj (run.symm.trans accepted))
    have get := good.live.hs
    rw [heapEq, setI_istates_same] at get
    cases Option.some.inj get
    exact Or.inr rfl

/-- The actual default header suffix establishes the full default state
relation, including its completed-header flag. -/
theorem headDefaultCheck_default_state {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (full : 16 ≤ l.bits.toNat) :
    ∃ regs after stream state,
      runX (headDefaultCheck c s l) l h = .ok ((.ok (), regs), after) ∧
      DefaultStateJ after r zs stream state := by
  obtain ⟨regs, after, stream, state, run, current, tables, pending, _, sizes, _, _, modes,
    _, _, static, frame, _⟩ :=
    headDefaultCheck_boundary_frame E invariant.good invariant.pending buffers full invariant.window
  have flags := headDefaultCheck_flags E invariant.window run current
  have guards : state.mode ≠ CODELENS ∧ state.mode ≠ LENLENS ∧ state.mode ≠ CHECK ∧ state.mode ≠ LENGTH ∧
      DICTID ≤ state.mode ∧ state.mode ≤ SYNC := by
    rcases modes with selected | selected | selected <;> rw [selected] <;> decide
  have base : DefaultDecodeJ after r zs stream state := by
    refine ⟨current, tables, pending, ?_, ?_, ?_, ?_, ?_, ?_, Or.inr guards.2.2.2.2, ?_, ?_, sizes.platform invariant.platform⟩
    · intro active
      exact False.elim (guards.1 active)
    · intro active
      exact False.elim (guards.2.1 active)
    · rw [frame]
      exact invariant.held
    · rw [frame]
      exact invariant.window
    · rw [frame]
      exact invariant.wrapper
    · rw [frame]
      exact invariant.header
    · rintro (active | active)
      · exact False.elim (guards.2.2.1 active)
      · exact False.elim (guards.2.2.2.1 active)
    · change after.static = _
      rw [static]
      exact invariant.globals
  refine ⟨regs, after, stream, state, run, ⟨base, ?_, ?_, ?_⟩⟩
  · rw [frame]
    exact invariant.requestedBits
  · rw [frame]
    exact invariant.requestedWrap
  · rcases flags with bad | flags
    · exact Or.inr (Or.inl bad)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr flags))))

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
    inflate_HEAD_zlib_window_prefix_count E buffers.bits wrap invariant.header
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
    inflate_HEAD_zlib_window_rank E invariant.good invariant.pending buffers mode wrap invariant.header invariant.window incoming
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
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = HEAD) (incoming : l.bits.toNat ≤ 39) :
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
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl raw))))⟩
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
  · exact inflate_dispatch_HEAD_zlib_state_rank E invariant buffers mode wrapped incoming

end Zlib.Inflate.Proofs
