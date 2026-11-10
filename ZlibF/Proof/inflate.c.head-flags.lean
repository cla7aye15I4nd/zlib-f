import ZlibF.Proof.«inflate.c.head-default-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual default zlib header parser either retains the incoming flag
on rejection or writes zero after accepting the header. -/
theorem headDefaultCheck_flags_two {c : Ctx} {h after : Heap}
    {r : ZStreamRef} {zs : Nat} {z stream : ZStream}
    {s state : InflateState} {l regs : IL}
    (E : Env c h r zs z s) (wbits : s.wbits = 15)
    (run : runX (headDefaultCheck c s l) l h =
      .ok ((.ok (), regs), after))
    (good : Good after r zs stream state) :
    state.flags = s.flags ∨ state.flags = 0 := by
  have rejected (out : IL) (i : Nat)
      (badRun : runX (headDefaultCheck c s l) l h =
        .ok ((.ok (), out), badHeap h r zs z s i)) :
      state.flags = s.flags ∨ state.flags = 0 := by
    have heapEq : after = badHeap h r zs z s i :=
      congrArg Prod.snd (Except.ok.inj (run.symm.trans badRun))
    have get := good.live.hs
    rw [heapEq] at get
    simp only [badHeap, setI_istates_same] at get
    cases Option.some.inj get
    exact Or.inl rfl
  by_cases header : headHeaderRejected s l = true
  · obtain ⟨i, badRun⟩ := headDefaultCheck_bad_header E l header
    exact rejected l i badRun
  have headerFalse : headHeaderRejected s l = false := by
    cases eq : headHeaderRejected s l <;> simp_all
  by_cases method : headMethodRejected l = true
  · obtain ⟨i, badRun⟩ :=
      headDefaultCheck_bad_method E l headerFalse method
    exact rejected l i badRun
  have methodFalse : headMethodRejected l = false := by
    cases eq : headMethodRejected l <;> simp_all
  by_cases window : 15 < (headWindowRegs l).len.toNat
  · obtain ⟨i, badRun⟩ :=
      headDefaultCheck_bad_window E l headerFalse methodFalse window
    exact rejected (headWindowRegs l) i badRun
  · have accepted := headDefaultCheck_accept E l headerFalse methodFalse
      (by omega) wbits
    have heapEq : after =
        setI (r.put h { z with adler := 1 }) zs (headDefaultState s l) :=
      congrArg Prod.snd (Except.ok.inj (run.symm.trans accepted))
    have get := good.live.hs
    rw [heapEq, setI_istates_same] at get
    cases Option.some.inj get
    exact Or.inr rfl

/-- A default zlib HEAD dispatch keeps the old flag on partial input or
rejection, and writes zero when the header is accepted. -/
theorem inflate_HEAD_zlib_flags_two {c : Ctx} {h after : Heap}
    {r : ZStreamRef} {zs : Nat} {z stream : ZStream}
    {s state : InflateState} {l regs : IL} {outcome : Except Ex Unit}
    {bs : List UInt8}
    (E : Env c h r zs z s)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs)
    (wrap : s.wrap = 1 ∨ s.wrap = 5)
    (run : runX (inflate_HEAD c) l h = .ok ((outcome, regs), after))
    (good : Good after r zs stream state) :
    state.flags = s.flags ∨ state.flags = 0 := by
  obtain ⟨_, current, _, bound, bits, cursor, shape, _, kinds,
    full, cut, _⟩ :=
    inflate_HEAD_zlib_window_prefix_count E buffers.bits wrap invariant.header
  have symbolShape : SymbolRegShape l current := by rw [shape]; rfl
  have packet := buffers.consume invariant.good invariant.good rfl
    (fun _ => rfl) (fun _ => rfl) symbolShape cursor bound bits
  rcases kinds with normal | wait
  · rw [normal] at cut
    obtain ⟨regs0, after0, stream0, state0, run0, final0⟩ :=
      headDefaultCheck_default_state E invariant packet (full normal)
    have actual : runX (inflate_HEAD c) l h =
        .ok ((.ok (), regs0), after0) := cut.trans run0
    rw [actual] at run
    cases run
    have sameState : state = state0 :=
      Option.some.inj (good.live.hs.symm.trans final0.good.live.hs)
    rw [sameState]
    exact headDefaultCheck_flags_two E invariant.window run0 final0.good
  · rw [wait] at cut
    rw [cut] at run
    cases run
    have sameState : state = s :=
      Option.some.inj (good.live.hs.symm.trans invariant.good.live.hs)
    rw [sameState]
    exact Or.inl rfl

/-- The complete HEAD dispatch obeys the same two-value flag transition,
including the raw-recovery branch. -/
theorem inflate_dispatch_HEAD_flags_two {c : Ctx} {h after : Heap}
    {r : ZStreamRef} {zs : Nat} {z stream : ZStream}
    {s state : InflateState} {l regs : IL} {outcome : Except Ex Unit}
    {bs : List UInt8}
    (E : Env c h r zs z s)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = HEAD)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (good : Good after r zs stream state) :
    state.flags = s.flags ∨ state.flags = 0 := by
  have headerRun : runX (inflate_HEAD c) l h =
      .ok ((outcome, regs), after) :=
    (inflate_dispatch_HEAD E l mode).symm.trans run
  rcases invariant.wrapper with raw | wrapped
  · have actual := inflate_HEAD_raw_run E l raw
    rw [actual] at headerRun
    cases headerRun
    have sameState : state = { s with mode := TYPEDO } := by
      have get := good.live.hs
      rw [setI_istates_same] at get
      exact Option.some.inj get.symm
    rw [sameState]
    exact Or.inl rfl
  · exact inflate_HEAD_zlib_flags_two E invariant buffers wrapped headerRun
      good

/-- A HEAD dispatch never enters the synchronization search. -/
theorem inflate_dispatch_HEAD_not_sync {c : Ctx} {h after : Heap}
    {r : ZStreamRef} {zs : Nat} {z stream : ZStream}
    {s state : InflateState} {l regs : IL} {outcome : Except Ex Unit}
    {bs : List UInt8}
    (E : Env c h r zs z s)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = HEAD)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (good : Good after r zs stream state) : state.mode ≠ SYNC := by
  have headerRun : runX (inflate_HEAD c) l h =
      .ok ((outcome, regs), after) :=
    (inflate_dispatch_HEAD E l mode).symm.trans run
  rcases invariant.wrapper with raw | wrapped
  · have actual := inflate_HEAD_raw_run E l raw
    rw [actual] at headerRun
    cases headerRun
    have get := good.live.hs
    rw [setI_istates_same] at get
    have same : state = { s with mode := TYPEDO } :=
      Option.some.inj get.symm
    rw [same]
    change TYPEDO ≠ SYNC
    decide
  · obtain ⟨_, current, _, bound, bits, cursor, shape, _, kinds,
      full, cut, _⟩ :=
      inflate_HEAD_zlib_window_prefix_count E buffers.bits wrapped
        invariant.header
    have symbolShape : SymbolRegShape l current := by rw [shape]; rfl
    have packet := buffers.consume invariant.good invariant.good rfl
      (fun _ => rfl) (fun _ => rfl) symbolShape cursor bound bits
    rcases kinds with normal | wait
    · rw [normal] at cut
      obtain ⟨regs0, after0, stream0, state0, run0, good0, _, _, _,
        _, _, _, modes, _, _, _, _, _⟩ :=
        headDefaultCheck_boundary_frame E invariant.good invariant.pending
          packet (full normal) invariant.window
      have actual : runX (inflate_HEAD c) l h =
          .ok ((.ok (), regs0), after0) := cut.trans run0
      rw [actual] at headerRun
      cases headerRun
      have same : state = state0 :=
        Option.some.inj (good.live.hs.symm.trans good0.live.hs)
      rw [same]
      rcases modes with bad | type | dict
      · rw [bad]; decide
      · rw [type]; decide
      · rw [dict]; decide
    · rw [wait] at cut
      rw [cut] at headerRun
      cases headerRun
      have same : state = s :=
        Option.some.inj (good.live.hs.symm.trans invariant.good.live.hs)
      rw [same, mode]
      decide

end Zlib.Inflate.Proofs
