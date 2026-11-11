import ZlibF.Proof.«inflate.c.origin-fields-control»
import ZlibF.Proof.«inflate.c.head-default-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The real zlib header suffix retains both installed pointers. A rejected
header retains the old flag; an accepted header writes zero. -/
theorem headDefaultCheck_origin_record {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l regs : IL} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (wbits : HeadWindow s)
    (actual : runX (headDefaultCheck c s l) l h = .ok ((outcome, regs), after)) :
    ∃ state, after.istates zs = some state ∧ (state.flags = s.flags ∨ state.flags = 0) ∧
      state.lencode = s.lencode ∧ state.distcode = s.distcode ∧ state.wrap = s.wrap := by
  have rejected {out : IL} {i : Nat}
      (source : runX (headDefaultCheck c s l) l h = .ok ((.ok (), out), badHeap h r zs z s i)) :
      ∃ state, after.istates zs = some state ∧ (state.flags = s.flags ∨ state.flags = 0) ∧
        state.lencode = s.lencode ∧ state.distcode = s.distcode ∧ state.wrap = s.wrap := by
    have same : after = badHeap h r zs z s i :=
      congrArg Prod.snd (Except.ok.inj (actual.symm.trans source))
    exact ⟨{ s with mode := BAD }, by rw [same]; simp [badHeap], Or.inl rfl, rfl, rfl, rfl⟩
  have accepted
      (source : runX (headDefaultCheck c s l) l h = .ok ((.ok (), { headWindowRegs l with hold := 0, bits := 0 }),
        setI (r.put h { z with adler := 1 }) zs (headDefaultState s l))) :
      ∃ state, after.istates zs = some state ∧ (state.flags = s.flags ∨ state.flags = 0) ∧
        state.lencode = s.lencode ∧ state.distcode = s.distcode ∧ state.wrap = s.wrap := by
    have same : after = setI (r.put h { z with adler := 1 }) zs (headDefaultState s l) :=
      congrArg Prod.snd (Except.ok.inj (actual.symm.trans source))
    exact ⟨headDefaultState s l, by rw [same]; exact setI_istates_same .., Or.inr rfl, rfl, rfl, rfl⟩
  by_cases header : headHeaderRejected s l = true
  · obtain ⟨_, source⟩ := headDefaultCheck_bad_header E l header
    exact rejected source
  have headerFalse : headHeaderRejected s l = false := by cases test : headHeaderRejected s l <;> simp_all
  by_cases method : headMethodRejected l = true
  · obtain ⟨_, source⟩ := headDefaultCheck_bad_method E l headerFalse method
    exact rejected source
  have methodFalse : headMethodRejected l = false := by cases test : headMethodRejected l <;> simp_all
  by_cases zero : s.wbits = 0
  · by_cases big : 15 < (headWindowRegs l).len.toNat
    · obtain ⟨_, source⟩ := headDefaultCheck_bad_window_zero E l headerFalse methodFalse big
      exact rejected source
    · exact accepted (headDefaultCheck_accept_zero E l headerFalse methodFalse zero (by omega))
  have range := wbits.resolve_right (fun e => zero e.1)
  have nonzero : s.wbits ≠ 0 := zero
  by_cases window : s.wbits.toNat < (headWindowRegs l).len.toNat
  · obtain ⟨_, source⟩ := headDefaultCheck_bad_window E l headerFalse methodFalse nonzero window
    exact rejected source
  · exact accepted (headDefaultCheck_accept E l headerFalse methodFalse (by omega) range)

/-- Observe actual HEAD on input exhaustion, raw recovery and every zlib
header refusal or acceptance admitted by the existing default invariant. -/
theorem inflate_HEAD_origin_record {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l regs : IL} {bs : List UInt8} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs)
    (actual : runX (inflate_HEAD c) l h = .ok ((outcome, regs), after)) :
    ∃ state, after.istates zs = some state ∧ (state.flags = s.flags ∨ state.flags = 0) ∧
      state.lencode = s.lencode ∧ state.distcode = s.distcode ∧ state.wrap = s.wrap := by
  rcases invariant.wrapper with raw | wrapped
  · have source := inflate_HEAD_raw_run E l raw
    have same : after = setI h zs { s with mode := TYPEDO } :=
      congrArg Prod.snd (Except.ok.inj (actual.symm.trans source))
    exact ⟨{ s with mode := TYPEDO }, by rw [same]; exact setI_istates_same .., Or.inl rfl, rfl, rfl, rfl⟩
  · obtain ⟨result, current, _, _, _, _, _, _, _, _, cut, _⟩ :=
      inflate_HEAD_zlib_window_prefix_count E buffers.bits (zlibStub wrapped) (invariant.head_none (zlibStub wrapped))
    rw [cut] at actual
    cases result with
    | error exit =>
      cases actual
      exact ⟨s, E.hs, Or.inl rfl, rfl, rfl, rfl⟩
    | ok unit =>
      cases unit
      exact headDefaultCheck_origin_record E invariant.headWindow actual

/-- Actual HEAD dispatch has the same source origins. -/
theorem inflate_dispatch_HEAD_origin_record {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l regs : IL} {bs : List UInt8} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = HEAD)
    (actual : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    ∃ state, after.istates zs = some state ∧ (state.flags = s.flags ∨ state.flags = 0) ∧
      state.lencode = s.lencode ∧ state.distcode = s.distcode ∧ state.wrap = s.wrap := by
  rw [inflate_dispatch_HEAD E l mode] at actual
  exact inflate_HEAD_origin_record E invariant buffers actual

/-- Combine actual header writes with the matching real J result. -/
theorem DefaultOriginState.of_header_fields {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} (before : DefaultOriginState h r zs z s)
    (current : DefaultStateJ after r zs stream state) (flags : state.flags = s.flags ∨ state.flags = 0)
    (lengths : state.lencode = s.lencode) (distances : state.distcode = s.distcode)
    (wrap : state.wrap = s.wrap) :
    DefaultOriginState after r zs stream state := by
  refine ⟨current, ?_, ?_⟩
  · rcases flags with retained | zero
    · exact before.flagsOrigin.same retained wrap
    · exact Or.inr (Or.inl zero)
  · simpa only [CopyTableOrigin, lengths, distances] using before.tableOrigin

#print axioms inflate_dispatch_HEAD_origin_record
end Zlib.Inflate.Proofs
