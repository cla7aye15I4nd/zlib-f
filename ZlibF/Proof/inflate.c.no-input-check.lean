import ZlibF.Proof.«inflate.c.held-bound»

/-!
# inflate.c: a call without input cannot make output and pass CHECK

In one call with no input (`have == 0` throughout) the decoder only drops
held bits. Output comes only from the data modes, which hold at most 32 bits
between dispatches. Leaving them for `TYPE` decodes the end-of-block code,
which drops at least one bit, so the block-control modes and `CHECK` are
reached with fewer than 32 bits, and `CHECK`'s `NEEDBITS(32)` cannot succeed.
So a call that rebases `out` in `CHECK` after making output has read input.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The modes and held bits reachable after output in a call without input. -/
def AfterOutput (mode bits : UInt32) : Prop :=
  mode = BAD ∨ (DataTableMode mode ∧ bits.toNat ≤ 32) ∨
    ((TYPE ≤ mode ∧ mode ≤ CODELENS ∨ mode = CHECK) ∧ bits.toNat < 32)

theorem AfterOutput.range {mode : UInt32} (m : TYPE ≤ mode ∧ mode ≤ CODELENS ∨ mode = CHECK) :
    mode ≠ HEAD ∧ mode ≠ DICTID ∧ mode ≠ DICT ∧ mode ≠ LENGTH ∧ ¬ TerminalMode mode ∧ ¬ DataTableMode mode := by
  rcases m with ⟨low, high⟩ | check
  · rw [UInt32.le_iff_toNat_le] at low high
    change 16191 ≤ mode.toNat at low
    change mode.toNat ≤ 16198 at high
    unfold TerminalMode DataTableMode
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first
      | (intro e; rw [e] at low high; revert low high; decide)
      | (rintro (e | e | e | e) <;> rw [e] at low high <;> revert low high <;> decide)
      | (rintro (e | e | e | e | e | e | e) <;> rw [e] at low high <;> revert low high <;> decide)
  · subst check
    unfold TerminalMode DataTableMode
    decide

/-- OPEN: a data dispatch with no input that ends in `TYPE` has dropped at
least one held bit (the end-of-block code has a positive length). -/
theorem inflate_dispatch_data_end_drops {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : DataTableMode s.mode) (empty : l.have_ = 0)
    {outcome : Except Ex Unit} {regs : IL} {after : Heap} {state : InflateState}
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some state) (type : state.mode = TYPE) :
    regs.bits.toNat < l.bits.toNat := by
  sorry

/-- A data dispatch with no input from at most 32 held bits ends in `AfterOutput`. -/
theorem inflate_dispatch_data_after {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : DataTableMode s.mode) (empty : l.have_ = 0)
    (held : l.bits.toNat ≤ 32)
    {outcome : Except Ex Unit} {regs : IL} {after : Heap} {state : InflateState}
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some state) :
    AfterOutput state.mode regs.bits := by
  obtain ⟨_, regs2, after2, _, state2, _, _, _, run2, final, exitMode, _, _, _, _, _, _, bits2, _⟩ :=
    inflate_dispatch_data_view_state_rank E invariant buffers mode
  obtain ⟨_, regsEq, heapEq⟩ := runX_same run run2
  subst regsEq heapEq
  have same : state = state2 := Option.some.inj (get.symm.trans final.good.live.hs)
  subst same
  rcases exitMode with data | type | bad
  · exact Or.inr (Or.inl ⟨data, by omega⟩)
  · have drops := inflate_dispatch_data_end_drops E invariant buffers mode empty run get type
    exact Or.inr (Or.inr ⟨Or.inl ⟨by rw [type]; decide, by rw [type]; decide⟩, by omega⟩)
  · exact Or.inl bad

/-- A table-construction dispatch with no input from at most 32 held bits
ends in `AfterOutput`; it may continue into the data modes. -/
theorem inflate_dispatch_construction_after {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE ∨ s.mode = LENLENS ∨ s.mode = CODELENS)
    (empty : l.have_ = 0) (held : l.bits.toNat ≤ 32)
    {outcome : Except Ex Unit} {regs : IL} {after : Heap} {state : InflateState}
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some state) (ok : outcome = .ok ()) :
    AfterOutput state.mode regs.bits := by
  obtain ⟨regs1, after1, stream1, state1, used, _, nextJ, _, packet, _, _, count1,
    _, _, _, bits1, _, stopped | continued⟩ :=
    inflate_dispatch_construction_state_boundary E invariant buffers mode
  · obtain ⟨outcome1, run1, why⟩ := stopped
    obtain ⟨outcomeEq, _, heapEq⟩ := runX_same run run1
    subst outcomeEq heapEq
    have same : state = state1 := Option.some.inj (get.symm.trans nextJ.good.live.hs)
    subst same
    rcases why with notOk | bad
    · exact absurd ok notOk
    · exact Or.inl bad
  · obtain ⟨nextMode, source⟩ := continued
    by_cases trees : c.flush = Z_TREES
    · rw [if_pos trees] at source
      obtain ⟨outcomeEq, _, _⟩ := runX_same run source
      rw [ok] at outcomeEq
      cases outcomeEq
    · rw [if_neg trees] at source
      have nextEnv : Env c after1 r zs stream1 state1 :=
        ⟨E.strm, E.st, nextJ.good.live.hz, nextJ.good.live.hs⟩
      have dataMode : DataTableMode state1.mode := by rw [nextMode]; unfold DataTableMode; decide
      have empty1 : regs1.have_ = 0 := by
        apply UInt32.toNat_inj.mp
        rw [empty] at count1
        simp only [UInt32.toNat_zero] at count1 ⊢
        omega
      exact inflate_dispatch_data_after nextEnv nextJ packet dataMode empty1 (by omega)
        ((inflate_dispatch_LEN_start nextEnv regs1 nextMode).trans (source.symm.trans run)) get

/-- A block-type dispatch from fewer than 32 held bits ends in `AfterOutput`. -/
theorem inflate_dispatch_type_after {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TYPE ∨ s.mode = TYPEDO)
    (held : l.bits.toNat < 32)
    {outcome : Except Ex Unit} {regs : IL} {after : Heap} {state : InflateState}
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some state) :
    AfterOutput state.mode regs.bits := by
  have bits := inflate_dispatch_type_held E invariant buffers mode run
  obtain ⟨_, regs2, after2, _, state2, _, _, run2, final, control, _⟩ :=
    inflate_dispatch_type_state_rank E invariant buffers mode (by omega)
  obtain ⟨_, regsEq, heapEq⟩ := runX_same run run2
  subst regsEq heapEq
  have same : state = state2 := Option.some.inj (get.symm.trans final.good.live.hs)
  subst same
  have small : regs.bits.toNat < 32 := by omega
  rcases control with m | m | m | m | m | m | m <;> rw [m]
  · exact Or.inr (Or.inr ⟨Or.inl ⟨by decide, by decide⟩, small⟩)
  · exact Or.inr (Or.inr ⟨Or.inl ⟨by decide, by decide⟩, small⟩)
  · exact Or.inr (Or.inr ⟨Or.inl ⟨by decide, by decide⟩, small⟩)
  · exact Or.inr (Or.inr ⟨Or.inl ⟨by decide, by decide⟩, small⟩)
  · exact Or.inr (Or.inl ⟨by unfold DataTableMode; decide, by omega⟩)
  · exact Or.inr (Or.inr ⟨Or.inr rfl, small⟩)
  · exact Or.inl rfl

/-- A stored-block dispatch from fewer than 32 held bits ends in `AfterOutput`,
and with no input it makes no output. -/
theorem inflate_dispatch_stored_after {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = STORED ∨ s.mode = COPY_ ∨ s.mode = COPY)
    (held : l.bits.toNat < 32)
    {outcome : Except Ex Unit} {regs : IL} {after : Heap} {state : InflateState}
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some state) :
    AfterOutput state.mode regs.bits := by
  have small : state.mode ≠ BAD → regs.bits.toNat < 32 := by
    intro notBad
    rcases mode with stored | start | copy
    · rw [inflate_dispatch_STORED E l stored] at run
      exact inflate_STORED_held E invariant buffers stored run get notBad
    · rw [inflate_dispatch_COPY_start E l start] at run
      obtain ⟨_, regs2, _, _, _, _, run2, _, _, _, _, _, _, _, _, _, _, bitsEq, _⟩ :=
        inflate_COPY_start_boundary_frame E invariant.good invariant.pending buffers start
      obtain ⟨_, regsEq, _⟩ := runX_same run run2
      rw [regsEq, bitsEq]
      exact held
    · rw [inflate_dispatch_COPY E l copy] at run
      obtain ⟨_, regs2, _, _, _, _, run2, _, _, _, _, _, _, _, _, _, _, bitsEq, _⟩ :=
        inflate_COPY_boundary_frame E invariant.good invariant.pending buffers copy
      obtain ⟨_, regsEq, _⟩ := runX_same run run2
      rw [regsEq, bitsEq]
      exact held
  obtain ⟨_, regs2, after2, _, state2, run2, final, exitMode⟩ :=
    inflate_dispatch_stored_state E invariant buffers mode
  obtain ⟨_, regsEq, heapEq⟩ := runX_same run run2
  subst regsEq heapEq
  have same : state = state2 := Option.some.inj (get.symm.trans final.good.live.hs)
  subst same
  rcases exitMode with m | m | m | m | m
  · exact Or.inr (Or.inr ⟨Or.inl ⟨by rw [m]; decide, by rw [m]; decide⟩, small (by rw [m]; decide)⟩)
  · exact Or.inr (Or.inr ⟨Or.inl ⟨by rw [m]; decide, by rw [m]; decide⟩, small (by rw [m]; decide)⟩)
  · exact Or.inr (Or.inr ⟨Or.inl ⟨by rw [m]; decide, by rw [m]; decide⟩, small (by rw [m]; decide)⟩)
  · exact Or.inr (Or.inr ⟨Or.inl ⟨by rw [m]; decide, by rw [m]; decide⟩, small (by rw [m]; decide)⟩)
  · exact Or.inl m

/-- With no input, a stored-block dispatch makes no output. -/
theorem inflate_dispatch_stored_no_output {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = STORED ∨ s.mode = COPY_ ∨ s.mode = COPY)
    (empty : l.have_ = 0)
    {outcome : Except Ex Unit} {regs : IL} {after : Heap}
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    regs.left = l.left := by
  have noBytes : bs.length = 0 := by
    have count := buffers.bits.have_eq
    rw [empty] at count
    simpa using count.symm
  rcases mode with stored | start | copy
  · rw [inflate_dispatch_STORED E l stored] at run
    exact inflate_STORED_no_output E invariant buffers empty run
  · rw [inflate_dispatch_COPY_start E l start] at run
    obtain ⟨_, regs2, _, _, made, madeBound, run2, _, _, _, _, _, _, _, _, _, leftCount, _⟩ :=
      inflate_COPY_start_boundary_frame E invariant.good invariant.pending buffers start
    obtain ⟨_, regsEq, _⟩ := runX_same run run2
    rw [regsEq]
    rw [noBytes] at madeBound
    apply UInt32.toNat_inj.mp
    omega
  · rw [inflate_dispatch_COPY E l copy] at run
    obtain ⟨_, regs2, _, _, made, madeBound, run2, _, _, _, _, _, _, _, _, _, leftCount, _⟩ :=
      inflate_COPY_boundary_frame E invariant.good invariant.pending buffers copy
    obtain ⟨_, regsEq, _⟩ := runX_same run run2
    rw [regsEq]
    rw [noBytes] at madeBound
    apply UInt32.toNat_inj.mp
    omega

/-- A `CHECK` dispatch with no input from fewer than 32 held bits leaves in
`CHECK` or reaches `BAD`; it does not rebase `out`. -/
theorem inflate_dispatch_check_after {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CHECK) (empty : l.have_ = 0)
    (held : l.bits.toNat < 32)
    {outcome : Except Ex Unit} {regs : IL} {after : Heap} {state : InflateState}
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some state) :
    state.mode ≠ LENGTH ∧ (outcome = .ok () → state.mode = BAD) := by
  rw [inflate_dispatch_CHECK E l mode] at run
  obtain ⟨_, regs2, after2, _, state2, _, _, run2, final, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    ⟨okBad, _, _, _, _, lengthFacts⟩⟩ :=
    inflate_CHECK_default_state_accounting_rank E invariant buffers mode (by omega)
  obtain ⟨outcomeEq, regsEq, heapEq⟩ := runX_same run run2
  subst outcomeEq regsEq heapEq
  have same : state = state2 := Option.some.inj (get.symm.trans final.good.live.hs)
  subst same
  refine ⟨fun length => ?_, okBad⟩
  have needs := (lengthFacts length).2.2
  rw [empty] at needs
  simp only [UInt32.toNat_zero] at needs
  omega

/-- One default dispatch in a call without input keeps `AfterOutput` once
output was made (the output count `left` moved from `base`). -/
theorem inflate_dispatch_no_input_step {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (local_ : HeaderLocal c h r s l) (incoming : l.bits.toNat ≤ 39)
    (held : s.mode ≠ BAD → l.bits.toNat ≤ 32) (empty : l.have_ = 0) (base : Nat)
    (pre : l.left.toNat ≠ base → AfterOutput s.mode l.bits)
    {outcome : Except Ex Unit} {regs : IL} {after : Heap} {state : InflateState}
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some state) (ok : outcome = .ok ()) :
    regs.left.toNat ≠ base → AfterOutput state.mode regs.bits := by
  intro moved
  -- a group that makes no output keeps `left`, so `pre` applies
  have entry (same : regs.left = l.left) : AfterOutput s.mode l.bits := pre (by rw [← same]; exact moved)
  rcases defaultMode_cases invariant.modes with head | dictionary | type | stored | construction | data | trailer | terminal | gzipHeader
  · have notAfter : ¬ AfterOutput s.mode l.bits := by
      rintro (bad | ⟨d, _⟩ | ⟨m, _⟩)
      · rw [head] at bad; exact absurd bad (by decide)
      · rw [head] at d; exact absurd d (by unfold DataTableMode; decide)
      · exact (AfterOutput.range m).1 head
    apply absurd _ notAfter
    apply entry
    by_cases gzip : GzipAllowed s.wrap
    · obtain ⟨_, regs2, _, _, _, _, _, run2, _, _, _, _, _, _, left2, _⟩ :=
        inflate_dispatch_HEAD_gzip_state_rank E invariant buffers head gzip
          (local_ (by rw [head]; decide) (by rw [head]; decide)) incoming
      obtain ⟨_, regsEq, _⟩ := runX_same run run2
      rw [regsEq]; exact left2
    · obtain ⟨_, regs2, _, _, _, _, _, run2, _, _, _, _, _, _, left2, _⟩ :=
        inflate_dispatch_HEAD_state_rank E invariant buffers head gzip incoming
      obtain ⟨_, regsEq, _⟩ := runX_same run run2
      rw [regsEq]; exact left2
  · have notAfter : ¬ AfterOutput s.mode l.bits := by
      rintro (bad | ⟨d, _⟩ | ⟨m, _⟩)
      · rcases dictionary with e | e <;> rw [e] at bad <;> exact absurd bad (by decide)
      · rcases dictionary with e | e <;> rw [e] at d <;> exact absurd d (by unfold DataTableMode; decide)
      · rcases dictionary with e | e
        · exact (AfterOutput.range m).2.1 e
        · exact (AfterOutput.range m).2.2.1 e
    apply absurd _ notAfter
    apply entry
    obtain ⟨_, regs2, _, _, _, _, _, run2, _, _, _, _, _, _, left2, _⟩ :=
      inflate_dispatch_dictionary_state_rank E invariant buffers dictionary incoming
    obtain ⟨_, regsEq, _⟩ := runX_same run run2
    rw [regsEq]; exact left2
  · obtain ⟨_, regs2, _, _, _, _, _, run2, _, _, _, _, _, _, _, left2, _⟩ :=
      inflate_dispatch_type_state_rank E invariant buffers type incoming
    obtain ⟨_, regsEq, _⟩ := runX_same run run2
    rcases entry (by rw [regsEq]; exact left2) with bad | ⟨d, _⟩ | ⟨_, small⟩
    · rcases type with e | e <;> rw [e] at bad <;> exact absurd bad (by decide)
    · rcases type with e | e <;> rw [e] at d <;> exact absurd d (by unfold DataTableMode; decide)
    · exact inflate_dispatch_type_after E invariant buffers type small run get
  · rcases entry (inflate_dispatch_stored_no_output E invariant buffers stored empty run) with
      bad | ⟨d, _⟩ | ⟨_, small⟩
    · rcases stored with e | e | e <;> rw [e] at bad <;> exact absurd bad (by decide)
    · rcases stored with e | e | e <;> rw [e] at d <;> exact absurd d (by unfold DataTableMode; decide)
    · exact inflate_dispatch_stored_after E invariant buffers stored small run get
  · exact inflate_dispatch_construction_after E invariant buffers construction empty
      (held (by rcases construction with e | e | e <;> rw [e] <;> decide)) run get ok
  · exact inflate_dispatch_data_after E invariant buffers data empty
      (held (by rcases data with e | e | e | e | e | e | e <;> rw [e] <;> decide)) run get
  · rcases trailer with check | length
    · obtain ⟨_, regs2, _, _, _, _, _, run2, _, _, _, _, _, _, left2, _⟩ :=
        inflate_CHECK_default_state_accounting_rank E invariant buffers check incoming
      have run' := run
      rw [inflate_dispatch_CHECK E l check] at run'
      obtain ⟨_, regsEq, _⟩ := runX_same run' run2
      rcases entry (by rw [regsEq]; exact left2) with bad | ⟨d, _⟩ | ⟨_, small⟩
      · rw [check] at bad; exact absurd bad (by decide)
      · rw [check] at d; exact absurd d (by unfold DataTableMode; decide)
      · exact Or.inl ((inflate_dispatch_check_after E invariant buffers check empty small run get).2 ok)
    · obtain ⟨_, regs2, _, _, _, _, _, run2, _, _, _, _, _, _, left2, _⟩ :=
        inflate_LENGTH_state_rank E invariant buffers length incoming
      have run' := run
      rw [inflate_dispatch_LENGTH E l length] at run'
      obtain ⟨_, regsEq, _⟩ := runX_same run' run2
      rcases entry (by rw [regsEq]; exact left2) with bad | ⟨d, _⟩ | ⟨m, _⟩
      · rw [length] at bad; exact absurd bad (by decide)
      · rw [length] at d; exact absurd d (by unfold DataTableMode; decide)
      · exact absurd length (AfterOutput.range m).2.2.2.1
  · obtain ⟨run2, _⟩ := inflate_dispatch_terminal_state E invariant buffers terminal
    obtain ⟨outcomeEq, _, _⟩ := runX_same run run2
    rw [ok] at outcomeEq
    unfold terminalExit at outcomeEq
    split at outcomeEq
    · cases outcomeEq
    · split at outcomeEq <;> cases outcomeEq
  · obtain ⟨low, high, _⟩ := gzipHeader
    have notAfter : ¬ AfterOutput s.mode l.bits := by
      have lowN := UInt32.le_iff_toNat_le.mp low
      have highN := UInt32.le_iff_toNat_le.mp high
      change 16181 ≤ s.mode.toNat at lowN
      change s.mode.toNat ≤ 16188 at highN
      rintro (bad | ⟨d, _⟩ | ⟨m, _⟩)
      · rw [bad] at highN; revert highN; decide
      · rcases d with e | e | e | e | e | e | e <;> rw [e] at highN <;> revert highN <;> decide
      · rcases m with ⟨l2, _⟩ | e
        · have := UInt32.le_iff_toNat_le.mp l2
          change 16191 ≤ s.mode.toNat at this
          omega
        · rw [e] at highN; revert highN; decide
    apply absurd _ notAfter
    apply entry
    have inRange : HEAD ≤ s.mode ∧ s.mode ≤ HCRC := ⟨UInt32.le_trans (by decide : HEAD ≤ FLAGS) low, high⟩
    obtain ⟨_, regs2, _, _, _, _, _, run2, _, _, _, _, _, _, left2, _⟩ :=
      inflate_dispatch_gzip_header_state_rank E invariant buffers ⟨low, high, ‹_›⟩
        (local_ inRange.1 inRange.2) incoming
    obtain ⟨_, regsEq, _⟩ := runX_same run run2
    rw [regsEq]; exact left2

end Zlib.Inflate.Proofs
