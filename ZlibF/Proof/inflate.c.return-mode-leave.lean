import ZlibF.Proof.«inflate.c.return-mode-trailer»
import ZlibF.Proof.«inflate.c.ret-loop»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

private theorem retBaseX_ite_cases {base : Int32} {test : Prop} [Decidable test]
    {yes no : X Unit} (hy : test → RetBaseX base yes) (hn : ¬test → RetBaseX base no) :
    RetBaseX base (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy selected
  · simpa only [selected, ↓reduceIte] using hn selected

/-- The actual switch preserves ret outside its seven assignment modes. -/
theorem inflate_dispatch_ret_unchanged
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l regs : IL} {outcome : Except Ex Unit}
    (E : Env c h r zs z s)
    (notTable : s.mode ≠ TABLE) (notLengths : s.mode ≠ LENLENS)
    (notCodes : s.mode ≠ CODELENS) (notBad : s.mode ≠ BAD)
    (notCheck : s.mode ≠ CHECK) (notLength : s.mode ≠ LENGTH) (notDone : s.mode ≠ DONE)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    regs.ret = l.ret := by
  unfold inflate_dispatch at run
  rw [runX_bind, runX_rdS E] at run
  simp only [] at run
  have observe (program : X Unit) (post : RetBaseX l.ret program)
      (source : runX program l h = .ok ((outcome, regs), after)) : regs.ret = l.ret :=
    post _ _ _ _ _ rfl source
  apply observe _ ?_ run
  repeat' first
    | with_reducible exact retBaseX_inflate_LIT l.ret c
    | with_reducible exact retBaseX_inflate_MATCH l.ret c
    | with_reducible exact retBaseX_inflate_DISTEXT l.ret c
    | with_reducible exact retBaseX_inflate_DIST l.ret c
    | with_reducible exact retBaseX_inflate_LENEXT l.ret c
    | with_reducible exact retBaseX_inflate_LEN l.ret c
    | with_reducible exact retBaseX_inflate_LEN_ l.ret c
    | with_reducible exact retBaseX_inflate_COPY l.ret c
    | with_reducible exact retBaseX_inflate_COPY_ l.ret c
    | with_reducible exact retBaseX_inflate_STORED l.ret c
    | with_reducible exact retBaseX_inflate_TYPEDO l.ret c
    | with_reducible exact retBaseX_inflate_TYPE l.ret c
    | with_reducible exact retBaseX_inflate_DICT l.ret c
    | with_reducible exact retBaseX_inflate_DICTID l.ret c
    | with_reducible exact retBaseX_inflate_HCRC l.ret c
    | with_reducible exact retBaseX_inflate_COMMENT l.ret c
    | with_reducible exact retBaseX_inflate_NAME l.ret c
    | with_reducible exact retBaseX_inflate_EXTRA l.ret c
    | with_reducible exact retBaseX_inflate_EXLEN l.ret c
    | with_reducible exact retBaseX_inflate_OS l.ret c
    | with_reducible exact retBaseX_inflate_TIME l.ret c
    | with_reducible exact retBaseX_inflate_FLAGS l.ret c
    | with_reducible exact retBaseX_inflate_HEAD l.ret c
    | (exfalso; apply notCheck; simpa only [beq_iff_eq] using
        (show (s.mode == CHECK) = true from by assumption))
    | (exfalso; apply notLength; simpa only [beq_iff_eq] using
        (show (s.mode == LENGTH) = true from by assumption))
    | (exfalso; apply notDone; simpa only [beq_iff_eq] using
        (show (s.mode == DONE) = true from by assumption))
    | (exfalso; apply notTable; simpa only [beq_iff_eq] using
        (show (s.mode == TABLE) = true from by assumption))
    | (exfalso; apply notLengths; simpa only [beq_iff_eq] using
        (show (s.mode == LENLENS) = true from by assumption))
    | (exfalso; apply notCodes; simpa only [beq_iff_eq] using
        (show (s.mode == CODELENS) = true from by assumption))
    | (exfalso; apply notBad; simpa only [beq_iff_eq] using
        (show (s.mode == BAD) = true from by assumption))
    | with_reducible refine retBaseX_ite_cases (fun _ => ?_) (fun _ => ?_)
    | ret_base_source

theorem inflate_dispatch_construction_leave_ret
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs)
    (mode : s.mode = TABLE ∨ s.mode = LENLENS ∨ s.mode = CODELENS) (initial : l.ret = Z_OK)
    (run : runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, regs), after))
    (get : after.istates zs = some returned) : regs.ret = Z_OK := by
  rcases inflate_dispatch_ret_construction E invariant buffers mode initial run get with ok | ⟨impossible, _⟩
  · exact ok
  · cases impossible

private theorem ok_not_error {regs : IL} (ok : regs.ret = Z_OK)
    (error : regs.ret = Z_DATA_ERROR) : False :=
  (by decide : Z_OK ≠ Z_DATA_ERROR) (ok.symm.trans error)

private theorem ok_not_end {regs : IL} (ok : regs.ret = Z_OK)
    (ended : regs.ret = Z_STREAM_END) : False :=
  (by decide : Z_OK ≠ Z_STREAM_END) (ok.symm.trans ended)

/-- A DATA_ERROR return register is the actual BAD dispatch result, not an
unconverted table-constructor error or a partial checksum wait. -/
theorem inflate_dispatch_data_error_mode
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (initial : l.ret = Z_OK ∨ s.mode = BAD)
    (run : runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, regs), after))
    (error : regs.ret = Z_DATA_ERROR) (get : after.istates zs = some returned) : returned.mode = BAD := by
  by_cases bad : s.mode = BAD
  · have source := inflate_dispatch_terminal_run E l (Or.inr (Or.inl bad))
    have same := xrun_state_eq source run invariant.good.live.hs get
    rw [← same]
    exact bad
  · have initialOK := initial.resolve_right bad
    by_cases table : s.mode = TABLE
    · exact False.elim (ok_not_error (inflate_dispatch_construction_leave_ret E invariant buffers (Or.inl table) initialOK run get) error)
    · by_cases lengths : s.mode = LENLENS
      · exact False.elim (ok_not_error (inflate_dispatch_construction_leave_ret E invariant buffers (Or.inr (Or.inl lengths)) initialOK run get) error)
      · by_cases codes : s.mode = CODELENS
        · exact False.elim (ok_not_error (inflate_dispatch_construction_leave_ret E invariant buffers (Or.inr (Or.inr codes)) initialOK run get) error)
        · have result := inflate_dispatch_ret_nonconstruction E table lengths codes bad run
          rw [initialOK] at result
          rcases result with ok | ⟨_, ended⟩
          · exact False.elim (ok_not_error ok error)
          · exact False.elim ((by decide : Z_STREAM_END ≠ Z_DATA_ERROR) (ended.symm.trans error))

/-- Actual STREAM_END is produced by DONE or default trailer completion.
Every other branch preserves OK or normalizes a table failure via BAD. -/
theorem inflate_dispatch_end_mode
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (initial : l.ret = Z_OK ∨ s.mode = BAD)
    (run : runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, regs), after))
    (ended : regs.ret = Z_STREAM_END) (get : after.istates zs = some returned)
    (incoming : l.bits.toNat ≤ 39) : returned.mode = DONE := by
  by_cases bad : s.mode = BAD
  · have source := inflate_dispatch_terminal_run E l (Or.inr (Or.inl bad))
    have ret : regs.ret = Z_DATA_ERROR := by
      rw [← xrun_regs_eq source run]
      simp only [terminalRegs, bad, show BAD ≠ DONE from by decide, ↓reduceIte]
    exact False.elim ((by decide : Z_DATA_ERROR ≠ Z_STREAM_END) (ret.symm.trans ended))
  · have initialOK := initial.resolve_right bad
    by_cases table : s.mode = TABLE
    · exact False.elim (ok_not_end (inflate_dispatch_construction_leave_ret E invariant buffers (Or.inl table) initialOK run get) ended)
    · by_cases lengths : s.mode = LENLENS
      · exact False.elim (ok_not_end (inflate_dispatch_construction_leave_ret E invariant buffers (Or.inr (Or.inl lengths)) initialOK run get) ended)
      · by_cases codes : s.mode = CODELENS
        · exact False.elim (ok_not_end (inflate_dispatch_construction_leave_ret E invariant buffers (Or.inr (Or.inr codes)) initialOK run get) ended)
        · by_cases check : s.mode = CHECK
          · exact inflate_CHECK_end_mode E invariant buffers check initialOK
              ((inflate_dispatch_CHECK E l check).symm.trans run) ended get
          · by_cases length : s.mode = LENGTH
            · obtain ⟨_, _, _, _, state2, _, _, source, final, _, _, _, _, _, _, _, _, _,
                ⟨_, _, _, _, _, _, endDone⟩⟩ := inflate_LENGTH_state_rank E invariant buffers length incoming
              have actual := (inflate_dispatch_LENGTH E l length).trans source
              have same := xrun_state_eq actual run final.good.live.hs get
              have leave := xrun_outcome_eq actual run
              have sameRegs := xrun_regs_eq actual run
              rw [← same]
              exact endDone leave (by rw [sameRegs]; exact ended) (by rw [initialOK]; decide)
            · by_cases done : s.mode = DONE
              · have source := inflate_dispatch_terminal_run E l (Or.inl done)
                have same := xrun_state_eq source run invariant.good.live.hs get
                rw [← same]
                exact done
              · have unchanged := inflate_dispatch_ret_unchanged E table lengths codes bad check length done run
                exact False.elim (ok_not_end (unchanged.trans initialOK) ended)

#print axioms inflate_dispatch_data_error_mode
#print axioms inflate_dispatch_end_mode
end Zlib.Inflate.Proofs
