import ZlibF.Proof.«inflate.c.local-return-mode-trailer»
import ZlibF.Proof.«inflate.c.local-ret-loop»
import ZlibF.Proof.«inflate.c.return-mode-leave»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

theorem inflate_dispatch_construction_leave_ret
    {c : Ctx} {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : LocalStateJ h cutoff r zs z s)
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
    {c : Ctx} {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : LocalStateJ h cutoff r zs z s)
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
    {c : Ctx} {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (initial : l.ret = Z_OK ∨ s.mode = BAD)
    (run : runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, regs), after))
    (ended : regs.ret = Z_STREAM_END) (get : after.istates zs = some returned) : returned.mode = DONE := by
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
            · obtain ⟨source, final, _⟩ := inflate_LENGTH_default_state_boundary E invariant buffers length
              have actual := (inflate_dispatch_LENGTH E l length).trans source
              have same := xrun_state_eq actual run final.good.live.hs get
              rw [← same]
            · by_cases done : s.mode = DONE
              · have source := inflate_dispatch_terminal_run E l (Or.inl done)
                have same := xrun_state_eq source run invariant.good.live.hs get
                rw [← same]
                exact done
              · have unchanged := inflate_dispatch_ret_unchanged E table lengths codes bad check length done run
                exact False.elim (ok_not_end (unchanged.trans initialOK) ended)

#print axioms inflate_dispatch_data_error_mode
#print axioms inflate_dispatch_end_mode
end Zlib.Inflate.Local
