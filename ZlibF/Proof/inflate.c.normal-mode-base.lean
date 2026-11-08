import ZlibF.Proof.«inflate.c.default-view-dispatch-rank»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Observe the same private state from two proved runs of one program. -/
theorem xrun_state_eq {α : Type} {program : X α} {l firstRegs secondRegs : IL}
    {h firstHeap secondHeap : Heap} {first second : Except Ex α}
    {zs : Nat} {firstState secondState : InflateState}
    (a : runX program l h = .ok ((first, firstRegs), firstHeap))
    (b : runX program l h = .ok ((second, secondRegs), secondHeap))
    (firstGet : firstHeap.istates zs = some firstState)
    (secondGet : secondHeap.istates zs = some secondState) : firstState = secondState := by
  have heapEq : firstHeap = secondHeap := congrArg Prod.snd (Except.ok.inj (a.symm.trans b))
  rw [heapEq] at firstGet
  exact Option.some.inj (firstGet.symm.trans secondGet)

theorem xrun_outcome_eq {α : Type} {program : X α} {l firstRegs secondRegs : IL}
    {h firstHeap secondHeap : Heap} {first second : Except Ex α}
    (a : runX program l h = .ok ((first, firstRegs), firstHeap))
    (b : runX program l h = .ok ((second, secondRegs), secondHeap)) : first = second :=
  congrArg (fun result => result.1.1) (Except.ok.inj (a.symm.trans b))

theorem BlockControlMode.lt_mem {mode : UInt32} (allowed : BlockControlMode mode) : mode < MEM := by
  rcases allowed with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem StoredExitMode.lt_mem {mode : UInt32} (allowed : StoredExitMode mode) : mode < MEM := by
  rcases allowed with rfl | rfl | rfl | rfl | rfl <;> decide

theorem DataExitMode.lt_mem {mode : UInt32} (allowed : DataExitMode mode) : mode < MEM := by
  rcases allowed with data | rfl | rfl
  · rcases data with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  all_goals decide

/-- The concrete dictionary metadata preparation retains J. Both admitted
successor modes and all source fields are explicit. -/
theorem DefaultStateJ.prepare_dictionary {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultStateJ h r zs z s)
    (beforeMode : s.mode = DICTID ∨ s.mode = DICT) (value : UInt64)
    (next : UInt32) (nextMode : next = DICT ∨ next = TYPE) :
    DefaultStateJ (setI (r.put h { z with adler := value }) zs { s with check := value, mode := next })
      r zs { z with adler := value } { s with check := value, mode := next } := by
  let stream := { z with adler := value }
  let state := { s with check := value, mode := next }
  let heap := setI (r.put h stream) zs state
  have good : Good heap r zs stream state := invariant.good.setZI rfl
    invariant.good.live.zalloc invariant.good.live.zfree rfl
    (by change HEAD ≤ next ∧ next ≤ SYNC; rcases nextMode with rfl | rfl <;> decide)
    (invariant.good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl invariant.good.inv.bits rfl rfl rfl)
  have tables : DataTableInvariant heap state := by
    apply dataTableInvariant_inactive
    change ¬ DataTableMode next
    rcases nextMode with rfl | rfl <;> unfold DataTableMode <;> decide
  have pending : DataPendingInvariant state := by
    apply dataPendingInvariant_idle (s := state) invariant.pending.sane
    change next ≠ LENEXT ∧ next ≠ DIST ∧ next ≠ DISTEXT ∧ next ≠ MATCH
    rcases nextMode with rfl | rfl <;> decide
  have sizes : ByteViewSizes h heap := by
    intro ref
    rw [byte_view_get_setI, byte_view_get_stream_put]
  exact invariant.dictionary_update beforeMode good tables pending (by rfl)
    nextMode invariant.held sizes (by simp only [setI, ZStreamRef.put_static])

/-- HEAD has only its actual header or block/error continuation on a
normal return. It cannot construct MEM or SYNC. -/
theorem inflate_HEAD_normal_low
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = HEAD)
    (run : runX (inflate_HEAD c) l h = .ok ((.ok (), regs), after))
    (get : after.istates zs = some returned) : returned.mode < MEM := by
  rcases invariant.wrapper with raw | wrapped
  · have source := inflate_HEAD_raw_run E l raw
    have same := xrun_state_eq (firstState := { s with mode := TYPEDO })
      source run (by simp only [setI_istates_same]) get
    rw [← same]
    change TYPEDO < MEM
    decide
  · obtain ⟨outcome, outRegs, heap, stream, state, used, _, source, good, _, _, _, _,
      _, _, _, _, _, _, kinds, _, _⟩ :=
      inflate_HEAD_zlib_window_boundary_frame E invariant.good invariant.pending buffers mode
        wrapped invariant.header invariant.window
    have normal := xrun_outcome_eq source run
    have same := xrun_state_eq source run good.live.hs get
    rw [← same]
    rcases kinds with ⟨wait, _⟩ | ⟨_, allowed⟩
    · cases wait.symm.trans normal
    · rcases allowed with selected | selected | selected <;> rw [selected] <;> decide

end Zlib.Inflate.Proofs
