import ZlibF.Proof.«inflate.c.memory-meta-frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

theorem memoryMetaFrameM_ub {α : Type} (r : ZStreamRef) (message : String) : MemoryMetaFrameM r (ub message : M α) := by
  intro h value after run
  cases run

theorem memoryMetaFrameM_ite {α : Type} {r : ZStreamRef} {test : Prop} [Decidable test] {yes no : M α}
    (hy : MemoryMetaFrameM r yes) (hn : MemoryMetaFrameM r no) : MemoryMetaFrameM r (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy
  · simpa only [selected, ↓reduceIte] using hn

section pointers
variable {R T : Type} [Space Heap R T]

theorem memoryMetaFrameM_ptr_add (r : ZStreamRef) (p : Ptr R) (offset : Int) : MemoryMetaFrameM r (p.add offset) := by
  intro h value after run
  unfold Ptr.add at run
  repeat' first | split at run | (cases run <;> rfl)

theorem memoryMetaFrameM_ptr_load (r : ZStreamRef) (p : Ptr R) : MemoryMetaFrameM r (Ptr.load p : M T) := by
  intro h value after run
  unfold Ptr.load at run
  repeat' first | split at run | (cases run <;> rfl)

theorem memoryMetaFrameM_ptr_index (r : ZStreamRef) (p : Ptr R) (index : Int) : MemoryMetaFrameM r (Ptr.index p index : M T) :=
  memoryMetaFrameM_bind (memoryMetaFrameM_ptr_add r p index) (fun next => memoryMetaFrameM_ptr_load r next)

theorem memoryMetaFrameM_ptr_diff [DecidableEq R] (r : ZStreamRef) (p q : Ptr R) : MemoryMetaFrameM r (p.diff q) := by
  intro h value after run
  unfold Ptr.diff at run
  repeat' first | split at run | (cases run <;> rfl)

theorem memoryMetaFrameM_ptr_lt [DecidableEq R] (r : ZStreamRef) (p q : Ptr R) : MemoryMetaFrameM r (p.lt q) := by
  intro h value after run
  unfold Ptr.lt at run
  repeat' first | split at run | (cases run <;> rfl)

theorem memoryMetaFrameM_ptr_le [DecidableEq R] (r : ZStreamRef) (p q : Ptr R) : MemoryMetaFrameM r (p.le q) :=
  memoryMetaFrameM_bind (memoryMetaFrameM_ptr_lt r q p) (fun _ => memoryMetaFrameM_pure r _)

/-- A typed store retains allocation metadata whenever writes to that
array space do. The concrete byte/word/code spaces discharge this rule. -/
theorem memoryMetaFrameM_ptr_store (r : ZStreamRef) (p : Ptr R) (value : T)
    (writes : ∀ (h : Heap) (ref : R) (array : Array T), memoryMeta (Space.put h ref array : Heap) = memoryMeta h) :
    MemoryMetaFrameM r (p.store value) := by
  intro h result after run
  cases p with
  | null => cases run
  | ref ref off =>
    cases get : Space.get h ref with
    | none => simp only [Ptr.store, get] at run; cases run
    | some array =>
      simp only [Ptr.store, get] at run
      split at run
      · cases run
      · split at run
        · rw [Space.modify_eq h ref array _ get] at run
          cases run
          simp only [MemoryMetaFrame, writes]
        · cases run
end pointers

theorem byte_view_put_memory_meta (h : Heap) (ref : BRef) (array : Array UInt8) (_r : ZStreamRef) :
    memoryMeta (Space.put h ref array) = memoryMeta h := by
  cases ref <;> simp only [Space.put]
  all_goals first | rfl | (split <;> rfl)

/-- Byte-view writes retain read-only flags and the allocation frontier. -/
theorem memoryMetaFrameM_store8 (r : ZStreamRef) (p : BPtr) (value : UInt8) : MemoryMetaFrameM r (store8 p value) :=
  memoryMetaFrameM_ptr_store r p value (fun h ref array => byte_view_put_memory_meta h ref array r)

theorem memoryMetaFrameM_ldS (r : ZStreamRef) (pointer : InflateStatePtr) : MemoryMetaFrameM r (ldInflateState pointer) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some pointer =>
    cases pointer with
    | tab zs =>
      rw [ldI_eq] at run
      split at run <;> cases run
      rfl

theorem memoryMetaFrameM_ldZ (r : ZStreamRef) (pointer : ZStreamPtr) : MemoryMetaFrameM r (ldZStream pointer) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some pointer =>
    rw [ldZ_eq] at run
    split at run <;> cases run
    rfl

theorem memoryMetaFrameM_rdS {α : Type} (r : ZStreamRef) (pointer : InflateStatePtr) (field : InflateState → α) :
    MemoryMetaFrameM r (rdS pointer field) :=
  memoryMetaFrameM_bind (memoryMetaFrameM_ldS r pointer) (fun _ => memoryMetaFrameM_pure r _)

theorem memoryMetaFrameM_rdZ {α : Type} (r : ZStreamRef) (pointer : ZStreamPtr) (field : ZStream → α) :
    MemoryMetaFrameM r (rdZ pointer field) :=
  memoryMetaFrameM_bind (memoryMetaFrameM_ldZ r pointer) (fun _ => memoryMetaFrameM_pure r _)

theorem memoryMetaFrameM_wrS_any (r : ZStreamRef) (pointer : InflateStatePtr) (update : InflateState → InflateState) :
    MemoryMetaFrameM r (wrS pointer update) := by
  cases pointer with
  | none => intro h value after run; cases run
  | some pointer => cases pointer with | tab zs => exact memoryMetaFrameM_wrS r zs update

theorem memoryMetaFrameM_setMode (r : ZStreamRef) (pointer : InflateStatePtr) (mode : UInt32) :
    MemoryMetaFrameM r (setMode pointer mode) := memoryMetaFrameM_wrS_any r pointer _

theorem memoryMetaFrameM_shl32 (r : ZStreamRef) (value shift : UInt32) : MemoryMetaFrameM r (shl32 value shift) := by
  unfold shl32
  exact memoryMetaFrameM_ite (memoryMetaFrameM_pure r _) (memoryMetaFrameM_ub r _)

/-- Read-only flags and the allocation frontier are preserved by successful do-while executions. -/
theorem memoryMetaFrameM_cdoWhile {σ : Type} {r : ZStreamRef} {body : σ → M σ} {cond : σ → M (Bool × σ)}
    (hb : ∀ state, MemoryMetaFrameM r (body state)) (hc : ∀ state, MemoryMetaFrameM r (cond state))
    (state : σ) : MemoryMetaFrameM r (cdoWhile body cond state) := by
  have key : ∀ n state, MemoryMetaFrameM r (cdoWhile.go body cond n state) := by
    intro n
    induction n with
    | zero =>
      intro state h value after run
      simp only [cdoWhile.go] at run
      cases run
    | succ n ih =>
      intro state h value after run
      simp only [cdoWhile.go, bind_app] at run
      cases executed : body state h with
      | error fault => rw [executed] at run; cases run
      | ok pair =>
        obtain ⟨middle, heap1⟩ := pair
        rw [executed] at run
        have first := hb state h middle heap1 executed
        simp only [] at run
        cases condition : cond middle heap1 with
        | error fault => rw [condition] at run; cases run
        | ok pair =>
          obtain ⟨⟨test, next⟩, heap2⟩ := pair
          rw [condition] at run
          have second := hc middle heap1 (test, next) heap2 condition
          cases test with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, pure_app] at run
            cases run
            exact first.trans second
          | true =>
            simp only [ite_true] at run
            exact first.trans (second.trans (ih next heap2 value after run))
  exact key fuel state

/-- Finite source for-loops retain the frame, including early completion. -/
theorem memoryMetaFrameM_list_forIn {α β : Type} (r : ZStreamRef) (values : List α)
    (body : (value : α) → value ∈ values → β → M (ForInStep β))
    (frames : ∀ value membership state, MemoryMetaFrameM r (body value membership state))
    (initial : β) : MemoryMetaFrameM r (List.forIn' values initial body) := by
  induction values generalizing initial with
  | nil =>
    simp only [List.forIn'_eq_forIn', List.forIn'_nil]
    exact memoryMetaFrameM_pure r _
  | cons head tail ih =>
    simp only [List.forIn'_eq_forIn', List.forIn'_cons]
    refine memoryMetaFrameM_bind (frames head (by simp) initial) (fun decision => ?_)
    cases decision with
    | done result => exact memoryMetaFrameM_pure r _
    | yield next =>
      exact ih (fun value membership state => body value (by simp [membership]) state)
        (fun value membership state => frames value (by simp [membership]) state) next

/-- Word/code array writes retain read-only flags and the allocation frontier. -/
theorem word_view_put_memory_meta (h : Heap) (ref : WRef) (array : Array UInt16) (r : ZStreamRef) :
    memoryMeta (Space.put h ref array) = memoryMeta h := by
  cases ref <;> simp only [Space.put]
  all_goals first | rfl | (split <;> rfl)

theorem code_view_put_memory_meta (h : Heap) (ref : CodeRef) (array : Array Code) (r : ZStreamRef) :
    memoryMeta (Space.put h ref array) = memoryMeta h := by
  cases ref <;> simp only [Space.put]
  all_goals first | rfl | (split <;> rfl)

theorem memoryMetaFrameM_store16 (r : ZStreamRef) (p : WPtr) (value : UInt16) : MemoryMetaFrameM r (p.store value) :=
  memoryMetaFrameM_ptr_store r p value (fun h ref array => word_view_put_memory_meta h ref array r)

theorem memoryMetaFrameM_storeCode (r : ZStreamRef) (p : CodePtr) (value : Code) : MemoryMetaFrameM r (p.store value) :=
  memoryMetaFrameM_ptr_store r p value (fun h ref array => code_view_put_memory_meta h ref array r)

theorem memoryMetaFrameM_stS (r : ZStreamRef) (pointer : InflateStatePtr) (state : InflateState) :
    MemoryMetaFrameM r (stInflateState pointer state) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some pointer =>
    cases pointer with
    | tab zs =>
      rw [stI_eq] at run
      split at run
      · cases run
        rfl
      · cases run

/-- Associativity for the concrete C state/fault monad. -/
theorem memory_meta_frame_bind_assoc {α β γ : Type} (first : M α) (next : α → M β) (last : β → M γ) :
    ((first >>= next) >>= last) = (first >>= fun value => next value >>= last) := by
  funext h
  simp only [bind_app]
  cases first h <;> rfl

/-- A literal load/update pair is the actual wrZ operation, even when
followed by more source code. Its old stream value is not generalized away. -/
theorem memoryMetaFrameM_ldZ_update {α : Type} (r : ZStreamRef) (update : ZStream → ZStream)
    (next : Unit → M α) (fixed : ∀ z, streamProtected (update z) = streamProtected z)
    (frame : ∀ value, MemoryMetaFrameM r (next value)) :
    MemoryMetaFrameM r (ldZStream (some r) >>= fun z => stZStream (some r) (update z) >>= next) := by
  rw [← memory_meta_frame_bind_assoc]
  change MemoryMetaFrameM r (wrZ (some r) update >>= next)
  exact memoryMetaFrameM_bind (memoryMetaFrameM_wrZ r update fixed) frame

theorem memoryMetaFrameM_castI (r : ZStreamRef) (state : Option StateRef) : MemoryMetaFrameM r (castInflateState state) := by
  intro h value after run
  unfold castInflateState at run
  repeat' first | split at run | (cases run <;> rfl)

theorem memoryMetaFrameM_strLit (r : ZStreamRef) (message : String) : MemoryMetaFrameM r (Zlib.Zutil.strLit message) := by
  intro h value after run
  unfold Zlib.Zutil.strLit strLitRef at run
  repeat' first | split at run | (cases run <;> rfl)

/-- A successful byte memcpy changes only its represented byte view. -/
theorem memoryMetaFrameM_memcpyB (r : ZStreamRef) (destination source : BPtr) (count : Nat) :
    MemoryMetaFrameM r (memcpyB destination source count) := by
  intro h value after run
  cases destination with
  | null => cases run
  | ref dest off =>
    cases source with
    | null => cases run
    | ref src srcOff =>
      cases destGet : (Space.get h dest : Option (Array UInt8)) <;>
        cases srcGet : (Space.get h src : Option (Array UInt8))
      all_goals simp only [memcpyB, Ptr.memcpy, destGet, srcGet] at run
      all_goals first
        | cases run
        | skip
      rename_i array sourceArray
      rw [Space.modify_eq h dest array _ destGet] at run
      repeat' first
        | split at run
        | (cases run <;> exact byte_view_put_memory_meta _ _ _ r)

/-- Literal messages are a partial update of the same live stream. -/
theorem memoryMetaFrameM_setMsg (r : ZStreamRef) (message : String) : MemoryMetaFrameM r (setMsg (some r) message) := by
  unfold setMsg
  refine memoryMetaFrameM_bind (memoryMetaFrameM_strLit r _) (fun pointer => ?_)
  change MemoryMetaFrameM r (wrZ (some r) (fun z => { z with msg := pointer }))
  exact memoryMetaFrameM_wrZ r _ (fun _ => rfl)

theorem memoryMetaFrameM_ldHeader (r : ZStreamRef) (pointer : GzHeaderPtr) : MemoryMetaFrameM r (ldGzHeader pointer) := by
  intro h value after run
  unfold ldGzHeader at run
  repeat' first | split at run | (cases run <;> rfl)

theorem memoryMetaFrameM_stHeader (r : ZStreamRef) (pointer : GzHeaderPtr) (header : GzHeader) :
    MemoryMetaFrameM r (stGzHeader pointer header) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some pointer =>
    cases pointer with
    | tab id =>
      simp only [stGzHeader, GzHeaderRef.get, GzHeaderRef.isRo, Bool.false_eq_true, ↓reduceIte] at run
      cases get : h.gzheaders id with
      | none => rw [get] at run; cases run
      | some old =>
        rw [get] at run
        cases run
        simp only [MemoryMetaFrame, memoryMeta, GzHeaderRef.put, get]

theorem memoryMetaFrameM_shr32 (r : ZStreamRef) (value shift : UInt32) : MemoryMetaFrameM r (shr32 value shift) := by
  unfold shr32
  exact memoryMetaFrameM_ite (memoryMetaFrameM_pure r _) (memoryMetaFrameM_ub r _)

theorem memoryMetaFrameM_shl64 (r : ZStreamRef) (value : UInt64) (shift : UInt32) : MemoryMetaFrameM r (shl64 value shift) := by
  unfold shl64
  exact memoryMetaFrameM_ite (memoryMetaFrameM_pure r _) (memoryMetaFrameM_ub r _)

theorem memoryMetaFrameM_shr64 (r : ZStreamRef) (value : UInt64) (shift : UInt32) : MemoryMetaFrameM r (shr64 value shift) := by
  unfold shr64
  exact memoryMetaFrameM_ite (memoryMetaFrameM_pure r _) (memoryMetaFrameM_ub r _)

theorem memoryMetaFrameM_chkI32 (r : ZStreamRef) (value : Int) : MemoryMetaFrameM r (chkI32 value) := by
  unfold chkI32
  exact memoryMetaFrameM_ite (memoryMetaFrameM_pure r _) (memoryMetaFrameM_ub r _)

theorem memoryMetaFrameM_chkI64 (r : ZStreamRef) (value : Int) : MemoryMetaFrameM r (chkI64 value) := by
  unfold chkI64
  exact memoryMetaFrameM_ite (memoryMetaFrameM_pure r _) (memoryMetaFrameM_ub r _)

theorem memoryMetaFrameM_hcrcOn (r : ZStreamRef) (pointer : InflateStatePtr) : MemoryMetaFrameM r (hcrcOn pointer) :=
  memoryMetaFrameM_bind (memoryMetaFrameM_ldS r pointer) (fun _ => memoryMetaFrameM_pure r _)

theorem memoryMetaFrameM_badMode (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) (message : String) :
    MemoryMetaFrameM r (badMode context message) := by
  unfold badMode
  rw [root]
  exact memoryMetaFrameM_bind (memoryMetaFrameM_setMsg r message) (fun _ => memoryMetaFrameM_setMode r _ _)

theorem memoryMetaFrameX_xdoWhile {r : ZStreamRef} {body : X Unit} {cond : X Bool}
    (hb : MemoryMetaFrameX r body) (hc : MemoryMetaFrameX r cond) : MemoryMetaFrameX r (xdoWhile body cond) :=
  memoryMetaFrameX_bind hb (fun _ => memoryMetaFrameX_xwhile hc hb)

theorem memoryMetaFrameX_xloopBrk {r : ZStreamRef} {body : X Bool} (frame : MemoryMetaFrameX r body) :
    MemoryMetaFrameX r (xloopBrk body) := memoryMetaFrameX_xwhileBrk (memoryMetaFrameX_pure r true) frame

theorem memoryMetaFrameM_orderAt (r : ZStreamRef) (index : UInt32) : MemoryMetaFrameM r (orderAt index) := by
  unfold orderAt
  split
  · exact memoryMetaFrameM_pure r _
  · exact memoryMetaFrameM_ub r _

end Zlib.Inflate.Proofs
