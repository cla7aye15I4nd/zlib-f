import ZlibF.Proof.«inflate.c.fast-memory-shape»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

theorem fastMemoryMetaFrameM_ub {α : Type} (r : ZStreamRef) (message : String) : FastMemoryMetaFrameM r (ub message : M α) := by
  intro h value after run
  cases run

theorem fastMemoryMetaFrameM_ite {α : Type} {r : ZStreamRef} {test : Prop} [Decidable test] {yes no : M α}
    (hy : FastMemoryMetaFrameM r yes) (hn : FastMemoryMetaFrameM r no) : FastMemoryMetaFrameM r (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy
  · simpa only [selected, ↓reduceIte] using hn

section pointers
variable {R T : Type} [Space Heap R T]

theorem fastMemoryMetaFrameM_ptr_add (r : ZStreamRef) (p : Ptr R) (offset : Int) : FastMemoryMetaFrameM r (p.add offset) := by
  intro h value after run
  unfold Ptr.add at run
  repeat' first | split at run | (cases run <;> rfl)

theorem fastMemoryMetaFrameM_ptr_load (r : ZStreamRef) (p : Ptr R) : FastMemoryMetaFrameM r (Ptr.load p : M T) := by
  intro h value after run
  unfold Ptr.load at run
  repeat' first | split at run | (cases run <;> rfl)

theorem fastMemoryMetaFrameM_ptr_index (r : ZStreamRef) (p : Ptr R) (index : Int) : FastMemoryMetaFrameM r (Ptr.index p index : M T) :=
  fastMemoryMetaFrameM_bind (fastMemoryMetaFrameM_ptr_add r p index) (fun next => fastMemoryMetaFrameM_ptr_load r next)

theorem fastMemoryMetaFrameM_ptr_diff [DecidableEq R] (r : ZStreamRef) (p q : Ptr R) : FastMemoryMetaFrameM r (p.diff q) := by
  intro h value after run
  unfold Ptr.diff at run
  repeat' first | split at run | (cases run <;> rfl)

theorem fastMemoryMetaFrameM_ptr_lt [DecidableEq R] (r : ZStreamRef) (p q : Ptr R) : FastMemoryMetaFrameM r (p.lt q) := by
  intro h value after run
  unfold Ptr.lt at run
  repeat' first | split at run | (cases run <;> rfl)

theorem fastMemoryMetaFrameM_ptr_le [DecidableEq R] (r : ZStreamRef) (p q : Ptr R) : FastMemoryMetaFrameM r (p.le q) :=
  fastMemoryMetaFrameM_bind (fastMemoryMetaFrameM_ptr_lt r q p) (fun _ => fastMemoryMetaFrameM_pure r _)

/-- A typed store retains allocation metadata whenever writes to that
array space do. The concrete byte/word/code spaces discharge this rule. -/
theorem fastMemoryMetaFrameM_ptr_store (r : ZStreamRef) (p : Ptr R) (value : T)
    (writes : ∀ (h : Heap) (ref : R) (old array : Array T), Space.get h ref = some old →
      Space.ro h ref = false → fastMemoryMeta (Space.put h ref array : Heap) = fastMemoryMeta h) :
    FastMemoryMetaFrameM r (p.store value) := by
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
          simp only [FastMemoryMetaFrame, writes h ref array _ get
            (by cases hro : Space.ro h ref <;> simp_all)]
        · cases run
end pointers

theorem byte_view_put_shape {h : Heap} {ref : BRef} {old array : Array UInt8}
    (get : Space.get h ref = some old) (write : Space.ro h ref = false) :
    Shape h (Space.put h ref array) := by
  cases ref with
  | blk id => exact shape_setB get array
  | str id => simp [Space.ro] at write
  | dstate_depth id =>
    cases state : h.dstates id with
    | none => simp [Space.get, state] at get
    | some s =>
      intro b
      by_cases same : b = id
      · subst b; simp [Shape, Space.put, state]
      · simp [Shape, Space.put, state, upd_ne _ _ _ _ same]
  | st_dist_code => simp [Space.ro] at write
  | st_length_code => simp [Space.ro] at write

theorem byte_view_put_memory_meta (h : Heap) (ref : BRef) (old array : Array UInt8)
    (get : Space.get h ref = some old) (write : Space.ro h ref = false) :
    fastMemoryMeta (Space.put h ref array) = fastMemoryMeta h := by
  have liveEq := fastMemoryMeta_live_eq_of_shape
    (byte_view_put_shape (array := array) get write)
  simp only [fastMemoryMeta]
  rw [liveEq]
  cases ref <;> simp only [Space.put]
  all_goals first | rfl | (split <;> rfl)

/-- Byte-view writes retain allocation shape and metadata. -/
theorem fastMemoryMetaFrameM_store8 (r : ZStreamRef) (p : BPtr) (value : UInt8) : FastMemoryMetaFrameM r (store8 p value) :=
  fastMemoryMetaFrameM_ptr_store r p value
    (fun h ref old array get write => byte_view_put_memory_meta h ref old array get write)

theorem fastMemoryMetaFrameM_ldS (r : ZStreamRef) (pointer : InflateStatePtr) : FastMemoryMetaFrameM r (ldInflateState pointer) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some pointer =>
    cases pointer with
    | tab zs =>
      rw [ldI_eq] at run
      split at run <;> cases run
      rfl

theorem fastMemoryMetaFrameM_ldZ (r : ZStreamRef) (pointer : ZStreamPtr) : FastMemoryMetaFrameM r (ldZStream pointer) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some pointer =>
    rw [ldZ_eq] at run
    split at run <;> cases run
    rfl

theorem fastMemoryMetaFrameM_rdS {α : Type} (r : ZStreamRef) (pointer : InflateStatePtr) (field : InflateState → α) :
    FastMemoryMetaFrameM r (rdS pointer field) :=
  fastMemoryMetaFrameM_bind (fastMemoryMetaFrameM_ldS r pointer) (fun _ => fastMemoryMetaFrameM_pure r _)

theorem fastMemoryMetaFrameM_rdZ {α : Type} (r : ZStreamRef) (pointer : ZStreamPtr) (field : ZStream → α) :
    FastMemoryMetaFrameM r (rdZ pointer field) :=
  fastMemoryMetaFrameM_bind (fastMemoryMetaFrameM_ldZ r pointer) (fun _ => fastMemoryMetaFrameM_pure r _)

theorem fastMemoryMetaFrameM_wrS_any (r : ZStreamRef) (pointer : InflateStatePtr) (update : InflateState → InflateState) :
    FastMemoryMetaFrameM r (wrS pointer update) := by
  cases pointer with
  | none => intro h value after run; cases run
  | some pointer => cases pointer with | tab zs => exact fastMemoryMetaFrameM_wrS r zs update

theorem fastMemoryMetaFrameM_setMode (r : ZStreamRef) (pointer : InflateStatePtr) (mode : UInt32) :
    FastMemoryMetaFrameM r (setMode pointer mode) := fastMemoryMetaFrameM_wrS_any r pointer _

theorem fastMemoryMetaFrameM_shl32 (r : ZStreamRef) (value shift : UInt32) : FastMemoryMetaFrameM r (shl32 value shift) := by
  unfold shl32
  exact fastMemoryMetaFrameM_ite (fastMemoryMetaFrameM_pure r _) (fastMemoryMetaFrameM_ub r _)

/-- Read-only flags and the allocation frontier are preserved by successful do-while executions. -/
theorem fastMemoryMetaFrameM_cdoWhile {σ : Type} {r : ZStreamRef} {body : σ → M σ} {cond : σ → M (Bool × σ)}
    (hb : ∀ state, FastMemoryMetaFrameM r (body state)) (hc : ∀ state, FastMemoryMetaFrameM r (cond state))
    (state : σ) : FastMemoryMetaFrameM r (cdoWhile body cond state) := by
  have key : ∀ n state, FastMemoryMetaFrameM r (cdoWhile.go body cond n state) := by
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
theorem fastMemoryMetaFrameM_list_forIn {α β : Type} (r : ZStreamRef) (values : List α)
    (body : (value : α) → value ∈ values → β → M (ForInStep β))
    (frames : ∀ value membership state, FastMemoryMetaFrameM r (body value membership state))
    (initial : β) : FastMemoryMetaFrameM r (List.forIn' values initial body) := by
  induction values generalizing initial with
  | nil =>
    simp only [List.forIn'_eq_forIn', List.forIn'_nil]
    exact fastMemoryMetaFrameM_pure r _
  | cons head tail ih =>
    simp only [List.forIn'_eq_forIn', List.forIn'_cons]
    refine fastMemoryMetaFrameM_bind (frames head (by simp) initial) (fun decision => ?_)
    cases decision with
    | done result => exact fastMemoryMetaFrameM_pure r _
    | yield next =>
      exact ih (fun value membership state => body value (by simp [membership]) state)
        (fun value membership state => frames value (by simp [membership]) state) next

theorem fastMemoryMetaFrameM_stS (r : ZStreamRef) (pointer : InflateStatePtr) (state : InflateState) :
    FastMemoryMetaFrameM r (stInflateState pointer state) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some pointer =>
    cases pointer with
    | tab zs =>
      rw [stI_eq] at run
      split at run
      · cases run
        have liveEq := fastMemoryMeta_live_eq_of_shape (shape_setI (by assumption) state)
        simp only [FastMemoryMetaFrame, fastMemoryMeta]
        rw [liveEq]
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
theorem fastMemoryMetaFrameM_ldZ_update {α : Type} (r : ZStreamRef) (update : ZStream → ZStream)
    (next : Unit → M α) (fixed : ∀ z, streamProtected (update z) = streamProtected z)
    (frame : ∀ value, FastMemoryMetaFrameM r (next value)) :
    FastMemoryMetaFrameM r (ldZStream (some r) >>= fun z => stZStream (some r) (update z) >>= next) := by
  rw [← memory_meta_frame_bind_assoc]
  change FastMemoryMetaFrameM r (wrZ (some r) update >>= next)
  exact fastMemoryMetaFrameM_bind (fastMemoryMetaFrameM_wrZ r update fixed) frame

theorem fastMemoryMetaFrameM_castI (r : ZStreamRef) (state : Option StateRef) : FastMemoryMetaFrameM r (castInflateState state) := by
  intro h value after run
  unfold castInflateState at run
  repeat' first | split at run | (cases run <;> rfl)

theorem fastMemoryMetaFrameM_strLit (r : ZStreamRef) (message : String) : FastMemoryMetaFrameM r (Zlib.Zutil.strLit message) := by
  intro h value after run
  unfold Zlib.Zutil.strLit strLitRef at run
  repeat' first | split at run | (cases run <;> rfl)


end Zlib.Inflate.Proofs
