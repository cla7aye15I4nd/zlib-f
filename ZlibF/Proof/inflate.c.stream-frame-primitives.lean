import ZlibF.Proof.«inflate.c.stream-frame»
import ZlibF.Proof.«inflate.c.byte-views»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

theorem streamFrameM_ub {α : Type} (r : ZStreamRef) (message : String) : StreamFrameM r (ub message : M α) := by
  intro h value after run
  cases run

theorem streamFrameM_ite {α : Type} {r : ZStreamRef} {test : Prop} [Decidable test] {yes no : M α}
    (hy : StreamFrameM r yes) (hn : StreamFrameM r no) : StreamFrameM r (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy
  · simpa only [selected, ↓reduceIte] using hn

section pointers
variable {R T : Type} [Space Heap R T]

theorem streamFrameM_ptr_add (r : ZStreamRef) (p : Ptr R) (offset : Int) : StreamFrameM r (p.add offset) := by
  intro h value after run
  unfold Ptr.add at run
  repeat' first | split at run | (cases run <;> rfl)

theorem streamFrameM_ptr_load (r : ZStreamRef) (p : Ptr R) : StreamFrameM r (Ptr.load p : M T) := by
  intro h value after run
  unfold Ptr.load at run
  repeat' first | split at run | (cases run <;> rfl)

theorem streamFrameM_ptr_index (r : ZStreamRef) (p : Ptr R) (index : Int) : StreamFrameM r (Ptr.index p index : M T) :=
  streamFrameM_bind (streamFrameM_ptr_add r p index) (fun next => streamFrameM_ptr_load r next)

theorem streamFrameM_ptr_diff [DecidableEq R] (r : ZStreamRef) (p q : Ptr R) : StreamFrameM r (p.diff q) := by
  intro h value after run
  unfold Ptr.diff at run
  repeat' first | split at run | (cases run <;> rfl)

theorem streamFrameM_ptr_lt [DecidableEq R] (r : ZStreamRef) (p q : Ptr R) : StreamFrameM r (p.lt q) := by
  intro h value after run
  unfold Ptr.lt at run
  repeat' first | split at run | (cases run <;> rfl)

theorem streamFrameM_ptr_le [DecidableEq R] (r : ZStreamRef) (p q : Ptr R) : StreamFrameM r (p.le q) :=
  streamFrameM_bind (streamFrameM_ptr_lt r q p) (fun _ => streamFrameM_pure r _)

/-- A typed store preserves the stream root whenever writes to that
array space do. The concrete byte/word/code spaces discharge this rule. -/
theorem streamFrameM_ptr_store (r : ZStreamRef) (p : Ptr R) (value : T)
    (writes : ∀ (h : Heap) (ref : R) (array : Array T), r.get (Space.put h ref array : Heap) = r.get h) :
    StreamFrameM r (p.store value) := by
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
          simp only [StreamRootFrame, writes]
        · cases run
end pointers

/-- All represented byte views preserve the stream record on writes. -/
theorem streamFrameM_store8 (r : ZStreamRef) (p : BPtr) (value : UInt8) : StreamFrameM r (store8 p value) :=
  streamFrameM_ptr_store r p value (fun h ref array => byte_view_put_stream h ref array r)

theorem streamFrameM_ldS (r : ZStreamRef) (pointer : InflateStatePtr) : StreamFrameM r (ldInflateState pointer) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some pointer =>
    cases pointer with
    | tab zs =>
      rw [ldI_eq] at run
      split at run <;> cases run
      rfl

theorem streamFrameM_ldZ (r : ZStreamRef) (pointer : ZStreamPtr) : StreamFrameM r (ldZStream pointer) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some pointer =>
    rw [ldZ_eq] at run
    split at run <;> cases run
    rfl

theorem streamFrameM_rdS {α : Type} (r : ZStreamRef) (pointer : InflateStatePtr) (field : InflateState → α) :
    StreamFrameM r (rdS pointer field) :=
  streamFrameM_bind (streamFrameM_ldS r pointer) (fun _ => streamFrameM_pure r _)

theorem streamFrameM_rdZ {α : Type} (r : ZStreamRef) (pointer : ZStreamPtr) (field : ZStream → α) :
    StreamFrameM r (rdZ pointer field) :=
  streamFrameM_bind (streamFrameM_ldZ r pointer) (fun _ => streamFrameM_pure r _)

theorem streamFrameM_wrS_any (r : ZStreamRef) (pointer : InflateStatePtr) (update : InflateState → InflateState) :
    StreamFrameM r (wrS pointer update) := by
  cases pointer with
  | none => intro h value after run; cases run
  | some pointer => cases pointer with | tab zs => exact streamFrameM_wrS r zs update

theorem streamFrameM_setMode (r : ZStreamRef) (pointer : InflateStatePtr) (mode : UInt32) :
    StreamFrameM r (setMode pointer mode) := streamFrameM_wrS_any r pointer _

theorem streamFrameM_shl32 (r : ZStreamRef) (value shift : UInt32) : StreamFrameM r (shl32 value shift) := by
  unfold shl32
  exact streamFrameM_ite (streamFrameM_pure r _) (streamFrameM_ub r _)

/-- Fixed stream fields are preserved by successful do-while executions. -/
theorem streamFrameM_cdoWhile {σ : Type} {r : ZStreamRef} {body : σ → M σ} {cond : σ → M (Bool × σ)}
    (hb : ∀ state, StreamFrameM r (body state)) (hc : ∀ state, StreamFrameM r (cond state))
    (state : σ) : StreamFrameM r (cdoWhile body cond state) := by
  have key : ∀ n state, StreamFrameM r (cdoWhile.go body cond n state) := by
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
theorem streamFrameM_list_forIn {α β : Type} (r : ZStreamRef) (values : List α)
    (body : (value : α) → value ∈ values → β → M (ForInStep β))
    (frames : ∀ value membership state, StreamFrameM r (body value membership state))
    (initial : β) : StreamFrameM r (List.forIn' values initial body) := by
  induction values generalizing initial with
  | nil =>
    simp only [List.forIn'_eq_forIn', List.forIn'_nil]
    exact streamFrameM_pure r _
  | cons head tail ih =>
    simp only [List.forIn'_eq_forIn', List.forIn'_cons]
    refine streamFrameM_bind (frames head (by simp) initial) (fun decision => ?_)
    cases decision with
    | done result => exact streamFrameM_pure r _
    | yield next =>
      exact ih (fun value membership state => body value (by simp [membership]) state)
        (fun value membership state => frames value (by simp [membership]) state) next

/-- Word/code array views do not overlap the represented stream record. -/
theorem word_view_put_stream (h : Heap) (ref : WRef) (array : Array UInt16) (r : ZStreamRef) :
    r.get (Space.put h ref array) = r.get h := by
  cases ref <;> cases r <;> simp only [Space.put, ZStreamRef.get]
  all_goals first | rfl | (split <;> rfl)

theorem code_view_put_stream (h : Heap) (ref : CodeRef) (array : Array Code) (r : ZStreamRef) :
    r.get (Space.put h ref array) = r.get h := by
  cases ref <;> cases r <;> simp only [Space.put, ZStreamRef.get]
  all_goals first | rfl | (split <;> rfl)

theorem streamFrameM_store16 (r : ZStreamRef) (p : WPtr) (value : UInt16) : StreamFrameM r (p.store value) :=
  streamFrameM_ptr_store r p value (fun h ref array => word_view_put_stream h ref array r)

theorem streamFrameM_storeCode (r : ZStreamRef) (p : CodePtr) (value : Code) : StreamFrameM r (p.store value) :=
  streamFrameM_ptr_store r p value (fun h ref array => code_view_put_stream h ref array r)

theorem streamFrameM_stS (r : ZStreamRef) (pointer : InflateStatePtr) (state : InflateState) :
    StreamFrameM r (stInflateState pointer state) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some pointer =>
    cases pointer with
    | tab zs =>
      rw [stI_eq] at run
      split at run
      · cases run
        simp only [StreamRootFrame, ZStreamRef.get_setI]
      · cases run

/-- Associativity for the concrete C state/fault monad. -/
theorem stream_frame_bind_assoc {α β γ : Type} (first : M α) (next : α → M β) (last : β → M γ) :
    ((first >>= next) >>= last) = (first >>= fun value => next value >>= last) := by
  funext h
  simp only [bind_app]
  cases first h <;> rfl

/-- A literal load/update pair is the actual wrZ operation, even when
followed by more source code. Its old stream value is not generalized away. -/
theorem streamFrameM_ldZ_update {α : Type} (r : ZStreamRef) (update : ZStream → ZStream)
    (next : Unit → M α) (fixed : ∀ z, streamProtected (update z) = streamProtected z)
    (frame : ∀ value, StreamFrameM r (next value)) :
    StreamFrameM r (ldZStream (some r) >>= fun z => stZStream (some r) (update z) >>= next) := by
  rw [← stream_frame_bind_assoc]
  change StreamFrameM r (wrZ (some r) update >>= next)
  exact streamFrameM_bind (streamFrameM_wrZ r update fixed) frame

theorem streamFrameM_castI (r : ZStreamRef) (state : Option StateRef) : StreamFrameM r (castInflateState state) := by
  intro h value after run
  unfold castInflateState at run
  repeat' first | split at run | (cases run <;> rfl)

theorem streamFrameM_strLit (r : ZStreamRef) (message : String) : StreamFrameM r (Zlib.Zutil.strLit message) := by
  intro h value after run
  unfold Zlib.Zutil.strLit strLitRef at run
  repeat' first | split at run | (cases run <;> rfl)

/-- A successful byte memcpy changes only its represented byte view. -/
theorem streamFrameM_memcpyB (r : ZStreamRef) (destination source : BPtr) (count : Nat) :
    StreamFrameM r (memcpyB destination source count) := by
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
        | (cases run <;> simp only [StreamRootFrame, byte_view_put_stream])

/-- Literal messages are a partial update of the same live stream. -/
theorem streamFrameM_setMsg (r : ZStreamRef) (message : String) : StreamFrameM r (setMsg (some r) message) := by
  unfold setMsg
  refine streamFrameM_bind (streamFrameM_strLit r _) (fun pointer => ?_)
  change StreamFrameM r (wrZ (some r) (fun z => { z with msg := pointer }))
  exact streamFrameM_wrZ r _ (fun _ => rfl)

theorem streamFrameM_ldHeader (r : ZStreamRef) (pointer : GzHeaderPtr) : StreamFrameM r (ldGzHeader pointer) := by
  intro h value after run
  unfold ldGzHeader at run
  repeat' first | split at run | (cases run <;> rfl)

theorem streamFrameM_stHeader (r : ZStreamRef) (pointer : GzHeaderPtr) (header : GzHeader) :
    StreamFrameM r (stGzHeader pointer header) := by
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
        simp only [StreamRootFrame, GzHeaderRef.put, get]
        cases r <;> rfl

theorem streamFrameM_shr32 (r : ZStreamRef) (value shift : UInt32) : StreamFrameM r (shr32 value shift) := by
  unfold shr32
  exact streamFrameM_ite (streamFrameM_pure r _) (streamFrameM_ub r _)

theorem streamFrameM_shl64 (r : ZStreamRef) (value : UInt64) (shift : UInt32) : StreamFrameM r (shl64 value shift) := by
  unfold shl64
  exact streamFrameM_ite (streamFrameM_pure r _) (streamFrameM_ub r _)

theorem streamFrameM_shr64 (r : ZStreamRef) (value : UInt64) (shift : UInt32) : StreamFrameM r (shr64 value shift) := by
  unfold shr64
  exact streamFrameM_ite (streamFrameM_pure r _) (streamFrameM_ub r _)

theorem streamFrameM_chkI32 (r : ZStreamRef) (value : Int) : StreamFrameM r (chkI32 value) := by
  unfold chkI32
  exact streamFrameM_ite (streamFrameM_pure r _) (streamFrameM_ub r _)

theorem streamFrameM_chkI64 (r : ZStreamRef) (value : Int) : StreamFrameM r (chkI64 value) := by
  unfold chkI64
  exact streamFrameM_ite (streamFrameM_pure r _) (streamFrameM_ub r _)

theorem streamFrameM_hcrcOn (r : ZStreamRef) (pointer : InflateStatePtr) : StreamFrameM r (hcrcOn pointer) :=
  streamFrameM_bind (streamFrameM_ldS r pointer) (fun _ => streamFrameM_pure r _)

theorem streamFrameM_badMode (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) (message : String) :
    StreamFrameM r (badMode context message) := by
  unfold badMode
  rw [root]
  exact streamFrameM_bind (streamFrameM_setMsg r message) (fun _ => streamFrameM_setMode r _ _)

theorem streamFrameX_xdoWhile {r : ZStreamRef} {body : X Unit} {cond : X Bool}
    (hb : StreamFrameX r body) (hc : StreamFrameX r cond) : StreamFrameX r (xdoWhile body cond) :=
  streamFrameX_bind hb (fun _ => streamFrameX_xwhile hc hb)

theorem streamFrameX_xloopBrk {r : ZStreamRef} {body : X Bool} (frame : StreamFrameX r body) :
    StreamFrameX r (xloopBrk body) := streamFrameX_xwhileBrk (streamFrameX_pure r true) frame

theorem streamFrameM_orderAt (r : ZStreamRef) (index : UInt32) : StreamFrameM r (orderAt index) := by
  unfold orderAt
  split
  · exact streamFrameM_pure r _
  · exact streamFrameM_ub r _

end Zlib.Inflate.Proofs
