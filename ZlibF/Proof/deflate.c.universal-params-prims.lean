import ZlibF.Proof.«deflate.c.universal-params-base»
import ZlibF.Zlib.«deflate.c»

/-!
# deflate.c: the parameter frame for the primitive operations

Batch C of the deflate skeleton. Every store primitive changes at most an array of a record
(`ExactM`); loads change nothing; a record update `wr s f` keeps the parameters in the sense of
`ParRel` when `f` does (`par_wr`).
-/

namespace Zlib.Deflate.Universal.Params
open C Zlib.Deflate Zlib.Deflate.Spec
set_option autoImplicit false

/-! ## Array stores -/

theorem exact_modify_B (h : Heap) (r : BRef) (f : Array UInt8 → Array UInt8) :
    ExactRel h (Space.modify h r f) := by
  cases r with
  | blk b => exact ExactRel.quiet rfl rfl rfl
  | str i => exact ExactRel.refl h
  | dstate_depth id => exact ExactRel.dstate_array id _ (fun _ => rfl)
  | st_dist_code => exact ExactRel.refl h
  | st_length_code => exact ExactRel.refl h

theorem exact_modify_W (h : Heap) (r : WRef) (f : Array UInt16 → Array UInt16) :
    ExactRel h (Space.modify h r f) := by
  cases r with
  | blk b => exact ExactRel.quiet rfl rfl rfl
  | dstate_bl_count id => exact ExactRel.dstate_array id _ (fun _ => rfl)
  | istate_lens id => exact ExactRel.quiet rfl rfl rfl
  | istate_work id => exact ExactRel.quiet rfl rfl rfl

theorem exact_modify_I (h : Heap) (r : IRef) (f : Array Int32 → Array Int32) :
    ExactRel h (Space.modify h r f) := by
  cases r with
  | dstate_heap id => exact ExactRel.dstate_array id _ (fun _ => rfl)
  | _ => exact ExactRel.refl h

theorem exact_modify_Ct (h : Heap) (r : CtDataRef) (f : Array CtData → Array CtData) :
    ExactRel h (Space.modify h r f) := by
  cases r with
  | dstate_dyn_ltree id => exact ExactRel.dstate_array id _ (fun _ => rfl)
  | dstate_dyn_dtree id => exact ExactRel.dstate_array id _ (fun _ => rfl)
  | dstate_bl_tree id => exact ExactRel.dstate_array id _ (fun _ => rfl)
  | _ => exact ExactRel.refl h

/-- A type of arrays whose in-place changes keep every parameter. -/
class ExactSpace (R : Type) (T : Type) [Space Heap R T] : Prop where
  modify : ∀ (h : Heap) (r : R) (f : Array T → Array T), ExactRel h (Space.modify h r f)

instance : ExactSpace BRef UInt8 := ⟨exact_modify_B⟩
instance : ExactSpace WRef UInt16 := ⟨exact_modify_W⟩
instance : ExactSpace IRef Int32 := ⟨exact_modify_I⟩
instance : ExactSpace CtDataRef CtData := ⟨exact_modify_Ct⟩

theorem exact_ptr_add {R T : Type} [Space Heap R T] (p : Ptr R) (k : Int) : ExactM (p.add k) := by
  intro h value after run
  unfold Ptr.add at run
  repeat' first | split at run | (cases run; exact ExactRel.refl h) | contradiction

theorem exact_ptr_load {R T : Type} [Space Heap R T] (p : Ptr R) : ExactM (Ptr.load p : M T) := by
  intro h value after run
  unfold Ptr.load at run
  repeat' first | split at run | (cases run; exact ExactRel.refl h) | contradiction

theorem exact_ptr_index {R T : Type} [Space Heap R T] (p : Ptr R) (k : Int) : ExactM (Ptr.index p k : M T) := by
  unfold Ptr.index
  exact ExactM.bind (exact_ptr_add _ _) (fun _ => exact_ptr_load _)

theorem exact_ptr_store {R T : Type} [Space Heap R T] [ExactSpace R T] (p : Ptr R) (v : T) :
    ExactM (Ptr.store p v) := by
  intro h value after run
  unfold Ptr.store at run
  repeat' first | split at run | (cases run; exact ExactSpace.modify h _ _) | contradiction

theorem exact_ptr_memcpy {R T : Type} [Space Heap R T] [ExactSpace R T] [DecidableEq R] [Inhabited T]
    (dst src : Ptr R) (n : Nat) : ExactM (Ptr.memcpy dst src n) := by
  intro h value after run
  unfold Ptr.memcpy at run
  repeat' first | split at run | (cases run; exact ExactSpace.modify h _ _) | contradiction

theorem exact_ptr_fill {R T : Type} [Space Heap R T] [ExactSpace R T] (dst : Ptr R) (v : T) (n : Nat) :
    ExactM (Ptr.fill dst v n) := by
  intro h value after run
  unfold Ptr.fill at run
  repeat' first | split at run | (cases run; exact ExactSpace.modify h _ _) | contradiction

theorem exact_ptr_diff {R T : Type} [Space Heap R T] [DecidableEq R] (p q : Ptr R) :
    ExactM (Ptr.diff (T := T) p q) := by
  intro h value after run
  unfold Ptr.diff at run
  repeat' first | split at run | (cases run; exact ExactRel.refl h) | contradiction

theorem exact_ptr_lt {R T : Type} [Space Heap R T] [DecidableEq R] (p q : Ptr R) :
    ExactM (Ptr.lt (T := T) p q) := by
  intro h value after run
  unfold Ptr.lt at run
  repeat' first | split at run | (cases run; exact ExactRel.refl h) | contradiction

/-! ## Records -/

theorem exact_ldDeflateState (p : DeflateStatePtr) : ExactM (ldDeflateState p) := by
  intro h value after run
  unfold ldDeflateState at run
  repeat' first | split at run | (cases run; exact ExactRel.refl h) | contradiction

theorem exact_ldZStream (p : ZStreamPtr) : ExactM (ldZStream p) := by
  intro h value after run
  unfold ldZStream at run
  repeat' first | split at run | (cases run; exact ExactRel.refl h) | contradiction

theorem exact_ldGzHeader (p : GzHeaderPtr) : ExactM (ldGzHeader p) := by
  intro h value after run
  unfold ldGzHeader at run
  repeat' first | split at run | (cases run; exact ExactRel.refl h) | contradiction

theorem exact_castDeflateState (p : Option StateRef) : ExactM (castDeflateState p) := by
  intro h value after run
  unfold castDeflateState at run
  repeat' first | split at run | (cases run; exact ExactRel.refl h) | contradiction

theorem exact_strLitRef (s : String) : ExactM (strLitRef s) := by
  intro h value after run
  unfold strLitRef at run
  repeat' first | split at run | (cases run; exact ExactRel.refl h) | contradiction

/-- Writing a stream record whose `state` and allocators are those of the current record. -/
theorem exact_put_stream {h : Heap} {r : ZStreamRef} {z : ZStream} (get : r.get h = some z) (z' : ZStream)
    (same : ZSame z z') : ExactRel h (r.put h z') := by
  refine ⟨fun ds d got => ⟨d, ?_, rfl⟩, fun q y got => ?_⟩
  · cases r <;> simp only [ZStreamRef.put] <;> split <;> exact got
  · by_cases eq : q = r
    · subst eq
      have zEq : y = z := Option.some.inj (got.symm.trans get)
      rw [zEq]
      exact ⟨z', Zlib.Deflate.Proofs.ZStreamRef.get_put_same get z', same⟩
    · refine ⟨y, ?_, ZSame.refl y⟩
      cases r with
      | tab i =>
        cases q with
        | tab j =>
          have ne : j ≠ i := fun e => eq (by rw [e])
          simp only [ZStreamRef.put] at got ⊢
          split <;> simp_all [ZStreamRef.get, upd_ne _ _ _ _ ne]
        | in_gzstate_strm j =>
          simp only [ZStreamRef.put]
          split <;> simpa only [ZStreamRef.get] using got
      | in_gzstate_strm i =>
        cases q with
        | tab j =>
          simp only [ZStreamRef.put]
          split <;> simpa only [ZStreamRef.get] using got
        | in_gzstate_strm j =>
          have ne : j ≠ i := fun e => eq (by rw [e])
          simp only [ZStreamRef.put] at got ⊢
          split <;> simp_all [ZStreamRef.get, upd_ne _ _ _ _ ne]

/-- `strm->f = ...`, when `f` keeps `state` and the allocators. -/
theorem exact_zwr (p : ZStreamPtr) (f : ZStream → ZStream) (hf : ∀ z, ZSame z (f z)) : ExactM (zwr p f) := by
  intro h value after run
  unfold zwr at run
  rw [bind_app] at run
  cases p with
  | none => cases run
  | some r =>
    cases get : r.get h with
    | none => simp [ldZStream, get] at run
    | some z =>
      simp only [ldZStream, get, stZStream] at run
      split at run
      · cases run
      · cases run
        exact exact_put_stream get (f z) (hf z)

/-- `s->f = ...`, when `f` keeps the parameters in the sense of `Same keep`. -/
theorem par_wr (keep : Bool) (p : DeflateStatePtr) (f : DeflateState → DeflateState)
    (hf : ∀ d, Same keep d (f d)) : ParM keep (wr p f) := by
  intro h value after run
  unfold wr at run
  rw [bind_app] at run
  cases p with
  | none => cases run
  | some r =>
    cases r with
    | tab i =>
      cases get : h.dstates i with
      | none => simp [ldDeflateState, DeflateStateRef.get, get] at run
      | some d =>
        simp only [ldDeflateState, DeflateStateRef.get, get, stDeflateState, DeflateStateRef.isRo] at run
        cases run
        rw [DeflateStateRef.put_tab get]
        refine ⟨fun ds e got => ?_, fun q z got => ⟨z, ?_, ZSame.refl z⟩⟩
        · by_cases same : ds = i
          · subst same
            have eq : e = d := Option.some.inj (got.symm.trans get)
            rw [eq]
            exact ⟨f d, by simp, hf d⟩
          · exact ⟨e, by simpa [upd_ne _ _ _ _ same] using got, Same.refl keep e⟩
        · cases q <;> simpa only [ZStreamRef.get] using got

end Zlib.Deflate.Universal.Params

namespace Zlib.Deflate.Universal.Params
open C Zlib.Deflate Zlib.Deflate.Spec

/-- A store of a record built from an earlier load of the same record, when everything between
the load and the store keeps the parameters exactly and the new record has the loaded
parameters. -/
theorem exact_ld_st {β γ : Type} (p : DeflateStatePtr) (q : DeflateState → M β)
    (g : DeflateState → β → DeflateState) (k : DeflateState → β → M γ)
    (hq : ∀ d, ExactM (q d)) (hg : ∀ d x, Pars (g d x) = Pars d) (hk : ∀ d x, ExactM (k d x)) :
    ExactM (do
      let d ← ldDeflateState p
      let x ← q d
      stDeflateState p (g d x)
      k d x) := by
  intro h value after run
  simp only [bind_app] at run
  cases p with
  | none => cases run
  | some r =>
    cases r with
    | tab i =>
      cases get : h.dstates i with
      | none => simp [ldDeflateState, DeflateStateRef.get, get] at run
      | some d =>
        simp only [ldDeflateState, DeflateStateRef.get, get] at run
        cases eq1 : q d h with
        | error _ => simp [eq1] at run
        | ok p1 =>
          rcases p1 with ⟨x, h1⟩
          simp only [eq1] at run
          have rel1 := hq d h x h1 eq1
          obtain ⟨d1, get1, pars1⟩ := rel1.1 i d get
          simp only [stDeflateState, DeflateStateRef.get, get1, DeflateStateRef.isRo] at run
          rw [DeflateStateRef.put_tab get1] at run
          have rel2 : ExactRel h1 { h1 with dstates := upd h1.dstates i (some (g d x)) } := by
            refine ⟨fun ds e got => ?_, fun q z got => ⟨z, ?_, ZSame.refl z⟩⟩
            · by_cases same : ds = i
              · subst same
                have eq : e = d1 := Option.some.inj (got.symm.trans get1)
                rw [eq]
                exact ⟨g d x, by simp, (hg d x).trans pars1.symm⟩
              · exact ⟨e, by simpa [upd_ne _ _ _ _ same] using got, rfl⟩
            · cases q <;> simpa only [ZStreamRef.get] using got
          exact rel1.trans (rel2.trans (hk d x _ value after run))

/-- `strm->... = ...` as a store of a stream record built from an earlier load of the same
record, when everything between keeps the stream's `state` and allocators. -/
theorem exact_ldz_st {β γ : Type} (p : ZStreamPtr) (q : ZStream → M β)
    (g : ZStream → β → ZStream) (k : ZStream → β → M γ)
    (hq : ∀ z, ExactM (q z)) (hg : ∀ z x, ZSame z (g z x)) (hk : ∀ z x, ExactM (k z x)) :
    ExactM (do
      let z ← ldZStream p
      let x ← q z
      stZStream p (g z x)
      k z x) := by
  intro h value after run
  simp only [bind_app] at run
  cases p with
  | none => cases run
  | some r =>
    cases get : r.get h with
    | none => simp [ldZStream, get] at run
    | some z =>
      simp only [ldZStream, get] at run
      cases eq1 : q z h with
      | error _ => simp [eq1] at run
      | ok p1 =>
        rcases p1 with ⟨x, h1⟩
        simp only [eq1] at run
        have rel1 := hq z h x h1 eq1
        obtain ⟨z1, get1, same1⟩ := rel1.2 r z get
        have hsame : ZSame z1 (g z x) := by
          have := hg z x
          exact ⟨this.state.trans same1.state.symm, this.zalloc.trans same1.zalloc.symm,
            this.zfree.trans same1.zfree.symm⟩
        have ro : r.isRo = false := by cases r <;> rfl
        simp only [stZStream, get1, ro, Bool.false_eq_true, ite_false] at run
        exact rel1.trans ((exact_put_stream get1 (g z x) hsame).trans (hk z x _ value after run))

end Zlib.Deflate.Universal.Params

namespace Zlib.Deflate.Universal.Params
open C

theorem exact_load8 (p : BPtr) : ExactM (load8 p) := exact_ptr_load p
theorem exact_index8 (p : BPtr) (i : Int) : ExactM (index8 p i) := exact_ptr_index p i
theorem exact_store8 (p : BPtr) (v : UInt8) : ExactM (store8 p v) := exact_ptr_store p v
theorem exact_memcpyB (dst src : BPtr) (n : Nat) : ExactM (memcpyB dst src n) := exact_ptr_memcpy dst src n
theorem exact_memsetB (dst : BPtr) (v : UInt8) (n : Nat) : ExactM (memsetB dst v n) := exact_ptr_fill dst v n

end Zlib.Deflate.Universal.Params
