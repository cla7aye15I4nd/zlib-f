import ZlibF.Proof.«inflate.c.byte-views»
import ZlibF.Zlib.«inffast.c»

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inflate.Spec Zlib.Inflate.Proofs
set_option autoImplicit false

/-- The fast decoder changes a stream's message on an error. Its other
fields must survive every successful execution of its body. -/
def streamFastFields (z : ZStream) : ZStream := { z with msg := .null }

def StreamFastFrame (r : ZStreamRef) (before after : Heap) : Prop :=
  (r.get after).map streamFastFields = (r.get before).map streamFastFields

def StreamFastFrameM {α : Type} (r : ZStreamRef) (program : M α) : Prop :=
  ∀ h value after, program h = .ok (value, after) → StreamFastFrame r h after

theorem StreamFastFrame.refl (r : ZStreamRef) (h : Heap) :
    StreamFastFrame r h h := rfl

theorem StreamFastFrame.trans {r : ZStreamRef} {a b c : Heap}
    (first : StreamFastFrame r a b) (second : StreamFastFrame r b c) :
    StreamFastFrame r a c := Eq.trans second first

theorem streamFastFrameM_pure {α : Type} (r : ZStreamRef) (value : α) :
    StreamFastFrameM r (pure value) := by
  intro h result after run
  cases run
  rfl

theorem streamFastFrameM_bind {α β : Type} {r : ZStreamRef}
    {first : M α} {next : α → M β}
    (hf : StreamFastFrameM r first)
    (hn : ∀ value, StreamFastFrameM r (next value)) :
    StreamFastFrameM r (first >>= next) := by
  intro h result after run
  rw [bind_app] at run
  cases firstRun : first h with
  | error fault => rw [firstRun] at run; cases run
  | ok pair =>
    obtain ⟨value, middle⟩ := pair
    rw [firstRun] at run
    exact (hf h value middle firstRun).trans (hn value middle result after run)

theorem streamFastFrameM_read {α : Type} {r : ZStreamRef} {program : M α}
    (same : ∀ h value after, program h = .ok (value, after) → after = h) :
    StreamFastFrameM r program := by
  intro h value after run
  rw [same h value after run]
  rfl

theorem streamFastFrameM_cdoWhile {σ : Type} {r : ZStreamRef}
    {body : σ → M σ} {cond : σ → M (Bool × σ)}
    (hb : ∀ state, StreamFastFrameM r (body state))
    (hc : ∀ state, StreamFastFrameM r (cond state))
    (state : σ) : StreamFastFrameM r (cdoWhile body cond state) := by
  have key : ∀ n state, StreamFastFrameM r (cdoWhile.go body cond n state) := by
    intro n
    induction n with
    | zero =>
      intro state h value after run
      cases run
    | succ n ih =>
      intro state h value after run
      simp only [cdoWhile.go, bind_app] at run
      cases bodyRun : body state h with
      | error fault => simp only [bodyRun] at run; cases run
      | ok pair =>
        obtain ⟨middle, heap1⟩ := pair
        simp only [bodyRun] at run
        have first := hb state h middle heap1 bodyRun
        cases condRun : cond middle heap1 with
        | error fault => simp only [condRun] at run; cases run
        | ok pair =>
          obtain ⟨⟨test, next⟩, heap2⟩ := pair
          simp only [condRun] at run
          have second := hc middle heap1 (test, next) heap2 condRun
          cases test with
          | false =>
            simp only [Bool.false_eq_true, ite_false, pure_app] at run
            cases run
            exact first.trans second
          | true =>
            simp only [ite_true] at run
            exact first.trans (second.trans (ih next heap2 value after run))
  exact key fuel state

theorem streamFastFrameM_cwhile {σ : Type} {r : ZStreamRef}
    {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (hc : ∀ state, StreamFastFrameM r (cond state))
    (hb : ∀ state, StreamFastFrameM r (body state))
    (state : σ) : StreamFastFrameM r (cwhile cond body state) := by
  have key : ∀ n state, StreamFastFrameM r (cwhile.go cond body n state) := by
    intro n
    induction n with
    | zero =>
      intro state h value after run
      cases run
    | succ n ih =>
      intro state h value after run
      simp only [cwhile.go, bind_app] at run
      cases condRun : cond state h with
      | error fault => simp only [condRun] at run; cases run
      | ok pair =>
        obtain ⟨⟨test, middle⟩, heap1⟩ := pair
        simp only [condRun] at run
        have first := hc state h (test, middle) heap1 condRun
        cases test with
        | false =>
          simp only [Bool.false_eq_true, ite_false, pure_app] at run
          cases run
          exact first
        | true =>
          simp only [ite_true, bind_app] at run
          cases bodyRun : body middle heap1 with
          | error fault => simp only [bodyRun] at run; cases run
          | ok pair =>
            obtain ⟨next, heap2⟩ := pair
            simp only [bodyRun] at run
            exact first.trans ((hb middle heap1 next heap2 bodyRun).trans
              (ih next heap2 value after run))
  exact key fuel state

theorem streamFastFrameM_ite {α : Type} {r : ZStreamRef}
    {test : Prop} [Decidable test] {yes no : M α}
    (hy : StreamFastFrameM r yes) (hn : StreamFastFrameM r no) :
    StreamFastFrameM r (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ite_true] using hy
  · simpa only [selected, ite_false] using hn

theorem streamFastFrameM_ptr_add {R T : Type} [Space Heap R T]
    (r : ZStreamRef) (p : Ptr R) (n : Int) :
    StreamFastFrameM r (p.add n) := by
  apply streamFastFrameM_read
  intro h value after run
  unfold Ptr.add at run
  repeat' (split at run <;> try cases run)
  all_goals rfl

theorem streamFastFrameM_ptr_load {R T : Type} [Space Heap R T]
    (r : ZStreamRef) (p : Ptr R) :
    StreamFastFrameM r (p.load : M T) := by
  apply streamFastFrameM_read
  intro h value after run
  unfold Ptr.load at run
  repeat' (split at run <;> try cases run)
  all_goals rfl

theorem streamFastFrameM_ptr_diff {R T : Type}
    [DecidableEq R] [Space Heap R T]
    (r : ZStreamRef) (p q : Ptr R) :
    StreamFastFrameM r (p.diff q) := by
  apply streamFastFrameM_read
  intro h value after run
  unfold Ptr.diff at run
  repeat' (split at run <;> try cases run)
  all_goals rfl

theorem streamFastFrameM_ptr_lt {R T : Type}
    [DecidableEq R] [Space Heap R T]
    (r : ZStreamRef) (p q : Ptr R) :
    StreamFastFrameM r (p.lt q) := by
  apply streamFastFrameM_read
  intro h value after run
  unfold Ptr.lt at run
  repeat' (split at run <;> try cases run)
  all_goals rfl

theorem streamFastFrameM_store8 (r : ZStreamRef)
    (p : BPtr) (byte : UInt8) :
    StreamFastFrameM r (store8 p byte) := by
  intro h value after run
  unfold store8 Ptr.store at run
  repeat' (split at run <;> try cases run)
  all_goals
    simp only [StreamFastFrame]
    rw [Space.modify_eq _ _ _ _ (by assumption)]
    rw [Zlib.Inflate.Proofs.byte_view_put_stream]

theorem streamFastFrameM_shl32 (r : ZStreamRef) (x n : UInt32) :
    StreamFastFrameM r (shl32 x n) := by
  apply streamFastFrameM_read
  intro h value after run
  unfold shl32 at run
  split at run <;> cases run
  rfl

theorem streamFastFrameM_shl64 (r : ZStreamRef) (x n : UInt64) :
    StreamFastFrameM r (shl64 x n) := by
  apply streamFastFrameM_read
  intro h value after run
  unfold shl64 at run
  split at run <;> cases run
  rfl

theorem streamFastFrameM_shr64 (r : ZStreamRef) (x n : UInt64) :
    StreamFastFrameM r (shr64 x n) := by
  apply streamFastFrameM_read
  intro h value after run
  unfold shr64 at run
  split at run <;> cases run
  rfl

theorem streamFastFrameM_strLit (r : ZStreamRef) (message : String) :
    StreamFastFrameM r (Zlib.Zutil.strLit message) := by
  apply streamFastFrameM_read
  intro h value after run
  unfold Zlib.Zutil.strLit strLitRef at run
  split at run <;> cases run
  rfl

theorem streamFastFrameM_chk64 (r : ZStreamRef) (value : Int) :
    StreamFastFrameM r (chk64 value) := by
  apply streamFastFrameM_read
  intro h result after run
  unfold chk64 at run
  split at run <;> cases run
  rfl

theorem streamFastFrameM_ldInflateState (r : ZStreamRef)
    (state : InflateStatePtr) :
    StreamFastFrameM r (ldInflateState state) := by
  apply streamFastFrameM_read
  intro h result after run
  unfold ldInflateState at run
  repeat' (split at run <;> try cases run)
  all_goals rfl

theorem streamFastFrameM_stInflateState (r : ZStreamRef)
    (zs : Nat) (state : InflateState) :
    StreamFastFrameM r (stInflateState (some (.tab zs)) state) := by
  intro h value after run
  cases get : h.istates zs with
  | none => simp [stInflateState, InflateStateRef.get, get] at run
  | some old =>
    have write := stInflateState_tab (v' := state) get
    rw [write] at run
    cases run
    change (r.get (setI h zs state)).map streamFastFields =
      (r.get h).map streamFastFields
    rw [ZStreamRef.get_setI]

theorem streamFastFrameM_badData {r : ZStreamRef} {zs : Nat}
    (c : Ctx) (message : String)
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs)) :
    StreamFastFrameM r (badData c message) := by
  intro h value after run
  unfold badData at run
  rw [streamPtr, statePtr] at run
  cases literal : Zlib.Zutil.strLit message h with
  | error fault => simp [bind_app, literal] at run
  | ok pair =>
    obtain ⟨pointer, litHeap⟩ := pair
    have litSame : litHeap = h := by
      have source := literal
      unfold Zlib.Zutil.strLit strLitRef at source
      split at source <;> cases source <;> rfl
    subst litHeap
    cases streamGet : r.get h with
    | none =>
      simp [bind_app, literal, ldZStream, streamGet] at run
    | some z =>
      have load := ldZStream_ok streamGet
      have write := stZStream_ok streamGet (by cases r <;> rfl)
        (v' := { z with msg := pointer })
      let updated : ZStream := { z with msg := pointer }
      let middle := r.put h updated
      cases stateGet : middle.istates zs with
      | none =>
        have stateGet' : (r.put h updated).istates zs = none := by
          simpa only [middle] using stateGet
        have stateGetH : h.istates zs = none := by
          simpa only [ZStreamRef.put_istates] using stateGet'
        simp [bind_app, literal, load, write, ldInflateState,
          InflateStateRef.get, stateGetH] at run
      | some s =>
        have stateGet' : (r.put h updated).istates zs = some s := by
          simpa only [middle] using stateGet
        have stateGetH : h.istates zs = some s := by
          simpa only [ZStreamRef.put_istates] using stateGet'
        simp [bind_app, literal, load, write, ldInflateState,
          stInflateState, InflateStateRef.get, ZStreamRef.put_istates,
          stateGetH] at run
        cases run
        rw [InflateStateRef.put_tab stateGet']
        change (r.get (setI (r.put h updated) zs { s with mode := BAD })).map
          streamFastFields = (r.get h).map streamFastFields
        rw [ZStreamRef.get_setI, ZStreamRef.get_put_same streamGet,
          streamGet]
        rfl

theorem streamFastFrameM_pull (r : ZStreamRef) (l : L) :
    StreamFastFrameM r (pull l) := by
  unfold pull
  apply streamFastFrameM_bind (streamFastFrameM_ptr_load r l.in_)
  intro byte
  apply streamFastFrameM_bind (streamFastFrameM_ptr_add r l.in_ 1)
  intro in_
  apply streamFastFrameM_bind (streamFastFrameM_shl64 r byte.toUInt64 l.bits.toUInt64)
  intro shift
  exact streamFastFrameM_pure r _

theorem streamFastFrameM_copy1 (r : ZStreamRef) (l : L) :
    StreamFastFrameM r (copy1 l) := by
  unfold copy1
  apply streamFastFrameM_bind (streamFastFrameM_ptr_load r l.from_)
  intro byte
  apply streamFastFrameM_bind (streamFastFrameM_ptr_add r l.from_ 1)
  intro from_
  apply streamFastFrameM_bind (streamFastFrameM_store8 r l.out byte)
  intro _
  apply streamFastFrameM_bind (streamFastFrameM_ptr_add r l.out 1)
  intro out
  exact streamFastFrameM_pure r _

theorem streamFastFrameM_copyOp (r : ZStreamRef) (l : L) :
    StreamFastFrameM r (copyOp l) := by
  unfold copyOp
  apply streamFastFrameM_cdoWhile
  · intro state
    exact streamFastFrameM_copy1 r state
  · intro state
    exact streamFastFrameM_pure r _

theorem streamFastFrameM_copyMatch (r : ZStreamRef) (zs : Nat) (c : Ctx) (l : L)
    (streamPtr : c.strm = some r) (statePtr : c.state = some (.tab zs)) :
    StreamFastFrameM r (copyMatch c l) := by
  unfold copyMatch
  repeat'
    first
    | exact streamFastFrameM_pure r _
    | (apply streamFastFrameM_bind (r := r)
          (first := badData c "invalid distance too far back");
       · exact streamFastFrameM_badData c _ streamPtr statePtr
       · intro; exact streamFastFrameM_pure r _)
    | (change StreamFastFrameM r (badData c "invalid distance too far back");
       exact streamFastFrameM_badData c _ streamPtr statePtr)
    | exact streamFastFrameM_badData c _ streamPtr statePtr
    | exact streamFastFrameM_ldInflateState r c.state
    | exact streamFastFrameM_copy1 r _
    | exact streamFastFrameM_copyOp r _
    | exact streamFastFrameM_ptr_add r _ _
    | exact streamFastFrameM_ptr_diff r _ _
    | refine streamFastFrameM_cwhile (r := r) (fun state => ?_) (fun state => ?_) _
    | refine streamFastFrameM_cdoWhile (r := r) (fun state => ?_) (fun state => ?_) _
    | apply streamFastFrameM_ite (r := r)
    | refine streamFastFrameM_bind (r := r) ?_ (fun value => ?_)

theorem streamFastFrameM_dodist (r : ZStreamRef) (zs : Nat) (c : Ctx) (l : L)
    (streamPtr : c.strm = some r) (statePtr : c.state = some (.tab zs)) :
    StreamFastFrameM r (dodist c l) := by
  unfold dodist
  repeat'
    first
    | exact streamFastFrameM_pure r _
    | (apply streamFastFrameM_bind (r := r)
          (first := badData c "invalid distance code");
       · exact streamFastFrameM_badData c _ streamPtr statePtr
       · intro; exact streamFastFrameM_pure r _)
    | exact streamFastFrameM_badData c _ streamPtr statePtr
    | exact streamFastFrameM_copyMatch r zs c _ streamPtr statePtr
    | exact streamFastFrameM_pull r _
    | exact streamFastFrameM_ptr_load r _
    | exact streamFastFrameM_ptr_add r _ _
    | exact streamFastFrameM_ptr_diff r _ _
    | exact streamFastFrameM_shl32 r _ _
    | exact streamFastFrameM_shr64 r _ _
    | apply streamFastFrameM_ite (r := r)
    | refine streamFastFrameM_bind (r := r) ?_ (fun value => ?_)

theorem streamFastFrameM_dolen (r : ZStreamRef) (zs : Nat) (c : Ctx) (l : L)
    (streamPtr : c.strm = some r) (statePtr : c.state = some (.tab zs)) :
    StreamFastFrameM r (dolen c l) := by
  unfold dolen
  repeat'
    first
    | exact streamFastFrameM_pure r _
    | (apply streamFastFrameM_bind (r := r)
          (first := badData c "invalid literal/length code");
       · exact streamFastFrameM_badData c _ streamPtr statePtr
       · intro; exact streamFastFrameM_pure r _)
    | exact streamFastFrameM_badData c _ streamPtr statePtr
    | exact streamFastFrameM_dodist r zs c _ streamPtr statePtr
    | exact streamFastFrameM_pull r _
    | exact streamFastFrameM_ptr_load r _
    | exact streamFastFrameM_ptr_add r _ _
    | exact streamFastFrameM_shl32 r _ _
    | exact streamFastFrameM_shr64 r _ _
    | exact streamFastFrameM_ldInflateState r c.state
    | (simpa only [statePtr] using streamFastFrameM_stInflateState r zs _)
    | exact streamFastFrameM_store8 r _ _
    | refine streamFastFrameM_cdoWhile (r := r) (fun state => ?_) (fun state => ?_) _
    | apply streamFastFrameM_ite (r := r)
    | refine streamFastFrameM_bind (r := r) ?_ (fun value => ?_)

theorem streamFastFrameM_body (r : ZStreamRef) (zs : Nat) (c : Ctx) (l : L)
    (streamPtr : c.strm = some r) (statePtr : c.state = some (.tab zs)) :
    StreamFastFrameM r (inflate_fast_body c l) := by
  unfold inflate_fast_body
  repeat'
    first
    | exact streamFastFrameM_pure r _
    | exact streamFastFrameM_dolen r zs c _ streamPtr statePtr
    | exact streamFastFrameM_pull r _
    | exact streamFastFrameM_ptr_add r _ _
    | refine streamFastFrameM_cdoWhile (r := r) (fun state => ?_) (fun state => ?_) _
    | apply streamFastFrameM_ite (r := r)
    | refine streamFastFrameM_bind (r := r) ?_ (fun value => ?_)

#print axioms streamFastFrameM_body

end Zlib.Inffast.Proofs
