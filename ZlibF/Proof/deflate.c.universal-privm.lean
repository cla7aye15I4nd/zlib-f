import ZlibF.Proof.«deflate.c.universal-outframe»
import ZlibF.Proof.«deflate.c.engine.slow-source»

/-!
# deflate.c: runs that change only the stream's own state and hash arrays (batch B)

`PrivM r ds d0 m`: every returning run of `m` from a heap whose state record `ds` has the keys of
`d0` is a private step (`PrivStep`: the stream root and the stream's own blocks change, the heap
shape is kept) and leaves a state record with the same keys. The rules are compositional, one per
primitive, with no callee contract. They give the private steps of the insertion loop of
`deflate_slow` (`slowMatchAdvance`), whose step lemmas do not name their heaps.
-/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Engine.Proofs
open Zlib.Deflate.Proofs
set_option autoImplicit false

/-- A run that changes only the stream root and the stream's own blocks, keeping the keys. -/
def PrivM {α : Type} (r : ZStreamRef) (ds : Nat) (d0 : DeflateState) (m : M α) : Prop :=
  ∀ h a h', (∃ e, h.dstates ds = some e ∧ Keys d0 e) → m h = .ok (a, h') →
    PrivStep h h' r ds d0 ∧ ∃ e', h'.dstates ds = some e' ∧ Keys d0 e'

/-- A run that does not change the heap. -/
def ReadM {α : Type} (m : M α) : Prop := ∀ h a h', m h = .ok (a, h') → h' = h

theorem ReadM.pure {α : Type} (a : α) : ReadM (Pure.pure a : M α) := by
  intro h v h' run; cases run; rfl

theorem ReadM.bind {α β : Type} {m : M α} {f : α → M β} (hm : ReadM m) (hf : ∀ a, ReadM (f a)) :
    ReadM (m >>= f) := by
  intro h value after run
  rw [bind_app] at run
  cases e : m h with
  | error _ => rw [e] at run; cases run
  | ok p =>
    rcases p with ⟨a, h1⟩
    rw [e] at run
    exact (hf a h1 value after run).trans (hm h a h1 e)

theorem ReadM.ptr_add {R T : Type} [Space Heap R T] (p : Ptr R) (k : Int) : ReadM (Ptr.add p k : M (Ptr R)) := by
  intro h q h' run
  cases p with
  | null =>
    simp only [Ptr.add] at run
    split at run
    · cases run; rfl
    · cases run
  | ref r off =>
    simp only [Ptr.add] at run
    split at run
    · cases run
    · split at run
      · cases run; rfl
      · cases run

theorem ReadM.ptr_load {R T : Type} [Space Heap R T] (p : Ptr R) : ReadM (Ptr.load p : M T) := by
  intro h v h' run
  cases p with
  | null => simp only [Ptr.load] at run; cases run
  | ref r off =>
    simp only [Ptr.load] at run
    split at run
    · cases run
    · split at run
      · cases run; rfl
      · cases run

theorem ReadM.ptr_index {R T : Type} [Space Heap R T] (p : Ptr R) (i : Int) : ReadM (Ptr.index p i : M T) :=
  ReadM.bind (ReadM.ptr_add p i) (fun q => ReadM.ptr_load q)

theorem ReadM.ushl (a n : UInt32) : ReadM (Zlib.Deflate.ushl a n) := by
  intro h v h' run
  unfold Zlib.Deflate.ushl at run
  split at run
  · cases run; rfl
  · cases run

theorem PrivM.of_read {α : Type} {r : ZStreamRef} {ds : Nat} {d0 : DeflateState} {m : M α} (hm : ReadM m) :
    PrivM r ds d0 m := by
  intro h a h' pre run
  have e := hm h a h' run
  subst e
  exact ⟨PrivStep.refl _ r ds d0, pre⟩

theorem PrivM.pure {α : Type} {r : ZStreamRef} {ds : Nat} {d0 : DeflateState} (a : α) :
    PrivM r ds d0 (Pure.pure a : M α) := PrivM.of_read (ReadM.pure a)

theorem PrivM.bind {α β : Type} {r : ZStreamRef} {ds : Nat} {d0 : DeflateState} {m : M α} {f : α → M β}
    (hm : PrivM r ds d0 m) (hf : ∀ a, PrivM r ds d0 (f a)) : PrivM r ds d0 (m >>= f) := by
  intro h value after pre run
  rw [bind_app] at run
  cases e : m h with
  | error _ => rw [e] at run; cases run
  | ok p =>
    rcases p with ⟨a, h1⟩
    rw [e] at run
    obtain ⟨s1, post1⟩ := hm h a h1 pre e
    obtain ⟨s2, post2⟩ := hf a h1 value after post1 run
    exact ⟨s1.trans s2, post2⟩

theorem PrivM.ite {α : Type} {r : ZStreamRef} {ds : Nat} {d0 : DeflateState} (p : Prop) [Decidable p]
    {a b : M α} (ha : PrivM r ds d0 a) (hb : PrivM r ds d0 b) : PrivM r ds d0 (if p then a else b) := by
  split <;> assumption

/-- A load of the state record, with the keys of the loaded record. -/
theorem PrivM.ld_bind {β : Type} {r : ZStreamRef} {ds : Nat} {d0 : DeflateState} {k : DeflateState → M β}
    (hk : ∀ e, Keys d0 e → PrivM r ds d0 (k e)) : PrivM r ds d0 (ldDeflateState (some (.tab ds)) >>= k) := by
  intro h a h' ⟨e, get, keys⟩ run
  rw [bind_app, ldDeflateState_tab get] at run
  exact hk e keys h a h' ⟨e, get, keys⟩ run

theorem PrivM.rd {α : Type} {r : ZStreamRef} {ds : Nat} {d0 : DeflateState} (f : DeflateState → α) :
    PrivM r ds d0 (rd (some (.tab ds)) f) :=
  PrivM.ld_bind (fun _ _ => PrivM.pure _)

theorem PrivM.st {r : ZStreamRef} {ds : Nat} {d0 : DeflateState} (v : DeflateState) (keys : Keys d0 v) :
    PrivM r ds d0 (stDeflateState (some (.tab ds)) v) := by
  intro h a h' ⟨e, get, _⟩ run
  rw [stD_eq, get] at run
  have eq := (Prod.mk.inj (Except.ok.inj run)).2
  subst eq
  exact ⟨priv_setD h r ds d0 v get, v, setD_dstates_same h ds v, keys⟩

theorem PrivM.wr {r : ZStreamRef} {ds : Nat} {d0 : DeflateState} (f : DeflateState → DeflateState)
    (keep : ∀ x, Keys x (f x)) : PrivM r ds d0 (wr (some (.tab ds)) f) := by
  intro h a h' ⟨e, get, keys⟩ run
  rw [wrD_eq, get] at run
  have eq := (Prod.mk.inj (Except.ok.inj run)).2
  subst eq
  exact ⟨priv_setD h r ds d0 (f e) get, f e, setD_dstates_same h ds (f e), keys.trans (keep e)⟩

/-- `p + n` from the start of a word block stays in that block. -/
theorem PrivM.padd_bind {β : Type} {r : ZStreamRef} {ds : Nat} {d0 : DeflateState} {P : Nat}
    (q : Ptr WRef) (pv : q = .ref (.blk P) 0) (n : Nat) {k : Ptr WRef → M β}
    (hk : ∀ m, PrivM r ds d0 (k (.ref (.blk P) m))) : PrivM r ds d0 (padd q n >>= k) := by
  intro h a h' pre run
  subst pv
  rw [bind_app] at run
  cases e : padd (Ptr.ref (WRef.blk P) 0) n h with
  | error _ => rw [e] at run; cases run
  | ok res =>
    rcases res with ⟨q', h1⟩
    rw [e] at run
    have hp : h1 = h := ReadM.ptr_add _ _ h _ _ e
    subst hp
    have form : ∃ m, q' = Ptr.ref (WRef.blk P) m := by
      simp only [padd, Ptr.add] at e
      split at e
      · cases e
      · split at e
        · cases e; exact ⟨_, rfl⟩
        · cases e
    obtain ⟨m, rfl⟩ := form
    exact hk m h1 a h' pre run

/-- A store into an owned word block. -/
theorem PrivM.store_blk {r : ZStreamRef} {ds : Nat} {d0 : DeflateState} {P : Nat} (m : Nat) (v : UInt16)
    (owned : DeflateOwned ds d0 P) : PrivM r ds d0 (Ptr.store (Ptr.ref (WRef.blk P) m) v) := by
  intro h a h' ⟨e, get, keys⟩ run
  have g : Space.get h (WRef.blk P) = h.words P := rfl
  have ro : Space.ro h (WRef.blk P) = false := rfl
  cases getW : h.words P with
  | none => simp [Ptr.store, g, getW] at run
  | some arr =>
    simp only [Ptr.store, g, getW, ro, Bool.false_eq_true, ite_false] at run
    split at run
    · have eq := (Prod.mk.inj (Except.ok.inj run)).2
      subst eq
      have same : Space.modify h (WRef.blk P) (fun a => a.set! m v) = setW h P (arr.set! m v) := by
        show { h with words := h.words.modify P (Option.map fun a => a.set! m v) } = _
        rw [Tbl.modify_opt _ _ _ _ getW]; rfl
      rw [same]
      exact ⟨priv_setW h r ds P d0 _ owned (by simp [getW]), e, by simpa [setW] using get, keys⟩
    · cases run

/-- The heap after `INSERT_STRING` from a hash environment is a private step. -/
theorem priv_inserted {h : Heap} {r : ZStreamRef} {ds w p q : Nat} {d : DeflateState} {wa : Array UInt8}
    {pa qa : Array UInt16} (key : UInt32) (hd : h.dstates ds = some d) (E : HashEnv h d w q p wa qa pa) :
    PrivStep h (insertedHeap h ds p q d pa qa key) r ds d :=
  ((priv_setW h r ds p d (pa.set! (d.strstart &&& d.w_mask).toNat (wfn qa key.toNat))
      (Or.inr (Or.inr (Or.inl E.prevp))) (by simp [E.pwords])).trans
    (priv_setW _ r ds q d (qa.set! key.toNat d.strstart.toUInt16) (Or.inr (Or.inr (Or.inr (Or.inl E.headp))))
      (by simp [setW, upd_ne _ _ _ _ E.hne, E.hwords]))).trans
    (priv_setD _ r ds d { d with ins_h := key } (by simpa [setW] using hd))

/-- `UPDATE_HASH` writes only `ins_h`. -/
theorem PrivM.update_hash {r : ZStreamRef} {ds : Nat} {d0 : DeflateState} (c : UInt8) :
    PrivM r ds d0 (UPDATE_HASH (some (.tab ds)) c) := by
  unfold UPDATE_HASH
  exact PrivM.ld_bind fun e keys => PrivM.bind (PrivM.of_read (ReadM.ushl _ _))
    fun _ => PrivM.st _ (keys.trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

/-- **`INSERT_STRING`** writes the state record and the stream's `prev` and `head` arrays. -/
theorem PrivM.insert_string {r : ZStreamRef} {ds p q : Nat} {d0 : DeflateState}
    (prev : d0.prev = .ref (.blk p) 0) (head : d0.head = .ref (.blk q) 0) (str : UInt32) :
    PrivM r ds d0 (INSERT_STRING (some (.tab ds)) str) := by
  unfold INSERT_STRING
  refine PrivM.ld_bind fun e _ => PrivM.bind (PrivM.of_read (ReadM.ptr_index _ _)) fun _ =>
    PrivM.bind (PrivM.update_hash _) fun _ => PrivM.ld_bind fun e2 keys2 =>
      PrivM.bind (PrivM.of_read (ReadM.ptr_index _ _)) fun v => ?_
  refine PrivM.padd_bind e2.prev (by rw [keys2.prev, prev]) _ fun m1 =>
    PrivM.bind (PrivM.store_blk m1 _ (Or.inr (Or.inr (Or.inl prev)))) fun _ => ?_
  exact PrivM.padd_bind e2.head (by rw [keys2.head, head]) _ fun m2 =>
    PrivM.bind (PrivM.store_blk m2 _ (Or.inr (Or.inr (Or.inr (Or.inl head))))) fun _ => PrivM.pure _

theorem PrivM.cdoWhile_go {σ : Type} {r : ZStreamRef} {ds : Nat} {d0 : DeflateState}
    (body : σ → M σ) (cond : σ → M (Bool × σ))
    (hb : ∀ s, PrivM r ds d0 (body s)) (hc : ∀ s, PrivM r ds d0 (cond s)) (n : Nat) (s : σ) :
    PrivM r ds d0 (cdoWhile.go body cond n s) := by
  induction n generalizing s with
  | zero => intro h v after _ run; cases run
  | succ n ih =>
    rw [cdoWhile.go]
    apply PrivM.bind (hb s)
    intro s'
    apply PrivM.bind (hc s')
    rintro ⟨c, t⟩
    exact PrivM.ite _ (ih t) (PrivM.pure _)

theorem PrivM.cdoWhile {σ : Type} {r : ZStreamRef} {ds : Nat} {d0 : DeflateState}
    (body : σ → M σ) (cond : σ → M (Bool × σ))
    (hb : ∀ s, PrivM r ds d0 (body s)) (hc : ∀ s, PrivM r ds d0 (cond s)) (s : σ) :
    PrivM r ds d0 (C.cdoWhile body cond s) := PrivM.cdoWhile_go body cond hb hc fuel s

/-- **The insertions after a match of `deflate_slow`** are a private step. -/
theorem PrivM.slow_match_advance {r : ZStreamRef} {ds p q : Nat} {d0 : DeflateState}
    (prev : d0.prev = .ref (.blk p) 0) (head : d0.head = .ref (.blk q) 0) (max_insert hash_head : UInt32) :
    PrivM r ds d0 (slowMatchAdvance (some (.tab ds)) max_insert hash_head) := by
  unfold slowMatchAdvance
  refine PrivM.bind (PrivM.wr _ fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) fun _ => PrivM.bind ?_ fun _ =>
    PrivM.bind (PrivM.wr _ fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) fun _ => PrivM.pure _
  refine PrivM.cdoWhile _ _ (fun s => ?_) (fun s => ?_) _
  · unfold slowMatchBody
    exact PrivM.bind (PrivM.wr _ fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) fun _ => PrivM.bind (PrivM.rd _) fun _ =>
      PrivM.ite _ (PrivM.insert_string prev head _) (PrivM.pure _)
  · unfold slowMatchCond
    exact PrivM.bind (PrivM.wr _ fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) fun _ => PrivM.bind (PrivM.rd _) fun _ =>
      PrivM.pure _

end Zlib.Deflate.Universal
