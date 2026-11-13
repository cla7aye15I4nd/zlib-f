import ZlibF.Proof.«gzlib.c.error-borrow»
import ZlibF.Proof.«gzfs.error-message-frame»

/-! # Actual error handling does not retain an external string view

Every returning execution of gz_error leaves its message pointer NULL or a
malloc-block root. This statement permits arbitrary incoming message pointers
and both allocation outcomes. It does not assert successful formatting for an
invalid caller or replace the separate message-content correctness goal.
-/
namespace C.LibcBorrow
open Zlib.Gzguts Zlib.Gzlib Zlib.GzFs

/-- Pointer representation that can belong to gzip's owned message slot. -/
def OwnedMessagePointer (p : BPtr) : Prop :=
  p = .null ∨ ∃ b, p = .ref (.blk b) 0

def MessageShape (i : Nat) (h : Heap) : Prop :=
  ∀ s, h.gzstates i = some s → OwnedMessagePointer s.msg

private def Protects (i : Nat) {α : Type} (m : M α) : Prop :=
  ∀ h value after, MessageShape i h → m h = .ok (value, after) → MessageShape i after

private def Establishes (i : Nat) {α : Type} (m : M α) : Prop :=
  ∀ h value after, m h = .ok (value, after) → MessageShape i after

private theorem Protects.pure {α : Type} (i : Nat) (a : α) : Protects i (pure a : M α) := by
  intro h v after hs hr
  cases hr
  exact hs

private theorem Protects.bind {α β : Type} {i : Nat} {m : M α} {f : α → M β}
    (hm : Protects i m) (hf : ∀ a, Protects i (f a)) : Protects i (m >>= f) := by
  intro h v after hs hr
  rw [bind_app] at hr
  cases he : m h with
  | error e => simp [he] at hr
  | ok p =>
    rcases p with ⟨a, h1⟩
    rw [he] at hr
    exact hf a h1 v after (hm h a h1 hs he) hr

private theorem Protects.ite {α : Type} {i : Nat} (p : Prop) [Decidable p]
    {yes no : M α} (hy : Protects i yes) (hn : Protects i no) :
    Protects i (if p then yes else no) := by
  split <;> assumption

private theorem Protects.of_records {α : Type} (i : Nat) {m : M α}
    (hm : RecordStableM m) : Protects i m := by
  intro h v after hs hr s he
  rw [hm h v after hr] at he
  exact hs s he

private theorem Establishes.protects {α : Type} {i : Nat} {m : M α}
    (hm : Establishes i m) : Protects i m := by
  intro h v after _ hr
  exact hm h v after hr

private theorem Establishes.bind {α β : Type} {i : Nat} {m : M α} {f : α → M β}
    (hm : Establishes i m) (hf : ∀ a, Protects i (f a)) : Establishes i (m >>= f) := by
  intro h v after hr
  rw [bind_app] at hr
  cases he : m h with
  | error e => simp [he] at hr
  | ok p =>
    rcases p with ⟨a, h1⟩
    rw [he] at hr
    exact hf a h1 v after (hm h a h1 he) hr

private theorem record_ldS (i : Nat) : RecordStableM (ldS (some (.tab i))) := by
  intro h v after hr
  change (match h.gzstates i with
    | some s => Except.ok (s, h)
    | none => Except.error (Fault.ub "access through a dangling pointer (gz_state)")) = Except.ok (v, after) at hr
  split at hr
  · cases hr; rfl
  · contradiction

private theorem record_strLit (s : String) : RecordStableM (strLit s) := by
  intro h v after hr
  unfold strLit strLitRef at hr
  split at hr
  · cases hr; rfl
  · contradiction

private theorem record_allocB (n : Nat) : RecordStableM (allocB n) := by
  intro h v after hr
  unfold allocB at hr
  split at hr
  · split at hr
    · contradiction
    · cases hr; rfl
  · cases hr; rfl

private theorem allocB_pointer_shape {n : Nat} {h after : Heap} {p : BPtr}
    (hr : allocB n h = .ok (p, after)) : OwnedMessagePointer p := by
  unfold allocB at hr
  split at hr
  · split at hr
    · contradiction
    · cases hr; exact Or.inr ⟨_, rfl⟩
  · cases hr; exact Or.inl rfl

private theorem ldS_run {i : Nat} {h after : Heap} {s : GzState}
    (hr : ldS (some (.tab i)) h = .ok (s, after)) :
    after = h ∧ h.gzstates i = some s := by
  change (match h.gzstates i with
    | some st => Except.ok (st, h)
    | none => Except.error (Fault.ub "access through a dangling pointer (gz_state)")) = Except.ok (s, after) at hr
  split at hr
  · cases hr; exact ⟨rfl, by assumption⟩
  · contradiction

private theorem updS_run {i : Nat} {h after : Heap} {v : Unit}
    (f : GzState → GzState) (hr : updS (some (.tab i)) f h = .ok (v, after)) :
    ∃ s, h.gzstates i = some s ∧ after = { h with gzstates := upd h.gzstates i (some (f s)) } := by
  unfold updS at hr
  rw [bind_app] at hr
  cases he : h.gzstates i with
  | none => simp [ldGzState, GzStateRef.get, he] at hr
  | some s =>
    simp only [ldGzState, GzStateRef.get, he] at hr
    simp only [stGzState, GzStateRef.get, he, GzStateRef.isRo, Bool.false_eq_true,
      ite_false, GzStateRef.put] at hr
    cases hr
    exact ⟨s, rfl, rfl⟩

private theorem protects_updS (i : Nat) (f : GzState → GzState)
    (hf : ∀ s, OwnedMessagePointer s.msg → OwnedMessagePointer (f s).msg) :
    Protects i (updS (some (.tab i)) f) := by
  intro h v after hs hr
  obtain ⟨s, he, rfl⟩ := updS_run f hr
  intro current hc
  simp only [upd_same] at hc
  cases hc
  exact hf s (hs s he)

private theorem establishes_updS (i : Nat) (f : GzState → GzState)
    (hf : ∀ s, OwnedMessagePointer (f s).msg) :
    Establishes i (updS (some (.tab i)) f) := by
  intro h v after hr
  obtain ⟨s, he, rfl⟩ := updS_run f hr
  intro current hc
  simp only [upd_same] at hc
  cases hc
  exact hf s

private theorem protects_alloc_message (i n : Nat) : Protects i (do
    let m ← allocB n
    updS (some (.tab i)) fun s => { s with msg := m }
    return m) := by
  intro h v after _ hr
  rw [bind_app] at hr
  cases he : allocB n h with
  | error e => simp [he] at hr
  | ok result =>
    rcases result with ⟨p, h1⟩
    rw [he] at hr
    apply Establishes.bind (establishes_updS i _ (fun _ => allocB_pointer_shape he))
      (fun _ => Protects.pure i p) h1 v after hr

private def errorAllocatedTail (i : Nat) (msg m : BPtr) : M Unit := do
  if m == .null then
    updS (some (.tab i)) fun s => { s with err := Z_MEM_ERROR }
    return
  let s ← ldS (some (.tab i))
  let fmt ← strLit "%s%s%s"
  let sep ← strLit ": "
  let l1 ← strlenB s.path
  let l2 ← strlenB msg
  let _ ← snprintf s.msg (l1 + l2 + 3) fmt [.str s.path, .str sep, .str msg]

private theorem protects_allocated_tail (i : Nat) (msg m : BPtr) :
    Protects i (errorAllocatedTail i msg m) := by
  unfold errorAllocatedTail
  apply Protects.ite
  · apply Protects.bind (protects_updS i (fun s => { s with err := Z_MEM_ERROR }) (fun _ hs => hs))
    intro _
    exact Protects.pure i _
  · apply Protects.bind (Protects.of_records i (record_ldS i))
    intro s
    apply Protects.bind (Protects.of_records i (record_strLit _))
    intro fmt
    apply Protects.bind (Protects.of_records i (record_strLit _))
    intro sep
    apply Protects.bind (Protects.of_records i (record_strlenB _))
    intro l1
    apply Protects.bind (Protects.of_records i (record_strlenB _))
    intro l2
    apply Protects.bind (Protects.of_records i (record_snprintf _ _ _ _))
    intro _
    exact Protects.pure i _

private def messageTail (i : Nat) (err : Int32) (msg : BPtr) : M Unit := do
  updS (some (.tab i)) fun s => { s with err := err }
  if msg == .null then return
  if err == Z_MEM_ERROR then return
  let s ← ldS (some (.tab i))
  let l1 ← strlenB s.path
  let l2 ← strlenB msg
  let m ← (do
    let allocated ← allocB (l1 + l2 + 3).toNat
    updS (some (.tab i)) fun s => { s with msg := allocated }
    return allocated)
  errorAllocatedTail i msg m

private theorem protects_message_tail (i : Nat) (err : Int32) (msg : BPtr) :
    Protects i (messageTail i err msg) := by
  unfold messageTail
  apply Protects.bind (protects_updS i (fun s => { s with err := err }) (fun _ hs => hs))
  intro _
  apply Protects.ite
  · exact Protects.pure i _
  · apply Protects.ite
    · exact Protects.pure i _
    · apply Protects.bind (Protects.of_records i (record_ldS i))
      intro s
      apply Protects.bind (Protects.of_records i (record_strlenB _))
      intro l1
      apply Protects.bind (Protects.of_records i (record_strlenB _))
      intro l2
      apply Protects.bind (protects_alloc_message i _)
      intro m
      exact protects_allocated_tail i msg m

private def clearMessage (i : Nat) : M Unit := do
  let s ← ldS (some (.tab i))
  if s.msg != .null then
    if s.err != Z_MEM_ERROR then freeB s.msg
    updS (some (.tab i)) fun s => { s with msg := .null }

private theorem establishes_clear_message (i : Nat) : Establishes i (clearMessage i) := by
  intro h v after hr
  unfold clearMessage at hr
  rw [bind_app] at hr
  cases he : ldS (some (.tab i)) h with
  | error e => simp [he] at hr
  | ok result =>
    rcases result with ⟨s, h1⟩
    obtain ⟨rfl, hs⟩ := ldS_run he
    rw [he] at hr
    dsimp only at hr
    split at hr
    · split at hr
      · rw [bind_app] at hr
        cases hf : freeB s.msg h1 with
        | error e => simp [hf] at hr
        | ok freed =>
          rcases freed with ⟨_, h2⟩
          rw [hf] at hr
          exact establishes_updS i _ (fun _ => Or.inl rfl) h2 v after hr
      · exact establishes_updS i _ (fun _ => Or.inl rfl) h1 v after hr
    · cases hr
      intro s' hs'
      rw [hs] at hs'
      cases hs'
      apply Or.inl
      by_cases heq : s.msg = .null
      · exact heq
      · exact False.elim (‹¬(s.msg != .null) = true› (by simpa only [bne_iff_ne] using heq))

private theorem msg_bind_assoc {α β γ : Type} (m : M α) (f : α → M β) (g : β → M γ) :
    (m >>= f) >>= g = m >>= (fun a => f a >>= g) := by
  funext h
  cases he : m h <;> simp [bind_app, he]

private theorem msg_pure_bind {α β : Type} (a : α) (f : α → M β) :
    (pure a >>= f) = f a := rfl

private theorem msg_ite_bind {α β : Type} (p : Prop) [Decidable p]
    (yes no : M α) (f : α → M β) :
    (if p then yes else no) >>= f = if p then yes >>= f else no >>= f := by
  split <;> rfl

private theorem error_source_shape (i : Nat) (err : Int32) (msg : BPtr) :
    gz_error (some (.tab i)) err msg = (do
      clearMessage i
      messageTail i err msg) := by
  unfold gz_error clearMessage messageTail errorAllocatedTail
  simp only [msg_bind_assoc, msg_pure_bind, msg_ite_bind]

/-- Every successful actual execution leaves only a NULL or malloc-block-root
message pointer. Borrowed .str views are consumed synchronously and never
retained in that owned slot, including both message-allocation outcomes. -/
theorem gz_error_message_noescape (i : Nat) (err : Int32) (msg : BPtr)
    (h after : Heap) (v : Unit)
    (hr : gz_error (some (.tab i)) err msg h = .ok (v, after)) :
    ∀ s, after.gzstates i = some s → OwnedMessagePointer s.msg := by
  rw [error_source_shape] at hr
  exact Establishes.bind (establishes_clear_message i)
    (fun _ => protects_message_tail i err msg) h v after hr

/-- A returned owned message cannot be a source literal or the external
borrowed errno view, regardless of its current epoch. -/
theorem gz_error_message_not_str (i : Nat) (err : Int32) (msg : BPtr)
    (h after : Heap) (v : Unit)
    (hr : gz_error (some (.tab i)) err msg h = .ok (v, after))
    (s : GzState) (hs : after.gzstates i = some s) (j off : Nat) :
    s.msg ≠ .ref (.str j) off := by
  rcases gz_error_message_noescape i err msg h after v hr s hs with hn | ⟨b, hb⟩
  · rw [hn]; intro he; cases he
  · rw [hb]; intro he; cases he

#print axioms gz_error_message_noescape
#print axioms gz_error_message_not_str
end C.LibcBorrow
