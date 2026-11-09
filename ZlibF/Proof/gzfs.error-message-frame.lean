import ZlibF.Proof.«gzfs.borrow-stable»

/-! # Actual formatting preserves the gzip-state table

The actual error-message formatter modifies byte storage only. This independent
observation is used to establish that the borrowed argument is not retained as
the writer's owned message pointer. No callee specification is assumed.
-/
namespace C.LibcBorrow
open Zlib.GzFs

def RecordStableM {α : Type} (m : M α) : Prop :=
  ∀ h value after, m h = .ok (value, after) → after.gzstates = h.gzstates

theorem RecordStableM.pure {α : Type} (a : α) : RecordStableM (pure a : M α) := by
  intro h value after hr
  cases hr
  rfl

theorem RecordStableM.bind {α β : Type} {m : M α} {f : α → M β}
    (hm : RecordStableM m) (hf : ∀ a, RecordStableM (f a)) : RecordStableM (m >>= f) := by
  intro h value after hr
  rw [bind_app] at hr
  cases he : m h with
  | error e => simp [he] at hr
  | ok p =>
    rcases p with ⟨a, h1⟩
    rw [he] at hr
    exact (hf a h1 value after hr).trans (hm h a h1 he)

theorem record_freeB (p : BPtr) : RecordStableM (freeB p) := by
  intro h value after hr
  unfold freeB at hr
  split at hr
  · cases hr; rfl
  · split at hr
    · split at hr
      · contradiction
      · cases hr; rfl
    · contradiction
  · contradiction

theorem record_strlenB (p : BPtr) : RecordStableM (strlenB p) := by
  intro h value after hr
  unfold strlenB at hr
  split at hr
  · contradiction
  · split at hr
    · contradiction
    · split at hr
      · cases hr; rfl
      · contradiction

theorem space_modify_gzstates (h : Heap) (r : BRef) (f : Array UInt8 → Array UInt8) :
    (Space.modify h r f).gzstates = h.gzstates := by
  cases r <;> rfl

theorem record_memcpyB (dst src : BPtr) (n : Nat) : RecordStableM (memcpyB dst src n) := by
  intro h value after hr
  unfold memcpyB Ptr.memcpy at hr
  split at hr
  · split at hr
    · split at hr
      · contradiction
      · split at hr
        · split at hr
          · cases hr; exact space_modify_gzstates _ _ _
          · contradiction
        · contradiction
    · contradiction
  · contradiction

theorem record_store8 (p : BPtr) (v : UInt8) : RecordStableM (store8 p v) := by
  intro h value after hr
  unfold store8 Ptr.store at hr
  split at hr
  · contradiction
  · split at hr
    · contradiction
    · split at hr
      · contradiction
      · split at hr
        · cases hr; exact space_modify_gzstates _ _ _
        · contradiction

theorem record_allocBytes (a : Array UInt8) : RecordStableM (allocBytes a) := by
  intro h value after hr
  unfold allocBytes at hr
  split at hr
  · contradiction
  · cases hr; rfl

theorem RecordStableM.list_forIn {α β : Type} (values : List α)
    (body : (value : α) → value ∈ values → β → M (ForInStep β))
    (stable : ∀ value member state, RecordStableM (body value member state))
    (initial : β) : RecordStableM (List.forIn' values initial body) := by
  induction values generalizing initial with
  | nil =>
    simp only [List.forIn'_eq_forIn', List.forIn'_nil]
    exact RecordStableM.pure _
  | cons head tail ih =>
    simp only [List.forIn'_eq_forIn', List.forIn'_cons]
    apply RecordStableM.bind (stable head (by simp) initial)
    intro decision
    cases decision with
    | done value => exact RecordStableM.pure _
    | yield next =>
      exact ih (fun value member state => body value (by simp [member]) state)
        (fun value member state => stable value (by simp [member]) state) next

theorem RecordStableM.ub {α : Type} (what : String) : RecordStableM (C.ub what : M α) := by
  intro h value after hr
  cases hr

theorem RecordStableM.ite {α : Type} (p : Prop) [Decidable p] {a b : M α}
    (ha : RecordStableM a) (hb : RecordStableM b) : RecordStableM (if p then a else b) := by
  split <;> assumption

theorem record_ptr_add {R T : Type} [Space Heap R T] (p : Ptr R) (k : Int) : RecordStableM (p.add k) := by
  intro h value after hr
  unfold Ptr.add at hr
  split at hr
  · split at hr
    · cases hr; rfl
    · contradiction
  · split at hr
    · contradiction
    · split at hr
      · cases hr; rfl
      · contradiction

theorem record_ptr_load {R T : Type} [Space Heap R T] (p : Ptr R) : RecordStableM (Ptr.load p : M T) := by
  intro h value after hr
  unfold Ptr.load at hr
  split at hr
  · contradiction
  · split at hr
    · contradiction
    · split at hr
      · cases hr; rfl
      · contradiction

theorem record_index8 (p : BPtr) (i : Int) : RecordStableM (index8 p i) := by
  unfold index8 Ptr.index
  exact RecordStableM.bind (record_ptr_add _ _) (fun _ => record_ptr_load _)

theorem record_cstring (p : BPtr) : RecordStableM (cstring p) := by
  unfold cstring
  apply RecordStableM.bind (record_strlenB p)
  intro n
  simp only [forIn, Std.Legacy.Range.forIn'_eq_forIn'_range']
  apply RecordStableM.bind
  · apply RecordStableM.list_forIn
    intro value _ current
    apply RecordStableM.bind (record_index8 _ _)
    intro byte
    exact RecordStableM.pure _
  · intro result
    exact RecordStableM.pure _

theorem record_formatBytes (f : Array UInt8) (args : List VaArg) : RecordStableM (formatBytes f args) := by
  intro h value after hr
  unfold formatBytes at hr
  split at hr
  · cases hr; rfl
  · contradiction

theorem record_storeBytes (p : BPtr) (bs : Array UInt8) : RecordStableM (storeBytes p bs) := by
  unfold storeBytes
  apply RecordStableM.ite
  · exact RecordStableM.pure _
  · apply RecordStableM.bind (record_allocBytes _)
    intro tmp
    apply RecordStableM.bind (record_memcpyB _ _ _)
    intro _
    exact record_freeB _

theorem record_vsnprintf (dst : BPtr) (size : UInt64) (fmt : BPtr) (args : List VaArg) :
    RecordStableM (vsnprintf dst size fmt args) := by
  unfold vsnprintf
  apply RecordStableM.bind (record_cstring _)
  intro f
  apply RecordStableM.bind (record_formatBytes _ _)
  intro out
  apply RecordStableM.ite
  · exact RecordStableM.ub _
  · dsimp only
    apply RecordStableM.ite
    · apply RecordStableM.bind (record_storeBytes _ _)
      intro _
      apply RecordStableM.bind (record_ptr_add _ _)
      intro q
      apply RecordStableM.bind (record_store8 _ _)
      intro _
      exact RecordStableM.pure _
    · exact RecordStableM.pure _

#print axioms record_vsnprintf
end C.LibcBorrow
