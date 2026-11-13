import ZlibF.Proof.«gzlib.c.base»
import ZlibF.Proof.«gzfs.borrow-stable»

/-!
# gzlib.c: `gz_error` keeps the output window `x`

`gz_error` writes only the fields `msg` and `err` of the state record. Its library calls
(`strlen`, `malloc`, `free`, `snprintf`) write byte storage and allocation counters, never a gz
state record. So `x` (`have`, `next`, `pos`) is the same after every returning execution. The read
side uses this on every error path: a reader that sets `x` and then reports an error leaves `x` as
set.
-/

namespace Zlib.Gzlib.KeepsX
open C Zlib.Gzguts Zlib.GzFs Zlib.Gzlib Zlib.Gzlib.Proofs
set_option autoImplicit false

/-- A returning execution leaves every gz state record unchanged. -/
def GzSame {α : Type} (m : M α) : Prop :=
  ∀ h a after, m h = .ok (a, after) → after.gzstates = h.gzstates

theorem GzSame.pure {α : Type} (a : α) : GzSame (pure a : M α) := by
  intro h value after hr; cases hr; rfl

theorem GzSame.bind {α β : Type} {m : M α} {f : α → M β}
    (hm : GzSame m) (hf : ∀ a, GzSame (f a)) : GzSame (m >>= f) := by
  intro h value after hr
  rw [bind_app] at hr
  cases he : m h with
  | error e => simp [he] at hr
  | ok p =>
    rcases p with ⟨a, h1⟩
    rw [he] at hr
    exact (hf a h1 value after hr).trans (hm h a h1 he)

theorem GzSame.ite {α : Type} (p : Prop) [Decidable p] {a b : M α}
    (ha : GzSame a) (hb : GzSame b) : GzSame (if p then a else b) := by
  split <;> assumption

theorem GzSame.ub {α : Type} (what : String) : GzSame (C.ub what : M α) := by
  intro h value after hr; cases hr

theorem same_strlenB (p : BPtr) : GzSame (strlenB p) := by
  intro h value after hr
  unfold strlenB at hr
  split at hr
  · contradiction
  · split at hr
    · contradiction
    · split at hr
      · cases hr; rfl
      · contradiction

theorem same_strLitRef (s : String) : GzSame (strLitRef s) := by
  intro h value after hr
  unfold strLitRef at hr
  split at hr
  · cases hr; rfl
  · contradiction

theorem space_modify_gz (h : Heap) (r : BRef) (f : Array UInt8 → Array UInt8) :
    (Space.modify h r f).gzstates = h.gzstates := by
  cases r <;> rfl

theorem same_memcpyB (dst src : BPtr) (n : Nat) : GzSame (memcpyB dst src n) := by
  intro h value after hr
  unfold memcpyB Ptr.memcpy at hr
  split at hr
  · split at hr
    · split at hr
      · contradiction
      · split at hr
        · split at hr
          · cases hr; exact space_modify_gz _ _ _
          · contradiction
        · contradiction
    · contradiction
  · contradiction

theorem same_store8 (p : BPtr) (v : UInt8) : GzSame (store8 p v) := by
  intro h value after hr
  unfold store8 Ptr.store at hr
  split at hr
  · contradiction
  · split at hr
    · contradiction
    · split at hr
      · contradiction
      · split at hr
        · cases hr; exact space_modify_gz _ _ _
        · contradiction

theorem same_allocBytes (a : Array UInt8) : GzSame (allocBytes a) := by
  intro h value after hr
  unfold allocBytes at hr
  split at hr
  · contradiction
  · cases hr; rfl

theorem same_allocB (n : Nat) : GzSame (allocB n) := by
  intro h value after hr
  unfold allocB at hr
  split at hr
  · split at hr
    · contradiction
    · cases hr; rfl
  · cases hr; rfl

theorem same_freeB (p : BPtr) : GzSame (freeB p) := by
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

theorem same_ptr_add {R T : Type} [Space Heap R T] (p : Ptr R) (k : Int) : GzSame (p.add k) := by
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

theorem same_ptr_load {R T : Type} [Space Heap R T] (p : Ptr R) : GzSame (Ptr.load p : M T) := by
  intro h value after hr
  unfold Ptr.load at hr
  split at hr
  · contradiction
  · split at hr
    · contradiction
    · split at hr
      · cases hr; rfl
      · contradiction

theorem same_index8 (p : BPtr) (i : Int) : GzSame (index8 p i) := by
  unfold index8 Ptr.index
  exact GzSame.bind (same_ptr_add _ _) (fun _ => same_ptr_load _)

theorem GzSame.list_forIn {α β : Type} (values : List α)
    (body : (value : α) → value ∈ values → β → M (ForInStep β))
    (same : ∀ value member state, GzSame (body value member state))
    (initial : β) : GzSame (List.forIn' values initial body) := by
  induction values generalizing initial with
  | nil =>
    simp only [List.forIn'_eq_forIn', List.forIn'_nil]
    exact GzSame.pure _
  | cons head tail ih =>
    simp only [List.forIn'_eq_forIn', List.forIn'_cons]
    apply GzSame.bind (same head (by simp) initial)
    intro decision
    cases decision with
    | done value => exact GzSame.pure _
    | yield next =>
      exact ih (fun value member state => body value (by simp [member]) state)
        (fun value member state => same value (by simp [member]) state) next

theorem same_cstring (p : BPtr) : GzSame (cstring p) := by
  unfold cstring
  apply GzSame.bind (same_strlenB p)
  intro n
  simp only [forIn, Std.Legacy.Range.forIn'_eq_forIn'_range']
  apply GzSame.bind
  · apply GzSame.list_forIn
    intro value _ current
    apply GzSame.bind (same_index8 _ _)
    intro byte
    exact GzSame.pure _
  · intro result
    exact GzSame.pure _

theorem same_formatBytes (f : Array UInt8) (args : List VaArg) : GzSame (formatBytes f args) := by
  intro h value after hr
  unfold formatBytes at hr
  split at hr
  · cases hr; rfl
  · contradiction

theorem same_storeBytes (p : BPtr) (bs : Array UInt8) : GzSame (storeBytes p bs) := by
  unfold storeBytes
  apply GzSame.ite
  · exact GzSame.pure _
  · apply GzSame.bind (same_allocBytes _)
    intro tmp
    apply GzSame.bind (same_memcpyB _ _ _)
    intro _
    exact same_freeB _

theorem same_snprintf (dst : BPtr) (size : UInt64) (fmt : BPtr) (args : List VaArg) :
    GzSame (snprintf dst size fmt args) := by
  unfold snprintf
  apply GzSame.bind (same_cstring _)
  intro f
  apply GzSame.bind (same_formatBytes _ _)
  intro out
  dsimp only
  apply GzSame.ite
  · apply GzSame.bind (same_storeBytes _ _)
    intro _
    apply GzSame.bind (same_ptr_add _ _)
    intro q
    apply GzSame.bind (same_store8 _ _)
    intro _
    exact GzSame.pure _
  · exact GzSame.pure _

/-- A returning execution keeps the record `i`, if it exists, with the same `x`. -/
def KeepsX {α : Type} (i : Nat) (m : M α) : Prop :=
  ∀ h a after, m h = .ok (a, after) → ∀ s, h.gzstates i = some s →
    ∃ s', after.gzstates i = some s' ∧ s'.x = s.x

theorem KeepsX.of_same {α : Type} {i : Nat} {m : M α} (hm : GzSame m) : KeepsX i m := by
  intro h a after hr s hs
  exact ⟨s, by rw [hm h a after hr]; exact hs, rfl⟩

theorem KeepsX.bind {α β : Type} {i : Nat} {m : M α} {f : α → M β}
    (hm : KeepsX i m) (hf : ∀ a, KeepsX i (f a)) : KeepsX i (m >>= f) := by
  intro h value after hr s hs
  rw [bind_app] at hr
  cases he : m h with
  | error e => simp [he] at hr
  | ok p =>
    rcases p with ⟨a, h1⟩
    rw [he] at hr
    obtain ⟨s1, hs1, x1⟩ := hm h a h1 he s hs
    obtain ⟨s2, hs2, x2⟩ := hf a h1 value after hr s1 hs1
    exact ⟨s2, hs2, x2.trans x1⟩

theorem KeepsX.ite {α : Type} {i : Nat} (p : Prop) [Decidable p] {a b : M α}
    (ha : KeepsX i a) (hb : KeepsX i b) : KeepsX i (if p then a else b) := by
  split <;> assumption

theorem keepsX_ldS (i j : Nat) : KeepsX i (ldS (some (.tab j))) := by
  intro h a after hr s hs
  rw [ldS_eq] at hr
  split at hr
  · cases hr; exact ⟨s, hs, rfl⟩
  · contradiction

theorem keepsX_updS (i j : Nat) (f : GzState → GzState) (hf : ∀ s, (f s).x = s.x) :
    KeepsX i (updS (some (.tab j)) f) := by
  intro h a after hr s hs
  rw [updS_eq] at hr
  split at hr
  · rename_i v hv
    cases hr
    by_cases e : i = j
    · subst e
      rw [hs] at hv; cases hv
      exact ⟨f s, setS_gz_same _ _ _, hf s⟩
    · exact ⟨s, by rw [setS_gz_ne _ _ _ _ e]; exact hs, rfl⟩
  · contradiction

/-- The source tail of `gz_error` after the release of the old message (statement for statement). -/
private def errorTail (p : GzStatePtr) (err : Int32) (msg : BPtr) : M Unit := do
  updS p fun s => { s with err := err }
  if msg == .null then return
  if err == Z_MEM_ERROR then return
  let s ← ldS p
  let l1 ← strlenB s.path
  let l2 ← strlenB msg
  let m ← allocB (l1 + l2 + 3).toNat
  updS p fun s => { s with msg := m }
  if m == .null then
    updS p fun s => { s with err := Z_MEM_ERROR }
    return
  let s ← ldS p
  let fmt ← strLit "%s%s%s"
  let sep ← strLit ": "
  let l1 ← strlenB s.path
  let l2 ← strlenB msg
  let _ ← snprintf s.msg (l1 + l2 + 3) fmt [.str s.path, .str sep, .str msg]

private theorem error_source (p : GzStatePtr) (err : Int32) (msg : BPtr) :
    gz_error p err msg = (do
      let s ← ldS p
      if s.msg != .null then
        if s.err != Z_MEM_ERROR then freeB s.msg
        updS p fun s => { s with msg := .null }
      errorTail p err msg) := rfl

theorem same_strLit (s : String) : GzSame (strLit s) := same_strLitRef s

/-- Steps through a statement sequence of `gz_error`, one primitive at a time. -/
local macro "keepsx" : tactic => `(tactic| repeat (first
  | exact KeepsX.of_same (GzSame.pure _)
  | exact KeepsX.of_same (same_freeB _)
  | apply KeepsX.ite
  | (apply KeepsX.bind (keepsX_updS _ _ _ (by intro; rfl)); intro _)
  | (apply KeepsX.bind (keepsX_ldS _ _); intro _)
  | (apply KeepsX.bind (KeepsX.of_same (same_strlenB _)); intro _)
  | (apply KeepsX.bind (KeepsX.of_same (same_allocB _)); intro _)
  | (apply KeepsX.bind (KeepsX.of_same (same_strLit _)); intro _)
  | (apply KeepsX.bind (KeepsX.of_same (same_snprintf _ _ _ _)); intro _)
  | (apply KeepsX.bind (KeepsX.of_same (same_freeB _)); intro _)
  | dsimp only))

private theorem errorTail_keepsX (i j : Nat) (err : Int32) (msg : BPtr) :
    KeepsX i (errorTail (some (.tab j)) err msg) := by
  unfold errorTail
  keepsx

/-- **`gz_error` keeps `x`** of every gz state record, on every returning execution (an existing
message freed or not, message allocation failed or not). -/
theorem gz_error_keepsX (i j : Nat) (err : Int32) (msg : BPtr) :
    KeepsX i (gz_error (some (.tab j)) err msg) := by
  rw [error_source]
  keepsx
  all_goals exact errorTail_keepsX i j err msg

end Zlib.Gzlib.KeepsX
