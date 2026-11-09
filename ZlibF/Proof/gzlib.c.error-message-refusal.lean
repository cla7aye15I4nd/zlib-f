import ZlibF.Proof.«gzfs.format-error-message»
import ZlibF.Proof.«gzlib.c.base»
import ZlibF.Spec.Public.GzState

/-! # Actual error-message allocation refusal

Arbitrary valid path/message C strings are read by the real strlen operations.
When the actual message allocation is refused, gz_error returns with NULL msg
and Z_MEM_ERROR, preserving every allocation and all bytes. The allocator call
is counted. This first branch requires no old message; old-message cleanup and
successful copied-message allocation remain separate producer branches.
-/
namespace Zlib.Gzlib.MessageRefusal
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzlib.Spec Zlib.Gzlib.Proofs
open ZlibF.Spec.Public

private theorem view_setS (h : Heap) (i : Nat) (s : GzState) (r : BRef) :
    Space.get (setS h i s) r = Space.get h r := by
  cases r <;> rfl

private theorem strlenB_setS (h : Heap) (i : Nat) (s : GzState) (p : BPtr) :
    strlenB p (setS h i s) = match strlenB p h with
      | .error e => .error e
      | .ok (n, _) => .ok (n, setS h i s) := by
  cases p with
  | null => rfl
  | ref r off =>
    simp only [strlenB, view_setS]
    cases he : Space.get h r with
    | none => rfl
    | some a =>
      dsimp only
      cases hl : strlenFrom a off <;> simp only [hl]

private theorem cstring_nonnull {h : Heap} {p : BPtr} {xs : List UInt8} (hc : CString h p xs) : p ≠ .null := by
  intro hp
  rcases hc.1 with hn | ⟨r, off, a, he, _⟩
  · have := hn.2.1; omega
  · rw [hp] at he; cases he

def refusedMessageState (s : GzState) : GzState := { s with err := Z_MEM_ERROR, msg := .null }
def refusedMessageHeap (h : Heap) (i : Nat) (s : GzState) : Heap :=
  { setS h i (refusedMessageState s) with nalloc := h.nalloc + 1 }

/-- Actual whole-handler refusal, with arbitrary readable CString views and
all malloc garbage. No strlen/callee contract is a premise. -/
theorem gz_error_errno_refusal_run {h : Heap} {i : Nat} {s : GzState} {msg : BPtr}
    {pathText errorText : List UInt8} (hs : h.gzstates i = some s) (hm : s.msg = .null)
    (hp : CString h s.path pathText) (he : CString h msg errorText)
    (ha : h.allocOk h.nalloc = false) :
    gz_error (some (.tab i)) Z_ERRNO msg h = .ok ((), refusedMessageHeap h i s) := by
  have hp0 := Zlib.GzFs.Proofs.strlenB_of_CString hp
  have he0 := Zlib.GzFs.Proofs.strlenB_of_CString he
  have hp1 : strlenB s.path (setS h i { s with err := Z_ERRNO }) =
      .ok (UInt64.ofNat pathText.length, setS h i { s with err := Z_ERRNO }) := by
    rw [strlenB_setS, hp0]
  have he1 : strlenB msg (setS h i { s with err := Z_ERRNO }) =
      .ok (UInt64.ofNat errorText.length, setS h i { s with err := Z_ERRNO }) := by
    rw [strlenB_setS, he0]
  simp only [setS, hm, Z_ERRNO] at hp1 he1
  have hn := cstring_nonnull he
  simp [gz_error, bind_app, ldS_eq, updS_eq, hs, hm, hn, hp1, he1,
    allocB, ha, Z_ERRNO, Z_MEM_ERROR, refusedMessageHeap, refusedMessageState,
    setS, upd_upd]

/-- Failure of message malloc creates or frees no object and changes no bytes.
The sole permitted old allocation footprint is the gzip handle itself. -/
theorem refused_message_frame (h : Heap) (i : Nat) (s : GzState) :
    Frame h (refusedMessageHeap h i s) (fun b => b = i) := by
  refine ⟨rfl, rfl, rfl, Nat.le_refl _, by change h.nalloc ≤ h.nalloc + 1; omega, ?_⟩
  intro b _ hb
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl,
    by simp [refusedMessageHeap, setS, upd_ne _ _ _ _ hb], rfl⟩

theorem refused_message_live (h : Heap) (i : Nat) (s : GzState) (hs : h.gzstates i = some s) :
    LiveChange h (refusedMessageHeap h i s) (fun _ => False) (fun _ => False) := by
  intro b
  change (setS h i (refusedMessageState s)).live b ↔ (h.live b ∧ ¬ False) ∨ False
  simpa using (Shape.live (shape_setS hs (refusedMessageState s)) b)

/-- The original public footprint also suffices; no caller-frame condition is
added to the public domain. -/
theorem refused_message_owned_frame (h : Heap) (i : Nat) (s : GzState) :
    Frame h (refusedMessageHeap h i s) (GzOwned h i s) := by
  obtain ⟨hs, ha, hg, hn, hc, hf⟩ := refused_message_frame h i s
  refine ⟨hs, ha, hg, hn, hc, ?_⟩
  intro b hl ho
  apply hf b hl
  intro hb
  exact ho (Or.inl hb)

#print axioms gz_error_errno_refusal_run
#print axioms refused_message_frame
#print axioms refused_message_live
#print axioms refused_message_owned_frame
end Zlib.Gzlib.MessageRefusal
