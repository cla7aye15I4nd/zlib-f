import ZlibF.Zlib.«gzlib.c»
import ZlibF.Proof.«gzfs.borrow-stable»

/-!
# gzlib.c: synchronous consumption of borrowed error text

The actual error handler does not call strerror. Its reads, malloc refusal,
owned-message formatting and cleanup keep the current external borrow stable.
The lifetime fact comes from executing this code, not a caller contract.
-/

namespace C.LibcBorrow
open Zlib.Gzguts Zlib.Gzlib Zlib.GzFs

theorem stable_ldS (p : GzStatePtr) : StableM (ldS p) := by
  intro h value after hr
  unfold ldS ldGzState at hr
  split at hr
  · contradiction
  · split at hr
    · cases hr; rfl
    · contradiction

theorem stable_stGzState (p : GzStatePtr) (s : GzState) : StableM (stGzState p s) := by
  intro h value after hr
  cases p with
  | none => cases hr
  | some p =>
    cases p with
    | tab i =>
      unfold stGzState at hr
      simp only [GzStateRef.get, GzStateRef.isRo, GzStateRef.put, Bool.false_eq_true, ite_false] at hr
      split at hr
      · cases hr; split <;> rfl
      · contradiction

theorem stable_updS (p : GzStatePtr) (f : GzState → GzState) : StableM (updS p f) := by
  unfold updS
  exact StableM.bind (stable_ldS _) (fun _ => stable_stGzState _ _)

/-- An exact source tail, used only to keep shared continuations small. -/
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

/-- Kernel source identity retains the complete actual statement order. -/
private theorem error_source_tail (p : GzStatePtr) (err : Int32) (msg : BPtr) :
    gz_error p err msg = (do
      let s ← ldS p
      if s.msg != .null then
        if s.err != Z_MEM_ERROR then freeB s.msg
        updS p fun s => { s with msg := .null }
      errorTail p err msg) := rfl

private theorem stable_errorTail (p : GzStatePtr) (err : Int32) (msg : BPtr) :
    StableM (errorTail p err msg) := by
  unfold errorTail
  apply StableM.bind (stable_updS _ _)
  intro _
  apply StableM.ite
  · exact StableM.pure _
  · apply StableM.ite
    · exact StableM.pure _
    · apply StableM.bind (stable_ldS _)
      intro current
      apply StableM.bind (stable_strlenB _)
      intro pathLen
      apply StableM.bind (stable_strlenB _)
      intro msgLen
      apply StableM.bind (stable_allocB _)
      intro allocated
      apply StableM.bind (stable_updS _ _)
      intro _
      apply StableM.ite
      · apply StableM.bind (stable_updS _ _)
        intro _
        exact StableM.pure _
      · apply StableM.bind (stable_ldS _)
        intro owned
        apply StableM.bind (stable_strLitRef _)
        intro fmt
        apply StableM.bind (stable_strLitRef _)
        intro sep
        apply StableM.bind (stable_strlenB _)
        intro pathLen1
        apply StableM.bind (stable_strlenB _)
        intro msgLen1
        apply StableM.bind (stable_snprintf _ _ _ _)
        intro _
        exact StableM.pure _

/-- The complete actual `gz_error` keeps borrow metadata on every returning
execution, including failed message allocation and an already existing message.
The exact source-tail identity prevents helper proofs from hiding C statements. -/
theorem gz_error_borrow_stable (p : GzStatePtr) (err : Int32) (msg : BPtr) :
    StableM (gz_error p err msg) := by
  rw [error_source_tail]
  apply StableM.bind (stable_ldS _)
  intro s
  dsimp only
  apply StableM.ite
  · try dsimp only
    apply StableM.ite
    · apply StableM.bind (stable_freeB _)
      intro _
      apply StableM.bind (stable_updS _ _)
      intro _
      exact stable_errorTail _ _ _
    · apply StableM.bind (stable_updS _ _)
      intro _
      exact stable_errorTail _ _ _
  · exact stable_errorTail _ _ _

#print axioms gz_error_borrow_stable
end C.LibcBorrow
