import ZlibF.Proof.«inflate.c.sync-first-origin»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Pointer arithmetic can fault, but any returned result has unchanged
storage. This observer imposes no caller-buffer representation restriction. -/
theorem sync_pointer_add_heap {h after : Heap} {pointer result : BPtr} {offset : Int}
    (actual : C.run (Ptr.add pointer offset) h = .ok (result, after)) : after = h := by
  change Ptr.add pointer offset h = _ at actual
  unfold Ptr.add at actual
  repeat' first | split at actual | (cases actual <;> rfl)

/-- A successful byte load only observes the heap. -/
theorem sync_pointer_load_heap {h after : Heap} {pointer : BPtr} {byte : UInt8}
    (actual : C.run (load8 pointer) h = .ok (byte, after)) : after = h := by
  change Ptr.load pointer h = _ at actual
  unfold Ptr.load at actual
  repeat' first | split at actual | (cases actual <;> rfl)

/-- A successful indexed read only observes the heap, including represented
embedded/static byte views and the source model's null arithmetic cases. -/
theorem sync_index8_heap {h after : Heap} {pointer : BPtr} {offset : Int} {byte : UInt8}
    (actual : C.run (index8 pointer offset) h = .ok (byte, after)) : after = h := by
  change Ptr.index pointer offset h = _ at actual
  unfold Ptr.index at actual
  rw [bind_app] at actual
  cases added : Ptr.add pointer offset h with
  | error fault => rw [added] at actual; cases actual
  | ok pair =>
    obtain ⟨result, middle⟩ := pair
    rw [added] at actual
    have same := sync_pointer_add_heap added
    subst middle
    exact sync_pointer_load_heap actual

/-- Every fault-free execution of the actual sync pattern search leaves
the heap unchanged. It does not assume readable input, termination or the
callee's desired result; the public history supplies an actual execution. -/
theorem syncsearch_heap_unchanged {h after : Heap} {pointer : BPtr} {len start used found : UInt32}
    (actual : C.run (syncsearch start pointer len) h = .ok ((used, found), after)) : after = h := by
  let condition : UInt32 × UInt32 → M (Bool × (UInt32 × UInt32)) :=
    fun (next, got) => pure (next < len && got < 4, (next, got))
  let body : UInt32 × UInt32 → M (UInt32 × UInt32) := fun (next, got) => do
    let byte ← index8 pointer next.toNat
    let found := if byte.toNat == (if got < 2 then 0 else 0xff) then got + 1
      else if byte != 0 then 0 else 4 - got
    pure (next + 1, found)
  have loop : ∀ count state before result final,
      cwhile.go condition body count state before = .ok (result, final) → final = before := by
    intro count
    induction count with
    | zero =>
      intro state before result final run
      simp only [cwhile.go] at run
      cases run
    | succ count ih =>
      intro state before result final run
      obtain ⟨next, got⟩ := state
      simp only [cwhile.go, condition, bind_app, pure_app] at run
      split at run
      · simp only [body, bind_app] at run
        cases read : index8 pointer next.toNat before with
        | error fault => rw [read] at run; cases run
        | ok pair =>
          obtain ⟨byte, middle⟩ := pair
          have same := sync_index8_heap read
          subst middle
          rw [read] at run
          simp only [pure_app] at run
          exact ih _ _ _ _ run
      · cases run
        rfl
  change (syncsearch start pointer len) h = _ at actual
  unfold syncsearch at actual
  change (cwhile condition body (0, start) >>= fun result => pure result) h = _ at actual
  rw [bind_app] at actual
  cases searched : cwhile condition body (0, start) h with
  | error fault => rw [searched] at actual; cases actual
  | ok pair =>
    obtain ⟨result, middle⟩ := pair
    rw [searched] at actual
    have same := loop fuel (0, start) h result middle searched
    cases actual
    exact same

#print axioms syncsearch_heap_unchanged
end Zlib.Inflate.Proofs
