import ZlibF.Proof.«uncompr.c.compat-tail»
import ZlibF.Proof.«uncompr.c.caller-objects»

/-!
# The actual counted call and compatibility return continuation

On the real prepared heap, the actual counted callee preserves both external
cells through its complete execution. Its returned local cells then feed both
external Stores and both temporary frees. No callee specification is assumed.
The complete source equation retains the original allocation prefix. Deriving
this prepared heap from that prefix and the public format goal remain separate.
-/

namespace Zlib.Uncompr.Proof.CompatibilityContinuation
open C Zlib.Gzguts ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs
open Zlib.Uncompr.Proof.CallerCells Zlib.Uncompr.Proof.CallerObjects

def continuation (dest destLen source sourceLen got used : BPtr) : M Int32 := do
  let rc ← uncompress2_z dest got source used
  Zlib.Uncompr.Proof.CompatibilityTail.finish destLen sourceLen got used rc

theorem uncompress2_continuation_source : uncompress2 = (fun dest destLen source sourceLen => do
    let got ← allocLocal 8
    let used ← allocLocal 8
    store64 got (← load64 destLen)
    store64 used (← load64 sourceLen)
    continuation dest destLen source sourceLen got used) := by
  unfold uncompress2 continuation Zlib.Uncompr.Proof.CompatibilityTail.finish
  with_reducible rfl

private theorem outside_separate (p : BPtr) (count block : Nat)
    (outside : ∀ off, p ≠ .ref (.blk block) off) :
    Separate p count (.ref (.blk block) 0) 8 := by
  cases p with
  | null => simp [Separate]
  | ref ref off =>
    have different : ref ≠ .blk block := by intro same; subst ref; exact outside off rfl
    exact Or.inr (Or.inr (Or.inl different))

theorem continuation_safe (h : Heap) (gotBlock usedBlock : Nat) (dest destLen source sourceLen : BPtr)
    (n capacity : UInt64) (xs : List UInt8)
    (fresh : Fresh h) (uniq : Uniq h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (sourceCell : LengthCell h sourceLen n) (destCell : LengthCell h destLen capacity)
    (gotCell : LengthCell h (.ref (.blk gotBlock) 0) capacity)
    (usedCell : LengthCell h (.ref (.blk usedBlock) 0) n)
    (readable : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat)
    (gotOutput : Separate (.ref (.blk gotBlock) 0) 8 dest capacity.toNat)
    (usedOutput : Separate (.ref (.blk usedBlock) 0) 8 dest capacity.toNat)
    (sourceOutput : Separate sourceLen 8 dest capacity.toNat)
    (destOutput : Separate destLen 8 dest capacity.toNat)
    (distinct : gotBlock ≠ usedBlock) (cellSeparate : Separate sourceLen 8 destLen 8)
    (sourceGot : ∀ off, sourceLen ≠ .ref (.blk gotBlock) off)
    (sourceUsed : ∀ off, sourceLen ≠ .ref (.blk usedBlock) off)
    (destGot : ∀ off, destLen ≠ .ref (.blk gotBlock) off)
    (destUsed : ∀ off, destLen ≠ .ref (.blk usedBlock) off)
    (validInput : source = .null → n = 0) (validOutput : dest = .null → capacity = 0) :
    ∃ rc after consumed produced,
      C.run (continuation dest destLen source sourceLen (.ref (.blk gotBlock) 0) (.ref (.blk usedBlock) 0)) h = .ok (rc, after) ∧
      LengthCell after sourceLen consumed ∧ LengthCell after destLen produced ∧
      consumed.toNat ≤ n.toNat ∧ produced.toNat ≤ capacity.toNat ∧
      LiveChange h after (fun _ => False) (fun x => x = gotBlock ∨ x = usedBlock) ∧
      Uniq after ∧ Fresh after ∧ ZlibF.PlatformMemory.ByteObjectsFit after := by
  have localSeparate : Separate (.ref (.blk usedBlock) 0) 8 (.ref (.blk gotBlock) 0) 8 := by
    simp [Separate, Ne.symm distinct]
  obtain ⟨rc, inner, consumed, produced, run, usedAfter, gotAfter, inputBound, outputBound, live, unique, freshAfter, fit⟩ :=
    uncompress2_z_caller_cells h source dest (.ref (.blk usedBlock) 0) (.ref (.blk gotBlock) 0) n capacity xs
      fresh uniq globals platform usedCell gotCell readable writable separate usedOutput gotOutput localSeparate validInput validOutput
  have sourceObject := uncompress2_z_object h inner source dest (.ref (.blk usedBlock) 0) (.ref (.blk gotBlock) 0)
    n capacity xs rc fresh uniq globals platform usedCell gotCell readable writable separate
    usedOutput gotOutput localSeparate validInput validOutput sourceLen 8 (lengthBytes n) true
    sourceCell.1 (fun _ => sourceCell.2) sourceOutput
    (outside_separate sourceLen 8 usedBlock sourceUsed) (outside_separate sourceLen 8 gotBlock sourceGot) run
  have destObject := uncompress2_z_object h inner source dest (.ref (.blk usedBlock) 0) (.ref (.blk gotBlock) 0)
    n capacity xs rc fresh uniq globals platform usedCell gotCell readable writable separate
    usedOutput gotOutput localSeparate validInput validOutput destLen 8 (lengthBytes capacity) true
    destCell.1 (fun _ => destCell.2) destOutput
    (outside_separate destLen 8 usedBlock destUsed) (outside_separate destLen 8 gotBlock destGot) run
  have sourceAfter : LengthCell inner sourceLen n := ⟨sourceObject.1, sourceObject.2 rfl⟩
  have destAfter : LengthCell inner destLen capacity := ⟨destObject.1, destObject.2 rfl⟩
  obtain ⟨_first, _second, after, tailRun, _storeSource, _storeDest, sourceFinal, destFinal,
    tailLedger, uniqueFinal, freshFinal, fitFinal⟩ :=
    Zlib.Uncompr.Proof.CompatibilityTail.finish_safe inner gotBlock usedBlock destLen sourceLen
      n capacity produced consumed rc unique freshAfter fit sourceAfter destAfter gotAfter usedAfter distinct cellSeparate
      sourceGot sourceUsed destGot destUsed
  refine ⟨rc, after, consumed, produced, ?_, sourceFinal, destFinal, inputBound, outputBound,
    ?_, uniqueFinal, freshFinal, fitFinal⟩
  · simp only [C.run] at run tailRun
    simpa only [C.run, continuation, bind_app, run] using tailRun
  · intro x
    have sameLive : inner.live x ↔ h.live x := by
      simpa only [not_false_eq_true, and_true, or_false] using live x
    simpa only [sameLive] using tailLedger x

#print axioms uncompress2_continuation_source
#print axioms continuation_safe
end Zlib.Uncompr.Proof.CompatibilityContinuation
