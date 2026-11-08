import ZlibF.Proof.«inflate.c.match-copy»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- Actual MATCH suffix after selecting and bounding its copy segment. -/
def matchEmitFrom (c : Ctx) (l : IL) (copy : UInt32) (from_ : BPtr) : X Unit := do
  set { l with left := l.left - copy, copy := copy, from_ := from_ }
  wrS c.st fun s => { s with length := s.length - copy }
  matchCopyLoop
  if (← rdS c.st (·.length)) == 0 then setMode c.st LEN

def matchEmit (c : Ctx) (copy : UInt32) (from_ : BPtr) : X Unit := do
  let l ← get
  matchEmitFrom c l copy from_

/-- The exact scalar state after one positive MATCH segment. -/
def matchEmitState (s : InflateState) (copy : UInt32) : InflateState :=
  let next := { s with length := s.length - copy }
  if next.length == 0 then { next with mode := LEN } else next

/-- Execute the actual bounded segment, including both counter updates,
the complete overlapping copy loop and the final mode test. -/
theorem matchEmit_run {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) {l : IL} {dest source : BRef}
    {output saved : Array UInt8} {outOffset sourceOffset : Nat} {copy : UInt32}
    (put : l.put = .ref dest outOffset)
    (outGet : Space.get h dest = some output) (write : Space.ro h dest = false)
    (sourceGet : Space.get h source = some (if source = dest then output else saved))
    (outBound : outOffset + copy.toNat ≤ output.size)
    (sourceBound : sourceOffset + copy.toNat ≤ (if source = dest then output else saved).size)
    (positive : 0 < copy.toNat) :
    runX (matchEmit c copy (.ref source sourceOffset)) l h =
      .ok ((.ok (), { l with left := l.left - copy, copy := 0, put := .ref dest (outOffset + copy.toNat), from_ := .ref source (sourceOffset + copy.toNat) }),
        setI (Space.put h dest (ZlibF.Math.InflateMatchCopy.copy (decide (source = dest)) saved
          copy.toNat sourceOffset outOffset output)) zs (matchEmitState s copy)) := by
  let state := { s with length := s.length - copy }
  let mid := setI h zs state
  let prepared := { l with left := l.left - copy, copy := copy, from_ := .ref source sourceOffset }
  let array := ZlibF.Math.InflateMatchCopy.copy (decide (source = dest)) saved copy.toNat sourceOffset outOffset output
  let regs := { l with left := l.left - copy, copy := 0, put := .ref dest (outOffset + copy.toNat), from_ := .ref source (sourceOffset + copy.toNat) }
  let heap := setI (Space.put h dest array) zs state
  have copied := matchCopyLoop_run (h := mid) (l := prepared) (saved := saved)
    (by exact put) rfl (by simpa only [mid, byte_view_get_setI] using outGet)
    (by simpa only [mid, byte_view_ro_setI] using write)
    (by simpa only [mid, byte_view_get_setI] using sourceGet) outBound sourceBound rfl positive
  have runCopy : runX matchCopyLoop prepared mid = .ok ((.ok (), regs), heap) := by
    simpa only [prepared, mid, byte_view_put_setI] using copied
  have afterEnv : Env c heap r zs z state :=
    ⟨E.strm, E.st, by simpa only [heap, ZStreamRef.get_setI, byte_view_put_stream] using E.hz, by simp [heap]⟩
  unfold matchEmit matchEmitFrom
  rw [runX_bind, runX_get]
  simp only []
  rw [runX_bind, runX_set]
  simp only []
  rw [runX_bind, runX_wrS E]
  simp only []
  rw [runX_bind, runCopy]
  simp only []
  rw [runX_bind, runX_rdS afterEnv]
  simp only []
  by_cases empty : state.length == 0
  · simp only [empty, ↓reduceIte]
    rw [runX_setMode afterEnv]
    simp only [heap, setI_setI, matchEmitState, state, empty, ↓reduceIte]
    rfl
  · simp only [empty, Bool.false_eq_true, ↓reduceIte, runX_pure]
    simp only [heap, matchEmitState, state, empty, Bool.false_eq_true, ↓reduceIte]
    rfl

end Zlib.Inflate.Proofs
