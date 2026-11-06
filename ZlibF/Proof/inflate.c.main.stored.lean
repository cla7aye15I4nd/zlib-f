import ZlibF.Proof.«inflate.c.main.type»

/-!
# inflate.c: `COPY_`, `COPY` and `STORED` (stored blocks)
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec

/-- The number of bytes `case COPY:` moves: `state->length` capped by `have` and then by `left`. -/
def copyAmt (len have_ left : UInt32) : UInt32 :=
  let c := if len > have_ then have_ else len
  if c > left then left else c

theorem copyAmt_le (len have_ left : UInt32) : (copyAmt len have_ left).toNat ≤ len.toNat ∧
    (copyAmt len have_ left).toNat ≤ have_.toNat ∧ (copyAmt len have_ left).toNat ≤ left.toNat := by
  unfold copyAmt
  simp only [gt_iff_lt, UInt32.lt_iff_toNat_lt]
  split <;> split <;> omega

/-- `case COPY:` with nothing left to copy: back to `TYPE`; `copy` is recorded as 0. -/
theorem inflate_COPY_done {c : Ctx} {h : Heap} {r zs z s} (E : Env c h r zs z s) (l : IL) (hz : s.length = 0) :
    runX (inflate_COPY c) l h = .ok ((.ok (), { l with copy := 0 }), setI h zs { s with mode := TYPE }) := by
  unfold inflate_COPY
  have hb : (s.length != 0) = false := by simp [hz]
  rw [runX_bind, runX_ldS E]
  simp only [hb, Bool.false_eq_true, ↓reduceIte]
  rw [runX_bind, runX_modify]
  simp only []
  rw [runX_setMode E]
  simp [hz]

/-- What `case COPY:` does once the amount `n` to copy is known. -/
def copyTail (c : Ctx) (n : UInt32) : X Unit := do
  let l ← get
  if n == 0 then
    set { l with copy := n }
    throw Ex.leave
  memcpyB l.put l.next n.toNat
  let nx ← l.next.add (n.toNat : Int)
  let pt ← l.put.add (n.toNat : Int)
  set { l with copy := n, have_ := l.have_ - n, next := nx, left := l.left - n, put := pt }
  wrS c.st fun s => { s with length := s.length - n }
  return

theorem inflate_COPY_split {c : Ctx} {h : Heap} {r zs z s} (E : Env c h r zs z s) (l : IL) (hnz : s.length ≠ 0) :
    runX (inflate_COPY c) l h = runX (copyTail c (copyAmt s.length l.have_ l.left)) l h := by
  have hb : (s.length != 0) = true := by simpa using hnz
  unfold inflate_COPY
  rw [runX_bind, runX_ldS E]
  simp only [hb, ↓reduceIte]
  rw [runX_bind, runX_get]
  simp only []
  unfold copyAmt
  by_cases c1 : s.length > l.have_ <;> by_cases c2 : l.have_ > l.left <;> by_cases c3 : s.length > l.left <;>
    simp [c1, c2, c3, copyTail]
  all_goals (split <;> simp_all [runX_bind, runX_set, runX_throw, runX_get, copyTail])

theorem copyTail_stall (c : Ctx) (l : IL) (h : Heap) :
    runX (copyTail c 0) l h = .ok ((.error Ex.leave, { l with copy := 0 }), h) := by
  unfold copyTail
  rw [runX_bind, runX_get]
  simp only [beq_self_eq_true, ↓reduceIte]
  rw [runX_bind, runX_set]
  simp only []
  rw [runX_bind, runX_throw]

/-- After writing the byte block `db`, every array keeps its size. -/
theorem get_after_put {h : Heap} {db : Nat} {da a' : Array UInt8} (hd : h.bytes db = some da) (hs : a'.size = da.size)
    {r : BRef} {a : Array UInt8} (hg : (Space.get h r : Option (Array UInt8)) = some a) :
    ∃ a2, (Space.get { h with bytes := upd h.bytes db (some a') } r : Option (Array UInt8)) = some a2 ∧ a2.size = a.size := by
  cases r with
  | blk b =>
    by_cases hb : b = db
    · subst hb
      refine ⟨a', ?_, ?_⟩
      · show (upd h.bytes b (some a')) b = _
        simp
      · have : a = da := by
          have : h.bytes b = some a := hg
          rw [hd] at this; exact (Option.some.inj this).symm
        subst this; exact hs
    · refine ⟨a, ?_, rfl⟩
      show (upd h.bytes db (some a')) b = _
      rw [upd_ne _ _ _ _ hb]; exact hg
  | str i => exact ⟨a, hg, rfl⟩
  | dstate_depth i => exact ⟨a, hg, rfl⟩
  | st_dist_code => exact ⟨a, hg, rfl⟩
  | st_length_code => exact ⟨a, hg, rfl⟩

end Zlib.Inflate.Proofs
