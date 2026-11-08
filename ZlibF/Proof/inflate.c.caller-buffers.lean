import ZlibF.Proof.«inflate.c.slow-step»
import ZlibF.Spec.Public.History

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The existing public caller-range premise excludes the stream's actual
owned window, for every supported caller byte view. -/
theorem callerRange_private_window {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (good : Good h r zs z s) {pointer : BPtr} {size : Nat} {writing : Bool}
    (range : CallerRange h r pointer size writing) {dest : BRef} {offset : Nat}
    (ptr : pointer = .ref dest offset) :
    ∀ w, s.window = .ref (.blk w) 0 → dest ≠ .blk w := by
  rcases range with null | ⟨_, _, unowned⟩
  · rw [ptr] at null
    cases null
  · intro w window same
    have root : ByteRoot pointer w := by rw [ptr, same]; exact rfl
    apply unowned w root
    exact ⟨z, good.live.hz, Or.inl ⟨zs, s, good.live.zst, good.live.hs, Or.inr window⟩⟩

/-- Extract the slow decoder's output view and private-window separation
from the public range. Cursor accounting remains an internal loop fact. -/
theorem callerRange_slow_output {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (good : Good h r zs z s) (l : IL) (range : CallerRange h r l.put l.left.toNat true)
    (nonnull : l.put ≠ .null) (count : l.left.toNat ≤ l.out_.toNat)
    (produced : ∀ dest offset, l.put = .ref dest offset → l.out_.toNat - l.left.toNat ≤ offset) :
    ∃ (dest : BRef) (array : Array UInt8) (outOffset : Nat),
      l.put = .ref dest outOffset ∧ Space.get h dest = some array ∧ Space.ro h dest = false ∧
      outOffset + l.left.toNat ≤ array.size ∧ l.left.toNat ≤ l.out_.toNat ∧
      l.out_.toNat - l.left.toNat ≤ outOffset ∧
      (∀ w, s.window = .ref (.blk w) 0 → dest ≠ .blk w) := by
  have writable : Writable h l.put l.left.toNat := by
    rcases range with null | ⟨_, write, _⟩
    · exact False.elim (nonnull null)
    · exact write rfl
  rcases writable with ⟨null, _⟩ | ⟨dest, outOffset, array, ptr, get, write, room⟩
  · exact False.elim (nonnull null)
  · exact ⟨dest, array, outOffset, ptr, get, write, room, count, produced dest outOffset ptr,
      callerRange_private_window good range ptr⟩

/-- The complete actual slow step uses the existing public caller-buffer domain. -/
theorem inflate_LEN_slow_step_buffers {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    {l : IL} {bs : List UInt8} (B : BitInv h l bs) (sane : s.sane ≠ 0)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true)
    (separate : ZlibF.Spec.Public.Separate l.next l.have_.toNat l.put l.left.toNat)
    (range : CallerRange h r l.put l.left.toNat true) (nonnull : l.put ≠ .null)
    (count : l.left.toNat ≤ l.out_.toNat)
    (produced : ∀ dest offset, l.put = .ref dest offset → l.out_.toNat - l.left.toNat ≤ offset) :
    ∃ outcome regs after stream state used consumed,
      used ≤ bs.length ∧ consumed ≤ 48 ∧
      runX (inflate_LEN c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ BitInv after regs (bs.drop used) ∧
      Zlib.Inflate.Proofs.stream regs (bs.drop used) = (Zlib.Inflate.Proofs.stream l bs).drop consumed ∧
      (outcome = .error Ex.leave ∨
        (outcome = .ok () ∧ (state.mode = LIT ∨ state.mode = TYPE ∨ state.mode = BAD)) ∨
        (outcome = .ok () ∧ (state.mode = LEN ∨ state.mode = MATCH) ∧ regs.left.toNat < l.left.toNat)) := by
  apply inflate_LEN_slow_step E good tables B sane slow separate
  intro _
  exact callerRange_slow_output good l range nonnull count produced

end Zlib.Inflate.Proofs
