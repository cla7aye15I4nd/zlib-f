import ZlibF.Proof.«inflate.c.main.macros»

/-!
# inflate.c: the modes that touch only the registers and the state record

`DONE` and `LIT`. A mode theorem is stated for a mode function run by `runX` from registers `l` on heap `h`; the
state record is `s` at table entry `zs` (`c.st = some (.tab zs)`). The heap after a write is `setI` of the base module.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec

theorem wrS_tab {h : Heap} {zs : Nat} {s : InflateState} (e : h.istates zs = some s) (f : InflateState → InflateState) :
    wrS (some (.tab zs)) f h = .ok ((), setI h zs (f s)) := by
  unfold wrS
  rw [bind_app, ldInflateState_tab e]
  simp only []
  rw [stInflateState_tab e]
  rfl

theorem setMode_tab {h : Heap} {zs : Nat} {s : InflateState} (e : h.istates zs = some s) (m : UInt32) :
    setMode (some (.tab zs)) m h = .ok ((), setI h zs { s with mode := m }) := wrS_tab e _

/-- `case DONE:` -- `ret = Z_STREAM_END; goto inf_leave`. -/
theorem inflate_DONE_run (c : Ctx) (l : IL) (h : Heap) :
    runX (inflate_DONE c) l h = .ok ((.error Ex.leave, { l with ret := Z_STREAM_END }), h) := rfl

/-- `case LIT:` with no room (`left = 0`): `goto inf_leave`, nothing changes. -/
theorem inflate_LIT_full (c : Ctx) (l : IL) (h : Heap) (h0 : l.left = 0) :
    runX (inflate_LIT c) l h = .ok ((.error Ex.leave, l), h) := by
  unfold inflate_LIT
  rw [runX_bind, runX_get]
  simp [h0, runX_throw, runX_bind]

/-- `case LIT:` with room: the byte `state->length` is stored at `put` (a writable caller byte block), `put` and `left`
move, and the mode becomes `LEN`. The only heap changes are that byte block and the state record. -/
theorem inflate_LIT_run {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState} {b off : Nat} {a : Array UInt8}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s) (hl : l.left ≠ 0) (hp : l.put = .ref (.blk b) off)
    (ha : h.bytes b = some a) (hro : Space.ro h (BRef.blk b) = false) (hoff : off < a.size) :
    runX (inflate_LIT c) l h = .ok ((.ok (), { l with put := .ref (.blk b) (off + 1), left := l.left - 1 }),
      setI { h with bytes := upd h.bytes b (some (a.set! off s.length.toUInt8)) } zs { s with mode := LEN }) := by
  have hg : (Space.get h (BRef.blk b) : Option (Array UInt8)) = some a := ha
  have hst : store8 l.put s.length.toUInt8 h = .ok ((), { h with bytes := upd h.bytes b (some (a.set! off s.length.toUInt8)) }) := by
    rw [hp]; exact Ptr.store_ok hg hro hoff
  have hadd : OkOn { h with bytes := upd h.bytes b (some (a.set! off s.length.toUInt8)) } (l.put.add 1) (.ref (.blk b) (off + 1)) := by
    rw [hp]
    have hg' : (Space.get { h with bytes := upd h.bytes b (some (a.set! off s.length.toUInt8)) } (BRef.blk b) : Option (Array UInt8))
        = some (a.set! off s.length.toUInt8) := by
      show (upd h.bytes b (some (a.set! off s.length.toUInt8))) b = _
      simp
    exact Ptr.add_nat_ok (n := 1) hg' (by simp; omega)
  have hs' : ({ h with bytes := upd h.bytes b (some (a.set! off s.length.toUInt8)) } : Heap).istates zs = some s := hs
  have hld : ldInflateState c.st h = .ok (s, h) := by rw [hc]; exact ldInflateState_tab hs
  have hne : (l.left == 0) = false := by simpa using hl
  unfold inflate_LIT
  rw [runX_bind, runX_get]
  simp only [hne, Bool.false_eq_true, ↓reduceIte]
  rw [runX_bind, runX_lift_ok hld]
  simp only []
  rw [runX_bind, runX_lift_ok hst]
  simp only []
  rw [runX_bind, runX_lift_ok hadd]
  simp only []
  rw [runX_bind, runX_set]
  simp only []
  rw [hc]
  have := runX_lift_ok (m := setMode (some (.tab zs)) LEN) (setMode_tab hs' LEN) { l with put := .ref (.blk b) (off + 1), left := l.left - 1 }
  exact this

end Zlib.Inflate.Proofs
