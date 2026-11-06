import ZlibF.Proof.«infback.c.macros»
import ZlibF.Proof.«inflate.c.main.simple»

/-!
# infback.c: `ROOM()` and the mode setters

`ROOM()` hands the full window to `out` and starts again at its beginning. The call-back sees the window as `len` readable
bytes; it may not change them (`CbContract`).
-/

namespace Zlib.Infback.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Infback Zlib.Infback.Spec

/-- `ROOM()` while there is room: nothing happens. -/
theorem ROOM_have (c : BCtx) {l : IL} {h : Heap} (hl : l.left ≠ 0) :
    runX (ROOM c) l h = .ok ((.ok (), l), h) := by
  have hb : (l.left == 0) = false := by simpa using hl
  unfold ROOM
  simp [runX_bind, runX_get, hb, hl, runX_pure]

/-- The heap `ROOM()` sets before it calls `out`: `state->whave = state->wsize`. -/
def roomHeap (h : Heap) (zs : Nat) (s : InflateState) : Heap := setI h zs { s with whave := s.wsize }

/-- **`ROOM()` with a full window.** The state is the record `s` at block `zs`, its window is `wsize` readable bytes. `out` is
called once on the window; it changes only its own blocks. If it returns 0 the fill restarts at the window, otherwise the call
ends with `Z_BUF_ERROR`. -/
theorem ROOM_run (c : BCtx) {win : Nat} {ownI ownO : Nat → Prop} {R : Heap → Prop}
    (hK : CbContract c.inCb c.inDesc c.outCb c.outDesc win ownI ownO R) {l : IL} {h : Heap} {zs : Nat}
    {s : InflateState} (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s) (hl : l.left = 0) (hR : R h)
    (hW : ReadableAt h s.window s.wsize.toNat) :
    ∃ r l' h', runX (ROOM c) l h = .ok ((r, l'), h') ∧ CbFrame ownO (roomHeap h zs s) h' ∧ R h' ∧
      ((r = .ok () ∧ l' = { l with put := s.window, left := s.wsize }) ∨
       (r = .error Ex.leave ∧ l' = { l with put := s.window, left := s.wsize, ret := Z_BUF_ERROR })) := by
  have hR1 : R (roomHeap h zs s) := (hK.local_ h (roomHeap h zs s) (fun b _ => rfl)).1 hR
  have hW1 : ReadableAt (roomHeap h zs s) s.window s.wsize.toNat := by
    obtain ⟨b, off, a, e, hb, hle⟩ := hW
    exact ⟨b, off, a, e, hb, hle⟩
  obtain ⟨r, h', he, fr, hR'⟩ := hK.outOk _ s.window s.wsize hR1 hW1
  have hld : ldInflateState c.st h = .ok (s, h) := by rw [hc]; exact ldInflateState_tab hs
  have hwr : wrS c.st (fun s => { s with whave := s.wsize }) h = .ok ((), roomHeap h zs s) := by
    rw [hc]; exact wrS_tab hs _
  have hb : (l.left == 0) = true := by simpa using hl
  have hcall : ∀ l1 : IL, runX (monadLift (c.outCb c.outDesc s.window s.wsize) : X Int32) l1 (roomHeap h zs s) =
      .ok ((.ok r, l1), h') := fun l1 => runX_lift_ok he l1
  by_cases hr0 : r = 0
  · refine ⟨.ok (), { l with put := s.window, left := s.wsize }, h', ?_, fr, hR', Or.inl ⟨rfl, rfl⟩⟩
    unfold ROOM
    simp [runX_bind, runX_get, hb, hl, runX_lift_ok hld, runX_set, runX_lift_ok hwr, hcall, hr0, runX_pure]
  · refine ⟨.error Ex.leave, { l with put := s.window, left := s.wsize, ret := Z_BUF_ERROR }, h', ?_, fr, hR',
      Or.inr ⟨rfl, rfl⟩⟩
    unfold ROOM
    simp [runX_bind, runX_get, hb, hl, runX_lift_ok hld, runX_set, runX_lift_ok hwr, hcall, hr0, runX_modify, runX_throw]

end Zlib.Infback.Proofs
