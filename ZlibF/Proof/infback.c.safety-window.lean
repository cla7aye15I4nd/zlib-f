import ZlibF.Proof.«infback.c.safety-modes»

/-!
# infback.c: a store of the decoder into the window, on the loop invariant

The decoder writes the window (the caller's byte block `w`, slice `[woff, woff + n)`) and nothing
else of the caller's memory. `PInv.storeWindow`: when a new array of the same size agrees with the
old one outside the slice, the invariant holds again. The input chunk is outside the slice
(`Separate`), restoring the slice gives back the old heap exactly (so the protocol's invariant
holds by its locality), and the step changes only the window's block.
-/

namespace Zlib.Infback.Safety
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Inflate Zlib.Inflate.Proofs Zlib.Infback Zlib.Infback.Proofs
open Zlib.Inflate.Spec (setI)
set_option autoImplicit false

/-- Two arrays that agree on `[o, o + k)` give the same `k` bytes from `o`. -/
theorem take_drop_congr {a a' : Array UInt8} {o k : Nat} (size : a'.size = a.size)
    (same : ∀ j, o ≤ j → j < o + k → a'[j]? = a[j]?) :
    (a'.toList.drop o).take k = (a.toList.drop o).take k := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_take, List.getElem?_take, List.getElem?_drop, List.getElem?_drop]
  split
  · simp only [Array.getElem?_toList]
    exact same (o + j) (Nat.le_add_right _ _) (by omega)
  · rfl

/-- Restoring a slice of an array that changed only inside it gives the old array. -/
theorem restore_slice {a a' : Array UInt8} {off n : Nat} (size : a'.size = a.size) (room : off + n ≤ a.size)
    (outside : ∀ j, j < off ∨ off + n ≤ j → a'[j]? = a[j]?) :
    a'.extract 0 off ++ a.extract off (off + n) ++ a'.extract (off + n) a'.size = a := by
  apply Array.ext_getElem?
  intro j
  rw [Array.getElem?_append, Array.getElem?_append]
  simp only [Array.size_append, Array.size_extract]
  by_cases h1 : j < off
  · rw [if_pos (by omega), if_pos (by omega), Array.getElem?_extract]
    simp only [Nat.zero_add]
    rw [if_pos (by omega)]
    exact outside j (Or.inl h1)
  · by_cases h2 : j < off + n
    · rw [if_pos (by omega), if_neg (by omega), Array.getElem?_extract, if_pos (by omega)]
      congr 1; omega
    · rw [if_neg (by omega), Array.getElem?_extract]
      by_cases h3 : j < a.size
      · rw [if_pos (by omega)]
        rw [show off + n + (j - (min off a'.size - 0 + (min (off + n) a.size - off))) = j by omega]
        exact outside j (Or.inr (by omega))
      · rw [if_neg (by omega)]
        simp; omega

/-- The heap after the decoder stores `a'` as the window's block. -/
def winHeap (h : Heap) (w : Nat) (a' : Array UInt8) : Heap := { h with bytes := upd h.bytes w (some a') }

theorem get_winHeap_ne {h : Heap} {w : Nat} {a' : Array UInt8} {ref : BRef} (ne : ref ≠ .blk w) :
    (Space.get (winHeap h w a') ref : Option (Array UInt8)) = Space.get h ref := by
  cases ref with
  | blk b =>
    have : b ≠ w := fun e => ne (by rw [e])
    show (upd h.bytes w (some a')) b = h.bytes b
    rw [upd_ne _ _ _ _ this]
  | _ => rfl

theorem shape_winHeap {h : Heap} {w : Nat} {a a' : Array UInt8} (get : h.bytes w = some a) :
    Zlib.Inflate.Proofs.Shape h (winHeap h w a') := by
  intro b
  by_cases e : b = w
  · subst e; simp [winHeap, get]
  · simp [winHeap, upd_ne _ _ _ _ e]

/-- **A store of the decoder into the window slice keeps `PInv`.** -/
theorem PInv.storeWindow {c : BCtx} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat} {pr : Proto c r i window n}
    {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log) {w woff : Nat}
    (hw : window = .ref (.blk w) woff) {a a' : Array UInt8} (get : h.bytes w = some a) (size : a'.size = a.size)
    (outside : ∀ j, j < woff ∨ woff + n ≤ j → a'[j]? = a[j]?) : PInv c pr h0 (winHeap h w a') l log := by
  classical
  obtain ⟨z, s, valid, win, sz⟩ := I.valid
  obtain ⟨hz, hs, zst, za, zf, wf, lo, hi, ws, nn, wr, fresh, uniq, globals⟩ := valid
  have shape := shape_winHeap (a' := a') get
  have room : woff + n ≤ a.size := by
    rw [win, sz, hw] at wr
    rcases wr with ⟨null, -⟩ | ⟨ref, off, a0, ptr, g, -, rm⟩
    · cases null
    · injection ptr with e1 e2; subst e1 e2
      change h.bytes w = some a0 at g
      rw [get] at g; injection g with e; subst e; exact rm
  have ro0 : h.ro w = false := by
    rw [win, sz, hw] at wr
    rcases wr with ⟨null, -⟩ | ⟨ref, off, a0, ptr, -, ro, -⟩
    · cases null
    · injection ptr with e1 _; subst e1; exact ro
  have valid' : BackValid (winHeap h w a') r i z s := by
    refine ⟨by cases r <;> exact hz, hs, zst, za, zf, wf, lo, hi, ws, nn, ?_,
      Zlib.Inflate.Proofs.Shape.fresh shape rfl fresh, Zlib.Inflate.Proofs.Shape.uniq shape uniq, globals⟩
    rw [win, sz, hw]
    exact Or.inr ⟨.blk w, woff, a', rfl, by simp [Space.get, winHeap], ro0, by rw [size]; exact room⟩
  have restore : restoreWindow h (winHeap h w a') window n = h := by
    unfold restoreWindow
    rw [hw]
    simp only []
    have g1 : (Space.get h (BRef.blk w) : Option (Array UInt8)) = some a := get
    have g2 : (Space.get (winHeap h w a') (BRef.blk w) : Option (Array UInt8)) = some a' := by simp [Space.get, winHeap]
    rw [g1, g2]
    simp only []
    rw [restore_slice size room outside]
    show { winHeap h w a' with bytes := upd (winHeap h w a').bytes w (some a) } = h
    simp only [winHeap, upd_upd]
    rw [upd_self h.bytes w a get]
  have proto' : pr.invariant (winHeap h w a') log := by
    refine (pr.local_ h _ log ?_).1 I.proto
    rw [restore]
    exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  have held' : ChunkOk (winHeap h w a') r i window n log.active log.held := by
    intro ne
    obtain ⟨bytes, sep, roots⟩ := I.held ne
    refine ⟨?_, sep, roots⟩
    rcases bytes with x | ⟨ref, off, b0, ptr, g, rm, xs⟩
    · exact Or.inl x
    · refine Or.inr ⟨ref, off, ?_, ptr, ?_, ?_, ?_⟩
      · exact if ref = .blk w then a' else b0
      · by_cases e : ref = .blk w
        · subst e; simp [Space.get, winHeap]
        · rw [if_neg e, get_winHeap_ne e]; exact g
      · by_cases e : ref = .blk w
        · rw [if_pos e, size]
          subst e
          change h.bytes w = some b0 at g
          rw [get] at g; injection g with e; subst e; exact rm
        · rw [if_neg e]; exact rm
      · by_cases e : ref = .blk w
        · rw [if_pos e]
          subst e
          change h.bytes w = some b0 at g
          rw [get] at g; injection g with e; subst e
          rw [ptr, hw] at sep
          generalize hk : log.held.length = k at rm xs sep ⊢
          rw [xs]
          symm
          apply take_drop_congr size
          intro j lo' hi'
          apply outside
          rcases sep with z0 | z0 | sep
          · omega
          · omega
          · simp only [ne_eq, not_true_eq_false, false_or] at sep
            omega
        · rw [if_neg e]; exact xs
  have frame' : CallbackFrame pr.own h0 (winHeap h w a') r i window n := by
    refine CallbackFrame.trans I.frame ?_ (fun d => window_views (by rw [win, sz] at wr; exact wr) I.winRoot d)
    refine ⟨⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun b _ outside' => ?_⟩, fun _ => ?_⟩
    · have ne : b ≠ w := fun e => outside' (Or.inr (Or.inr (Or.inr (by rw [hw, e]; rfl))))
      exact ⟨by simp [winHeap, upd_ne _ _ _ _ ne], rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · obtain ⟨statics, allocs, garbages, nexts, counts, words, streams, gzheaders, istates, gzstates, ro⟩ :=
        restoreRegions_other h (winHeap h w a') [⟨window, n⟩]
      refine ⟨⟨statics.symm, allocs.symm, garbages.symm, by rw [nexts]; exact Nat.le_refl _,
        by rw [counts]; exact Nat.le_refl _, fun x _ outside' => ?_⟩, ?_⟩
      · refine ⟨?_, by rw [words]; rfl, by rw [streams]; rfl, by rw [gzheaders]; rfl, ?_, by rw [istates]; rfl,
          by rw [gzstates]; rfl, by rw [ro]; rfl⟩
        · rw [restoreRegions_bytes]; split
          · rfl
          · next notRoot =>
            have ne : x ≠ w := by
              intro e; subst e; apply notRoot
              exact ⟨⟨⟨window, n⟩, List.mem_singleton.mpr rfl, woff, hw⟩, by rw [get]; simp⟩
            simp [winHeap, upd_ne _ _ _ _ ne]
        · rw [restoreRegions_dstates]; split
          · show _ = h.dstates x
            cases e : h.dstates x <;> simp [winHeap, e]
          · rfl
      intro region member ref off b0 pointer g
      simp only [List.mem_singleton] at member
      subst member
      change window = .ref ref off at pointer
      rw [hw] at pointer
      injection pointer with e1 e2
      subst e1
      change h.bytes w = some b0 at g
      rw [get] at g; injection g with e; subst e
      refine ⟨a', by simp [Space.get, winHeap], size, fun j lt notCovered => outside j ?_⟩
      rcases Nat.lt_or_ge j woff with x | x
      · exact Or.inl x
      · right
        apply Nat.le_of_not_lt
        intro y
        exact notCovered ⟨⟨window, n⟩, List.mem_singleton.mpr rfl, woff, hw, x, y⟩
  exact
    { cstrm := I.cstrm, cst := I.cst, valid := ⟨z, s, valid', win, sz⟩, winRoot := I.winRoot, put := I.put,
      chunk := I.chunk, held := held', bits := I.bits, proto := proto', frame := frame',
      live := fun b o => (Zlib.Inflate.Proofs.Shape.live shape b).trans (I.live b o),
      mode := fun s1 g => I.mode s1 g,
      platform := I.platform, chunkBlk := I.chunkBlk, stOk := fun s1 g => I.stOk s1 g,
      fit := by
        intro ref b g
        by_cases e : ref = .blk w
        · subst e
          have g' : b = a' := by simpa [Space.get, winHeap] using g.symm
          subst g'
          rw [size]; exact I.fit (.blk w) a get
        · rw [get_winHeap_ne e] at g; exact I.fit ref b g }

end Zlib.Infback.Safety
