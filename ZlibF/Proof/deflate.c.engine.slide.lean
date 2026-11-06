import ZlibF.Proof.«deflate.c.engine.macros»
import ZlibF.Proof.«deflate.c.engine.chains»

/-!
# deflate.c, engine: `slide_hash`

`slide_hash` rescales `head` (`hash_size` entries) and `prev` (`w_size` entries): every entry `m` becomes
`m >= w_size ? m - w_size : NIL`, and `slid` becomes 1. Both loops are `do ... while (--n)` loops that walk a
pointer down from the end of the array; they run `n` times when `n >= 1`. The entries may hold any value (`prev` is
never cleared), so the theorem holds for every content of the two arrays.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate

/-- The body of the two loops of `slide_hash`, as in the translation. -/
def slBody (wsize : UInt32) : UInt32 × WPtr → M (UInt32 × WPtr) := fun (n, p) => do
  let p ← psub p 1
  let m : UInt32 := (← Ptr.load p).toUInt32
  Ptr.store p (if m ≥ wsize then (m - wsize).toUInt16 else (0 : UInt16))
  pure (n, p)

/-- The condition `while (--n)` of the two loops. -/
def slCond : UInt32 × WPtr → M (Bool × (UInt32 × WPtr)) := fun (n, p) => let n := n - 1; pure (n != 0, (n, p))

theorem slide_hash_unfold (s : DeflateStatePtr) : slide_hash s = (do
    let d ← ldDeflateState s
    let wsize : UInt32 := d.w_size
    let n : UInt32 := d.hash_size
    let p : WPtr ← padd d.head n.toNat
    let (_, _) ← cdoWhile (slBody wsize) slCond (n, p)
    let n : UInt32 := wsize
    let p : WPtr ← padd d.prev n.toNat
    let (_, _) ← cdoWhile (slBody wsize) slCond (n, p)
    wr s (fun d => { d with slid := 1 })) := rfl


theorem slideVal_eq (wsize : UInt32) (m : UInt16) :
    (if m.toUInt32 ≥ wsize then (m.toUInt32 - wsize).toUInt16 else (0 : UInt16)) = slideVal wsize m := by
  unfold slideVal; split <;> simp_all

theorem u32_sub_one_toNat (n : UInt32) (h : 1 ≤ n.toNat) : (n - 1).toNat = n.toNat - 1 := by
  rw [UInt32.toNat_sub_of_le]; · simp
  rw [UInt32.le_iff_toNat_le]; simpa using h

/-- **The loop of `slide_hash`** on one array: for `cnt >= 1` entries below the pointer, the loop does not fault and
slides each of the first `cnt` entries; the rest of the array and every other table stay as they were. The result is
the heap with the one block replaced. -/
theorem slide_loop {h0 : Heap} {b : Nat} {a0 : Array UInt16} (w : UInt32) (cnt : Nat)
    (hb : h0.words b = some a0) (hpos : 1 ≤ cnt) (hcs : cnt ≤ a0.size) (hc32 : cnt < 2 ^ 32) :
    ∃ a : Array UInt16, cdoWhile (slBody w) slCond (UInt32.ofNat cnt, Ptr.ref (WRef.blk b) cnt) h0 =
      .ok ((0, Ptr.ref (WRef.blk b) 0), { h0 with words := upd h0.words b (some a) }) ∧
      a.size = a0.size ∧ ∀ i, wfn a i = if i < cnt then slideVal w (wfn a0 i) else wfn a0 i := by
  let P : Nat → UInt32 × WPtr → Heap → Prop := fun k s h =>
    s.1.toNat = k + 1 ∧ s.2 = Ptr.ref (WRef.blk b) (k + 1) ∧ k + 1 ≤ cnt ∧
    ∃ a : Array UInt16, h = { h0 with words := upd h0.words b (some a) } ∧ a.size = a0.size ∧
      ∀ i, wfn a i = if k + 1 ≤ i ∧ i < cnt then slideVal w (wfn a0 i) else wfn a0 i
  let Q : UInt32 × WPtr → Heap → Prop := fun s h =>
    s = (0, Ptr.ref (WRef.blk b) 0) ∧
    ∃ a : Array UInt16, h = { h0 with words := upd h0.words b (some a) } ∧ a.size = a0.size ∧
      ∀ i, wfn a i = if i < cnt then slideVal w (wfn a0 i) else wfn a0 i
  -- one iteration of the body on a state satisfying the invariant for `k + 1` remaining iterations
  have body : ∀ k (n : UInt32) (a : Array UInt16), n.toNat = k + 1 → k + 1 ≤ cnt → a.size = a0.size →
      slBody w (n, Ptr.ref (WRef.blk b) (k + 1)) { h0 with words := upd h0.words b (some a) } =
        .ok ((n, Ptr.ref (WRef.blk b) k), { h0 with words := upd h0.words b (some (a.set! k (slideVal w (wfn a k)))) }) := by
    intro k n a hn hk hsz
    have hg : Space.get ({ h0 with words := upd h0.words b (some a) } : Heap) (WRef.blk b) = some a := by simp
    have hk' : k < a.size := by omega
    have hp : psub (Ptr.ref (WRef.blk b) (k + 1)) 1 { h0 with words := upd h0.words b (some a) } =
        .ok (Ptr.ref (WRef.blk b) k, { h0 with words := upd h0.words b (some a) }) := by
      have := psub_ok' (h := { h0 with words := upd h0.words b (some a) }) (r := WRef.blk b) (a := a)
        (off := k + 1) (n := 1) hg (by omega) (by omega)
      simpa using this
    have hl : Ptr.load (Ptr.ref (WRef.blk b) k) { h0 with words := upd h0.words b (some a) } =
        .ok (a[k], { h0 with words := upd h0.words b (some a) }) :=
      Ptr.load_ok (r := WRef.blk b) hg hk'
    have hst := Ptr.store_ok (h := { h0 with words := upd h0.words b (some a) }) (r := WRef.blk b) (a := a)
      (off := k) (v := slideVal w a[k]) hg (by simp) hk'
    simp only [slBody, bind_app, hp, hl, slideVal_eq, hst, pure_app]
    simp [wfn_getElem a k hk', upd_upd]
  have hs := cdoWhile_run (σ := UInt32 × WPtr) (body := slBody w) (cond := slCond) (h := h0) P Q
    (s := (UInt32.ofNat cnt, Ptr.ref (WRef.blk b) cnt)) (k := cnt - 1) ?_ ?_ ?_ ?_
  · obtain ⟨s', h', hrun, hq⟩ := hs
    obtain ⟨hs', a, hh', hsz, hw⟩ := hq
    subst hs' hh'
    exact ⟨a, hrun, hsz, hw⟩
  · -- the step
    intro k s h hP
    obtain ⟨hn, hp, hkc, a, rfl, hsz, hw⟩ := hP
    obtain ⟨n, p⟩ := s
    simp only at hn hp
    subst hp
    have hb' := body (k + 1) n a hn hkc hsz
    have hn1 : (n - 1).toNat = k + 1 := by rw [u32_sub_one_toNat n (by omega)]; omega
    refine ⟨(n, Ptr.ref (WRef.blk b) (k + 1)),
      { h0 with words := upd h0.words b (some (a.set! (k + 1) (slideVal w (wfn a (k + 1))))) },
      (n - 1, Ptr.ref (WRef.blk b) (k + 1)),
      { h0 with words := upd h0.words b (some (a.set! (k + 1) (slideVal w (wfn a (k + 1))))) }, hb', ?_, ?_⟩
    · simp only [slCond, pure_app]
      have : (n - 1 != 0) = true := by
        simp only [bne_iff_ne, ne_eq]; intro h; rw [h] at hn1; simp at hn1
      rw [this]
    · refine ⟨hn1, rfl, by omega, a.set! (k + 1) (slideVal w (wfn a (k + 1))), rfl, by simp [hsz], ?_⟩
      intro i
      rw [wfn_set _ _ _ (by omega)]
      by_cases hi : i = k + 1
      · subst hi
        rw [hw (k + 1)]
        have : ¬ (k + 1 + 1 ≤ k + 1 ∧ k + 1 < cnt) := by omega
        simp only [this, ite_false]
        have : k + 1 ≤ k + 1 ∧ k + 1 < cnt := by omega
        simp [this]
      · rw [if_neg hi, hw i]
        by_cases h1 : k + 1 + 1 ≤ i ∧ i < cnt
        · have : k + 1 ≤ i ∧ i < cnt := by omega
          simp [h1, this]
        · have : ¬ (k + 1 ≤ i ∧ i < cnt) := by omega
          simp [h1, this]
  · -- the last iteration
    intro s h hP
    obtain ⟨hn, hp, hkc, a, rfl, hsz, hw⟩ := hP
    obtain ⟨n, p⟩ := s
    simp only at hn hp
    subst hp
    have hb' := body 0 n a hn hkc hsz
    have hn1 : (n - 1) = 0 := by
      apply UInt32.toNat_inj.mp; rw [u32_sub_one_toNat n (by omega)]; simp; omega
    refine ⟨(n, Ptr.ref (WRef.blk b) 0),
      { h0 with words := upd h0.words b (some (a.set! 0 (slideVal w (wfn a 0)))) },
      (0, Ptr.ref (WRef.blk b) 0),
      { h0 with words := upd h0.words b (some (a.set! 0 (slideVal w (wfn a 0)))) }, hb', ?_, ?_⟩
    · simp only [slCond, pure_app, hn1]
      rfl
    · refine ⟨rfl, a.set! 0 (slideVal w (wfn a 0)), rfl, by simp [hsz], ?_⟩
      intro i
      rw [wfn_set _ _ _ (by omega)]
      by_cases hi : i = 0
      · subst hi
        rw [hw 0]
        have : ¬ (0 + 1 ≤ 0 ∧ 0 < cnt) := by omega
        simp only [this, ite_false]
        have : 0 < cnt := by omega
        simp [this]
      · rw [if_neg hi, hw i]
        by_cases h1 : 0 + 1 ≤ i ∧ i < cnt
        · simp [h1]
        · have : ¬ (i < cnt) := by omega
          simp [this]
  · -- the start
    have hn : (UInt32.ofNat cnt).toNat = cnt := by simp; omega
    refine ⟨by rw [hn]; omega, ?_, by omega, a0, ?_, rfl, ?_⟩
    · show Ptr.ref (WRef.blk b) cnt = Ptr.ref (WRef.blk b) (cnt - 1 + 1)
      congr 1; omega
    · rw [upd_self _ _ _ hb]
    · intro i
      have : ¬ (cnt - 1 + 1 ≤ i ∧ i < cnt) := by omega
      simp [this]
  · show cnt - 1 < 2 ^ 64
    omega


/-- **slide_hash, safety and exact effect.** For `head` a block of at least `hash_size >= 1` words and `prev` a different
block of at least `w_size >= 1` words (with any content: `prev` is never cleared), `slide_hash` does not fault. Every
entry `m` of `head[0 .. hash_size)` and of `prev[0 .. w_size)` becomes `m >= w_size ? m - w_size : 0`, the entries
beyond stay as they were, and `slid` becomes 1. No other table, block or field changes. -/
theorem slide_hash_ok {h : Heap} {sr hb pb : Nat} {d : DeflateState} {ha pa : Array UInt16}
    (hd : h.dstates sr = some d) (hhead : d.head = .ref (.blk hb) 0) (hprev : d.prev = .ref (.blk pb) 0)
    (hh : h.words hb = some ha) (hp : h.words pb = some pa) (hne : hb ≠ pb)
    (h1 : d.hash_size.toNat ≤ ha.size) (h2 : d.w_size.toNat ≤ pa.size)
    (hn1 : 1 ≤ d.hash_size.toNat) (hn2 : 1 ≤ d.w_size.toNat) :
    ∃ ha' pa' : Array UInt16, slide_hash (some (.tab sr)) h = .ok ((), { h with
      words := upd (upd h.words hb (some ha')) pb (some pa'),
      dstates := upd h.dstates sr (some { d with slid := 1 }) }) ∧
    ha'.size = ha.size ∧ pa'.size = pa.size ∧
    (∀ i, wfn ha' i = if i < d.hash_size.toNat then slideVal d.w_size (wfn ha i) else wfn ha i) ∧
    (∀ i, wfn pa' i = if i < d.w_size.toNat then slideVal d.w_size (wfn pa i) else wfn pa i) := by
  have hh32 : d.hash_size.toNat < 2 ^ 32 := d.hash_size.toNat_lt
  have hw32 : d.w_size.toNat < 2 ^ 32 := d.w_size.toNat_lt
  obtain ⟨a1, hr1, hs1, hw1⟩ := slide_loop (h0 := h) (b := hb) (a0 := ha) d.w_size d.hash_size.toNat hh hn1 h1 hh32
  obtain ⟨H1, hH1⟩ : ∃ x : Heap, x = { h with words := upd h.words hb (some a1) } := ⟨_, rfl⟩
  rw [← hH1] at hr1
  have hp1 : H1.words pb = some pa := by rw [hH1]; simp [upd_ne _ _ _ _ hne.symm, hp]
  obtain ⟨a2, hr2, hs2, hw2⟩ := slide_loop (h0 := H1) (b := pb) (a0 := pa) d.w_size d.w_size.toNat hp1 hn2 h2 hw32
  obtain ⟨H2, hH2⟩ : ∃ x : Heap, x = { H1 with words := upd H1.words pb (some a2) } := ⟨_, rfl⟩
  rw [← hH2] at hr2
  have hd2 : H2.dstates sr = some d := by rw [hH2, hH1]; exact hd
  have e0 : ldDeflateState (some (.tab sr)) h = .ok (d, h) := ldDeflateState_tab hd
  have e1 : padd d.head d.hash_size.toNat h = .ok (.ref (.blk hb) d.hash_size.toNat, h) := by
    rw [hhead]
    simpa using padd_ok' (h := h) (r := WRef.blk hb) (a := ha) (off := 0) (n := d.hash_size.toNat) hh (by omega)
  have e2 : padd d.prev d.w_size.toNat H1 = .ok (.ref (.blk pb) d.w_size.toNat, H1) := by
    rw [hprev]
    simpa using padd_ok' (h := H1) (r := WRef.blk pb) (a := pa) (off := 0) (n := d.w_size.toNat) hp1 (by omega)
  have e3 : ldDeflateState (some (.tab sr)) H2 = .ok (d, H2) := ldDeflateState_tab hd2
  refine ⟨a1, a2, ?_, hs1, hs2, hw1, hw2⟩
  rw [slide_hash_unfold]
  rw [UInt32.ofNat_toNat] at hr1 hr2
  simp only [bind_app, e0, e1, hr1, e2, hr2, wr, e3]
  rw [stDeflateState_tab hd2]
  simp [hH2, hH1]

end Zlib.Deflate.Engine.Proofs
