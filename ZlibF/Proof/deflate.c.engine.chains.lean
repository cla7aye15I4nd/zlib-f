import ZlibF.Proof.«deflate.c.engine.hash»

/-!
# deflate.c, engine: the hash-chain invariant H

The tables `head` (`hash_size` entries) and `prev` (`w_size` entries) are functions `Nat → UInt16` (the content of
the array, `0` outside; the proofs relating a heap array to its function are in the memory modules). Positions are
window indices. `0` is `NIL`.

**H.** A position `p ≠ 0` reachable from `head[k]` through `prev[p & wmask]` while the slot is still its own
(`top <= p + w_size`, where `top` is one past the last inserted position) was inserted: `p < top`, its first three
bytes lie below `lim` (the valid window data, `strstart + lookahead`) and hash to `k`, and `prev[p & wmask]` holds
a smaller position. A slot that was never written is never followed, so the junk in a fresh `prev` is harmless.

The theorems are `chains_insert` (one `INSERT_STRING`), `chains_slide` (`slide_hash` with the window copy),
`chains_congr`/`chains_mono` (frames), and `chain_ok_of_chains` (the chain `longest_match` walks).
-/

namespace Zlib.Deflate.Engine.Proofs

/-- Positions reachable in the hash table from `head[k]`, following `prev[p & wmask]` from every reached
`p ≠ 0` whose slot cannot have been reused yet (`top <= p + ws`). -/
inductive Reach (head prev : Nat → UInt16) (ws top k : Nat) : Nat → Prop
  | head : Reach head prev ws top k (head k).toNat
  | step {p : Nat} : Reach head prev ws top k p → p ≠ 0 → top ≤ p + ws →
      Reach head prev ws top k (prev (p &&& (ws - 1))).toNat

/-- **H, the hash-chain invariant.** -/
structure HashChains (head prev : Nat → UInt16) (w : Nat → UInt8) (n hsh hm : UInt32)
    (ws top lim : Nat) : Prop where
  node : ∀ k p, k < n.toNat → Reach head prev ws top k p → p ≠ 0 → top ≤ p + ws →
    p < top ∧ p + 3 ≤ lim ∧ (hkey hsh hm w p).toNat = k ∧ (prev (p &&& (ws - 1))).toNat < p

theorem reach_congr {h1 p1 h2 p2 : Nat → UInt16} {ws top k p : Nat}
    (hH : ∀ i, h2 i = h1 i) (hP : ∀ i, p2 i = p1 i)
    (hr : Reach h2 p2 ws top k p) : Reach h1 p1 ws top k p := by
  induction hr with
  | head => rw [hH]; exact Reach.head
  | step _ hp ht ih => rw [hP]; exact Reach.step ih hp ht

/-- Writes outside `head`/`prev`, and window changes at or beyond `lim`, keep the invariant. -/
theorem chains_congr {h1 p1 h2 p2 : Nat → UInt16} {w w' : Nat → UInt8} {n hsh hm : UInt32}
    {ws top lim : Nat} (hc : HashChains h1 p1 w n hsh hm ws top lim)
    (hH : ∀ i, h2 i = h1 i) (hP : ∀ i, p2 i = p1 i)
    (hw : ∀ i, i < lim → w' i = w i) : HashChains h2 p2 w' n hsh hm ws top lim := by
  refine ⟨fun k p hk hr hp ht => ?_⟩
  obtain ⟨a1, a2, a3, a4⟩ := hc.node k p hk (reach_congr hH hP hr) hp ht
  refine ⟨a1, a2, ?_, by rw [hP]; exact a4⟩
  rw [hkey_congr (w := w) (p := p) (fun j hj => hw _ (by omega))]; exact a3

theorem reach_mono {h1 p1 : Nat → UInt16} {ws top top' k p : Nat} (ht : top ≤ top')
    (hr : Reach h1 p1 ws top' k p) : Reach h1 p1 ws top k p := by
  induction hr with
  | head => exact Reach.head
  | step _ hp ht' ih => exact Reach.step ih hp (by omega)

/-- A larger `top` or `lim` keeps the invariant. -/
theorem chains_mono {h1 p1 : Nat → UInt16} {w : Nat → UInt8} {n hsh hm : UInt32}
    {ws top lim top' lim' : Nat} (hc : HashChains h1 p1 w n hsh hm ws top lim)
    (ht : top ≤ top') (hl : lim ≤ lim') : HashChains h1 p1 w n hsh hm ws top' lim' := by
  refine ⟨fun k p hk hr hp ht' => ?_⟩
  obtain ⟨a1, a2, a3, a4⟩ := hc.node k p hk (reach_mono ht hr) hp (by omega)
  exact ⟨by omega, by omega, a3, a4⟩

/-- A non-NIL head entry is below `top`. -/
theorem head_lt {h1 p1 : Nat → UInt16} {w : Nat → UInt8} {n hsh hm : UInt32} {ws top lim : Nat}
    (hc : HashChains h1 p1 w n hsh hm ws top lim) {k : Nat} (hk : k < n.toNat)
    (h0 : (h1 k).toNat ≠ 0) : (h1 k).toNat < top := by
  by_cases ht : top ≤ (h1 k).toNat + ws
  · exact (hc.node k _ hk Reach.head h0 ht).1
  · omega

/-- **INSERT_STRING keeps the invariant.** Inserting position `str >= top` with key `x = hkey str` (its three
bytes below `lim`): `prev[str & wmask] = head[x]` (`u`), `head[x] = str`. The result satisfies H with
`top := str + 1`. -/
theorem chains_insert {h1 p1 h2 p2 : Nat → UInt16} {w : Nat → UInt8} {n hsh hm : UInt32}
    {ws top lim b : Nat} (hc : HashChains h1 p1 w n hsh hm ws top lim) (hb2 : ws = 2 ^ b)
    {str x : Nat} {s16 : UInt16} (htop : top ≤ str) (hlim : str + 3 ≤ lim)
    (hx : (hkey hsh hm w str).toNat = x) (hxn : x < n.toNat)
    (hs16 : s16.toNat = str)
    (hH : ∀ i, h2 i = if i = x then s16 else h1 i)
    (hP : ∀ i, p2 i = if i = str &&& (ws - 1) then h1 x else p1 i) :
    HashChains h2 p2 w n hsh hm ws (str + 1) lim := by
  have hws : 0 < ws := by subst hb2; exact Nat.two_pow_pos b
  have A : ∀ k p, k < n.toNat → Reach h2 p2 ws (str + 1) k p →
      (k = x ∧ p = str) ∨ Reach h1 p1 ws top k p := by
    intro k p hk hr
    induction hr with
    | head =>
      rw [hH]
      split
      · rename_i e; exact Or.inl ⟨e, hs16⟩
      · exact Or.inr Reach.head
    | @step p _ hp ht ih =>
      rcases ih with ⟨rfl, rfl⟩ | hr
      · rw [hP, if_pos rfl]
        exact Or.inr Reach.head
      · have hpt := (hc.node k p hk hr hp (by omega)).1
        rw [hP, if_neg (and_wm_ne hb2 (by omega) (by omega))]
        exact Or.inr (Reach.step hr hp (by omega))
  refine ⟨fun k p hk hr hp ht => ?_⟩
  rcases A k p hk hr with ⟨rfl, rfl⟩ | hr0
  · refine ⟨by omega, hlim, hx, ?_⟩
    rw [hP, if_pos rfl]
    by_cases hu0 : (h1 k).toNat = 0
    · omega
    · have := head_lt hc hxn hu0; omega
  · obtain ⟨a1, a2, a3, a4⟩ := hc.node k p hk hr0 hp (by omega)
    refine ⟨by omega, a2, a3, ?_⟩
    rw [hP, if_neg (and_wm_ne hb2 (by omega) (by omega))]; exact a4

/-! ## Sliding -/

/-- The value `slide_hash` stores for an entry `m`: `m >= wsize ? m - wsize : NIL`. -/
def slideVal (w : UInt32) (m : UInt16) : UInt16 :=
  (if m.toUInt32 >= w then m.toUInt32 - w else 0).toUInt16

theorem slideVal_toNat (w : UInt32) (m : UInt16) (hw : w.toNat ≤ 65536) :
    (slideVal w m).toNat = if w.toNat ≤ m.toNat then m.toNat - w.toNat else 0 := by
  unfold slideVal
  have hm := m.toNat_lt
  by_cases hge : m.toUInt32 >= w
  · rw [if_pos hge]
    have h' : w.toNat ≤ m.toNat := by
      rw [GE.ge, UInt32.le_iff_toNat_le] at hge; simpa using hge
    rw [if_pos h']
    simp only [UInt32.toNat_toUInt16]
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simpa using h')]
    simp; omega
  · rw [if_neg hge]
    have h' : ¬ w.toNat ≤ m.toNat := by
      rw [GE.ge, UInt32.le_iff_toNat_le] at hge; simpa using hge
    rw [if_neg h']; rfl

/-- **slide_hash keeps the invariant** (with the window copy of `fill_window`): if every `head` entry and every
`prev` entry is slid by `w = w_size` and window bytes `i < lim - w` are the old bytes `i + w`, H holds with `top`
and `lim` lowered by `w`; positions below `w` became NIL. -/
theorem chains_slide {h1 p1 h2 p2 : Nat → UInt16} {w w' : Nat → UInt8} {n hsh hm ws : UInt32}
    {top lim b : Nat} (hc : HashChains h1 p1 w n hsh hm ws.toNat top lim)
    (hb2 : ws.toNat = 2 ^ b) (hw16 : ws.toNat ≤ 65536)
    (hH : ∀ i, i < n.toNat → h2 i = slideVal ws (h1 i))
    (hP : ∀ i, i < ws.toNat → p2 i = slideVal ws (p1 i))
    (hw : ∀ i, i + ws.toNat < lim → w' i = w (i + ws.toNat)) :
    HashChains h2 p2 w' n hsh hm ws.toNat (top - ws.toNat) (lim - ws.toNat) := by
  have B : ∀ k p, k < n.toNat → Reach h2 p2 ws.toNat (top - ws.toNat) k p → p ≠ 0 →
      Reach h1 p1 ws.toNat top k (p + ws.toNat) := by
    intro k p hk hr
    induction hr with
    | head =>
      intro hv0
      have := slideVal_toNat ws (h1 k) hw16
      rw [← hH k hk] at this
      split at this
      · rw [show (h2 k).toNat + ws.toNat = (h1 k).toNat by omega]; exact Reach.head
      · omega
    | @step p _ hp ht ih =>
      intro hv0
      have hr1 := ih hp
      obtain ⟨-, -, -, hvv⟩ := hc.node k _ hk hr1 (by omega) (by omega)
      rw [and_wm_add hb2] at hvv
      have := slideVal_toNat ws (p1 (p &&& (ws.toNat - 1))) hw16
      rw [← hP _ (and_wm_lt hb2 p)] at this
      split at this
      · rw [show (p2 (p &&& (ws.toNat - 1))).toNat + ws.toNat = (p1 (p &&& (ws.toNat - 1))).toNat by omega]
        have := Reach.step (p := p + ws.toNat) hr1 (by omega) (by omega)
        rw [and_wm_add hb2] at this
        exact this
      · omega
  refine ⟨fun k p hk hr hp ht => ?_⟩
  have hr1 := B k p hk hr hp
  obtain ⟨h1', h2', h3, hvv⟩ := hc.node k _ hk hr1 (by omega) (by omega)
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rw [hkey_congr (w := w) (p := p + ws.toNat) (fun j hj => by
      rw [hw _ (by omega)]; congr 1; omega)]; exact h3
  · rw [and_wm_add hb2] at hvv
    rw [hP _ (and_wm_lt hb2 p), slideVal_toNat ws _ hw16]
    split <;> omega

/-! ## The chain read by `longest_match` -/

/-- `limit` of `longest_match`: `strstart > MAX_DIST ? strstart - MAX_DIST : NIL`. -/
def lmLimit (ss md : Nat) : Nat := if ss > md then ss - md else 0

/-- Positions visited by the hash chain from `cur`: `cur`, then each `prev[p & wmask]` while it exceeds `limit`. -/
inductive Chain (prev : Nat → UInt16) (wm limit cur : Nat) : Nat → Prop
  | start : Chain prev wm limit cur cur
  | step {p q : Nat} : Chain prev wm limit cur p → q = (prev (p &&& wm)).toNat → limit < q →
      Chain prev wm limit cur q

/-- **The chain invariant gives what `longest_match` needs.** Right after `INSERT_STRING` at `ss`
(`head[x] = ss`, `prev[ss & wmask] = c`, the old head) with H at `top = ss + 1`, every position on the chain
`longest_match` walks from `c` (`1 <= c`, `ss - c <= MAX_DIST`) is in `[1, ss)` and agrees with `ss` in its third
byte whenever it agrees in the first two. -/
theorem chain_ok_of_chains {h1 p1 : Nat → UInt16} {w : Nat → UInt8} {n hsh hm : UInt32}
    {ws lim ss x c : Nat} (prm : HashParams n hsh hm)
    (hc : HashChains h1 p1 w n hsh hm ws (ss + 1) lim)
    (hx : (hkey hsh hm w ss).toNat = x) (hxn : x < n.toNat)
    (hhead : (h1 x).toNat = ss)
    (hu : (p1 (ss &&& (ws - 1))).toNat = c)
    (hc1 : 1 ≤ c) (hcs : c < ss) (hdist : ss - c ≤ ws - 262) :
    ∀ p, Chain p1 (ws - 1) (lmLimit ss (ws - 262)) c p →
      1 ≤ p ∧ p < ss ∧ (p1 (p &&& (ws - 1))).toNat < p ∧
      (w p = w ss → w (p + 1) = w (ss + 1) → w (p + 2) = w (ss + 2)) := by
  have r0 : Reach h1 p1 ws (ss + 1) x ss := hhead ▸ Reach.head
  have rc : Reach h1 p1 ws (ss + 1) x c := hu ▸ Reach.step r0 (by omega) (by omega)
  have C : ∀ p, Chain p1 (ws - 1) (lmLimit ss (ws - 262)) c p →
      Reach h1 p1 ws (ss + 1) x p ∧ p ≠ 0 ∧ ss + 1 ≤ p + ws ∧ p ≤ c := by
    intro p hp
    induction hp with
    | start => exact ⟨rc, by omega, by omega, Nat.le_refl _⟩
    | @step p q _ hq hlim ih =>
      obtain ⟨hr, hp0, hpw, hpc⟩ := ih
      obtain ⟨-, -, -, hlt⟩ := hc.node x p hxn hr hp0 hpw
      subst hq
      refine ⟨Reach.step hr hp0 hpw, by unfold lmLimit at hlim; split at hlim <;> omega, ?_, by omega⟩
      unfold lmLimit at hlim; split at hlim <;> omega
  intro p hp
  obtain ⟨hr, hp0, hpw, hpc⟩ := C p hp
  obtain ⟨-, -, hk, hlt⟩ := hc.node x p hxn hr hp0 hpw
  exact ⟨by omega, by omega, hlt, fun e0 e1 => hkey_third prm (by rw [hk, hx]) e0 e1⟩

end Zlib.Deflate.Engine.Proofs
