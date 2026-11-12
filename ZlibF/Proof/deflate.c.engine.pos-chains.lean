import ZlibF.Proof.«deflate.c.engine.chains»

/-!
# deflate.c, engine: positional hash chains

Safety needs less of the hash tables than the exact invariant H (`HashChains`): every node that a walk can
reach from a head lies below the insertion point. `ReachS` is the walk: from `head[k]`, then from each reached
`p ≠ 0` whose slot is still its own (`top ≤ p + w_size`) and that is not waiting for insertion (`p < stop`),
to `prev[p & wmask]`. `PosChains` says such nodes are below `top`. In the state between calls `top` is
`strstart` and `stop` is `strstart - insert`: the positions from `strstart - insert` on are waiting for
`fill_window` to insert them, and their `prev` slots hold old values until then.

The key of a node, its three bytes and the order of a chain are functional facts of H. They are not needed:
`INSERT_STRING` indexes `head` through a masked value, and `longest_match` only needs its walk to stay in
`[1, strstart)`.

Theorems: `posChains_of_hashChains` (H gives the positional form), `pos_mono` and `pos_congr` (frames),
`pos_insert` (one `INSERT_STRING`), `pos_slide` (`slide_hash`), `chain_pos_ok` (the walk of `longest_match`
right after `INSERT_STRING` at `strstart`).
-/

namespace Zlib.Deflate.Engine.Proofs
open Zlib.Deflate
set_option autoImplicit false

/-- The walk from `head[k]` that does not step from a position waiting for insertion (`stop ≤ p`). -/
inductive ReachS (head prev : Nat → UInt16) (ws top stop k : Nat) : Nat → Prop
  | head : ReachS head prev ws top stop k (head k).toNat
  | step {p : Nat} : ReachS head prev ws top stop k p → p ≠ 0 → top ≤ p + ws → p < stop →
      ReachS head prev ws top stop k (prev (p &&& (ws - 1))).toNat

/-- **Positional hash chains.** Every node `p ≠ 0` reached from a head whose slot is still its own is below
`top`. -/
structure PosChains (head prev : Nat → UInt16) (n : UInt32) (ws top stop : Nat) : Prop where
  node : ∀ k p, k < n.toNat → ReachS head prev ws top stop k p → p ≠ 0 → top ≤ p + ws → p < top

theorem reachS_reach {h1 p1 : Nat → UInt16} {ws top stop k p : Nat}
    (hr : ReachS h1 p1 ws top stop k p) : Reach h1 p1 ws top k p := by
  induction hr with
  | head => exact Reach.head
  | step _ hp ht _ ih => exact Reach.step ih hp ht

/-- **H gives the positional form**, for every `stop`. -/
theorem posChains_of_hashChains {h1 p1 : Nat → UInt16} {w : Nat → UInt8} {n hsh hm : UInt32}
    {ws top lim : Nat} (hc : HashChains h1 p1 w n hsh hm ws top lim) (stop : Nat) :
    PosChains h1 p1 n ws top stop :=
  ⟨fun k p hk hr hp ht => (hc.node k p hk (reachS_reach hr) hp ht).1⟩

theorem reachS_congr {h1 p1 h2 p2 : Nat → UInt16} {ws top stop k p : Nat}
    (hH : ∀ i, h2 i = h1 i) (hP : ∀ i, p2 i = p1 i)
    (hr : ReachS h2 p2 ws top stop k p) : ReachS h1 p1 ws top stop k p := by
  induction hr with
  | head => rw [hH]; exact ReachS.head
  | step _ hp ht hs ih => rw [hP]; exact ReachS.step ih hp ht hs

/-- Equal tables keep the invariant. -/
theorem pos_congr {h1 p1 h2 p2 : Nat → UInt16} {n : UInt32} {ws top stop : Nat}
    (hc : PosChains h1 p1 n ws top stop) (hH : ∀ i, h2 i = h1 i) (hP : ∀ i, p2 i = p1 i) :
    PosChains h2 p2 n ws top stop :=
  ⟨fun k p hk hr hp ht => hc.node k p hk (reachS_congr hH hP hr) hp ht⟩

theorem reachS_mono {h1 p1 : Nat → UInt16} {ws top top' stop stop' k p : Nat}
    (ht : top ≤ top') (hs : stop' ≤ stop)
    (hr : ReachS h1 p1 ws top' stop' k p) : ReachS h1 p1 ws top stop k p := by
  induction hr with
  | head => exact ReachS.head
  | step _ hp ht' hs' ih => exact ReachS.step ih hp (by omega) (by omega)

/-- A larger `top` or a smaller `stop` keeps the invariant. -/
theorem pos_mono {h1 p1 : Nat → UInt16} {n : UInt32} {ws top top' stop stop' : Nat}
    (hc : PosChains h1 p1 n ws top stop) (ht : top ≤ top') (hs : stop' ≤ stop) :
    PosChains h1 p1 n ws top' stop' :=
  ⟨fun k p hk hr hp ht' => by
    have := hc.node k p hk (reachS_mono ht hs hr) hp (by omega)
    omega⟩

/-- **INSERT_STRING keeps the invariant.** Inserting `str` (key `x`): `prev[str & wmask] = head[x]`,
`head[x] = str`. The new `top'` is above `str`, and the new `stop'` lets the walk step from no other new
position than `str`, the first position waiting for insertion. -/
theorem pos_insert {h1 p1 h2 p2 : Nat → UInt16} {n : UInt32} {ws top stop top' stop' b : Nat}
    (hc : PosChains h1 p1 n ws top stop) (hb2 : ws = 2 ^ b)
    {str x : Nat} {s16 : UInt16} (hxn : x < n.toNat) (hs16 : s16.toNat = str)
    (htop : top ≤ top') (hstr : str < top') (hfront : stop ≤ str)
    (hstop : ∀ p, p < stop' → p ≠ str → p < stop)
    (hH : ∀ i, h2 i = if i = x then s16 else h1 i)
    (hP : ∀ i, p2 i = if i = str &&& (ws - 1) then h1 x else p1 i) :
    PosChains h2 p2 n ws top' stop' := by
  have hws : 0 < ws := by subst hb2; exact Nat.two_pow_pos b
  -- every node reached in the new tables is `str` or reached in the old ones, from some key
  have A : ∀ k p, k < n.toNat → ReachS h2 p2 ws top' stop' k p →
      p = str ∨ ∃ k', k' < n.toNat ∧ ReachS h1 p1 ws top stop k' p := by
    intro k p hk hr
    induction hr with
    | head =>
      rw [hH]
      split
      · exact Or.inl hs16
      · exact Or.inr ⟨k, hk, ReachS.head⟩
    | @step p _ hp ht hs ih =>
      rcases ih with e | ⟨k', hk', hr⟩
      · subst e
        rw [hP, ite_eq_left rfl]
        exact Or.inr ⟨x, hxn, ReachS.head⟩
      · by_cases e : p = str
        · subst e
          rw [hP, ite_eq_left rfl]
          exact Or.inr ⟨x, hxn, ReachS.head⟩
        · have below : p < stop := hstop p hs e
          have hpt := hc.node k' p hk' hr hp (by omega)
          rw [hP, ite_eq_right (fun eq => and_wm_ne hb2 (p := p) (q := str) (by omega) (by omega) eq)]
          exact Or.inr ⟨k', hk', ReachS.step hr hp (by omega) below⟩
  refine ⟨fun k p hk hr hp ht => ?_⟩
  rcases A k p hk hr with e | ⟨k', hk', hr0⟩
  · omega
  · have := hc.node k' p hk' hr0 hp (by omega)
    omega

/-- **slide_hash keeps the invariant**: every `head` and `prev` entry slid by `w = w_size`; `top` and `stop`
are lowered by `w`. Positions below `w` became NIL. -/
theorem pos_slide {h1 p1 h2 p2 : Nat → UInt16} {n ws : UInt32} {top stop b : Nat}
    (hc : PosChains h1 p1 n ws.toNat top stop)
    (hb2 : ws.toNat = 2 ^ b) (hw16 : ws.toNat ≤ 65536)
    (hH : ∀ i, i < n.toNat → h2 i = slideVal ws (h1 i))
    (hP : ∀ i, i < ws.toNat → p2 i = slideVal ws (p1 i)) :
    PosChains h2 p2 n ws.toNat (top - ws.toNat) (stop - ws.toNat) := by
  have B : ∀ k p, k < n.toNat → ReachS h2 p2 ws.toNat (top - ws.toNat) (stop - ws.toNat) k p → p ≠ 0 →
      ReachS h1 p1 ws.toNat top stop k (p + ws.toNat) := by
    intro k p hk hr
    induction hr with
    | head =>
      intro hv0
      have := slideVal_toNat ws (h1 k) hw16
      rw [← hH k hk] at this
      split at this
      · rw [show (h2 k).toNat + ws.toNat = (h1 k).toNat by omega]; exact ReachS.head
      · omega
    | @step p _ hp ht hs ih =>
      intro hv0
      have hr1 := ih hp
      have := slideVal_toNat ws (p1 (p &&& (ws.toNat - 1))) hw16
      rw [← hP _ (and_wm_lt hb2 p)] at this
      split at this
      · rw [show (p2 (p &&& (ws.toNat - 1))).toNat + ws.toNat = (p1 (p &&& (ws.toNat - 1))).toNat by omega]
        have := ReachS.step (p := p + ws.toNat) hr1 (by omega) (by omega) (by omega)
        rw [and_wm_add hb2] at this
        exact this
      · omega
  refine ⟨fun k p hk hr hp ht => ?_⟩
  have := hc.node k _ hk (B k p hk hr hp) (by omega) (by omega)
  omega

/-- **The walk of `longest_match` stays in `[1, ss)`.** Before `INSERT_STRING` at `ss` the chains hold with
`top = stop = ss` (nothing waits for insertion); the insertion sets `head[x] = ss` and `prev[ss & wmask] = c`,
the old head. Every position on the chain `longest_match` walks from `c` (`1 ≤ c`, `ss - c ≤ MAX_DIST`) is in
`[1, ss)`. -/
theorem chain_pos_ok {h1 p1 p2 : Nat → UInt16} {n : UInt32} {ws b ss x c : Nat}
    (hc : PosChains h1 p1 n ws ss ss) (hb2 : ws = 2 ^ b) (hwsz : 262 ≤ ws) (hxn : x < n.toNat)
    (hu : (h1 x).toNat = c)
    (hP : ∀ i, i ≠ ss &&& (ws - 1) → p2 i = p1 i)
    (hc1 : 1 ≤ c) (hdist : ss - c ≤ ws - 262) :
    ∀ p, Chain p2 (ws - 1) (lmLimit ss (ws - 262)) c p → 1 ≤ p ∧ p < ss := by
  have hws : 0 < ws := by subst hb2; exact Nat.two_pow_pos b
  have C : ∀ p, Chain p2 (ws - 1) (lmLimit ss (ws - 262)) c p →
      ReachS h1 p1 ws ss ss x p ∧ 1 ≤ p ∧ p < ss ∧ ss + 262 ≤ p + ws := by
    intro p hp
    induction hp with
    | start =>
      have r : ReachS h1 p1 ws ss ss x c := hu ▸ ReachS.head
      exact ⟨r, hc1, hc.node x c hxn r (by omega) (by omega), by omega⟩
    | @step p q _ hq hlim ih =>
      obtain ⟨hr, hp1, hps, hpw⟩ := ih
      have hlim' : 1 ≤ q ∧ ss + 262 ≤ q + ws := by
        unfold lmLimit at hlim; split at hlim <;> omega
      have same : p2 (p &&& (ws - 1)) = p1 (p &&& (ws - 1)) :=
        hP _ (fun eq => and_wm_ne hb2 (p := p) (q := ss) hps (by omega) eq)
      have hreach : ReachS h1 p1 ws ss ss x q := by
        rw [hq, same]
        exact ReachS.step hr (by omega) (by omega) hps
      exact ⟨hreach, hlim'.1, hc.node x q hxn hreach (by omega) (by omega), hlim'.2⟩
  intro p hp
  obtain ⟨_, a, b', _⟩ := C p hp
  exact ⟨a, b'⟩

end Zlib.Deflate.Engine.Proofs
