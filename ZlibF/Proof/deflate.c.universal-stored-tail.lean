import ZlibF.Proof.«deflate.c.universal-stored-loop»

/-!
# deflate.c, universal engine: the end of `deflate_stored`

After the copy loop, `deflate_stored` keeps the last `w_size` bytes of the consumed input in the
window (sliding it without the hash tables; the slides are counted in `matches`), refills the
window from the input, and emits a stored block from the window into `pending_buf` when enough
is there. At level 0 there is no lookahead, so the hash chains of `DInv` only constrain positions
below `strstart`: window writes at and beyond `strstart` keep them, and a slide turns them into
the slid chains (`matches = 1`), which `deflateParams` repairs.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Universal
set_option autoImplicit false

/-! ## The hash chains at level 0 -/

/-- The hash part of `DInv` without lookahead. -/
def LevelHash (h : Heap) (d : DeflateState) : Prop :=
  (d.«matches» = 0 → Chains h d) ∧ (d.«matches» = 1 → SlidChains h d)

theorem LevelHash.hashing {h : Heap} {d : DeflateState} (hash : LevelHash h d) (la : d.lookahead = 0) :
    Hashing h d :=
  ⟨hash.1, hash.2, fun _ _ large => by rw [la] at large; simp at large⟩

/-- The fields of the hash geometry. -/
def HashKeys (d d' : DeflateState) : Prop :=
  d'.window = d.window ∧ d'.prev = d.prev ∧ d'.head = d.head ∧ d'.w_size = d.w_size ∧
    d'.hash_size = d.hash_size ∧ d'.hash_shift = d.hash_shift ∧ d'.hash_mask = d.hash_mask

/-- Window writes at or beyond `strstart`, with `strstart` and the insertion frontier moving up,
keep the chains. -/
theorem level_hash_write {h g : Heap} {d d' : DeflateState} (hash : LevelHash h d)
    (la : d.lookahead = 0) (la' : d'.lookahead = 0) (keys : HashKeys d d') (slides : d'.«matches» = d.«matches»)
    (grow : d.strstart.toNat ≤ d'.strstart.toNat)
    (top : d.strstart.toNat - d.insert.toNat ≤ d'.strstart.toNat - d'.insert.toNat)
    (words : ∀ p, (d.prev = .ref (.blk p) 0 ∨ d.head = .ref (.blk p) 0) → g.words p = h.words p)
    (window : ∀ w wa, d.window = .ref (.blk w) 0 → h.bytes w = some wa →
      ∃ wa', g.bytes w = some wa' ∧ ∀ i, i < d.strstart.toNat → bfn wa' i = bfn wa i) :
    LevelHash g d' := by
  obtain ⟨kw, kp, kq, kws, khs, khsh, khm⟩ := keys
  refine ⟨fun zero => ?_, fun one => ?_⟩
  · rw [slides] at zero
    obtain ⟨w, p, q, wa, pa, qa, win, prv, hd, hw, hp, hq, H⟩ := hash.1 zero
    obtain ⟨wa', gw, same⟩ := window w wa win hw
    refine ⟨w, p, q, wa', pa, qa, by rw [kw]; exact win, by rw [kp]; exact prv, by rw [kq]; exact hd, gw,
      by rw [words p (Or.inl prv)]; exact hp, by rw [words q (Or.inr hd)]; exact hq, ?_⟩
    rw [khs, khsh, khm, kws, la']
    rw [la] at H
    have H' := chains_congr H (fun _ => rfl) (fun _ => rfl) (w' := bfn wa') (fun i lt => same i (by simp at lt; omega))
    exact chains_mono H' top (by omega)
  · rw [slides] at one
    obtain ⟨w, p, q, wa, pa, qa, win, prv, hd, hw, hp, hq, H⟩ := hash.2 one
    obtain ⟨wa', gw, same⟩ := window w wa win hw
    refine ⟨w, p, q, wa', pa, qa, by rw [kw]; exact win, by rw [kp]; exact prv, by rw [kq]; exact hd, gw,
      by rw [words p (Or.inl prv)]; exact hp, by rw [words q (Or.inr hd)]; exact hq, ?_⟩
    rw [khs, khsh, khm, kws, la']
    rw [la] at H
    have H' := chains_congr H (fun _ => rfl) (fun _ => rfl) (w' := bfn wa') (fun i lt => same i (by simp at lt; omega))
    exact chains_mono H' top (by omega)

/-- `matches` saturates at 2: one more slide. -/
def slideCount (m : UInt32) : UInt32 := if m < 2 then m + 1 else m

/-- A slide of the window by `w_size` without the hash tables (`zmemcpy(s->window, s->window +
s->w_size, s->strstart)` after `s->strstart -= s->w_size`) turns exact chains into slid chains. -/
theorem level_hash_slide {h g : Heap} {d d' : DeflateState} (hash : LevelHash h d)
    (la : d.lookahead = 0) (la' : d'.lookahead = 0) (keys : HashKeys d d')
    (slides : d'.«matches» = slideCount d.«matches»)
    (bits : ∃ b, d.w_size.toNat = 2 ^ b) (small : d.w_size.toNat ≤ 65536)
    (wide : d.w_size.toNat ≤ d.strstart.toNat)
    (shift : d'.strstart.toNat = d.strstart.toNat - d.w_size.toNat)
    (insert : d'.insert.toNat ≤ d.insert.toNat)
    (words : ∀ p, (d.prev = .ref (.blk p) 0 ∨ d.head = .ref (.blk p) 0) → g.words p = h.words p)
    (window : ∀ w wa, d.window = .ref (.blk w) 0 → h.bytes w = some wa →
      ∃ wa', g.bytes w = some wa' ∧ ∀ i, i + d.w_size.toNat < d.strstart.toNat →
        bfn wa' i = bfn wa (i + d.w_size.toNat)) :
    LevelHash g d' := by
  obtain ⟨kw, kp, kq, kws, khs, khsh, khm⟩ := keys
  have cases : d.«matches» = 0 ∨ d'.«matches» ≠ 0 ∧ d'.«matches» ≠ 1 := by
    rw [slides]
    unfold slideCount
    by_cases zero : d.«matches» = 0
    · exact Or.inl zero
    · right
      split
      · rename_i lt
        have lt' := UInt32.lt_iff_toNat_lt.mp lt
        have nz : d.«matches».toNat ≠ 0 := fun e => zero (UInt32.toNat_inj.mp (by rw [e]; rfl))
        have one : d.«matches».toNat = 1 := by simp at lt'; omega
        constructor <;> intro e <;> have := congrArg UInt32.toNat e <;>
          rw [UInt32.toNat_add, one] at this <;> simp at this
      · rename_i ge
        have ge' : ¬ d.«matches».toNat < 2 := fun c => ge (UInt32.lt_iff_toNat_lt.mpr c)
        constructor <;> intro e <;> have := congrArg UInt32.toNat e <;> simp at this <;> omega
  rcases cases with zero | ⟨n0, n1⟩
  · have one : d'.«matches» = 1 := by rw [slides, zero]; rfl
    refine ⟨fun z0 => absurd (one.symm.trans z0) (by decide), fun _ => ?_⟩
    obtain ⟨w, p, q, wa, pa, qa, win, prv, hd, hw, hp, hq, H⟩ := hash.1 zero
    obtain ⟨wa', gw, same⟩ := window w wa win hw
    obtain ⟨b, hb⟩ := bits
    refine ⟨w, p, q, wa', pa, qa, by rw [kw]; exact win, by rw [kp]; exact prv, by rw [kq]; exact hd, gw,
      by rw [words p (Or.inl prv)]; exact hp, by rw [words q (Or.inr hd)]; exact hq, ?_⟩
    rw [khs, khsh, khm, kws, la']
    rw [la] at H
    have S := chains_slide (h2 := fun i => slideVal d.w_size (wfn qa i))
      (p2 := fun i => slideVal d.w_size (wfn pa i)) (w' := bfn wa') H hb small (fun _ _ => rfl) (fun _ _ => rfl)
      (fun i lt => same i (by simp at lt; omega))
    exact chains_mono S (by simp; omega) (by simp; omega)
  · exact ⟨fun e => absurd e n0, fun e => absurd e n1⟩

end Zlib.Deflate.Engine.Proofs
