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


/-! ## A step on the window side -/

/-- The window-side fields `deflate_stored` writes after its loop. -/
def keepState (d : DeflateState) (ss ins m : UInt32) (bs : Int64) (hw : UInt64) : DeflateState :=
  { d with strstart := ss, insert := ins, «matches» := m, block_start := bs, high_water := hw }

/-- **A step on the window side.** New window bytes of the same size and new window-side fields
keep `DInv` once the new shape and chains hold. -/
theorem window_state_step {h : Heap} {r : ZStreamRef} {ds w : Nat} {z : ZStream} {d : DeflateState}
    {wa : Array UInt8} (inv : DInv h r ds z d) (buffers : StreamBuffers h r) (level0 : d.level = 0)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa) (wa' : Array UInt8) (size : wa'.size = wa.size)
    (d' : DeflateState) (fields : ∃ ss ins m bs hw, d' = keepState d ss ins m bs hw) (shape : Shape d')
    (hash : LevelHash (setD { h with bytes := upd h.bytes w (some wa') } ds d') d') :
    DInv (setD { h with bytes := upd h.bytes w (some wa') } ds d') r ds z d' ∧
      StreamBuffers (setD { h with bytes := upd h.bytes w (some wa') } ds d') r ∧
      ByteSizes h (setD { h with bytes := upd h.bytes w (some wa') } ds d') := by
  obtain ⟨ss, ins, m, bs, hwv, rfl⟩ := fields
  have good := inv.good
  have goodB : DGood { h with bytes := upd h.bytes w (some wa') } r ds z d := good.bytes_set w wa' wa get size
  have dinv : DStInv { h with bytes := upd h.bytes w (some wa') } ds (keepState d ss ins m bs hwv) :=
    { goodB.inv with blocks := goodB.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl, hw := shape.highWater }
  have goodG := goodB.setD' (d' := keepState d ss ins m bs hwv) rfl good.live.status dinv (by trkeep)
  have sizes : ByteSizes h (setD { h with bytes := upd h.bytes w (some wa') } ds (keepState d ss ins m bs hwv)) := by
    refine ⟨fun ref a g0 => ?_, fun ref => by cases ref <;> rfl⟩
    obtain ⟨a', g1, s1⟩ := byte_view_write_size g0 get size
    exact ⟨a', by
      rw [byte_view_setD_depth (h := { h with bytes := upd h.bytes w (some wa') }) (d := d)
        (result := keepState d ss ins m bs hwv) (by simpa using good.live.hs) rfl ref]; exact g1, s1⟩
  have owned := stream_owned_keys good goodG rfl rfl rfl rfl
  have buffersG := stream_buffers_sizes good.live.hz goodG.live.hz buffers sizes owned
    (Zlib.Deflate.Engine.Proofs.stream_accounting_self z)
  refine ⟨⟨goodG, inv.alloc, inv.globals, shape, hash.hashing ?_, ?_⟩, buffersG, sizes⟩
  · exact (inv.shape.levelZero level0).2.1
  · obtain ⟨⟨xs, ⟨b, a, pbuf, getP, ledger⟩, dist⟩, clear, below⟩ := inv.symbols
    obtain ⟨w0, p0, q0, b0, blocks⟩ := good.inv.blocks
    have bw : b ≠ w := by
      have e1 : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
      have e2 : b0 = b := by simpa only [pbuf, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.pbuf.symm
      subst e1 e2; exact Ne.symm blocks.wb
    refine ⟨⟨xs, ⟨b, a, pbuf, ?_, ledger.keep rfl rfl rfl rfl⟩, dist⟩, ⟨clear.bl, clear.opt, clear.fixed⟩, below⟩
    show (upd h.bytes w (some wa')) b = some a
    rw [upd_ne _ _ _ _ bw]; exact getP


theorem bfn_copyRange (d s : Array UInt8) (doff soff n i : Nat) (hfit : doff + n ≤ d.size) :
    bfn (copyRange d s doff soff n) i = if doff ≤ i ∧ i < doff + n then bfn s (soff + (i - doff)) else bfn d i := by
  unfold bfn
  rw [Array.getD_eq_getD_getElem?, getElem?_copyRange _ _ _ _ _ _ hfit]
  split
  · simp [getElem!_def, Array.getD_eq_getD_getElem?]
    split <;> simp_all <;> rfl
  · rw [Array.getD_eq_getD_getElem?]

/-- The shape after the window side moved at level 0. -/
theorem shape_keep {d : DeflateState} (shape : Shape d) (level0 : d.level = 0) (ss ins m : UInt32) (bs : Int64)
    (hw : UInt64) (room : ss.toNat ≤ d.window_size.toNat) (insert : ins.toNat ≤ ss.toNat)
    (low : 0 ≤ bs.toInt) (high : bs.toInt ≤ ss.toNat) (available : d.match_available ≠ 0 → 1 ≤ ss.toNat)
    (water : hw.toNat ≤ d.window_size.toNat) (slides : m.toNat ≤ 2) :
    Shape (keepState d ss ins m bs hw) := by
  have zero := shape.levelZero level0
  have la : d.lookahead.toNat = 0 := by rw [zero.2.1]; rfl
  refine ⟨by show ss.toNat + d.lookahead.toNat ≤ d.window_size.toNat; omega, insert,
    fun big => absurd big (by show ¬ 3 ≤ d.lookahead.toNat; omega), shape.prevLength, shape.matchLength,
    shape.matchAvailable, high, fun ne => absurd level0 ne, fun _ => ⟨low, zero.2.1, zero.2.2⟩, available,
    fun (big : 3 ≤ d.match_length.toNat) => ?_, fun lo => absurd lo (by show ¬ 1 ≤ d.level.toInt; rw [level0]; decide), water, shape.lastFlush,
    shape.headerFlush, shape.trailer, shape.biValid, shape.cursor, shape.symRoom,
    ⟨slides, fun ne => absurd level0 ne⟩⟩
  have := (shape.pendingMatch big).2.2
  exact absurd (show d.match_length.toNat ≤ d.lookahead.toNat + 1 from this) (by omega)

end Zlib.Deflate.Engine.Proofs
