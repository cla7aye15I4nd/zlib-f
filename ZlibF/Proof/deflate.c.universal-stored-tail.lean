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


/-! ## Keeping the consumed input in the window -/

theorem min_toNat_le (a b : UInt32) : (MIN a b).toNat ≤ a.toNat := by
  unfold MIN; split
  · rename_i lt; have := UInt32.lt_iff_toNat_lt.mp lt; omega
  · exact Nat.le_refl _

theorem psub_view {h : Heap} {ref : BRef} {a : Array UInt8} {io n : Nat} (get : Space.get h ref = some a)
    (le : n ≤ io) (bound : io ≤ a.size) : psub (.ref ref io : BPtr) n h = .ok (.ref ref (io - n), h) := by
  have := Ptr.add_ok (off := io) (k := -(n : Int)) get (by omega) (by omega)
  have e : ((io : Int) + -(n : Int)).toNat = io - n := by omega
  rw [e] at this
  exact this

theorem padd_view {h : Heap} {ref : BRef} {a : Array UInt8} {io n : Nat} (get : Space.get h ref = some a)
    (bound : io + n ≤ a.size) : padd (.ref ref io : BPtr) n h = .ok (.ref ref (io + n), h) := by
  simpa only [OkOn, padd] using Ptr.add_nat_ok get bound

theorem view_setD_other {h : Heap} {ds : Nat} {d : DeflateState} {ref : BRef} (ne : ref ≠ .dstate_depth ds) :
    Space.get (setD h ds d) ref = Space.get h ref := by
  cases ref with
  | dstate_depth o =>
    have : o ≠ ds := fun e => ne (by rw [e])
    show ((setD h ds d).dstates o).map (·.depth) = (h.dstates o).map (·.depth)
    rw [setD_dstates_ne _ _ _ _ this]
  | blk _ | str _ | st_dist_code | st_length_code => rfl

theorem view_put_other {h : Heap} {w : Nat} {a : Array UInt8} {ref : BRef} (ne : ref ≠ .blk w) :
    Space.get (Space.put h (BRef.blk w) a) ref = Space.get h ref := by
  cases ref with
  | blk b =>
    have : b ≠ w := fun e => ne (by rw [e])
    exact upd_ne _ _ _ _ this
  | str _ | dstate_depth _ | st_dist_code | st_length_code => rfl

theorem put_blk_put_blk (h : Heap) (w : Nat) (a b : Array UInt8) :
    Space.put (Space.put h (BRef.blk w) a) (BRef.blk w) b = Space.put h (BRef.blk w) b := by
  show ({ h with bytes := upd (upd h.bytes w (some a)) w (some b) } : Heap) = { h with bytes := upd h.bytes w (some b) }
  rw [upd_upd]

theorem put_setD (h : Heap) (ds w : Nat) (d : DeflateState) (a : Array UInt8) :
    Space.put (setD h ds d) (BRef.blk w) a = setD (Space.put h (BRef.blk w) a) ds d := rfl


/-- The state after the slide in `storedKeep` and in the refill. -/
def keepSlide (d : DeflateState) : DeflateState :=
  { d with strstart := d.strstart - d.w_size, «matches» := if d.«matches» < 2 then d.«matches» + 1 else d.«matches», insert := if d.insert > d.strstart - d.w_size then d.strstart - d.w_size else d.insert }

/-- The last part of `storedKeep`: `used` input bytes after `strstart`, then the block start. -/
theorem keep_write {H : Heap} {r : ZStreamRef} {ds w : Nat} {z : ZStream} {e : DeflateState}
    {wb ia : Array UInt8} {ref : BRef} {io : Nat} (used : UInt32)
    (state : H.dstates ds = some e) (win : e.window = .ref (.blk w) 0)
    (get : Space.get H (BRef.blk w) = some wb) (ro : Space.ro H (BRef.blk w) = false)
    (fit : e.strstart.toNat + used.toNat ≤ wb.size) (hz : r.get H = some z) (src : z.next_in = .ref ref io)
    (inGet : Space.get H ref = some ia) (inBound : io ≤ ia.size) (consumed : used.toNat ≤ io)
    (apart : ref ≠ .blk w) :
    (do
      let d ← ldDeflateState (some (.tab ds))
      memcpyB (← padd d.window d.strstart.toNat) (← psub (← zrd (some r) (·.next_in)) used.toNat) used.toNat
      wr (some (.tab ds)) (fun d => { d with strstart := d.strstart + used, insert := d.insert + MIN used (d.w_size - d.insert) })
      wr (some (.tab ds)) (fun d => { d with block_start := d.strstart.toUInt64.toInt64 })) H =
      .ok ((), setD (Space.put H (BRef.blk w) (copyRange wb ia e.strstart.toNat (io - used.toNat) used.toNat)) ds
        (keepState e (e.strstart + used) (e.insert + MIN used (e.w_size - e.insert)) e.«matches»
          (e.strstart + used).toUInt64.toInt64 e.high_water)) := by
  have dst : padd e.window e.strstart.toNat H = .ok (.ref (.blk w) e.strstart.toNat, H) := by
    rw [win]; have := padd_view (io := 0) (n := e.strstart.toNat) get (by omega)
    rw [Nat.zero_add] at this; exact this
  have read : zrd (some r) (·.next_in) H = .ok (.ref ref io, H) := by simp [zrd_eq, hz, src]
  have sub := psub_view (n := used.toNat) inGet consumed inBound
  have copy : memcpyB (.ref (.blk w) e.strstart.toNat) (.ref ref (io - used.toNat)) used.toNat H =
      .ok ((), Space.put H (BRef.blk w) (copyRange wb ia e.strstart.toNat (io - used.toNat) used.toNat)) :=
    Ptr.memcpy_ok get inGet ro fit (by omega) (Or.inl (Ne.symm apart))
  have state1 : (Space.put H (BRef.blk w) (copyRange wb ia e.strstart.toNat (io - used.toNat) used.toNat)).dstates ds =
      some e := state
  simp only [bind_app, ldDeflateState_tab state, dst, read, sub, copy, wrD_eq, state1, setD_dstates_same, setD_setD]
  rfl

set_option maxHeartbeats 8000000 in
/-- **`deflate_stored` keeps the consumed input in the window.** `used` bytes were consumed by the
loop, so the input pointer is at least `used` past the start of its view. -/
theorem stored_keep {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (buffers : StreamBuffers h r) (level0 : d.level = 0)
    (used : UInt32) {ref : BRef} {io : Nat} {ia : Array UInt8}
    (src : z.next_in = .ref ref io) (inGet : Space.get h ref = some ia) (inBound : io ≤ ia.size)
    (consumed : used.toNat ≤ io) (apartW : ∀ w, d.window = .ref (.blk w) 0 → ref ≠ .blk w)
    (apartS : ref ≠ .dstate_depth ds) :
    ∃ g d', storedKeep (some (.tab ds)) (some r) used h = .ok ((), g) ∧ DInv g r ds z d' ∧
      StreamBuffers g r ∧ ByteSizes h g ∧ (∃ ss ins m bs hw, d' = keepState d ss ins m bs hw) ∧
      g.static = h.static ∧ g.nalloc = h.nalloc := by
  have good := inv.good
  have shape := inv.shape
  have zero := shape.levelZero level0
  obtain ⟨w, wa, win, getW, sizeW⟩ := window_block good
  have apart := apartW w win
  have wsz := good.inv.wsz
  have wsize := good.inv.wsize
  have wbits := good.inv.wbits_hi
  have wbitsLo := good.inv.wbits_lo
  have wpow : 2 ^ d.w_bits.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) wbits
  have wpowLo : 2 ^ 9 ≤ 2 ^ d.w_bits.toNat := Nat.pow_le_pow_right (by omega) wbitsLo
  have room := shape.room
  have la : d.lookahead.toNat = 0 := by rw [zero.2.1]; rfl
  have insLe := shape.insert
  have ro : Space.ro h (BRef.blk w) = false := by
    obtain ⟨w0, p0, q0, b0, blocks⟩ := good.inv.blocks
    have : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
    subst this; exact blocks.wro
  have getWv : Space.get h (BRef.blk w) = some wa := getW
  have readIn : ∀ H : Heap, r.get H = some z → zrd (some r) (·.next_in) H = .ok (.ref ref io, H) := by
    intro H hz; simp [zrd_eq, hz, src]
  have ssLt := d.strstart.toNat_lt
  have uLt := used.toNat_lt
  have hwLe := shape.highWater
  have keysRefl : HashKeys d d := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hash0 : LevelHash h d := ⟨inv.hashing.chains, inv.hashing.slid⟩
  have state0 : h.dstates ds = some d := good.live.hs
  by_cases big : used ≥ d.w_size
  · -- the whole window from the input
    have bigN : d.w_size.toNat ≤ used.toNat := UInt32.le_iff_toNat_le.mp big
    let wa1 := copyRange wa ia 0 (io - d.w_size.toNat) d.w_size.toNat
    have sub := psub_view (n := d.w_size.toNat) inGet (by omega) inBound
    have copy : memcpyB d.window (.ref ref (io - d.w_size.toNat)) d.w_size.toNat h =
        .ok ((), Space.put h (BRef.blk w) wa1) := by
      rw [win]; exact Ptr.memcpy_ok getWv inGet ro (by omega) (by omega) (Or.inl (Ne.symm apart))
    let d' := keepState d d.w_size d.w_size 2 d.w_size.toUInt64.toInt64 d.high_water
    have state1 : (Space.put h (BRef.blk w) wa1).dstates ds = some d := state0
    have run : storedKeep (some (.tab ds)) (some r) used h = .ok ((), setD (Space.put h (BRef.blk w) wa1) ds d') := by
      unfold storedKeep
      simp only [bind_app, ldDeflateState_tab state0, big, ite_true, readIn h good.live.hz, sub, copy,
        wrD_eq, state1, setD_dstates_same, setD_setD]
      rfl
    have bsN : (d.w_size.toUInt64.toInt64).toInt = d.w_size.toNat := u32_toInt64_toInt _
    have shape' : Shape d' := shape_keep shape level0 _ _ _ _ _ (by omega) (Nat.le_refl _)
      (by rw [bsN]; omega) (by rw [bsN]; omega) (fun _ => by omega) hwLe (by decide)
    have hash' : LevelHash (setD { h with bytes := upd h.bytes w (some wa1) } ds d') d' :=
      ⟨fun e => absurd (show (2 : UInt32) = 0 from e) (by decide),
        fun e => absurd (show (2 : UInt32) = 1 from e) (by decide)⟩
    obtain ⟨invG, buffersG, sizesG⟩ := window_state_step inv buffers level0 win getW wa1
      (by simp [wa1, size_copyRange]) d' ⟨_, _, _, _, _, rfl⟩ shape' hash'
    exact ⟨_, d', run, invG, buffersG, sizesG, ⟨_, _, _, _, _, rfl⟩, rfl, rfl⟩
  · have smallN : used.toNat < d.w_size.toNat := by
      have : ¬ d.w_size.toNat ≤ used.toNat := fun c => big (UInt32.le_iff_toNat_le.mpr c)
      omega
    have wsS : (d.window_size - d.strstart.toUInt64).toNat = d.window_size.toNat - d.strstart.toNat := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp
    have hz := good.live.hz
    have minLe := min_toNat_le used (d.w_size - d.insert)
    by_cases slide : d.window_size - d.strstart.toUInt64 ≤ used.toUInt64
    · have slideN : d.window_size.toNat - d.strstart.toNat ≤ used.toNat := by
        have := UInt64.le_iff_toNat_le.mp slide; rw [wsS] at this; simpa using this
      have wide : d.w_size.toNat < d.strstart.toNat := by omega
      have ssN : (d.strstart - d.w_size).toNat = d.strstart.toNat - d.w_size.toNat :=
        UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))
      have dstW : padd d.window d.w_size.toNat h = .ok (.ref (.blk w) d.w_size.toNat, h) := by
        rw [win]; have := padd_view (io := 0) (n := d.w_size.toNat) getWv (by omega)
        rw [Nat.zero_add] at this; exact this
      have copy1 : memcpyB d.window (.ref (.blk w) d.w_size.toNat) (d.strstart - d.w_size).toNat h =
          .ok ((), Space.put h (BRef.blk w) (copyRange wa wa 0 d.w_size.toNat (d.strstart - d.w_size).toNat)) := by
        rw [win]
        exact Ptr.memcpy_ok getWv getWv ro (by omega) (by omega) (Or.inr (Or.inl (by omega)))
      have size1 : (copyRange wa wa 0 d.w_size.toNat (d.strstart - d.w_size).toNat).size = wa.size :=
        size_copyRange _ _ _ _ _
      have hzH : r.get (setD (Space.put h (BRef.blk w) (copyRange wa wa 0 d.w_size.toNat (d.strstart - d.w_size).toNat)) ds
          (keepSlide d)) = some z := by
        show r.get (Space.put h (BRef.blk w) (copyRange wa wa 0 d.w_size.toNat (d.strstart - d.w_size).toNat)) = some z
        rw [view_put_stream]; exact hz
      have w2 := keep_write (H := setD (Space.put h (BRef.blk w)
          (copyRange wa wa 0 d.w_size.toNat (d.strstart - d.w_size).toNat)) ds (keepSlide d))
        (r := r) (z := z) used (setD_dstates_same _ _ _) win
        (by rw [view_setD_other (by simp)]; exact view_put_get getWv ro _) ro
        (by rw [size1]; show (d.strstart - d.w_size).toNat + used.toNat ≤ wa.size; omega)
        hzH src (by rw [view_setD_other apartS, view_put_other apart]; exact inGet) inBound consumed apart
      -- the final heap and state
      obtain ⟨wa1, hwa1⟩ : ∃ x, x = copyRange wa wa 0 d.w_size.toNat (d.strstart - d.w_size).toNat := ⟨_, rfl⟩
      rw [← hwa1] at copy1 size1 hzH w2
      obtain ⟨wa2, hwa2⟩ : ∃ x, x = copyRange wa1 ia (keepSlide d).strstart.toNat (io - used.toNat) used.toNat :=
        ⟨_, rfl⟩
      rw [← hwa2] at w2
      have size2 : wa2.size = wa.size := by rw [hwa2, size_copyRange, size1]
      have s1N : (keepSlide d).strstart.toNat = d.strstart.toNat - d.w_size.toNat := ssN
      have i1N : (keepSlide d).insert.toNat ≤ d.insert.toNat ∧ (keepSlide d).insert.toNat ≤ (keepSlide d).strstart.toNat := by
        show (if d.insert > d.strstart - d.w_size then d.strstart - d.w_size else d.insert).toNat ≤ _ ∧
          (if d.insert > d.strstart - d.w_size then d.strstart - d.w_size else d.insert).toNat ≤ (d.strstart - d.w_size).toNat
        split
        · rename_i gt; have := UInt32.lt_iff_toNat_lt.mp gt; omega
        · rename_i ngt
          have : ¬ (d.strstart - d.w_size).toNat < d.insert.toNat := fun c => ngt (UInt32.lt_iff_toNat_lt.mpr c)
          omega
      have m1 : (keepSlide d).«matches».toNat ≤ 2 := by
        have := shape.slides.1
        show (if d.«matches» < 2 then d.«matches» + 1 else d.«matches»).toNat ≤ 2
        split
        · rename_i lt; have := UInt32.lt_iff_toNat_lt.mp lt; rw [UInt32.toNat_add]; simp at this ⊢; omega
        · omega
      let e3 := keepState (keepSlide d) ((keepSlide d).strstart + used) ((keepSlide d).insert + MIN used ((keepSlide d).w_size - (keepSlide d).insert)) (keepSlide d).«matches»
        ((keepSlide d).strstart + used).toUInt64.toInt64 (keepSlide d).high_water
      have minLe1 := min_toNat_le used ((keepSlide d).w_size - (keepSlide d).insert)
      have sumN : ((keepSlide d).strstart + used).toNat = (keepSlide d).strstart.toNat + used.toNat := by
        rw [UInt32.toNat_add]; omega
      have insN : ((keepSlide d).insert + MIN used ((keepSlide d).w_size - (keepSlide d).insert)).toNat =
          (keepSlide d).insert.toNat + (MIN used ((keepSlide d).w_size - (keepSlide d).insert)).toNat := by
        rw [UInt32.toNat_add]; omega
      have bsN : (((keepSlide d).strstart + used).toUInt64.toInt64).toInt = ((keepSlide d).strstart + used).toNat := u32_toInt64_toInt _
      have run : storedKeep (some (.tab ds)) (some r) used h =
          .ok ((), setD { h with bytes := upd h.bytes w (some wa2) } ds e3) := by
        have stateP : (Space.put h (BRef.blk w) wa1).dstates ds = some d := state0
        have heapEq : setD (Space.put (setD (Space.put h (BRef.blk w) wa1) ds (keepSlide d)) (BRef.blk w) wa2) ds e3 =
            setD { h with bytes := upd h.bytes w (some wa2) } ds e3 := by
          rw [put_setD, setD_setD, put_blk_put_blk]; rfl
        rw [← heapEq, ← w2]
        unfold storedKeep
        simp only [bind_app, ldDeflateState_tab state0, big, ite_false, slide, ite_true, dstW, copy1, wrD_eq,
          stateP]
        rfl
      have hash1 : LevelHash (setD (Space.put h (BRef.blk w) wa1) ds (keepSlide d)) (keepSlide d) :=
        level_hash_slide hash0 zero.2.1 zero.2.1 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl
          ⟨d.w_bits.toNat, wsize⟩ (by omega) (by omega) s1N i1N.1 (fun _ _ => rfl)
          (fun w' wa' e g' => by
            have : w' = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using e.symm
            subst this
            have : wa' = wa := Option.some.inj (g'.symm.trans getW)
            subst this
            refine ⟨wa1, upd_same _ _ _, fun i lt => ?_⟩
            rw [hwa1, bfn_copyRange _ _ _ _ _ _ (by omega)]
            rw [if_pos (by omega)]
            congr 1; omega)
      have hash2 : LevelHash (setD { h with bytes := upd h.bytes w (some wa2) } ds e3) e3 :=
        level_hash_write hash1 zero.2.1 zero.2.1 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl
          (by show (keepSlide d).strstart.toNat ≤ ((keepSlide d).strstart + used).toNat; omega)
          (by show (keepSlide d).strstart.toNat - (keepSlide d).insert.toNat ≤ ((keepSlide d).strstart + used).toNat -
                ((keepSlide d).insert + MIN used ((keepSlide d).w_size - (keepSlide d).insert)).toNat; omega)
          (fun _ _ => rfl)
          (fun w' wa' e g' => by
            have e' : d.window = .ref (.blk w') 0 := e
            have : w' = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using e'.symm
            subst this
            have : wa' = wa1 := Option.some.inj (g'.symm.trans (upd_same _ _ _))
            subst this
            refine ⟨wa2, upd_same _ _ _, fun i lt => ?_⟩
            rw [hwa2, bfn_copyRange _ _ _ _ _ _ (by rw [size1]; omega)]
            rw [ite_eq_right (by omega)])
      have shape3 : Shape e3 := shape_keep shape level0 _ _ _ _ _ (by rw [sumN]; omega) (by omega)
        (by rw [bsN]; omega) (by rw [bsN]; omega) (fun _ => by omega) hwLe m1
      obtain ⟨invG, buffersG, sizesG⟩ := window_state_step inv buffers level0 win getW wa2 size2 e3
        ⟨_, _, _, _, _, rfl⟩ shape3 hash2
      exact ⟨_, e3, run, invG, buffersG, sizesG, ⟨_, _, _, _, _, rfl⟩, rfl, rfl⟩
    · have slideN : ¬ d.window_size.toNat - d.strstart.toNat ≤ used.toNat := by
        intro c; apply slide; apply UInt64.le_iff_toNat_le.mpr; rw [wsS]; simpa using c
      have w2 := keep_write (H := h) (r := r) (z := z) used state0 win getWv ro
        (by rw [sizeW]; omega) hz src inGet inBound consumed apart
      obtain ⟨wa2, hwa2⟩ : ∃ x, x = copyRange wa ia d.strstart.toNat (io - used.toNat) used.toNat := ⟨_, rfl⟩
      rw [← hwa2] at w2
      have size2 : wa2.size = wa.size := by rw [hwa2, size_copyRange]
      let e3 := keepState d (d.strstart + used) (d.insert + MIN used (d.w_size - d.insert)) d.«matches»
        (d.strstart + used).toUInt64.toInt64 d.high_water
      have sumN : (d.strstart + used).toNat = d.strstart.toNat + used.toNat := by
        rw [UInt32.toNat_add]; omega
      have insN : (d.insert + MIN used (d.w_size - d.insert)).toNat =
          d.insert.toNat + (MIN used (d.w_size - d.insert)).toNat := by
        rw [UInt32.toNat_add]; omega
      have bsN : ((d.strstart + used).toUInt64.toInt64).toInt = (d.strstart + used).toNat := u32_toInt64_toInt _
      have run : storedKeep (some (.tab ds)) (some r) used h =
          .ok ((), setD { h with bytes := upd h.bytes w (some wa2) } ds e3) := by
        rw [show setD { h with bytes := upd h.bytes w (some wa2) } ds e3 = setD (Space.put h (BRef.blk w) wa2) ds e3 from rfl,
          ← w2]
        unfold storedKeep
        simp only [bind_app, ldDeflateState_tab state0, big, ite_false, slide]
      have hash2 : LevelHash (setD { h with bytes := upd h.bytes w (some wa2) } ds e3) e3 :=
        level_hash_write hash0 zero.2.1 zero.2.1 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl
          (by show d.strstart.toNat ≤ (d.strstart + used).toNat; omega)
          (by show d.strstart.toNat - d.insert.toNat ≤ (d.strstart + used).toNat -
                (d.insert + MIN used (d.w_size - d.insert)).toNat; omega)
          (fun _ _ => rfl)
          (fun w' wa' e g' => by
            have : w' = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using e.symm
            subst this
            have : wa' = wa := Option.some.inj (g'.symm.trans getW)
            subst this
            refine ⟨wa2, upd_same _ _ _, fun i lt => ?_⟩
            rw [hwa2, bfn_copyRange _ _ _ _ _ _ (by omega)]
            rw [ite_eq_right (by omega)])
      have shape3 : Shape e3 := shape_keep shape level0 _ _ _ _ _ (by rw [sumN]; omega) (by omega)
        (by rw [bsN]; omega) (by rw [bsN]; omega) (fun av => by have := shape.available av; omega) hwLe
        shape.slides.1
      obtain ⟨invG, buffersG, sizesG⟩ := window_state_step inv buffers level0 win getW wa2 size2 e3
        ⟨_, _, _, _, _, rfl⟩ shape3 hash2
      exact ⟨_, e3, run, invG, buffersG, sizesG, ⟨_, _, _, _, _, rfl⟩, rfl, rfl⟩


/-! ## Steps that also change the stream record -/

theorem hashing_congr {g g' : Heap} {d : DeflateState} (hash : Hashing g d)
    (bytes : g'.bytes = g.bytes) (words : g'.words = g.words) : Hashing g' d := by
  obtain ⟨chains, slid, rolling⟩ := hash
  refine ⟨fun zero => ?_, fun one => ?_, fun a b large => ?_⟩
  · obtain ⟨w, p, q, wa, pa, qa, win, prv, hd, hw, hp, hq, H⟩ := chains zero
    exact ⟨w, p, q, wa, pa, qa, win, prv, hd, by rw [bytes]; exact hw, by rw [words]; exact hp,
      by rw [words]; exact hq, H⟩
  · obtain ⟨w, p, q, wa, pa, qa, win, prv, hd, hw, hp, hq, H⟩ := slid one
    exact ⟨w, p, q, wa, pa, qa, win, prv, hd, by rw [bytes]; exact hw, by rw [words]; exact hp,
      by rw [words]; exact hq, H⟩
  · obtain ⟨w, wa, win, hw, form⟩ := rolling a b large
    exact ⟨w, wa, win, by rw [bytes]; exact hw, form⟩

theorem stream_put_words (h : Heap) (r : ZStreamRef) (z : ZStream) : (r.put h z).words = h.words := by
  cases r <;> simp only [ZStreamRef.put] <;> split <;> rfl

/-- A new stream record with accounted cursors keeps `DInv` and the caller ranges. -/
theorem dinv_stream_put {g : Heap} {r : ZStreamRef} {ds : Nat} {z z' : ZStream} {d : DeflateState}
    {used produced : Nat} (inv : DInv g r ds z d) (buffers : StreamBuffers g r)
    (account : StreamAccounting z z' used produced) :
    DInv (r.put g z') r ds z' d ∧ StreamBuffers (r.put g z') r ∧ ByteSizes g (r.put g z') := by
  have good := good_stream_put inv.good z' account.2.2.2.2.2.2.1 account.2.2.2.2.2.2.2.1
    account.2.2.2.2.2.2.2.2.1
  have sizes := sizes_stream_put g r z'
  have owned := stream_owned_keys inv.good good rfl rfl rfl rfl
  refine ⟨⟨good, ⟨account.2.2.2.2.2.2.2.1.trans inv.alloc.1, account.2.2.2.2.2.2.2.2.1.trans inv.alloc.2⟩,
    by unfold LibraryGlobals; rw [ZStreamRef.put_static]; exact inv.globals, inv.shape,
    hashing_congr inv.hashing (ZStreamRef.put_bytes _ _ _) (stream_put_words _ _ _), ?_⟩,
    stream_buffers_sizes inv.good.live.hz good.live.hz buffers sizes owned account, sizes⟩
  obtain ⟨⟨xs, ⟨b, a, pbuf, getP, ledger⟩, dist⟩, clear, below⟩ := inv.symbols
  exact ⟨⟨xs, ⟨b, a, pbuf, by rw [ZStreamRef.put_bytes]; exact getP, ledger⟩, dist⟩, clear, below⟩

theorem setD_put_comm (h : Heap) (r : ZStreamRef) (z : ZStream) (ds : Nat) (d : DeflateState) :
    setD (r.put h z) ds d = r.put (setD h ds d) z := by
  cases r <;> simp only [ZStreamRef.put, setD] <;> split <;> rename_i heq <;> simp only [heq] <;> rfl


/-! ## The refill -/

/-- The state after the slide of the refill. -/
def refillSlide (d : DeflateState) : DeflateState :=
  { keepSlide d with block_start := Int64.ofInt (d.block_start.toInt - d.w_size.toNat) }

theorem stored_slide_run {h : Heap} {ds w : Nat} {d : DeflateState} {wa : Array UInt8}
    (state : h.dstates ds = some d) (win : d.window = .ref (.blk w) 0) (get : Space.get h (BRef.blk w) = some wa)
    (ro : Space.ro h (BRef.blk w) = false) (size : wa.size = 2 * d.w_size.toNat)
    (wide : d.w_size.toNat ≤ d.strstart.toNat) (high : d.strstart.toNat ≤ 2 * d.w_size.toNat)
    (low : 0 ≤ d.block_start.toInt) (top : d.block_start.toInt ≤ d.strstart.toNat) :
    storedSlide (some (.tab ds)) d h =
      .ok ((), setD (Space.put h (BRef.blk w) (copyRange wa wa 0 d.w_size.toNat (d.strstart - d.w_size).toNat)) ds
        (refillSlide d)) := by
  have ssLt := d.strstart.toNat_lt
  have wsN : d.w_size.toUInt64.toInt64.toInt = d.w_size.toNat := u32_toInt64_toInt _
  have sub := lsub_value d.block_start d.w_size.toUInt64.toInt64 h (by rw [wsN]; omega) (by rw [wsN]; omega)
  rw [wsN] at sub
  have ssN : (d.strstart - d.w_size).toNat = d.strstart.toNat - d.w_size.toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr wide)
  have dst : padd d.window d.w_size.toNat h = .ok (.ref (.blk w) d.w_size.toNat, h) := by
    rw [win]; have := padd_view (io := 0) (n := d.w_size.toNat) get (by omega)
    rw [Nat.zero_add] at this; exact this
  have copy : memcpyB d.window (.ref (.blk w) d.w_size.toNat) (d.strstart - d.w_size).toNat h =
      .ok ((), Space.put h (BRef.blk w) (copyRange wa wa 0 d.w_size.toNat (d.strstart - d.w_size).toNat)) := by
    rw [win]; exact Ptr.memcpy_ok get get ro (by omega) (by omega) (Or.inr (Or.inl (by omega)))
  have state1 : (Space.put h (BRef.blk w) (copyRange wa wa 0 d.w_size.toNat (d.strstart - d.w_size).toNat)).dstates ds =
      some d := state
  unfold storedSlide
  simp only [bind_app, sub, dst, copy, wrD_eq, state1]
  rfl

/-- The state after the read of the refill and the high-water mark. -/
def refillRead (e : DeflateState) (n : UInt32) : DeflateState :=
  let e2 := { e with strstart := e.strstart + n, insert := e.insert + MIN n (e.w_size - e.insert) }
  { e2 with high_water := if e2.high_water < e2.strstart.toUInt64 then e2.strstart.toUInt64 else e2.high_water }

theorem stored_read_run {H : Heap} {r : ZStreamRef} {ds w : Nat} {z : ZStream} {e : DeflateState}
    {wb : Array UInt8} (n : UInt32) (state : H.dstates ds = some e) (hz : r.get H = some z)
    (zst : z.state = some (.deflate ds)) (globals : e.wrap = 2 → CrcGlobals H)
    (win : e.window = .ref (.blk w) 0) (get : H.bytes w = some wb) (ro : H.ro w = false)
    (fit : e.strstart.toNat + n.toNat ≤ wb.size) (avail : n.toNat ≤ z.avail_in.toNat)
    (input : n ≠ 0 → ∃ ref io ia, z.next_in = .ref ref io ∧ Space.get H ref = some ia ∧
      io + z.avail_in.toNat ≤ ia.size ∧ ref ≠ .blk w) :
    ∃ waF zF, storedRead (some (.tab ds)) (some r) n H =
        .ok ((), setD (r.put { H with bytes := upd H.bytes w (some waF) } zF) ds (refillRead e n)) ∧
      waF.size = wb.size ∧ (∀ i, i < e.strstart.toNat → bfn waF i = bfn wb i) ∧
      StreamAccounting z zF n.toNat 0 := by
  by_cases zero : n = 0
  · subst zero
    refine ⟨wb, z, ?_, rfl, fun _ _ => rfl, ?_⟩
    · have keep : r.put { H with bytes := upd H.bytes w (some wb) } z = H := by
        rw [upd_self _ _ _ get]; exact ZStreamRef.put_self hz
      rw [keep]
      unfold storedRead
      simp only [bne_self_eq_false, Bool.false_eq_true, ite_false, bind_app, pure_app, wrD_eq, state]
      have e0 : refillRead e 0 = { e with high_water := if e.high_water < e.strstart.toUInt64 then e.strstart.toUInt64 else e.high_water } := by
        unfold refillRead MIN
        simp
      rw [e0]
    · have := Zlib.Deflate.Engine.Proofs.stream_accounting_self z
      simpa using this
  · obtain ⟨ref, io, ia, src, inGet, inBound, apart⟩ := input zero
    have count : rbLen z.avail_in n = n := by
      unfold rbLen; split
      · rfl
      · rename_i big
        have b2 : z.avail_in.toNat ≤ n.toNat := UInt32.le_iff_toNat_le.mp (by simpa using big)
        exact UInt32.toNat_inj.mp (by omega)
    have nz : n.toNat ≠ 0 := fun c => zero (UInt32.toNat_inj.mp (by rw [c]; rfl))
    have read := read_buf_any (bo := e.strstart.toNat) hz zst state globals src inGet get ro n
      (by rw [count]; exact zero) (by rw [count]; omega) (by rw [count]; exact fit)
      (Or.inl (Ne.symm apart))
    rw [count] at read
    have getv : Space.get H (BRef.blk w) = some wb := get
    have dst : padd e.window e.strstart.toNat H = .ok (.ref (.blk w) e.strstart.toNat, H) := by
      rw [win]; have := padd_view (io := 0) (n := e.strstart.toNat) getv (by omega)
      rw [Nat.zero_add] at this; exact this
    have state1 : (r.put { H with bytes := upd H.bytes w (some (copyRange wb ia e.strstart.toNat io n.toNat)) }
        (readStream z n ref io (checksumValue e.wrap z.adler ((ia.toList.drop io).take n.toNat)))).dstates ds =
        some e := by
      rw [ZStreamRef.put_dstates]; exact state
    refine ⟨copyRange wb ia e.strstart.toNat io n.toNat,
      readStream z n ref io (checksumValue e.wrap z.adler ((ia.toList.drop io).take n.toNat)), ?_,
      size_copyRange _ _ _ _ _, fun i lt => ?_, read_stream_accounting z n ref io _ src avail⟩
    · unfold storedRead
      simp only [show (n != 0) = true by simpa using zero, ite_true, bind_app, ldDeflateState_tab state, dst,
        read, wrD_eq, state1, setD_dstates_same, setD_setD]
      rfl
    · rw [bfn_copyRange _ _ _ _ _ _ fit, ite_eq_right (by omega)]

end Zlib.Deflate.Engine.Proofs
