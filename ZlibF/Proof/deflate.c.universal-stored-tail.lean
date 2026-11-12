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
  have topC : chainTop d ≤ chainTop d' := by
    unfold chainTop; rw [la, la']; simp only [UInt32.toNat_zero, Nat.add_zero]; omega
  refine ⟨fun zero => ?_, fun one => ?_⟩
  · rw [slides] at zero
    obtain ⟨w, p, q, wa, pa, qa, win, prv, hd, hw, hp, hq, H⟩ := hash.1 zero
    obtain ⟨wa', gw, same⟩ := window w wa win hw
    refine ⟨w, p, q, wa', pa, qa, by rw [kw]; exact win, by rw [kp]; exact prv, by rw [kq]; exact hd, gw,
      by rw [words p (Or.inl prv)]; exact hp, by rw [words q (Or.inr hd)]; exact hq, ?_⟩
    rw [khs, khsh, khm, kws, la']
    rw [la] at H
    have H' := chains_congr H (fun _ => rfl) (fun _ => rfl) (w' := bfn wa') (fun i lt => same i (by simp at lt; omega))
    exact chains_mono H' topC (by omega)
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
    have := chainTop_le d
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
    (water : hw.toNat ≤ d.window_size.toNat) (slides : m.toNat ≤ 2) (init : ss.toNat ≤ hw.toNat) :
    Shape (keepState d ss ins m bs hw) := by
  have zero := shape.levelZero level0
  have la : d.lookahead.toNat = 0 := by rw [zero.2.1]; rfl
  refine ⟨by show ss.toNat + d.lookahead.toNat ≤ d.window_size.toNat; omega, insert,
    fun big => absurd big (by show ¬ 3 ≤ d.lookahead.toNat; omega), shape.prevLength, shape.matchLength,
    shape.matchAvailable, high, fun ne => absurd level0 ne, fun _ => ⟨low, zero.2.1, zero.2.2⟩, available,
    fun (big : 3 ≤ d.match_length.toNat) => ?_, fun lo => absurd lo (by show ¬ 1 ≤ d.level.toInt; rw [level0]; decide), water,
    (show ss.toNat + d.lookahead.toNat ≤ hw.toNat by omega), shape.lastFlush,
    shape.headerFlush, shape.trailer, shape.biValid, shape.cursor, shape.symRoom,
    ⟨slides, fun ne => absurd level0 ne⟩⟩
  have := (shape.pendingMatch big).2.2.1
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

/-- The high-water update after keeping the input. -/
def waterState (e : DeflateState) : DeflateState :=
  { e with high_water := if e.high_water < e.strstart.toUInt64 then e.strstart.toUInt64 else e.high_water }

theorem water_wr (X : Heap) (ds : Nat) (e : DeflateState) :
    wr (some (.tab ds)) (fun d => { d with high_water := if d.high_water < d.strstart.toUInt64 then d.strstart.toUInt64 else d.high_water })
      (setD X ds e) = .ok ((), setD X ds (waterState e)) := by
  rw [wrD_eq, setD_dstates_same]
  dsimp only
  rw [setD_setD]
  rfl

theorem water_facts {d : DeflateState} (e : DeflateState) (high : e.high_water.toNat ≤ d.window_size.toNat)
    (room : e.strstart.toNat ≤ d.window_size.toNat) (small : d.window_size.toNat < 2 ^ 32) :
    (waterState e).high_water.toNat ≤ d.window_size.toNat ∧ e.strstart.toNat ≤ (waterState e).high_water.toNat := by
  unfold waterState
  dsimp only
  split
  · rename_i lt
    simp only [UInt32.toNat_toUInt64]
    omega
  · rename_i nlt
    have : ¬ e.high_water.toNat < e.strstart.toNat := by
      intro c; apply nlt; rw [UInt64.lt_iff_toNat_lt]; simpa using c
    omega

/-- A window write and a state write are private. -/
theorem window_priv {h : Heap} {r : ZStreamRef} {ds w : Nat} {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (wa' : Array UInt8) (d' : DeflateState) :
    PrivStep h (setD { h with bytes := upd h.bytes w (some wa') } ds d') r ds d :=
  (priv_setB h r ds w d wa' (Or.inr (Or.inl win)) (by simp [get])).trans
    (priv_setD _ r ds d d' (by simpa [Zlib.Trees.Proofs.Out.setB] using good.live.hs))

/-- A window write, a stream write and a state write are private. -/
theorem canonical_priv {h : Heap} {r : ZStreamRef} {ds w : Nat} {z zF : ZStream} {d : DeflateState}
    {wa : Array UInt8} (good : DGood h r ds z d) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (waF : Array UInt8) (eF : DeflateState) :
    PrivStep h (setD (r.put { h with bytes := upd h.bytes w (some waF) } zF) ds eF) r ds d :=
  ((priv_setB h r ds w d waF (Or.inr (Or.inl win)) (by simp [get])).trans
    (priv_put _ r ds d zF)).trans
    (priv_setD _ r ds d eF (by rw [ZStreamRef.put_dstates]; simpa [Zlib.Trees.Proofs.Out.setB] using good.live.hs))

set_option maxHeartbeats 8000000 in
/-- **`deflate_stored` keeps the consumed input in the window.** `used` bytes were consumed by the
loop, so the input pointer is at least `used` past the start of its view. -/
theorem stored_keep {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (buffers : StreamBuffers h r) (level0 : d.level = 0)
    (used : UInt32) {ref : BRef} {io : Nat} {ia : Array UInt8}
    (src : z.next_in = .ref ref io) (inGet : Space.get h ref = some ia) (inBound : io ≤ ia.size)
    (consumed : used.toNat ≤ io) (apartW : ∀ w, d.window = .ref (.blk w) 0 → ref ≠ .blk w)
    (apartS : ref ≠ .dstate_depth ds) :
    ∃ gm g d', storedKeep (some (.tab ds)) (some r) used h = .ok ((), gm) ∧
      wr (some (.tab ds)) (fun d => { d with high_water := if d.high_water < d.strstart.toUInt64 then d.strstart.toUInt64 else d.high_water }) gm =
        .ok ((), g) ∧ DInv g r ds z d' ∧
      StreamBuffers g r ∧ ByteSizes h g ∧ (∃ ss ins m bs hw, d' = keepState d ss ins m bs hw) ∧
      g.static = h.static ∧ g.nalloc = h.nalloc ∧ PrivStep h g r ds d := by
  have good := inv.good
  have wsSmall : d.window_size.toNat < 2 ^ 32 := by
    have := good.inv.wsz; have := good.inv.wsize; have := good.inv.wbits_hi
    have : 2 ^ d.w_bits.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) good.inv.wbits_hi
    omega
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
    have wf := water_facts (d := d) d' hwLe (by show d.w_size.toNat ≤ _; omega) wsSmall
    have shape' : Shape (waterState d') := shape_keep shape level0 d.w_size d.w_size 2 d.w_size.toUInt64.toInt64
      (waterState d').high_water (by omega) (Nat.le_refl _)
      (by rw [bsN]; omega) (by rw [bsN]; omega) (fun _ => by omega) wf.1 (by decide) wf.2
    have hash' : LevelHash (setD { h with bytes := upd h.bytes w (some wa1) } ds (waterState d')) (waterState d') :=
      ⟨fun e => absurd (show (2 : UInt32) = 0 from e) (by decide),
        fun e => absurd (show (2 : UInt32) = 1 from e) (by decide)⟩
    obtain ⟨invG, buffersG, sizesG⟩ := window_state_step inv buffers level0 win getW wa1
      (by simp [wa1, size_copyRange]) (waterState d') ⟨_, _, _, _, _, rfl⟩ shape' hash'
    exact ⟨_, _, waterState d', run, water_wr _ _ _, invG, buffersG, sizesG, ⟨_, _, _, _, _, rfl⟩, rfl, rfl,
      window_priv good win getW _ _⟩
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
      have wf := water_facts (d := d) e3 hwLe (by show ((keepSlide d).strstart + used).toNat ≤ _; rw [sumN]; omega)
        wsSmall
      have shape3 : Shape (waterState e3) := shape_keep shape level0 ((keepSlide d).strstart + used)
        ((keepSlide d).insert + MIN used ((keepSlide d).w_size - (keepSlide d).insert)) (keepSlide d).«matches»
        ((keepSlide d).strstart + used).toUInt64.toInt64 (waterState e3).high_water (by rw [sumN]; omega) (by omega)
        (by rw [bsN]; omega) (by rw [bsN]; omega) (fun _ => by omega) wf.1 m1 wf.2
      obtain ⟨invG, buffersG, sizesG⟩ := window_state_step inv buffers level0 win getW wa2 size2 (waterState e3)
        ⟨_, _, _, _, _, rfl⟩ shape3 hash2
      exact ⟨_, _, waterState e3, run, water_wr _ _ _, invG, buffersG, sizesG, ⟨_, _, _, _, _, rfl⟩, rfl, rfl,
      window_priv good win getW _ _⟩
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
      have wf := water_facts (d := d) e3 hwLe (by show (d.strstart + used).toNat ≤ _; rw [sumN]; omega) wsSmall
      have shape3 : Shape (waterState e3) := shape_keep shape level0 (d.strstart + used)
        (d.insert + MIN used (d.w_size - d.insert)) d.«matches» (d.strstart + used).toUInt64.toInt64
        (waterState e3).high_water (by rw [sumN]; omega) (by omega)
        (by rw [bsN]; omega) (by rw [bsN]; omega) (fun av => by have := shape.available av; omega) wf.1
        shape.slides.1 wf.2
      obtain ⟨invG, buffersG, sizesG⟩ := window_state_step inv buffers level0 win getW wa2 size2 (waterState e3)
        ⟨_, _, _, _, _, rfl⟩ shape3 hash2
      exact ⟨_, _, waterState e3, run, water_wr _ _ _, invG, buffersG, sizesG, ⟨_, _, _, _, _, rfl⟩, rfl, rfl,
      window_priv good win getW _ _⟩


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
      StreamAccounting z zF n.toNat 0 ∧ Totals z zF n.toNat 0 := by
  by_cases zero : n = 0
  · subst zero
    refine ⟨wb, z, ?_, rfl, fun _ _ => rfl, ?_, Totals.refl z⟩
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
      size_copyRange _ _ _ _ _, fun i lt => ?_, read_stream_accounting z n ref io _ src avail,
      by simp [readStream], by simp [readStream]⟩
    · unfold storedRead
      simp only [show (n != 0) = true by simpa using zero, ite_true, bind_app, ldDeflateState_tab state, dst,
        read, wrD_eq, state1, setD_dstates_same, setD_setD]
      rfl
    · rw [bfn_copyRange _ _ _ _ _ _ fit, ite_eq_right (by omega)]


theorem input_not_state {h : Heap} {r : ZStreamRef} {ds io : Nat} {z : ZStream} {d : DeflateState} {ref : BRef}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (pointer : z.next_in = .ref ref io) :
    ref ≠ .dstate_depth ds := by
  intro e
  subst e
  obtain ⟨z0, get0, caller, _, _⟩ := buffers
  have same : z0 = z := Option.some.inj (get0.symm.trans good.live.hz)
  subst z0
  rw [pointer] at caller
  rcases caller with null | ⟨_, _, outside⟩
  · cases null
  · exact outside ds rfl ((stream_owned_deflate good ds).mpr (Or.inl rfl))

theorem level_hash_congr {g g' : Heap} {d : DeflateState} (hash : LevelHash g d)
    (bytes : g'.bytes = g.bytes) (words : g'.words = g.words) : LevelHash g' d := by
  refine ⟨fun zero => ?_, fun one => ?_⟩
  · obtain ⟨w, p, q, wa, pa, qa, win, prv, hd, hw, hp, hq, H⟩ := hash.1 zero
    exact ⟨w, p, q, wa, pa, qa, win, prv, hd, by rw [bytes]; exact hw, by rw [words]; exact hp,
      by rw [words]; exact hq, H⟩
  · obtain ⟨w, p, q, wa, pa, qa, win, prv, hd, hw, hp, hq, H⟩ := hash.2 one
    exact ⟨w, p, q, wa, pa, qa, win, prv, hd, by rw [bytes]; exact hw, by rw [words]; exact hp,
      by rw [words]; exact hq, H⟩


/-- **A window-side step with input accounting.** -/
theorem canonical_step {h : Heap} {r : ZStreamRef} {ds w : Nat} {z zF : ZStream} {d : DeflateState}
    {wa : Array UInt8} {used produced : Nat} (inv : DInv h r ds z d) (buffers : StreamBuffers h r)
    (level0 : d.level = 0) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (waF : Array UInt8) (size : waF.size = wa.size) (account : StreamAccounting z zF used produced)
    (eF : DeflateState) (fields : ∃ ss ins m bs hw, eF = keepState d ss ins m bs hw) (shape : Shape eF)
    (hash : LevelHash (setD (r.put { h with bytes := upd h.bytes w (some waF) } zF) ds eF) eF) :
    DInv (setD (r.put { h with bytes := upd h.bytes w (some waF) } zF) ds eF) r ds zF eF ∧
      StreamBuffers (setD (r.put { h with bytes := upd h.bytes w (some waF) } zF) ds eF) r ∧
      ByteSizes h (setD (r.put { h with bytes := upd h.bytes w (some waF) } zF) ds eF) := by
  have hash0 : LevelHash (setD { h with bytes := upd h.bytes w (some waF) } ds eF) eF :=
    level_hash_congr hash (by simp) (by simp [stream_put_words])
  obtain ⟨inv0, buffers0, sizes0⟩ := window_state_step inv buffers level0 win get waF size eF fields shape hash0
  obtain ⟨inv1, buffers1, sizes1⟩ := dinv_stream_put inv0 buffers0 account
  rw [← setD_put_comm] at inv1 buffers1 sizes1
  exact ⟨inv1, buffers1, sizes0.chain sizes1⟩


theorem shape_refill {d : DeflateState} (shape : Shape d) (level0 : d.level = 0) (ss ins m : UInt32) (bs : Int64)
    (hw : UInt64) (n : UInt32) (room : ss.toNat + n.toNat ≤ d.window_size.toNat) (insert : ins.toNat ≤ ss.toNat)
    (low : 0 ≤ bs.toInt) (high : bs.toInt ≤ ss.toNat) (water : hw.toNat ≤ d.window_size.toNat)
    (slides : m.toNat ≤ 2) (available : d.match_available ≠ 0 → 1 ≤ ss.toNat + n.toNat)
    (wsmall : d.window_size.toNat ≤ 65536) :
    Shape (refillRead (keepState d ss ins m bs hw) n) := by
  have ssLt := ss.toNat_lt
  have nLt := n.toNat_lt
  have sumN : (ss + n).toNat = ss.toNat + n.toNat := by
    rw [UInt32.toNat_add]; omega
  have minLe := min_toNat_le n (d.w_size - ins)
  have insN : (ins + MIN n (d.w_size - ins)).toNat = ins.toNat + (MIN n (d.w_size - ins)).toNat := by
    rw [UInt32.toNat_add]; omega
  have e : refillRead (keepState d ss ins m bs hw) n = keepState d (ss + n) (ins + MIN n (d.w_size - ins)) m bs
      (if hw < (ss + n).toUInt64 then (ss + n).toUInt64 else hw) := rfl
  rw [e]
  have hwN : (if hw < (ss + n).toUInt64 then (ss + n).toUInt64 else hw).toNat ≤ d.window_size.toNat := by
    split
    · simp; omega
    · exact water
  have initN : (ss + n).toNat ≤ (if hw < (ss + n).toUInt64 then (ss + n).toUInt64 else hw).toNat := by
    split
    · simp
    · rename_i nlt
      have : ¬ hw.toNat < (ss + n).toNat := by
        intro c; apply nlt; rw [UInt64.lt_iff_toNat_lt]; simpa using c
      omega
  exact shape_keep shape level0 _ _ _ _ _ (by omega) (by omega) low (by rw [sumN]; omega)
    (fun av => by have := available av; omega) hwN slides initN

set_option maxHeartbeats 4000000 in
/-- The read of the refill keeps `DInv`, from a window and state reached from `h` on the window
side, given the shape of the result. -/
theorem refill_finish {h : Heap} {r : ZStreamRef} {ds w : Nat} {z : ZStream} {d : DeflateState}
    {wa : Array UInt8} (inv : DInv h r ds z d) (buffers : StreamBuffers h r) (level0 : d.level = 0)
    (win : d.window = .ref (.blk w) 0) (getW : h.bytes w = some wa)
    (e : DeflateState) (wb : Array UInt8) (sizeB : wb.size = wa.size)
    (fields : ∃ ss ins m bs hw, e = keepState d ss ins m bs hw) (hashE : LevelHash (setD { h with bytes := upd h.bytes w (some wb) } ds e) e)
    (n : UInt32) (avail : n.toNat ≤ z.avail_in.toNat) (fit : e.strstart.toNat + n.toNat ≤ wa.size)
    (small : wa.size ≤ 65536) (grow : e.insert.toNat ≤ e.strstart.toNat)
    (input : z.avail_in ≠ 0 → z.next_in ≠ .null) (shapeF : Shape (refillRead e n)) :
    ∃ g zF, storedRead (some (.tab ds)) (some r) n (setD { h with bytes := upd h.bytes w (some wb) } ds e) =
        .ok ((), g) ∧ DInv g r ds zF (refillRead e n) ∧ StreamBuffers g r ∧ ByteSizes h g ∧
      StreamAccounting z zF n.toNat 0 ∧ g.static = h.static ∧ g.nalloc = h.nalloc ∧ Totals z zF n.toNat 0 ∧
      PrivStep h g r ds d := by
  have good := inv.good
  obtain ⟨ss, ins, m, bs, hw, rfl⟩ := fields
  let H := setD { h with bytes := upd h.bytes w (some wb) } ds (keepState d ss ins m bs hw)
  have stateH : H.dstates ds = some (keepState d ss ins m bs hw) := setD_dstates_same _ _ _
  have hzH : r.get H = some z := by
    show r.get { h with bytes := upd h.bytes w (some wb) } = some z; rw [stream_get_bytes]; exact good.live.hz
  have getH : H.bytes w = some wb := upd_same _ _ _
  have roW : h.ro w = false := by
    obtain ⟨w0, p0, q0, b0, blocks⟩ := good.inv.blocks
    have : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
    subst this; exact blocks.wro
  have globalsH : (keepState d ss ins m bs hw).wrap = 2 → CrcGlobals H := fun _ => by
    have := crc_globals_of_library inv.globals
    exact ⟨this.1, this.2⟩
  have inputH : n ≠ 0 → ∃ ref io ia, z.next_in = .ref ref io ∧ Space.get H ref = some ia ∧
      io + z.avail_in.toNat ≤ ia.size ∧ ref ≠ .blk w := by
    intro nz
    have availNZ : z.avail_in ≠ 0 := by
      intro e0; apply nz; apply UInt32.toNat_inj.mp; rw [e0] at avail; simp at avail ⊢; omega
    obtain ⟨ref, io, pointer⟩ : ∃ ref io, z.next_in = .ref ref io := by
      cases p : z.next_in with
      | null => exact absurd p (input availNZ)
      | ref ref io => exact ⟨ref, io, rfl⟩
    obtain ⟨ia, inGet, inBound⟩ := caller_input_array good buffers pointer
    have apartW := caller_input_window_separate good buffers win pointer
    have apartS := input_not_state good buffers pointer
    refine ⟨ref, io, ia, pointer, ?_, inBound, Ne.symm apartW⟩
    rw [view_setD_other apartS]
    show Space.get (Space.put h (BRef.blk w) wb) ref = some ia
    rw [view_put_other (Ne.symm apartW)]; exact inGet
  obtain ⟨waF, zF, run, sizeF, keepF, accF, totF⟩ := stored_read_run (H := H) n stateH hzH good.live.zst globalsH
    win getH roW (by rw [sizeB]; exact fit) avail inputH
  have heapEq : setD (r.put { H with bytes := upd H.bytes w (some waF) } zF) ds (refillRead (keepState d ss ins m bs hw) n) =
      setD (r.put { h with bytes := upd h.bytes w (some waF) } zF) ds (refillRead (keepState d ss ins m bs hw) n) := by
    show setD (r.put (setD { h with bytes := upd (upd h.bytes w (some wb)) w (some waF) } ds (keepState d ss ins m bs hw)) zF) ds _ = _
    rw [upd_upd, ← setD_put_comm, setD_setD]
  rw [heapEq] at run
  have minLe := min_toNat_le n ((keepState d ss ins m bs hw).w_size - (keepState d ss ins m bs hw).insert)
  have hashF : LevelHash (setD (r.put { h with bytes := upd h.bytes w (some waF) } zF) ds
      (refillRead (keepState d ss ins m bs hw) n)) (refillRead (keepState d ss ins m bs hw) n) := by
    change ss.toNat + n.toNat ≤ wa.size at fit
    change ins.toNat ≤ ss.toNat at grow
    change (MIN n (d.w_size - ins)).toNat ≤ n.toNat at minLe
    have sumN : (ss + n).toNat = ss.toNat + n.toNat := by rw [UInt32.toNat_add]; omega
    have insN : (ins + MIN n (d.w_size - ins)).toNat = ins.toNat + (MIN n (d.w_size - ins)).toNat := by
      rw [UInt32.toNat_add]; omega
    exact level_hash_write hashE (inv.shape.levelZero level0).2.1 (inv.shape.levelZero level0).2.1
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl
      (by show ss.toNat ≤ (ss + n).toNat; omega)
      (by show ss.toNat - ins.toNat ≤ (ss + n).toNat - (ins + MIN n (d.w_size - ins)).toNat
          omega)
      (fun _ _ => by simp [stream_put_words])
      (fun w' wa' e g' => by
        have e' : d.window = .ref (.blk w') 0 := e
        have : w' = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using e'.symm
        subst this
        have : wa' = wb := Option.some.inj (g'.symm.trans (upd_same _ _ _))
        subst this
        exact ⟨waF, by simp, keepF⟩)
  obtain ⟨invG, buffersG, sizesG⟩ := canonical_step inv buffers level0 win getW waF (sizeF.trans sizeB) accF
    (refillRead (keepState d ss ins m bs hw) n) ⟨_, _, _, _, _, rfl⟩ shapeF hashF
  exact ⟨_, zF, run, invG, buffersG, sizesG, accF, by simp, by simp [ZStreamRef.put]; cases r <;> simp only [ZStreamRef.put] <;> split <;> rfl,
    totF, canonical_priv good win getW _ _⟩


set_option maxHeartbeats 8000000 in
/-- **The refill of the window keeps `DInv`.** -/
theorem stored_refill {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (buffers : StreamBuffers h r) (level0 : d.level = 0)
    (input : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ g zF eF used, storedRefill (some (.tab ds)) (some r) d h = .ok ((), g) ∧ DInv g r ds zF eF ∧
      StreamBuffers g r ∧ ByteSizes h g ∧ StreamAccounting z zF used 0 ∧
      (∃ ss ins m bs hw, eF = keepState d ss ins m bs hw) ∧ g.static = h.static ∧ g.nalloc = h.nalloc ∧
          Totals z zF used 0 ∧ PrivStep h g r ds d := by
  have good := inv.good
  have shape := inv.shape
  have zero := shape.levelZero level0
  obtain ⟨w, wa, win, getW, sizeW⟩ := window_block good
  have wsz := good.inv.wsz
  have wsize := good.inv.wsize
  have wbits := good.inv.wbits_hi
  have wbitsLo := good.inv.wbits_lo
  have wpow : 2 ^ d.w_bits.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) wbits
  have wpowLo : 2 ^ 9 ≤ 2 ^ d.w_bits.toNat := Nat.pow_le_pow_right (by omega) wbitsLo
  have room := shape.room
  have la : d.lookahead.toNat = 0 := by rw [zero.2.1]; rfl
  have insLe := shape.insert
  have bsHi := shape.blockStart
  have hwLe := shape.highWater
  have hz := good.live.hz
  have state0 := good.live.hs
  have getWv : Space.get h (BRef.blk w) = some wa := getW
  have ro : Space.ro h (BRef.blk w) = false := by
    obtain ⟨w0, p0, q0, b0, blocks⟩ := good.inv.blocks
    have : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
    subst this; exact blocks.wro
  have hash0 : LevelHash h d := ⟨inv.hashing.chains, inv.hashing.slid⟩
  have readAvail : ∀ H : Heap, r.get H = some z → zrd (some r) (·.avail_in) H = .ok (z.avail_in, H) := by
    intro H hzH; simp [zrd_eq, hzH]
  have have0N : ((d.window_size - d.strstart.toUInt64).toUInt32).toNat = d.window_size.toNat - d.strstart.toNat := by
    rw [UInt64.toNat_toUInt32, UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]
    simp; omega
  have ssLt := d.strstart.toNat_lt
  have aLt := z.avail_in.toNat_lt
  have hSelf : setD { h with bytes := upd h.bytes w (some wa) } ds d = h := by
    rw [upd_self _ _ _ getW]; exact setD_self state0
  unfold storedRefill
  simp only [bind_app, readAvail h hz]
  by_cases cond : (decide (z.avail_in > (d.window_size - d.strstart.toUInt64).toUInt32) &&
      decide (d.block_start ≥ d.w_size.toUInt64.toInt64)) = true
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at cond
    obtain ⟨more, far⟩ := cond
    have moreN := UInt32.lt_iff_toNat_lt.mp more
    rw [have0N] at moreN
    have wsN : d.w_size.toUInt64.toInt64.toInt = d.w_size.toNat := u32_toInt64_toInt _
    have farN : (d.w_size.toNat : Int) ≤ d.block_start.toInt := by
      have := Int64.le_iff_toInt_le.mp far; rw [wsN] at this; exact this
    have wide : d.w_size.toNat ≤ d.strstart.toNat := by omega
    have slide := stored_slide_run state0 win getWv ro (by omega) wide (by omega) zero.1 bsHi
    obtain ⟨wa1, hwa1⟩ : ∃ x, x = copyRange wa wa 0 d.w_size.toNat (d.strstart - d.w_size).toNat := ⟨_, rfl⟩
    rw [← hwa1] at slide
    have size1 : wa1.size = wa.size := by rw [hwa1, size_copyRange]
    have ssN : (d.strstart - d.w_size).toNat = d.strstart.toNat - d.w_size.toNat :=
      UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr wide)
    have hz1 : r.get (setD (Space.put h (BRef.blk w) wa1) ds (refillSlide d)) = some z := by
      show r.get (Space.put h (BRef.blk w) wa1) = some z
      rw [view_put_stream]; exact hz
    have i1 : (refillSlide d).insert.toNat ≤ d.insert.toNat ∧
        (refillSlide d).insert.toNat ≤ (d.strstart - d.w_size).toNat := by
      show (if d.insert > d.strstart - d.w_size then d.strstart - d.w_size else d.insert).toNat ≤ _ ∧
        (if d.insert > d.strstart - d.w_size then d.strstart - d.w_size else d.insert).toNat ≤ _
      split
      · rename_i gt; have := UInt32.lt_iff_toNat_lt.mp gt; omega
      · rename_i ngt
        have : ¬ (d.strstart - d.w_size).toNat < d.insert.toNat := fun c => ngt (UInt32.lt_iff_toNat_lt.mpr c)
        omega
    have m1 : (refillSlide d).«matches».toNat ≤ 2 := by
      have := shape.slides.1
      show (if d.«matches» < 2 then d.«matches» + 1 else d.«matches»).toNat ≤ 2
      split
      · rename_i lt; have := UInt32.lt_iff_toNat_lt.mp lt; rw [UInt32.toNat_add]; simp at this ⊢; omega
      · omega
    have bs1 : (Int64.ofInt (d.block_start.toInt - d.w_size.toNat)).toInt = d.block_start.toInt - d.w_size.toNat :=
      int64_ofInt_toInt _ (by omega) (by omega)
    have hashE : LevelHash (setD { h with bytes := upd h.bytes w (some wa1) } ds (refillSlide d)) (refillSlide d) :=
      level_hash_slide hash0 zero.2.1 zero.2.1 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl
        ⟨d.w_bits.toNat, wsize⟩ (by omega) wide ssN i1.1 (fun _ _ => rfl)
        (fun w' wa' e g' => by
          have : w' = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using e.symm
          subst this
          have : wa' = wa := Option.some.inj (g'.symm.trans getW)
          subst this
          refine ⟨wa1, upd_same _ _ _, fun i lt => ?_⟩
          rw [hwa1, bfn_copyRange _ _ _ _ _ _ (by omega), if_pos (by omega)]
          congr 1; omega)
    have have1N : ((d.window_size - d.strstart.toUInt64).toUInt32 + d.w_size).toNat =
        d.window_size.toNat - d.strstart.toNat + d.w_size.toNat := by
      rw [UInt32.toNat_add, have0N]; omega
    have finishA : ∀ n : UInt32, n.toNat ≤ z.avail_in.toNat →
        n.toNat ≤ d.window_size.toNat - d.strstart.toNat + d.w_size.toNat → 1 ≤ n.toNat →
        ∃ g zF eF used, storedRead (some (.tab ds)) (some r) n (setD (Space.put h (BRef.blk w) wa1) ds (refillSlide d)) =
            .ok ((), g) ∧ DInv g r ds zF eF ∧ StreamBuffers g r ∧ ByteSizes h g ∧ StreamAccounting z zF used 0 ∧
          (∃ ss ins m bs hw, eF = keepState d ss ins m bs hw) ∧ g.static = h.static ∧ g.nalloc = h.nalloc ∧
          Totals z zF used 0 ∧ PrivStep h g r ds d := by
      intro n avail fitN one
      have shapeF : Shape (refillRead (refillSlide d) n) := shape_refill shape level0 (d.strstart - d.w_size) (refillSlide d).insert
        (refillSlide d).«matches» (Int64.ofInt (d.block_start.toInt - d.w_size.toNat)) d.high_water n
        (by omega) i1.2 (by rw [bs1]; omega) (by rw [bs1]; omega) hwLe m1 (fun _ => by omega) (by omega)
      obtain ⟨g, zF, run, invG, buffersG, sizesG, acc, st, na, tot, pv⟩ := refill_finish inv buffers level0 win getW
        (refillSlide d) wa1 size1 ⟨_, _, _, _, _, rfl⟩ hashE n avail
        (by show (d.strstart - d.w_size).toNat + n.toNat ≤ wa.size; omega) (by omega) i1.2 input shapeF
      exact ⟨g, zF, _, n.toNat, run, invG, buffersG, sizesG, acc, ⟨_, _, _, _, _, rfl⟩, st, na, tot, pv⟩
    have condT : (decide (z.avail_in > (d.window_size - d.strstart.toUInt64).toUInt32) &&
        decide (d.block_start ≥ d.w_size.toUInt64.toInt64)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨more, far⟩
    simp only [condT, ite_true, bind_app, slide, readAvail _ hz1]
    by_cases c2 : (d.window_size - d.strstart.toUInt64).toUInt32 + d.w_size > z.avail_in
    · have c2N := UInt32.lt_iff_toNat_lt.mp c2
      rw [have1N] at c2N
      simp only [c2, decide_true, ite_true]
      exact finishA _ (Nat.le_refl _) (by omega) (by omega)
    · have c2N : ¬ z.avail_in.toNat < ((d.window_size - d.strstart.toUInt64).toUInt32 + d.w_size).toNat :=
        fun c => c2 (UInt32.lt_iff_toNat_lt.mpr c)
      rw [have1N] at c2N
      simp only [c2, decide_false, Bool.false_eq_true, ite_false]
      exact finishA _ (by rw [have1N]; omega) (by rw [have1N]; exact Nat.le_refl _) (by rw [have1N]; omega)
  · simp only [Bool.not_eq_true] at cond
    simp only [cond, Bool.false_eq_true, ite_false, bind_app, readAvail h hz]
    have finishB : ∀ n : UInt32, n.toNat ≤ z.avail_in.toNat → n.toNat ≤ d.window_size.toNat - d.strstart.toNat →
        ∃ g zF eF used, storedRead (some (.tab ds)) (some r) n h = .ok ((), g) ∧ DInv g r ds zF eF ∧
          StreamBuffers g r ∧ ByteSizes h g ∧ StreamAccounting z zF used 0 ∧
          (∃ ss ins m bs hw, eF = keepState d ss ins m bs hw) ∧ g.static = h.static ∧ g.nalloc = h.nalloc ∧
          Totals z zF used 0 ∧ PrivStep h g r ds d := by
      intro n avail fitN
      have same : keepState d d.strstart d.insert d.«matches» d.block_start d.high_water = d := rfl
      have shapeF := shape_refill shape level0 d.strstart d.insert d.«matches» d.block_start d.high_water n
        (by omega) insLe zero.1 bsHi hwLe shape.slides.1 (fun av => by have := shape.available av; omega) (by omega)
      have hashE : LevelHash (setD { h with bytes := upd h.bytes w (some wa) } ds
          (keepState d d.strstart d.insert d.«matches» d.block_start d.high_water))
          (keepState d d.strstart d.insert d.«matches» d.block_start d.high_water) := by
        rw [same, hSelf]; exact hash0
      obtain ⟨g, zF, run, invG, buffersG, sizesG, acc, st, na, tot, pv⟩ := refill_finish inv buffers level0 win getW
        (keepState d d.strstart d.insert d.«matches» d.block_start d.high_water) wa rfl ⟨_, _, _, _, _, rfl⟩
        hashE n avail (by show d.strstart.toNat + n.toNat ≤ wa.size; omega) (by omega) insLe input shapeF
      rw [same, hSelf] at run
      exact ⟨g, zF, _, n.toNat, run, invG, buffersG, sizesG, acc, ⟨_, _, _, _, _, rfl⟩, st, na, tot, pv⟩
    by_cases c2 : (d.window_size - d.strstart.toUInt64).toUInt32 > z.avail_in
    · have c2N := UInt32.lt_iff_toNat_lt.mp c2
      rw [have0N] at c2N
      simp only [c2, decide_true, ite_true]
      exact finishB _ (Nat.le_refl _) (by omega)
    · have c2N : ¬ z.avail_in.toNat < ((d.window_size - d.strstart.toUInt64).toUInt32).toNat :=
        fun c => c2 (UInt32.lt_iff_toNat_lt.mpr c)
      rw [have0N] at c2N
      simp only [c2, decide_false, Bool.false_eq_true, ite_false]
      exact finishB _ (by rw [have0N]; omega) (by rw [have0N]; exact Nat.le_refl _)


/-! ## The final stored block -/

set_option maxHeartbeats 4000000 in
open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff) in
/-- **The final stored block of `deflate_stored`.** `len` bytes of the window from `block_start`
go into `pending_buf` behind a stored header, `block_start` moves past them, and the pending bytes
are flushed. -/
theorem stored_block_flush {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (out : z.next_out ≠ .null)
    (pending : d.pending = 0) (cursor : d.pending_out = d.pending_buf) (bits : d.bi_valid.toInt ≤ 7)
    (low : 0 ≤ d.block_start.toInt) (len : UInt32)
    (span : d.block_start.toInt + len.toNat ≤ d.strstart.toNat) (range : d.strstart.toNat ≤ d.window_size.toNat)
    (room : (d.bi_valid.toInt.toNat + 42) / 8 + len.toNat ≤ d.pending_buf_size.toNat) (lastv : Bool) :
    ∃ (p : BPtr) (H1 : Heap) (bs : Int64) (H2 after : Heap) (z' : ZStream) (e : DeflateState) (produced : Nat),
      Ptr.add d.window d.block_start.toInt h = .ok (p, h) ∧
      Zlib.Trees._tr_stored_block (some (.tab ds)) p len.toUInt64 (if lastv then 1 else 0) h = .ok ((), H1) ∧
      ladd d.block_start len.toUInt64.toInt64 H1 = .ok (bs, H1) ∧
      wr (some (.tab ds)) (fun d => { d with block_start := bs }) H1 = .ok ((), H2) ∧
      flush_pending (some r) H2 = .ok ((), after) ∧
      DGood after r ds z' e ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      StoredFields d e ∧ e.block_start.toInt = d.block_start.toInt + len.toNat ∧ e.bi_valid.toInt = 0 ∧
      (e.pending = 0 → e.pending_out = e.pending_buf) ∧ after.static = h.static ∧ after.nalloc = h.nalloc ∧
      (∀ w, d.window = .ref (.blk w) 0 → after.bytes w = h.bytes w) ∧
      (∀ p, d.prev = .ref (.blk p) 0 → after.words p = h.words p) ∧
      (∀ q, d.head = .ref (.blk q) 0 → after.words q = h.words q) ∧ Totals z z' 0 produced ∧
      Fr h r ds d z after z' e := by
  obtain ⟨w, p, q, pb, blocks⟩ := good.inv.blocks
  obtain ⟨buf, getB, sizeB⟩ := blocks.ba
  obtain ⟨wa, getW, sizeW⟩ := blocks.wa
  have trees : TreesInvAt h ds d pb buf := Zlib.Deflate.Universal.trees_at_of_good good blocks.pbuf getB
  have bufSize : buf.size = d.pending_buf_size.toNat := trees.base.psize.symm
  have wsz := good.inv.wsz
  have lenLt := len.toNat_lt
  have bsN : (d.block_start.toInt.toNat : Int) = d.block_start.toInt := Int.toNat_of_nonneg low
  have add : Ptr.add d.window d.block_start.toInt h = .ok (.ref (.blk w) d.block_start.toInt.toNat, h) := by
    rw [blocks.win]
    have := Ptr.add_ok (off := 0) (k := d.block_start.toInt) (show Space.get h (BRef.blk w) = some wa from getW)
      (by omega) (by omega)
    have e0 : ((0 : Nat) : Int) + d.block_start.toInt = d.block_start.toInt := by omega
    rw [e0] at this
    exact this
  have lenN : len.toUInt64.toNat = len.toNat := by simp
  obtain ⟨next, r1, run1, trees1, size1, aligned1, pend1, diff1⟩ :=
    Zlib.Trees.Proofs.Out.stored_block_exact (off := d.block_start.toInt.toNat) trees getW (Ne.symm blocks.wb)
      bits len.toUInt64
      (by rw [lenN]; omega) (by rw [pending, UInt64.toNat_zero]; have := trees.base.lit_lo; omega)
      (by rw [pending, lenN, UInt64.toNat_zero]; omega) lastv
  replace run1 : Zlib.Trees._tr_stored_block (some (.tab ds)) (.ref (.blk w) d.block_start.toInt.toNat) len.toUInt64
      (if lastv then 1 else 0) h = .ok ((), setD (Zlib.Trees.Proofs.Out.setB h pb next) ds r1) := run1
  replace trees1 : TreesInvAt (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds r1) ds r1 pb next := trees1
  have good1 := output_bits_good good cursor getB size1 diff1 trees1
  have buffers1 := output_bits_buffers good buffers cursor getB size1 diff1 trees1
  have sizes1 := output_bits_sizes good getB size1 diff1
  obtain ⟨pp, aa, vv, uu, hr1⟩ := diff1
  have bs1 : r1.block_start = d.block_start := by rw [hr1]
  have lenI : len.toUInt64.toInt64.toInt = (len.toNat : Int) := Zlib.Deflate.Universal.u32_toInt64_toInt len
  have ssLt := d.strstart.toNat_lt
  have lad := ladd_value d.block_start len.toUInt64.toInt64 (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds r1)
    (by rw [lenI]; omega) (by rw [lenI]; omega)
  rw [lenI] at lad
  let r2 := { r1 with block_start := Int64.ofInt (d.block_start.toInt + len.toNat) }
  have state1 : (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds r1).dstates ds = some r1 := setD_dstates_same _ _ _
  have wrt : wr (some (.tab ds)) (fun x => { x with block_start := Int64.ofInt (d.block_start.toInt + len.toNat) })
      (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds r1) = .ok ((), setD (Zlib.Trees.Proofs.Out.setB h pb next) ds r2) := by
    rw [wrD_eq, state1]; dsimp only; rw [setD_setD]
  let H2 := setD (Zlib.Trees.Proofs.Out.setB h pb next) ds r2
  have inv2 : DStInv (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds r1) ds r2 :=
    { good1.inv with blocks := good1.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  have good2 : DGood H2 r ds z r2 := by
    have g := good1.setD' (d' := r2) rfl good1.live.status inv2 (by trkeep)
    rw [setD_setD] at g; exact g
  have buffers2 : StreamBuffers H2 r := by
    have b := Zlib.Deflate.Universal.state_write_buffers good1 buffers1 (d' := r2) ⟨rfl, rfl, rfl, rfl⟩
      (by have g := good1.setD' (d' := r2) rfl good1.live.status inv2 (by trkeep); exact g)
    rw [setD_setD] at b; exact b
  have trees2 : TreesInvAt H2 ds r2 pb next :=
    ⟨⟨setD_dstates_same _ _ _, trees1.base.wf, trees1.base.static, trees1.base.pbuf, trees1.base.bytes,
      trees1.base.rw, trees1.base.size, trees1.base.psize, trees1.base.sym, trees1.base.lit_lo, trees1.base.lit_hi,
      trees1.base.sym_end, trees1.base.pending_le⟩,
      ⟨trees1.run.ldyn, trees1.run.lstat, trees1.run.ddyn, trees1.run.dstat, trees1.run.bldyn, trees1.run.blstat,
        trees1.run.bi_lo, trees1.run.bi_hi, trees1.run.bi_buf, trees1.run.sym_next_le, trees1.run.sym_next_mod⟩⟩
  have cursor2 : r2.pending_out = r2.pending_buf := by
    show r1.pending_out = r1.pending_buf; rw [hr1]; exact cursor
  have room2 : 8 * r2.pending.toNat + r2.bi_valid.toInt.toNat ≤ 8 * next.size := by
    show 8 * r1.pending.toNat + r1.bi_valid.toInt.toNat ≤ 8 * next.size
    rw [pend1, aligned1, size1, pending, lenN, UInt64.toNat_zero]; simp only [Int.toNat_zero]; omega
  have depth1 : r1.depth = d.depth := by rw [hr1]
  have sizes2 : ByteSizes h H2 := sizes1.chain ⟨fun ref a get => ⟨a, by
      show Space.get (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds r2) ref = some a
      rw [byte_view_setD_depth (h := Zlib.Trees.Proofs.Out.setB h pb next) (d := d) (result := r2) good.live.hs depth1]
      rw [byte_view_setD_depth (h := Zlib.Trees.Proofs.Out.setB h pb next) (d := d) (result := r1) good.live.hs depth1] at get
      exact get, rfl⟩, fun ref => by cases ref <;> rfl⟩
  have fieldsW : r2.window = d.window ∧ r2.prev = d.prev ∧ r2.head = d.head ∧ r2.pending_buf = d.pending_buf := by
    show r1.window = d.window ∧ r1.prev = d.prev ∧ r1.head = d.head ∧ r1.pending_buf = d.pending_buf
    rw [hr1]; exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨pa, getP, _⟩ := blocks.pa
  obtain ⟨qa, getQ, _⟩ := blocks.qa
  have getW2 : H2.bytes w = some wa := by
    show (upd h.bytes pb (some next)) w = some wa
    rw [upd_ne _ _ _ _ blocks.wb]; exact getW
  have bsR : (Int64.ofInt (d.block_start.toInt + len.toNat)).toInt = d.block_start.toInt + len.toNat :=
    int64_ofInt_toInt _ (by omega) (by omega)
  have finish : ∀ (produced : Nat) (after : Heap) (z' : ZStream) (result : DeflateState),
      flush_pending (some r) H2 = .ok ((), after) → DGood after r ds z' result → StreamBuffers after r →
      StreamAccounting z z' 0 produced → Totals z z' 0 produced →
      BufferFrame H2 after (fun b => StreamRoot r b ∨ DeflateOwned ds r2 b) [⟨z.next_out, produced⟩] →
      Zlib.Deflate.Proofs.Shape H2 after → ByteSizes H2 after →
      result.bi_valid.toInt.toNat = r2.bi_valid.toInt.toNat % 8 →
      result = { r2 with pending := result.pending, pending_out := result.pending_out, bi_buf := result.bi_buf, bi_valid := result.bi_valid, bi_used := result.bi_used } →
      (result.pending = 0 → result.pending_out = result.pending_buf) →
      after.static = H2.static → after.nalloc = H2.nalloc →
      (after.bytes w = some wa ∧ after.words p = some pa ∧ after.words q = some qa) →
      ∃ (p : BPtr) (H1 : Heap) (bs : Int64) (H2 after : Heap) (z' : ZStream) (e : DeflateState) (produced : Nat),
        Ptr.add d.window d.block_start.toInt h = .ok (p, h) ∧
        Zlib.Trees._tr_stored_block (some (.tab ds)) p len.toUInt64 (if lastv then 1 else 0) h = .ok ((), H1) ∧
        ladd d.block_start len.toUInt64.toInt64 H1 = .ok (bs, H1) ∧
        wr (some (.tab ds)) (fun d => { d with block_start := bs }) H1 = .ok ((), H2) ∧
        flush_pending (some r) H2 = .ok ((), after) ∧
        DGood after r ds z' e ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
        StoredFields d e ∧ e.block_start.toInt = d.block_start.toInt + len.toNat ∧ e.bi_valid.toInt = 0 ∧
        (e.pending = 0 → e.pending_out = e.pending_buf) ∧ after.static = h.static ∧ after.nalloc = h.nalloc ∧
        (∀ w, d.window = .ref (.blk w) 0 → after.bytes w = h.bytes w) ∧
        (∀ p, d.prev = .ref (.blk p) 0 → after.words p = h.words p) ∧
        (∀ q, d.head = .ref (.blk q) 0 → after.words q = h.words q) ∧ Totals z z' 0 produced ∧
        Fr h r ds d z after z' e := by
    intro produced after z' result run goodA buffersA account totals bufferF shapeF _ valid fields cursorA staticA nallocA kept
    have bv : result.bi_valid.toInt = 0 := by
      have v1 : r2.bi_valid.toInt = 0 := aligned1
      rw [v1] at valid
      have := goodA.inv.bits.1
      have v2 : result.bi_valid.toInt.toNat = 0 := by rw [valid]; rfl
      omega
    have fieldsS : StoredFields d result := by
      unfold StoredFields
      rw [fields]
      dsimp only [r2]
      rw [hr1]
    refine ⟨_, _, _, _, after, z', result, produced, add, run1, lad, wrt, run, goodA, buffersA, account, fieldsS,
      ?_, bv, cursorA, by rw [staticA]; rfl, by rw [nallocA]; rfl, fun w' e => ?_, fun p' e => ?_, fun q' e => ?_, totals, ?_⟩
    · rw [fields]; exact bsR
    · have : w' = w := by simpa only [blocks.win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using e.symm
      subst this; rw [kept.1, getW]
    · have : p' = p := by simpa only [blocks.prev, Ptr.ref.injEq, WRef.blk.injEq, and_true] using e.symm
      subst this; rw [kept.2.1, getP]
    · have : q' = q := by simpa only [blocks.head, Ptr.ref.injEq, WRef.blk.injEq, and_true] using e.symm
      subst this; rw [kept.2.2, getQ]
    · have privH2 : PrivStep h H2 r ds d :=
        (priv_setB h r ds pb d next (Or.inr (Or.inr (Or.inr (Or.inr blocks.pbuf)))) (by simp [getB])).trans
          (priv_setD _ r ds d r2 (by simpa [Zlib.Trees.Proofs.Out.setB] using good.live.hs))
      have keysE : Keys r2 result := by rw [fields]; exact ⟨rfl, rfl, rfl, rfl⟩
      exact Fr.trans good buffers (Fr.priv good buffers privH2 fieldsW)
        (Fr.flush account (by rw [totals.1]; simp) totals.2 bufferF shapeF keysE)
  obtain ⟨ob, pointer⟩ := Zlib.Deflate.Universal.output_reference good.live.hz buffers out
  have zEq : good2.live.hz = good2.live.hz := rfl
  rcases pointer with ⟨oo, pointer⟩ | ⟨oo, pointer⟩
  · obtain ⟨produced, after, z', result, _written, _remaining, run, goodA, buffersA, accountA,
      sizesA, storageA, _count, _left, _low, validA, fieldsA, _bytes, _pendingA, _outputA⟩ :=
      flush_pending_raw_bits good2 trees2 buffers2 pointer cursor2 room2
    have cursorA := raw_pending_run_empty_cursor good2 trees2 buffers2 pointer cursor2 room2 run goodA.live.hs
    have kept := storageA.private_arrays good2 buffers2 pointer (by rw [fieldsW.1]; exact blocks.win) getW2
      (by rw [fieldsW.2.1]; exact blocks.prev) getP (by rw [fieldsW.2.2.1]; exact blocks.head) getQ
      (by rw [fieldsW.2.2.2]; exact blocks.pbuf)
    have tot := flush_pending_run_counter_effects good2 trees2 buffers2 pointer cursor2 room2 run goodA.live.hz accountA
    have bufferA := flush_pending_run_buffer_frame good2 trees2 buffers2 pointer cursor2 room2 run goodA.live.hz accountA
    exact finish produced after z' result run goodA buffersA accountA ⟨by rw [tot.1]; simp, tot.2⟩ bufferA
      storageA.shape sizesA validA
      fieldsA cursorA storageA.frame.1.symm storageA.nalloc kept
  · obtain ⟨produced, after, z', result, _written, _remaining, run, goodA, buffersA, accountA,
      sizesA, storageA, _count, _left, _low, validA, fieldsA, _bytes, _pendingA, _outputA, bufferF0⟩ :=
      flush_pending_foreign_bits_frame good2 trees2 buffers2 pointer cursor2 room2
    have cursorA := foreign_pending_run_empty_cursor good2 trees2 buffers2 pointer cursor2 room2 run goodA.live.hs
    have kept := storageA.foreign_private_arrays good2 buffers2 pointer (by rw [fieldsW.1]; exact blocks.win) getW2
      (by rw [fieldsW.2.1]; exact blocks.prev) getP (by rw [fieldsW.2.2.1]; exact blocks.head) getQ
      (by rw [fieldsW.2.2.2]; exact blocks.pbuf)
    have tot := default_foreign_flush_pending_run_counter_effects good2 trees2 buffers2 pointer cursor2 room2 run
      goodA.live.hz accountA
    have bufferA := buffer_frame_weaken bufferF0 (large := fun b => StreamRoot r b ∨ DeflateOwned ds r2 b)
      (fun b c => by
        rcases c with root | same | pbe
        · exact Or.inl root
        · exact Or.inr (Or.inl same)
        · subst pbe; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (fieldsW.2.2.2.trans blocks.pbuf))))))
    exact finish produced after z' result run goodA buffersA accountA ⟨by rw [tot.1]; simp, tot.2⟩ bufferA
      storageA.shape sizesA validA
      fieldsA cursorA storageA.frame.1.symm storageA.nalloc kept


/-- `s->bi_used = 8` keeps the invariant. -/
theorem bi_used_step {g : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {e : DeflateState}
    (inv : DInv g r ds z e) (buffers : StreamBuffers g r) (level0 : e.level = 0) :
    wr (some (.tab ds)) (fun d => { d with bi_used := 8 }) g = .ok ((), setD g ds { e with bi_used := 8 }) ∧
      DInv (setD g ds { e with bi_used := 8 }) r ds z { e with bi_used := 8 } ∧
      StreamBuffers (setD g ds { e with bi_used := 8 }) r := by
  have good := inv.good
  have inv2 : DStInv g ds { e with bi_used := 8 } :=
    { good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  have good2 := good.setD' (d' := { e with bi_used := 8 }) rfl good.live.status inv2 (by trkeep)
  refine ⟨by rw [wrD_eq, good.live.hs], ?_, Zlib.Deflate.Universal.state_write_buffers good buffers
    ⟨rfl, rfl, rfl, rfl⟩ good2⟩
  have sh := inv.shape
  have sh2 : Shape { e with bi_used := 8 } := ⟨sh.room, sh.insert, sh.insertDone, sh.prevLength, sh.matchLength,
    sh.matchAvailable, sh.blockStart, sh.blockSpan, sh.levelZero, sh.available, sh.pendingMatch, sh.fastLazy,
    sh.highWater, sh.windowInit, sh.lastFlush, sh.headerFlush, sh.trailer, sh.biValid, sh.cursor, sh.symRoom, sh.slides⟩
  exact dinv_stored_keep inv good2 rfl sh2 (inv.shape.levelZero level0).2.2 rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl

set_option maxHeartbeats 8000000 in
/-- **The final block of `deflate_stored` keeps the invariant.** -/
theorem stored_final {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (buffers : StreamBuffers h r) (pend0 : d.pending = 0) (out : z.next_out ≠ .null)
    (level0 : d.level = 0) (flush last0 : Int32) (lastZero : last0 = 0) :
    ∃ ret g z' d' produced, storedFinal (some (.tab ds)) flush (some r) last0 h = .ok (ret, g) ∧
      DInv g r ds z' d' ∧ StreamBuffers g r ∧ StreamAccounting z z' 0 produced ∧
      (ret = finish_started → flush = Z_FINISH) ∧ ret ≠ finish_done ∧ ret ≠ block_done ∧
      Totals z z' 0 produced ∧ Fr h r ds d z g z' d' := by
  have good := inv.good
  have shape := inv.shape
  have zero := shape.levelZero level0
  have bits := inv.bi_valid_le
  have hvN := header_bytes_value d.bi_valid bits.1 bits.2
  have room := shape.room
  have wsz := good.inv.wsz
  have wsize := good.inv.wsize
  have wbits := good.inv.wbits_hi
  have wpow : 2 ^ d.w_bits.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) wbits
  have la : d.lookahead.toNat = 0 := by rw [zero.2.1]; rfl
  obtain ⟨lsubEq, word, _⟩ := Zlib.Deflate.Universal.Block.flush_length_general (d := d) (by omega)
    shape.blockStart (by omega)
  have lsubRun := congrFun lsubEq h
  have pbs := good.inv.blocks
  obtain ⟨w0, p0, q0, b0, blocks⟩ := pbs
  have psize := blocks.psize
  have lit := good.inv.lit
  have hsize := good.inv.hsize
  have hbits := good.inv.hbits_lo
  have hpow : 2 ^ 8 ≤ 2 ^ d.hash_bits.toNat := Nat.pow_le_pow_right (by omega) hbits
  have PLe : (d.bi_valid.toInt.toNat + 42) / 8 ≤ 6 := by omega
  have hvU : (((d.bi_valid.toUInt32 + 42) >>> 3).toUInt64).toNat = (d.bi_valid.toInt.toNat + 42) / 8 := by
    rw [UInt32.toNat_toUInt64, hvN]
  have pbsLe : (((d.bi_valid.toUInt32 + 42) >>> 3).toUInt64) ≤ d.pending_buf_size := by
    rw [UInt64.le_iff_toNat_le, hvU]; omega
  have HvN : ((MIN (d.pending_buf_size - ((d.bi_valid.toUInt32 + 42) >>> 3).toUInt64) MAX_STORED.toUInt64).toUInt32).toNat ≤
      d.pending_buf_size.toNat - (d.bi_valid.toInt.toNat + 42) / 8 := by
    have sub : (d.pending_buf_size - ((d.bi_valid.toUInt32 + 42) >>> 3).toUInt64).toNat =
        d.pending_buf_size.toNat - (d.bi_valid.toInt.toNat + 42) / 8 := by
      rw [UInt64.toNat_sub_of_le _ _ pbsLe, hvU]
    have m : MAX_STORED.toUInt64.toNat = 65535 := rfl
    unfold MIN
    split
    · rename_i lt
      have lt' := UInt64.lt_iff_toNat_lt.mp lt
      rw [sub, m] at lt'
      rw [UInt64.toNat_toUInt32, m]
      omega
    · rw [UInt64.toNat_toUInt32, sub]
      exact Nat.mod_le _ _
  have hz := good.live.hz
  have readAvail : zrd (some r) (·.avail_in) h = .ok (z.avail_in, h) := by simp [zrd_eq, hz]
  unfold storedFinal
  simp only [bind_app, ldDeflateState_tab good.live.hs, lsubRun, pure_app, readAvail]
  obtain ⟨left, hleft⟩ : ∃ l, l = (Int64.ofInt ((d.strstart.toNat : Int) - d.block_start.toInt)).toUInt64.toUInt32 :=
    ⟨_, rfl⟩
  rw [← hleft]
  have leftN : left.toNat = ((d.strstart.toNat : Int) - d.block_start.toInt).toNat := by
    rw [hleft, UInt64.toNat_toUInt32, word]
    apply Nat.mod_eq_of_lt
    have := shape.blockStart; have := zero.1; omega
  obtain ⟨Hv, hHv⟩ : ∃ x, x = (MIN (d.pending_buf_size - ((d.bi_valid.toUInt32 + 42) >>> 3).toUInt64)
      MAX_STORED.toUInt64).toUInt32 := ⟨_, rfl⟩
  rw [← hHv]
  rw [← hHv] at HvN
  have lenLe := min_toNat_le left Hv
  have lenLe2 : (MIN left Hv).toNat ≤ Hv.toNat := by
    unfold MIN; split
    · exact Nat.le_refl _
    · rename_i nlt
      have : ¬ Hv.toNat < left.toNat := fun c => nlt (UInt32.lt_iff_toNat_lt.mpr c)
      omega
  have noBlock : ∀ (last : Int32), ∃ ret g z' d' produced,
      (do
        if last != 0 then wr (some (.tab ds)) (fun d => { d with bi_used := 8 })
        pure (if last != 0 then finish_started else need_more) : M block_state) h = .ok (ret, g) ∧
      DInv g r ds z' d' ∧ StreamBuffers g r ∧ StreamAccounting z z' 0 produced ∧ (last = 0 → ret = need_more) ∧
      Totals z z' 0 produced ∧ Fr h r ds d z g z' d' := by
    intro last
    by_cases l0 : (last != 0) = true
    · obtain ⟨wrRun, invB, buffersB⟩ := bi_used_step inv buffers level0
      exact ⟨_, _, z, _, 0, by simp only [l0, ite_true, bind_app, wrRun]; rfl, invB, buffersB,
        Zlib.Deflate.Engine.Proofs.stream_accounting_self z, fun e => by subst e; simp at l0, Totals.refl z,
        Fr.priv good buffers (priv_setD h r ds d _ good.live.hs) ⟨rfl, rfl, rfl, rfl⟩⟩
    · simp only [Bool.not_eq_true] at l0
      exact ⟨need_more, h, z, d, 0, by simp only [l0, Bool.false_eq_true, ite_false, bind_app, pure_app], inv,
        buffers, Zlib.Deflate.Engine.Proofs.stream_accounting_self z, fun _ => rfl, Totals.refl z, Fr.refl good buffers⟩
  by_cases c : (decide (left ≥ MIN Hv d.w_size) || ((left != 0 || flush == Z_FINISH) && flush != Z_NO_FLUSH &&
      z.avail_in == 0 && decide (left ≤ Hv))) = true
  · have lastv := flush == Z_FINISH && z.avail_in == 0 && MIN left Hv == left
    obtain ⟨p, H1, bs, H2, after, z', e, produced, add, blk, lad, wrt, fl, goodA, buffersA, accA, fieldsA, bsA,
        bvA, cursorA, staticA, nallocA, winA, prevA, headA, totA, frA⟩ :=
      stored_block_flush good buffers out pend0 (shape.cursor pend0) bits.2 zero.1 (MIN left Hv)
        (by have := shape.blockStart; omega) (by omega) (by omega)
        (flush == Z_FINISH && z.avail_in == 0 && MIN left Hv == left)
    have shapeA : Shape e := shape_stored shape fieldsA level0 (by rw [bsA]; omega)
      (by rw [bsA]; have := shape.blockStart; omega) (by omega) cursorA
    have invA : DInv after r ds z' e := dinv_stored_keep inv goodA fieldsA shapeA zero.2.2 staticA winA prevA headA
      accA.2.2.2.2.2.2.2.1 accA.2.2.2.2.2.2.2.2.1
    have levelA : e.level = 0 := by rw [fieldsA]; exact level0
    simp only [c, ite_true, bind_app, add, blk, lad, wrt, fl]
    by_cases l0 : ((if (flush == Z_FINISH && z.avail_in == 0 && MIN left Hv == left) = true then (1 : Int32) else 0) != 0) = true
    · obtain ⟨wrRun, invB, buffersB⟩ := bi_used_step invA buffersA levelA
      have fin : flush = Z_FINISH := by
        by_cases cf : (flush == Z_FINISH && z.avail_in == 0 && MIN left Hv == left) = true
        · simp only [Bool.and_eq_true, beq_iff_eq] at cf; exact cf.1.1
        · rw [if_neg cf] at l0; simp at l0
      exact ⟨finish_started, _, z', _, produced, by simp only [l0, ite_true, bind_app, wrRun]; rfl, invB, buffersB, accA,
        fun _ => fin, by decide, by decide, totA,
        Fr.trans good buffers frA (Fr.priv invA.good buffersA (priv_setD after r ds e _ invA.good.live.hs) ⟨rfl, rfl, rfl, rfl⟩)⟩
    · simp only [Bool.not_eq_true] at l0
      exact ⟨need_more, after, z', e, produced, by simp only [l0, Bool.false_eq_true, ite_false, bind_app, pure_app],
        invA, buffersA, accA, fun e => absurd e (by decide), by decide, by decide, totA, frA⟩
  · simp only [Bool.not_eq_true] at c
    simp only [c, Bool.false_eq_true, ite_false]
    obtain ⟨ret, g, z', d', produced, run, invB, buffersB, accB, retEq, totB, frB⟩ := noBlock last0
    have rn := retEq lastZero
    subst rn
    exact ⟨need_more, g, z', d', produced, run, invB, buffersB, accB, fun e => absurd e (by decide), by decide,
      by decide, totB, frB⟩


/-- `if (s->high_water < s->strstart) s->high_water = s->strstart;` keeps the invariant. -/
theorem high_water_step {g : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {e : DeflateState}
    (inv : DInv g r ds z e) (buffers : StreamBuffers g r) (level0 : e.level = 0) :
    let e' := { e with high_water := if e.high_water < e.strstart.toUInt64 then e.strstart.toUInt64 else e.high_water }
    wr (some (.tab ds)) (fun d => { d with high_water := if d.high_water < d.strstart.toUInt64 then d.strstart.toUInt64 else d.high_water }) g =
        .ok ((), setD g ds e') ∧
      DInv (setD g ds e') r ds z e' ∧ StreamBuffers (setD g ds e') r ∧ ByteSizes g (setD g ds e') ∧
      (∃ ss ins m bs hw, e' = keepState e ss ins m bs hw) := by
  intro e'
  have good := inv.good
  have shape := inv.shape
  have zero := shape.levelZero level0
  obtain ⟨w, wa, win, getW, sizeW⟩ := window_block good
  have same : setD { g with bytes := upd g.bytes w (some wa) } ds e' = setD g ds e' := by
    rw [upd_self _ _ _ getW]
  have hwN : (if e.high_water < e.strstart.toUInt64 then e.strstart.toUInt64 else e.high_water).toNat ≤
      e.window_size.toNat := by
    have := shape.room; have := shape.highWater
    split
    · simp; omega
    · omega
  have ke : e' = keepState e e.strstart e.insert e.«matches» e.block_start
      (if e.high_water < e.strstart.toUInt64 then e.strstart.toUInt64 else e.high_water) := rfl
  have shape' : Shape e' := by
    rw [ke]
    have initN : e.strstart.toNat ≤ (if e.high_water < e.strstart.toUInt64 then e.strstart.toUInt64 else e.high_water).toNat := by
      split
      · simp
      · rename_i nlt
        have : ¬ e.high_water.toNat < e.strstart.toNat := by
          intro c; apply nlt; rw [UInt64.lt_iff_toNat_lt]; simpa using c
        omega
    exact shape_keep shape level0 _ _ _ _ _ (by have := shape.room; omega) shape.insert zero.1 shape.blockStart
      shape.available hwN shape.slides.1 initN
  have hash' : LevelHash (setD { g with bytes := upd g.bytes w (some wa) } ds e') e' := by
    rw [same]
    exact level_hash_write (h := g) ⟨inv.hashing.chains, inv.hashing.slid⟩ zero.2.1 zero.2.1
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl (Nat.le_refl _) (Nat.le_refl _) (fun _ _ => rfl)
      (fun w' wa' _ g' => ⟨wa', g', fun _ _ => rfl⟩)
  obtain ⟨invG, buffersG, sizesG⟩ := window_state_step inv buffers level0 win getW wa rfl e'
    ⟨_, _, _, _, _, ke⟩ shape' hash'
  rw [same] at invG buffersG sizesG
  exact ⟨by rw [wrD_eq, good.live.hs], invG, buffersG, sizesG, ⟨_, _, _, _, _, ke⟩⟩


/-! ## The end of `deflate_stored` -/

/-- What the return value of `deflate_stored` says (`deflate_call` reads it): `finish_*` only for
`Z_FINISH`, and `finish_done` after the last block with the input used up and nothing pending. -/
structure StoredMeaning (flush : Int32) (bstate : block_state) (z' : ZStream) (d' : DeflateState) : Prop where
  finish : bstate = finish_started ∨ bstate = finish_done → flush = Z_FINISH
  done : bstate = finish_done → z'.avail_in = 0 ∧ d'.pending = 0 ∧ d'.bi_valid.toInt = 0

set_option maxHeartbeats 8000000 in
/-- **The end of `deflate_stored` keeps the invariant.** `used0` is `avail_in` at the call;
the loop consumed `consumed` bytes, so the input cursor is at least that far into its view. -/
theorem stored_end {g : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv g r ds z d) (buffers : StreamBuffers g r) (pend0 : d.pending = 0)
    (out : z.next_out ≠ .null) (input : z.avail_in ≠ 0 → z.next_in ≠ .null) (level0 : d.level = 0)
    (flush : Int32) (mb used0 : UInt32) (st : StoredS) (consumed : Nat)
    (count : used0.toNat = z.avail_in.toNat + consumed)
    (cursor : consumed ≠ 0 → ∃ ref io, z.next_in = .ref ref io ∧ consumed ≤ io)
    (lastF : st.last ≠ 0 → flush = Z_FINISH ∧ z.avail_in = 0 ∧ d.bi_valid.toInt = 0) :
    ∃ ret g' z' d' used produced, storedEnd (some (.tab ds)) flush (some r) mb used0 st g = .ok (ret, g') ∧
      DInv g' r ds z' d' ∧ StreamBuffers g' r ∧ StreamAccounting z z' used produced ∧
      StoredMeaning flush ret z' d' ∧ Totals z z' used produced ∧ Fr g r ds d z g' z' d' := by
  have good := inv.good
  have hz := good.live.hz
  have readAvail : ∀ H : Heap, r.get H = some z → zrd (some r) (·.avail_in) H = .ok (z.avail_in, H) := by
    intro H hzH; simp [zrd_eq, hzH]
  have usedN : (used0 - z.avail_in).toNat = consumed := by
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))]; omega
  -- keep the consumed input in the window
  obtain ⟨g1, g2, e2, keepRun, hwRun, inv2, buffers2, pend1, level1, bv1, fr2⟩ : ∃ g1 g2 e2,
      (if (used0 - z.avail_in != 0) = true then storedKeep (some (.tab ds)) (some r) (used0 - z.avail_in)
        else pure ()) g = .ok ((), g1) ∧
      wr (some (.tab ds)) (fun d => { d with high_water := if d.high_water < d.strstart.toUInt64 then d.strstart.toUInt64 else d.high_water }) g1 =
        .ok ((), g2) ∧
      DInv g2 r ds z e2 ∧ StreamBuffers g2 r ∧ e2.pending = 0 ∧ e2.level = 0 ∧ e2.bi_valid = d.bi_valid ∧
      Fr g r ds d z g2 z e2 := by
    by_cases u0 : (used0 - z.avail_in != 0) = true
    · have nz : consumed ≠ 0 := by
        intro c; rw [← usedN] at c; simp at u0; exact u0 (UInt32.toNat_inj.mp (by rw [c]; rfl))
      obtain ⟨ref, io, src, le⟩ := cursor nz
      obtain ⟨ia, inGet, inBound⟩ := caller_input_array good buffers src
      have apartW : ∀ w, d.window = .ref (.blk w) 0 → ref ≠ .blk w :=
        fun w win => Ne.symm (caller_input_window_separate good buffers win src)
      obtain ⟨gm, g2, e2, run, wrun, inv2, buffers2, _, ⟨ss, ins, m, bs, hw, rfl⟩, _, _, privK⟩ :=
        stored_keep inv buffers level0 (used0 - z.avail_in) src inGet (by omega) (by rw [usedN]; exact le)
          apartW (input_not_state good buffers src)
      exact ⟨gm, g2, _, by simp only [u0, ite_true, run], wrun, inv2, buffers2, pend0, level0, rfl,
        Fr.priv good buffers privK ⟨rfl, rfl, rfl, rfl⟩⟩
    · obtain ⟨hwRun, inv2, buffers2, _, _⟩ := high_water_step inv buffers level0
      exact ⟨g, _, _, by simp only [u0, Bool.false_eq_true, ite_false]; rfl, hwRun, inv2, buffers2, pend0, level0, rfl,
        Fr.priv good buffers (priv_setD g r ds d _ good.live.hs) ⟨rfl, rfl, rfl, rfl⟩⟩
  have hz2 := inv2.good.live.hz
  unfold storedEnd
  simp only [ite_seq]
  simp only [bind_app, readAvail g hz, keepRun, hwRun]
  by_cases lastC : (st.last != 0) = true
  · obtain ⟨wrRun, inv3, buffers3⟩ := bi_used_step inv2 buffers2 level1
    have facts := lastF (by simpa using lastC)
    exact ⟨finish_done, _, z, _, 0, 0, by simp only [lastC, ite_true, bind_app, wrRun]; rfl, inv3, buffers3,
      Zlib.Deflate.Engine.Proofs.stream_accounting_self z,
      ⟨fun _ => facts.1, fun _ => ⟨facts.2.1, pend1, by show e2.bi_valid.toInt = 0; rw [bv1]; exact facts.2.2⟩⟩,
      Totals.refl z,
      Fr.trans good buffers fr2 (Fr.priv inv2.good buffers2 (priv_setD g2 r ds e2 _ inv2.good.live.hs) ⟨rfl, rfl, rfl, rfl⟩)⟩
  · simp only [Bool.not_eq_true] at lastC
    simp only [lastC, Bool.false_eq_true, ite_false, bind_app, ldDeflateState_tab inv2.good.live.hs, readAvail _ hz2]
    by_cases early : (flush != Z_NO_FLUSH && flush != Z_FINISH && z.avail_in == 0 &&
        (e2.strstart.toUInt64.toInt64 == e2.block_start)) = true
    · exact ⟨block_done, _, z, _, 0, 0, by simp only [early, ite_true]; rfl, inv2, buffers2,
        Zlib.Deflate.Engine.Proofs.stream_accounting_self z,
        ⟨fun e => by rcases e with e | e <;> exact absurd e (by decide), fun e => absurd e (by decide)⟩, Totals.refl z, fr2⟩
    · simp only [Bool.not_eq_true] at early
      simp only [early, Bool.false_eq_true, ite_false]
      obtain ⟨g3, z3, e3, u3, refillRun, inv3, buffers3, _, acc3, ⟨_, _, _, _, _, ke3⟩, _, _, tot3, priv3⟩ :=
        stored_refill inv2 buffers2 level1 input
      have pend3 : e3.pending = 0 := by rw [ke3]; exact pend1
      have level3 : e3.level = 0 := by rw [ke3]; exact level1
      obtain ⟨ret, g4, z4, e4, p4, finalRun, inv4, buffers4, acc4, startedF, notDone, _, tot4, fr4⟩ :=
        stored_final inv3 buffers3 pend3 (output_valid_after acc3 out) level3 flush st.last (by simpa using lastC)
      exact ⟨ret, g4, z4, e4, _, _, by simp only [bind_app, refillRun, finalRun], inv4, buffers4,
        Zlib.Deflate.Engine.Proofs.stream_accounting_trans acc3 acc4,
        ⟨fun e => by rcases e with e | e; exact startedF e; exact absurd e notDone, fun e => absurd e notDone⟩,
        Totals.trans tot3 tot4,
        Fr.trans good buffers fr2 (Fr.trans inv2.good buffers2
          (Fr.read inv2.good buffers2 priv3 acc3 tot3 (by rw [ke3]; exact ⟨rfl, rfl, rfl, rfl⟩)) fr4)⟩


set_option maxHeartbeats 4000000 in
/-- **`deflate_stored` keeps the invariant**, with the stream accounting of the call. -/
theorem stored_spec_of {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (entry : StrategyEntry h r z d) (flush : Int32) (level : d.level = 0) :
    ∃ bstate after z' d', C.run (Zlib.Deflate.deflate_stored (some (.tab ds)) flush) h = .ok (bstate, after) ∧
      DInv after r ds z' d' ∧ StreamBuffers after r ∧ Fr h r ds d z after z' d' ∧
      StoredMeaning flush bstate z' d' := by
  have good := inv.good
  have hz := good.live.hz
  have strm := good.live.back
  obtain ⟨st, g, z1, d1, loopRun, step, lastF⟩ := stored_loop inv entry.buffers entry.pending entry.out entry.input
    level flush (MIN (d.pending_buf_size - 5) d.w_size.toUInt64).toUInt32
    { last := 0, len := 0, left := 0, have_ := 0, all := false, brk := false } rfl
  obtain ⟨u1, p1, acc1, tot1⟩ := step.account
  have fr1 := step.fr
  have level1 : d1.level = 0 := by rw [step.fields]; exact level
  have count : z.avail_in.toNat = z1.avail_in.toNat + u1 := by have := acc1.2.2.1; omega
  have cursor : u1 ≠ 0 → ∃ ref io, z1.next_in = .ref ref io ∧ u1 ≤ io := by
    intro nz
    have nzIn : z.avail_in ≠ 0 := by
      intro e; have := acc1.1; rw [e] at this; simp at this; omega
    obtain ⟨ref, io0, src0⟩ : ∃ ref io, z.next_in = .ref ref io := by
      cases p : z.next_in with
      | null => exact absurd p (entry.input nzIn)
      | ref ref io => exact ⟨ref, io, rfl⟩
    refine ⟨ref, io0 + u1, ?_, by omega⟩
    rw [acc1.2.2.2.2.1, src0]; rfl
  obtain ⟨ret, g', z', d', u2, p2, endRun, inv', buffers', acc2, meaning, tot2, fr2⟩ :=
    stored_end step.inv step.buffers step.pending step.out step.input level1 flush
      (MIN (d.pending_buf_size - 5) d.w_size.toUInt64).toUInt32 z.avail_in st u1 count cursor lastF
  refine ⟨ret, g', z', d', ?_, inv', buffers', Fr.trans inv.good entry.buffers fr1 fr2, meaning⟩
  have readAvail : zrd (some r) (·.avail_in) h = .ok (z.avail_in, h) := by simp [zrd_eq, hz]
  simp only [C.run, deflate_stored_source, bind_app, ldDeflateState_tab good.live.hs, strm, readAvail, loopRun,
    endRun]

end Zlib.Deflate.Engine.Proofs

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec
set_option autoImplicit false

/-- **`deflate_stored` keeps the invariant** (level 0, the checks of `deflate` done), with the
stream accounting of the call. No premise beyond `DInv` and `StrategyEntry`. -/
theorem stored_spec {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (entry : StrategyEntry h r z d) (flush : Int32) (level : d.level = 0) :
    ∃ bstate after z' d', C.run (Zlib.Deflate.deflate_stored (some (.tab ds)) flush) h = .ok (bstate, after) ∧
      DInv after r ds z' d' ∧ StreamBuffers after r ∧ Fr h r ds d z after z' d' ∧
      Zlib.Deflate.Engine.Proofs.StoredMeaning flush bstate z' d' :=
  Zlib.Deflate.Engine.Proofs.stored_spec_of inv entry flush level

end Zlib.Deflate.Universal
