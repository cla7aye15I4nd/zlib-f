import ZlibF.Proof.«deflate.c.engine.lmbody»

/-!
# deflate.c, engine: `longest_match`

`longest_match_ok`: under the environment `LMEnv` (window block, `prev` block, position facts and the chain facts that
the hash invariant H gives), the function does not fault, only `match_start` changes, and it returns
`min(best_len, lookahead)` where `prev_length <= best_len <= 258` and either `best_len = prev_length` with `match_start`
unchanged, or `match_start` names a match: it lies before `strstart`, within `MAX_DIST`, and the window bytes at
`match_start` and at `strstart` agree on the first `best_len` bytes (so on the returned length).
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate

/-- The condition of the `longest_match` loop, as in the translation. -/
def lmCond (prev : WPtr) (wmask limit : UInt32) : LMState → M (Bool × LMState) := fun st => do
  if st.brk then return (false, st)
  let cm : UInt32 := (← Ptr.index prev (st.cur_match &&& wmask).toNat).toUInt32
  let st := { st with cur_match := cm }
  if cm > limit then
    let cl := st.chain_length - 1
    return (cl != 0, { st with chain_length := cl })
  return (false, st)

theorem longest_match_unfold (s : DeflateStatePtr) (cur_match : UInt32) : longest_match s cur_match = (do
  let d ← ldDeflateState s
  let mut chain_length : UInt32 := d.max_chain_length
  let scan ← padd d.window d.strstart.toNat
  let best_len : Int32 := d.prev_length.toInt32
  let mut nice_match : Int32 := d.nice_match
  let maxd : UInt32 := d.w_size - MIN_LOOKAHEAD_u
  let limit : UInt32 := if d.strstart > maxd then d.strstart - maxd else 0
  let prev := d.prev
  let wmask := d.w_mask
  let _strend ← padd (← padd d.window d.strstart.toNat) MAX_MATCH_u.toNat
  let scan_end1 ← index8 scan (← isub best_len 1).toInt
  let scan_end ← index8 scan best_len.toInt
  if d.prev_length ≥ d.good_match then chain_length := chain_length >>> 2
  if nice_match.toUInt32 > d.lookahead then nice_match := d.lookahead.toInt32
  let st ← cdoWhile (lm_body s) (lmCond prev wmask limit)
    { cur_match, chain_length, best_len, nice_match, scan, scan_end1, scan_end, brk := false }
  let lookahead ← rd s (·.lookahead)
  if st.best_len.toUInt32 ≤ lookahead then return st.best_len.toUInt32
  return lookahead) := rfl

/-- The state after the condition read `v = prev[cur_match & wmask]` and set the counter to `cl`. -/
def lmStep (st1 : LMState) (v : UInt16) (cl : UInt32) : LMState := { st1 with cur_match := v.toUInt32, chain_length := cl }

/-- What the loop guarantees at its end (or at `break`). -/
def LMOut (h0 : Heap) (sr : Nat) (d : DeflateState) (wa : Array UInt8) (st : LMState) (h : Heap) : Prop :=
  ∃ (ms : UInt32) (b : Nat), h = hAt h0 sr d ms ∧ st.best_len.toInt = (b : Int) ∧ d.prev_length.toNat ≤ b ∧ b ≤ 258 ∧
    ((b = d.prev_length.toNat ∧ ms = d.match_start) ∨
     (d.prev_length.toNat < b ∧ GoodMatch wa d.strstart.toNat d.w_size.toNat ms.toNat b))

theorem LMInv.out {h0 : Heap} {sr wb pb : Nat} {d : DeflateState} {wa : Array UInt8} {pa : Array UInt16} {c : UInt32}
    {st : LMState} {h : Heap} (hI : LMInv h0 sr d wb pb wa pa c st h) : LMOut h0 sr d wa st h := by
  obtain ⟨ms, b, hh, _, hb, hpl, hb258, _, _, hgood⟩ := hI
  exact ⟨ms, b, hh, hb, hpl, hb258, hgood⟩

theorem u32_toInt32_toInt (x : UInt32) (hx : x.toNat < 2 ^ 31) : x.toInt32.toInt = (x.toNat : Int) := by
  have h1 : x.toInt32.toInt = x.toBitVec.toInt := rfl
  rw [BitVec.toInt_eq_toNat_cond] at h1
  have : x.toBitVec.toNat = x.toNat := rfl
  rw [this] at h1
  split at h1 <;> omega

theorem i32_toUInt32_toNat (x : Int32) (b : Nat) (hx : x.toInt = (b : Int)) (hb : b < 2 ^ 31) : x.toUInt32.toNat = b := by
  have h1 : x.toInt = x.toBitVec.toInt := rfl
  rw [BitVec.toInt_eq_toNat_cond] at h1
  have : x.toUInt32.toNat = x.toBitVec.toNat := rfl
  rw [this]
  split at h1 <;> omega

/-- **The loop.** From a state with the invariant and `brk = false`, the loop does not fault and ends in a state
that satisfies `LMOut`. The measure is `cur_match`, which falls at every step because `prev[p & wmask] < p` (H). -/
theorem lm_loop_ok {h0 : Heap} {sr wb pb : Nat} {d : DeflateState} {wa : Array UInt8} {pa : Array UInt16} {c : UInt32}
    (E : LMEnv h0 sr d wb pb wa pa c) (limit : UInt32) (hlimit : limit.toNat = lmLimit d.strstart.toNat (d.w_size.toNat - 262))
    (st : LMState) (h : Heap) (hbrk : st.brk = false) (hI : LMInv h0 sr d wb pb wa pa c st h) :
    ∃ st' h', cdoWhile (lm_body (some (.tab sr))) (lmCond d.prev d.w_mask limit) st h = .ok (st', h') ∧
      LMOut h0 sr d wa st' h' := by
  have key := cdoWhile_measure (σ := LMState) (body := lm_body (some (.tab sr))) (cond := lmCond d.prev d.w_mask limit)
    (fun st h => st.brk = false ∧ LMInv h0 sr d wb pb wa pa c st h) (fun st => st.cur_match.toNat)
    (fun st h => LMOut h0 sr d wa st h) ?_ (s := st) (h := h) ⟨hbrk, hI⟩
    (by unfold fuel; have := st.cur_match.toNat_lt; omega)
  · exact key
  · intro st h hIn
    obtain ⟨hbrk, hI⟩ := hIn
    obtain ⟨st1, h1, hrun, hI1, hcur, hcl, hnm⟩ := lm_body_ok E st hbrk hI
    have hout := hI1.out
    by_cases hb1 : st1.brk = true
    · exact ⟨st1, h1, false, st1, h1, hrun, by simp [lmCond, hb1], fun _ => hout, by simp⟩
    have hb1' : st1.brk = false := by simpa using hb1
    obtain ⟨k, hk, hk9, hk15⟩ := E.wsb
    have hws9 : 512 ≤ d.w_size.toNat := by
      rw [hk]; calc 512 = 2 ^ 9 := by decide
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk9
    have hI1' := hI1
    obtain ⟨ms1, b1, hh1, hscan1, hb, hpl, hb258, hse', hch1, hgood1⟩ := hI1'
    obtain ⟨hcm1, hcmlt, hcmprev, _⟩ := E.chain _ hch1
    have hwm : d.w_mask.toNat = d.w_size.toNat - 1 := by
      rw [E.wmask, UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
      simp
    have hidx : (st1.cur_match &&& d.w_mask).toNat = st1.cur_match.toNat &&& (d.w_size.toNat - 1) := by
      rw [UInt32.toNat_and, hwm]
    have hidx_lt : st1.cur_match.toNat &&& (d.w_size.toNat - 1) < d.w_size.toNat :=
      and_wm_lt (by rw [hk]) _
    have hpw : h1.words pb = some pa := by rw [hh1]; exact E.pwords
    have hidx_arr : st1.cur_match.toNat &&& (d.w_size.toNat - 1) < pa.size := by have := E.psize; omega
    have hrd : Ptr.index d.prev (↑(st1.cur_match &&& d.w_mask).toNat) h1 =
        .ok (wfn pa (st1.cur_match.toNat &&& (d.w_size.toNat - 1)), h1) := by
      rw [E.prevp, hidx]
      have := Ptr.index_ok (h := h1) (r := WRef.blk pb) (a := pa) (off := 0)
        (i := st1.cur_match.toNat &&& (d.w_size.toNat - 1)) (by simpa using hpw) (by omega)
      unfold OkOn at this
      simp only [Nat.zero_add] at this
      rw [this, wfn_getElem _ _ hidx_arr]
    by_cases big : limit.toNat < (wfn pa (st1.cur_match.toNat &&& (d.w_size.toNat - 1))).toNat
    · have hgt : limit < (wfn pa (st1.cur_match.toNat &&& (d.w_size.toNat - 1))).toUInt32 := by
        rw [UInt32.lt_iff_toNat_lt]; simpa using big
      have hch2 : Chain (wfn pa) (d.w_size.toNat - 1) (lmLimit d.strstart.toNat (d.w_size.toNat - 262)) c.toNat
          (wfn pa (st1.cur_match.toNat &&& (d.w_size.toNat - 1))).toNat :=
        Chain.step hch1 rfl (by rw [← hlimit]; exact big)
      by_cases hcl0 : (st1.chain_length - 1 != 0) = true
      · refine ⟨st1, h1, true, lmStep st1 (wfn pa (st1.cur_match.toNat &&& (d.w_size.toNat - 1))) (st1.chain_length - 1), h1, hrun, ?_, by simp, ?_⟩
        · simp only [lmCond, bind_app, pure_app, M_ite_app, hb1', Bool.false_eq_true, ↓reduceIte, hrd, GT.gt, hgt, hcl0, lmStep]
        · intro _
          refine ⟨⟨hb1', ms1, b1, hh1, hscan1, hb, hpl, hb258, hse', ?_, hgood1⟩, ?_⟩
          · simpa [lmStep] using hch2
          · simp only [lmStep, hcur] at hcmprev ⊢
            simpa using hcmprev
      · have hcl0' : (st1.chain_length - 1 != 0) = false := by simpa using hcl0
        refine ⟨st1, h1, false, lmStep st1 (wfn pa (st1.cur_match.toNat &&& (d.w_size.toNat - 1))) (st1.chain_length - 1), h1, hrun, ?_, fun _ => hout, by simp⟩
        simp only [lmCond, bind_app, pure_app, M_ite_app, hb1', Bool.false_eq_true, ↓reduceIte, hrd, GT.gt, hgt, hcl0', lmStep]
    · have hng : ¬ limit < (wfn pa (st1.cur_match.toNat &&& (d.w_size.toNat - 1))).toUInt32 := by
        rw [UInt32.lt_iff_toNat_lt]; simpa using big
      refine ⟨st1, h1, false, lmStep st1 (wfn pa (st1.cur_match.toNat &&& (d.w_size.toNat - 1))) st1.chain_length, h1, hrun, ?_, fun _ => hout, by simp⟩
      simp only [lmCond, bind_app, pure_app, M_ite_app, hb1', Bool.false_eq_true, ↓reduceIte, hrd, GT.gt, hng, lmStep]

theorem hAt_self (h0 : Heap) (sr : Nat) (d : DeflateState) (hd : h0.dstates sr = some d) :
    hAt h0 sr d d.match_start = h0 := by
  simp [hAt, upd_self _ _ _ hd]

/-- The initial state of the loop satisfies the invariant, whatever `chain_length` and `nice_match` are. -/
theorem lm_init_inv {h0 : Heap} {sr wb pb : Nat} {d : DeflateState} {wa : Array UInt8} {pa : Array UInt16} {c : UInt32}
    (E : LMEnv h0 sr d wb pb wa pa c) (cl : UInt32) (nm : Int32) :
    LMInv h0 sr d wb pb wa pa c
      { cur_match := c, chain_length := cl, best_len := d.prev_length.toInt32, nice_match := nm,
        scan := Ptr.ref (BRef.blk wb) d.strstart.toNat,
        scan_end1 := bfn wa (d.strstart.toNat + d.prev_length.toNat - 1),
        scan_end := bfn wa (d.strstart.toNat + d.prev_length.toNat), brk := false } h0 := by
  have h31 : d.prev_length.toNat < 2 ^ 31 := by have := E.plle; omega
  refine ⟨d.match_start, d.prev_length.toNat, (hAt_self h0 sr d E.hd).symm, rfl, u32_toInt32_toInt _ h31, Nat.le_refl _,
    E.plle, fun _ => ⟨rfl, rfl⟩, ?_, Or.inl ⟨rfl, rfl⟩⟩
  exact Chain.start

theorem lm_loop_total {h0 : Heap} {sr wb pb : Nat} {d : DeflateState} {wa : Array UInt8} {pa : Array UInt16} {c : UInt32}
    (E : LMEnv h0 sr d wb pb wa pa c) (limit : UInt32) (hlimit : limit.toNat = lmLimit d.strstart.toNat (d.w_size.toNat - 262))
    (st : LMState) (h : Heap) (hbrk : st.brk = false) (hI : LMInv h0 sr d wb pb wa pa c st h)
    (res : Except Fault (LMState × Heap)) (hres : cdoWhile (lm_body (some (.tab sr))) (lmCond d.prev d.w_mask limit) st h = res) :
    ∃ st' h', res = .ok (st', h') ∧ LMOut h0 sr d wa st' h' := by
  obtain ⟨st', h', hr, ho⟩ := lm_loop_ok E limit hlimit st h hbrk hI
  exact ⟨st', h', hres.symm.trans hr, ho⟩


/-- The part of `longest_match` after the two tests on `prev_length` and `lookahead`: the loop and the final `min`. -/
def lmRest (sr : Nat) (L : UInt32) (d : DeflateState) (c : UInt32) (wb : Nat) (wa : Array UInt8) (cl : UInt32) (nm : Int32) :
    M UInt32 := do
  let st ← cdoWhile (lm_body (some (.tab sr))) (lmCond d.prev d.w_mask L)
      { cur_match := c, chain_length := cl, best_len := d.prev_length.toInt32, nice_match := nm,
        scan := Ptr.ref (BRef.blk wb) d.strstart.toNat,
        scan_end1 := bfn wa (d.strstart.toNat + d.prev_length.toNat - 1),
        scan_end := bfn wa (d.strstart.toNat + d.prev_length.toNat), brk := false }
  let lookahead ← rd (some (.tab sr)) (fun x => x.lookahead)
  if st.best_len.toUInt32 ≤ lookahead then return st.best_len.toUInt32
  return lookahead

theorem lmRest_ok {h0 : Heap} {sr wb pb : Nat} {d : DeflateState} {wa : Array UInt8} {pa : Array UInt16} {c : UInt32}
    (E : LMEnv h0 sr d wb pb wa pa c) (L : UInt32)
    (hlimit : L.toNat = lmLimit d.strstart.toNat (d.w_size.toNat - 262)) (cl : UInt32) (nm : Int32) :
    ∃ (r : UInt32) (h' : Heap) (ms : UInt32) (best : Nat),
      lmRest sr L d c wb wa cl nm h0 = .ok (r, h') ∧
      r = UInt32.ofNat (lmResult best d.lookahead.toNat) ∧ h' = hAt h0 sr d ms ∧
      d.prev_length.toNat ≤ best ∧ best ≤ 258 ∧
      ((best = d.prev_length.toNat ∧ ms = d.match_start) ∨
       (d.prev_length.toNat < best ∧ GoodMatch wa d.strstart.toNat d.w_size.toNat ms.toNat best)) := by
  obtain ⟨st', h', hrun, ms, b, hh, hb, hpl, hb258, hgood⟩ :=
    lm_loop_ok E L hlimit _ h0 rfl (lm_init_inv E cl nm)
  subst hh
  have hdd : (hAt h0 sr d ms).dstates sr = some { d with match_start := ms } := by simp [hAt]
  have hrd : rd (some (.tab sr)) (fun x => x.lookahead) (hAt h0 sr d ms) = .ok (d.lookahead, hAt h0 sr d ms) := by
    simp [rd, ldDeflateState_tab hdd]
  have hbn : st'.best_len.toUInt32.toNat = b := i32_toUInt32_toNat _ b hb (by omega)
  have hbu : st'.best_len.toUInt32 = UInt32.ofNat b := by
    apply UInt32.toNat_inj.mp; rw [hbn]; simp; omega
  by_cases hle : b ≤ d.lookahead.toNat
  · have hle' : st'.best_len.toUInt32 ≤ d.lookahead := by
      rw [UInt32.le_iff_toNat_le, hbn]; exact hle
    refine ⟨st'.best_len.toUInt32, hAt h0 sr d ms, ms, b, ?_, ?_, rfl, hpl, hb258, hgood⟩
    · simp only [lmRest, bind_app, pure_app, M_ite_app, hrun, hrd, hle', ite_true]
    · rw [hbu]; unfold lmResult; rw [if_pos hle]
  · have hle' : ¬ st'.best_len.toUInt32 ≤ d.lookahead := by
      rw [UInt32.le_iff_toNat_le, hbn]; exact hle
    refine ⟨d.lookahead, hAt h0 sr d ms, ms, b, ?_, ?_, rfl, hpl, hb258, hgood⟩
    · simp only [lmRest, bind_app, pure_app, M_ite_app, hrun, hrd, hle', ite_false]
    · unfold lmResult; rw [if_neg hle]; simp

/-- **longest_match, safety and specification.** Under `LMEnv` the call does not fault and only `match_start` changes
(the result heap is `hAt h0 sr d ms`). It returns `min(best, lookahead)` for some `best` with
`prev_length <= best <= 258`; either `best = prev_length` and `match_start` is unchanged, or `match_start` names a good
match of length `best`: before `strstart`, within `MAX_DIST`, and the window bytes agree on the first `best` bytes. -/
theorem longest_match_ok {h0 : Heap} {sr wb pb : Nat} {d : DeflateState} {wa : Array UInt8} {pa : Array UInt16} {c : UInt32}
    (E : LMEnv h0 sr d wb pb wa pa c) :
    ∃ (r : UInt32) (h' : Heap) (ms : UInt32) (best : Nat),
      longest_match (some (.tab sr)) c h0 = .ok (r, h') ∧
      r = UInt32.ofNat (lmResult best d.lookahead.toNat) ∧ h' = hAt h0 sr d ms ∧
      d.prev_length.toNat ≤ best ∧ best ≤ 258 ∧
      ((best = d.prev_length.toNat ∧ ms = d.match_start) ∨
       (d.prev_length.toNat < best ∧ GoodMatch wa d.strstart.toNat d.w_size.toNat ms.toNat best)) := by
  obtain ⟨k, hk, hk9, hk15⟩ := E.wsb
  have hws9 : 512 ≤ d.w_size.toNat := by
    rw [hk]; calc 512 = 2 ^ 9 := by decide
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk9
  have hws15 : d.w_size.toNat ≤ 32768 := by
    rw [hk]; calc 2 ^ k ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) hk15
      _ = 32768 := by decide
  have hroom := E.room
  have hasz := E.asize
  have hss : d.strstart.toNat + 258 < wa.size := by omega
  have hss2 : 2 ≤ d.strstart.toNat := by have := E.c1; have := E.clt; omega
  have hmm : MAX_MATCH_u.toNat = 258 := rfl
  have h1i : (1 : Int32).toInt = 1 := by decide
  have hpl := E.plle
  have e_ld0 : ldDeflateState (some (.tab sr)) h0 = .ok (d, h0) := ldDeflateState_tab E.hd
  have hbytes : h0.bytes wb = some wa := E.wbytes
  have f14 : padd (Ptr.ref (BRef.blk wb) 0) d.strstart.toNat h0 = .ok (Ptr.ref (BRef.blk wb) d.strstart.toNat, h0) := by
    simpa using padd_ok' (h := h0) (r := BRef.blk wb) (a := wa) (off := 0) (n := d.strstart.toNat)
      (by simpa using hbytes) (by omega)
  have f15 : padd (Ptr.ref (BRef.blk wb) d.strstart.toNat) 258 h0 =
      .ok (Ptr.ref (BRef.blk wb) (d.strstart.toNat + 258), h0) := padd_ok' (by simpa using hbytes) (by omega)
  have i0 : d.prev_length.toInt32.toInt = (d.prev_length.toNat : Int) := u32_toInt32_toInt _ (by omega)
  have i4 : isub d.prev_length.toInt32 1 h0 = .ok (Int32.ofInt ((d.prev_length.toNat : Int) - 1), h0) := by
    rw [isub_ok _ 1 (by rw [i0, h1i]; omega), i0, h1i]
  have i5' : (Int32.ofInt ((d.prev_length.toNat : Int) - 1)).toInt = (d.prev_length.toNat : Int) - 1 :=
    Int32.toInt_ofInt_of_le (by omega) (by omega)
  have i5 : index8 (Ptr.ref (BRef.blk wb) d.strstart.toNat) ((d.prev_length.toNat : Int) - 1) h0 =
      .ok (bfn wa (d.strstart.toNat + d.prev_length.toNat - 1), h0) := index8_bfn hbytes (by omega) (by omega)
  have i6 : index8 (Ptr.ref (BRef.blk wb) d.strstart.toNat) (d.prev_length.toNat : Int) h0 =
      .ok (bfn wa (d.strstart.toNat + d.prev_length.toNat), h0) := index8_bfn hbytes (by omega) (by omega)
  have hmin : MIN_LOOKAHEAD_u.toNat = 262 := rfl
  have hsub : (d.w_size - MIN_LOOKAHEAD_u).toNat = d.w_size.toNat - 262 := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, hmin]; omega), hmin]
  obtain ⟨L, hL⟩ : ∃ L : UInt32, L = (if d.strstart > d.w_size - MIN_LOOKAHEAD_u then d.strstart - (d.w_size - MIN_LOOKAHEAD_u) else 0) :=
    ⟨_, rfl⟩
  have hlimit : L.toNat = lmLimit d.strstart.toNat (d.w_size.toNat - 262) := by
    rw [hL]; unfold lmLimit
    by_cases hg : d.strstart > d.w_size - MIN_LOOKAHEAD_u
    · have hg' : d.strstart.toNat > d.w_size.toNat - 262 := by
        rw [GT.gt, UInt32.lt_iff_toNat_lt, hsub] at hg; exact hg
      rw [if_pos hg, if_pos hg', UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; rw [GT.gt, UInt32.lt_iff_toNat_lt] at hg; omega), hsub]
    · have hg' : ¬ d.strstart.toNat > d.w_size.toNat - 262 := by
        intro hh; apply hg; rw [GT.gt, UInt32.lt_iff_toNat_lt, hsub]; exact hh
      rw [if_neg hg, if_neg hg']; rfl
  have hLsame : (if d.strstart > d.w_size - MIN_LOOKAHEAD_u then d.strstart - (d.w_size - MIN_LOOKAHEAD_u) else 0) = L := hL.symm
  have key : ∀ (cl : UInt32) (nm : Int32), ∃ (r : UInt32) (h' : Heap) (ms : UInt32) (best : Nat),
      lmRest sr L d c wb wa cl nm h0 = .ok (r, h') ∧
      r = UInt32.ofNat (lmResult best d.lookahead.toNat) ∧ h' = hAt h0 sr d ms ∧
      d.prev_length.toNat ≤ best ∧ best ≤ 258 ∧
      ((best = d.prev_length.toNat ∧ ms = d.match_start) ∨
       (d.prev_length.toNat < best ∧ GoodMatch wa d.strstart.toNat d.w_size.toNat ms.toNat best)) :=
    fun cl nm => lmRest_ok E L hlimit cl nm
  rw [longest_match_unfold]
  simp only [bind_app, pure_app, M_ite_app, e_ld0, E.win, f14, f15, i0, i4, i5', i5, i6, hmm, hLsame]
  by_cases hg : d.prev_length ≥ d.good_match <;> by_cases hn : d.nice_match.toUInt32 > d.lookahead
  · obtain ⟨r, h', ms, best, hr, hrest⟩ := key (d.max_chain_length >>> 2) d.lookahead.toInt32
    refine ⟨r, h', ms, best, ?_, hrest⟩
    simp only [hg, hn, ite_true]; simp only [lmRest, bind_app, pure_app, M_ite_app] at hr; exact hr
  · obtain ⟨r, h', ms, best, hr, hrest⟩ := key (d.max_chain_length >>> 2) d.nice_match
    refine ⟨r, h', ms, best, ?_, hrest⟩
    simp only [hg, hn, ite_true, ite_false]; simp only [lmRest, bind_app, pure_app, M_ite_app] at hr; exact hr
  · obtain ⟨r, h', ms, best, hr, hrest⟩ := key d.max_chain_length d.lookahead.toInt32
    refine ⟨r, h', ms, best, ?_, hrest⟩
    simp only [hg, hn, ite_true, ite_false]; simp only [lmRest, bind_app, pure_app, M_ite_app] at hr; exact hr
  · obtain ⟨r, h', ms, best, hr, hrest⟩ := key d.max_chain_length d.nice_match
    refine ⟨r, h', ms, best, ?_, hrest⟩
    simp only [hg, hn, ite_true, ite_false]; simp only [lmRest, bind_app, pure_app, M_ite_app] at hr; exact hr

end Zlib.Deflate.Engine.Proofs
