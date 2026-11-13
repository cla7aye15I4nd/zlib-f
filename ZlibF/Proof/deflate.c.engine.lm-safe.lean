import ZlibF.Proof.«deflate.c.engine.lmmain»

/-!
# deflate.c, engine: `longest_match` from a positional chain fact

`longest_match_safe` is `longest_match_ok` for safety. Its environment `LMEnvS` asks of the chain from the first
candidate only that every position on it is in `[1, strstart)`: the order of the chain and the third-byte fact of
the hash are not needed. The loop ends by `chain_length` (the measure is `chain_length - 1`, which falls at every
step that continues); a found match is `SafeMatch`: before `strstart`, within `MAX_DIST`, at most 258 long. The
proofs are those of `deflate.c.engine.lmbody` and `deflate.c.engine.lmmain` without the byte agreement.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate

/-- A found match as safety needs it: before `ss`, within `MAX_DIST`, at most 258 bytes. -/
def SafeMatch (ss ws m len : Nat) : Prop :=
  m < ss ∧ ss - m ≤ ws - 262 ∧ len ≤ 258

theorem GoodMatch.safe {wa : Array UInt8} {ss ws m len : Nat} (g : GoodMatch wa ss ws m len) : SafeMatch ss ws m len :=
  ⟨g.1, g.2.1, g.2.2.1⟩

structure LMEnvS (h0 : Heap) (sr : Nat) (d : DeflateState) (wb pb : Nat) (wa : Array UInt8) (pa : Array UInt16)
    (c : UInt32) : Prop where
  hd : h0.dstates sr = some d
  win : d.window = .ref (.blk wb) 0
  wbytes : h0.bytes wb = some wa
  prevp : d.prev = .ref (.blk pb) 0
  pwords : h0.words pb = some pa
  wsb : ∃ b, d.w_size.toNat = 2 ^ b ∧ 9 ≤ b ∧ b ≤ 15
  wmask : d.w_mask = d.w_size - 1
  psize : d.w_size.toNat ≤ pa.size
  asize : 2 * d.w_size.toNat ≤ wa.size
  room : d.strstart.toNat + 262 ≤ 2 * d.w_size.toNat
  lale : d.lookahead.toNat ≤ 2 * d.w_size.toNat
  plle : d.prev_length.toNat ≤ 258
  c1 : 1 ≤ c.toNat
  clt : c.toNat < d.strstart.toNat
  cdist : d.strstart.toNat - c.toNat ≤ d.w_size.toNat - 262
  chain : ∀ p, Chain (wfn pa) (d.w_size.toNat - 1) (lmLimit d.strstart.toNat (d.w_size.toNat - 262)) c.toNat p →
    1 ≤ p ∧ p < d.strstart.toNat

def LMInvS (h0 : Heap) (sr : Nat) (d : DeflateState) (wb pb : Nat) (wa : Array UInt8) (pa : Array UInt16)
    (c : UInt32) (st : LMState) (h : Heap) : Prop :=
  ∃ (ms : UInt32) (b : Nat), h = hAt h0 sr d ms ∧
    st.scan = .ref (.blk wb) d.strstart.toNat ∧ st.best_len.toInt = (b : Int) ∧ d.prev_length.toNat ≤ b ∧ b ≤ 258 ∧
    (st.brk = false → st.scan_end1 = bfn wa (d.strstart.toNat + b - 1) ∧ st.scan_end = bfn wa (d.strstart.toNat + b)) ∧
    Chain (wfn pa) (d.w_size.toNat - 1) (lmLimit d.strstart.toNat (d.w_size.toNat - 262)) c.toNat st.cur_match.toNat ∧
    ((b = d.prev_length.toNat ∧ ms = d.match_start) ∨
     (d.prev_length.toNat < b ∧ SafeMatch d.strstart.toNat d.w_size.toNat ms.toNat b))


theorem LMEnvS.dist {h0 : Heap} {sr : Nat} {d : DeflateState} {wb pb : Nat} {wa : Array UInt8} {pa : Array UInt16} {c : UInt32}
    (E : LMEnvS h0 sr d wb pb wa pa c) :
    ∀ p, Chain (wfn pa) (d.w_size.toNat - 1) (lmLimit d.strstart.toNat (d.w_size.toNat - 262)) c.toNat p →
      p ≤ d.strstart.toNat → d.strstart.toNat - p ≤ d.w_size.toNat - 262 := by
  intro p hp hps
  induction hp with
  | start => exact E.cdist
  | step _ hq hlim _ => unfold lmLimit at hlim; split at hlim <;> omega

/-- **One candidate.** The body of the `longest_match` loop does not fault when the loop invariant holds and

`brk` is false, and the invariant holds afterwards; `cur_match`, `chain_length` and `nice_match` are not changed. -/
theorem lm_body_safe {h0 : Heap} {sr wb pb : Nat} {d : DeflateState} {wa : Array UInt8} {pa : Array UInt16} {c : UInt32}
    (E : LMEnvS h0 sr d wb pb wa pa c) (st : LMState) {h : Heap} (hbrk : st.brk = false)
    (hI : LMInvS h0 sr d wb pb wa pa c st h) :
    ∃ st' h', lm_body (some (.tab sr)) st h = .ok (st', h') ∧ LMInvS h0 sr d wb pb wa pa c st' h' ∧
      st'.cur_match = st.cur_match ∧ st'.chain_length = st.chain_length ∧ st'.nice_match = st.nice_match := by
  have hI0 := hI
  obtain ⟨ms, b, rfl, hscan, hb, hpl, hb258, hse, hch, hgood⟩ := hI
  obtain ⟨hse1, hse⟩ := hse hbrk
  obtain ⟨k, hk, hk9, hk15⟩ := E.wsb
  have hws9 : 512 ≤ d.w_size.toNat := by
    rw [hk]; calc 512 = 2 ^ 9 := by decide
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk9
  have hws15 : d.w_size.toNat ≤ 32768 := by
    rw [hk]; calc 2 ^ k ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) hk15
      _ = 32768 := by decide
  have hroom := E.room
  have hasz := E.asize
  obtain ⟨hcm1, hcmlt⟩ := E.chain _ hch
  have hdist := E.dist _ hch (by omega)
  have hss : d.strstart.toNat + 258 < wa.size := by omega
  -- the heap
  have hdd : (hAt h0 sr d ms).dstates sr = some { d with match_start := ms } := by simp [hAt]
  have e_ld : ldDeflateState (some (.tab sr)) (hAt h0 sr d ms) = .ok ({ d with match_start := ms }, hAt h0 sr d ms) :=
    ldDeflateState_tab hdd
  have hbytes : (hAt h0 sr d ms).bytes wb = some wa := E.wbytes
  have hmm : MAX_MATCH_u.toNat = 258 := rfl
  have h258 : (258 : Int32).toInt = 258 := by decide
  have h1i : (1 : Int32).toInt = 1 := by decide
  -- the monadic steps
  have f2 : padd (Ptr.ref (BRef.blk wb) 0) st.cur_match.toNat (hAt h0 sr d ms) = .ok (Ptr.ref (BRef.blk wb) st.cur_match.toNat, hAt h0 sr d ms) := by
    simpa using padd_ok' (h := hAt h0 sr d ms) (r := BRef.blk wb) (a := wa) (off := 0) (n := st.cur_match.toNat)
      (by simpa using hbytes) (by omega)
  have f3 : index8 (Ptr.ref (BRef.blk wb) st.cur_match.toNat) (b : Int) (hAt h0 sr d ms) = .ok (bfn wa (st.cur_match.toNat + b), hAt h0 sr d ms) :=
    index8_bfn hbytes (by omega) (by omega)
  have f4 : isub st.best_len 1 (hAt h0 sr d ms) = .ok (Int32.ofInt ((b : Int) - 1), hAt h0 sr d ms) := by
    rw [isub_ok st.best_len 1 (by rw [hb, h1i]; omega)]
    rw [hb, h1i]
  have f5 : (Int32.ofInt ((b : Int) - 1)).toInt = (b : Int) - 1 := Int32.toInt_ofInt_of_le (by omega) (by omega)
  have f6 : index8 (Ptr.ref (BRef.blk wb) st.cur_match.toNat) ((b : Int) - 1) (hAt h0 sr d ms) = .ok (bfn wa (st.cur_match.toNat + b - 1), hAt h0 sr d ms) :=
    index8_bfn hbytes (by omega) (by omega)
  have f7 : load8 (Ptr.ref (BRef.blk wb) st.cur_match.toNat) (hAt h0 sr d ms) = .ok (bfn wa st.cur_match.toNat, hAt h0 sr d ms) :=
    load8_bfn hbytes (by omega)
  have f8 : load8 (Ptr.ref (BRef.blk wb) d.strstart.toNat) (hAt h0 sr d ms) = .ok (bfn wa d.strstart.toNat, hAt h0 sr d ms) :=
    load8_bfn hbytes (by omega)
  have f9 : padd (Ptr.ref (BRef.blk wb) st.cur_match.toNat) 1 (hAt h0 sr d ms) = .ok (Ptr.ref (BRef.blk wb) (st.cur_match.toNat + 1), hAt h0 sr d ms) :=
    padd_ok' (by simpa using hbytes) (by omega)
  have f10 : load8 (Ptr.ref (BRef.blk wb) (st.cur_match.toNat + 1)) (hAt h0 sr d ms) = .ok (bfn wa (st.cur_match.toNat + 1), hAt h0 sr d ms) :=
    load8_bfn hbytes (by omega)
  have f11 : index8 (Ptr.ref (BRef.blk wb) d.strstart.toNat) 1 (hAt h0 sr d ms) = .ok (bfn wa (d.strstart.toNat + 1), hAt h0 sr d ms) :=
    index8_bfn hbytes (by omega) (by omega)
  have f12 : padd (Ptr.ref (BRef.blk wb) d.strstart.toNat) 2 (hAt h0 sr d ms) = .ok (Ptr.ref (BRef.blk wb) (d.strstart.toNat + 2), hAt h0 sr d ms) :=
    padd_ok' (by simpa using hbytes) (by omega)
  have f13 : padd (Ptr.ref (BRef.blk wb) (st.cur_match.toNat + 1)) 1 (hAt h0 sr d ms) = .ok (Ptr.ref (BRef.blk wb) (st.cur_match.toNat + 2), hAt h0 sr d ms) :=
    padd_ok' (by simpa using hbytes) (by omega)
  have f14 : padd (Ptr.ref (BRef.blk wb) 0) d.strstart.toNat (hAt h0 sr d ms) = .ok (Ptr.ref (BRef.blk wb) d.strstart.toNat, hAt h0 sr d ms) := by
    simpa using padd_ok' (h := hAt h0 sr d ms) (r := BRef.blk wb) (a := wa) (off := 0) (n := d.strstart.toNat)
      (by simpa using hbytes) (by omega)
  have f15 : padd (Ptr.ref (BRef.blk wb) d.strstart.toNat) 258 (hAt h0 sr d ms) = .ok (Ptr.ref (BRef.blk wb) (d.strstart.toNat + 258), hAt h0 sr d ms) :=
    padd_ok' (by simpa using hbytes) (by omega)
  have f16 : psub (Ptr.ref (BRef.blk wb) (d.strstart.toNat + 258)) 258 (hAt h0 sr d ms) = .ok (Ptr.ref (BRef.blk wb) d.strstart.toNat, hAt h0 sr d ms) := by
    simpa using psub_ok' (h := hAt h0 sr d ms) (r := BRef.blk wb) (a := wa) (off := d.strstart.toNat + 258) (n := 258)
      (by simpa using hbytes) (by omega) (by omega)
  -- the early returns
  by_cases T1 : bfn wa (st.cur_match.toNat + b) = bfn wa (d.strstart.toNat + b)
  rotate_left
  · refine ⟨st, hAt h0 sr d ms, ?_, hI0, rfl, rfl, rfl⟩
    simp only [lm_body, bind_app, pure_app, M_ite_app, ↓reduceIte, e_ld, E.win, f2, hb, f3, hse, T1]
    simp [T1]
  by_cases T2 : bfn wa (st.cur_match.toNat + b - 1) = bfn wa (d.strstart.toNat + b - 1)
  rotate_left
  · refine ⟨st, hAt h0 sr d ms, ?_, hI0, rfl, rfl, rfl⟩
    simp only [lm_body, bind_app, pure_app, M_ite_app, ↓reduceIte, e_ld, E.win, f2, hb, f3, hse, T1, f4, f5, f6, hse1]
    simp [T2]
  by_cases T3 : bfn wa st.cur_match.toNat = bfn wa d.strstart.toNat
  rotate_left
  · refine ⟨st, hAt h0 sr d ms, ?_, hI0, rfl, rfl, rfl⟩
    simp only [lm_body, bind_app, pure_app, M_ite_app, ↓reduceIte, e_ld, E.win, f2, hb, f3, hse, T1, f4, f5, f6, hse1, T2, f7,
      hscan, f8]
    simp [T3]
  by_cases T4 : bfn wa (st.cur_match.toNat + 1) = bfn wa (d.strstart.toNat + 1)
  rotate_left
  · refine ⟨st, hAt h0 sr d ms, ?_, hI0, rfl, rfl, rfl⟩
    simp only [lm_body, bind_app, pure_app, M_ite_app, ↓reduceIte, e_ld, E.win, f2, hb, f3, hse, T1, f4, f5, f6, hse1, T2, f7,
      hscan, f8, T3, f9, f10, f11]
    simp [T4]
  obtain ⟨r, hr⟩ : ∃ r, r = matchLen (bfn wa) d.strstart.toNat st.cur_match.toNat := ⟨_, rfl⟩
  obtain ⟨hr3, hr258⟩ := matchLen_bounds (bfn wa) d.strstart.toNat st.cur_match.toNat
  rw [← hr] at hr3 hr258
  have hcmss : st.cur_match.toNat ≤ d.strstart.toNat := by omega
  have hloop := lm_inner_loop_any (h := hAt h0 sr d ms) hbytes d.strstart.toNat st.cur_match.toNat hss hcmss
  rw [← hr] at hloop
  have fd : Ptr.diff (Ptr.ref (BRef.blk wb) (d.strstart.toNat + 258)) (Ptr.ref (BRef.blk wb) (d.strstart.toNat + r)) (hAt h0 sr d ms) =
      .ok (Int64.ofInt (258 - (r : Int)), hAt h0 sr d ms) := by
    have := Ptr.diff_ok (h := hAt h0 sr d ms) (r := BRef.blk wb) (a := wa) (o1 := d.strstart.toNat + 258) (o2 := d.strstart.toNat + r)
      (by simpa using hbytes) (by omega) (by omega) (by omega)
    unfold OkOn at this
    rw [this]
    congr 3
    omega
  have fl : isub 258 (Int64.ofInt (258 - (r : Int))).toInt32 (hAt h0 sr d ms) = .ok (Int32.ofInt (r : Int), hAt h0 sr d ms) := by
    rw [Int64.toInt32_ofInt]
    have e1 : (Int32.ofInt (258 - (r : Int))).toInt = 258 - (r : Int) := Int32.toInt_ofInt_of_le (by omega) (by omega)
    rw [isub_ok 258 _ (by rw [e1, h258]; omega), e1, h258]
    congr 3
    omega
  have hlen : (Int32.ofInt (r : Int)).toInt = (r : Int) := Int32.toInt_ofInt_of_le (by omega) (by omega)
  by_cases hgt : b < r
  rotate_left
  · -- no improvement
    have hngt : ¬ (Int32.ofInt (r : Int) > st.best_len) := by
      rw [GT.gt, Int32.lt_iff_toInt_lt, hb, hlen]; omega
    refine ⟨{ st with scan := Ptr.ref (BRef.blk wb) d.strstart.toNat }, hAt h0 sr d ms, ?_, ?_, rfl, rfl, rfl⟩
    · simp only [lm_body, bind_app, pure_app, M_ite_app, ↓reduceIte, e_ld, E.win, f2, hb, f3, hse, T1, f4, f5, f6, hse1, T2,
        f7, hscan, f8, T3, f9, f10, f11, T4, f12, f13, f14, f15, hmm, hloop, fd, fl, f16, hngt]
      simp [T1, T2, T3, T4, hngt]
    · exact ⟨ms, b, rfl, rfl, hb, hpl, hb258, fun _ => ⟨hse1, hse⟩, hch, hgood⟩
  -- an improvement
  have hgt' : Int32.ofInt (r : Int) > st.best_len := by
    rw [GT.gt, Int32.lt_iff_toInt_lt, hb, hlen]; omega
  have hgm : SafeMatch d.strstart.toNat d.w_size.toNat st.cur_match.toNat r :=
    ⟨hcmlt, hdist, hr258⟩
  have hdd1 : (hAt h0 sr d ms).dstates sr = some { d with match_start := ms } := hdd
  have f17 : wr (some (.tab sr)) (fun d => { d with match_start := st.cur_match }) (hAt h0 sr d ms) =
      .ok ((), hAt h0 sr d st.cur_match) := by
    unfold wr
    simp only [bind_app, e_ld]
    rw [stDeflateState_tab hdd1]
    simp [hAt, upd_upd]
  have hbytes1 : (hAt h0 sr d st.cur_match).bytes wb = some wa := E.wbytes
  have g1 : isub (Int32.ofInt (r : Int)) 1 (hAt h0 sr d st.cur_match) =
      .ok (Int32.ofInt ((r : Int) - 1), hAt h0 sr d st.cur_match) := by
    rw [isub_ok _ 1 (by rw [hlen, h1i]; omega)]
    rw [hlen, h1i]
  have g1' : (Int32.ofInt ((r : Int) - 1)).toInt = (r : Int) - 1 := Int32.toInt_ofInt_of_le (by omega) (by omega)
  have g2 : index8 (Ptr.ref (BRef.blk wb) d.strstart.toNat) ((r : Int) - 1) (hAt h0 sr d st.cur_match) =
      .ok (bfn wa (d.strstart.toNat + r - 1), hAt h0 sr d st.cur_match) := index8_bfn hbytes1 (by omega) (by omega)
  have g3 : index8 (Ptr.ref (BRef.blk wb) d.strstart.toNat) (r : Int) (hAt h0 sr d st.cur_match) =
      .ok (bfn wa (d.strstart.toNat + r), hAt h0 sr d st.cur_match) := index8_bfn hbytes1 (by omega) (by omega)
  have hgm' : SafeMatch d.strstart.toNat d.w_size.toNat st.cur_match.toNat r := hgm
  by_cases hnice : st.nice_match ≤ Int32.ofInt (r : Int)
  · refine ⟨{ st with scan := Ptr.ref (BRef.blk wb) d.strstart.toNat, best_len := Int32.ofInt (r : Int), brk := true },
      hAt h0 sr d st.cur_match, ?_, ?_, rfl, rfl, rfl⟩
    · simp only [lm_body, bind_app, pure_app, M_ite_app, ↓reduceIte, e_ld, E.win, f2, hb, f3, hse, T1, f4, f5, f6, hse1, T2,
        f7, hscan, f8, T3, f9, f10, f11, T4, f12, f13, f14, f15, hmm, hloop, fd, fl, f16, hgt', f17]
      simp [T1, T2, T3, T4, hgt', hnice]
    · exact ⟨st.cur_match, r, rfl, rfl, hlen, by omega, hr258, fun h => by simp at h, hch, Or.inr ⟨by omega, hgm'⟩⟩
  · refine ⟨{ st with scan := Ptr.ref (BRef.blk wb) d.strstart.toNat, best_len := Int32.ofInt (r : Int), scan_end1 := bfn wa (d.strstart.toNat + r - 1), scan_end := bfn wa (d.strstart.toNat + r) }, hAt h0 sr d st.cur_match, ?_, ?_, rfl, rfl, rfl⟩
    · simp only [lm_body, bind_app, pure_app, M_ite_app, ↓reduceIte, e_ld, E.win, f2, hb, f3, hse, T1, f4, f5, f6, hse1, T2,
        f7, hscan, f8, T3, f9, f10, f11, T4, f12, f13, f14, f15, hmm, hloop, fd, fl, f16, hgt', f17, g1, g1', g2, hlen, g3]
      simp [T1, T2, T3, T4, hgt', hnice]
    · exact ⟨st.cur_match, r, rfl, rfl, hlen, by omega, hr258, fun _ => ⟨rfl, rfl⟩, hch, Or.inr ⟨by omega, hgm'⟩⟩



/-- What the loop guarantees at its end (or at `break`). -/
def LMOutS (h0 : Heap) (sr : Nat) (d : DeflateState) (wa : Array UInt8) (st : LMState) (h : Heap) : Prop :=
  ∃ (ms : UInt32) (b : Nat), h = hAt h0 sr d ms ∧ st.best_len.toInt = (b : Int) ∧ d.prev_length.toNat ≤ b ∧ b ≤ 258 ∧
    ((b = d.prev_length.toNat ∧ ms = d.match_start) ∨
     (d.prev_length.toNat < b ∧ SafeMatch d.strstart.toNat d.w_size.toNat ms.toNat b))

theorem LMInvS.out {h0 : Heap} {sr wb pb : Nat} {d : DeflateState} {wa : Array UInt8} {pa : Array UInt16} {c : UInt32}
    {st : LMState} {h : Heap} (hI : LMInvS h0 sr d wb pb wa pa c st h) : LMOutS h0 sr d wa st h := by
  obtain ⟨ms, b, hh, _, hb, hpl, hb258, _, _, hgood⟩ := hI
  exact ⟨ms, b, hh, hb, hpl, hb258, hgood⟩


/-- **The loop.** From a state with the invariant and `brk = false`, the loop does not fault and ends in a state
that satisfies `LMOutS`. The measure is `chain_length - 1`: a step that continues has `chain_length - 1 ≠ 0` and
lowers it by one. -/
theorem lm_loop_safe {h0 : Heap} {sr wb pb : Nat} {d : DeflateState} {wa : Array UInt8} {pa : Array UInt16} {c : UInt32}
    (E : LMEnvS h0 sr d wb pb wa pa c) (limit : UInt32) (hlimit : limit.toNat = lmLimit d.strstart.toNat (d.w_size.toNat - 262))
    (st : LMState) (h : Heap) (hbrk : st.brk = false) (hI : LMInvS h0 sr d wb pb wa pa c st h) :
    ∃ st' h', cdoWhile (lm_body (some (.tab sr))) (lmCond d.prev d.w_mask limit) st h = .ok (st', h') ∧
      LMOutS h0 sr d wa st' h' := by
  have key := cdoWhile_measure (σ := LMState) (body := lm_body (some (.tab sr))) (cond := lmCond d.prev d.w_mask limit)
    (fun st h => st.brk = false ∧ LMInvS h0 sr d wb pb wa pa c st h) (fun st => (st.chain_length - 1).toNat)
    (fun st h => LMOutS h0 sr d wa st h) ?_ (s := st) (h := h) ⟨hbrk, hI⟩
    (by unfold fuel; have := (st.chain_length - 1).toNat_lt; omega)
  · exact key
  · intro st h hIn
    obtain ⟨hbrk, hI⟩ := hIn
    obtain ⟨st1, h1, hrun, hI1, hcur, hcl, hnm⟩ := lm_body_safe E st hbrk hI
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
          · have ne : st1.chain_length - 1 ≠ 0 := by simpa using hcl0
            have pos : (st1.chain_length - 1).toNat ≠ 0 := fun e => ne (UInt32.toNat_inj.mp (by simpa using e))
            have dec : (st1.chain_length - 1 - 1).toNat = (st1.chain_length - 1).toNat - 1 :=
              UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simp; omega))
            simp only [lmStep, hcl]
            rw [← hcl, dec]
            omega
      · have hcl0' : (st1.chain_length - 1 != 0) = false := by simpa using hcl0
        refine ⟨st1, h1, false, lmStep st1 (wfn pa (st1.cur_match.toNat &&& (d.w_size.toNat - 1))) (st1.chain_length - 1), h1, hrun, ?_, fun _ => hout, by simp⟩
        simp only [lmCond, bind_app, pure_app, M_ite_app, hb1', Bool.false_eq_true, ↓reduceIte, hrd, GT.gt, hgt, hcl0', lmStep]
    · have hng : ¬ limit < (wfn pa (st1.cur_match.toNat &&& (d.w_size.toNat - 1))).toUInt32 := by
        rw [UInt32.lt_iff_toNat_lt]; simpa using big
      refine ⟨st1, h1, false, lmStep st1 (wfn pa (st1.cur_match.toNat &&& (d.w_size.toNat - 1))) st1.chain_length, h1, hrun, ?_, fun _ => hout, by simp⟩
      simp only [lmCond, bind_app, pure_app, M_ite_app, hb1', Bool.false_eq_true, ↓reduceIte, hrd, GT.gt, hng, lmStep]


/-- The initial state of the loop satisfies the invariant, whatever `chain_length` and `nice_match` are. -/
theorem lm_init_safe {h0 : Heap} {sr wb pb : Nat} {d : DeflateState} {wa : Array UInt8} {pa : Array UInt16} {c : UInt32}
    (E : LMEnvS h0 sr d wb pb wa pa c) (cl : UInt32) (nm : Int32) :
    LMInvS h0 sr d wb pb wa pa c
      { cur_match := c, chain_length := cl, best_len := d.prev_length.toInt32, nice_match := nm,
        scan := Ptr.ref (BRef.blk wb) d.strstart.toNat,
        scan_end1 := bfn wa (d.strstart.toNat + d.prev_length.toNat - 1),
        scan_end := bfn wa (d.strstart.toNat + d.prev_length.toNat), brk := false } h0 := by
  have h31 : d.prev_length.toNat < 2 ^ 31 := by have := E.plle; omega
  refine ⟨d.match_start, d.prev_length.toNat, (hAt_self h0 sr d E.hd).symm, rfl, u32_toInt32_toInt _ h31, Nat.le_refl _,
    E.plle, fun _ => ⟨rfl, rfl⟩, ?_, Or.inl ⟨rfl, rfl⟩⟩
  exact Chain.start



theorem lmRest_safe {h0 : Heap} {sr wb pb : Nat} {d : DeflateState} {wa : Array UInt8} {pa : Array UInt16} {c : UInt32}
    (E : LMEnvS h0 sr d wb pb wa pa c) (L : UInt32)
    (hlimit : L.toNat = lmLimit d.strstart.toNat (d.w_size.toNat - 262)) (cl : UInt32) (nm : Int32) :
    ∃ (r : UInt32) (h' : Heap) (ms : UInt32) (best : Nat),
      lmRest sr L d c wb wa cl nm h0 = .ok (r, h') ∧
      r = UInt32.ofNat (lmResult best d.lookahead.toNat) ∧ h' = hAt h0 sr d ms ∧
      d.prev_length.toNat ≤ best ∧ best ≤ 258 ∧
      ((best = d.prev_length.toNat ∧ ms = d.match_start) ∨
       (d.prev_length.toNat < best ∧ SafeMatch d.strstart.toNat d.w_size.toNat ms.toNat best)) := by
  obtain ⟨st', h', hrun, ms, b, hh, hb, hpl, hb258, hgood⟩ :=
    lm_loop_safe E L hlimit _ h0 rfl (lm_init_safe E cl nm)
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
    · rw [hbu]; unfold lmResult; rw [ite_eq_left hle]
  · have hle' : ¬ st'.best_len.toUInt32 ≤ d.lookahead := by
      rw [UInt32.le_iff_toNat_le, hbn]; exact hle
    refine ⟨d.lookahead, hAt h0 sr d ms, ms, b, ?_, ?_, rfl, hpl, hb258, hgood⟩
    · simp only [lmRest, bind_app, pure_app, M_ite_app, hrun, hrd, hle', ite_false]
    · unfold lmResult; rw [ite_eq_right hle]; simp

/-- **longest_match, safety and specification.** Under `LMEnv` the call does not fault and only `match_start` changes
(the result heap is `hAt h0 sr d ms`). It returns `min(best, lookahead)` for some `best` with
`prev_length <= best <= 258`; either `best = prev_length` and `match_start` is unchanged, or `match_start` names a good
match of length `best`: before `strstart`, within `MAX_DIST`, and the window bytes agree on the first `best` bytes. -/
theorem longest_match_safe {h0 : Heap} {sr wb pb : Nat} {d : DeflateState} {wa : Array UInt8} {pa : Array UInt16} {c : UInt32}
    (E : LMEnvS h0 sr d wb pb wa pa c) :
    ∃ (r : UInt32) (h' : Heap) (ms : UInt32) (best : Nat),
      longest_match (some (.tab sr)) c h0 = .ok (r, h') ∧
      r = UInt32.ofNat (lmResult best d.lookahead.toNat) ∧ h' = hAt h0 sr d ms ∧
      d.prev_length.toNat ≤ best ∧ best ≤ 258 ∧
      ((best = d.prev_length.toNat ∧ ms = d.match_start) ∨
       (d.prev_length.toNat < best ∧ SafeMatch d.strstart.toNat d.w_size.toNat ms.toNat best)) := by
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
      rw [ite_eq_left hg, ite_eq_left hg', UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; rw [GT.gt, UInt32.lt_iff_toNat_lt] at hg; omega), hsub]
    · have hg' : ¬ d.strstart.toNat > d.w_size.toNat - 262 := by
        intro hh; apply hg; rw [GT.gt, UInt32.lt_iff_toNat_lt, hsub]; exact hh
      rw [ite_eq_right hg, ite_eq_right hg']; rfl
  have hLsame : (if d.strstart > d.w_size - MIN_LOOKAHEAD_u then d.strstart - (d.w_size - MIN_LOOKAHEAD_u) else 0) = L := hL.symm
  have key : ∀ (cl : UInt32) (nm : Int32), ∃ (r : UInt32) (h' : Heap) (ms : UInt32) (best : Nat),
      lmRest sr L d c wb wa cl nm h0 = .ok (r, h') ∧
      r = UInt32.ofNat (lmResult best d.lookahead.toNat) ∧ h' = hAt h0 sr d ms ∧
      d.prev_length.toNat ≤ best ∧ best ≤ 258 ∧
      ((best = d.prev_length.toNat ∧ ms = d.match_start) ∨
       (d.prev_length.toNat < best ∧ SafeMatch d.strstart.toNat d.w_size.toNat ms.toNat best)) :=
    fun cl nm => lmRest_safe E L hlimit cl nm
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
