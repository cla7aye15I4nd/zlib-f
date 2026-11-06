import ZlibF.Proof.«deflate.c.engine.lminner»
import ZlibF.Proof.«deflate.c.engine.chains»
import ZlibF.Proof.«deflate.c.engine.window»

/-!
# deflate.c, engine: one candidate of `longest_match`

The loop of `longest_match` visits the candidates on the hash chain. This module defines the environment (the
window block, the `prev` block, the size and position facts), the loop invariant `LMInv`, and proves that one
execution of the body `lm_body` does not fault and keeps the invariant.

**Environment.** The window block holds at least `2 * w_size` bytes and `strstart <= window_size - 262`; `prev` holds
`w_size` words; the first candidate `c` satisfies `1 <= c < strstart` and `strstart - c <= MAX_DIST`; every position
on the chain from `c` (while above `limit`) is in `[1, strstart)`, its `prev` entry is smaller, and it agrees with
`strstart` in the third byte whenever it agrees in the first two (this is what H gives after `INSERT_STRING`).

**Invariant.** `best_len` is `b` with `prev_length <= b <= 258`; `scan_end1` and `scan_end` are the window bytes
`strstart + b - 1` and `strstart + b`; `cur_match` lies on the chain; and either nothing has been found
(`b = prev_length`, `match_start` unchanged) or `match_start` names a good match of length `b`.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate

/-- A good match: before `ss`, within `MAX_DIST`, of length at most 258, and the bytes agree. -/
def GoodMatch (wa : Array UInt8) (ss ws m len : Nat) : Prop :=
  m < ss ∧ ss - m ≤ ws - 262 ∧ len ≤ 258 ∧ ∀ j, j < len → bfn wa (m + j) = bfn wa (ss + j)

/-- The heap once `match_start` of the state record `sr` was set to `ms`. -/
def hAt (h0 : Heap) (sr : Nat) (d : DeflateState) (ms : UInt32) : Heap :=
  { h0 with dstates := upd h0.dstates sr (some { d with match_start := ms }) }

structure LMEnv (h0 : Heap) (sr : Nat) (d : DeflateState) (wb pb : Nat) (wa : Array UInt8) (pa : Array UInt16)
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
    1 ≤ p ∧ p < d.strstart.toNat ∧ (wfn pa (p &&& (d.w_size.toNat - 1))).toNat < p ∧
    (bfn wa p = bfn wa d.strstart.toNat → bfn wa (p + 1) = bfn wa (d.strstart.toNat + 1) →
      bfn wa (p + 2) = bfn wa (d.strstart.toNat + 2))

def LMInv (h0 : Heap) (sr : Nat) (d : DeflateState) (wb pb : Nat) (wa : Array UInt8) (pa : Array UInt16)
    (c : UInt32) (st : LMState) (h : Heap) : Prop :=
  ∃ (ms : UInt32) (b : Nat), h = hAt h0 sr d ms ∧
    st.scan = .ref (.blk wb) d.strstart.toNat ∧ st.best_len.toInt = (b : Int) ∧ d.prev_length.toNat ≤ b ∧ b ≤ 258 ∧
    (st.brk = false → st.scan_end1 = bfn wa (d.strstart.toNat + b - 1) ∧ st.scan_end = bfn wa (d.strstart.toNat + b)) ∧
    Chain (wfn pa) (d.w_size.toNat - 1) (lmLimit d.strstart.toNat (d.w_size.toNat - 262)) c.toNat st.cur_match.toNat ∧
    ((b = d.prev_length.toNat ∧ ms = d.match_start) ∨
     (d.prev_length.toNat < b ∧ GoodMatch wa d.strstart.toNat d.w_size.toNat ms.toNat b))

/-! ## Integer helpers -/

theorem isub_ok (a b : Int32) (hr : -2147483648 ≤ a.toInt - b.toInt ∧ a.toInt - b.toInt ≤ 2147483647) :
    ∀ h, isub a b h = .ok (Int32.ofInt (a.toInt - b.toInt), h) := by
  intro h
  simp [isub, chk32, hr]

theorem getElem_bfn (a : Array UInt8) (j : Nat) (hj : j < a.size) : a[j] = bfn a j := by
  simp [bfn, Array.getD_eq_getD_getElem?, hj]

theorem load8_bfn {h : Heap} {wb : Nat} {wa : Array UInt8} (hb : h.bytes wb = some wa) {i : Nat}
    (hi : i < wa.size) : load8 (.ref (.blk wb) i) h = .ok (bfn wa i, h) := by
  have g : Space.get h (BRef.blk wb) = some wa := by simpa using hb
  have := Ptr.load_ok (h := h) (r := BRef.blk wb) (a := wa) (off := i) g hi
  unfold OkOn at this
  show (Ptr.ref (BRef.blk wb) i).load h = _
  rw [this, getElem_bfn _ _ hi]

theorem index8_bfn {h : Heap} {wb : Nat} {wa : Array UInt8} (hb : h.bytes wb = some wa) {off : Nat} {k : Int} {i : Nat}
    (hk : (off : Int) + k = i) (hi : i < wa.size) : index8 (.ref (.blk wb) off) k h = .ok (bfn wa i, h) := by
  have g : Space.get h (BRef.blk wb) = some wa := by simpa using hb
  have a1 := Ptr.add_ok (h := h) (r := BRef.blk wb) (a := wa) (off := off) (k := k) g (by omega) (by omega)
  have e : ((off : Int) + k).toNat = i := by omega
  rw [e] at a1
  have a2 : OkOn h (Ptr.load (Ptr.ref (BRef.blk wb) i)) (bfn wa i) := load8_bfn hb hi
  exact OkOn.bind (f := fun p => Ptr.load p) a1 a2

theorem LMEnv.dist {h0 : Heap} {sr : Nat} {d : DeflateState} {wb pb : Nat} {wa : Array UInt8} {pa : Array UInt16} {c : UInt32}
    (E : LMEnv h0 sr d wb pb wa pa c) :
    ∀ p, Chain (wfn pa) (d.w_size.toNat - 1) (lmLimit d.strstart.toNat (d.w_size.toNat - 262)) c.toNat p →
      p ≤ d.strstart.toNat → d.strstart.toNat - p ≤ d.w_size.toNat - 262 := by
  intro p hp hps
  induction hp with
  | start => exact E.cdist
  | step _ hq hlim _ => unfold lmLimit at hlim; split at hlim <;> omega

/-- **One candidate.** The body of the `longest_match` loop does not fault when the loop invariant holds and
`brk` is false, and the invariant holds afterwards; `cur_match`, `chain_length` and `nice_match` are not changed. -/
theorem lm_body_ok {h0 : Heap} {sr wb pb : Nat} {d : DeflateState} {wa : Array UInt8} {pa : Array UInt16} {c : UInt32}
    (E : LMEnv h0 sr d wb pb wa pa c) (st : LMState) {h : Heap} (hbrk : st.brk = false)
    (hI : LMInv h0 sr d wb pb wa pa c st h) :
    ∃ st' h', lm_body (some (.tab sr)) st h = .ok (st', h') ∧ LMInv h0 sr d wb pb wa pa c st' h' ∧
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
  obtain ⟨hcm1, hcmlt, hcmprev, hcm3⟩ := E.chain _ hch
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
  -- the candidate agrees on three bytes
  have T5 : bfn wa (st.cur_match.toNat + 2) = bfn wa (d.strstart.toNat + 2) := hcm3 T3 T4
  obtain ⟨r, hr⟩ : ∃ r, r = matchLen (bfn wa) d.strstart.toNat st.cur_match.toNat := ⟨_, rfl⟩
  obtain ⟨hr3, hr258⟩ := matchLen_bounds (bfn wa) d.strstart.toNat st.cur_match.toNat
  rw [← hr] at hr3 hr258
  have hcmss : st.cur_match.toNat ≤ d.strstart.toNat := by omega
  have hloop := lm_inner_loop (h := hAt h0 sr d ms) hbytes d.strstart.toNat st.cur_match.toNat hss hcmss T3.symm T4.symm T5.symm
  rw [← hr] at hloop
  have hagree : ∀ j, j < r → bfn wa (st.cur_match.toNat + j) = bfn wa (d.strstart.toNat + j) := by
    intro j hj
    rw [hr] at hj
    exact (matchLen_agree (bfn wa) d.strstart.toNat st.cur_match.toNat T3.symm T4.symm T5.symm j hj).symm
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
  have hgm : GoodMatch wa d.strstart.toNat d.w_size.toNat st.cur_match.toNat r :=
    ⟨hcmlt, hdist, hr258, hagree⟩
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
  have hgm' : GoodMatch wa d.strstart.toNat d.w_size.toNat st.cur_match.toNat r := hgm
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

end Zlib.Deflate.Engine.Proofs
