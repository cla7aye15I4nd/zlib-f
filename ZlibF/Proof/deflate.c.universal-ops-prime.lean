import ZlibF.Proof.«deflate.c.universal-ops-reset»
import ZlibF.Proof.«deflate.c.engine.output-state»
import ZlibF.Proof.«trees.c.bits»
import ZlibF.Proof.«deflate.c.prime»

/-!
# deflate.c: `deflatePrime` keeps the invariant (batch A, `operation_step`)

`deflatePrime(strm, bits, value)` on a stream that no `deflate` call has started
(`DeflateNotStarted`, the domain of the history). Three parts:

* the count check (`bits` outside 0..16 returns `Z_BUF_ERROR` with the heap unchanged);
* the compaction loop: when `pending_out ≠ pending_buf`, the `pending` bytes move to the start
  of `pending_buf`, a forward copy inside the block, then `pending_out = pending_buf`;
* the room check and the bit loop: at most `need = (bi_valid + bits) >> 3` bytes go to
  `pending_buf`, each iteration adds `min (16 - bi_valid, bits)` bits and calls `_tr_flush_bits`.

The bytes written lie in `pending_buf`, which also holds the symbol buffer. The invariant reads
the symbol bytes through the symbol ledger, so the proof needs no recorded symbols: the header
facts `HeaderInv` (beside `DInv`) give `sym_next = 0` in `INIT_STATE` and `GZIP_STATE`.
-/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Engine.Proofs
open Zlib.Deflate.Proofs
open Zlib.Trees.Proofs.Out (TreesBase TreesRun TreesInvAt BitsDiff setB)
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## The program in parts -/

/-- The test of the compaction loop. -/
def moveCond : UInt64 × BPtr × BPtr → M (Bool × (UInt64 × BPtr × BPtr)) :=
  fun (n, to, from_) => pure (n != 0, (n - 1, to, from_))

/-- The body of the compaction loop: `*to++ = *from++`. -/
def moveBody : UInt64 × BPtr × BPtr → M (UInt64 × BPtr × BPtr) :=
  fun (n, to, from_) => do
    store8 to (← load8 from_)
    pure (n, ← padd to 1, ← padd from_ 1)

/-- The bit loop body after `put` is chosen. -/
def bitRest (s : DeflateStatePtr) (d : DeflateState) (bits value put : Int32) : M (Int32 × Int32) := do
  let mask ← isub (← ishl 1 put.toInt) 1
  let sh ← ishl (value &&& mask) d.bi_valid.toInt
  wr s (fun d => { d with bi_buf := d.bi_buf ||| sh.toInt16.toUInt16 })
  let bv ← iadd d.bi_valid put
  wr s (fun d => { d with bi_valid := bv })
  Zlib.Trees.«_tr_flush_bits» s
  pure (← isub bits put, value >>> put)

/-- The body of the bit loop. -/
def bitBody (s : DeflateStatePtr) : Int32 × Int32 → M (Int32 × Int32) :=
  fun (bits, value) => do
    let d ← ldDeflateState s
    let put ← isub Buf_size d.bi_valid
    if put > bits then bitRest s d bits value bits else bitRest s d bits value put

/-- The test of the bit loop. -/
def bitCond : Int32 × Int32 → M (Bool × (Int32 × Int32)) :=
  fun (bits, value) => pure (bits != 0, (bits, value))

/-- The room check and the bit loop. -/
def primeTail (s : DeflateStatePtr) (bits value : Int32) : M Int32 := do
  let d ← ldDeflateState s
  let need : Int32 := (← iadd d.bi_valid bits) >>> 3
  if d.pending_buf_size - d.pending < need.toInt64.toUInt64 then return Z_BUF_ERROR
  let (_, _) ← cdoWhile (bitBody s) bitCond (bits, value)
  return Z_OK

set_option maxRecDepth 20000 in
theorem prime_split (strm : ZStreamPtr) (bits value : Int32) :
    deflatePrime strm bits value = (do
      if (← deflateStateCheck strm) != 0 then return Z_STREAM_ERROR
      let s ← castDeflateState (← zrd strm (·.state))
      if bits < 0 || bits > 16 then return Z_BUF_ERROR
      let d ← ldDeflateState s
      if d.pending_out != d.pending_buf then
        let _ ← cwhile moveCond moveBody (d.pending, d.pending_buf, d.pending_out)
        wr s (fun d => { d with pending_out := d.pending_buf })
      primeTail s bits value) := by
  delta deflatePrime primeTail moveCond moveBody bitCond bitBody bitRest
  exact rfl

/-! ## Loop rules -/

theorem prime_while_go {σ : Type} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (I : σ → Heap → Prop) (Q : σ → Heap → Prop) (μ : σ → Heap → Nat)
    (step : ∀ s h, I s h → ∃ c s1 h1, cond s h = .ok ((c, s1), h1) ∧
      (c = true → ∃ s2 h2, body s1 h1 = .ok (s2, h2) ∧ I s2 h2 ∧ μ s2 h2 < μ s h) ∧
      (c = false → Q s1 h1)) :
    ∀ n s h, I s h → μ s h < n → ∃ s' h', cwhile.go cond body n s h = .ok (s', h') ∧ Q s' h' := by
  intro n
  induction n with
  | zero => intro s h _ bound; omega
  | succ n ih =>
    intro s h inv bound
    obtain ⟨c, s1, h1, run, more, stop⟩ := step s h inv
    cases c with
    | false =>
      exact ⟨s1, h1, by simp [cwhile.go, run], stop rfl⟩
    | true =>
      obtain ⟨s2, h2, body2, inv2, less⟩ := more rfl
      obtain ⟨s', h', go, q⟩ := ih s2 h2 inv2 (by omega)
      exact ⟨s', h', by simp [cwhile.go, run, body2, go], q⟩

theorem prime_doWhile_go {σ : Type} {body : σ → M σ} {cond : σ → M (Bool × σ)}
    (I : σ → Heap → Prop) (Q : σ → Heap → Prop) (μ : σ → Heap → Nat)
    (step : ∀ s h, I s h → ∃ s1 h1 c s2 h2, body s h = .ok (s1, h1) ∧ cond s1 h1 = .ok ((c, s2), h2) ∧
      (c = true → I s2 h2 ∧ μ s2 h2 < μ s h) ∧ (c = false → Q s2 h2)) :
    ∀ n s h, I s h → μ s h < n → ∃ s' h', cdoWhile.go body cond n s h = .ok (s', h') ∧ Q s' h' := by
  intro n
  induction n with
  | zero => intro s h _ bound; omega
  | succ n ih =>
    intro s h inv bound
    obtain ⟨s1, h1, c, s2, h2, runB, runC, more, stop⟩ := step s h inv
    cases c with
    | false => exact ⟨s2, h2, by simp [cdoWhile.go, runB, runC], stop rfl⟩
    | true =>
      obtain ⟨inv2, less⟩ := more rfl
      obtain ⟨s', h', go, q⟩ := ih s2 h2 inv2 (by omega)
      exact ⟨s', h', by simp [cdoWhile.go, runB, runC, go], q⟩

/-! ## Machine arithmetic -/

theorem prime_chk32 {v : Int} (h1 : -2147483648 ≤ v) (h2 : v ≤ 2147483647) :
    Zlib.Deflate.chk32 v = pure (Int32.ofInt v) := by
  unfold Zlib.Deflate.chk32; simp [h1, h2]

theorem prime_ofInt {v : Int} (h1 : -2147483648 ≤ v) (h2 : v ≤ 2147483647) :
    (Int32.ofInt v).toInt = v := by
  rw [Int32.toInt_ofInt]; simp only [Int32.size, Int.bmod]; omega

theorem prime_pow (k : Nat) : (2 : Int) ^ k = ((2 ^ k : Nat) : Int) := by
  simp

theorem prime_ishl {a : Int32} {k : Nat} (hk : k < 32) (ha : 0 ≤ a.toInt)
    (hv : a.toInt * ((2 ^ k : Nat) : Int) ≤ 2147483647) :
    Zlib.Deflate.ishl a (k : Int) = pure (Int32.ofInt (a.toInt * ((2 ^ k : Nat) : Int))) := by
  unfold Zlib.Deflate.ishl
  have nonneg : (0 : Int) ≤ a.toInt * ((2 ^ k : Nat) : Int) := Int.mul_nonneg ha (Int.natCast_nonneg _)
  have c : 0 ≤ (k : Int) ∧ (k : Int) < 32 ∧ 0 ≤ a.toInt := ⟨by omega, by omega, ha⟩
  simp only [c, and_self, ↓reduceIte, Int.toNat_natCast, prime_pow]
  exact prime_chk32 (by omega) hv

theorem prime_isub_one (N : Nat) (h1 : 1 ≤ N) (h2 : N ≤ 65536) :
    isub (Int32.ofInt (N : Int)) 1 = pure (Int32.ofInt ((N : Int) - 1)) := by
  have one : (1 : Int32).toInt = 1 := by decide
  unfold isub
  rw [prime_ofInt (by omega) (by omega), one]
  exact prime_chk32 (by omega) (by omega)

/-- `value & ((1 << k) - 1)` is the low `k` bits of `value`. -/
theorem prime_and_mask (v : Int32) (k : Nat) (hk : k ≤ 16) :
    (v &&& Int32.ofInt (((2 ^ k : Nat) : Int) - 1)).toInt = ((v.toBitVec.toNat % 2 ^ k : Nat) : Int) := by
  have hk2 : 2 ^ k ≤ 2 ^ 16 := Nat.pow_le_pow_right (by decide) hk
  have pos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hm : (Int32.ofInt (((2 ^ k : Nat) : Int) - 1)).toBitVec.toNat = 2 ^ k - 1 := by
    simp only [Int32.toBitVec_ofInt, BitVec.toNat_ofInt]
    omega
  have hn : (v &&& Int32.ofInt (((2 ^ k : Nat) : Int) - 1)).toBitVec.toNat = v.toBitVec.toNat % 2 ^ k := by
    rw [Int32.toBitVec_and, BitVec.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod]
  have hlt : v.toBitVec.toNat % 2 ^ k < 2 ^ k := Nat.mod_lt _ pos
  rw [Int32.toInt, BitVec.toInt_eq_toNat_cond, hn]
  split <;> omega

/-- The low 16 bits of a small nonnegative `int`. -/
theorem prime_toU16 (n : Nat) (h1 : n < 2 ^ 16) :
    ((Int32.ofInt (n : Int)).toInt16.toUInt16).toNat = n := by
  simp only [Int32.toInt16, UInt16.toNat, Int32.toBitVec_ofInt]
  rw [BitVec.toNat_signExtend]
  simp
  omega

/-- The byte count `need` of the room check. -/
theorem prime_need : ∀ x : Fin 24,
    ((Int32.ofInt ((x.val : Nat) : Int)) >>> 3).toInt64.toUInt64 = UInt64.ofNat (x.val / 8) := by
  decide

/-! ## The compaction loop -/

/-- **The compaction loop** copies inside `pending_buf`: no fault, the block keeps its size. -/
theorem move_loop {h : Heap} {b off : Nat} {buf : Array UInt8} (get : h.bytes b = some buf)
    (ro : h.ro b = false) (n : UInt64) (fit : off + n.toNat ≤ buf.size) :
    ∃ st a, cwhile moveCond moveBody (n, (.ref (.blk b) 0 : BPtr), (.ref (.blk b) off : BPtr)) h =
      .ok (st, setB h b a) ∧ a.size = buf.size := by
  have key := prime_while_go (cond := moveCond) (body := moveBody)
    (fun st H => ∃ k a, H = setB h b a ∧ a.size = buf.size ∧ st.2.1 = .ref (.blk b) k ∧
      st.2.2 = .ref (.blk b) (off + k) ∧ st.1.toNat + k = n.toNat)
    (fun _ H => ∃ a, H = setB h b a ∧ a.size = buf.size) (fun st _ => st.1.toNat) ?_ fuel
    (n, .ref (.blk b) 0, .ref (.blk b) off) h
    ⟨0, buf, (Zlib.Trees.Proofs.Out.setB_self get).symm, rfl, rfl, by simp, by simp⟩
    (by have := n.toNat_lt; simp only [fuel]; omega)
  · obtain ⟨st, H, run, a, rfl, size⟩ := key
    exact ⟨st, a, run, size⟩
  · rintro ⟨m, to, fr⟩ H ⟨k, a, rfl, size, hto, hfr, count⟩
    simp only at hto hfr count
    subst hto hfr
    refine ⟨m != 0, (m - 1, .ref (.blk b) k, .ref (.blk b) (off + k)), setB h b a, rfl, ?_, ?_⟩
    · intro more
      have ne : m ≠ 0 := by simpa using more
      have m0 : m.toNat ≠ 0 := fun e => ne (UInt64.toNat_inj.mp (by rw [e]; rfl))
      have sub : (m - 1).toNat = m.toNat - 1 := by
        have := UInt64.toNat_sub_of_le m 1 (UInt64.le_iff_toNat_le.mpr (by simp; omega))
        simpa using this
      have getA : Space.get (setB h b a) (BRef.blk b) = some a := by
        show (setB h b a).bytes b = some a; simp
      have load : load8 (.ref (.blk b) (off + k)) (setB h b a) = .ok (a[off + k]'(by omega), setB h b a) :=
        Ptr.load_ok getA (by omega)
      have roA : Space.ro (setB h b a) (BRef.blk b) = false := by
        show (setB h b a).ro b = false; simpa using ro
      have store : store8 (.ref (.blk b) k) (a[off + k]'(by omega)) (setB h b a) =
          .ok ((), setB h b (a.set! k (a[off + k]'(by omega)))) := by
        rw [store8, Ptr.store_ok getA roA (by omega)]
        show Except.ok ((), setB (setB h b a) b _) = _
        rw [Zlib.Trees.Proofs.Out.setB_setB]
      have getB : Space.get (setB h b (a.set! k (a[off + k]'(by omega)))) (BRef.blk b) =
          some (a.set! k (a[off + k]'(by omega))) := by
        show (setB h b _).bytes b = some _; simp
      have sizeB : (a.set! k (a[off + k]'(by omega))).size = a.size := by simp
      have padd1 : padd (.ref (.blk b) k : BPtr) 1 (setB h b (a.set! k (a[off + k]'(by omega)))) =
          .ok (.ref (.blk b) (k + 1), setB h b (a.set! k (a[off + k]'(by omega)))) :=
        Ptr.add_nat_ok getB (by omega)
      have padd2 : padd (.ref (.blk b) (off + k) : BPtr) 1 (setB h b (a.set! k (a[off + k]'(by omega)))) =
          .ok (.ref (.blk b) (off + k + 1), setB h b (a.set! k (a[off + k]'(by omega)))) :=
        Ptr.add_nat_ok getB (by omega)
      refine ⟨(m - 1, .ref (.blk b) (k + 1), .ref (.blk b) (off + k + 1)),
        setB h b (a.set! k (a[off + k]'(by omega))), ?_, ⟨k + 1, _, rfl, by rw [sizeB, size], rfl,
          by simp only [Nat.add_assoc], by simp only; omega⟩, by simp only; omega⟩
      simp only [moveBody, bind_app, load, store, padd1, padd2, pure_app]
    · intro _
      exact ⟨a, rfl, size⟩

/-! ## The bit flush with exact room -/

/-- `bi_flush` when the bits fit in the bytes left in `pending_buf` (the room of `deflatePrime`'s
check, which may leave up to seven bits beyond the last byte). -/
theorem prime_flush {h : Heap} {id : Nat} {d : DeflateState} {b : Nat} {buf : Array UInt8}
    (hI : TreesInvAt h id d b buf)
    (hroom : 8 * d.pending.toNat + d.bi_valid.toInt.toNat ≤ 8 * buf.size + 7) :
    ∃ buf' d', Zlib.Trees.bi_flush (some (.tab id)) h =
        .ok ((), Zlib.Trees.Proofs.Out.setD (setB h b buf') id d') ∧
      TreesInvAt (Zlib.Trees.Proofs.Out.setD (setB h b buf') id d') id d' b buf' ∧
      0 ≤ d'.bi_valid.toInt ∧ d'.bi_valid.toInt < 8 ∧ buf'.size = buf.size ∧
      8 * d'.pending.toNat + d'.bi_valid.toInt.toNat = 8 * d.pending.toNat + d.bi_valid.toInt.toNat ∧
      (∃ p a v, d' = { d with pending := p, bi_buf := a, bi_valid := v }) := by
  obtain ⟨hb, hr⟩ := hI
  have hbl := hr.bi_lo
  have hbh := hr.bi_hi
  have hbb := hr.bi_buf
  have hp := hb.pending_small
  have hpsz := hb.psize
  have hple := hb.pending_le
  by_cases h16 : d.bi_valid.toInt = 16
  · have hroom2 : d.pending.toNat + 2 ≤ buf.size := by
      have : d.bi_valid.toInt.toNat = 16 := by omega
      omega
    have hp2 := Zlib.Trees.Proofs.Out.toNat_add_two_u64 hp
    have hbuf2 : ((buf.set! d.pending.toNat (d.bi_buf &&& 0xff).toUInt8).set! (d.pending.toNat + 1)
        (d.bi_buf >>> 8).toUInt8).size = buf.size := by simp
    refine ⟨_, _, Zlib.Trees.Proofs.Out.bi_flush_16 hb h16 hroom2, ?_, ?_, ?_, hbuf2, ?_, ⟨_, _, _, rfl⟩⟩
    · refine ⟨hb.step _ hbuf2 _ hb.wf rfl rfl rfl rfl rfl (by simp only []; rw [hp2]; omega), ?_⟩
      refine hr.with_bi _ rfl rfl rfl ?_ ?_ ?_ rfl rfl
      · show 0 ≤ (0 : Int32).toInt; decide
      · show (0 : Int32).toInt ≤ 16; decide
      · show (0 : UInt16).toNat < 2 ^ (0 : Int32).toInt.toNat; decide
    · show 0 ≤ (0 : Int32).toInt; decide
    · show (0 : Int32).toInt < 8; decide
    · show 8 * (d.pending + 2).toNat + (0 : Int32).toInt.toNat = _
      rw [hp2]
      have : (0 : Int32).toInt.toNat = 0 := by decide
      rw [this]; omega
  · by_cases h8 : 8 ≤ d.bi_valid.toInt
    · have hlt16 : d.bi_valid.toInt < 16 := by omega
      have hroom1 : d.pending.toNat + 1 ≤ buf.size := by
        have : 8 ≤ d.bi_valid.toInt.toNat := by omega
        omega
      have hp1 := Zlib.Trees.Proofs.Out.toNat_add_one_u64 hp
      have hbuf1 : (buf.set! d.pending.toNat d.bi_buf.toUInt8).size = buf.size := by simp
      have hnv : (Int32.ofInt (d.bi_valid.toInt - 8)).toInt = d.bi_valid.toInt - 8 :=
        prime_ofInt (by omega) (by omega)
      refine ⟨_, _, Zlib.Trees.Proofs.Out.bi_flush_mid hb h8 hlt16 hroom1, ?_, ?_, ?_, hbuf1, ?_,
        ⟨_, _, _, rfl⟩⟩
      · refine ⟨hb.step _ hbuf1 _ hb.wf rfl rfl rfl rfl rfl (by simp only []; rw [hp1]; omega), ?_⟩
        refine hr.with_bi _ rfl rfl rfl ?_ ?_ ?_ rfl rfl
        · show 0 ≤ (Int32.ofInt _).toInt; rw [hnv]; omega
        · show (Int32.ofInt _).toInt ≤ 16; rw [hnv]; omega
        · show (d.bi_buf >>> 8).toNat < 2 ^ (Int32.ofInt _).toInt.toNat
          rw [hnv, Zlib.Trees.Proofs.Out.u16_shr8_toNat]
          have := Zlib.Trees.Proofs.Out.natBits_shr_lt d.bi_buf.toNat d.bi_valid.toInt.toNat 8 hbb (by omega)
          rw [Nat.shiftRight_eq_div_pow] at this
          have e : (d.bi_valid.toInt - 8).toNat = d.bi_valid.toInt.toNat - 8 := by omega
          rw [e]; simpa using this
      · show 0 ≤ (Int32.ofInt _).toInt; rw [hnv]; omega
      · show (Int32.ofInt _).toInt < 8; rw [hnv]; omega
      · show 8 * (d.pending + 1).toNat + (Int32.ofInt (d.bi_valid.toInt - 8)).toInt.toNat = _
        rw [hp1, hnv]; omega
    · have hlt8 : d.bi_valid.toInt < 8 := by omega
      refine ⟨buf, d, ?_, ?_, hbl, hlt8, rfl, rfl, ⟨_, _, _, rfl⟩⟩
      · rw [Zlib.Trees.Proofs.Out.setB_self hb.bytes, Zlib.Trees.Proofs.Out.setD_self hb.dstate]
        exact Zlib.Trees.Proofs.Out.bi_flush_low hb.dstate hlt8
      · rw [Zlib.Trees.Proofs.Out.setB_self hb.bytes, Zlib.Trees.Proofs.Out.setD_self hb.dstate]
        exact ⟨hb, hr⟩

/-! ## The bit loop -/

/-- The state of the bit loop: only `pending_buf`, `pending` and the bit fields have changed
since `H1`, and the bits still to send fit in the room the check left. -/
def BitState (H1 : Heap) (ds b : Nat) (d1 : DeflateState) (S : Nat) (st : Int32 × Int32) (H : Heap) : Prop :=
  ∃ bf e, H = setD (setB H1 b bf) ds e ∧ TreesInvAt H ds e b bf ∧ bf.size = S ∧
    (∃ p w v u, e = { d1 with pending := p, bi_buf := w, bi_valid := v, bi_used := u }) ∧
    0 ≤ e.bi_valid.toInt ∧ e.bi_valid.toInt ≤ 7 ∧ 0 ≤ st.1.toInt ∧ st.1.toInt ≤ 16 ∧
    8 * e.pending.toNat + e.bi_valid.toInt.toNat + st.1.toInt.toNat ≤ 8 * S + 7

/-- The end of the bit loop. -/
def BitEnd (H1 : Heap) (ds b : Nat) (d1 : DeflateState) (S : Nat) (_st : Int32 × Int32) (H : Heap) : Prop :=
  ∃ bf e, H = setD (setB H1 b bf) ds e ∧ TreesInvAt H ds e b bf ∧ bf.size = S ∧
    (∃ p w v u, e = { d1 with pending := p, bi_buf := w, bi_valid := v, bi_used := u }) ∧
    e.bi_valid.toInt ≤ 7

theorem setD_setB_twice (H : Heap) (b ds : Nat) (a a' : Array UInt8) (e e' : DeflateState) :
    setD (setB (setD (setB H b a) ds e) b a') ds e' = setD (setB H b a') ds e' := by
  simp only [setD, setB, upd_upd]

theorem heap_conv (H1 : Heap) (b ds : Nat) (bf : Array UInt8) (e e2 : DeflateState) :
    Zlib.Trees.Proofs.Out.setD (setD (setB H1 b bf) ds e) ds e2 = setD (setB H1 b bf) ds e2 := by
  simp only [Zlib.Trees.Proofs.Out.setD, Zlib.Deflate.Spec.setD, upd_upd]

/-- One iteration of the bit loop, once `put` is chosen. -/
theorem bit_rest {H1 H : Heap} {ds b S : Nat} {d1 e : DeflateState} {bf : Array UInt8}
    (eq : H = setD (setB H1 b bf) ds e) (trees : TreesInvAt H ds e b bf) (size : bf.size = S)
    (fields : ∃ p w v u, e = { d1 with pending := p, bi_buf := w, bi_valid := v, bi_used := u })
    (v0 : 0 ≤ e.bi_valid.toInt) (v7 : e.bi_valid.toInt ≤ 7)
    (bits value put : Int32) (b0 : 0 ≤ bits.toInt) (b16 : bits.toInt ≤ 16)
    (p0 : 0 ≤ put.toInt) (pBits : put.toInt ≤ bits.toInt) (pRoom : put.toInt ≤ 16 - e.bi_valid.toInt)
    (pMin : put.toInt = bits.toInt ∨ put.toInt = 16 - e.bi_valid.toInt)
    (room : 8 * e.pending.toNat + e.bi_valid.toInt.toNat + bits.toInt.toNat ≤ 8 * S + 7) :
    ∃ st H', bitRest (some (.tab ds)) e bits value put H = .ok (st, H') ∧
      (∃ c, bitCond st H' = .ok ((c, st), H') ∧
        (c = true → BitState H1 ds b d1 S st H' ∧ st.1.toInt.toNat < bits.toInt.toNat) ∧
        (c = false → BitEnd H1 ds b d1 S st H')) := by
  subst eq
  obtain ⟨p, w, v, u, rfl⟩ := fields
  have hs := trees.base.dstate
  -- the arithmetic
  obtain ⟨k, hk⟩ : ∃ k : Nat, put.toInt = (k : Int) := ⟨put.toInt.toNat, by omega⟩
  simp only at v0 v7 pRoom pMin room
  obtain ⟨j, hj⟩ : ∃ j : Nat, v.toInt = (j : Int) := ⟨v.toInt.toNat, by omega⟩
  have k16 : k ≤ 16 := by omega
  have kj : k + j ≤ 16 := by omega
  have pk : 2 ^ k ≤ 2 ^ 16 := Nat.pow_le_pow_right (by decide) k16
  have pkj : 2 ^ (k + j) ≤ 2 ^ 16 := Nat.pow_le_pow_right (by decide) kj
  have one : (1 : Int32).toInt = 1 := by decide
  have shl1 : Zlib.Deflate.ishl 1 put.toInt = pure (Int32.ofInt (((2 ^ k : Nat) : Int))) := by
    rw [hk, prime_ishl (by omega) (by rw [one]; omega) (by rw [one]; omega), one, Int.one_mul]
  have sub1 : isub (Int32.ofInt (((2 ^ k : Nat) : Int))) 1 =
      pure (Int32.ofInt (((2 ^ k : Nat) : Int) - 1)) := by
    exact prime_isub_one _ (Nat.two_pow_pos k) pk
  have xlt : value.toBitVec.toNat % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
  have hx := prime_and_mask value k k16
  have xj : (value.toBitVec.toNat % 2 ^ k) * 2 ^ j < 2 ^ (k + j) :=
    Zlib.Trees.Proofs.Out.pow_mul_lt _ k j xlt
  have hxle : (((value.toBitVec.toNat % 2 ^ k) * 2 ^ j : Nat) : Int) ≤ 2147483647 := by
    have small : (value.toBitVec.toNat % 2 ^ k) * 2 ^ j ≤ 2147483647 := by omega
    generalize (value.toBitVec.toNat % 2 ^ k) * 2 ^ j = X at small ⊢
    omega
  have shl2 : Zlib.Deflate.ishl (value &&& Int32.ofInt (((2 ^ k : Nat) : Int) - 1)) v.toInt =
      pure (Int32.ofInt ((((value.toBitVec.toNat % 2 ^ k) * 2 ^ j : Nat) : Int))) := by
    rw [hj, prime_ishl (by omega) (by rw [hx]; omega) (by rw [hx, ← Int.natCast_mul]; exact hxle), hx,
      ← Int.natCast_mul]
  have word : ((Int32.ofInt ((((value.toBitVec.toNat % 2 ^ k) * 2 ^ j : Nat) : Int))).toInt16.toUInt16).toNat =
      (value.toBitVec.toNat % 2 ^ k) * 2 ^ j :=
    prime_toU16 _ (by omega)
  have add : iadd v put = pure (Int32.ofInt (v.toInt + put.toInt)) := by
    unfold iadd; exact prime_chk32 (by omega) (by omega)
  have subBits : isub bits put = pure (Int32.ofInt (bits.toInt - put.toInt)) := by
    unfold isub; exact prime_chk32 (by omega) (by omega)
  have nv : (Int32.ofInt (v.toInt + put.toInt)).toInt = (j : Int) + k := by
    rw [prime_ofInt (by omega) (by omega)]; omega
  have nb : (Int32.ofInt (bits.toInt - put.toInt)).toInt = bits.toInt - put.toInt :=
    prime_ofInt (by omega) (by omega)
  -- the state before the flush
  let e2 : DeflateState := { d1 with pending := p, bi_buf := w ||| (Int32.ofInt ((((value.toBitVec.toNat % 2 ^ k) * 2 ^ j : Nat) : Int))).toInt16.toUInt16, bi_valid := Int32.ofInt (v.toInt + put.toInt), bi_used := u }
  have e2p : e2.pending = p := rfl
  have e2v : e2.bi_valid = Int32.ofInt (v.toInt + put.toInt) := rfl
  have trees2 : TreesInvAt (setD (setB H1 b bf) ds e2) ds e2 b bf := by
    have base := trees.base.stepD e2 trees.base.wf rfl rfl rfl rfl rfl trees.base.pending_le
    rw [heap_conv] at base
    refine ⟨base, ?_⟩
    refine trees.run.with_bi e2 rfl rfl rfl ?_ ?_ ?_ rfl rfl
    · show 0 ≤ (Int32.ofInt (v.toInt + put.toInt)).toInt; rw [nv]; omega
    · show (Int32.ofInt (v.toInt + put.toInt)).toInt ≤ 16; rw [nv]; omega
    · show (w ||| (Int32.ofInt ((((value.toBitVec.toNat % 2 ^ k) * 2 ^ j : Nat) : Int))).toInt16.toUInt16).toNat <
        2 ^ (Int32.ofInt (v.toInt + put.toInt)).toInt.toNat
      have wlt : w.toNat < 2 ^ j := by
        have := trees.run.bi_buf
        simp only at this
        rw [hj] at this; simpa using this
      rw [nv, UInt16.toNat_or, word]
      have e' : ((j : Int) + (k : Int)).toNat = k + j := by omega
      rw [e']
      apply Nat.or_lt_two_pow
      · exact Nat.lt_of_lt_of_le wlt (Nat.pow_le_pow_right (by decide) (by omega))
      · exact xj
  obtain ⟨bf', e', flush, trees', lo', hi', size', count', ⟨p', w', v', rfl⟩⟩ :=
    prime_flush trees2 (by
      show 8 * p.toNat + (Int32.ofInt (v.toInt + put.toInt)).toInt.toNat ≤ 8 * bf.size + 7
      rw [nv, size]; omega)
  refine ⟨(Int32.ofInt (bits.toInt - put.toInt), value >>> put),
    Zlib.Trees.Proofs.Out.setD (setB (setD (setB H1 b bf) ds e2) b bf') ds
      { e2 with pending := p', bi_buf := w', bi_valid := v' }, ?_, ?_⟩
  · simp only [bitRest, bind_app, shl1, sub1, shl2, pure_app, wrD_eq, hs, add, subBits,
      setD_dstates_same, setD_setD]
    rw [show Zlib.Trees.«_tr_flush_bits» (some (.tab ds)) = Zlib.Trees.bi_flush (some (.tab ds)) from rfl]
    rw [flush]
  · refine ⟨_, rfl, ?_, ?_⟩
    · intro more
      have nz : Int32.ofInt (bits.toInt - put.toInt) ≠ 0 := by simpa using more
      have nzi : bits.toInt - put.toInt ≠ 0 := fun z => nz (by rw [z]; rfl)
      refine ⟨⟨bf', _, setD_setB_twice H1 b ds bf bf' e2 _, trees', by rw [size', size],
        ⟨_, _, _, u, rfl⟩, lo', by omega, by simp only; rw [nb]; omega, by simp only; rw [nb]; omega, ?_⟩, ?_⟩
      · have c' := count'
        simp only [e2p, e2v] at c'
        rw [nv] at c'
        simp only
        rw [nb]
        omega
      · simp only; rw [nb]
        rcases pMin with m | m <;> omega
    · intro _
      exact ⟨bf', _, setD_setB_twice H1 b ds bf bf' e2 _, trees', by rw [size', size], ⟨_, _, _, u, rfl⟩,
        by omega⟩

/-- One iteration of the bit loop: `put = min (16 - bi_valid, bits)`. -/
theorem bit_body {H1 H : Heap} {ds b S : Nat} {d1 : DeflateState} (st : Int32 × Int32)
    (state : BitState H1 ds b d1 S st H) :
    ∃ st1 H', bitBody (some (.tab ds)) st H = .ok (st1, H') ∧
      (∃ c, bitCond st1 H' = .ok ((c, st1), H') ∧
        (c = true → BitState H1 ds b d1 S st1 H' ∧ st1.1.toInt.toNat < st.1.toInt.toNat) ∧
        (c = false → BitEnd H1 ds b d1 S st1 H')) := by
  obtain ⟨bits, value⟩ := st
  obtain ⟨bf, e, eq, trees, size, fields, v0, v7, b0, b16, room⟩ := state
  simp only at b0 b16 room
  have hs : H.dstates ds = some e := trees.base.dstate
  have sub : isub Buf_size e.bi_valid = pure (Int32.ofInt (16 - e.bi_valid.toInt)) := by
    unfold isub
    rw [show Buf_size.toInt = 16 from by decide]
    exact prime_chk32 (by omega) (by omega)
  have pv : (Int32.ofInt (16 - e.bi_valid.toInt)).toInt = 16 - e.bi_valid.toInt :=
    prime_ofInt (by omega) (by omega)
  by_cases gt : Int32.ofInt (16 - e.bi_valid.toInt) > bits
  · have gt' : bits.toInt < 16 - e.bi_valid.toInt := by
      have := Int32.lt_iff_toInt_lt.mp gt; omega
    obtain ⟨st1, H', run, c, crun, more, stop⟩ := bit_rest eq trees size fields v0 v7 bits value bits b0 b16
      b0 (Int.le_refl _) (by omega) (Or.inl rfl) room
    refine ⟨st1, H', ?_, c, crun, more, stop⟩
    simp only [bitBody, bind_app, ldD_eq, hs, sub, pure_app, gt, ↓reduceIte]
    exact run
  · have le' : 16 - e.bi_valid.toInt ≤ bits.toInt := by
      have : ¬ bits.toInt < (Int32.ofInt (16 - e.bi_valid.toInt)).toInt :=
        fun lt => gt (Int32.lt_iff_toInt_lt.mpr lt)
      omega
    obtain ⟨st1, H', run, c, crun, more, stop⟩ := bit_rest eq trees size fields v0 v7 bits value
      (Int32.ofInt (16 - e.bi_valid.toInt)) b0 b16 (by omega) (by omega) (by omega) (Or.inr pv) room
    refine ⟨st1, H', ?_, c, crun, more, stop⟩
    simp only [bitBody, bind_app, ldD_eq, hs, sub, pure_app, gt, ↓reduceIte]
    exact run

/-- **The bit loop** ends, with at most seven bits held. -/
theorem bit_loop {H1 H : Heap} {ds b S : Nat} {d1 : DeflateState} (st : Int32 × Int32)
    (state : BitState H1 ds b d1 S st H) :
    ∃ st' H', cdoWhile (bitBody (some (.tab ds))) bitCond st H = .ok (st', H') ∧
      BitEnd H1 ds b d1 S st' H' := by
  have bound : st.1.toInt.toNat < fuel := by
    obtain ⟨_, _, _, _, _, _, _, _, _, b16, _⟩ := state
    simp only [fuel]; omega
  refine prime_doWhile_go (BitState H1 ds b d1 S) (BitEnd H1 ds b d1 S) (fun st _ => st.1.toInt.toNat) ?_
    fuel st H state bound
  intro st H state
  obtain ⟨st1, H', run, c, crun, more, stop⟩ := bit_body st state
  exact ⟨st1, H', c, st1, H', run, crun, more, stop⟩

theorem self_heap {H : Heap} {b ds : Nat} {a : Array UInt8} {d : DeflateState}
    (hb : H.bytes b = some a) (hs : H.dstates ds = some d) : setD (setB H b a) ds d = H := by
  show Zlib.Trees.Proofs.Out.setD (setB H b a) ds d = H
  rw [Zlib.Trees.Proofs.Out.setD_self (by simpa using hs), Zlib.Trees.Proofs.Out.setB_self hb]

/-- **The room check and the bit loop.** -/
theorem prime_tail {H1 : Heap} {ds b : Nat} {d1 : DeflateState} {a : Array UInt8} (bits value : Int32)
    (trees : TreesInvAt H1 ds d1 b a) (b0 : 0 ≤ bits.toInt) (b16 : bits.toInt ≤ 16)
    (v0 : 0 ≤ d1.bi_valid.toInt) (v7 : d1.bi_valid.toInt ≤ 7) :
    ∃ rc bf e, primeTail (some (.tab ds)) bits value H1 = .ok (rc, setD (setB H1 b bf) ds e) ∧
      TreesInvAt (setD (setB H1 b bf) ds e) ds e b bf ∧ bf.size = a.size ∧
      (∃ p w v u, e = { d1 with pending := p, bi_buf := w, bi_valid := v, bi_used := u }) ∧
      e.bi_valid.toInt ≤ 7 := by
  have hs : H1.dstates ds = some d1 := trees.base.dstate
  have self := self_heap trees.base.bytes hs
  have add : iadd d1.bi_valid bits = pure (Int32.ofInt (d1.bi_valid.toInt + bits.toInt)) := by
    unfold iadd; exact prime_chk32 (by omega) (by omega)
  let x : Fin 24 := ⟨(d1.bi_valid.toInt + bits.toInt).toNat, by omega⟩
  have xeq : d1.bi_valid.toInt + bits.toInt = ((x.val : Nat) : Int) := by simp only [x]; omega
  have need : ((Int32.ofInt (d1.bi_valid.toInt + bits.toInt)) >>> 3).toInt64.toUInt64 = UInt64.ofNat (x.val / 8) := by
    rw [xeq]; exact prime_need x
  have ple : d1.pending.toNat ≤ d1.pending_buf_size.toNat := trees.base.pending_le
  have hsub : (d1.pending_buf_size - d1.pending).toNat = d1.pending_buf_size.toNat - d1.pending.toNat :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr ple)
  have hof : (UInt64.ofNat (x.val / 8)).toNat = x.val / 8 := by
    simp; omega
  by_cases chk : d1.pending_buf_size - d1.pending < UInt64.ofNat (x.val / 8)
  · refine ⟨Z_BUF_ERROR, a, d1, ?_, by rw [self]; exact trees, rfl, ⟨_, _, _, _, rfl⟩, v7⟩
    rw [self]
    simp only [primeTail, bind_app, ldD_eq, hs, add, pure_app, need, chk, ↓reduceIte]
  · have fits : x.val / 8 ≤ d1.pending_buf_size.toNat - d1.pending.toNat := by
      have : ¬ (d1.pending_buf_size - d1.pending).toNat < (UInt64.ofNat (x.val / 8)).toNat :=
        fun lt => chk (UInt64.lt_iff_toNat_lt.mpr lt)
      rw [hsub, hof] at this; omega
    have state : BitState H1 ds b d1 a.size (bits, value) H1 := by
      refine ⟨a, d1, self.symm, by first | exact trees | (rw [self]; exact trees), rfl, ⟨_, _, _, _, rfl⟩, v0, v7, b0, b16, ?_⟩
      have := trees.base.psize
      have xv : (x.val : Int) = d1.bi_valid.toInt + bits.toInt := by omega
      simp only
      omega
    obtain ⟨st', H', loop, bf, e, rfl, trees', size', fields', v7'⟩ := bit_loop (bits, value) state
    refine ⟨Z_OK, bf, e, ?_, trees', size', fields', v7'⟩
    simp only [primeTail, bind_app, ldD_eq, hs, add, pure_app, need, chk, ↓reduceIte, loop]

/-! ## The invariant afterwards -/

/-- Compaction keeps `DGood`: the pending bytes move inside `pending_buf` and `pending_out` returns
to its start. -/
theorem move_good {h : Heap} {r : ZStreamRef} {ds b : Nat} {z : ZStream} {d : DeflateState}
    {buf a : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d b buf) (size : a.size = buf.size) :
    DGood (setD (setB h b a) ds { d with pending_out := d.pending_buf }) r ds z
        { d with pending_out := d.pending_buf } ∧
      TreesInvAt (setD (setB h b a) ds { d with pending_out := d.pending_buf }) ds
        { d with pending_out := d.pending_buf } b a := by
  let d1 : DeflateState := { d with pending_out := d.pending_buf }
  let copied := setB h b a
  have goodB : DGood copied r ds z d := good.bytes_set b a buf trees.base.bytes size
  obtain ⟨w, p, q, b', blocks⟩ := goodB.inv.blocks
  have blocksA : DBlocks copied d1 w p q b' :=
    { blocks with pout := ⟨0, blocks.pbuf, by simpa using trees.base.pending_le⟩ }
  have inv : DStInv copied ds d1 := { goodB.inv with blocks := ⟨w, p, q, b', blocksA⟩ }
  have treesA : TreesInvAt (setD copied ds d1) ds d1 b a :=
    ⟨trees.base.step a size d1 trees.base.wf rfl rfl rfl rfl rfl trees.base.pending_le,
      trees.run.with_bi d1 rfl rfl rfl trees.run.bi_lo trees.run.bi_hi trees.run.bi_buf rfl rfl⟩
  have shape := shape_setD goodB.live.hs d1
  refine ⟨⟨?_, DStInv.congr (h := copied) (h' := setD copied ds d1) rfl rfl rfl rfl inv,
    shape.uniq goodB.uniq, shape.fresh rfl goodB.fresh, ⟨d1, b, a, treesA⟩⟩, treesA⟩
  exact ⟨by simpa only [ZStreamRef.get_setD] using goodB.live.hz, by simp, good.live.zst,
    good.live.back, good.live.status, good.live.zalloc, good.live.zfree⟩

/-- The frame of a run that writes `pending_buf` and the state record. -/
theorem prime_frame {h : Heap} {r : ZStreamRef} {ds b : Nat} {d e : DeflateState} {bf : Array UInt8}
    (pb : d.pending_buf = .ref (.blk b) 0) :
    Frame h (setD (setB h b bf) ds e) (fun x => StreamRoot r x ∨ DeflateOwned ds d x) := by
  refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun x _ nc => ?_⟩
  have hi : x ≠ ds := fun eq => nc (Or.inr (Or.inl eq))
  have hb : x ≠ b := fun eq => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [pb, eq]))))))
  simp [setD, setB, upd_ne, hi, hb]

/-- **`deflatePrime` keeps the invariant** on a stream not yet started. The header facts
`HeaderInv` (beside `DInv`) give that such a stream has recorded no symbols. -/
theorem step_prime {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (bits value : Int32) (notStarted : DeflateNotStarted h r)
    (header : HeaderInv d) :
    StepOk h r (.deflatePrime (some r) bits value) := by
  have good := inv.good
  have hL := good.live
  by_cases range : bits.toInt < 0 ∨ 16 < bits.toInt
  · exact step_unchanged inv _ (heapCall_run (deflatePrime_invalid_count hL bits value range)) rfl
  have b0 : 0 ≤ bits.toInt := by omega
  have b16 : bits.toInt ≤ 16 := by omega
  have symZero : d.sym_next = 0 := by
    obtain ⟨z', i, s, get, zst, hs', st⟩ := notStarted
    have zz : z' = z := Option.some.inj (get.symm.trans hL.hz)
    subst zz
    rw [hL.zst] at zst
    cases zst
    have ss : s = d := Option.some.inj (hs'.symm.trans hL.hs)
    subst ss
    exact header.empty (st.elim Or.inl (fun g => Or.inr (Or.inl g)))
  obtain ⟨d0, b, buf, trees⟩ := good.trees
  have e0 : d0 = d := Option.some.inj (trees.base.dstate.symm.trans hL.hs)
  rw [e0] at trees
  obtain ⟨w, p, q, b', blocks⟩ := good.inv.blocks
  have bb : b = b' := by
    have := blocks.pbuf; rw [trees.base.pbuf] at this; cases this; rfl
  subst bb
  obtain ⟨off, pout, offFit⟩ := blocks.pout
  have v0 : 0 ≤ d.bi_valid.toInt := good.inv.bits.1
  have v7 : d.bi_valid.toInt ≤ 7 := inv.shape.biValid
  have notRange : (bits < 0 || bits > 16) = false := by
    have l1 : ¬ bits < 0 := fun lt => by have := Int32.lt_iff_toInt_lt.mp lt; simp at this; omega
    have l2 : ¬ bits > 16 := fun lt => by have := Int32.lt_iff_toInt_lt.mp lt; simp at this; omega
    simp [l1, l2]
  -- the compaction
  have move : ∃ a, deflatePrime (some r) bits value h =
      primeTail (some (.tab ds)) bits value (setD (setB h b a) ds { d with pending_out := d.pending_buf }) ∧
      a.size = buf.size := by
    by_cases mv : d.pending_out = d.pending_buf
    · refine ⟨buf, ?_, rfl⟩
      have same : ({ d with pending_out := d.pending_buf } : DeflateState) = d := by
        cases d; simp only at mv; subst mv; rfl
      rw [same, self_heap trees.base.bytes hL.hs, prime_split]
      simp [stateCheck_live hL, zrd_eq, hL.hz, hL.zst, castD, ldD_eq, hL.hs, notRange, mv]
    · have psz := trees.base.psize
      obtain ⟨st, a, loop, size⟩ := move_loop trees.base.bytes trees.base.rw d.pending (off := off)
        (by have := trees.base.psize; omega)
      have loop' : cwhile moveCond moveBody (d.pending, d.pending_buf, d.pending_out) h = .ok (st, setB h b a) := by
        rw [trees.base.pbuf, pout]; exact loop
      refine ⟨a, ?_, size⟩
      rw [prime_split]
      simp [stateCheck_live hL, zrd_eq, hL.hz, hL.zst, castD, ldD_eq, hL.hs, notRange, mv, loop', wrD_eq]
  obtain ⟨a, runMove, sizeA⟩ := move
  obtain ⟨good1, trees1⟩ := move_good good trees sizeA
  obtain ⟨rc, bf, e, runTail, trees2, size2, ⟨p2, w2, v2, u2, rfl⟩, v7'⟩ :=
    prime_tail bits value trees1 b0 b16 v0 v7
  have heapEq : setD (setB (setD (setB h b a) ds { d with pending_out := d.pending_buf }) b bf) ds
      { d with pending_out := d.pending_buf, pending := p2, bi_buf := w2, bi_valid := v2, bi_used := u2 } =
      setD (setB h b bf) ds
      { d with pending_out := d.pending_buf, pending := p2, bi_buf := w2, bi_valid := v2, bi_used := u2 } :=
    setD_setB_twice h b ds a bf _ _
  have good2 := output_bits_good good1 rfl
    (show (setD (setB h b a) ds { d with pending_out := d.pending_buf }).bytes b = some a by simp [setD, setB])
    (by rw [size2, sizeA]) ⟨p2, w2, v2, u2, rfl⟩ trees2
  rw [heapEq] at good2 runTail
  have hb : (setD (setB h b bf) ds { d with pending_out := d.pending_buf, pending := p2, bi_buf := w2, bi_valid := v2, bi_used := u2 }).bytes b = some bf := by simp [setD, setB]
  have winSame : ∀ x, d.window = .ref (.blk x) 0 →
      (setD (setB h b bf) ds { d with pending_out := d.pending_buf, pending := p2, bi_buf := w2, bi_valid := v2, bi_used := u2 }).bytes x = h.bytes x := by
    intro x ex
    have xw : x = w := by rw [blocks.win] at ex; cases ex; rfl
    subst xw
    have : x ≠ b := blocks.wb
    simp [setD, setB, upd_ne, this]
  have inv' : DInv (setD (setB h b bf) ds { d with pending_out := d.pending_buf, pending := p2, bi_buf := w2, bi_valid := v2, bi_used := u2 }) r ds z
      { d with pending_out := d.pending_buf, pending := p2, bi_buf := w2, bi_valid := v2, bi_used := u2 } := by
    refine ⟨good2, inv.alloc, by unfold LibraryGlobals at *; exact inv.globals,
      { inv.shape with biValid := v7', cursor := fun _ => rfl }, ⟨fun zero => ?_, fun one => ?_, fun s2 s3 three => ?_⟩,
      ⟨⟨[], ⟨b, bf, trees.base.pbuf, hb, ?_⟩, by simp⟩, ⟨inv.symbols.clear.bl, inv.symbols.clear.opt,
        inv.symbols.clear.fixed⟩, fun _ _ _ nz => absurd symZero nz⟩⟩
    · obtain ⟨w', p', q', wa, pa, qa, ew, ep, eq, hw, hp, hq, H⟩ := inv.hashing.chains zero
      exact ⟨w', p', q', wa, pa, qa, ew, ep, eq, (winSame w' ew).trans hw, hp, hq, H⟩
    · obtain ⟨w', p', q', wa, pa, qa, ew, ep, eq, hw, hp, hq, H⟩ := inv.hashing.slid one
      exact ⟨w', p', q', wa, pa, qa, ew, ep, eq, (winSame w' ew).trans hw, hp, hq, H⟩
    · obtain ⟨w', wa, ew, hw, form⟩ := inv.hashing.rolling s2 s3 three
      exact ⟨w', wa, ew, (winSame w' ew).trans hw, form⟩
    · obtain ⟨xs, ⟨_, _, _, _, ledger⟩, _⟩ := inv.symbols.recorded
      have empty : xs = [] := by
        have := ledger.count
        rw [symZero] at this
        simp at this
        exact List.eq_nil_of_length_eq_zero (by omega)
      subst empty
      exact ⟨by simp [symZero], by simp, fun i s sel => by simp at sel, ledger.literal, ledger.distance⟩
  refine ⟨rc, _, heapCall_run (runMove.trans runTail), ⟨ds, z, _, inv'⟩, ?_, ?_⟩
  · have regions : StreamWriteRegions h r (.deflatePrime (some r) bits value) = [] := rfl
    rw [regions]
    refine ⟨?_, fun _ mem => by cases mem⟩
    simp only [restoreRegions, List.foldl]
    exact frame_owned inv (prime_frame trees.base.pbuf)
  · have shape := (shape_setB trees.base.bytes bf).trans (shape_setD (h := { h with bytes := upd h.bytes b (some bf) })
      hL.hs { d with pending_out := d.pending_buf, pending := p2, bi_buf := w2, bi_valid := v2, bi_used := u2 })
    exact live_same inv inv' (fun x => shape.live x) (fun _ => Iff.rfl)

/-- `deflatePrime` does not write the stream record. -/
theorem prime_stream {h after : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) {bits value rc : Int32}
    (run : C.run (deflatePrime (some r) bits value) h = .ok (rc, after)) : r.get after = r.get h := by
  have good := inv.good
  have hL := good.live
  by_cases range : bits.toInt < 0 ∨ 16 < bits.toInt
  · have same := run.symm.trans (deflatePrime_invalid_count hL bits value range)
    simp only [Except.ok.injEq, Prod.mk.injEq] at same
    obtain ⟨-, rfl⟩ := same
    rfl
  have b0 : 0 ≤ bits.toInt := by omega
  have b16 : bits.toInt ≤ 16 := by omega
  obtain ⟨d0, b, buf, trees⟩ := good.trees
  have e0 : d0 = d := Option.some.inj (trees.base.dstate.symm.trans hL.hs)
  rw [e0] at trees
  obtain ⟨w, p, q, b', blocks⟩ := good.inv.blocks
  have bb : b = b' := by
    have := blocks.pbuf; rw [trees.base.pbuf] at this; cases this; rfl
  subst bb
  obtain ⟨off, pout, offFit⟩ := blocks.pout
  have v0 : 0 ≤ d.bi_valid.toInt := good.inv.bits.1
  have v7 : d.bi_valid.toInt ≤ 7 := inv.shape.biValid
  have notRange : (bits < 0 || bits > 16) = false := by
    have l1 : ¬ bits < 0 := fun lt => by have := Int32.lt_iff_toInt_lt.mp lt; simp at this; omega
    have l2 : ¬ bits > 16 := fun lt => by have := Int32.lt_iff_toInt_lt.mp lt; simp at this; omega
    simp [l1, l2]
  -- the compaction
  have move : ∃ a, deflatePrime (some r) bits value h =
      primeTail (some (.tab ds)) bits value (setD (setB h b a) ds { d with pending_out := d.pending_buf }) ∧
      a.size = buf.size := by
    by_cases mv : d.pending_out = d.pending_buf
    · refine ⟨buf, ?_, rfl⟩
      have same : ({ d with pending_out := d.pending_buf } : DeflateState) = d := by
        cases d; simp only at mv; subst mv; rfl
      rw [same, self_heap trees.base.bytes hL.hs, prime_split]
      simp [stateCheck_live hL, zrd_eq, hL.hz, hL.zst, castD, ldD_eq, hL.hs, notRange, mv]
    · have psz := trees.base.psize
      obtain ⟨st, a, loop, size⟩ := move_loop trees.base.bytes trees.base.rw d.pending (off := off)
        (by have := trees.base.psize; omega)
      have loop' : cwhile moveCond moveBody (d.pending, d.pending_buf, d.pending_out) h = .ok (st, setB h b a) := by
        rw [trees.base.pbuf, pout]; exact loop
      refine ⟨a, ?_, size⟩
      rw [prime_split]
      simp [stateCheck_live hL, zrd_eq, hL.hz, hL.zst, castD, ldD_eq, hL.hs, notRange, mv, loop', wrD_eq]
  obtain ⟨a, runMove, sizeA⟩ := move
  obtain ⟨good1, trees1⟩ := move_good good trees sizeA
  obtain ⟨rc, bf, e, runTail, trees2, size2, ⟨p2, w2, v2, u2, rfl⟩, v7'⟩ :=
    prime_tail bits value trees1 b0 b16 v0 v7
  have heapEq : setD (setB (setD (setB h b a) ds { d with pending_out := d.pending_buf }) b bf) ds
      { d with pending_out := d.pending_buf, pending := p2, bi_buf := w2, bi_valid := v2, bi_used := u2 } =
      setD (setB h b bf) ds
      { d with pending_out := d.pending_buf, pending := p2, bi_buf := w2, bi_valid := v2, bi_used := u2 } :=
    setD_setB_twice h b ds a bf _ _
  rw [heapEq] at runTail
  have same := run.symm.trans (runMove.trans runTail)
  simp only [Except.ok.injEq, Prod.mk.injEq] at same
  obtain ⟨-, rfl⟩ := same
  cases r <;> rfl

end Zlib.Deflate.Universal
