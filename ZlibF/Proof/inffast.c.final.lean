import ZlibF.Proof.«inffast.c.loop»

/-!
# inffast.c: normalization and final writeback

The proof adapts the earlier split into normalization, pointer-derived
remaining counts, and stream/state stores to the current record heap.
-/

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inffast.Spec
variable {e : Env} {c : Ctx}

theorem bits_whole (b : UInt32) : (b >>> 3).toNat = b.toNat / 8 := by
  rw [UInt32.toNat_shiftRight]
  simp [Nat.shiftRight_eq_div_pow]

theorem bits_whole_shift (b : UInt32) (hb : b.toNat ≤ 30) :
    ((b >>> 3) <<< 3).toNat = b.toNat / 8 * 8 := by
  rw [UInt32.toNat_shiftLeft, bits_whole, Nat.shiftLeft_eq]
  change (b.toNat / 8 * 8) % 4294967296 = b.toNat / 8 * 8
  exact Nat.mod_eq_of_lt (by omega)

theorem bits_residual (b : UInt32) (hb : b.toNat ≤ 30) :
    (b - ((b >>> 3) <<< 3)).toNat = b.toNat % 8 := by
  rw [u32_toNat_sub (by rw [bits_whole_shift b hb]; omega), bits_whole_shift b hb]
  omega

theorem LS.buffered_le {l : L} {i o : Nat} (hl : LS e l i o) :
    l.bits.toNat / 8 ≤ i - e.i0 := by
  have hacc := hl.hacc
  have hb0 := e.hbits
  omega

theorem normalized_hold_lt (H : UInt64) (b : UInt32) (hb : b.toNat < 32) :
    (H &&& (((1 : UInt32) <<< b) - 1).toUInt64).toNat < 2 ^ b.toNat := by
  have hm : ((((1 : UInt32) <<< b) - 1).toUInt64).toNat = 2 ^ b.toNat - 1 := by
    rw [UInt32.toNat_toUInt64]
    exact u32_shl1_sub1 hb
  rw [u64_and_mask hm]
  exact Nat.mod_lt _ (Nat.pow_pos (by omega))

/-- The C conditional arithmetic computes the exact nonnegative remaining
count, in both pointer-order branches. -/
theorem ptr_avail_run {h : Heap} {r : BRef} {A : Array UInt8} {p q k : Nat}
    (hg : Space.get h r = some A) (hp : p ≤ A.size) (hq : q ≤ A.size)
    (hsz : A.size < 2 ^ 63) (hle : p ≤ q + k) (hk : k < 2 ^ 31)
    (hr : q + k - p < 2 ^ 32) :
    (do
      if ← Ptr.lt (.ref r p) (.ref r q) then do
        let d ← Ptr.diff (.ref r q) (.ref r p)
        chk64 ((k : Int) + d.toInt)
      else do
        let d ← Ptr.diff (.ref r p) (.ref r q)
        chk64 ((k : Int) - d.toInt)) h =
    .ok (Int64.ofInt ((q + k - p : Nat) : Int), h) := by
  rw [bind_ok (Ptr.lt_ok hg hp hq)]
  by_cases hc : p < q
  · simp only [hc, decide_true, ite_true]
    have hd := Ptr.diff_ok hg hq hp (by omega)
    have hdiff : (q : Int) - (p : Int) = ((q - p : Nat) : Int) := by omega
    rw [hdiff] at hd
    rw [bind_ok hd, i64_toInt (q - p) (by omega)]
    have hv : (k : Int) + (q - p : Nat) = ((q + k - p : Nat) : Int) := by omega
    rw [hv, chk64_eq (by omega) (by omega)]
    rfl
  · simp only [hc, decide_false, Bool.false_eq_true, ite_false]
    have hd := Ptr.diff_ok hg hp hq (by omega)
    have hdiff : (p : Int) - (q : Int) = ((p - q : Nat) : Int) := by omega
    rw [hdiff] at hd
    rw [bind_ok hd, i64_toInt (p - q) (by omega)]
    have hv : (k : Int) - (p - q : Nat) = ((q + k - p : Nat) : Int) := by omega
    rw [hv, chk64_eq (by omega) (by omega)]
    rfl

/-- The C conditional arithmetic computes the exact nonnegative remaining
count, in both pointer-order branches. -/
theorem ptr_avail_cont {α : Type} {h : Heap} {r : BRef} {A : Array UInt8} {p q k : Nat}
    (hg : Space.get h r = some A) (hp : p ≤ A.size) (hq : q ≤ A.size)
    (hsz : A.size < 2 ^ 63) (hle : p ≤ q + k) (hk : k < 2 ^ 31)
    (hr : q + k - p < 2 ^ 32) (K : Int64 → M α) :
    (do
      if ← Ptr.lt (.ref r p) (.ref r q) then do
        let d ← Ptr.diff (.ref r q) (.ref r p)
        let v ← chk64 ((k : Int) + d.toInt)
        K v
      else do
        let d ← Ptr.diff (.ref r p) (.ref r q)
        let v ← chk64 ((k : Int) - d.toInt)
        K v) h =
    K (Int64.ofInt ((q + k - p : Nat) : Int)) h := by
  rw [bind_ok (Ptr.lt_ok hg hp hq)]
  by_cases hc : p < q
  · simp only [hc, decide_true, ite_true]
    have hd := Ptr.diff_ok hg hq hp (by omega)
    have hdiff : (q : Int) - (p : Int) = ((q - p : Nat) : Int) := by omega
    rw [hdiff] at hd
    rw [bind_ok hd, i64_toInt (q - p) (by omega)]
    have hv : (k : Int) + (q - p : Nat) = ((q + k - p : Nat) : Int) := by omega
    rw [hv, chk64_eq (by omega) (by omega)]
    rfl
  · simp only [hc, decide_false, Bool.false_eq_true, ite_false]
    have hd := Ptr.diff_ok hg hp hq (by omega)
    have hdiff : (p : Int) - (q : Int) = ((p - q : Nat) : Int) := by omega
    rw [hdiff] at hd
    rw [bind_ok hd, i64_toInt (p - q) (by omega)]
    have hv : (k : Int) - (p - q : Nat) = ((q + k - p : Nat) : Int) := by omega
    rw [hv, chk64_eq (by omega) (by omega)]
    rfl

theorem ptr_avail_wp {α : Type} {h : Heap} {r : BRef} {A : Array UInt8} {p q k : Nat}
    (hg : Space.get h r = some A) (hp : p ≤ A.size) (hq : q ≤ A.size)
    (hsz : A.size < 2 ^ 63) (hle : p ≤ q + k) (hk : k < 2 ^ 31)
    (hr : q + k - p < 2 ^ 32) {K : Int64 → M α} {Q : α → Heap → Prop}
    (hK : Wp (K (Int64.ofInt ((q + k - p : Nat) : Int))) h Q) :
    Wp (do
      if ← Ptr.lt (.ref r p) (.ref r q) then do
        let d ← Ptr.diff (.ref r q) (.ref r p)
        let v ← chk64 ((k : Int) + d.toInt)
        K v
      else do
        let d ← Ptr.diff (.ref r p) (.ref r q)
        let v ← chk64 ((k : Int) - d.toInt)
        K v) h Q := by
  obtain ⟨v, h', hrK, hpost⟩ := hK
  exact ⟨v, h', (ptr_avail_cont hg hp hq hsz hle hk hr K).trans hrK, hpost⟩

theorem i64_to_u32_eq (n : Nat) (hn : n < 2 ^ 32) :
    (Int64.ofInt (n : Int)).toUInt64.toUInt32 = UInt32.ofNat n := by
  apply UInt32.toNat_inj.mp
  rw [i64_toU32 n hn, UInt32.toNat_ofNat']
  exact (Nat.mod_eq_of_lt hn).symm

theorem Env.stream_get_frame (e : Env) (bytes : Tbl (Option (Array UInt8)))
    (states : Tbl (Option InflateState)) :
    e.r.get { e.h0 with bytes, istates := states } = some e.sm0 := by
  have hh := e.hsm
  cases hr : e.r <;> (rw [hr] at hh; simpa [ZStreamRef.get] using hh)

/-- Exact stream/state stores in the translated epilogue. -/
theorem fast_stores_run (e : Env) (A : Array UInt8) (msg : BPtr) (mode : UInt32)
    (input output : BPtr) (ai ao : UInt32) (hold : UInt64) (bits : UInt32) :
    (do
      let sm ← ldZStream e.strm
      stZStream e.strm { sm with next_in := input, next_out := output, avail_in := ai, avail_out := ao }
      let st ← ldInflateState (some (.tab e.stid))
      stInflateState (some (.tab e.stid)) { st with hold, bits }) (e.heap A msg mode) =
    .ok ((), e.r.put
      { e.h0 with bytes := upd e.h0.bytes e.ob (some A), istates := upd e.h0.istates e.stid (some { e.s0 with mode, hold, bits }) }
      { e.sm0 with next_in := input, next_out := output, avail_in := ai, avail_out := ao, msg }) := by
  rw [e.hstrm, bind_ok (ldZStream_ok (e.heap_rget A msg mode)),
    bind_ok (stZStream_ok (e.heap_rget A msg mode) e.hrw)]
  let H := e.r.put (e.heap A msg mode)
    { e.sm0 with next_in := input, next_out := output, avail_in := ai, avail_out := ao, msg }
  have hg : H.istates e.stid = some { e.s0 with mode } := by
    dsimp only [H]
    rw [put_istates, e.heap_istates]
    exact upd_same _ _ _
  rw [bind_ok (ldInflateState_tab hg), stInflateState_tab hg]
  dsimp only [H]
  unfold Env.heap
  rw [put_istates_comm, put_istates_comm]
  simp only [put_istates, upd_upd]
  rw [put_put _ _ e.sm0 _ _ (e.stream_get_frame _ _)]

/-- The actual normalization and writeback fragment establishes FastPost
from the proved loop facts. No callee behavior is an assumption. -/
theorem fast_finish_wp (e : Env) (A : Array UInt8) (msg : BPtr) (mode : UInt32)
    (l : L) (i o : Nat) (hl : LS e l i o) (hAsz : A.size = e.A0.size)
    (ho : o ≤ e.o0 + e.sm0.avail_out.toNat)
    (hf : ∀ j, (j < e.o0 ∨ o ≤ j) → A[j]? = e.A0[j]?)
    (hclass : (mode = e.s0.mode ∧ msg = e.sm0.msg) ∨ (mode = TYPE ∧ msg = e.sm0.msg) ∨ mode = BAD)
    (hstop : mode ≠ TYPE → mode ≠ BAD → i + 6 > e.i0 + e.sm0.avail_in.toNat ∨
      o + 258 > e.o0 + e.sm0.avail_out.toNat)
    (hfr : e.InputFrame A i) :
    Wp (do
      let len := l.bits >>> 3
      let input ← subn l.in_ len
      let bits := l.bits - (len <<< 3)
      let hold := l.hold &&& ((← shl32 1 bits) - 1).toUInt64
      let ai : Int64 ←
        if ← Ptr.lt input (.ref (BRef.blk e.ib) (e.i0 + e.sm0.avail_in.toNat - 5)) then do
          let d ← Ptr.diff (.ref (BRef.blk e.ib) (e.i0 + e.sm0.avail_in.toNat - 5)) input
          chk64 (5 + d.toInt)
        else do
          let d ← Ptr.diff input (.ref (BRef.blk e.ib) (e.i0 + e.sm0.avail_in.toNat - 5))
          chk64 (5 - d.toInt)
      let ao : Int64 ←
        if ← Ptr.lt l.out (.ref (BRef.blk e.ob) (e.o0 + e.sm0.avail_out.toNat - 257)) then do
          let d ← Ptr.diff (.ref (BRef.blk e.ob) (e.o0 + e.sm0.avail_out.toNat - 257)) l.out
          chk64 (257 + d.toInt)
        else do
          let d ← Ptr.diff l.out (.ref (BRef.blk e.ob) (e.o0 + e.sm0.avail_out.toNat - 257))
          chk64 (257 - d.toInt)
      let sm ← ldZStream e.strm
      stZStream e.strm { sm with next_in := input, next_out := l.out, avail_in := ai.toUInt64.toUInt32, avail_out := ao.toUInt64.toUInt32 }
      let st ← ldInflateState (some (.tab e.stid))
      stInflateState (some (.tab e.stid)) { st with hold, bits })
      (e.heap A msg mode) (fun _ after => FastPost e after) := by
  let buf := l.bits.toNat / 8
  let used := i - e.i0 - buf
  let produced := o - e.o0
  let bits := l.bits - ((l.bits >>> 3) <<< 3)
  let hold := l.hold &&& (((1 : UInt32) <<< bits) - 1).toUInt64
  have hbuf : buf ≤ i - e.i0 := hl.buffered_le
  have hsmall : buf ≤ 3 := by dsimp only [buf]; have := hl.hb; omega
  have hused : used + buf = i - e.i0 := by dsimp only [used]; omega
  have hui : used + buf ≤ e.sm0.avail_in.toNat := by have := hl.hi0; have := hl.hi1; omega
  have hup : produced ≤ e.sm0.avail_out.toNat := by dsimp only [produced]; have := hl.ho0; omega
  have hio : i - (l.bits >>> 3).toNat = e.i0 + used := by
    rw [bits_whole]
    change i - buf = e.i0 + used
    have := hl.hi0
    omega
  have hout : o = e.o0 + produced := by dsimp only [produced]; have := hl.ho0; omega
  have hbits : bits.toNat < 8 := by dsimp only [bits]; rw [bits_residual _ hl.hb]; omega
  have hinbuf : OkOn (e.heap A msg mode) (subn l.in_ (l.bits >>> 3))
      (.ref (BRef.blk e.ib) (e.i0 + used)) := by
    rw [hl.hin]
    have hr := subn_ok (h := e.heap A msg mode) (r := BRef.blk e.ib) (a := e.inArr A) (e.heap_bytes_in A msg mode)
      (n := l.bits >>> 3) (off := i) (by rw [bits_whole]; have := hl.hi0; omega)
      (by have := hl.hi1; have := e.hINsz; have := e.inArr_size hfr; omega)
    simpa only [hio] using hr
  refine Wp.bindO hinbuf ?_
  refine Wp.bindO (shl32_ok (x := 1) (n := bits) (by omega)) ?_
  have hu32 : e.sm0.avail_in.toNat - used < 2 ^ 32 := by have := UInt32.toNat_lt e.sm0.avail_in; omega
  have ho32 : e.sm0.avail_out.toNat - produced < 2 ^ 32 := by have := UInt32.toNat_lt e.sm0.avail_out; omega
  have hei : e.i0 + e.sm0.avail_in.toNat - 5 + 5 - (e.i0 + used) = e.sm0.avail_in.toNat - used := by
    have := e.hai; omega
  refine ptr_avail_wp (h := e.heap A msg mode) (r := BRef.blk e.ib) (A := e.inArr A)
    (p := e.i0 + used) (q := e.i0 + e.sm0.avail_in.toNat - 5) (k := 5)
    (e.heap_bytes_in A msg mode) (by have := e.hINsz; have := e.inArr_size hfr; omega)
    (by have := e.hINsz; have := e.inArr_size hfr; omega)
    (by rw [e.inArr_size hfr]; exact e.hINbig) (by have := e.hai; omega) (by decide) (by rw [hei]; exact hu32) ?_
  rw [hei]
  rw [hl.hout]
  have heo : e.o0 + e.sm0.avail_out.toNat - 257 + 257 - o = e.sm0.avail_out.toNat - produced := by
    have := e.hao; omega
  refine ptr_avail_wp (h := e.heap A msg mode) (r := BRef.blk e.ob) (A := A)
    (p := o) (q := e.o0 + e.sm0.avail_out.toNat - 257) (k := 257)
    (e.heap_bytes_ob A msg mode) (by rw [hAsz]; have := e.hAsz; omega) (by rw [hAsz]; have := e.hAsz; omega)
    (by rw [hAsz]; exact e.hAbig) (by have := e.hao; omega) (by decide) (by rw [heo]; exact ho32) ?_
  rw [heo]
  rw [i64_to_u32_eq _ hu32, i64_to_u32_eq _ ho32]
  refine Wp.of_eq (fast_stores_run e A msg mode (.ref (BRef.blk e.ib) (e.i0 + used)) (.ref (BRef.blk e.ob) o)
    (UInt32.ofNat (e.sm0.avail_in.toNat - used)) (UInt32.ofNat (e.sm0.avail_out.toNat - produced)) hold bits) ?_
  refine ⟨used, produced, buf, A, msg, mode, bits, hold, hui, hsmall, hup, hAsz, hbits,
    normalized_hold_lt l.hold bits (by omega), ?_, ?_, hclass, ?_⟩
  · rw [← hout]
  · intro j hj
    exact hf j (by rw [← hout] at hj; exact hj)
  · intro hnt hnb
    rcases hstop hnt hnb with hi | ho
    · exact Or.inl (by have := hl.hi0; omega)
    · exact Or.inr (by omega)

/-- The complete actual fast decoder satisfies the unchanged reviewed
safety, termination, frame, normalization and writeback goal. -/
theorem inflate_fast_safe : Goal.fast_safe := by
  intro e
  have hw : Wp (inflate_fast e.strm e.start) e.h0 (fun _ after => FastPost e after) := by
    let c0 : Ctx := {
      strm := e.strm, state := some (.tab e.stid),
      last := .ref (BRef.blk e.ib) (e.i0 + e.sm0.avail_in.toNat - 5),
      beg := .ref (BRef.blk e.ob) e.bg,
      end_ := .ref (BRef.blk e.ob) (e.o0 + e.sm0.avail_out.toNat - 257),
      wsize := e.s0.wsize, whave := e.s0.whave, wnext := e.s0.wnext, window := e.s0.window,
      lcode := e.s0.lencode, dcode := e.s0.distcode,
      lmask := ((1 : UInt32) <<< e.s0.lenbits) - 1, dmask := ((1 : UInt32) <<< e.s0.distbits) - 1 }
    let l0 : L := {
      in_ := .ref (BRef.blk e.ib) e.i0, out := .ref (BRef.blk e.ob) e.o0,
      hold := e.s0.hold, bits := e.s0.bits, here := default, op := 0, len := 0, dist := 0,
      from_ := default, broke := false, againL := false, againD := false }
    have hc0 : CtxOK e c0 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hl0 : LS e l0 e.i0 e.o0 := by
      dsimp only [l0]
      refine ⟨rfl, rfl, by omega, ?_, by omega, ?_, e.hhold, ?_⟩
      · have := e.hai; omega
      · change e.s0.bits.toNat ≤ 30
        have := e.hbits; omega
      · change e.s0.bits.toNat + 8 * e.i0 ≤ e.s0.bits.toNat + 8 * e.i0
        exact Nat.le_refl _
    have hlast : OkOn e.h0 (Ptr.add e.sm0.next_in (e.sm0.avail_in - 5).toNat)
        (.ref (BRef.blk e.ib) (e.i0 + e.sm0.avail_in.toNat - 5)) := by
      rw [e.hnin, u32_toNat_sub (by change 5 ≤ e.sm0.avail_in.toNat; have := e.hai; omega)]
      have hr := Ptr.add_nat_ok (h := e.h0) (r := BRef.blk e.ib) (a := e.IN)
        (off := e.i0) (n := e.sm0.avail_in.toNat - 5) e.hIN (by have := e.hINsz; omega)
      have hoff : e.i0 + (e.sm0.avail_in.toNat - 5) = e.i0 + e.sm0.avail_in.toNat - 5 := by have := e.hai; omega
      simpa [hoff] using hr
    have hbeg : OkOn e.h0 (subn e.sm0.next_out (e.start - e.sm0.avail_out))
        (.ref (BRef.blk e.ob) e.bg) := by
      rw [e.hnout]
      have hn : (e.start - e.sm0.avail_out).toNat = e.start.toNat - e.sm0.avail_out.toNat :=
        u32_toNat_sub e.hstart
      have hr := subn_ok (h := e.h0) (r := BRef.blk e.ob) (a := e.A0)
        (off := e.o0) (n := e.start - e.sm0.avail_out) e.hA0 (by rw [hn]; exact e.hbeg)
        (by have := e.hAsz; omega)
      simpa only [hn, Env.bg] using hr
    have hend : OkOn e.h0 (Ptr.add e.sm0.next_out (e.sm0.avail_out - 257).toNat)
        (.ref (BRef.blk e.ob) (e.o0 + e.sm0.avail_out.toNat - 257)) := by
      rw [e.hnout, u32_toNat_sub (by change 257 ≤ e.sm0.avail_out.toNat; have := e.hao; omega)]
      have hr := Ptr.add_nat_ok (h := e.h0) (r := BRef.blk e.ob) (a := e.A0)
        (off := e.o0) (n := e.sm0.avail_out.toNat - 257) e.hA0 (by have := e.hAsz; omega)
      have hoff : e.o0 + (e.sm0.avail_out.toNat - 257) = e.o0 + e.sm0.avail_out.toNat - 257 := by have := e.hao; omega
      simpa [hoff] using hr
    unfold inflate_fast
    refine Wp.bindO (x := e.sm0) (by rw [e.hstrm]; exact ldZStream_ok e.hsm) ?_
    refine Wp.bindO (x := some (InflateStateRef.tab e.stid)) (by rw [e.hstate]; exact castInflateState_ok) ?_
    refine Wp.bindO hlast ?_
    refine Wp.bindO hbeg ?_
    refine Wp.bindO hend ?_
    refine Wp.bindO (ldInflateState_tab e.hs0) ?_
    refine Wp.bindO (shl32_ok (x := 1) (n := e.s0.lenbits) (by have := e.hlt.1; omega)) ?_
    refine Wp.bindO (shl32_ok (x := 1) (n := e.s0.distbits) (by have := e.hdt.1; omega)) ?_
    rw [e.hnin, e.hnout]
    obtain ⟨l, h, hr, hpost⟩ := fast_loop_wp hc0 l0 e.i0 e.o0 e.A0 hl0 rfl rfl
      (by have := e.hai; omega) (by have := e.hao; omega) (by intro _ _; rfl)
    rw [e.heap_initial] at hr
    refine Wp.bindE hr ?_
    obtain ⟨i, o, A, msg, mode, hl, ho, hA, hh, hf, hclass, hstop⟩ := hpost
    rw [hh]
    exact fast_finish_wp e A msg mode l i o hl hA ho hf hclass hstop
      (e.inputFrame_of_frame hA hf ho hl.hi0)
  obtain ⟨⟨⟩, after, hr, hp⟩ := hw
  exact ⟨after, hr, hp⟩

end Zlib.Inffast.Proofs
