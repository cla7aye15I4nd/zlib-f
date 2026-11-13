import ZlibF.Proof.«inffast.c.final»
import ZlibF.Proof.«inffast.c.loop-progress»

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inffast.Spec

/-- A complete nonterminal fast call strictly consumes output room.
The state and stream are the actual records on the returned heap. -/
def FastProgress (e : Env) (after : Heap) : Prop :=
  ∃ stream state, e.r.get after = some stream ∧ after.istates e.stid = some state ∧
    (state.mode ≠ TYPE → state.mode ≠ BAD → stream.avail_out.toNat < e.sm0.avail_out.toNat)

theorem fast_finish_progress_wp (e : Env) (A : Array UInt8) (msg : BPtr) (mode : UInt32)
    (l : L) (i o : Nat) (hl : LS e l i o) (hAsz : A.size = e.A0.size)
    (ho : o ≤ e.o0 + e.sm0.avail_out.toNat)
    (hf : ∀ j, (j < e.o0 ∨ o ≤ j) → A[j]? = e.A0[j]?)
    (hclass : (mode = e.s0.mode ∧ msg = e.sm0.msg) ∨ (mode = TYPE ∧ msg = e.sm0.msg) ∨ mode = BAD)
    (hstop : mode ≠ TYPE → mode ≠ BAD → i + 6 > e.i0 + e.sm0.avail_in.toNat ∨
      o + 258 > e.o0 + e.sm0.avail_out.toNat)
    (progress : mode ≠ TYPE → mode ≠ BAD → e.o0 < o)
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
      (e.heap A msg mode) (fun _ after => FastPost e after ∧ FastProgress e after) := by
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
  constructor
  · refine ⟨used, produced, buf, A, msg, mode, bits, hold, hui, hsmall, hup, hAsz, hbits,
      normalized_hold_lt l.hold bits (by omega), ?_, ?_, hclass, ?_⟩
    · rw [← hout]
    · intro j hj
      exact hf j (by rw [← hout] at hj; exact hj)
    · intro hnt hnb
      rcases hstop hnt hnb with hi | ho
      · exact Or.inl (by have := hl.hi0; omega)
      · exact Or.inr (by omega)

  · let stream := { e.sm0 with next_in := .ref (.blk e.ib) (e.i0 + used), next_out := .ref (.blk e.ob) o, avail_in := UInt32.ofNat (e.sm0.avail_in.toNat - used), avail_out := UInt32.ofNat (e.sm0.avail_out.toNat - produced), msg }
    let state := { e.s0 with mode, hold, bits }
    have baseGet : e.r.get { e.h0 with bytes := upd e.h0.bytes e.ob (some A), istates := upd e.h0.istates e.stid (some state) } = some e.sm0 := by
      cases refEq : e.r with
      | tab k => simpa only [refEq, ZStreamRef.get] using e.hsm
      | in_gzstate_strm k => simpa only [refEq, ZStreamRef.get] using e.hsm
    refine ⟨stream, state, put_get _ _ _ _ baseGet, ?_, ?_⟩
    · rw [put_istates, upd_same]
    · intro nonterminal nonbad
      have positive : 0 < produced := by
        dsimp only [produced]
        have advancing := progress nonterminal nonbad
        omega
      change (UInt32.ofNat (e.sm0.avail_out.toNat - produced)).toNat < e.sm0.avail_out.toNat
      rw [UInt32.toNat_ofNat_of_lt' (by simp only [UInt32.size]; exact ho32)]
      omega

/-- The actual complete fast decoder retains safety and strict nonterminal output progress. -/
theorem inflate_fast_safe_progress (e : Env) :
    ∃ after, C.run (inflate_fast e.strm e.start) e.h0 = .ok ((), after) ∧
      FastPost e after ∧ FastProgress e after := by
  have hw : Wp (inflate_fast e.strm e.start) e.h0 (fun _ after => FastPost e after ∧ FastProgress e after) := by
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
    obtain ⟨l, h, hr, hpost⟩ := fast_loop_wp_progress hc0 l0 e.i0 e.o0 e.A0 hl0 rfl rfl
      (by have := e.hai; omega) (by have := e.hao; omega) (by intro _ _; rfl)
    rw [e.heap_initial] at hr
    refine Wp.bindE hr ?_
    obtain ⟨i, o, A, msg, mode, hl, ho, hA, hh, hf, hclass, hstop, _, progress⟩ := hpost
    rw [hh]
    exact fast_finish_progress_wp e A msg mode l i o hl hA ho hf hclass hstop progress
      (e.inputFrame_of_frame hA hf ho hl.hi0)
  obtain ⟨⟨⟩, after, hr, hp⟩ := hw
  exact ⟨after, hr, hp⟩

end Zlib.Inffast.Proofs
