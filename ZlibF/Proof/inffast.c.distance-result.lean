import ZlibF.Spec.InflateFastDistanceResult
import ZlibF.Proof.«inffast.c.match-history»
import ZlibF.Proof.«inffast.c.distance-semantics»
import ZlibF.Proof.«inffast.c.advance»
import ZlibF.Proof.«inffast.c.flags»

/-!
# Actual distance lookup, extra bits and independent match copying

The source proves the three physical exits before table semantics classify
its selected symbol. Copy failures retain the exact stream after extras.
-/

set_option autoImplicit false

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inffast.Spec.DistanceResult ZlibF.Math.LZ77Copy
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
variable {e : Env} {c : Ctx}

private theorem copy_result_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32)
    (l : L) (i o : Nat) (hls : LS e l i o)
    (hbg : e.bg ≤ o) (hop : l.op.toNat = o-e.bg)
    (hd : 1 ≤ l.dist.toNat) (hlen : 3 ≤ l.len.toNat)
    (hroom : o+l.len.toNat ≤ A.size) (hbroke : l.broke = false) :
    Wp (copyMatch c l) (e.heap A msg m) (fun l' after =>
      CopyOutcome e A msg m (Sg e l.hold.toNat l.bits.toNat i) o l.len.toNat l.dist.toNat l' after) := by
  have copy := actual_copy_match_refines_lz77 e c A msg m l o hc hls.hout hbg hop hd hlen hroom hbroke
  dsimp only at copy
  unfold CopyOutcome
  by_cases far :
      (MatchHistory.saved e.W e.s0.wsize.toNat e.s0.wnext.toNat e.s0.whave.toNat e.woff).length +
        (writtenBytes A o (o-e.bg)).length < l.dist.toNat
  · simp only [far,ite_true] at copy ⊢
    obtain ⟨l',after,p,run,hin,hold,bits,againL,againD,broke,hout,heap⟩ := copy
    refine ⟨l',after,run,i,p,broke,?_,?_,heap⟩
    · exact hls.congr hin hout hold bits
    · simp only [hold,bits]
  · simp only [far,ite_false] at copy ⊢
    obtain ⟨l',after,run,hin,hold,bits,againL,againD,broke,hout,heap,meaning⟩ := copy
    refine ⟨l',after,run,i,broke,?_,?_,heap,meaning⟩
    · exact ⟨hin.trans hls.hin,hout,hls.hi0,hls.hi1,by have := hls.ho0; omega,
        by rw [bits]; exact hls.hb,by rw [hold,bits]; exact hls.hH,by rw [bits]; exact hls.hacc⟩
    · simp only [hold,bits]

private theorem distCont_result_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32) (l : L) (i o : Nat)
    (hls : LS e l i o) (hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size) (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hAb : A.size < 2 ^ 63)
    (hx : l.op.toNat ≤ 13) (hxb : l.op.toNat ≤ l.bits.toNat) (hd1 : 1 ≤ l.dist.toNat) (hd2 : l.dist.toNat ≤ 65536)
    (hlen : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258) (hbroke : l.broke = false) :
    Wp (distCont c l) (e.heap A msg m) (fun l' after =>
      ∃ extra rest, readBits l.op.toNat (Sg e l.hold.toNat l.bits.toNat i) = some (extra,rest) ∧
        CopyOutcome e A msg m rest o l.len.toNat (l.dist.toNat+extra) l' after) := by
  have hbgo : e.bg ≤ o := by have := e.bg_le; have := hls.ho0; omega
  have hoA : o ≤ A.size := by omega
  have hxs : l.op.toNat < 32 := by omega
  unfold distCont
  refine Wp.bindO (shl32_ok hxs) ?_
  dsimp only
  have hlow := hold_low32 (x := l.hold) (k := l.op) hxs
  have hlowlt : l.hold.toNat % 2 ^ l.op.toNat < 2 ^ l.op.toNat := Nat.mod_lt _ (Nat.pow_pos (by omega))
  have hpow : 2 ^ l.op.toNat ≤ 2 ^ 13 := Nat.pow_le_pow_right (by omega) hx
  have hdist' : (l.dist + (l.hold.toUInt32 &&& (1 <<< l.op) - 1)).toNat = l.dist.toNat + l.hold.toNat % 2 ^ l.op.toNat := by
    rw [u32_toNat_add (by rw [hlow]; omega), hlow]
  refine Wp.bindO (shr64_ok (x := l.hold) (n := l.op.toUInt64) (by rw [UInt32.toNat_toUInt64]; omega)) ?_
  have hbgdef : e.bg = e.o0 - (e.start.toNat - e.sm0.avail_out.toNat) := rfl
  have hst32 := UInt32.toNat_lt e.start
  have hstart := e.hstart
  have hbeg := e.hbeg
  have hdiff : OkOn (e.heap A msg m) (Ptr.diff l.out c.beg) (Int64.ofInt (((o - e.bg : Nat)) : Int)) := by
    rw [hls.hout, hc.beg]
    have := Ptr.diff_ok (r := BRef.blk e.ob) (a := A) (o1 := o) (o2 := e.bg) (e.heap_bytes_ob A msg m) hoA (by omega)
      ⟨by omega, by omega⟩
    have e1 : (o : Int) - (e.bg : Int) = ((o - e.bg : Nat) : Int) := by omega
    rw [e1] at this
    exact this
  refine Wp.bindO hdiff ?_
  have hopn : (Int64.ofInt (((o - e.bg : Nat)) : Int)).toUInt64.toUInt32.toNat = o - e.bg := i64_toU32 _ (by omega)
  have hls1 : LS e (dropL l l.op) i o := hls.dropL l.op hxb (by omega)
  have hrb := readBits_bitsOfNat l.op.toNat l.bits.toNat l.hold.toNat (inBits e i) hxb
  have hsg := Sg_dropL (e := e) l l.op i hxb (by omega)
  refine Wp.mono (copy_result_wp (e:=e) (c:=c) hc A msg m
    { in_ := l.in_, out := l.out, hold := l.hold >>> l.op.toUInt64, bits := l.bits-l.op, here := l.here,
      op := (Int64.ofInt (((o-e.bg : Nat)) : Int)).toUInt64.toUInt32, len := l.len,
      dist := l.dist + (l.hold.toUInt32 &&& 1 <<< l.op - 1), from_ := l.from_, broke := l.broke,
      againL := l.againL, againD := l.againD }
    i o (LS.congr hls1 rfl rfl rfl rfl) hbgo hopn
    (by simp only [hdist']; omega) hlen.1 (by simp only []; omega) hbroke) ?_
  intro l' after copy
  refine ⟨l.hold.toNat % 2^l.op.toNat,Sg e (dropL l l.op).hold.toNat (dropL l l.op).bits.toNat i,?_,?_⟩
  · unfold Sg
    rw [hrb,dropL_hold l l.op (by omega),dropL_bits l l.op hxb]
  · simpa only [dropL,hdist'] using copy

private theorem dodistBase_result_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32) (l : L) (i o : Nat)
    (hls : LS e l i o) (hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size) (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hAb : A.size < 2 ^ 63) (hx : l.op.toNat ≤ 13) (hd1 : 1 ≤ l.dist.toNat) (hd2 : l.dist.toNat ≤ 65536)
    (hlen : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258) (hbroke : l.broke = false)
    (hpull : i + 2 ≤ e.i0 + e.sm0.avail_in.toNat ∨ (i + 1 ≤ e.i0 + e.sm0.avail_in.toNat ∧ 5 ≤ l.bits.toNat)) :
    Wp (dodistBase c l) (e.heap A msg m) (fun l' after =>
      ∃ extra rest, readBits l.op.toNat (Sg e l.hold.toNat l.bits.toNat i) = some (extra,rest) ∧
        CopyOutcome e A msg m rest o l.len.toNat (l.dist.toNat+extra) l' after) := by
  unfold dodistBase
  by_cases h1 : l.bits < l.op
  · simp only [h1, ite_true]
    have h1' : l.bits.toNat < l.op.toNat := UInt32.lt_iff_toNat_lt.mp h1
    have hiin : i < e.i0 + e.sm0.avail_in.toNat := by omega
    refine Wp.bindO (pull_run e _ l i o hls (by omega) hiin (e.heap_bytes_in A msg m)) ?_
    have hl3 := hls.pullL (by omega) hiin
    have hs3 := Sg_pullL hls (by omega) hiin
    have hb3 := pullL_bits l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1)) hls.hb
    by_cases h2 : (pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1))).bits <
        (pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1))).op
    · simp only [h2, ite_true]
      have h2' : l.bits.toNat + 8 < l.op.toNat := by
        have := UInt32.lt_iff_toNat_lt.mp h2
        simp only [pullL] at this hb3 ⊢
        omega
      have hi2 : i + 1 < e.i0 + e.sm0.avail_in.toNat := by omega
      have hb3' : (pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1))).bits.toNat ≤ 22 := by omega
      refine Wp.bindO (pull_run e _ _ (i + 1) o hl3 hb3' hi2 (e.heap_bytes_in A msg m)) ?_
      have hl4 := hl3.pullL hb3' hi2
      have hs4 := Sg_pullL hl3 hb3' hi2
      have hb4 := pullL_bits (pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1))) (e.IN.getD (i + 1) 0)
        (.ref (BRef.blk e.ib) (i + 1 + 1)) hl3.hb
      refine Wp.mono (distCont_result_wp hc A msg m _ (i + 1 + 1) o hl4 hA ho hAb (by simp only [pullL]; omega)
        (by simp only [pullL] at hb3 hb4 ⊢; omega) (by simp only [pullL]; omega) (by simp only [pullL]; omega)
        (by simp only [pullL]; omega) (by simp only [pullL]; omega)) ?_
      intro l' h' hq
      obtain ⟨extra,rest,read,copy⟩ := hq
      refine ⟨extra,rest,?_,copy⟩
      simp only [pullL] at read hs4 hs3 ⊢
      rw [hs4,hs3] at read
      exact read
    · simp only [h2, ite_false]
      have h2n : (pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1))).op.toNat ≤
          (pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1))).bits.toNat := by
        have : ¬ ((pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1))).bits.toNat <
            (pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1))).op.toNat) :=
          fun h => h2 (UInt32.lt_iff_toNat_lt.mpr h)
        omega
      refine Wp.mono (distCont_result_wp hc A msg m _ (i + 1) o hl3 hA ho hAb (by simp only [pullL]; omega)
        h2n (by simp only [pullL]; omega) (by simp only [pullL]; omega)
        (by simp only [pullL]; omega) (by simp only [pullL]; omega)) ?_
      intro l' h' hq
      obtain ⟨extra,rest,read,copy⟩ := hq
      refine ⟨extra,rest,?_,copy⟩
      simp only [pullL] at read hs3 ⊢
      rw [hs3] at read
      exact read
  · simp only [h1, ite_false]
    have h1' : l.op.toNat ≤ l.bits.toNat := by
      have : ¬ (l.bits.toNat < l.op.toNat) := fun h => h1 (UInt32.lt_iff_toNat_lt.mpr h)
      omega
    refine Wp.mono (distCont_result_wp hc A msg m l i o hls hA ho hAb hx h1' hd1 hd2 hlen hbroke) ?_
    intro l' h' hq
    exact hq

set_option maxHeartbeats 1000000 in
private theorem dodist_result_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32) (l : L) (i o d k : Nat)
    (hls : LS e l i o) (hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size) (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hAb : A.size < 2 ^ 63) (hbroke : l.broke = false) (hlen : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    (hhere : l.here = .ref e.rd k) (hk : k < e.DCA.size)
    (hEb : (e.DCA.getD k default).bits.toNat ≤ l.bits.toNat)
    (hEd : (e.DCA.getD k default).bits.toNat + d ≤ 15)
    (hcl : DistClass e (e.DCA.getD k default))
    (hpull : i + 2 ≤ e.i0 + e.sm0.avail_in.toNat ∨ (i + 1 ≤ e.i0 + e.sm0.avail_in.toNat ∧ 20 ≤ l.bits.toNat + d)) :
    Wp (dodist c l) (e.heap A msg m) (fun l' after =>
      l'.againD = true ∨
        PhysicalOutcome e A msg m (Sg e l.hold.toNat l.bits.toNat i) o l.len.toNat
          (e.DCA.getD k default) (e.DCA.getD k default).bits.toNat l' after) := by
  have hkE : e.DCA[k]'hk = e.DCA.getD k default := by simp [Array.getD_eq_getD_getElem?, hk]
  have hld : OkOn (e.heap A msg m) (Ptr.load l.here) (e.DCA.getD k default) := by
    rw [hhere, ← hkE]; exact Ptr.load_ok (e.heap_cget_DCA A msg m) hk
  have hEb64 : (((e.DCA.getD k default).bits.toUInt32).toUInt64).toNat = (e.DCA.getD k default).bits.toNat := by
    simp [toNat32]
  have hEbn : ((e.DCA.getD k default).bits.toUInt32).toNat = (e.DCA.getD k default).bits.toNat := toNat32 _
  have hls1 : LS e (dropL l (e.DCA.getD k default).bits.toUInt32) i o :=
    hls.dropL _ (by omega) (by omega)
  have hEb64 : (((e.DCA.getD k default).bits.toUInt32).toUInt64).toNat = (e.DCA.getD k default).bits.toNat := by
    simp [toNat32]
  have hEbn : ((e.DCA.getD k default).bits.toUInt32).toNat = (e.DCA.getD k default).bits.toNat := toNat32 _
  have hls1 : LS e (dropL l (e.DCA.getD k default).bits.toUInt32) i o :=
    hls.dropL _ (by omega) (by omega)
  have hsg1 := Sg_dropL (e := e) l (e.DCA.getD k default).bits.toUInt32 i (by omega) (by omega)
  have hlow64 : ∀ x : UInt32, x.toNat < 32 → (l.hold >>> (e.DCA.getD k default).bits.toUInt32.toUInt64).toNat = l.hold.toNat / 2 ^ (e.DCA.getD k default).bits.toNat := by
    intro x _; rw [u64_shr (by omega), hEbn]
  rw [dodist_eq_base]
  dsimp only
  refine Wp.bindO hld ?_
  refine Wp.bindO (shr64_ok (x:=l.hold)
    (n:=(e.DCA.getD k default).bits.toUInt32.toUInt64) (by rw [UInt32.toNat_toUInt64,hEbn]; omega)) ?_
  refine Wp.bindO hld ?_
  generalize e.DCA.getD k default = E at *
  have hsg1' : Sg e (l.hold >>> E.bits.toUInt32.toUInt64).toNat (l.bits - E.bits.toUInt32).toNat i =
      (Sg e l.hold.toNat l.bits.toNat i).drop E.bits.toNat := by
    have := hsg1; rw [hEbn] at this; exact this
  by_cases hb16 : (E.op.toUInt32 &&& 16 != 0) = true
  · simp only [hb16, ite_true]
    have hb16' : E.op &&& 16 ≠ 0 := by
      rw [mask16] at hb16; simpa using hb16
    have hbase : E.op &&& 16 ≠ 0 ∧ ((E.op &&& 15).toNat ≤ 13) ∧ 1 ≤ E.val.toNat := by
      rcases hcl with h | h | h
      · exact h
      · exact absurd h.1 hb16'
      · exact absurd h.1 hb16'
    refine Wp.bindO hld ?_
    have hv : E.val.toUInt32.toNat = E.val.toNat := by simp
    have hv2 := UInt16.toNat_lt E.val
    have hbn := dropL_bits l E.bits.toUInt32 (by omega)
    have key := (dodistBase_result_wp hc A msg m
      { in_ := l.in_, out := l.out, hold := l.hold >>> E.bits.toUInt32.toUInt64, bits := l.bits - E.bits.toUInt32,
        here := l.here, op := E.op.toUInt32 &&& 15, len := l.len, dist := E.val.toUInt32, from_ := l.from_,
        broke := l.broke, againL := l.againL, againD := false } i o (LS.congr hls1 rfl rfl rfl rfl) hA ho hAb
      (by rw [mask15]; exact hbase.2.1) (by rw [hv]; exact hbase.2.2) (by rw [hv]; omega) hlen hbroke
      (by rcases hpull with h | h
          · exact Or.inl h
          · refine Or.inr ⟨h.1, ?_⟩
            show 5 ≤ (l.bits - E.bits.toUInt32).toNat
            have hbn' : (l.bits - E.bits.toUInt32).toNat = l.bits.toNat - E.bits.toNat := by
              rw [u32_toNat_sub (by omega), hEbn]
            omega))
    refine Wp.mono key ?_
    intro l' after result
    obtain ⟨extra,rest,read,copy⟩ := result
    right; right
    refine ⟨hb16',extra,rest,?_,?_⟩
    · rw [mask15,hsg1'] at read
      exact read
    · simpa only [hv] using copy
  · -- not a base: a link or an invalid code
    have hb16' : E.op &&& 16 = 0 := by
      rw [mask16] at hb16; simpa using hb16
    by_cases hb64 : (E.op.toUInt32 &&& 64 == 0) = true
    · simp only [hb16, hb64, ite_true, ite_false, Bool.false_eq_true]
      have hb64' : E.op &&& 64 = 0 := by
        rw [mask64] at hb64; simpa using hb64
      have hlink : 1 ≤ E.op.toNat ∧ E.op.toNat ≤ 15 ∧ e.od + E.val.toNat + 2 ^ E.op.toNat ≤ e.DCA.size := by
        rcases hcl with h | h | h
        · exact absurd hb16' h.1
        · exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
        · exact absurd hb64' h.2
      refine Wp.bindO hld ?_
      have hdc : c.dcode = .ref e.rd e.od := by rw [hc.dcode]; exact e.hdc
      have hop32 : E.op.toUInt32.toNat < 32 := by rw [toNat32]; omega
      refine Wp.bindO (x := Ptr.ref e.rd (e.od + E.val.toNat)) ?_ ?_
      · rw [hdc]
        exact Ptr.add_nat_ok (e.heap_cget_DCA A msg m) (Nat.le_trans (Nat.le_add_right _ _) hlink.2.2)
      refine Wp.bindO (shl32_ok hop32) ?_
      have hlow := hold_low64 (x := l.hold >>> E.bits.toUInt32.toUInt64) (k := E.op.toUInt32) hop32
      have hjlt : (l.hold >>> E.bits.toUInt32.toUInt64).toNat % 2 ^ E.op.toUInt32.toNat < 2 ^ E.op.toNat := by
        rw [toNat32]; exact Nat.mod_lt _ (Nat.pow_pos (by omega))
      generalize hjd : (l.hold >>> E.bits.toUInt32.toUInt64).toNat % 2 ^ E.op.toUInt32.toNat = j at hlow hjlt
      refine Wp.bindO (x := Ptr.ref e.rd (e.od + E.val.toNat + j)) ?_ ?_
      · rw [hlow]
        exact Ptr.add_nat_ok (h := e.heap A msg m) (r := e.rd) (a := e.DCA) (off := e.od + E.val.toNat)
          (n := j) (e.heap_cget_DCA A msg m) (by have := hlink.2.2; omega)
      exact Wp.pure' (Or.inl rfl)
    · simp only [hb16, hb64, ite_false, Bool.false_eq_true]
      obtain ⟨ip, hip⟩ := badData_run hc A msg m "invalid distance code" (by decide +kernel)
      refine Wp.bindE hip (Wp.pure' (Or.inr (Or.inl ⟨hb16',i,Ptr.ref (.str ip) 0,rfl,
        LS.congr hls1 rfl rfl rfl rfl,hsg1',rfl⟩)))

private theorem dodistLoop_result_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32) (l : L) (i o kidx : Nat)
    (hts : DistTableSafe e.DCA e.od e.s0.distbits.toNat) (hk : kidx < 2 ^ e.s0.distbits.toNat)
    (hls : LS e l i o) (hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size) (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hAb : A.size < 2 ^ 63) (hbroke : l.broke = false) (hlen : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    (hhere : l.here = .ref e.rd (e.od + kidx)) (hb15 : 15 ≤ l.bits.toNat)
    (hpull : i + 2 ≤ e.i0 + e.sm0.avail_in.toNat ∨ (i + 1 ≤ e.i0 + e.sm0.avail_in.toNat ∧ 20 ≤ l.bits.toNat)) :
    Wp (cdoWhile (dodist c) (fun l => pure (l.againD, l)) l) (e.heap A msg m) (fun l' h' =>
      ∃ E cb, cb ≤ 15 ∧ DistLook e l.hold.toNat kidx E cb ∧
        DistEnd e A msg m ((Sg e l.hold.toNat l.bits.toNat i).drop cb) i o l.len.toNat E l' h' ∧
        PhysicalOutcome e A msg m (Sg e l.hold.toNat l.bits.toNat i) o l.len.toNat E cb l' h') := by
  obtain ⟨hksz, hlk, hnl⟩ := distRoot hts kidx hk
  have hcl0 := distClass_of (e := e) _ hlk hnl
  have hEd0 : (e.DCA.getD (e.od + kidx) default).bits.toNat + 0 ≤ 15 := by
    by_cases hl : DistLink (e.DCA.getD (e.od + kidx) default)
    · have := (hlk hl).1; omega
    · have := (hnl hl).1; omega
  obtain ⟨l1, h1, e1, hq1⟩ := dodist_pass hc A msg m l i o 0 (e.od + kidx) hls hA ho hAb hbroke hlen hhere hksz
    (by omega) hEd0 hcl0 (by simpa using hpull)
  obtain ⟨E0, hE0⟩ : ∃ E0, e.DCA.getD (e.od + kidx) default = E0 := ⟨_, rfl⟩
  rw [hE0] at hq1 hlk hnl hcl0 hEd0
  rcases hq1 with ⟨hag, hbr, hh, ⟨hl16, hl64⟩, j, hjlt, hjd, hhere1, hls1, hsg1, hb1, hlen1, hout1, hdist1, hagL1⟩ | ⟨hNL, hag, hend⟩
  · -- a link: the second pass ends the block
    subst hh
    have hlink : DistLink E0 := ⟨hl16, hl64⟩
    have hlk' := hlk hlink
    have hleaf := hlk'.2.2.2.2 j hjlt
    have hk2 : e.od + E0.val.toNat + j < e.DCA.size := by
      have := hlk'.2.2.2.1; omega
    have hcl1 : DistClass e (e.DCA.getD (e.od + E0.val.toNat + j) default) := by
      rcases hleaf.2 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    have hb15' : E0.bits.toNat ≤ 15 := hlk'.1
    obtain ⟨l2, h2, e2, hq2⟩ := dodist_pass hc A msg m l1 i o E0.bits.toNat (e.od + E0.val.toNat + j) hls1 hA ho hAb hbr
      (by rw [hlen1]; exact hlen) hhere1 hk2 (by have := hleaf.1; omega) (by omega) hcl1 (by
        rcases hpull with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h.1, by omega⟩)
    rcases hq2 with ⟨hag2, -, -, ⟨hl16', hl64'⟩, -⟩ | hend2
    · rcases hleaf.2 with h | h
      · exact absurd hl16' h.1
      · exact absurd hl64' h.2
    · have physical := Wp.at_run (dodist_result_wp hc A msg m l1 i o E0.bits.toNat
          (e.od+E0.val.toNat+j) hls1 hA ho hAb hbr (by rw [hlen1]; exact hlen) hhere1 hk2
          (by have := hleaf.1; omega) (by omega) hcl1 (by
            rcases hpull with h | h
            · exact Or.inl h
            · exact Or.inr ⟨h.1,by omega⟩)) e2
      have physical' : PhysicalOutcome e A msg m (Sg e l1.hold.toNat l1.bits.toNat i) o l1.len.toNat
          (e.DCA.getD (e.od+E0.val.toNat+j) default)
          (e.DCA.getD (e.od+E0.val.toNat+j) default).bits.toNat l2 h2 := by
        rcases physical with flag | result
        · rw [hend2.2.1] at flag; contradiction
        · exact result
      have c1 : (fun l : L => (pure (l.againD, l) : M (Bool × L))) l1 (e.heap A msg m) = .ok ((true, l1), e.heap A msg m) := by simp [hag]
      have c2 : (fun l : L => (pure (l.againD, l) : M (Bool × L))) l2 h2 = .ok ((false, l2), h2) := by simp [hend2.2.1]
      have e1' : dodist c l (e.heap A msg m) = .ok (l1, e.heap A msg m) := e1
      refine Wp.of_eq (cdoWhile_two e1' c1 e2 c2) ?_
      refine ⟨e.DCA.getD (e.od + E0.val.toNat + j) default, E0.bits.toNat + (e.DCA.getD (e.od + E0.val.toNat + j) default).bits.toNat, by have := hleaf.1; omega, ?_, ?_, ?_⟩
      · refine Or.inr ⟨E0, j, hE0, hlink, hjlt, ?_, rfl, rfl, by have := hleaf.1; omega, ?_⟩
        · rw [hjd]
        · intro hl; rcases hleaf.2 with h | h
          · exact absurd hl.1 h.1
          · exact absurd hl.2 h.2
      · have := hend2
        rw [hlen1] at this
        have hd : (Sg e l.hold.toNat l.bits.toNat i).drop (E0.bits.toNat + (e.DCA.getD (e.od + E0.val.toNat + j) default).bits.toNat) =
            ((Sg e l.hold.toNat l.bits.toNat i).drop E0.bits.toNat).drop (e.DCA.getD (e.od + E0.val.toNat + j) default).bits.toNat := by
          rw [List.drop_drop]
        rw [hd, ← hsg1]
        exact this
      · simpa only [PhysicalOutcome,hlen1,hsg1,List.drop_drop] using physical'
  · -- the first pass ended the block
    have c1 : (fun l : L => (pure (l.againD, l) : M (Bool × L))) l1 h1 = .ok ((false, l1), h1) := by simp [hag]
    have physical := Wp.at_run (dodist_result_wp hc A msg m l i o 0 (e.od+kidx)
      hls hA ho hAb hbroke hlen hhere hksz (by rw [hE0]; omega) (by rw [hE0]; exact hEd0)
      (by rw [hE0]; exact hcl0) (by simpa using hpull)) e1
    rw [hE0] at physical
    have physical' : PhysicalOutcome e A msg m (Sg e l.hold.toNat l.bits.toNat i) o l.len.toNat E0 E0.bits.toNat l1 h1 := by
      rcases physical with flag | result
      · rw [hag] at flag; contradiction
      · exact result
    refine Wp.of_eq (cdoWhile_one e1 c1) ?_
    exact ⟨E0,E0.bits.toNat,by omega,Or.inl ⟨hE0,rfl,hNL⟩,⟨hNL,hag,hend⟩,physical'⟩
private theorem dolenDist_result_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32) (l : L) (i o : Nat)
    (hts : DistTableSafe e.DCA e.od e.s0.distbits.toNat)
    (hls : LS e l i o) (hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size) (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hAb : A.size < 2 ^ 63) (hbroke : l.broke = false) (hlen : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    (hb15 : 15 ≤ l.bits.toNat)
    (hpull : i + 2 ≤ e.i0 + e.sm0.avail_in.toNat ∨ (i + 1 ≤ e.i0 + e.sm0.avail_in.toNat ∧ 20 ≤ l.bits.toNat)) :
    Wp (dolenDist c l) (e.heap A msg m) (fun l' h' =>
      ∃ E cb, cb ≤ 15 ∧ DistLook e l.hold.toNat (l.hold.toNat % 2 ^ e.s0.distbits.toNat) E cb ∧
        DistEnd e A msg m ((Sg e l.hold.toNat l.bits.toNat i).drop cb) i o l.len.toNat E l' h' ∧
        PhysicalOutcome e A msg m (Sg e l.hold.toNat l.bits.toNat i) o l.len.toNat E cb l' h') := by
  unfold dolenDist
  have hdc : c.dcode = .ref e.rd e.od := by rw [hc.dcode]; exact e.hdc
  have hR : e.s0.distbits.toNat < 32 := by have := hts.1; omega
  have hmask : c.dmask.toUInt64.toNat = 2 ^ e.s0.distbits.toNat - 1 := by
    rw [hc.dmask, UInt32.toNat_toUInt64]; exact u32_shl1_sub1 hR
  have hidx := u64_and_mask (x := l.hold) hmask
  have hmod : l.hold.toNat % 2 ^ e.s0.distbits.toNat < 2 ^ e.s0.distbits.toNat :=
    Nat.mod_lt _ (Nat.pow_pos (by omega))
  refine Wp.bindO (x := Ptr.ref e.rd (e.od + l.hold.toNat % 2 ^ e.s0.distbits.toNat)) ?_ ?_
  · rw [hdc, hidx]
    exact Ptr.add_nat_ok (e.heap_cget_DCA A msg m) (by have := hts.2.1; omega)
  · exact Wp.mono (dodistLoop_result_wp hc A msg m { l with here := Ptr.ref e.rd (e.od + l.hold.toNat % 2 ^ e.s0.distbits.toNat) }
      i o _ hts hmod (LS.congr hls rfl rfl rfl rfl) hA ho hAb hbroke hlen rfl hb15 hpull) (fun _ _ h => h)
private theorem distance_extra_limit : ∀ k, k < 30 → distExtras.getD k 0 ≤ 13 := by
  decide +kernel

private theorem distance_extra_mask : ∀ op : UInt8, 16 ≤ op.toNat → op.toNat ≤ 29 →
    (op &&& 15).toNat = op.toNat-16 := by
  apply u8_forall
  decide +kernel

/-- The actual complete distance block selects an independent symbol and
copies the independent match, or retains its exact input on either error. -/
theorem actual_distance_refines_lz77 : Goal.actual_distance_refines_lz77 := by
  intro e c bytes msg mode l input output tableUsed lens ctx locals size room big notBroke len enough pullRoom inv stable flags
  obtain ⟨l',after,run,entry,consumed,bound,look,old,physical⟩ :=
    dolenDist_result_wp ctx bytes msg mode l input output e.hdt locals size room big notBroke len enough pullRoom
  refine ⟨l',after,entry,consumed,run,bound,look,old,?_⟩
  obtain ⟨query,positive,limit,leaf,meaning⟩ := distance_lookup_matches_format e l.hold.toNat
    l.bits.toNat input tableUsed lens entry consumed inv stable flags locals.hH enough look
  unfold Outcome
  dsimp only
  rcases meaning with ⟨noBase,future⟩ | ⟨hasBase,symbol,valid,symbolEntry,codeLength,decoded,extended⟩
  · rcases physical with ⟨_,bad⟩ | ⟨hasBase,_⟩
    · exact Or.inl ⟨noBase,future,bad⟩
    · exact False.elim (hasBase noBase)
  · rcases physical with ⟨noBase,_⟩ | ⟨_,extra,rest,read,copy⟩
    · exact False.elim (hasBase noBase)
    · have entryMeaning := symbolEntry
      unfold SymbolEntry at entryMeaning
      simp only [show DISTS ≠ LENS by decide,ite_false,valid,ite_true] at entryMeaning
      obtain ⟨opValue,baseValue⟩ := entryMeaning
      have extraBound := distance_extra_limit symbol (by omega)
      have mask := distance_extra_mask entry.op (by omega) (by omega)
      have extraValue : (entry.op &&& 15).toNat = distExtras.getD symbol 0 := by
        rw [mask]
        omega
      right
      refine ⟨hasBase,symbol,extra,(Sg e l.hold.toNat l.bits.toNat input).drop consumed,rest,
        valid,symbolEntry,codeLength,decoded,?_,?_⟩
      · rw [extraValue] at read
        exact read
      · simpa only [CopyOutcome,baseValue] using copy

end Zlib.Inffast.Proofs
