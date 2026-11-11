import ZlibF.Spec.InflateFastBodyOrigin
import ZlibF.Proof.«inffast.c.origin»
import ZlibF.Proof.«inffast.c.body»
import ZlibF.Proof.«inffast.c.distance-origin»

/-!
# The actual fast body preserves its source-bit origin

Every source refill and drop updates the exact suffix invariant. Copying
and control fields preserve the buffered bits. No decoding-table semantic
contract is assumed; the existing table safety domain is retained.
-/

namespace Zlib.Inffast.Proofs.BodyOriginProof
open C Zlib.Inffast Zlib.Inffast.Spec Zlib.Inffast.Proofs ZlibF.Spec

variable {e : Env} {c : Ctx}

private theorem pull_origin {l : L} {i o used : Nat}
    (hl : LS e l i o) (origin : Origin.Inv e l.hold.toNat l.bits.toNat i used)
    (buffer : l.bits.toNat ≤ 22) (available : i < e.i0 + e.sm0.avail_in.toNat) :
    Origin.Inv e (pullL l (e.IN.getD i 0) (.ref (.blk e.ib) (i + 1))).hold.toNat
      (pullL l (e.IN.getD i 0) (.ref (.blk e.ib) (i + 1))).bits.toNat (i + 1) used := by
  have next := pull_preserves_origin e l.hold.toNat l.bits.toNat i used origin available
  simpa only [pullL_hold l _ _ hl.hb hl.hH, pullL_bits l _ _ hl.hb] using next

private theorem drop_origin {l : L} {i o used : Nat} (count : UInt32)
    (hl : LS e l i o) (origin : Origin.Inv e l.hold.toNat l.bits.toNat i used)
    (available : count.toNat ≤ l.bits.toNat) :
    Origin.Inv e (dropL l count).hold.toNat (dropL l count).bits.toNat i (used + count.toNat) := by
  exact (actual_drop_preserves_origin e e.h0 l i o used count hl origin available).2.2

private theorem refill_origin_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32) (l : L) (i o s used : Nat)
    (hls : LS e l i o) (hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size) (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hAb : A.size < 2 ^ 63) (hbroke : l.broke = false) (hlen : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    (hs6 : s + 6 ≤ e.i0 + e.sm0.avail_in.toNat) (hT : i ≤ s + 3) (hT3 : i = s + 3 → 4 ≤ l.bits.toNat)
    (origin : Origin.Inv e l.hold.toNat l.bits.toNat i used)
    (hfr : e.InputFrame A i) :
    Wp (dolenRefill c l) (e.heap A msg m) (fun l' _ =>
      ∃ i' o' used', LS e l' i' o' ∧ Origin.Inv e l'.hold.toNat l'.bits.toNat i' used' ∧ used ≤ used') := by
  unfold dolenRefill
  by_cases h1 : l.bits < 15
  · simp only [h1, ite_true]
    have h1' : l.bits.toNat < 15 := by simpa using UInt32.lt_iff_toNat_lt.mp h1
    have hiin : i < e.i0 + e.sm0.avail_in.toNat := by omega
    refine Wp.bindO (pull_run e _ l i o hls (by omega) hiin (e.heap_bytes_in A msg m) (hfr.get (by omega) (by omega))) ?_
    have hl3 := hls.pullL (by omega) hiin
    have origin3 := pull_origin hls origin (by omega) hiin
    have hb3 := pullL_bits l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1)) hls.hb
    have hi2 : i + 1 < e.i0 + e.sm0.avail_in.toNat := by omega
    have hb3' : (pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1))).bits.toNat ≤ 22 := by
      simp only [pullL] at hb3 ⊢; omega
    refine Wp.bindO (pull_run e _ _ (i + 1) o hl3 hb3' hi2 (e.heap_bytes_in A msg m) (hfr.get (by omega) (by omega))) ?_
    have hl4 := hl3.pullL hb3' hi2
    have origin4 := pull_origin hl3 origin3 hb3' hi2
    have hb4 := pullL_bits (pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1))) (e.IN.getD (i + 1) 0)
      (.ref (BRef.blk e.ib) (i + 1 + 1)) hl3.hb
    simp only [pullL] at hb3 hb4
    obtain ⟨lr, hr, run, _, endOrigin⟩ := actual_distance_block_preserves_origin e c A msg m _ (i + 1 + 1) o used
      hc hl4 hA ho hAb hbroke hlen (by simp only [pullL]; omega) (by
        by_cases hc3 : i = s + 3
        · right; have := hT3 hc3; simp only [pullL]; omega
        · left; omega) origin4 (hfr.mono (by omega))
    exact Wp.of_eq run endOrigin
  · simp only [h1, ite_false]
    have h1' : 15 ≤ l.bits.toNat := by
      have : ¬ (l.bits.toNat < 15) := fun h => h1 (UInt32.lt_iff_toNat_lt.mpr (by simpa using h))
      omega
    obtain ⟨lr, hr, run, _, endOrigin⟩ := actual_distance_block_preserves_origin e c A msg m l i o used
      hc hls hA ho hAb hbroke hlen h1' (Or.inl (by omega)) origin hfr
    exact Wp.of_eq run endOrigin

private theorem ext_origin_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32) (l : L) (i o s used : Nat)
    (hls : LS e l i o) (hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size) (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hAb : A.size < 2 ^ 63) (hbroke : l.broke = false) (hx : l.op.toNat ≤ 5) (hxb : l.op.toNat ≤ l.bits.toNat)
    (hlen : 3 ≤ l.len.toNat ∧ l.len.toNat + 2 ^ l.op.toNat ≤ 259)
    (hs6 : s + 6 ≤ e.i0 + e.sm0.avail_in.toNat) (hT : i ≤ s + 3) (hT3 : i = s + 3 → 4 + l.op.toNat ≤ l.bits.toNat)
    (origin : Origin.Inv e l.hold.toNat l.bits.toNat i used)
    (hfr : e.InputFrame A i) :
    Wp (dolenExt c l) (e.heap A msg m) (fun l' _ =>
      ∃ i' o' used', LS e l' i' o' ∧ Origin.Inv e l'.hold.toNat l'.bits.toNat i' used' ∧ used ≤ used') := by
  unfold dolenExt
  have hxs : l.op.toNat < 32 := by omega
  refine Wp.bindO (shl32_ok hxs) ?_
  dsimp only
  have hlow := hold_low32 (x := l.hold) (k := l.op) hxs
  have hlowlt : l.hold.toNat % 2 ^ l.op.toNat < 2 ^ l.op.toNat := Nat.mod_lt _ (Nat.pow_pos (by omega))
  have hpow : 0 < 2 ^ l.op.toNat := Nat.pow_pos (by omega)
  have hlen' : (l.len + (l.hold.toUInt32 &&& (1 <<< l.op) - 1)).toNat = l.len.toNat + l.hold.toNat % 2 ^ l.op.toNat := by
    rw [u32_toNat_add (by rw [hlow]; omega), hlow]
  refine Wp.bindO (shr64_ok (x := l.hold) (n := l.op.toUInt64) (by rw [UInt32.toNat_toUInt64]; omega)) ?_
  have hls1 : LS e (dropL l l.op) i o := hls.dropL l.op hxb (by omega)
  have origin1 := drop_origin l.op hls origin hxb
  have hbn := dropL_bits l l.op hxb
  refine Wp.mono (refill_origin_wp hc A msg m
    { in_ := l.in_, out := l.out, hold := l.hold >>> l.op.toUInt64, bits := l.bits - l.op, here := l.here, op := l.op,
      len := l.len + (l.hold.toUInt32 &&& (1 <<< l.op) - 1), dist := l.dist, from_ := l.from_, broke := l.broke,
      againL := l.againL, againD := l.againD } i o s (used + l.op.toNat) (LS.congr hls1 rfl rfl rfl rfl) hA ho hAb hbroke
    (by rw [hlen']; omega) hs6 hT (by intro h3; have := hT3 h3; show 4 ≤ (l.bits - l.op).toNat; simp only [dropL] at hbn; omega)
    origin1 (hfr.mono (by omega))) ?_
  intro l' h' result
  obtain ⟨i', o', used', locals, finalOrigin, mono⟩ := result
  exact ⟨i', o', used', locals, finalOrigin, by omega⟩

private theorem len_origin_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32) (l : L) (i o s used : Nat)
    (hls : LS e l i o) (hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size) (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hAb : A.size < 2 ^ 63) (hbroke : l.broke = false) (hx : l.op.toNat ≤ 5)
    (hlen : 3 ≤ l.len.toNat ∧ l.len.toNat + 2 ^ l.op.toNat ≤ 259)
    (hs6 : s + 6 ≤ e.i0 + e.sm0.avail_in.toNat) (hT : i ≤ s + 2) (hb2 : i = s + 2 → 1 ≤ l.bits.toNat)
    (origin : Origin.Inv e l.hold.toNat l.bits.toNat i used)
    (hfr : e.InputFrame A i) :
    Wp (dolenLen c l) (e.heap A msg m) (fun l' _ =>
      ∃ i' o' used', LS e l' i' o' ∧ Origin.Inv e l'.hold.toNat l'.bits.toNat i' used' ∧ used ≤ used') := by
  unfold dolenLen
  by_cases h0 : l.op != 0
  · simp only [h0, ite_true]
    have h0' : l.op.toNat ≠ 0 := by
      intro h; apply (by simpa using h0 : l.op ≠ 0); exact UInt32.toNat_inj.mp (by simpa using h)
    by_cases h1 : l.bits < l.op
    · simp only [h1, ite_true]
      have h1' : l.bits.toNat < l.op.toNat := UInt32.lt_iff_toNat_lt.mp h1
      have hiin : i < e.i0 + e.sm0.avail_in.toNat := by omega
      refine Wp.bindO (pull_run e _ l i o hls (by omega) hiin (e.heap_bytes_in A msg m) (hfr.get (by omega) (by omega))) ?_
      have hl3 := hls.pullL (by omega) hiin
      have origin3 := pull_origin hls origin (by omega) hiin
      have hb3 := pullL_bits l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1)) hls.hb
      exact ext_origin_wp hc A msg m _ (i + 1) o s used hl3 hA ho hAb hbroke (by simp only [pullL]; omega)
        (by simp only [pullL] at hb3 ⊢; omega) (by simp only [pullL]; omega) hs6 (by omega)
        (by intro h3; simp only [pullL] at hb3 ⊢; have := hb2 (by omega); omega) origin3 (hfr.mono (by omega))
    · simp only [h1, ite_false]
      have h1' : l.op.toNat ≤ l.bits.toNat := by
        have : ¬ (l.bits.toNat < l.op.toNat) := fun h => h1 (UInt32.lt_iff_toNat_lt.mpr h)
        omega
      exact ext_origin_wp hc A msg m l i o s used hls hA ho hAb hbroke hx h1' hlen hs6 (by omega)
        (by intro h3; omega) origin (hfr.mono (by omega))
  · simp only [h0, ite_false]
    exact refill_origin_wp hc A msg m l i o s used hls hA ho hAb hbroke ⟨hlen.1, by
      have : 0 < 2 ^ l.op.toNat := Nat.pow_pos (by omega)
      omega⟩ hs6 (by omega) (by intro h3; omega) origin (hfr.mono (by omega))

set_option maxHeartbeats 1000000 in
/-- One actual length-table pass either follows its one permitted link or
establishes the reviewed body postcondition. -/
private theorem pass_origin_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32)
    (l : L) (i o s d k used : Nat) (hls : LS e l i o) (hAsz : A.size = e.A0.size)
    (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat) (hbroke : l.broke = false)
    (hs6 : s + 6 ≤ e.i0 + e.sm0.avail_in.toNat) (hsi : s ≤ i) (hT : i ≤ s + 2)
    (hb15 : 15 ≤ l.bits.toNat + d) (hbi2 : i = s + 2 → 16 ≤ l.bits.toNat + d)
    (hhere : l.here = .ref e.rl k) (hk : k < e.LCA.size)
    (hEb : (e.LCA.getD k default).bits.toNat ≤ l.bits.toNat)
    (hEd : (e.LCA.getD k default).bits.toNat + d ≤ 15)
    (hcl : (LenLink (e.LCA.getD k default) ∧ LinkOK LenLeaf e.LCA e.ol (e.LCA.getD k default)) ∨
      LenLeaf d (e.LCA.getD k default))
    (origin : Origin.Inv e l.hold.toNat l.bits.toNat i used)
    (hfr : e.InputFrame A i) :
    Wp (dolen c l) (e.heap A msg m) (fun l' h' =>
      ((l'.againL = true ∧ l'.broke = false ∧ h' = e.heap A msg m ∧
        LenLink (e.LCA.getD k default) ∧
        ∃ j, j < 2 ^ (e.LCA.getD k default).op.toNat ∧
          l'.here = .ref e.rl (e.ol + (e.LCA.getD k default).val.toNat + j) ∧
          LS e l' i o ∧ l'.bits.toNat = l.bits.toNat - (e.LCA.getD k default).bits.toNat) ∨
      StepPost e A msg m s o l' h') ∧
      ∃ i' o' used', LS e l' i' o' ∧ Origin.Inv e l'.hold.toNat l'.bits.toNat i' used' ∧ used ≤ used') := by
  have hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size := by rw [hAsz]; exact e.hAsz
  have hAb : A.size < 2 ^ 63 := by rw [hAsz]; exact e.hAbig
  have hkE : e.LCA[k]'hk = e.LCA.getD k default := by simp [Array.getD_eq_getD_getElem?, hk]
  have hld : OkOn (e.heap A msg m) (Ptr.load l.here) (e.LCA.getD k default) := by
    rw [hhere, ← hkE]; exact Ptr.load_ok (e.heap_cget_LCA A msg m) hk
  have hEbn : (e.LCA.getD k default).bits.toUInt32.toNat = (e.LCA.getD k default).bits.toNat := toNat32 _
  have hEb64 : (e.LCA.getD k default).bits.toUInt32.toUInt64.toNat = (e.LCA.getD k default).bits.toNat := by simp [toNat32]
  have hls1 := hls.dropL (e.LCA.getD k default).bits.toUInt32 (by omega) (by omega)
  have origin1 := drop_origin (e.LCA.getD k default).bits.toUInt32 hls origin (by omega)
  rw [dolen_eq_len]
  dsimp only
  refine Wp.bindO hld ?_
  refine Wp.bindO (shr64_ok (x := l.hold) (by omega)) ?_
  refine Wp.bindO hld ?_
  generalize e.LCA.getD k default = E at *
  by_cases hz : (E.op.toUInt32 == 0) = true
  · simp only [hz, ite_true]
    refine Wp.bindO hld ?_
    have hst : store8 l.out E.val.toUInt8 (e.heap A msg m) =
        .ok ((), e.heap (A.set! o E.val.toUInt8) msg m) := by
      rw [hls.hout, ← e.heap_put A (A.set! o E.val.toUInt8) msg m]
      exact Ptr.store_ok (e.heap_bytes_ob A msg m) (e.heap_ro_ob A msg m) (by omega)
    refine Wp.bindE hst ?_
    refine Wp.bindO (x := Ptr.ref (BRef.blk e.ob) (o + 1)) ?_ ?_
    · rw [hls.hout]
      exact Ptr.add_nat_ok (e.heap_bytes_ob _ msg m) (by simp; omega)
    · refine Wp.pure' ⟨Or.inr ?_, ?_⟩
      · refine ⟨i, o + 1, A.set! o E.val.toUInt8, msg, m, ?_, hsi, by omega, by omega, by omega,
          by simp, rfl, rfl, ?_, ?_, ?_⟩
        · exact ⟨hls.hin, rfl, hls.hi0, hls.hi1, by have := hls.ho0; omega, hls1.hb, hls1.hH, hls1.hacc⟩
        · intro j hj
          have hne : o ≠ j := by omega
          simp [Array.set!, hne]
        · intro _; exact ⟨by omega, rfl, rfl⟩
        · intro h; simp [hbroke] at h
      · refine ⟨i, o + 1, used + E.bits.toUInt32.toNat, ?_, origin1, by omega⟩
        exact ⟨hls.hin, rfl, hls.hi0, hls.hi1, by have := hls.ho0; omega, hls1.hb, hls1.hH, hls1.hacc⟩
  · have hz' : E.op ≠ 0 := by rw [mask0] at hz; simpa using hz
    by_cases hb16 : (E.op.toUInt32 &&& 16 != 0) = true
    · simp only [hz, hb16, ite_true, ite_false, Bool.false_eq_true]
      have hb16' : E.op &&& 16 ≠ 0 := by rw [mask16] at hb16; simpa using hb16
      have hbase : (E.op &&& 15).toNat ≤ 5 ∧ 3 ≤ E.val.toNat ∧
          E.val.toNat + 2 ^ (E.op &&& 15).toNat ≤ 259 := by
        rcases hcl with h | h
        · exact False.elim (hb16' h.1.2.1)
        · rcases h.2 with h0 | h | h
          · exact False.elim (hz' h0)
          · exact h.2
          · exact False.elim (hb16' h.1)
      refine Wp.bindO hld ?_
      let stage : L :=
        { in_ := l.in_, out := l.out, hold := l.hold >>> E.bits.toUInt32.toUInt64, bits := l.bits - E.bits.toUInt32,
          here := l.here, op := E.op.toUInt32 &&& 15, len := E.val.toUInt32, dist := l.dist, from_ := l.from_,
          broke := l.broke, againL := false, againD := l.againD }
      have stageLocals : LS e stage i o := LS.congr hls1 rfl rfl rfl rfl
      have stageOrigin : Origin.Inv e stage.hold.toNat stage.bits.toNat i (used + E.bits.toUInt32.toNat) := origin1
      have stageExtra : stage.op.toNat ≤ 5 := by dsimp [stage]; rw [mask15]; exact hbase.1
      have stageLength : 3 ≤ stage.len.toNat ∧ stage.len.toNat + 2 ^ stage.op.toNat ≤ 259 := by
        simpa [stage, mask15] using hbase.2
      have stageBits : i = s + 2 → 1 ≤ stage.bits.toNat := by
        intro hi
        have := hbi2 hi
        dsimp [stage]
        rw [u32_toNat_sub (by omega), hEbn]
        omega
      obtain ⟨l', h', run, outOrigin⟩ := len_origin_wp hc A msg m stage i o s (used + E.bits.toUInt32.toNat)
        stageLocals hA ho hAb hbroke stageExtra stageLength hs6 hT stageBits stageOrigin (hfr.mono (by omega))
      have step := Wp.at_run (dolenLen_step_wp hc A msg m stage i o s stageLocals hAsz ho
        hbroke rfl stageExtra stageLength hs6 hsi hT stageBits (hfr.mono (by omega))) run
      refine Wp.of_eq run ⟨Or.inr step, ?_⟩
      obtain ⟨i', o', used', locals', origin', mono⟩ := outOrigin
      exact ⟨i', o', used', locals', origin', by omega⟩
    · have hb16' : E.op &&& 16 = 0 := by rw [mask16] at hb16; simpa using hb16
      by_cases hb64 : (E.op.toUInt32 &&& 64 == 0) = true
      · simp only [hz, hb16, hb64, ite_true, ite_false, Bool.false_eq_true]
        have hb64' : E.op &&& 64 = 0 := by rw [mask64] at hb64; simpa using hb64
        have hl : LenLink E := ⟨hz', hb16', hb64'⟩
        have hlk : LinkOK LenLeaf e.LCA e.ol E := by
          rcases hcl with h | h
          · exact h.2
          · rcases h.2 with h0 | h | h
            · exact False.elim (hz' h0)
            · exact False.elim (h.1 hb16')
            · exact False.elim (h.2 hb64')
        refine Wp.bindO hld ?_
        have hlc : c.lcode = .ref e.rl e.ol := by rw [hc.lcode]; exact e.hlc
        have hop32 : E.op.toUInt32.toNat < 32 := by rw [toNat32]; have := hlk.2.2.1; omega
        refine Wp.bindO (x := Ptr.ref e.rl (e.ol + E.val.toNat)) ?_ ?_
        · rw [hlc]
          exact Ptr.add_nat_ok (h := e.heap A msg m) (r := e.rl) (a := e.LCA) (off := e.ol)
            (n := E.val.toNat) (e.heap_cget_LCA A msg m)
            (Nat.le_trans (Nat.le_add_right _ _) hlk.2.2.2.1)
        refine Wp.bindO (shl32_ok hop32) ?_
        have hlow := hold_low64 (x := l.hold >>> E.bits.toUInt32.toUInt64) (k := E.op.toUInt32) hop32
        have hjlt : (l.hold >>> E.bits.toUInt32.toUInt64).toNat % 2 ^ E.op.toUInt32.toNat < 2 ^ E.op.toNat := by
          rw [toNat32]; exact Nat.mod_lt _ (Nat.pow_pos (by omega))
        generalize hjd : (l.hold >>> E.bits.toUInt32.toUInt64).toNat % 2 ^ E.op.toUInt32.toNat = j at hlow hjlt
        refine Wp.bindO (x := Ptr.ref e.rl (e.ol + E.val.toNat + j)) ?_ ?_
        · rw [hlow]
          exact Ptr.add_nat_ok (h := e.heap A msg m) (r := e.rl) (a := e.LCA) (off := e.ol + E.val.toNat)
            (n := j) (e.heap_cget_LCA A msg m) (by have := hlk.2.2.2.1; omega)
        refine Wp.pure' ⟨Or.inl ⟨rfl, hbroke, rfl, hl, j, hjlt, rfl,
          LS.congr hls1 rfl rfl rfl rfl, ?_⟩,
          i, o, used + E.bits.toUInt32.toNat, LS.congr hls1 rfl rfl rfl rfl, origin1, by omega⟩
        rw [u32_toNat_sub (by omega), hEbn]
      · simp only [hz, hb16, hb64, ite_false, Bool.false_eq_true]
        by_cases hb32 : (E.op.toUInt32 &&& 32 != 0) = true
        · simp only [hb32, ite_true]
          refine Wp.bindE (e.heap_ldstate hc A msg m) ?_
          refine Wp.bindE (e.heap_stmode hc A msg m TYPE _ rfl) ?_
          refine Wp.pure' ⟨Or.inr ?_, i, o, used + E.bits.toUInt32.toNat,
            LS.congr hls1 rfl rfl rfl rfl, origin1, by omega⟩
          refine ⟨i, o, A, msg, TYPE, LS.congr hls1 rfl rfl rfl rfl, hsi, by omega, by omega, by omega,
            rfl, rfl, rfl, (fun _ _ => rfl), ?_, (fun _ => Or.inl rfl)⟩
          intro h; cases h
        · simp only [hb32, ite_false, Bool.false_eq_true]
          obtain ⟨ip, hip⟩ := badData_run hc A msg m "invalid literal/length code" (by decide +kernel)
          refine Wp.bindE hip ?_
          refine Wp.pure' ⟨Or.inr ?_, i, o, used + E.bits.toUInt32.toNat, LS.congr hls1 rfl rfl rfl rfl, origin1, by omega⟩
          refine ⟨i, o, A, .ref (BRef.str ip) 0, BAD, LS.congr hls1 rfl rfl rfl rfl, hsi, by omega, by omega, by omega,
            rfl, rfl, rfl, (fun _ _ => rfl), ?_, (fun _ => Or.inr rfl)⟩
          intro h; cases h

/-- The actual `dolen` root/link loop ends after at most two passes. -/
private theorem loop_origin_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32)
    (l : L) (i o s kidx used : Nat) (hls : LS e l i o) (hAsz : A.size = e.A0.size)
    (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat) (hbroke : l.broke = false)
    (hs6 : s + 6 ≤ e.i0 + e.sm0.avail_in.toNat) (hsi : s ≤ i) (hT : i ≤ s + 2)
    (hb15 : 15 ≤ l.bits.toNat) (hbi2 : i = s + 2 → 16 ≤ l.bits.toNat)
    (hk : kidx < 2 ^ e.s0.lenbits.toNat) (hhere : l.here = .ref e.rl (e.ol + kidx))
    (origin : Origin.Inv e l.hold.toNat l.bits.toNat i used)
    (hfr : e.InputFrame A i) :
    Wp (cdoWhile (dolen c) (fun l => pure (l.againL, l)) l) (e.heap A msg m)
      (fun l' h' => StepPost e A msg m s o l' h' ∧
        ∃ i' o' used', LS e l' i' o' ∧ Origin.Inv e l'.hold.toNat l'.bits.toNat i' used' ∧ used ≤ used') := by
  have hts := e.hlt
  obtain ⟨hR, hsz, hall⟩ := hts
  have hksz : e.ol + kidx < e.LCA.size := by omega
  have hclass : (LenLink (e.LCA.getD (e.ol + kidx) default) ∧
      LinkOK LenLeaf e.LCA e.ol (e.LCA.getD (e.ol + kidx) default)) ∨
      LenLeaf 0 (e.LCA.getD (e.ol + kidx) default) := by
    have hh := hall kidx hk
    by_cases hl : LenLink (e.LCA.getD (e.ol + kidx) default)
    · rw [ite_eq_left hl] at hh; exact Or.inl ⟨hl, hh⟩
    · rw [ite_eq_right hl] at hh; exact Or.inr hh
  have hEd0 : (e.LCA.getD (e.ol + kidx) default).bits.toNat + 0 ≤ 15 := by
    rcases hclass with h | h
    · exact h.2.1
    · exact h.1
  obtain ⟨l1, h1, e1, hq1, origin1⟩ := pass_origin_wp hc A msg m l i o s 0 (e.ol + kidx) used hls hAsz ho hbroke
    hs6 hsi hT (by omega) (by intro hi; have := hbi2 hi; omega) hhere hksz (by omega) hEd0 hclass origin (hfr.mono (by omega))
  generalize hE0 : e.LCA.getD (e.ol + kidx) default = E0 at hq1 hclass hEd0
  rcases hq1 with ⟨hag, hbr, hh, hlink, j, hjlt, hhere1, hls1, hb1⟩ | hend
  · subst hh
    obtain ⟨i1, o1, used1, locals1, O1, mono1⟩ := origin1
    have i1eq : i1 = i := (Ptr.ref.inj (locals1.hin.symm.trans hls1.hin)).2
    have o1eq : o1 = o := (Ptr.ref.inj (locals1.hout.symm.trans hls1.hout)).2
    subst i1 o1
    have hlk : LinkOK LenLeaf e.LCA e.ol E0 := by
      rcases hclass with h | h
      · exact h.2
      · rcases h.2 with h0 | h | h
        · exact False.elim (hlink.1 h0)
        · exact False.elim (h.1 hlink.2.1)
        · exact False.elim (h.2 hlink.2.2)
    have hleaf := hlk.2.2.2.2 j hjlt
    have hk2 : e.ol + E0.val.toNat + j < e.LCA.size := by have := hlk.2.2.2.1; omega
    obtain ⟨l2, h2, e2, hq2, origin2⟩ := pass_origin_wp hc A msg m l1 i o s E0.bits.toNat (e.ol + E0.val.toNat + j) used1
      hls1 hAsz ho hbr hs6 hsi hT (by omega) (by intro hi; have := hbi2 hi; omega)
      hhere1 hk2 (by have := hleaf.1; omega) hleaf.1 (Or.inr hleaf) O1 (hfr.mono (by omega))
    rcases hq2 with ⟨_, _, _, hl2, _⟩ | hend2
    · rcases hleaf.2 with h0 | h | h
      · exact False.elim (hl2.1 h0)
      · exact False.elim (h.1 hl2.2.1)
      · exact False.elim (h.2 hl2.2.2)
    · have c1 : (fun l : L => (pure (l.againL, l) : M (Bool × L))) l1 (e.heap A msg m) =
          .ok ((true, l1), e.heap A msg m) := by simp [hag]
      have c2 : (fun l : L => (pure (l.againL, l) : M (Bool × L))) l2 h2 =
          .ok ((false, l2), h2) := by simp [StepPost.againL hend2]
      refine Wp.of_eq (cdoWhile_two e1 c1 e2 c2) ⟨hend2, ?_⟩
      obtain ⟨i2, o2, used2, locals2, O2, mono2⟩ := origin2
      exact ⟨i2, o2, used2, locals2, O2, by omega⟩
  · have c1 : (fun l : L => (pure (l.againL, l) : M (Bool × L))) l1 h1 =
        .ok ((false, l1), h1) := by simp [StepPost.againL hend]
    exact Wp.of_eq (cdoWhile_one e1 c1) ⟨hend, origin1⟩


/-- Root-table lookup followed by the actual length root/link loop. -/
private theorem root_origin_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32)
    (l : L) (i o s used : Nat) (hls : LS e l i o) (hAsz : A.size = e.A0.size)
    (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat) (hbroke : l.broke = false)
    (hs6 : s + 6 ≤ e.i0 + e.sm0.avail_in.toNat) (hsi : s ≤ i) (hT : i ≤ s + 2)
    (hb15 : 15 ≤ l.bits.toNat) (hbi2 : i = s + 2 → 16 ≤ l.bits.toNat)
    (origin : Origin.Inv e l.hold.toNat l.bits.toNat i used)
    (hfr : e.InputFrame A i) :
    Wp (do
      let here ← c.lcode.add (l.hold &&& c.lmask.toUInt64).toNat
      cdoWhile (dolen c) (fun l => pure (l.againL, l)) {l with here})
      (e.heap A msg m) (fun l' h' => StepPost e A msg m s o l' h' ∧
        ∃ i' o' used', LS e l' i' o' ∧ Origin.Inv e l'.hold.toNat l'.bits.toNat i' used' ∧ used ≤ used') := by
  have hlc : c.lcode = .ref e.rl e.ol := by rw [hc.lcode]; exact e.hlc
  have hR : e.s0.lenbits.toNat < 32 := by have := e.hlt.1; omega
  have hmask : c.lmask.toUInt64.toNat = 2 ^ e.s0.lenbits.toNat - 1 := by
    rw [hc.lmask, UInt32.toNat_toUInt64]; exact u32_shl1_sub1 hR
  have hidx := u64_and_mask (x := l.hold) hmask
  have hmod : l.hold.toNat % 2 ^ e.s0.lenbits.toNat < 2 ^ e.s0.lenbits.toNat :=
    Nat.mod_lt _ (Nat.pow_pos (by omega))
  refine Wp.bindO (x := Ptr.ref e.rl (e.ol + l.hold.toNat % 2 ^ e.s0.lenbits.toNat)) ?_ ?_
  · rw [hlc, hidx]
    exact Ptr.add_nat_ok (e.heap_cget_LCA A msg m) (by have := e.hlt.2.1; omega)
  · exact loop_origin_wp hc A msg m _ i o s _ used (LS.congr hls rfl rfl rfl rfl) hAsz ho hbroke
      hs6 hsi hT hb15 hbi2 hmod rfl origin hfr


/-- Every source path retains the original body postcondition and an exact
source suffix; accepted table-symbol semantics are a separate obligation. -/
theorem actual_body_preserves_origin : BodyOrigin.Goal.actual_body_preserves_origin := by
  intro e c A msg m l i o used hp origin
  have hfr := hp.inputFrame
  rcases hp with ⟨hc, hls, hAsz, hi6, ho258, hbroke⟩
  change Wp (inflate_fast_body c l) (e.heap A msg m) (fun l' h' => StepPost e A msg m i o l' h' ∧
    ∃ i' o' used', LS e l' i' o' ∧ Origin.Inv e l'.hold.toNat l'.bits.toNat i' used' ∧ used ≤ used')
  unfold inflate_fast_body
  by_cases h1 : l.bits < 15
  · simp only [h1, ite_true]
    have hb : l.bits.toNat < 15 := by simpa using UInt32.lt_iff_toNat_lt.mp h1
    have hiin : i < e.i0 + e.sm0.avail_in.toNat := by omega
    refine Wp.bindO (pull_run e _ l i o hls (by omega) hiin (e.heap_bytes_in A msg m) (hfr.get (by omega) (by omega))) ?_
    have hl1 := hls.pullL (by omega) hiin
    have origin1 := pull_origin hls origin (by omega) hiin
    have hb1 := pullL_bits l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1)) hls.hb
    have hi2 : i + 1 < e.i0 + e.sm0.avail_in.toNat := by omega
    have hb1' : (pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1))).bits.toNat ≤ 22 := by
      simp only [pullL] at hb1 ⊢; omega
    refine Wp.bindO (pull_run e _ _ (i + 1) o hl1 hb1' hi2 (e.heap_bytes_in A msg m) (hfr.get (by omega) (by omega))) ?_
    have hl2 := hl1.pullL hb1' hi2
    have origin2 := pull_origin hl1 origin1 hb1' hi2
    have hb2 := pullL_bits (pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1)))
      (e.IN.getD (i + 1) 0) (.ref (BRef.blk e.ib) (i + 1 + 1)) hl1.hb
    exact root_origin_wp hc A msg m _ (i + 1 + 1) o i used hl2 hAsz ho258 hbroke hi6 (by omega) (by omega)
      (by simp only [pullL] at hb1 hb2 ⊢; omega)
      (by intro _; simp only [pullL] at hb1 hb2 ⊢; omega) origin2 (hfr.mono (by omega))
  · simp only [h1, ite_false]
    have hb : 15 ≤ l.bits.toNat := by
      have : ¬ l.bits.toNat < 15 := fun h => h1 (UInt32.lt_iff_toNat_lt.mpr (by simpa using h))
      omega
    exact root_origin_wp hc A msg m l i o i used hls hAsz ho258 hbroke hi6 (by omega) (by omega) hb (by omega) origin (hfr.mono (by omega))

end Zlib.Inffast.Proofs.BodyOriginProof

namespace Zlib.Inffast.Proofs
open Zlib.Inffast.Spec
/-- The entire actual body retains the exact entry-stream origin on every exit. -/
theorem actual_body_preserves_origin : BodyOrigin.Goal.actual_body_preserves_origin :=
  BodyOriginProof.actual_body_preserves_origin
end Zlib.Inffast.Proofs
