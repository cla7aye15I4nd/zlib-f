import ZlibF.Spec.InflateFastBodyToken
import ZlibF.Proof.«inffast.c.length-trace»
import ZlibF.Proof.«inffast.c.length-semantics»
import ZlibF.Proof.«inffast.c.distance-result»

set_option autoImplicit false

namespace Zlib.Inffast.Proofs.BodyTokenProof
open C Zlib.Inffast Zlib.Inffast.Spec Zlib.Inffast.Proofs ZlibF.Spec
open Zlib.Inftrees Zlib.Inftrees.Spec ZlibF.Math.LZ77Copy
open Zlib.Inffast.Spec.BodyToken
open Zlib.Inffast.Spec.LengthTrace
variable {e : Env} {c : Ctx}

private theorem written_length (bytes : Array UInt8) (offset count : Nat)
    (hc : count ≤ offset) (hb : offset ≤ bytes.size) :
    (writtenBytes bytes offset count).length = count := by
  simp only [writtenBytes, List.length_take, List.length_drop, Array.length_toList]
  omega

private theorem written_get (bytes : Array UInt8) (offset count i : Nat) :
    (writtenBytes bytes offset count)[i]? =
      if i < count then bytes[offset - count + i]? else none := by
  simp only [writtenBytes, List.getElem?_take, List.getElem?_drop, Array.getElem?_toList]

private theorem written_set_append (bytes : Array UInt8) (offset count : Nat)
    (value : UInt8) (hc : count ≤ offset) (hb : offset < bytes.size) :
    writtenBytes (bytes.set! offset value) (offset + 1) (count + 1) =
      writtenBytes bytes offset count ++ [value] := by
  apply List.ext_getElem?
  intro i
  rw [written_get, List.getElem?_append, written_length bytes offset count hc (by omega)]
  have hstart : offset + 1 - (count + 1) = offset - count := by omega
  rw [hstart]
  by_cases hi : i < count
  · have hne : offset ≠ offset - count + i := by omega
    simp [hi, show i < count + 1 by omega, written_get, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds, hne]
  · by_cases he : i = count
    · subst i
      have hs : offset - count + count = offset := by omega
      simp [show ¬ count < count by omega, show count < count + 1 by omega, hs,
        Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, hb]
    · have hn : ¬ i < count + 1 := by omega
      have hz : i - count ≠ 0 := by omega
      simp [hi, hn, List.getElem?_singleton, hz]


private theorem length_base_fields (symbol : Nat) (entry : Code)
    (lo : 257 ≤ symbol) (hi : symbol ≤ 285)
    (meaning : DecodeSemantics.SymbolEntry LENS symbol entry) :
    entry.op &&& 16 ≠ 0 ∧
    (entry.op &&& 15).toNat = lengthExtras.getD (symbol - 257) 0 ∧
    entry.val.toNat = lengthBases.getD (symbol - 257) 0 := by
  have extrasBound : ∀ n : Fin 29, lengthExtras.getD n.val 0 ≤ 5 := by decide +kernel
  have bound : lengthExtras.getD (symbol - 257) 0 ≤ 5 := extrasBound ⟨symbol - 257, by omega⟩
  have fields : entry.op.toNat = 16 + lengthExtras.getD (symbol - 257) 0 ∧
      entry.val.toNat = lengthBases.getD (symbol - 257) 0 := by
    simpa only [DecodeSemantics.SymbolEntry, ite_true,
      if_neg (show ¬ symbol < 256 by omega), if_neg (show symbol ≠ 256 by omega), if_pos hi] using meaning
  have mask : ∀ op : UInt8, 16 ≤ op.toNat → op.toNat ≤ 21 →
      op &&& 16 ≠ 0 ∧ (op &&& 15).toNat = op.toNat - 16 := by
    apply u8_forall
    decide +kernel
  have shape := mask entry.op (by omega) (by omega)
  exact ⟨shape.1, by rw [shape.2, fields.1]; omega, fields.2⟩

private theorem literal_symbol (symbol : Nat) (entry : Code) (hi : symbol ≤ 285)
    (meaning : DecodeSemantics.SymbolEntry LENS symbol entry) (literal : entry.op = 0) :
    symbol < 256 ∧ entry.val.toNat = symbol := by
  by_cases small : symbol < 256
  · have fields : entry.op = 0 ∧ entry.val.toNat = symbol := by
      simpa only [DecodeSemantics.SymbolEntry, ite_true, if_pos small] using meaning
    exact ⟨small, fields.2⟩
  · by_cases eob : symbol = 256
    · subst symbol
      have fields : entry.op = 96 ∧ entry.val = 0 := by
        simpa [DecodeSemantics.SymbolEntry] using meaning
      simp [literal] at fields
    · have fields := length_base_fields symbol entry (by omega) hi meaning
      simp [literal] at fields

private theorem base_symbol (symbol : Nat) (entry : Code) (hi : symbol ≤ 285)
    (meaning : DecodeSemantics.SymbolEntry LENS symbol entry) (base : entry.op &&& 16 ≠ 0) :
    257 ≤ symbol := by
  by_cases small : symbol < 256
  · have fields : entry.op = 0 ∧ entry.val.toNat = symbol := by
      simpa only [DecodeSemantics.SymbolEntry, ite_true, if_pos small] using meaning
    simp [fields.1] at base
  · by_cases eob : symbol = 256
    · subst symbol
      have fields : entry.op = 96 ∧ entry.val = 0 := by
        simpa [DecodeSemantics.SymbolEntry] using meaning
      exact False.elim (base (by rw [fields.1]; decide +kernel))
    · omega

private theorem eob_symbol (symbol : Nat) (entry : Code) (hi : symbol ≤ 285)
    (meaning : DecodeSemantics.SymbolEntry LENS symbol entry)
    (nonzero : entry.op ≠ 0) (noBase : entry.op &&& 16 = 0) : symbol = 256 := by
  by_cases small : symbol < 256
  · have fields : entry.op = 0 ∧ entry.val.toNat = symbol := by
      simpa only [DecodeSemantics.SymbolEntry, ite_true, if_pos small] using meaning
    exact False.elim (nonzero fields.1)
  · by_cases eob : symbol = 256
    · exact eob
    · have fields := length_base_fields symbol entry (by omega) hi meaning
      exact False.elim (fields.1 noBase)

private theorem refill_entry_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32) (l : L) (i o s : Nat)
    (hts : DistTableSafe e.DCA e.od e.s0.distbits.toNat)
    (hls : LS e l i o) (hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size) (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hAb : A.size < 2 ^ 63) (hbroke : l.broke = false) (hlen : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    (hs6 : s + 6 ≤ e.i0 + e.sm0.avail_in.toNat) (hT : i ≤ s + 3) (hT3 : i = s + 3 → 4 ≤ l.bits.toNat) :
    Wp (dolenRefill c l) (e.heap A msg m) (fun l' h' =>
      DistanceEntry e c A msg m (Sg e l.hold.toNat l.bits.toNat i) i o l.len.toNat l' h') := by
  unfold dolenRefill
  by_cases h1 : l.bits < 15
  · simp only [h1, ite_true]
    have h1' : l.bits.toNat < 15 := by simpa using UInt32.lt_iff_toNat_lt.mp h1
    have hiin : i < e.i0 + e.sm0.avail_in.toNat := by omega
    refine Wp.bindO (pull_run e _ l i o hls (by omega) hiin (e.heap_bytes_in A msg m)) ?_
    have hl3 := hls.pullL (by omega) hiin
    have hs3 := Sg_pullL hls (by omega) hiin
    have hb3 := pullL_bits l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1)) hls.hb
    have hi2 : i + 1 < e.i0 + e.sm0.avail_in.toNat := by omega
    have hb3' : (pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1))).bits.toNat ≤ 22 := by
      simp only [pullL] at hb3 ⊢; omega
    refine Wp.bindO (pull_run e _ _ (i + 1) o hl3 hb3' hi2 (e.heap_bytes_in A msg m)) ?_
    have hl4 := hl3.pullL hb3' hi2
    have hs4 := Sg_pullL hl3 hb3' hi2
    have hb4 := pullL_bits (pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1))) (e.IN.getD (i + 1) 0)
      (.ref (BRef.blk e.ib) (i + 1 + 1)) hl3.hb
    simp only [pullL] at hb3 hb4
    have pullRoom : i + 1 + 1 + 2 ≤ e.i0 + e.sm0.avail_in.toNat ∨
        (i + 1 + 1 + 1 ≤ e.i0 + e.sm0.avail_in.toNat ∧
          20 ≤ (pullL (pullL l (e.IN.getD i 0) (.ref (.blk e.ib) (i + 1)))
            (e.IN.getD (i + 1) 0) (.ref (.blk e.ib) (i + 1 + 1))).bits.toNat) := by
      by_cases hc3 : i = s + 3
      · right; have := hT3 hc3; simp only [pullL]; omega
      · left; omega
    obtain ⟨l', after, run, _⟩ := dolenDist_wp hc A msg m _ (i + 1 + 1) o hts hl4 hA ho hAb hbroke hlen
      (by simp only [pullL]; omega) pullRoom
    exact Wp.of_eq run ⟨_, i + 1 + 1, by omega, by omega, hl4, hbroke, rfl,
      by simp only [pullL]; omega, pullRoom, hs4.trans hs3, run⟩
  · simp only [h1, ite_false]
    have h1' : 15 ≤ l.bits.toNat := by
      have : ¬ (l.bits.toNat < 15) := fun h => h1 (UInt32.lt_iff_toNat_lt.mpr (by simpa using h))
      omega
    obtain ⟨l', after, run, _⟩ := dolenDist_wp hc A msg m l i o hts hls hA ho hAb hbroke hlen h1' (Or.inl (by omega))
    exact Wp.of_eq run ⟨l, i, by omega, by omega, hls, hbroke, rfl, h1', Or.inl (by omega), rfl, run⟩

private theorem ext_entry_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32) (l : L) (i o s : Nat)
    (hts : DistTableSafe e.DCA e.od e.s0.distbits.toNat)
    (hls : LS e l i o) (hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size) (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hAb : A.size < 2 ^ 63) (hbroke : l.broke = false) (hx : l.op.toNat ≤ 5) (hxb : l.op.toNat ≤ l.bits.toNat)
    (hlen : 3 ≤ l.len.toNat ∧ l.len.toNat + 2 ^ l.op.toNat ≤ 259)
    (hs6 : s + 6 ≤ e.i0 + e.sm0.avail_in.toNat) (hT : i ≤ s + 3)
    (hT3 : i = s + 3 → 4 + l.op.toNat ≤ l.bits.toNat) :
    Wp (dolenExt c l) (e.heap A msg m) (fun l' h' =>
      ∃ lx S1, readBits l.op.toNat (Sg e l.hold.toNat l.bits.toNat i) = some (lx, S1) ∧
        DistanceEntry e c A msg m S1 i o (l.len.toNat + lx) l' h') := by
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
  have hbn := dropL_bits l l.op hxb
  have hrb := readBits_bitsOfNat l.op.toNat l.bits.toNat l.hold.toNat (inBits e i) hxb
  have hsg := Sg_dropL (e := e) l l.op i hxb (by omega)
  refine Wp.mono (refill_entry_wp hc A msg m
    { in_ := l.in_, out := l.out, hold := l.hold >>> l.op.toUInt64, bits := l.bits - l.op, here := l.here, op := l.op,
      len := l.len + (l.hold.toUInt32 &&& (1 <<< l.op) - 1), dist := l.dist, from_ := l.from_, broke := l.broke,
      againL := l.againL, againD := l.againD } i o s hts (LS.congr hls1 rfl rfl rfl rfl) hA ho hAb hbroke
    (by rw [hlen']; omega) hs6 hT (by intro h3; have := hT3 h3; show 4 ≤ (l.bits - l.op).toNat; simp only [dropL] at hbn; omega)) ?_
  intro l' h' hq
  refine ⟨l.hold.toNat % 2 ^ l.op.toNat, Sg e (dropL l l.op).hold.toNat (dropL l l.op).bits.toNat i, ?_, ?_⟩
  · unfold Sg; rw [hrb, dropL_hold l l.op (by omega), dropL_bits l l.op hxb]
  · simp only [hlen'] at hq
    exact hq


private theorem len_entry_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32) (l : L) (i o s : Nat)
    (hts : DistTableSafe e.DCA e.od e.s0.distbits.toNat)
    (hls : LS e l i o) (hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size) (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hAb : A.size < 2 ^ 63) (hbroke : l.broke = false) (hx : l.op.toNat ≤ 5)
    (hlen : 3 ≤ l.len.toNat ∧ l.len.toNat + 2 ^ l.op.toNat ≤ 259)
    (hs6 : s + 6 ≤ e.i0 + e.sm0.avail_in.toNat) (hT : i ≤ s + 2) (hb2 : i = s + 2 → 1 ≤ l.bits.toNat) :
    Wp (dolenLen c l) (e.heap A msg m) (fun l' h' =>
      ∃ i2 lx S1, i ≤ i2 ∧ i2 ≤ i + 1 ∧ readBits l.op.toNat (Sg e l.hold.toNat l.bits.toNat i) = some (lx, S1) ∧
        DistanceEntry e c A msg m S1 i2 o (l.len.toNat + lx) l' h') := by
  unfold dolenLen
  by_cases h0 : l.op != 0
  · simp only [h0, ite_true]
    have h0' : l.op.toNat ≠ 0 := by
      intro h; apply (by simpa using h0 : l.op ≠ 0); exact UInt32.toNat_inj.mp (by simpa using h)
    by_cases h1 : l.bits < l.op
    · simp only [h1, ite_true]
      have h1' : l.bits.toNat < l.op.toNat := UInt32.lt_iff_toNat_lt.mp h1
      have hiin : i < e.i0 + e.sm0.avail_in.toNat := by omega
      refine Wp.bindO (pull_run e _ l i o hls (by omega) hiin (e.heap_bytes_in A msg m)) ?_
      have hl3 := hls.pullL (by omega) hiin
      have hs3 := Sg_pullL hls (by omega) hiin
      have hb3 := pullL_bits l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1)) hls.hb
      refine Wp.mono (ext_entry_wp hc A msg m _ (i + 1) o s hts hl3 hA ho hAb hbroke (by simp only [pullL]; omega)
        (by simp only [pullL] at hb3 ⊢; omega) (by simp only [pullL]; omega) hs6 (by omega)
        (by intro h3; simp only [pullL] at hb3 ⊢; have := hb2 (by omega); omega)) ?_
      intro l' h' hq
      obtain ⟨lx, S1, hr, hrp⟩ := hq
      refine ⟨i + 1, lx, S1, by omega, by omega, ?_, ?_⟩
      · simp only [pullL] at hr hs3 ⊢; rw [hs3] at hr; exact hr
      · simp only [pullL] at hrp ⊢; exact hrp
    · simp only [h1, ite_false]
      have h1' : l.op.toNat ≤ l.bits.toNat := by
        have : ¬ (l.bits.toNat < l.op.toNat) := fun h => h1 (UInt32.lt_iff_toNat_lt.mpr h)
        omega
      refine Wp.mono (ext_entry_wp hc A msg m l i o s hts hls hA ho hAb hbroke hx h1' hlen hs6 (by omega)
        (by intro h3; omega)) ?_
      intro l' h' hq
      obtain ⟨lx, S1, hr, hrp⟩ := hq
      exact ⟨i, lx, S1, by omega, by omega, hr, hrp⟩
  · simp only [h0, ite_false]
    have h0' : l.op.toNat = 0 := by
      have : l.op = 0 := by simpa using h0
      rw [this]; rfl
    refine Wp.mono (refill_entry_wp hc A msg m l i o s hts hls hA ho hAb hbroke ⟨hlen.1, by
      have : 0 < 2 ^ l.op.toNat := Nat.pow_pos (by omega)
      omega⟩ hs6 (by omega) (by intro h3; omega)) ?_
    intro l' h' hq
    refine ⟨i, 0, Sg e l.hold.toNat l.bits.toNat i, by omega, by omega, ?_, ?_⟩
    · rw [h0']; rfl
    · simpa using hq

set_option maxHeartbeats 1000000 in
private theorem pass_entry_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32)
    (l : L) (i o s d k : Nat) (hls : LS e l i o) (hAsz : A.size = e.A0.size)
    (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat) (hbroke : l.broke = false)
    (hs6 : s + 6 ≤ e.i0 + e.sm0.avail_in.toNat) (hsi : s ≤ i) (hT : i ≤ s + 2)
    (hb15 : 15 ≤ l.bits.toNat + d) (hbi2 : i = s + 2 → 16 ≤ l.bits.toNat + d)
    (hhere : l.here = .ref e.rl k) (hk : k < e.LCA.size)
    (hEb : (e.LCA.getD k default).bits.toNat ≤ l.bits.toNat)
    (hEd : (e.LCA.getD k default).bits.toNat + d ≤ 15)
    (hcl : (LenLink (e.LCA.getD k default) ∧ LinkOK LenLeaf e.LCA e.ol (e.LCA.getD k default)) ∨
      LenLeaf d (e.LCA.getD k default)) :
    Wp (dolen c l) (e.heap A msg m) (fun l' h' =>
      (l'.againL = true ∧ l'.broke = false ∧ h' = e.heap A msg m ∧
        LenLink (e.LCA.getD k default) ∧
        ∃ j, j < 2 ^ (e.LCA.getD k default).op.toNat ∧
          l'.here = .ref e.rl (e.ol + (e.LCA.getD k default).val.toNat + j) ∧
          j = (l.hold.toNat / 2 ^ (e.LCA.getD k default).bits.toNat) % 2 ^ (e.LCA.getD k default).op.toNat ∧
          LS e l' i o ∧ l'.bits.toNat = l.bits.toNat - (e.LCA.getD k default).bits.toNat ∧
          Sg e l'.hold.toNat l'.bits.toNat i = (Sg e l.hold.toNat l.bits.toNat i).drop (e.LCA.getD k default).bits.toNat) ∨
      EndWithDistanceEntry e c A msg m ((Sg e l.hold.toNat l.bits.toNat i).drop (e.LCA.getD k default).bits.toNat)
        i o (e.LCA.getD k default) l' h') := by
  have hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size := by rw [hAsz]; exact e.hAsz
  have hAb : A.size < 2 ^ 63 := by rw [hAsz]; exact e.hAbig
  have hkE : e.LCA[k]'hk = e.LCA.getD k default := by simp [Array.getD_eq_getD_getElem?, hk]
  have hld : OkOn (e.heap A msg m) (Ptr.load l.here) (e.LCA.getD k default) := by
    rw [hhere, ← hkE]; exact Ptr.load_ok (e.heap_cget_LCA A msg m) hk
  have hEbn : (e.LCA.getD k default).bits.toUInt32.toNat = (e.LCA.getD k default).bits.toNat := toNat32 _
  have hEb64 : (e.LCA.getD k default).bits.toUInt32.toUInt64.toNat = (e.LCA.getD k default).bits.toNat := by simp [toNat32]
  have hls1 := hls.dropL (e.LCA.getD k default).bits.toUInt32 (by omega) (by omega)
  have hsg1 := Sg_dropL (e := e) l (e.LCA.getD k default).bits.toUInt32 i (by omega) (by omega)
  rw [dolen_eq_len]
  dsimp only
  refine Wp.bindO hld ?_
  refine Wp.bindO (shr64_ok (x := l.hold) (by omega)) ?_
  refine Wp.bindO hld ?_
  generalize e.LCA.getD k default = E at *
  have hsg1' : Sg e (l.hold >>> E.bits.toUInt32.toUInt64).toNat (l.bits - E.bits.toUInt32).toNat i =
      (Sg e l.hold.toNat l.bits.toNat i).drop E.bits.toNat := by
    simpa only [dropL, hEbn] using hsg1
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
    · have hop : E.op = 0 := by rw [mask0] at hz; simpa using hz
      refine Wp.pure' (Or.inr ?_)
      refine ⟨?_, ?_⟩
      · refine ⟨?_, rfl, Or.inl ⟨hop, hbroke, ?_, hsg1', rfl⟩⟩
        · intro link; exact link.1 hop
        · exact ⟨hls.hin, rfl, hls.hi0, hls.hi1, by have := hls.ho0; omega, hls1.hb, hls1.hH, hls1.hacc⟩
      · intro bad; exact False.elim (bad.1 hop)
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
      obtain ⟨l', h', run, tail⟩ := len_entry_wp hc A msg m stage i o s e.hdt
        (LS.congr hls1 rfl rfl rfl rfl) hA ho hAb hbroke
        (by dsimp [stage]; rw [mask15]; exact hbase.1)
        (by simpa [stage, mask15] using hbase.2) hs6 hT
        (by intro hi; have := hbi2 hi; show 1 ≤ (l.bits - E.bits.toUInt32).toNat
            rw [u32_toNat_sub (by omega), hEbn]; omega)
      have oldRun := dolenLen_wp hc A msg m stage i o s e.hdt
        (LS.congr hls1 rfl rfl rfl rfl) hA ho hAb hbroke
        (by dsimp [stage]; rw [mask15]; exact hbase.1)
        (by simpa [stage, mask15] using hbase.2) hs6 hT
        (by intro hi; have := hbi2 hi; show 1 ≤ (l.bits - E.bits.toUInt32).toNat
            rw [u32_toNat_sub (by omega), hEbn]; omega)
      have result := Wp.at_run oldRun run
      have hag : l'.againL = false := by simpa [stage] using dolenLen_againL run
      refine Wp.of_eq run (Or.inr ?_)
      refine ⟨?_, ?_⟩
      · refine ⟨?_, hag, Or.inr (Or.inl ⟨hz', hb16', ?_⟩)⟩
        · intro link; exact hb16' link.2.1
        · obtain ⟨i', extra, rest, hi, hi1, read, refill⟩ := result
          refine ⟨i', extra, rest, hi, hi1, ?_, ?_⟩
          · simpa only [stage, mask15, hsg1'] using read
          · simpa only [stage, UInt16.toNat_toUInt32] using refill
      · intro _
        obtain ⟨i', extra, rest, hi, hi1, read, distance⟩ := tail
        refine ⟨i', extra, rest, hi, hi1, ?_, ?_⟩
        · simpa only [stage, mask15, hsg1'] using read
        · simpa only [stage, UInt16.toNat_toUInt32] using distance
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
        refine Wp.pure' (Or.inl ⟨rfl, hbroke, rfl, hl, j, hjlt, rfl, ?_,
          LS.congr hls1 rfl rfl rfl rfl, ?_, hsg1'⟩)
        · have hshift : (l.hold >>> E.bits.toUInt32.toUInt64).toNat = l.hold.toNat / 2 ^ E.bits.toNat := by
            rw [u64_shr (by omega), hEbn]
          simpa only [hshift, toNat32] using hjd.symm
        · rw [u32_toNat_sub (by omega), hEbn]
      · simp only [hz, hb16, hb64, ite_false, Bool.false_eq_true]
        by_cases hb32 : (E.op.toUInt32 &&& 32 != 0) = true
        · simp only [hb32, ite_true]
          refine Wp.bindE (e.heap_ldstate hc A msg m) ?_
          refine Wp.bindE (e.heap_stmode hc A msg m TYPE _ rfl) ?_
          have hb64' : E.op &&& 64 ≠ 0 := by rw [mask64] at hb64; simpa using hb64
          have hb32' : E.op &&& 32 ≠ 0 := by rw [mask32] at hb32; simpa using hb32
          refine Wp.pure' (Or.inr ?_)
          refine ⟨?_, ?_⟩
          · refine ⟨?_, rfl, Or.inr (Or.inr (Or.inl ⟨hz', hb16', hb64', hb32', rfl,
              LS.congr hls1 rfl rfl rfl rfl, hsg1', rfl⟩))⟩
            intro link; exact hb64' link.2.2
          · intro bad; exact False.elim (bad.2 hb16')
        · simp only [hb32, ite_false, Bool.false_eq_true]
          obtain ⟨ip, hip⟩ := badData_run hc A msg m "invalid literal/length code" (by decide +kernel)
          refine Wp.bindE hip ?_
          have hb64' : E.op &&& 64 ≠ 0 := by rw [mask64] at hb64; simpa using hb64
          have hb32' : E.op &&& 32 = 0 := by rw [mask32] at hb32; simpa using hb32
          refine Wp.pure' (Or.inr ?_)
          refine ⟨?_, ?_⟩
          · refine ⟨?_, rfl, Or.inr (Or.inr (Or.inr ⟨hz', hb16', hb64', hb32', rfl,
              LS.congr hls1 rfl rfl rfl rfl, hsg1', .ref (.str ip) 0, rfl⟩))⟩
            intro link; exact hb64' link.2.2
          · intro bad; exact False.elim (bad.2 hb16')

private theorem loop_entry_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32)
    (l : L) (i o s kidx : Nat) (hls : LS e l i o) (hAsz : A.size = e.A0.size)
    (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat) (hbroke : l.broke = false)
    (hs6 : s + 6 ≤ e.i0 + e.sm0.avail_in.toNat) (hsi : s ≤ i) (hT : i ≤ s + 2)
    (hb15 : 15 ≤ l.bits.toNat) (hbi2 : i = s + 2 → 16 ≤ l.bits.toNat)
    (hk : kidx < 2 ^ e.s0.lenbits.toNat) (hhere : l.here = .ref e.rl (e.ol + kidx)) :
    Wp (cdoWhile (dolen c) (fun l => pure (l.againL, l)) l) (e.heap A msg m)
      (fun l' h' => ∃ entry consumed, consumed ≤ 15 ∧
        LengthSemantics.Look e l.hold.toNat kidx entry consumed ∧
        EndWithDistanceEntry e c A msg m ((Sg e l.hold.toNat l.bits.toNat i).drop consumed) i o entry l' h') := by
  obtain ⟨hR, hsz, hall⟩ := e.hlt
  have hksz : e.ol + kidx < e.LCA.size := by omega
  have hclass : (LenLink (e.LCA.getD (e.ol + kidx) default) ∧
      LinkOK LenLeaf e.LCA e.ol (e.LCA.getD (e.ol + kidx) default)) ∨
      LenLeaf 0 (e.LCA.getD (e.ol + kidx) default) := by
    have hh := hall kidx hk
    by_cases hl : LenLink (e.LCA.getD (e.ol + kidx) default)
    · rw [if_pos hl] at hh; exact Or.inl ⟨hl, hh⟩
    · rw [if_neg hl] at hh; exact Or.inr hh
  have hEd0 : (e.LCA.getD (e.ol + kidx) default).bits.toNat + 0 ≤ 15 := by
    rcases hclass with h | h
    · exact h.2.1
    · exact h.1
  obtain ⟨l1, h1, run1, result1⟩ := pass_entry_wp hc A msg m l i o s 0 (e.ol + kidx) hls hAsz ho hbroke
    hs6 hsi hT (by omega) (by intro hi; have := hbi2 hi; omega) hhere hksz (by omega) hEd0 hclass
  generalize firstCell : e.LCA.getD (e.ol + kidx) default = first at result1 hclass hEd0
  rcases result1 with ⟨again1, broke1, heap1, link1, j, jLt, here1, jEq, locals1, bits1, stream1⟩ | end1
  · subst heap1
    have links : LinkOK LenLeaf e.LCA e.ol first := by
      rcases hclass with h | h
      · exact h.2
      · rcases h.2 with h0 | h | h
        · exact False.elim (link1.1 h0)
        · exact False.elim (h.1 link1.2.1)
        · exact False.elim (h.2 link1.2.2)
    have leaf := links.2.2.2.2 j jLt
    have secondIn : e.ol + first.val.toNat + j < e.LCA.size := by have := links.2.2.2.1; omega
    obtain ⟨l2, h2, run2, result2⟩ := pass_entry_wp hc A msg m l1 i o s first.bits.toNat
      (e.ol + first.val.toNat + j) locals1 hAsz ho broke1 hs6 hsi hT
      (by omega) (by intro hi; have := hbi2 hi; omega) here1 secondIn
      (by have := leaf.1; omega) leaf.1 (Or.inr leaf)
    rcases result2 with ⟨_, _, _, link2, _⟩ | end2
    · rcases leaf.2 with h0 | h | h
      · exact False.elim (link2.1 h0)
      · exact False.elim (h.1 link2.2.1)
      · exact False.elim (h.2 link2.2.2)
    · have cond1 : (fun q : L => (pure (q.againL, q) : M (Bool × L))) l1 (e.heap A msg m) =
          .ok ((true, l1), e.heap A msg m) := by simp [again1]
      have cond2 : (fun q : L => (pure (q.againL, q) : M (Bool × L))) l2 h2 =
          .ok ((false, l2), h2) := by simp [end2.1.2.1]
      refine Wp.of_eq (cdoWhile_two run1 cond1 run2 cond2)
        ⟨e.LCA.getD (e.ol + first.val.toNat + j) default,
          first.bits.toNat + (e.LCA.getD (e.ol + first.val.toNat + j) default).bits.toNat,
          by have := leaf.1; omega, ?_, ?_⟩
      · exact Or.inr ⟨first, j, firstCell, link1, jLt, jEq, rfl, rfl, by have := leaf.1; omega, end2.1.1⟩
      · simpa only [stream1, List.drop_drop] using end2
  · have cond1 : (fun q : L => (pure (q.againL, q) : M (Bool × L))) l1 h1 =
        .ok ((false, l1), h1) := by simp [end1.1.2.1]
    exact Wp.of_eq (cdoWhile_one run1 cond1)
      ⟨first, first.bits.toNat, by omega, Or.inl ⟨firstCell, rfl, end1.1.1⟩, end1⟩

private theorem root_entry_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32)
    (l : L) (i o s : Nat) (hls : LS e l i o) (hAsz : A.size = e.A0.size)
    (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat) (hbroke : l.broke = false)
    (hs6 : s + 6 ≤ e.i0 + e.sm0.avail_in.toNat) (hsi : s ≤ i) (hT : i ≤ s + 2)
    (hb15 : 15 ≤ l.bits.toNat) (hbi2 : i = s + 2 → 16 ≤ l.bits.toNat) :
    Wp (do
      let here ← c.lcode.add (l.hold &&& c.lmask.toUInt64).toNat
      cdoWhile (dolen c) (fun l => pure (l.againL, l)) {l with here}) (e.heap A msg m)
      (fun l' h' => ∃ entry consumed, consumed ≤ 15 ∧
        LengthSemantics.Look e l.hold.toNat (l.hold.toNat % 2 ^ e.s0.lenbits.toNat) entry consumed ∧
        EndWithDistanceEntry e c A msg m ((Sg e l.hold.toNat l.bits.toNat i).drop consumed) i o entry l' h') := by
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
  · exact loop_entry_wp hc A msg m _ i o s _ (LS.congr hls rfl rfl rfl rfl)
      hAsz ho hbroke hs6 hsi hT hb15 hbi2 hmod rfl

private theorem body_entry_wp (e : Env) (c : Ctx) (A : Array UInt8) (msg : BPtr) (m : UInt32)
    (l : L) (i o : Nat) (hp : StepPre e c A l i o) :
    Wp (inflate_fast_body c l) (e.heap A msg m) (fun l' h' =>
      Sg e (ready e l i).1.hold.toNat (ready e l i).1.bits.toNat (ready e l i).2 =
        Sg e l.hold.toNat l.bits.toNat i ∧
      ∃ entry consumed, consumed ≤ 15 ∧
        LengthSemantics.Look e (ready e l i).1.hold.toNat
          ((ready e l i).1.hold.toNat % 2 ^ e.s0.lenbits.toNat) entry consumed ∧
        EndWithDistanceEntry e c A msg m ((Sg e (ready e l i).1.hold.toNat (ready e l i).1.bits.toNat
          (ready e l i).2).drop consumed) (ready e l i).2 o entry l' h') := by
  have hc := hp.context
  have hls := hp.locals
  have hAsz := hp.outputSize
  have hi6 := hp.inputRoom
  have ho258 := hp.outputRoom
  have hbroke := hp.notStopped
  have trace : Wp (inflate_fast_body c l) (e.heap A msg m) (fun l' h' =>
      Sg e (ready e l i).1.hold.toNat (ready e l i).1.bits.toNat (ready e l i).2 =
        Sg e l.hold.toNat l.bits.toNat i ∧
      ∃ entry consumed, consumed ≤ 15 ∧
        LengthSemantics.Look e (ready e l i).1.hold.toNat
          ((ready e l i).1.hold.toNat % 2 ^ e.s0.lenbits.toNat) entry consumed ∧
        EndWithDistanceEntry e c A msg m ((Sg e (ready e l i).1.hold.toNat (ready e l i).1.bits.toNat
          (ready e l i).2).drop consumed) (ready e l i).2 o entry l' h') := by
    unfold inflate_fast_body
    by_cases h1 : l.bits < 15
    · simp only [ready, h1, ite_true]
      have hb : l.bits.toNat < 15 := by simpa using UInt32.lt_iff_toNat_lt.mp h1
      have hiin : i < e.i0 + e.sm0.avail_in.toNat := by omega
      refine Wp.bindO (pull_run e _ l i o hls (by omega) hiin (e.heap_bytes_in A msg m)) ?_
      have hl1 := hls.pullL (by omega) hiin
      have stream1 := Sg_pullL hls (by omega) hiin
      have hb1 := pullL_bits l (e.IN.getD i 0) (.ref (.blk e.ib) (i + 1)) hls.hb
      have hi2 : i + 1 < e.i0 + e.sm0.avail_in.toNat := by omega
      have hb1' : (pullL l (e.IN.getD i 0) (.ref (.blk e.ib) (i + 1))).bits.toNat ≤ 22 := by
        simp only [pullL] at hb1 ⊢; omega
      refine Wp.bindO (pull_run e _ _ (i + 1) o hl1 hb1' hi2 (e.heap_bytes_in A msg m)) ?_
      have hl2 := hl1.pullL hb1' hi2
      have stream2 := Sg_pullL hl1 hb1' hi2
      have hb2 := pullL_bits (pullL l (e.IN.getD i 0) (.ref (.blk e.ib) (i + 1)))
        (e.IN.getD (i + 1) 0) (.ref (.blk e.ib) (i + 1 + 1)) hl1.hb
      refine Wp.mono (root_entry_wp hc A msg m _ (i + 1 + 1) o i hl2 hAsz ho258 hbroke hi6 (by omega) (by omega)
        (by simp only [pullL] at hb1 hb2 ⊢; omega)
        (by intro _; simp only [pullL] at hb1 hb2 ⊢; omega)) ?_
      intro l' h' result
      exact ⟨stream2.trans stream1, result⟩
    · simp only [ready, h1, ite_false]
      have hb : 15 ≤ l.bits.toNat := by
        have : ¬ l.bits.toNat < 15 := fun h => h1 (UInt32.lt_iff_toNat_lt.mpr (by simpa using h))
        omega
      exact Wp.mono (root_entry_wp hc A msg m l i o i hls hAsz ho258 hbroke hi6 (by omega) (by omega) hb (by omega))
        (fun _ _ result => ⟨by trivial, result⟩)
  exact trace

private theorem ready_locals (e : Env) (c : Ctx) (A : Array UInt8)
    (l : L) (i o : Nat) (pre : StepPre e c A l i o) :
    LS e (ready e l i).1 (ready e l i).2 o ∧ 15 ≤ (ready e l i).1.bits.toNat := by
  by_cases short : l.bits < 15
  · have bitsLt : l.bits.toNat < 15 := by simpa using UInt32.lt_iff_toNat_lt.mp short
    have in1 : i < e.i0 + e.sm0.avail_in.toNat := by have := pre.inputRoom; omega
    have first := pre.locals.pullL (by omega) in1
    have bits1 := pullL_bits l (e.IN.getD i 0) (.ref (.blk e.ib) (i + 1)) pre.locals.hb
    have bound1 : (pullL l (e.IN.getD i 0) (.ref (.blk e.ib) (i + 1))).bits.toNat ≤ 22 := by
      simp only [pullL] at bits1 ⊢; omega
    have in2 : i + 1 < e.i0 + e.sm0.avail_in.toNat := by have := pre.inputRoom; omega
    have second := first.pullL bound1 in2
    have bits2 := pullL_bits (pullL l (e.IN.getD i 0) (.ref (.blk e.ib) (i + 1)))
      (e.IN.getD (i + 1) 0) (.ref (.blk e.ib) (i + 1 + 1)) first.hb
    simp only [ready, short, ite_true]
    constructor
    · simpa only [Nat.add_assoc] using second
    · simp only [pullL] at bits1 bits2 ⊢; omega
  · simp only [ready, short, ite_false]
    refine ⟨pre.locals, ?_⟩
    have large : ¬ l.bits.toNat < 15 := fun h => short (UInt32.lt_iff_toNat_lt.mpr (by simpa using h))
    omega



theorem actual_body_refines_token : BodyToken.Goal.actual_body_refines_token := by
  intro e c bytes msg mode l input output L D pre tables
  obtain ⟨l', after, run, sameStream, entry, consumed, limit, look, oldEnd, tail⟩ :=
    body_entry_wp e c bytes msg mode l input output pre
  have safe := Wp.at_run (inflate_fast_body_step_safe e c bytes msg mode l input output pre) run
  obtain ⟨readyLS, enough⟩ := ready_locals e c bytes l input output pre
  obtain ⟨usedL, invL⟩ := tables.lengthTable
  obtain ⟨query, positive, codeBound, leaf, semantic⟩ := length_lookup_matches_format e
    (ready e l input).1.hold.toNat (ready e l input).1.bits.toNat (ready e l input).2
    usedL L entry consumed invL tables.lengthStable tables.lengthFlags readyLS.hH enough look
  rw [sameStream] at semantic oldEnd tail
  have acceptedMeaning (accepts : FastTableFlags.FastLeafAccepted LENS entry) :
      ∃ symbol, symbol ≤ 285 ∧ DecodeSemantics.SymbolEntry LENS symbol entry ∧
        consumed = L.getD symbol 0 ∧
        decodeSym L (Sg e l.hold.toNat l.bits.toNat input) =
          some (symbol, (Sg e l.hold.toNat l.bits.toNat input).drop consumed) := by
    rcases semantic with ⟨rejects, _⟩ | ⟨_, symbol, valid, meaning, length, decoded, _⟩
    · exact False.elim (rejects accepts)
    · exact ⟨symbol, valid, meaning, length, decoded⟩
  have bgLe : e.bg ≤ output := Nat.le_trans e.bg_le pre.locals.ho0
  have outSize : output < bytes.size := by
    have := pre.outputRoom
    have endSize := e.hAsz
    rw [← pre.outputSize] at endSize
    omega
  rcases oldEnd.2.2 with literal | length | eob | invalid
  · obtain ⟨hop, stopped, locals, rest, heap⟩ := literal
    have accepts : FastTableFlags.FastLeafAccepted LENS entry := by
      simp [FastTableFlags.FastLeafAccepted, hop]
    obtain ⟨symbol, valid, meaning, _, decoded⟩ := acceptedMeaning accepts
    obtain ⟨small, value⟩ := literal_symbol symbol entry valid meaning hop
    refine ⟨l', after, (ready e l input).2, output + 1, bytes.set! output entry.val.toUInt8,
      msg, mode, run, safe, locals, by simp, heap, Or.inl ⟨stopped, ?_⟩⟩
    have written := written_set_append bytes output (output - e.bg) entry.val.toUInt8 (by omega) outSize
    have count : output + 1 - e.bg = output - e.bg + 1 := by omega
    rw [count, written, rest]
    have byte : entry.val.toUInt8 = symbol.toUInt8 := by
      apply UInt8.toNat_inj.mp
      simp only [UInt16.toNat_toUInt8, UInt8.toNat_ofNat']
      rw [value]
    rw [byte]
    exact Token.Step.literal decoded small
  · obtain ⟨nonzero, hasBase, _⟩ := length
    have accepts : FastTableFlags.FastLeafAccepted LENS entry := by
      simp [FastTableFlags.FastLeafAccepted, hasBase]
    obtain ⟨symbol, valid, meaning, _, decoded⟩ := acceptedMeaning accepts
    have lower := base_symbol symbol entry valid meaning hasBase
    obtain ⟨_, extraBits, baseValue⟩ := length_base_fields symbol entry lower valid meaning
    obtain ⟨input2, xl, r2, _, _, readLength, distEntry⟩ := tail ⟨nonzero, hasBase⟩
    obtain ⟨dl, di, _, _, dlLocals, dlRunning, dlLength, dlBits, dlRoom, dlSource, dlRun⟩ := distEntry
    have lenBase : 3 ≤ entry.val.toNat ∧
        entry.val.toNat + 2 ^ (entry.op &&& 15).toNat ≤ 259 := by
      rcases leaf.2 with literal | base | invalid
      · exact False.elim (nonzero literal)
      · exact base.2.2
      · exact False.elim (hasBase invalid.1)
    have xlBound := readBits_value_lt readLength
    have dlLen : 3 ≤ dl.len.toNat ∧ dl.len.toNat ≤ 258 := by omega
    obtain ⟨usedD, invD⟩ := tables.distanceTable
    obtain ⟨dl', dh, distanceEntry, dc, distanceRun, _, _, _, outcome⟩ := actual_distance_refines_lz77
      e c bytes msg mode dl di output usedD D pre.context dlLocals
      (by rw [pre.outputSize]; exact e.hAsz) pre.outputRoom
      (by rw [pre.outputSize]; exact e.hAbig) dlRunning dlLen dlBits dlRoom
      invD tables.distanceStable tables.distanceFlags
    have sameRun := distanceRun.symm.trans dlRun
    cases sameRun
    unfold DistanceResult.Outcome at outcome
    dsimp only at outcome
    rw [dlSource] at outcome
    rw [extraBits] at readLength
    rcases outcome with ⟨noBase, rejected, di', errorMsg, stopped, locals, rest, heap⟩ |
      ⟨base, distanceSymbol, xd, codeRest, finalRest, distanceValid, distanceMeaning, _,
        distanceDecoded, readDistance, copy⟩
    · refine ⟨l', after, di', output, bytes, errorMsg, BAD, run, safe, locals, rfl, heap,
        Or.inr (Or.inr ⟨stopped, rfl, rfl, ?_⟩)⟩
      exact Token.Rejected.distance decoded lower valid readLength rejected
    · by_cases tooFar : (MatchHistory.saved e.W e.s0.wsize.toNat e.s0.wnext.toNat
          e.s0.whave.toNat e.woff).length + (writtenBytes bytes output (output - e.bg)).length <
          distBases.getD distanceSymbol 0 + xd
      · rw [if_pos tooFar] at copy
        obtain ⟨di', errorMsg, stopped, locals, rest, heap⟩ := copy
        refine ⟨l', after, di', output, bytes, errorMsg, BAD, run, safe, locals, rfl, heap,
          Or.inr (Or.inr ⟨stopped, rfl, rfl, ?_⟩)⟩
        exact Token.Rejected.tooFar decoded lower valid readLength distanceDecoded distanceValid
          readDistance (by simpa only [List.length_append] using tooFar)
      · rw [if_neg tooFar] at copy
        obtain ⟨di', stopped, locals, rest, heap, written⟩ := copy
        refine ⟨l', after, di', output + dl.len.toNat, _, msg, mode, run, safe, locals,
          matchArr_size _ _ _ _ _ _ _ _ _, heap, Or.inl ⟨stopped, ?_⟩⟩
        have count : output + dl.len.toNat - e.bg = output - e.bg + dl.len.toNat := by omega
        rw [count, written, rest, dlLength, baseValue]
        exact Token.Step.copy decoded lower valid readLength distanceDecoded distanceValid readDistance
          (by simp only [List.length_append]; omega)
  · obtain ⟨nonzero, noBase, invalidFlag, endFlag, stopped, locals, rest, heap⟩ := eob
    have accepts : FastTableFlags.FastLeafAccepted LENS entry := by
      simp [FastTableFlags.FastLeafAccepted, invalidFlag, endFlag]
    obtain ⟨symbol, valid, meaning, _, decoded⟩ := acceptedMeaning accepts
    have symbolIsEnd := eob_symbol symbol entry valid meaning nonzero noBase
    subst symbol
    refine ⟨l', after, (ready e l input).2, output, bytes, msg, TYPE,
      run, safe, locals, rfl, heap, Or.inr (Or.inl ⟨stopped, rfl, ?_⟩)⟩
    rw [rest]
    exact Token.Step.eob decoded
  · obtain ⟨nonzero, noBase, invalidFlag, noEnd, stopped, locals, rest, errorMsg, heap⟩ := invalid
    have rejects : ¬ FastTableFlags.FastLeafAccepted LENS entry := by
      simp [FastTableFlags.FastLeafAccepted, nonzero, noBase, noEnd]
    have future : ∀ more : List Bool,
        ¬ ∃ symbol remaining, decodeSym L (Sg e l.hold.toNat l.bits.toNat input ++ more) =
          some (symbol, remaining) ∧ symbol ≤ 285 := by
      rcases semantic with ⟨_, allFuture⟩ | ⟨accepts, _⟩
      · exact allFuture
      · exact False.elim (rejects accepts)
    refine ⟨l', after, (ready e l input).2, output, bytes, errorMsg, BAD,
      run, safe, locals, rfl, heap, Or.inr (Or.inr ⟨stopped, rfl, rfl, ?_⟩)⟩
    exact Token.Rejected.length future

end Zlib.Inffast.Proofs.BodyTokenProof

namespace Zlib.Inffast.Proofs
/-- The actual fast body emits one independent token, ends the block,
or rejects the current token without emitting output. -/
theorem actual_body_refines_token : Spec.BodyToken.Goal.actual_body_refines_token :=
  BodyTokenProof.actual_body_refines_token
end Zlib.Inffast.Proofs
