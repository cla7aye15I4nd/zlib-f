import ZlibF.Proof.«inffast.c.progress»

/-!
# inffast.c: a nonterminal fast call strictly consumes input bits

`FastProgress` (`inffast.c.progress`) gives output progress. `inflateBack` needs input progress
instead, because its `ROOM()` resets the output room. `FastConsumes` states it on the actual
returned records: the bits held plus eight times the bytes left never grow, and they strictly fall
when the call does not end in `TYPE` or `BAD`.

Strictness needs `LenLeavesPositive`: every literal/length leaf reads at least one bit. Each body
then drops at least one bit of its length code; the rest of the body never takes back bits
(`dolenLen_step_led`, read off the bit stream `Sg`). The global ledger `LS.hacc` turns the local
strict drop of the last body into the strict inequality of the whole call.
-/

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inffast.Spec ZlibF.Spec

/-- A complete fast call never adds held-plus-unread input bits, and strictly consumes them unless
it ends in `TYPE` or `BAD`. The state and stream are the actual records on the returned heap. -/
def FastConsumes {α : Bool} (e : EnvG α) (after : Heap) : Prop :=
  ∃ stream state, e.r.get after = some stream ∧ after.istates e.stid = some state ∧
    state.bits.toNat + 8 * stream.avail_in.toNat ≤ e.s0.bits.toNat + 8 * e.sm0.avail_in.toNat ∧
    (state.mode ≠ TYPE → state.mode ≠ BAD →
      state.bits.toNat + 8 * stream.avail_in.toNat < e.s0.bits.toNat + 8 * e.sm0.avail_in.toNat)

theorem consume_readBits_length : ∀ (n : Nat) (inp rest : List Bool) (v : Nat),
    readBits n inp = some (v, rest) → rest.length + n = inp.length
  | 0, inp, rest, v, h => by
    simp only [readBits, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    simp
  | n + 1, [], rest, v, h => by simp [readBits] at h
  | n + 1, b :: r, rest, v, h => by
    simp only [readBits] at h
    cases hr : readBits n r with
    | none => simp [hr] at h
    | some p =>
      obtain ⟨v', r'⟩ := p
      simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
      have := consume_readBits_length n r r' v' hr
      rw [← h.2]
      simp only [List.length_cons]
      omega

theorem consume_bytesToBits_length (a : List UInt8) : (bytesToBits a).length = 8 * a.length := by
  induction a with
  | nil => rfl
  | cons x rest ih =>
    simp only [bytesToBits, List.flatMap_cons, List.length_append] at ih ⊢
    rw [ih]
    simp [byteBits]
    omega

variable {α : Bool} {e : EnvG α} {c : Ctx}

/-- The length of the bit stream of a state: the held bits and eight bits per unread byte. -/
theorem Sg_length (H b j : Nat) :
    (Sg e H b j).length = b + 8 * (e.i0 + e.sm0.avail_in.toNat - j) := by
  have hsz := e.hINsz
  unfold Sg inBits
  rw [List.length_append, bitsOfNat_length, consume_bytesToBits_length]
  simp only [List.length_take, List.length_drop, Array.length_toList]
  omega

/-- A shorter bit stream is a smaller ledger `bits + 8 * (end - input)`. -/
theorem ledger_of_Sg {H b j H' b' j' : Nat} (hj : j ≤ e.i0 + e.sm0.avail_in.toNat)
    (hj' : j' ≤ e.i0 + e.sm0.avail_in.toNat)
    (hle : (Sg e H' b' j').length ≤ (Sg e H b j).length) : b' + 8 * j ≤ b + 8 * j' := by
  rw [Sg_length, Sg_length] at hle
  omega

/-- The length branch never takes bits back: from its entry at input offset `i`, a continuing
result holds no more bits than were held plus eight per byte read. -/
theorem dolenLen_step_led (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32)
    (l : L) (i o s : Nat) (hls : LS e l i o) (hAsz : A.size = e.A0.size)
    (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hbroke : l.broke = false) (hagain : l.againL = false) (hx : l.op.toNat ≤ 5)
    (hlen : 3 ≤ l.len.toNat ∧ l.len.toNat + 2 ^ l.op.toNat ≤ 259)
    (hs6 : s + 6 ≤ e.i0 + e.sm0.avail_in.toNat) (hsi : s ≤ i) (hT : i ≤ s + 2)
    (hb2 : i = s + 2 → 1 ≤ l.bits.toNat)
    (hfr : e.InputFrame A i) :
    Wp (dolenLen c l) (e.heap A msg m) (fun l' h' => StepPost e A msg m s o l' h' ∧
      (l'.broke = false → ∀ i', l'.in_ = .ref (BRef.blk e.ib) i' →
        l'.bits.toNat + 8 * i ≤ l.bits.toNat + 8 * i')) := by
  have hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size := by rw [hAsz]; exact e.hAsz
  have hAb : A.size < 2 ^ 63 := by rw [hAsz]; exact e.hAbig
  obtain ⟨l', h', hr, hq⟩ := dolenLen_wp hc A msg m l i o s e.hdt hls hA ho hAb hbroke hx hlen hs6 hT hb2
    (hfr.mono (by omega))
  refine ⟨l', h', hr, Wp.at_run (dolenLen_step_wp hc A msg m l i o s hls hAsz ho hbroke hagain hx hlen
    hs6 hsi hT hb2 hfr) hr, ?_⟩
  intro hnb i' hi'
  obtain ⟨i2, lx, S1, _, _, hrb, i3, H3, b3, E, cb, _, _, _, _, _, _, _, _, hend⟩ := hq
  rcases hend.2.2 with hgood | hbad
  · obtain ⟨i4, xv, rest, _, _, hrd, _, hls', hSg, _⟩ := hgood
    have hi4 : i4 = i' := (Ptr.ref.inj (hls'.hin.symm.trans hi')).2
    subst hi4
    have h1 := consume_readBits_length _ _ _ _ hrb
    have h2 := consume_readBits_length _ _ _ _ hrd
    have h3 : (S1.drop cb).length ≤ S1.length := by simp
    have hle : (Sg e l'.hold.toNat l'.bits.toNat i4).length ≤
        (Sg e l.hold.toNat l.bits.toNat i).length := by
      rw [hSg]; omega
    exact ledger_of_Sg hls.hi1 hls'.hi1 hle
  · obtain ⟨_, _, _, _, hb, _, _⟩ := hbad
    rw [hb] at hnb
    cases hnb

set_option maxHeartbeats 1000000 in
/-- `dolen_pass_wp` with the bit ledger: a pass that does not follow a link is not a link entry,
and a continuing result has dropped at least the width of the entry. -/
theorem dolen_pass_led (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32)
    (l : L) (i o s d k : Nat) (hls : LS e l i o) (hAsz : A.size = e.A0.size)
    (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat) (hbroke : l.broke = false)
    (hs6 : s + 6 ≤ e.i0 + e.sm0.avail_in.toNat) (hsi : s ≤ i) (hT : i ≤ s + 2)
    (hb15 : 15 ≤ l.bits.toNat + d) (hbi2 : i = s + 2 → 16 ≤ l.bits.toNat + d)
    (hhere : l.here = .ref e.rl k) (hk : k < e.LCA.size)
    (hEb : (e.LCA.getD k default).bits.toNat ≤ l.bits.toNat)
    (hEd : (e.LCA.getD k default).bits.toNat + d ≤ 15)
    (hcl : (LenLink (e.LCA.getD k default) ∧ LinkOK LenLeaf e.LCA e.ol (e.LCA.getD k default)) ∨
      LenLeaf d (e.LCA.getD k default))
    (hfr : e.InputFrame A i) :
    Wp (dolen c l) (e.heap A msg m) (fun l' h' =>
      (l'.againL = true ∧ l'.broke = false ∧ h' = e.heap A msg m ∧
        LenLink (e.LCA.getD k default) ∧
        ∃ j, j < 2 ^ (e.LCA.getD k default).op.toNat ∧
          l'.here = .ref e.rl (e.ol + (e.LCA.getD k default).val.toNat + j) ∧
          LS e l' i o ∧ l'.bits.toNat = l.bits.toNat - (e.LCA.getD k default).bits.toNat) ∨
      (StepPost e A msg m s o l' h' ∧ ¬ LenLink (e.LCA.getD k default) ∧
        (l'.broke = false → ∀ i', l'.in_ = .ref (BRef.blk e.ib) i' →
          l'.bits.toNat + 8 * i + (e.LCA.getD k default).bits.toNat ≤ l.bits.toNat + 8 * i'))) := by
  have hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size := by rw [hAsz]; exact e.hAsz
  have hkE : e.LCA[k]'hk = e.LCA.getD k default := by simp [Array.getD_eq_getD_getElem?, hk]
  have hld : OkOn (e.heap A msg m) (Ptr.load l.here) (e.LCA.getD k default) := by
    rw [hhere, ← hkE]; exact Ptr.load_ok (e.heap_cget_LCA A msg m) hk
  have hEbn : (e.LCA.getD k default).bits.toUInt32.toNat = (e.LCA.getD k default).bits.toNat := toNat32 _
  have hEb64 : (e.LCA.getD k default).bits.toUInt32.toUInt64.toNat = (e.LCA.getD k default).bits.toNat := by simp [toNat32]
  have hls1 := hls.dropL (e.LCA.getD k default).bits.toUInt32 (by omega) (by omega)
  have hsub : (l.bits - (e.LCA.getD k default).bits.toUInt32).toNat =
      l.bits.toNat - (e.LCA.getD k default).bits.toNat := by
    rw [u32_toNat_sub (by omega), hEbn]
  rw [dolen_eq_len]
  dsimp only
  refine Wp.bindO hld ?_
  refine Wp.bindO (shr64_ok (x := l.hold) (by omega)) ?_
  refine Wp.bindO hld ?_
  generalize e.LCA.getD k default = E at *
  by_cases hz : (E.op.toUInt32 == 0) = true
  · simp only [hz, ite_true]
    have hz0 : E.op = 0 := by rw [mask0] at hz; simpa using hz
    refine Wp.bindO hld ?_
    have hst : store8 l.out E.val.toUInt8 (e.heap A msg m) =
        .ok ((), e.heap (A.set! o E.val.toUInt8) msg m) := by
      rw [hls.hout, ← e.heap_put A (A.set! o E.val.toUInt8) msg m]
      exact Ptr.store_ok (e.heap_bytes_ob A msg m) (e.heap_ro_ob A msg m) (by omega)
    refine Wp.bindE hst ?_
    refine Wp.bindO (x := Ptr.ref (BRef.blk e.ob) (o + 1)) ?_ ?_
    · rw [hls.hout]
      exact Ptr.add_nat_ok (e.heap_bytes_ob _ msg m) (by simp; omega)
    · refine Wp.pure' (Or.inr ⟨?_, fun hl => hl.1 hz0, ?_⟩)
      · refine ⟨i, o + 1, A.set! o E.val.toUInt8, msg, m, ?_, hsi, by omega, by omega, by omega,
          by simp, rfl, rfl, ?_, ?_, ?_⟩
        · exact ⟨hls.hin, rfl, hls.hi0, hls.hi1, by have := hls.ho0; omega, hls1.hb, hls1.hH, hls1.hacc⟩
        · intro j hj
          have hne : o ≠ j := by omega
          simp [Array.set!, hne]
        · intro _; exact ⟨by omega, rfl, rfl⟩
        · intro h; simp [hbroke] at h
      · intro _ i' hi'
        dsimp only at hi' ⊢
        have hii : i = i' := (Ptr.ref.inj (hls.hin.symm.trans hi')).2
        omega
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
      refine Wp.mono (dolenLen_step_led hc A msg m
        { in_ := l.in_, out := l.out, hold := l.hold >>> E.bits.toUInt32.toUInt64, bits := l.bits - E.bits.toUInt32,
          here := l.here, op := E.op.toUInt32 &&& 15, len := E.val.toUInt32, dist := l.dist, from_ := l.from_,
          broke := l.broke, againL := false, againD := l.againD }
        i o s (LS.congr hls1 rfl rfl rfl rfl) hAsz ho hbroke rfl
        (by rw [mask15]; exact hbase.1) (by simpa [mask15] using hbase.2)
        hs6 hsi hT (by intro hi; have := hbi2 hi; show 1 ≤ (l.bits - E.bits.toUInt32).toNat
                       rw [u32_toNat_sub (by omega), hEbn]; omega) (hfr.mono (by omega))) ?_
      intro l' h' hq
      obtain ⟨hsp, hled⟩ := hq
      refine Or.inr ⟨hsp, fun hl => hb16' hl.2.1, fun hnb i' hi' => ?_⟩
      have := hled hnb i' hi'
      dsimp only at this
      omega
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
        refine Wp.pure' (Or.inl ⟨rfl, hbroke, rfl, hl, j, hjlt, rfl,
          LS.congr hls1 rfl rfl rfl rfl, ?_⟩)
        rw [u32_toNat_sub (by omega), hEbn]
      · simp only [hz, hb16, hb64, ite_false, Bool.false_eq_true]
        have hb64' : E.op &&& 64 ≠ 0 := by rw [mask64] at hb64; simpa using hb64
        by_cases hb32 : (E.op.toUInt32 &&& 32 != 0) = true
        · simp only [hb32, ite_true]
          refine Wp.bindE (e.heap_ldstate hc A msg m) ?_
          refine Wp.bindE (e.heap_stmode hc A msg m TYPE _ rfl) ?_
          refine Wp.pure' (Or.inr ⟨?_, fun hl => hb64' hl.2.2, ?_⟩)
          · refine ⟨i, o, A, msg, TYPE, LS.congr hls1 rfl rfl rfl rfl, hsi, by omega, by omega, by omega,
              rfl, rfl, rfl, (fun _ _ => rfl), ?_, (fun _ => Or.inl rfl)⟩
            intro h; cases h
          · intro h; cases h
        · simp only [hb32, ite_false, Bool.false_eq_true]
          obtain ⟨ip, hip⟩ := badData_run hc A msg m "invalid literal/length code" (by decide +kernel)
          refine Wp.bindE hip ?_
          refine Wp.pure' (Or.inr ⟨?_, fun hl => hb64' hl.2.2, ?_⟩)
          · refine ⟨i, o, A, .ref (BRef.str ip) 0, BAD, LS.congr hls1 rfl rfl rfl rfl, hsi, by omega, by omega, by omega,
              rfl, rfl, rfl, (fun _ _ => rfl), ?_, (fun _ => Or.inr rfl)⟩
            intro h; cases h
          · intro h; cases h

/-- `dolenLoop_step_wp` with strict consumption: a continuing body drops at least one bit of its
length code (`LenLeavesPositive`). -/
theorem dolenLoop_step_led (hc : CtxOK e c) (hpos : LenLeavesPositive e.LCA e.ol e.s0.lenbits.toNat)
    (A : Array UInt8) (msg : BPtr) (m : UInt32)
    (l : L) (i o s kidx : Nat) (hls : LS e l i o) (hAsz : A.size = e.A0.size)
    (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat) (hbroke : l.broke = false)
    (hs6 : s + 6 ≤ e.i0 + e.sm0.avail_in.toNat) (hsi : s ≤ i) (hT : i ≤ s + 2)
    (hb15 : 15 ≤ l.bits.toNat) (hbi2 : i = s + 2 → 16 ≤ l.bits.toNat)
    (hk : kidx < 2 ^ e.s0.lenbits.toNat) (hhere : l.here = .ref e.rl (e.ol + kidx))
    (hfr : e.InputFrame A i) :
    Wp (cdoWhile (dolen c) (fun l => pure (l.againL, l)) l) (e.heap A msg m)
      (fun l' h' => StepPost e A msg m s o l' h' ∧
        (l'.broke = false → ∀ i', l'.in_ = .ref (BRef.blk e.ib) i' →
          l'.bits.toNat + 8 * i < l.bits.toNat + 8 * i')) := by
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
  obtain ⟨l1, h1, e1, hq1⟩ := dolen_pass_led hc A msg m l i o s 0 (e.ol + kidx) hls hAsz ho hbroke
    hs6 hsi hT (by omega) (by intro hi; have := hbi2 hi; omega) hhere hksz (by omega) hEd0 hclass (hfr.mono (by omega))
  have hp0 := hpos kidx hk
  generalize hE0 : e.LCA.getD (e.ol + kidx) default = E0 at hq1 hclass hEd0 hp0
  rcases hq1 with ⟨hag, hbr, hh, hlink, j, hjlt, hhere1, hls1, hb1⟩ | ⟨hend, hnl, hled⟩
  · subst hh
    have hlk : LinkOK LenLeaf e.LCA e.ol E0 := by
      rcases hclass with h | h
      · exact h.2
      · rcases h.2 with h0 | h | h
        · exact False.elim (hlink.1 h0)
        · exact False.elim (h.1 hlink.2.1)
        · exact False.elim (h.2 hlink.2.2)
    have hleaf := hlk.2.2.2.2 j hjlt
    have hpj : 1 ≤ (e.LCA.getD (e.ol + E0.val.toNat + j) default).bits.toNat := by
      rw [if_pos hlink] at hp0; exact hp0 j hjlt
    have hk2 : e.ol + E0.val.toNat + j < e.LCA.size := by have := hlk.2.2.2.1; omega
    obtain ⟨l2, h2, e2, hq2⟩ := dolen_pass_led hc A msg m l1 i o s E0.bits.toNat (e.ol + E0.val.toNat + j)
      hls1 hAsz ho hbr hs6 hsi hT (by omega) (by intro hi; have := hbi2 hi; omega)
      hhere1 hk2 (by have := hleaf.1; omega) hleaf.1 (Or.inr hleaf) (hfr.mono (by omega))
    rcases hq2 with ⟨_, _, _, hl2, _⟩ | ⟨hend2, _, hled2⟩
    · rcases hleaf.2 with h0 | h | h
      · exact False.elim (hl2.1 h0)
      · exact False.elim (h.1 hl2.2.1)
      · exact False.elim (h.2 hl2.2.2)
    · have c1 : (fun l : L => (pure (l.againL, l) : M (Bool × L))) l1 (e.heap A msg m) =
          .ok ((true, l1), e.heap A msg m) := by simp [hag]
      have c2 : (fun l : L => (pure (l.againL, l) : M (Bool × L))) l2 h2 =
          .ok ((false, l2), h2) := by simp [StepPost.againL hend2]
      refine Wp.of_eq (cdoWhile_two e1 c1 e2 c2) ⟨hend2, fun hnb i' hi' => ?_⟩
      have := hled2 hnb i' hi'
      omega
  · have c1 : (fun l : L => (pure (l.againL, l) : M (Bool × L))) l1 h1 =
        .ok ((false, l1), h1) := by simp [StepPost.againL hend]
    have hpE : 1 ≤ E0.bits.toNat := by rw [if_neg hnl] at hp0; exact hp0
    refine Wp.of_eq (cdoWhile_one e1 c1) ⟨hend, fun hnb i' hi' => ?_⟩
    have := hled hnb i' hi'
    omega

/-- Root-table lookup and the length loop, with strict consumption. -/
theorem dolenRoot_step_led (hc : CtxOK e c) (hpos : LenLeavesPositive e.LCA e.ol e.s0.lenbits.toNat)
    (A : Array UInt8) (msg : BPtr) (m : UInt32)
    (l : L) (i o s : Nat) (hls : LS e l i o) (hAsz : A.size = e.A0.size)
    (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat) (hbroke : l.broke = false)
    (hs6 : s + 6 ≤ e.i0 + e.sm0.avail_in.toNat) (hsi : s ≤ i) (hT : i ≤ s + 2)
    (hb15 : 15 ≤ l.bits.toNat) (hbi2 : i = s + 2 → 16 ≤ l.bits.toNat)
    (hfr : e.InputFrame A i) :
    Wp (do
      let here ← c.lcode.add (l.hold &&& c.lmask.toUInt64).toNat
      cdoWhile (dolen c) (fun l => pure (l.againL, l)) {l with here})
      (e.heap A msg m) (fun l' h' => StepPost e A msg m s o l' h' ∧
        (l'.broke = false → ∀ i', l'.in_ = .ref (BRef.blk e.ib) i' →
          l'.bits.toNat + 8 * i < l.bits.toNat + 8 * i')) := by
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
  · exact dolenLoop_step_led hc hpos A msg m _ i o s _ (LS.congr hls rfl rfl rfl rfl) hAsz ho hbroke
      hs6 hsi hT hb15 hbi2 hmod rfl (hfr.mono (by omega))

/-- One actual body that continues strictly consumes held-plus-unread input bits. -/
theorem inflate_fast_body_consumes (e : EnvG α) (c : Ctx) (A : Array UInt8) (msg : BPtr)
    (m : UInt32) (l : L) (i o : Nat) (hp : StepPre e c A l i o)
    (hpos : LenLeavesPositive e.LCA e.ol e.s0.lenbits.toNat) :
    Wp (inflate_fast_body c l) (e.heap A msg m) (fun l' _ =>
      l'.broke = false → ∀ i', l'.in_ = .ref (BRef.blk e.ib) i' →
        l'.bits.toNat + 8 * i < l.bits.toNat + 8 * i') := by
  have hfr := hp.inputFrame
  rcases hp with ⟨hc, hls, hAsz, hi6, ho258, hbroke⟩
  unfold inflate_fast_body
  by_cases h1 : l.bits < 15
  · simp only [h1, ite_true]
    have hb : l.bits.toNat < 15 := by simpa using UInt32.lt_iff_toNat_lt.mp h1
    have hiin : i < e.i0 + e.sm0.avail_in.toNat := by omega
    refine Wp.bindO (pull_run e _ l i o hls (by omega) hiin (e.heap_bytes_in A msg m) (hfr.get (by omega) (by omega))) ?_
    have hl1 := hls.pullL (by omega) hiin
    have hb1 := pullL_bits l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1)) hls.hb
    have hi2 : i + 1 < e.i0 + e.sm0.avail_in.toNat := by omega
    have hb1' : (pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1))).bits.toNat ≤ 22 := by
      simp only [pullL] at hb1 ⊢; omega
    refine Wp.bindO (pull_run e _ _ (i + 1) o hl1 hb1' hi2 (e.heap_bytes_in A msg m) (hfr.get (by omega) (by omega))) ?_
    have hl2 := hl1.pullL hb1' hi2
    have hb2 := pullL_bits (pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1)))
      (e.IN.getD (i + 1) 0) (.ref (BRef.blk e.ib) (i + 1 + 1)) hl1.hb
    refine Wp.mono (dolenRoot_step_led hc hpos A msg m _ (i + 1 + 1) o i hl2 hAsz ho258 hbroke hi6 (by omega) (by omega)
      (by simp only [pullL] at hb1 hb2 ⊢; omega)
      (by intro _; simp only [pullL] at hb1 hb2 ⊢; omega) (hfr.mono (by omega))) ?_
    intro l' _ hq hnb i' hi'
    have := hq.2 hnb i' hi'
    simp only [pullL] at hb1 hb2 this
    omega
  · simp only [h1, ite_false]
    have hb : 15 ≤ l.bits.toNat := by
      have : ¬ l.bits.toNat < 15 := fun h => h1 (UInt32.lt_iff_toNat_lt.mpr (by simpa using h))
      omega
    exact Wp.mono (dolenRoot_step_led hc hpos A msg m l i o i hls hAsz ho258 hbroke hi6 (by omega) (by omega) hb
      (by omega) (hfr.mono (by omega))) (fun _ _ hq => hq.2)

/-- `fast_loop_wp_progress` with the bit ledger: a loop that does not end in `TYPE` or `BAD`
leaves strictly fewer held-plus-read bits than it found at entry. -/
theorem fast_loop_wp_consumes (hc : CtxOK e c) (hpos : LenLeavesPositive e.LCA e.ol e.s0.lenbits.toNat)
    (l : L) (i o : Nat) (A : Array UInt8)
    (hl : LS e l i o) (hA : A.size = e.A0.size) (hb : l.broke = false)
    (hi : i + 6 ≤ e.i0 + e.sm0.avail_in.toNat)
    (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hf : ∀ j, (j < e.o0 ∨ o ≤ j) → A[j]? = e.A0[j]?) :
    Wp (cdoWhile (inflate_fast_body c)
      (fun l => do
        if l.broke then pure (false, l)
        else if ← Ptr.lt l.in_ c.last then pure (← Ptr.lt l.out c.end_, l)
        else pure (false, l)) l) (e.heap A e.sm0.msg e.s0.mode)
      (fun l' h' => ∃ i' o' A' msg' m',
        LS e l' i' o' ∧ o' ≤ e.o0 + e.sm0.avail_out.toNat ∧ A'.size = e.A0.size ∧
        h' = e.heap A' msg' m' ∧
        (∀ j, (j < e.o0 ∨ o' ≤ j) → A'[j]? = e.A0[j]?) ∧
        ((m' = e.s0.mode ∧ msg' = e.sm0.msg) ∨ (m' = TYPE ∧ msg' = e.sm0.msg) ∨ m' = BAD) ∧
        (m' ≠ TYPE → m' ≠ BAD → i' + 6 > e.i0 + e.sm0.avail_in.toNat ∨
          o' + 258 > e.o0 + e.sm0.avail_out.toNat) ∧ o ≤ o' ∧
        (m' ≠ TYPE → m' ≠ BAD → o < o') ∧
        (m' ≠ TYPE → m' ≠ BAD → l'.bits.toNat + 8 * e.i0 < e.s0.bits.toNat + 8 * i')) := by
  let firstOut := o
  let Inv : L → Heap → Prop := fun l h => ∃ i o A,
    LS e l i o ∧ A.size = e.A0.size ∧ h = e.heap A e.sm0.msg e.s0.mode ∧ l.broke = false ∧
    i + 6 ≤ e.i0 + e.sm0.avail_in.toNat ∧ o + 258 ≤ e.o0 + e.sm0.avail_out.toNat ∧
    (∀ j, (j < e.o0 ∨ o ≤ j) → A[j]? = e.A0[j]?) ∧ firstOut ≤ o
  let μ : L → Nat := fun l => match l.out with
    | .null => 0
    | .ref _ k => e.o0 + e.sm0.avail_out.toNat - k
  have hμ : ∀ l i o, LS e l i o → μ l = e.o0 + e.sm0.avail_out.toNat - o := by
    intro l i o hl
    simp only [μ, hl.hout]
  refine Wp.cdoWhile Inv μ _ ?_ ⟨i, o, A, hl, hA, rfl, hb, hi, ho, hf, Nat.le_refl _⟩ ?_
  · intro l h hI
    obtain ⟨i, o, A, hl, hA, rfl, hb, hi, ho, hf, lower⟩ := hI
    have hp : StepPre e c A l i o :=
      ⟨hc, hl, hA, hi, ho, hb, e.inputFrame_of_frame hA hf (by omega) hl.hi0⟩
    obtain ⟨l1, h1, hr, hpost⟩ := inflate_fast_body_step_safe_gen e c A e.sm0.msg e.s0.mode l i o hp
    obtain ⟨B, p, q, hmsgheap, _, htype⟩ := Wp.at_run
      (inflate_fast_body_type_message e c A e.sm0.msg e.s0.mode l i o hp) hr
    have hled := Wp.at_run (inflate_fast_body_consumes e c A e.sm0.msg e.s0.mode l i o hp hpos) hr
    obtain ⟨i', o', A', msg', m', hl', hii, hi6, hoo, ho258, hsz, hh, _, hframe, hcont, hbreak⟩ := hpost
    have hAsz : A'.size = e.A0.size := hsz.trans hA
    have hoend : o' ≤ e.o0 + e.sm0.avail_out.toNat := by omega
    have hft : ∀ j, (j < e.o0 ∨ o' ≤ j) → A'[j]? = e.A0[j]? := by
      intro j hj
      rw [hframe j (by have := hl.ho0; omega)]
      exact hf j (by omega)
    have hmq := e.heap_msg_mode_eq (hh.symm.trans hmsgheap)
    have htype' : m' = TYPE → msg' = e.sm0.msg := by
      intro hm
      exact hmq.1.trans (htype (hmq.2.symm.trans hm))
    refine ⟨l1, h1, hr, ?_⟩
    cases hstop : l1.broke with
    | true =>
      refine Or.inl ⟨l1, h1, ?_, i', o', A', msg', m', hl', hoend, hAsz, hh, hft, ?_, ?_, ?_, ?_, ?_⟩
      · simp [hstop]
      · rcases hbreak hstop with hm | hm
        · exact Or.inr (Or.inl ⟨hm, htype' hm⟩)
        · exact Or.inr (Or.inr hm)
      · intro hnt hnb
        rcases hbreak hstop with hm | hm
        · exact False.elim (hnt hm)
        · exact False.elim (hnb hm)
      · exact Nat.le_trans lower hoo
      · intro hnt hnb
        rcases hbreak hstop with hm | hm
        · exact False.elim (hnt hm)
        · exact False.elim (hnb hm)
      · intro hnt hnb
        rcases hbreak hstop with hm | hm
        · exact False.elim (hnt hm)
        · exact False.elim (hnb hm)
    | false =>
      obtain ⟨hout, hmsg, hmode⟩ := hcont hstop
      have hcnd := fast_cond_live hc A' msg' m' l1 i' o' hl' hAsz hoend hstop
      have hstrict : l1.bits.toNat + 8 * e.i0 < e.s0.bits.toNat + 8 * i' := by
        have := hled hstop i' hl'.hin
        have := hl.hacc
        omega
      by_cases hroom : i' + 6 ≤ e.i0 + e.sm0.avail_in.toNat ∧
          o' + 258 ≤ e.o0 + e.sm0.avail_out.toNat
      · refine Or.inr ⟨l1, h1, ?_, ?_, ?_⟩
        · rw [hh]; simpa [hstop, hroom.1, hroom.2] using hcnd
        · exact ⟨i', o', A', hl', hAsz, by rw [hh, hmsg, hmode], hstop, hroom.1, hroom.2, hft, Nat.le_trans lower hoo⟩
        · rw [hμ _ _ _ hl', hμ _ _ _ hl]
          omega
      · refine Or.inl ⟨l1, h1, ?_, i', o', A', msg', m', hl', hoend, hAsz, hh, hft,
          Or.inl ⟨hmode, hmsg⟩, ?_, Nat.le_trans lower hoo, ?_, fun _ _ => hstrict⟩
        · have hcfalse : (decide (i' + 6 ≤ e.i0 + e.sm0.avail_in.toNat) &&
              decide (o' + 258 ≤ e.o0 + e.sm0.avail_out.toNat)) = false := by
            simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
            omega
          rw [hh]
          simpa [hstop, hcfalse] using hcnd
        · intro _ _; omega
        · intro _ _
          exact Nat.lt_of_le_of_lt lower hout
  · rw [hμ _ _ _ hl]
    apply lt_fuel_of
    have := UInt32.toNat_lt e.sm0.avail_out
    have := hl.ho0
    omega

/-- `fast_finish_progress_wp` with the bit ledger: the writeback returns whole bytes, so the
ledger of the locals is the ledger of the records. -/
theorem fast_finish_consumes_wp {α : Bool} (e : EnvG α) (A : Array UInt8) (msg : BPtr) (mode : UInt32)
    (l : L) (i o : Nat) (hl : LS e l i o) (hAsz : A.size = e.A0.size)
    (ho : o ≤ e.o0 + e.sm0.avail_out.toNat)
    (hf : ∀ j, (j < e.o0 ∨ o ≤ j) → A[j]? = e.A0[j]?)
    (hclass : (mode = e.s0.mode ∧ msg = e.sm0.msg) ∨ (mode = TYPE ∧ msg = e.sm0.msg) ∨ mode = BAD)
    (hstop : mode ≠ TYPE → mode ≠ BAD → i + 6 > e.i0 + e.sm0.avail_in.toNat ∨
      o + 258 > e.o0 + e.sm0.avail_out.toNat)
    (progress : mode ≠ TYPE → mode ≠ BAD → e.o0 < o)
    (strict : mode ≠ TYPE → mode ≠ BAD → l.bits.toNat + 8 * e.i0 < e.s0.bits.toNat + 8 * i)
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
      (e.heap A msg mode) (fun _ after => FastPost e after ∧ FastProgress e after ∧ FastConsumes e after) := by
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
  have hres : bits.toNat = l.bits.toNat % 8 := by dsimp only [bits]; rw [bits_residual _ hl.hb]
  have hbits : bits.toNat < 8 := by rw [hres]; omega
  have hbufd : buf = l.bits.toNat / 8 := rfl
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
  let stream := { e.sm0 with next_in := .ref (.blk e.ib) (e.i0 + used), next_out := .ref (.blk e.ob) o, avail_in := UInt32.ofNat (e.sm0.avail_in.toNat - used), avail_out := UInt32.ofNat (e.sm0.avail_out.toNat - produced), msg }
  let state := { e.s0 with mode, hold, bits }
  have baseGet : e.r.get { e.h0 with bytes := upd e.h0.bytes e.ob (some A), istates := upd e.h0.istates e.stid (some state) } = some e.sm0 := by
    cases refEq : e.r with
    | tab k => simpa only [refEq, ZStreamRef.get] using e.hsm
    | in_gzstate_strm k => simpa only [refEq, ZStreamRef.get] using e.hsm
  have hin32 : (UInt32.ofNat (e.sm0.avail_in.toNat - used)).toNat = e.sm0.avail_in.toNat - used :=
    UInt32.toNat_ofNat_of_lt' (by simp only [UInt32.size]; exact hu32)
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨used, produced, buf, A, msg, mode, bits, hold, hui, hsmall, hup, hAsz, hbits,
      normalized_hold_lt l.hold bits (by omega), ?_, ?_, hclass, ?_⟩
    · rw [← hout]
    · intro j hj
      exact hf j (by rw [← hout] at hj; exact hj)
    · intro hnt hnb
      rcases hstop hnt hnb with hi | ho
      · exact Or.inl (by have := hl.hi0; omega)
      · exact Or.inr (by omega)
  · refine ⟨stream, state, put_get _ _ _ _ baseGet, ?_, ?_⟩
    · rw [put_istates, upd_same]
    · intro nonterminal nonbad
      have positive : 0 < produced := by
        dsimp only [produced]
        have advancing := progress nonterminal nonbad
        omega
      change (UInt32.ofNat (e.sm0.avail_out.toNat - produced)).toNat < e.sm0.avail_out.toNat
      rw [UInt32.toNat_ofNat_of_lt' (by simp only [UInt32.size]; exact ho32)]
      omega
  · refine ⟨stream, state, put_get _ _ _ _ baseGet, ?_, ?_, ?_⟩
    · rw [put_istates, upd_same]
    · change bits.toNat + 8 * (UInt32.ofNat (e.sm0.avail_in.toNat - used)).toNat ≤
        e.s0.bits.toNat + 8 * e.sm0.avail_in.toNat
      rw [hin32, hres]
      have := hl.hacc
      have := hl.hi0
      omega
    · intro nonterminal nonbad
      have hlt := strict nonterminal nonbad
      change bits.toNat + 8 * (UInt32.ofNat (e.sm0.avail_in.toNat - used)).toNat <
        e.s0.bits.toNat + 8 * e.sm0.avail_in.toNat
      rw [hin32, hres]
      have := hl.hi0
      omega

/-- **`fast_consumes`.** On any `EnvG α` whose literal/length table reads at least one bit per
leaf, the actual complete fast decoder is safe (`FastPost`), makes output progress
(`FastProgress`) and consumes input bits (`FastConsumes`): never more held-plus-unread bits than at
entry, and strictly fewer unless it ends in `TYPE` or `BAD`. -/
theorem fast_consumes {α : Bool} (e : EnvG α) (hpos : LenLeavesPositive e.LCA e.ol e.s0.lenbits.toNat) :
    ∃ after, C.run (inflate_fast e.strm e.start) e.h0 = .ok ((), after) ∧
      FastPost e after ∧ FastProgress e after ∧ FastConsumes e after := by
  have hw : Wp (inflate_fast e.strm e.start) e.h0
      (fun _ after => FastPost e after ∧ FastProgress e after ∧ FastConsumes e after) := by
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
      simpa only [hn, EnvG.bg] using hr
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
    obtain ⟨l, h, hr, hpost⟩ := fast_loop_wp_consumes hc0 hpos l0 e.i0 e.o0 e.A0 hl0 rfl rfl
      (by have := e.hai; omega) (by have := e.hao; omega) (by intro _ _; rfl)
    rw [e.heap_initial] at hr
    refine Wp.bindE hr ?_
    obtain ⟨i, o, A, msg, mode, hl, ho, hA, hh, hf, hclass, hstop, _, progress, strict⟩ := hpost
    rw [hh]
    exact fast_finish_consumes_wp e A msg mode l i o hl hA ho hf hclass hstop progress strict
      (e.inputFrame_of_frame hA hf ho hl.hi0)
  obtain ⟨⟨⟩, after, hr, hp⟩ := hw
  exact ⟨after, hr, hp⟩

end Zlib.Inffast.Proofs
