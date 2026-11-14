import ZlibF.Proof.«gzwrite.c.write-calls»
import ZlibF.Proof.«deflate.c.universal-params-accounting»

/-!
# gzwrite.c: the public calls `gzflush` and `gzsetparams`

`gzflush_step_of`: the skeleton statement `gzflush_step` (branch `skeleton/gz`, `gz.skeleton-write.lean`), from the
facts of `gz_error` (`GzErrorSpec`, `GzErrorOwn`). The callees are `zero_any` and `comp_any`
(`gzwrite.c.write-calls`): `gz_zero` and `gz_comp` on a writer with or without buffers.

`gzsetparams_step_of`: the skeleton statement `gzsetparams_step`, from the facts of `gz_error`. `gz_comp(state, Z_BLOCK)`
is `gz_comp_safe_shape_of'` at flush 5. `deflateParams`
on the embedded stream is `params_step`, from `params_full` (`deflate.c.universal-params-accounting`): the accounting
of the call keeps W4 and W5, and the call is a step of the deflate history. On a transparent writer (no codec) the
call refuses (`params_nostate`).
-/

namespace ZlibF.Spec.Public.GzSkeleton
open C Zlib.GzFs Zlib.Gzguts ZlibF.Spec.Public
open Zlib.Gzwrite.SafeInit (GzErrorSpec GzErrorOwn)
set_option autoImplicit false

section flush
variable {i : Nat}

/-- `gzflush` from the compression on. -/
def flushTail (i : Nat) (flush : Int32) : G Int32 := do
  let _ ← Zlib.Gzwrite.gz_comp (gzSt i) flush
  return (← ldS (gzSt i)).err

theorem gzflush_eq (flush : Int32) :
    Zlib.Gzwrite.gzflush (some (.in_gzstate_x i)) flush = (do
      let s ← ldS (gzSt i)
      if s.mode != GZ_WRITE || (s.err != Z_OK && s.again == 0) then return Z_STREAM_ERROR
      Zlib.Gzlib.gz_error (gzSt i) Z_OK .null
      if flush < 0 || flush > Z_FINISH then return Z_STREAM_ERROR
      if (← ldS (gzSt i)).skip != 0 then
        if (← Zlib.Gzwrite.gz_zero (gzSt i)) == -1 then return (← ldS (gzSt i)).err
      flushTail i flush : G Int32) := rfl

theorem flushTail_ok (err : GzErrorSpec) (errOwn : GzErrorOwn) {h0 : Heap} {s0 : GzState} {fs0 fs : Fs} {H : Heap}
    {v : GzState} (flush : Int32) (hf : 0 ≤ flush.toInt ∧ flush.toInt ≤ 4) (E : GetcUngetc.Eff i h0 s0 fs0 fs H)
    (inv : GzInv H i v) (hw : v.mode = GZ_WRITE) :
    ∃ r fs' h', flushTail i flush fs H = .ok ((r, fs'), h') ∧ GetcUngetc.Eff i h0 s0 fs0 fs' h' := by
  obtain ⟨r, fs2, H2, run, k2, post⟩ := comp_any err errOwn inv E.2.1 hw flush ⟨hf.1, by omega⟩
  have E2 := GetcUngetc.Eff.trans E inv post k2
  obtain ⟨-, -, s2, inv2, -⟩ := id E2
  have hS2 : ldS (gzSt i) H2 = .ok (s2, H2) := Zlib.Gzlib.Proofs.ldS_run inv2.common.record
  refine ⟨s2.err, fs2, H2, ?_, E2⟩
  unfold flushTail
  simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, run, hS2]

/-- **`gzflush_step`** (skeleton statement), given the facts of `gz_error`. -/
theorem gzflush_step_of (err : GzErrorSpec) (errOwn : GzErrorOwn) (i : Nat) (flush : Int32) :
    GzCallSafe i (.gzflush (some (.in_gzstate_x i)) flush) := by
  intro h fs s inv hfs _
  have R : Ok (Zlib.Gzwrite.gzflush (some (.in_gzstate_x i)) flush) fs h
      (fun _ fs' after => GetcUngetc.Eff i h s fs fs' after) := by
    rw [gzflush_eq]
    have hS : ldS (gzSt i) h = .ok (s, h) := Zlib.Gzlib.Proofs.ldS_run inv.common.record
    by_cases hm : (s.mode != GZ_WRITE || (s.err != Z_OK && s.again == 0)) = true
    · refine ⟨Z_STREAM_ERROR, fs, h, ?_, GetcUngetc.Eff.refl inv hfs⟩
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
        hm, ↓reduceIte]
    have hm' := Bool.eq_false_iff.mpr hm
    have hw := mode_of hm'
    obtain ⟨run1, inv1, post1⟩ := clear_step (fs := fs) inv hfs
    have E1 : GetcUngetc.Eff i h s fs fs (okHeap h i s) :=
      GetcUngetc.Eff.trans (GetcUngetc.Eff.refl inv hfs) inv post1 (fun _ => Iff.rfl)
    by_cases hc : (decide (flush < 0) || decide (flush > Z_FINISH)) = true
    · refine ⟨Z_STREAM_ERROR, fs, okHeap h i s, ?_, E1⟩
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
        hm', Bool.false_eq_true, ↓reduceIte, run1, hc]
    have hc' := Bool.eq_false_iff.mpr hc
    have hf : 0 ≤ flush.toInt ∧ flush.toInt ≤ 4 := by
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Int32.lt_iff_toInt_lt, GT.gt] at hc'
      have z0 : (0 : Int32).toInt = 0 := rfl
      have f4 : Z_FINISH.toInt = 4 := rfl
      omega
    have hS1 : ldS (gzSt i) (okHeap h i s) = .ok (okRec s, okHeap h i s) :=
      Zlib.Gzlib.Proofs.ldS_run inv1.common.record
    by_cases hk : (okRec s).skip = 0
    · have hkB : ((okRec s).skip != 0) = false := by simp [hk]
      obtain ⟨r, fs', h', run, E'⟩ := flushTail_ok err errOwn flush hf E1 inv1 hw
      refine ⟨r, fs', h', ?_, E'⟩
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
        hm', Bool.false_eq_true, ↓reduceIte, run1, hc', hS1, hkB]
      exact run
    · have hkB : ((okRec s).skip != 0) = true := by simpa using hk
      obtain ⟨r, fs2, H2, run2, hr, k2, post2, -⟩ := zero_any err errOwn inv1 hfs hw
      have E2 := GetcUngetc.Eff.trans E1 inv1 post2 k2
      obtain ⟨-, -, s2, inv2, hm2, -⟩ := id E2
      rcases hr with rfl | rfl
      · obtain ⟨r, fs', h', run, E'⟩ := flushTail_ok err errOwn flush hf E2 inv2 (hm2.trans hw)
        refine ⟨r, fs', h', ?_, E'⟩
        simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
          hm', Bool.false_eq_true, ↓reduceIte, run1, hc', hS1, hkB, run2, int32_zero_ne_neg_one]
        exact run
      · have hS2 : ldS (gzSt i) H2 = .ok (s2, H2) := Zlib.Gzlib.Proofs.ldS_run inv2.common.record
        refine ⟨s2.err, fs2, H2, ?_, E2⟩
        simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
          hm', Bool.false_eq_true, ↓reduceIte, run1, hc', hS1, hkB, run2, beq_self_eq_true, hS2]
  have RS := runSafe_of_ok R
  exact ⟨RS.1, fun _ => RS.2.1 trivial, fun v fs' after he => GetcUngetc.Eff.post rfl (RS.2.2 v fs' after he)⟩

end flush

/-! ## `gzsetparams` -/

section params
variable {i : Nat} {src : Region}
open ZlibF.Spec.Public.GzRead (DataBuf)

set_option maxHeartbeats 4000000 in
/-- **`deflateParams` on the embedded stream** of a compressing writer with buffers (the state of `St`): it returns,
the state of `St` holds after it with the same input region, it changes only blocks the handle owns and keeps the
live and the owned blocks, the record changes only in its stream, and the `strerror` borrow is kept. The stream
facts are `params_full` (`deflate.c.universal-params-accounting`); the rest is `call_step`'s argument. -/
theorem params_step {h : Heap} {s : GzState} (S : St i src h s) (level strategy : Int32) :
    ∃ rc after s', C.run (Zlib.Deflate.deflateParams (some (gzStrm i)) level strategy) h = .ok (rc, after) ∧
      after.gzstates i = some s' ∧ St i src after s' ∧ Frame h after (GzOwned h i s) ∧
      (∀ b, after.live b ↔ h.live b) ∧ (∀ b, GzOwned after i s' b ↔ GzOwned h i s b) ∧
      s' = { s with strm := s'.strm } ∧ after.libcErrorBorrow = h.libcErrorBorrow := by
  have F := facts_of S.up S.direct S.size
  have P := ptr_free S.up S.size S.direct
  have buffers := buffers_of S
  have active := active_of S
  have hget : (gzStrm i).get h = some s.strm := by simp [ZStreamRef.get, gzStrm, F.record]
  obtain ⟨ds, z0, d, inv, header, cf⟩ := Zlib.Deflate.Universal.reachable_inv_of
    (Zlib.Deflate.Universal.Call.sequence_facts_of Zlib.Deflate.Engine.Proofs.tinyOverlay) F.reach
  have e0 : z0 = s.strm := Option.some.inj (inv.good.live.hz.symm.trans hget)
  subst e0
  obtain ⟨rc, after, z', d', used, kp, run, inv', acc, bframe, hlive, own, gzEq⟩ :=
    Zlib.Deflate.Universal.params_full inv header cf buffers active level strategy
  obtain ⟨hu1, hu2, hu3, hu4, hu5, hu6, hu7, -⟩ := acc
  obtain ⟨s', hs', es'⟩ := Zlib.Deflate.Universal.Params.deflateParams_keeps_gz_records _ _ _ _ _ _ run i s F.record
  have hz' : s'.strm = z' := by
    have g := inv'.good.live.hz
    simp only [ZStreamRef.get, gzStrm, hs', Option.map_some, Option.some.injEq] at g
    exact g
  have hget' : (gzStrm i).get after = some s'.strm := by simp [ZStreamRef.get, gzStrm, hs']
  obtain ⟨k, dk, hk, hdk, hhead⟩ := F.head
  have ek : k = ds := by
    have := inv.good.live.zst
    rw [hk] at this
    cases this
    rfl
  subst ek
  have ed : dk = d := Option.some.inj (hdk.symm.trans inv.good.live.hs)
  subst ed
  obtain ⟨ob, oa, hop, hob, hor, hos⟩ := F.outbuf
  obtain ⟨ib, ia, hip, hib, hir, his⟩ := F.inbuf
  obtain ⟨bo, co, hnext, havail, hx, hcb, hbs⟩ := F.out
  have hnext' : s.strm.next_out = .ref (.blk ob) bo := by rw [hnext, hop]; simp [padv]
  have obOwn : GzOwned h i s ob := Or.inr (Or.inr (Or.inr ⟨S.size, Or.inr ⟨Or.inr S.direct, Or.inl hop⟩⟩))
  have ibOwn : GzOwned h i s ib := Or.inr (Or.inr (Or.inr ⟨S.size, Or.inl hip⟩))
  have obLive := F.ownLive ob obOwn
  have soIff : ∀ b, StreamOwned h (gzStrm i) b ↔ DeflateOwned k dk b := inv.owned
  have obC : ¬ (StreamRoot (gzStrm i) ob ∨ DeflateOwned k dk ob) := by
    rintro (e | e)
    · exact (P.1 ob hop).1 e
    · exact (P.1 ob hop).2 ((soIff ob).2 e)
  rw [hnext'] at bframe
  obtain ⟨fr0, ⟨oa', hoa', hos'⟩, hro⟩ := frame_of_out bframe hob obLive obC
  have hso : ∀ b, StreamOwned after (gzStrm i) b ↔ StreamOwned h (gzStrm i) b :=
    fun b => (inv'.owned b).trans ((own b).symm.trans (soIff b).symm)
  have frD : Frame h after (fun b => b = i ∨ StreamOwned h (gzStrm i) b ∨ DataBuf s b) :=
    Zlib.Gzwrite.SafeInit.frame_mono fr0 (fun b hb => by
      rcases hb with (e | e) | e
      · exact Or.inl e
      · exact Or.inr (Or.inl ((soIff b).2 e))
      · subst e
        exact Or.inr (Or.inr ⟨S.size, Or.inr ⟨Or.inr S.direct, hop⟩⟩))
  have frG : Frame h after (GzOwned h i s) :=
    Zlib.Gzwrite.SafeInit.frame_mono frD (fun b hb => by
      rcases hb with e | e | e
      · exact Or.inl e
      · exact F.streamOwned b e
      · exact e.owned)
  have hbor : after.libcErrorBorrow = h.libcErrorBorrow :=
    Zlib.Deflate.BorrowProofs.stable_deflateParams _ _ _ h rc after run
  have ibob : ib ≠ ob := fun e => P.2.2 ib hip (by rw [hop, e])
  have ibC : ¬ ((StreamRoot (gzStrm i) ib ∨ DeflateOwned k dk ib) ∨ ib = ob) := by
    rintro ((e | e) | e)
    · exact (P.2.1 ib hip).1 e
    · exact (P.2.1 ib hip).2 ((soIff ib).2 e)
    · exact ibob e
  have hdata : ∀ b, DataBuf s b → (∃ a a', h.bytes b = some a ∧ after.bytes b = some a' ∧ a'.size = a.size) ∧
      after.ro b = h.ro b := by
    rintro b ⟨-, hb | ⟨-, hb⟩⟩
    · rw [hip] at hb
      cases hb
      obtain ⟨e1, -, -, -, -, -, -, e8⟩ := fr0.2.2.2.2.2 ib (F.ownLive ib ibOwn) ibC
      exact ⟨⟨ia, ia, hib, by rw [e1]; exact hib, rfl⟩, e8⟩
    · rw [hop] at hb
      cases hb
      exact ⟨⟨oa, oa', hob, hoa', hos'⟩, hro⟩
  have uniq' : Zlib.Gzlib.Spec.Uniq after := (gz_uniq_iff_deflate after).2 inv'.good.uniq
  obtain ⟨w, p, q, bb, blocks⟩ := inv'.good.inv.blocks
  have I' := inv'.good.inv
  have wle : d'.w_size.toNat ≤ 2 ^ 15 := by
    rw [I'.wsize]; exact Nat.pow_le_pow_right (by decide) I'.wbits_hi
  have lle : d'.lit_bufsize.toNat ≤ 2 ^ 15 := by
    have e1 := I'.lit
    have e2 := I'.hsize
    have : 2 ^ d'.hash_bits.toNat ≤ 2 ^ 16 := Nat.pow_le_pow_right (by decide) I'.hbits_hi
    omega
  have lim : (2 : Nat) ^ 18 < ZlibF.PlatformMemory.byteObjectLimit := by
    unfold ZlibF.PlatformMemory.byteObjectLimit; decide
  have changedOwned : ∀ x, DeflateOwned k dk x → x = k ∨ x = w ∨ x = p ∨ x = q ∨ x = bb := by
    intro x hx
    rcases (own x).1 hx with e | e | e | e | e
    · exact Or.inl e
    · rw [blocks.win] at e; cases e; exact Or.inr (Or.inl rfl)
    · rw [blocks.prev] at e; cases e; exact Or.inr (Or.inr (Or.inl rfl))
    · rw [blocks.head] at e; cases e; exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · rw [blocks.pbuf] at e; cases e; exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  have fit : ZlibF.PlatformMemory.ByteObjectsFit after := by
    apply Zlib.Gzwrite.SafeInit.fit_of F.fit fr0.1.symm hbor
    · intro x arr e
      by_cases hxo : x = ob
      · subst hxo
        rw [hoa'] at e
        cases e
        right
        rw [hos']
        exact F.fit (.blk x) oa hob
      by_cases hl : h.live x
      · by_cases hc : StreamRoot (gzStrm i) x ∨ DeflateOwned k dk x
        · rcases hc with e1 | e1
          · exfalso
            change x = i at e1
            subst e1
            rw [(Zlib.Gzwrite.SafeInit.uniq_gz_only uniq' hs').1] at e
            cases e
          · rcases changedOwned x e1 with e2 | e2 | e2 | e2 | e2 <;> subst e2
            · exfalso
              rw [(Zlib.Gzwrite.SafeInit.uniq_dstates_only uniq' inv'.good.live.hs).1] at e; cases e
            · right
              obtain ⟨a, ga, gs⟩ := blocks.wa
              rw [ga] at e
              cases e
              rw [gs]
              exact Nat.lt_of_le_of_lt (by omega) lim
            · exfalso
              obtain ⟨a, ga, -⟩ := blocks.pa
              rw [(Zlib.Gzwrite.SafeInit.uniq_words_only uniq' ga).1] at e; cases e
            · exfalso
              obtain ⟨a, ga, -⟩ := blocks.qa
              rw [(Zlib.Gzwrite.SafeInit.uniq_words_only uniq' ga).1] at e; cases e
            · right
              obtain ⟨a, ga, gs⟩ := blocks.ba
              rw [ga] at e
              cases e
              rw [gs]
              exact Nat.lt_of_le_of_lt (by omega) lim
        · left
          rw [← (fr0.2.2.2.2.2 x hl (fun y => y.elim hc hxo)).1]
          exact e
      · exact absurd ((hlive x).1 (Or.inl (by rw [e]; simp))) hl
    · intro x d0 e
      by_cases hxk : x = k
      · subst hxk
        rw [inv'.good.live.hs] at e
        cases e
        right
        rw [I'.wf.2.2.2.2.2]
        exact Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt lim)
      have hl : h.live x := (hlive x).1 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [e]; simp))))))
      by_cases hc : (StreamRoot (gzStrm i) x ∨ DeflateOwned k dk x) ∨ x = ob
      · exfalso
        rcases hc with (e1 | e1) | e1
        · change x = i at e1
          subst e1
          rw [(Zlib.Gzwrite.SafeInit.uniq_gz_only uniq' hs').2.2.2.2.1] at e; cases e
        · rcases changedOwned x e1 with e2 | e2 | e2 | e2 | e2 <;> subst e2
          · exact hxk rfl
          · obtain ⟨a, ga, -⟩ := blocks.wa
            rw [(Zlib.Gzwrite.SafeInit.uniq_bytes_only uniq' ga).1] at e; cases e
          · obtain ⟨a, ga, -⟩ := blocks.pa
            rw [(Zlib.Gzwrite.SafeInit.uniq_words_only uniq' ga).2] at e; cases e
          · obtain ⟨a, ga, -⟩ := blocks.qa
            rw [(Zlib.Gzwrite.SafeInit.uniq_words_only uniq' ga).2] at e; cases e
          · obtain ⟨a, ga, -⟩ := blocks.ba
            rw [(Zlib.Gzwrite.SafeInit.uniq_bytes_only uniq' ga).1] at e; cases e
        · subst e1
          rw [(Zlib.Gzwrite.SafeInit.uniq_bytes_only uniq' hoa').1] at e; cases e
      · left
        exact ⟨d0, by rw [← (fr0.2.2.2.2.2 x hl hc).2.2.2.2.1]; exact e, rfl⟩
  have reach' : StreamReachable .deflate after (gzStrm i) :=
    StreamReachable.step (call := Call.deflateParams (some (gzStrm i)) level strategy) F.reach (fun e => nomatch e)
      ⟨rfl, rfl⟩ ⟨buffers, active⟩ (Zlib.Deflate.Universal.heapCall_run run)
  have hout' : s'.out = s.out := by rw [es']
  have hsz' : s'.size = s.size := by rw [es']
  have hx' : s'.x = s.x := by rw [es']
  have hdir' : s'.direct = s.direct := by rw [es']
  have sh : SameShape s s' := by rw [es']; exact SameShape.refl s
  have output' : OutW5 s' := by
    refine ⟨bo + kp, co, ?_, ?_, by rw [hx', hout']; exact hx, by omega, by rw [hsz']; omega⟩
    · rw [hz', hu6, hnext, advance_padv, hout']
    · rw [hz', hsz']; omega
  have input' : NextInOk s' src := by
    rcases S.up.2.2.2.1 with ⟨hn, h0⟩ | ⟨a, ha, hle⟩
    · have hused : used = 0 := by rw [h0] at hu1; simpa using hu1
      subst hused
      left
      refine ⟨by rw [hz', hu5, hn]; rfl, ?_⟩
      apply UInt32.toNat_inj.mp
      rw [hz']
      rw [h0] at hu3
      simp only [UInt32.toNat_zero] at hu3 ⊢
      omega
    · exact Or.inr ⟨a + used, by rw [hz', hu5, ha, advance_padv], by rw [hz']; omega⟩
  have srcB : src.pointer = s.«in» ∧ src.length ≤ 2 * s.size.toNat ∨ ∃ xs, Bytes after src.pointer src.length xs := by
    rcases S.up.2.2.2.2 with hin | ⟨⟨xs, hb⟩, no⟩
    · exact Or.inl hin
    · exact Or.inr ⟨xs, bytes_after hb no (fun r o hroot => get_of_frame frG hbor r o hroot)⟩
  obtain ⟨U', hown⟩ := upTo_step S.up S.direct S.size hs' sh frD hdata hso hlive inv'.good.fresh uniq'
    inv'.globals fit reach' ⟨k, d', by rw [hz', hu7]; exact hk, inv'.good.live.hs, by rw [gzEq]; exact hhead⟩
    (by rw [es']; exact F.reset) output' input' srcB
  exact ⟨rc, after, s', run, hs', ⟨U', hdir'.trans S.direct, hsz'.symm ▸ S.size⟩, frG, hlive, hown, es', hbor⟩


/-- `deflateParams` on the embedded stream of a writer without codec (`strm.state = NULL`) refuses. -/
theorem params_nostate {H : Heap} {v : GzState} (hs : H.gzstates i = some v) (hn : v.strm.state = none)
    (level strategy : Int32) :
    Zlib.Deflate.deflateParams (strmOf (gzSt i)) level strategy H = .ok (Z_STREAM_ERROR, H) := by
  have hget : (ZStreamRef.in_gzstate_strm i).get H = some v.strm := by simp [ZStreamRef.get, hs]
  have hD : Zlib.Deflate.Spec.StreamDom H (some (.in_gzstate_strm i)) :=
    Or.inr ⟨_, _, rfl, hget, Or.inr (Or.inr (Or.inl hn))⟩
  have hN : ¬ Zlib.Deflate.Spec.DInitialised H (some (.in_gzstate_strm i)) := by
    rintro ⟨r, ds, z, d, hr, hL⟩
    cases hr
    have e := hL.hz
    rw [hget] at e
    cases e
    have := hL.zst
    rw [hn] at this
    cases this
  have hck : Zlib.Deflate.deflateStateCheck (strmOf (gzSt i)) H = .ok (1, H) :=
    Zlib.Deflate.Proofs.notInit_check hD hN
  unfold Zlib.Deflate.deflateParams
  simp only [C.bind_app, hck]
  rfl

/-- `gzsetparams` from the store of the parameters on. -/
def setTail (i : Nat) (level strategy : Int32) : G Int32 := do
  updS (gzSt i) fun s => { s with level, strategy }
  return Z_OK

/-- `gzsetparams` from `deflateParams` on. -/
def setDP (i : Nat) (level strategy : Int32) : G Int32 := do
  let _ ← Zlib.Deflate.deflateParams (strmOf (gzSt i)) level strategy
  setTail i level strategy

/-- `gzsetparams` after the pending skip. -/
def paramsT (i : Nat) (level strategy : Int32) : G Int32 := do
  if (← ldS (gzSt i)).size != 0 then
    if (← ldZ (strmOf (gzSt i))).avail_in != 0 then
      if (← Zlib.Gzwrite.gz_comp (gzSt i) Z_BLOCK) == -1 then return (← ldS (gzSt i)).err
    setDP i level strategy
  else setTail i level strategy

theorem gzsetparams_eq (level strategy : Int32) :
    Zlib.Gzwrite.gzsetparams (some (.in_gzstate_x i)) level strategy = (do
      let s ← ldS (gzSt i)
      if s.mode != GZ_WRITE || (s.err != Z_OK && s.again == 0) || s.direct != 0 then return Z_STREAM_ERROR
      Zlib.Gzlib.gz_error (gzSt i) Z_OK .null
      let s ← ldS (gzSt i)
      if level == s.level && strategy == s.strategy then return Z_OK
      if s.skip != 0 then
        if (← Zlib.Gzwrite.gz_zero (gzSt i)) == -1 then return (← ldS (gzSt i)).err
      paramsT i level strategy : G Int32) := rfl

theorem setTail_ok {h0 : Heap} {s0 : GzState} {fs0 fs : Fs} {H : Heap} {v : GzState}
    (E : GetcUngetc.Eff i h0 s0 fs0 fs H) (inv : GzInv H i v) (hw : v.mode = GZ_WRITE) (level strategy : Int32) :
    ∃ r fs' h', setTail i level strategy fs H = .ok ((r, fs'), h') ∧ GetcUngetc.Eff i h0 s0 fs0 fs' h' := by
  have hs := inv.common.record
  have c := inv.common
  have w := inv.writer hw
  have inv' : GzInv (putGz H i { v with level, strategy }) i { v with level, strategy } :=
    GzInv.put_scalars inv ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨c.want.1, c.want.2, Or.inr rfl⟩ c.pos
      (Nat.le_refl _) (fun hr => absurd (hw.symm.trans hr) (by decide)) (fun _ => w.reset)
      (fun hr => absurd (hw.symm.trans hr) (by decide))
  have P := post_put (P := GzInv) (fs := fs) (v := { v with level, strategy }) hs c.live E.2.1
    (owned_rec (v := { v with level, strategy }) hs rfl rfl rfl rfl rfl rfl rfl rfl) rfl rfl inv'
  have hU : updS (gzSt i) (fun s => { s with level, strategy }) H = .ok ((), putGz H i { v with level, strategy }) :=
    Zlib.Gzlib.Proofs.updS_run hs _
  refine ⟨Z_OK, fs, _, ?_, GetcUngetc.Eff.trans E inv P (fun _ => Iff.rfl)⟩
  unfold setTail
  simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hU]

theorem setDP_ok {h0 : Heap} {s0 : GzState} {fs0 fs : Fs} {H : Heap} {v : GzState}
    (E : GetcUngetc.Eff i h0 s0 fs0 fs H) (inv : GzInv H i v) (hw : v.mode = GZ_WRITE) (hsz : v.size ≠ 0)
    (level strategy : Int32) :
    ∃ r fs' h', setDP i level strategy fs H = .ok ((r, fs'), h') ∧ GetcUngetc.Eff i h0 s0 fs0 fs' h' := by
  have hs := inv.common.record
  have hfs : FileSystem fs := E.2.1
  by_cases hd : v.direct = 0
  · have S : St i ⟨v.«in», v.size.toNat⟩ H v := ⟨upTo_of_inv inv hw hsz, hd, hsz⟩
    obtain ⟨rc, H2, s2, run, hs2, S2, fr, hl, ho, es2, -⟩ := params_step S level strategy
    have run' : Zlib.Deflate.deflateParams (strmOf (gzSt i)) level strategy H = .ok (rc, H2) := run
    have hin2 : s2.«in» = v.«in» := by rw [es2]
    have hsize2 : s2.size = v.size := by rw [es2]
    have hm2 : s2.mode = v.mode := by rw [es2]
    have hfd2 : s2.fd = v.fd := by rw [es2]
    obtain ⟨-, invC, hw2, inp, -⟩ := S2.up
    have inv2 : GzInv H2 i s2 := by
      refine inv_of_clear hs2 invC hw2 ?_
      rcases inp with hn | ⟨a, ha, hle⟩
      · exact Or.inl hn
      · exact Or.inr ⟨by rw [hsize2]; exact hsz, a, by rw [hin2]; exact ha, by rw [hsize2]; exact hle⟩
    have E2 := GetcUngetc.Eff.trans E inv (post_frame inv.common.live hfs fr hl ho hm2 hfd2 inv2) (fun _ => Iff.rfl)
    obtain ⟨r, fs', h', runT, E'⟩ := setTail_ok E2 inv2 (hm2.trans hw) level strategy
    refine ⟨r, fs', h', ?_, E'⟩
    unfold setDP
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, run']
    exact runT
  · have hn : v.strm.state = none := (inv.writer hw).transparent hd
    obtain ⟨r, fs', h', runT, E'⟩ := setTail_ok E inv hw level strategy
    refine ⟨r, fs', h', ?_, E'⟩
    unfold setDP
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app,
      params_nostate hs hn level strategy]
    exact runT

theorem paramsT_ok (err : GzErrorSpec) (errOwn : GzErrorOwn) {h0 : Heap} {s0 : GzState} {fs0 fs : Fs} {H : Heap} {v : GzState}
    (E : GetcUngetc.Eff i h0 s0 fs0 fs H) (inv : GzInv H i v) (hw : v.mode = GZ_WRITE) (level strategy : Int32) :
    ∃ r fs' h', paramsT i level strategy fs H = .ok ((r, fs'), h') ∧ GetcUngetc.Eff i h0 s0 fs0 fs' h' := by
  have hs := inv.common.record
  have hfs : FileSystem fs := E.2.1
  have hS : ldS (gzSt i) H = .ok (v, H) := Zlib.Gzlib.Proofs.ldS_run hs
  have hZ : ldZ (strmOf (gzSt i)) H = .ok (v.strm, H) := Zlib.Gzlib.Proofs.ldZ_run hs
  by_cases hsz : v.size = 0
  · have hszB : (v.size != 0) = false := by simp [hsz]
    obtain ⟨r, fs', h', runT, E'⟩ := setTail_ok E inv hw level strategy
    refine ⟨r, fs', h', ?_, E'⟩
    unfold paramsT
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
      hszB, Bool.false_eq_true, ↓reduceIte]
    exact runT
  have hszB : (v.size != 0) = true := by simpa using hsz
  by_cases hav : v.strm.avail_in = 0
  · have havB : (v.strm.avail_in != 0) = false := by simp [hav]
    obtain ⟨r, fs', h', runT, E'⟩ := setDP_ok E inv hw hsz level strategy
    refine ⟨r, fs', h', ?_, E'⟩
    unfold paramsT
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
      hszB, ↓reduceIte, hZ, havB, Bool.false_eq_true]
    exact runT
  have havB : (v.strm.avail_in != 0) = true := by simpa using hav
  have R := gz_comp_safe_shape_of' err errOwn i Z_BLOCK ⟨v.«in», v.size.toNat⟩ H fs v (upTo_of_inv inv hw hsz) hfs hsz
    (by decide)
  obtain ⟨r, fs2, H2, run2⟩ := R.2.1 trivial
  obtain ⟨hr, k2, p2⟩ := R.2.2 r fs2 H2 run2
  have E2 : GetcUngetc.Eff i h0 s0 fs0 fs2 H2 :=
    ⟨(GetcUngetc.EffI.trans GetcUngetc.good_inv (good_cq ⟨v.«in», v.size.toNat⟩ v H Z_BLOCK r) E hs p2 k2).1,
      GzPost.mono (GetcUngetc.EffI.trans GetcUngetc.good_inv (good_cq ⟨v.«in», v.size.toNat⟩ v H Z_BLOCK r) E hs p2 k2).2
        fun _ _ _ q => inv_of_cq' hsz q⟩
  obtain ⟨-, s2, q2, hm2, -⟩ := id p2
  have inv2 : GzInv H2 i s2 := inv_of_cq' hsz q2
  have hS2 : ldS (gzSt i) H2 = .ok (s2, H2) := Zlib.Gzlib.Proofs.ldS_run inv2.common.record
  rcases hr with rfl | rfl
  · obtain ⟨r, fs', h', runT, E'⟩ := setDP_ok E2 inv2 (hm2.trans hw) (by rw [q2.2.1.2.2.2.1]; exact hsz) level strategy
    refine ⟨r, fs', h', ?_, E'⟩
    unfold paramsT
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
      hszB, ↓reduceIte, hZ, havB, run2, int32_zero_ne_neg_one, Bool.false_eq_true]
    exact runT
  · refine ⟨s2.err, fs2, H2, ?_, E2⟩
    unfold paramsT
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
      hszB, ↓reduceIte, hZ, havB, run2, beq_self_eq_true, hS2]

/-- **`gzsetparams_step`** (skeleton statement), given the facts of `gz_error`. `gz_comp(state, Z_BLOCK)` is
`gz_comp_safe_shape_of'` at flush 5; `deflateParams` is a step of the deflate history (`params_step`). -/
theorem gzsetparams_step_of (err : GzErrorSpec) (errOwn : GzErrorOwn) (i : Nat)
    (level strategy : Int32) : GzCallSafe i (.gzsetparams (some (.in_gzstate_x i)) level strategy) := by
  intro h fs s inv hfs _
  have R : Ok (Zlib.Gzwrite.gzsetparams (some (.in_gzstate_x i)) level strategy) fs h
      (fun _ fs' after => GetcUngetc.Eff i h s fs fs' after) := by
    rw [gzsetparams_eq]
    have hS : ldS (gzSt i) h = .ok (s, h) := Zlib.Gzlib.Proofs.ldS_run inv.common.record
    by_cases hm : (s.mode != GZ_WRITE || (s.err != Z_OK && s.again == 0) || s.direct != 0) = true
    · refine ⟨Z_STREAM_ERROR, fs, h, ?_, GetcUngetc.Eff.refl inv hfs⟩
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
        hm, ↓reduceIte]
    have hm' := Bool.eq_false_iff.mpr hm
    have hw : s.mode = GZ_WRITE := by
      refine Classical.byContradiction fun hne => ?_
      simp [hne] at hm'
    obtain ⟨run1, inv1, post1⟩ := clear_step (fs := fs) inv hfs
    have E1 : GetcUngetc.Eff i h s fs fs (okHeap h i s) :=
      GetcUngetc.Eff.trans (GetcUngetc.Eff.refl inv hfs) inv post1 (fun _ => Iff.rfl)
    have hS1 : ldS (gzSt i) (okHeap h i s) = .ok (okRec s, okHeap h i s) :=
      Zlib.Gzlib.Proofs.ldS_run inv1.common.record
    by_cases hq : (level == (okRec s).level && strategy == (okRec s).strategy) = true
    · refine ⟨Z_OK, fs, okHeap h i s, ?_, E1⟩
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
        hm', Bool.false_eq_true, ↓reduceIte, run1, hS1, hq]
    have hq' := Bool.eq_false_iff.mpr hq
    by_cases hk : (okRec s).skip = 0
    · have hkB : ((okRec s).skip != 0) = false := by simp [hk]
      obtain ⟨r, fs', h', run, E'⟩ := paramsT_ok err errOwn E1 inv1 hw level strategy
      refine ⟨r, fs', h', ?_, E'⟩
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
        hm', Bool.false_eq_true, ↓reduceIte, run1, hS1, hq', hkB]
      exact run
    · have hkB : ((okRec s).skip != 0) = true := by simpa using hk
      obtain ⟨r, fs2, H2, run2, hr, k2, post2, -⟩ := zero_any err errOwn inv1 hfs hw
      have E2 := GetcUngetc.Eff.trans E1 inv1 post2 k2
      obtain ⟨-, -, s2, inv2, hm2, -⟩ := id E2
      rcases hr with rfl | rfl
      · obtain ⟨r, fs', h', run, E'⟩ := paramsT_ok err errOwn E2 inv2 (hm2.trans hw) level strategy
        refine ⟨r, fs', h', ?_, E'⟩
        simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
          hm', Bool.false_eq_true, ↓reduceIte, run1, hS1, hq', hkB, run2, int32_zero_ne_neg_one]
        exact run
      · have hS2 : ldS (gzSt i) H2 = .ok (s2, H2) := Zlib.Gzlib.Proofs.ldS_run inv2.common.record
        refine ⟨s2.err, fs2, H2, ?_, E2⟩
        simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
          hm', Bool.false_eq_true, ↓reduceIte, run1, hS1, hq', hkB, run2, beq_self_eq_true, hS2]
  have RS := runSafe_of_ok R
  exact ⟨RS.1, fun _ => RS.2.1 trivial, fun v fs' after he => GetcUngetc.Eff.post rfl (RS.2.2 v fs' after he)⟩

end params

end ZlibF.Spec.Public.GzSkeleton
