import ZlibF.Proof.«public-compress-safe-end»

/-!
# compress.c: safety of `compress2_z`, `compress2`, `compress_z` and `compress`

`Goal.compress2_z_safety` and its wrappers, from the public goal `Goal.deflate` and the four
deflate facts `DeflateLoopFacts`, both explicit hypotheses. `deflateInit_` and `deflateEnd` are
used through their proved lemmas (`deflateInit_proof` and its parts, `deflateEnd_safe`,
`deflate_end_public`). The loop terminates by the measure of `public-compress-safe-loop`.
-/

namespace ZlibF.Spec.Public.Proofs.Compress
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Compress Zlib.Deflate
open ZlibF.Spec.Public.Proofs.Uncompress hiding measure
open Zlib.Deflate.Spec (DGood)
set_option autoImplicit false

/-- Editing only the buffer fields of the record of a stream at a table entry is a rebuffer. -/
theorem rebuffer_tab {H : Heap} {k i : Nat} {z z1 : ZStream} {s : DeflateState}
    (good : DGood H (.tab k) i z s) (glob : LibraryGlobals H) (notOwn : ¬ DeflateOwned i s k)
    (form : z1 = { z with
      next_in := z1.next_in, avail_in := z1.avail_in
      next_out := z1.next_out, avail_out := z1.avail_out }) :
    Rebuffer H ((ZStreamRef.tab k).put H z1) (.tab k) := by
  have hz : H.streams k = some z := good.live.hz
  have H1eq : (ZStreamRef.tab k).put H z1 = { H with streams := upd H.streams k (some z1) } := put_tab_eq hz
  have hz1 : (ZStreamRef.tab k).get ((ZStreamRef.tab k).put H z1) = some z1 :=
    Zlib.Deflate.Proofs.ZStreamRef.get_put_same good.live.hz _
  refine ⟨by rw [H1eq]; exact fresh_put_tab hz z1 good.fresh,
    by rw [H1eq]; exact uniq_put_tab hz z1 (by exact good.uniq), by rw [H1eq]; exact glob, ?_,
    z, z1, good.live.hz, hz1, form⟩
  refine ⟨by rw [H1eq], by rw [H1eq], by rw [H1eq], by rw [H1eq]; exact Nat.le_refl _,
    by rw [H1eq]; exact Nat.le_refl _, ?_⟩
  intro b live notChanged
  by_cases bk : b = k
  · exfalso
    subst bk
    exact notChanged (fun own => notOwn ((good_owned good b).1 own))
  · rcases put_tab_same hz z1 b with x | x
    · rw [H1eq]
      obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ := x
      exact ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩
    · exact absurd x bk

theorem same_refl (h : Heap) : SameObjectsUpToTableShape h h :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩

set_option maxRecDepth 10000 in
/-- Safety of `compress2_z` at every level, from `Goal.deflate` and `DeflateLoopFacts`. -/
theorem compress2_z_safety_of (call : Goal.deflate) (facts : DeflateLoopFacts) : Goal.compress2_z_safety := by
  intro level h dest capacity source n xs fresh uniq globals fit _ args
  by_cases rej : compressRejected dest capacity source n
  · -- the argument checks refuse before anything is made
    have run : C.run (compress2_z dest capacity source n level) h = .ok ((Z_STREAM_ERROR, capacity), h) := by
      rcases rej with c0 | ⟨sn, n0⟩ | ⟨c, rfl, dn, c0⟩
      · subst c0; rfl
      · cases capacity with
        | none => rfl
        | some c =>
          have npos : (decide (n > 0)) = true := by
            simp only [decide_eq_true_eq, gt_iff_lt, UInt64.lt_iff_toNat_lt, UInt64.toNat_zero]
            have : n.toNat ≠ 0 := fun e => n0 (UInt64.toNat_inj.mp (by simpa using e))
            omega
          simp [C.run, compress2_z, npos, sn]
      · have cpos : (decide (c > 0)) = true := by
          simp only [decide_eq_true_eq, gt_iff_lt, UInt64.lt_iff_toNat_lt, UInt64.toNat_zero]
          have : c.toNat ≠ 0 := fun e => c0 (UInt64.toNat_inj.mp (by simpa using e))
          omega
        simp [C.run, compress2_z, cpos, dn]
    exact ⟨Z_STREAM_ERROR, capacity, h, [], h, run, Or.inl ⟨rfl, rfl⟩, same_refl h, Nat.zero_le _,
      fun e => absurd e (by decide), fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩
  · rcases args with r0 | ⟨c, rfl, srcB, destW, sep⟩
    · exact absurd r0 rej
    have a1 : ¬ (n > 0 ∧ source = .null) := fun x => rej (Or.inr (Or.inl ⟨x.2, by
      intro e; rw [e] at x; exact absurd x.1 (by decide)⟩))
    have a2 : ¬ (c > 0 ∧ dest = .null) := fun x => rej (Or.inr (Or.inr ⟨c, rfl, x.2, by
      intro e; rw [e] at x; exact absurd x.1 (by decide)⟩))
    have harg : ((decide (n > 0) && source == .null) || (decide (c > 0) && dest == .null)) = false := by
      cases hb : ((decide (n > 0) && source == .null) || (decide (c > 0) && dest == .null))
      · rfl
      · simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hb
        rcases hb with x | x
        · exact absurd x a1
        · exact absurd x a2
    have slot : ({ h with allocOk := fun _ => true } : Heap).slotUsed h.nextBlk = false := fresh.slotUsed_next
    unfold compress2_z
    simp [C.run, harg, allocLocalZ, allocZStream, slot, zwr, zrd, ldZStream,
      stZStream, ZStreamRef.get, ZStreamRef.put, ZStreamRef.isRo, version_run, upd_upd]
    generalize hI : deflateInit_ _ _ _ _ _ = I
    have hI' : deflateInit_ (some (.tab h.nextBlk)) level (.ref (.str 57) 0) 112 (cHeap h) = I := hI
    obtain ⟨rc, after, initRun, outcome⟩ := init_cases fresh uniq globals level
    rw [initRun] at hI'
    subst hI'
    rcases outcome with ⟨rcNe, u2, liveA, frameA, ⟨z', hz'⟩, memA⟩ | ⟨rfl, -, p, initial⟩
    · -- `deflateInit` failed: free the stream and return
      have hzA : after.streams h.nextBlk = some z' := hz'
      refine ⟨rc, some 0, { after with streams := upd after.streams h.nextBlk none }, ?_, [], h,
        Or.inl ⟨rfl, rfl⟩, init_failure_heap fresh u2 liveA frameA hzA, Nat.zero_le _, ?_, fun r => absurd r rej⟩
      · simp [rcNe, freeZStream, hzA]
      · intro m
        obtain ⟨j, lo, hi, bad⟩ := memA m
        exact ⟨j, lo, hi, bad⟩
    · -- the initial loop state
      obtain ⟨z, s, good, -, zfree, -, -, -, -, -, -, -, -, -, gzhead, -, -, -, frameI, liveI, ownedI⟩ := initial
      let e : CEnv := ⟨h, dest, source, xs, n.toNat, c.toNat⟩
      have ok : COK e := ⟨fresh, globals, srcB, destW, sep, bytes_bound srcB fit, writable_bound destW fit⟩
      have k0 : ¬ h.live h.nextBlk := fresh _ (Nat.le_refl _)
      have hzA : after.streams h.nextBlk = some z := good.live.hz
      let z0 : ZStream := { z with next_in := source, avail_in := 0, next_out := dest, avail_out := 0 }
      have globalsA : LibraryGlobals after := by
        have := frameI.1
        simp only [LibraryGlobals, cHeap] at globals ⊢
        rw [← this]; exact globals
      have notOwnK : ¬ DeflateOwned (h.nextBlk + 1) s h.nextBlk := by
        intro o; have := (ownedI h.nextBlk).1 o; simp only [cHeap] at this; omega
      have rb := rebuffer_tab (z1 := z0) good globalsA notOwnK (by simp [z0])
      have initRun2 : C.run (deflateInit2_ (some (.tab h.nextBlk)) level Z_DEFLATED MAX_WBITS DEF_MEM_LEVEL
          Z_DEFAULT_STRATEGY (.ref (.str 57) 0) 112) (cHeap h) = .ok (Z_OK, after) := initRun
      have reachI : StreamReachable .deflate after (.tab h.nextBlk) :=
        StreamReachable.deflateInit (cHeap_fresh fresh) (cHeap_uniq fresh uniq) (cHeap_globals globals)
          (cHeap_get h) (cStream_default h) (version_value (cHeap h)) initRun2
      obtain ⟨z0', hz0', -, good0⟩ := Zlib.Deflate.Universal.rebuffer_good good rb
      have H0eq : (ZStreamRef.tab h.nextBlk).put after z0 =
          { after with streams := upd after.streams h.nextBlk (some z0) } := put_tab_eq hzA
      have ez : z0' = z0 := by
        have := Zlib.Deflate.Proofs.ZStreamRef.get_put_same (r := .tab h.nextBlk) good.live.hz z0
        exact Option.some.inj (hz0'.symm.trans this)
      subst ez
      have sameA : ∀ b, h.live b → SameAt h { after with streams := upd after.streams h.nextBlk (some z0) } b := by
        intro b lb
        have bk : b ≠ h.nextBlk := fun x => k0 (x ▸ lb)
        have notOwnB : ¬ DeflateOwned (h.nextBlk + 1) s b := by
          intro o; have := (ownedI b).1 o; have := fresh.lt lb; simp [cHeap] at *; omega
        obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ :=
          frameI.2.2.2.2.2 b ((cHeap_live h b).2 (Or.inl lb)) (by simp only [StreamRoot]; exact bk)
        simp only [cHeap, upd_ne _ _ _ _ bk] at t1 t2 t3 t4 t5 t6 t7 t8
        exact ⟨t1, t2, by simp [upd_ne _ _ _ _ bk, t3], t4, t5, t6, t7, t8⟩
      have borrowA : after.libcErrorBorrow = h.libcErrorBorrow := by
        have := Zlib.Deflate.BorrowProofs.stable_deflateInit_ (some (.tab h.nextBlk)) level (.ref (.str 57) 0) 112
          (cHeap h) Z_OK after initRun
        simpa [cHeap] using this
      have cs0 : CState e (Z_OK, c, n) { after with streams := upd after.streams h.nextBlk (some z0) } [] 0 z0 s := by
        refine
          { reach := by rw [← H0eq]; exact .rebuffer reachI rb (fun e => by cases e)
            good := by rw [← H0eq]; exact good0
            zfree := zfree
            gzhead := gzhead
            owned := fun b => by
              show DeflateOwned (h.nextBlk + 1) s b ↔ h.nextBlk + 1 ≤ b ∧ b < h.nextBlk + 6
              rw [show h.nextBlk + 6 = (h.nextBlk + 1) + 5 by omega]
              exact ownedI b
            inCount := by show 0 + (0 : UInt32).toNat + n.toNat = n.toNat; simp
            nextIn := by show source = advance source 0; rw [advance_zero]
            outCount := by show ([] : List UInt8).length + (0 : UInt32).toNat + c.toNat = c.toNat; simp
            nextOut := by show dest = advance dest ([] : List UInt8).length; rw [List.length_nil, advance_zero]
            agree := ?_
            liveOnly := ?_
            nalloc := ?_ }
        · rw [writeOut_nil]
          refine ⟨sameA, ?_, ?_, ?_, ?_⟩
          · have := frameI.1; simp [cHeap] at this; exact this.symm
          · have := frameI.2.1; simp [cHeap] at this; exact this.symm
          · have := frameI.2.2.1; simp [cHeap] at this; exact this.symm
          · exact borrowA
        · intro b lb
          have l1 : after.live b := by
            by_cases bk : b = h.nextBlk
            · subst bk; simp [Heap.live, hzA]
            · simpa [Heap.live, upd_ne _ _ _ _ bk] using lb
          rcases (liveI b).1 l1 with ⟨lc, -⟩ | o
          · rcases (cHeap_live h b).1 lc with x | x
            · exact Or.inl x
            · exact Or.inr (Or.inl x)
          · right; right
            have := (ownedI b).1 o
            simpa [cHeap, CEnv.k] using this
        · have := frameI.2.2.2.2.1
          simp [cHeap] at this
          exact this
      -- the loop
      simp [ldZStream, stZStream, ZStreamRef.get, ZStreamRef.put, ZStreamRef.isRo, hzA]
      generalize hres : cdoWhile _ _ _ _ = res
      obtain ⟨st', H', loopEq, code', out, used, zf, sf, csf⟩ :=
        loop_result call facts ok cs0 (Or.inl rfl) hres (k := h.nextBlk) rfl (by cbody_ok) (fun _ _ => rfl)
      rw [loopEq]
      -- the cleanup
      obtain ⟨d, rcE, H2, diffRun, endRun, freeRun, store, same, outLe⟩ := epilogue ok csf
      have hzf : H'.streams h.nextBlk = some zf := csf.good.live.hz
      have endRun' : deflateEnd (some (.tab h.nextBlk)) H' = .ok (rcE, H2) := endRun
      have freeRun' : freeZStream (some (.tab h.nextBlk)) H2 =
          .ok ((), { H2 with streams := upd H2.streams h.nextBlk none }) := freeRun
      have diffRun' : ptrDiff zf.next_out dest H' = .ok (d, H') := diffRun
      refine ⟨if st'.1 = Z_STREAM_END then Z_OK else st'.1, some d.toUInt64,
        { H2 with streams := upd H2.streams h.nextBlk none }, ?_, out, writeOut h dest out, store, same,
        outLe, ?_, fun r => absurd r rej⟩
      · simp [hzf, diffRun', endRun', freeRun']
      · intro m
        exfalso
        rcases code' with x | x | x | x <;> rw [x] at m <;> exact absurd m (by decide)

/-- Safety of `compress_z`: `compress2_z` at the default level. -/
theorem compress_z_safety_of (call : Goal.deflate) (facts : DeflateLoopFacts) : Goal.compress_z_safety :=
  compress2_z_safety_of call facts Z_DEFAULT_COMPRESSION

/-- Safety of `compress2`: the wrapper reads the length cell and calls `compress2_z`. -/
theorem compress2_safety_of (call : Goal.deflate) (facts : DeflateLoopFacts) : Goal.compress2_safety := by
  intro level h dest capacity source n xs fresh uniq globals fit nn args
  cases capacity with
  | none => exact absurd rfl (nn rfl)
  | some got =>
    obtain ⟨rc, stored, after, out, expected, run, store, same, le, mem, rejC⟩ :=
      compress2_z_safety_of call facts level h dest (some got) source n xs fresh uniq globals fit
        (fun e => absurd e (by decide)) args
    have run' : compress2_z dest (some got) source n level h = .ok ((rc, stored), after) := run
    refine ⟨rc, some (stored.getD got), after, out, expected, ?_, store, same, le, mem, ?_⟩
    · simp [C.run, compress2, run']
    · intro rej
      obtain ⟨r1, r2, r3, r4⟩ := rejC rej
      exact ⟨r1, by rw [r2]; rfl, r3, r4⟩

/-- Safety of `compress`: `compress2` at the default level. -/
theorem compress_safety_of (call : Goal.deflate) (facts : DeflateLoopFacts) : Goal.compress_safety :=
  compress2_safety_of call facts Z_DEFAULT_COMPRESSION

#print axioms compress2_z_safety_of
#print axioms compress2_safety_of
#print axioms compress_z_safety_of
#print axioms compress_safety_of

end ZlibF.Spec.Public.Proofs.Compress
