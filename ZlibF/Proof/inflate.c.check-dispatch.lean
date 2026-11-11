import ZlibF.Proof.«inflate.c.main.check»
import ZlibF.Proof.«inflate.c.leave-checksum-general»
import ZlibF.Proof.«inflate.c.dictid-dispatch»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The real CHECK mode accepts every represented readable output view.
The returned checksum is obtained from the actual translated callee for every seed. -/
theorem inflate_CHECK_views_run {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {bs : List UInt8} (out : UInt32) (hout : out = l.out_ - l.left)
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (hz : r.get h = some z)
    (hs : h.istates zs = some s) (hw : s.wrap ≠ 0) (B : BitInv h l bs) (hS : Zlib.Crc32.Proofs.StaticsOK h)
    (hput : chkCond s out = true → ∃ ref off array, l.put = .ref ref off ∧
      Space.get h ref = some array ∧ out.toNat ≤ off ∧ off ≤ array.size) :
    ∃ rr l' j, runX (NEEDBITS 32) l h = .ok ((rr, l'), h) ∧ j ≤ bs.length ∧ BitInv h l' (bs.drop j) ∧
      stream l' (bs.drop j) = stream l bs ∧
      (rr = .error Ex.leave → l'.have_ = 0 ∧ j = bs.length ∧ l'.bits.toNat < 32 ∧
        runX (inflate_CHECK c) l h = .ok ((.error Ex.leave, l'), h)) ∧
      (rr = .ok () → 32 ≤ l'.bits.toNat ∧ ∃ v,
        ((s.wrap &&& 4) ≠ 0 → (if s.flags ≠ 0 then l'.hold else ZSWAP32 l'.hold) ≠ (chkS s out v).check →
          ∃ i, strTable[i]? = some "incorrect data check" ∧
            runX (inflate_CHECK c) l h =
              .ok ((.ok (), { l' with out_ := l.left }), tcBadHeap (chkH h r zs z s out v) r zs (chkZ z s out v) (chkS s out v) i)) ∧
        (¬ ((s.wrap &&& 4) ≠ 0 ∧ (if s.flags ≠ 0 then l'.hold else ZSWAP32 l'.hold) ≠ (chkS s out v).check) →
          runX (inflate_CHECK c) l h =
            runX (inflate_LENGTH c) { l' with out_ := l.left, hold := 0, bits := 0 }
              (setI (chkH h r zs z s out v) zs { chkS s out v with mode := LENGTH }))) := by
  obtain ⟨rr, l', j, hrun, hj, B', hS', hbits, hshape, hmax, hid, hok, hleave⟩ := NEEDBITS_run B 32 (by decide)
  have hw' : ¬ s.wrap = 0 := hw
  have hput' : l'.put = l.put := by rw [hshape]
  have hleft' : l'.left = l.left := by rw [hshape]
  have hout' : l'.out_ = l.out_ := by rw [hshape]
  refine ⟨rr, l', j, hrun, hj, B', hS', ?_, ?_⟩
  · intro e
    obtain ⟨h1, h2, h3⟩ := hleave e
    refine ⟨h2, h1, h3, ?_⟩
    unfold inflate_CHECK
    rw [hc]
    simp [runX_bind, runX_lift, ldI_eq, hs, hw', hrun, e, runX_throw]
  · intro e
    refine ⟨hok e, ?_⟩
    by_cases hcond : chkCond s out = true
    · obtain ⟨ref, off, a, hp, hb, ho1, ho2⟩ := hput hcond
      have hct' : chkCond s (l.out_ - l.left) = true := by rw [← hout]; exact hcond
      have hct3 : ¬ s.wrap &&& 4 = 0 ∧ ¬ l.out_ - l.left = 0 := by
        simpa [chkCond, ← hout] using hcond
      -- the heap after `total_out += out; total += out`
      let h1 : Heap := setI (r.put h { z with total_out := z.total_out + out.toUInt64 }) zs
        { s with total := s.total + out.toUInt64 }
      have hg1 : (Space.get h1 ref : Option (Array UInt8)) = some a := by
        rw [byte_view_get_setI, byte_view_get_stream_put]
        exact hb
      have hs1 : h1.istates zs = some { s with total := s.total + out.toUInt64 } := by simp [h1]
      have hS1 : Zlib.Crc32.Proofs.StaticsOK h1 := by
        simpa only [Zlib.Crc32.Proofs.StaticsOK, h1, setI, ZStreamRef.put_static] using hS
      have hptr : Ptr.add l.put (-(out.toNat : Int)) h1 = .ok (.ref ref (off - out.toNat), h1) := by
        rw [hp]; exact Ptr.sub_nat_ok hg1 ho1 ho2
      let v := inflateChecksumValue s.flags s.check ((a.toList.drop (off - out.toNat)).take out.toNat)
      have hv : UPDATE_CHECK (some (.tab zs)) s.check (.ref ref (off - out.toNat)) out h1 = .ok (v, h1) :=
        UPDATE_CHECK_all_views hS1 hs1 hg1 (by omega) s.check
      have hptr2 := hptr
      have hv2 := hv
      simp [h1, hout] at hptr2 hv2
      refine ⟨v, ?_, ?_⟩
      · intro hbad hne
        have hz2 : r.get (chkH h r zs z s out v) = some (chkZ z s out v) := by
          simp [chkH, hz]
        have hs2 : (chkH h r zs z s out v).istates zs = some (chkS s out v) := by simp [chkH]
        obtain ⟨i, hi, hbm⟩ := tcBadMode_run (c := c) "incorrect data check" lit_data_check hr hc hz2 hs2
        refine ⟨i, hi, ?_⟩
        simp [chkH, chkZ, chkS, tcBadHeap, hcond, hct', hout] at hbm
        have hbad2 : (¬ s.wrap &&& 4 = 0 ∧ ¬ (if s.flags = 0 then ZSWAP32 l'.hold else l'.hold) = v) := by
          refine ⟨hbad, ?_⟩
          simp only [chkS, hcond, ↓reduceIte] at hne
          by_cases hf0 : s.flags = 0
          · rw [if_pos hf0]
            rw [if_neg (by simpa using hf0)] at hne
            exact hne
          · rw [if_neg hf0]
            rw [if_pos hf0] at hne
            exact hne
        unfold inflate_CHECK
        rw [hc]
        simp [runX_bind, runX_lift, ldI_eq, hs, hw', hrun, e, hr, runX_modify, runX_get, wrZ_eq, wrI_eq, hz,
          hout, hout', hleft', runX_pure, hct3, hct', hbad2, setMode, runX_INITBITS, chkH, chkZ, chkS, hcond, hbm, chkCond,
          hput', hptr2, hv2]
        simp [tcBadHeap]
      · intro hn
        have hn2 : ¬ (¬ s.wrap &&& 4 = 0 ∧ ¬ (if s.flags = 0 then ZSWAP32 l'.hold else l'.hold) = v) := by
          rintro ⟨ha, hb⟩
          apply hn
          refine ⟨ha, ?_⟩
          simp only [chkS, hcond, ↓reduceIte]
          by_cases hf0 : s.flags = 0
          · rw [if_pos hf0] at hb
            rw [if_neg (by simpa using hf0)]
            exact hb
          · rw [if_neg hf0] at hb
            rw [if_pos hf0]
            exact hb
        have hn3 : (if s.flags = 0 then ZSWAP32 l'.hold else l'.hold) = v := by
          by_cases hh : (if s.flags = 0 then ZSWAP32 l'.hold else l'.hold) = v
          · exact hh
          · exact absurd ⟨hct3.1, hh⟩ hn2
        unfold inflate_CHECK
        rw [hc]
        simp [runX_bind, runX_lift, ldI_eq, hs, hw', hrun, e, hr, runX_modify, runX_get, wrZ_eq, wrI_eq, hz,
          hout, hout', hleft', runX_pure, hct3, hct', hn3, setMode, runX_INITBITS, chkH, chkZ, chkS, hcond, chkCond,
          hput', hptr2, hv2]
    · have hcf : chkCond s out = false := by simpa using hcond
      have hcf' : chkCond s (l.out_ - l.left) = false := by rw [← hout]; exact hcf
      have hcf2 : ¬ ((s.wrap &&& 4) != 0 && (l.out_ - l.left) != 0) = true := by
        simpa [chkCond, ← hout] using hcond
      have hcf3 : ¬ (¬ s.wrap &&& 4 = 0 ∧ ¬ l.out_ - l.left = 0) := by
        simpa [chkCond, ← hout] using hcond
      refine ⟨s.check, ?_, ?_⟩
      · intro hbad hne
        have hz2 : r.get (chkH h r zs z s out s.check) = some (chkZ z s out s.check) := by
          simp [chkH, hz]
        have hs2 : (chkH h r zs z s out s.check).istates zs = some (chkS s out s.check) := by simp [chkH]
        obtain ⟨i, hi, hbm⟩ := tcBadMode_run (c := c) "incorrect data check" lit_data_check hr hc hz2 hs2
        refine ⟨i, hi, ?_⟩
        have hcf4 : l.out_ - l.left = 0 := by
          by_cases hz0 : l.out_ - l.left = 0
          · exact hz0
          · exact absurd ⟨hbad, hz0⟩ hcf3
        simp [chkH, chkZ, chkS, tcBadHeap, hcf, hcf', hout, hcf4, chkCond] at hbm
        have hbad2 : (¬ s.wrap &&& 4 = 0 ∧ ¬ (if s.flags = 0 then ZSWAP32 l'.hold else l'.hold) = s.check) := by
          refine ⟨hbad, ?_⟩
          simp only [chkS, hcf, Bool.false_eq_true, ↓reduceIte, ite_self] at hne
          by_cases hf0 : s.flags = 0
          · rw [if_pos hf0]
            rw [if_neg (by simpa using hf0)] at hne
            exact hne
          · rw [if_neg hf0]
            rw [if_pos hf0] at hne
            exact hne
        unfold inflate_CHECK
        rw [hc]
        simp [runX_bind, runX_lift, ldI_eq, hs, hw', hrun, e, hr, runX_modify, runX_get, wrZ_eq, wrI_eq, hz,
          hout, hout', hleft', runX_pure, hcf3, hcf4, hcf', hbad2, setMode, runX_INITBITS, chkH, chkZ, chkS, hcf, hbm, chkCond]
        simp [tcBadHeap]
      · intro hn
        have hn2 : ¬ (¬ s.wrap &&& 4 = 0 ∧ ¬ (if s.flags = 0 then ZSWAP32 l'.hold else l'.hold) = s.check) := by
          rintro ⟨ha, hb⟩
          apply hn
          refine ⟨ha, ?_⟩
          simp only [chkS, hcf, Bool.false_eq_true, ↓reduceIte]
          by_cases hf0 : s.flags = 0
          · rw [if_pos hf0] at hb
            rw [if_neg (by simpa using hf0)]
            exact hb
          · rw [if_neg hf0] at hb
            rw [if_pos hf0]
            exact hb
        unfold inflate_CHECK
        rw [hc]
        simp [runX_bind, runX_lift, ldI_eq, hs, hw', hrun, e, hr, runX_modify, runX_get, wrZ_eq, wrI_eq, hz, hcf2,
          hout, hout', hleft', runX_pure, hcf3, hcf', hn2, setMode, runX_INITBITS, chkH, chkZ, chkS, hcf]


/-- Once CHECK accounts for its output, the new segment starts at put.
The public buffer intervals and unread input do not change. -/
theorem DispatchBuffers.rebase_output {h : Heap} {r : ZStreamRef} {l : IL} {bs : List UInt8}
    (buffers : DispatchBuffers h r l bs) : DispatchBuffers h r { l with out_ := l.left } bs := by
  refine ⟨buffers.input, ⟨buffers.output.range, buffers.output.nonnull, Nat.le_refl _, ?_⟩,
    buffers.separate, ⟨buffers.bits.have_eq, buffers.bits.next, buffers.bits.hold_lt⟩⟩
  intro ref off ptr
  change l.left.toNat - l.left.toNat ≤ off
  omega

/-- The actual CHECK counter/checksum writes preserve all storage clauses.
Only totals, check and adler change. -/
theorem check_account_packet {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} (good : Good h r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CHECK) (out : UInt32) (v : UInt64) :
    Good (chkH h r zs z s out v) r zs (chkZ z s out v) (chkS s out v) ∧
      DataPendingInvariant (chkS s out v) ∧ DispatchBuffers (chkH h r zs z s out v) r l bs ∧
      ByteViewSizes h (chkH h r zs z s out v) ∧ (chkH h r zs z s out v).static = h.static := by
  have nextGood : Good (chkH h r zs z s out v) r zs (chkZ z s out v) (chkS s out v) :=
    good.setZI rfl good.live.zalloc good.live.zfree rfl good.live.mode
      (good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl good.inv.bits rfl rfl rfl)
  have views : ∀ ref : BRef, Space.get (chkH h r zs z s out v) ref = Space.get h ref := by
    intro ref
    rw [chkH, byte_view_get_setI, byte_view_get_stream_put]
  have readonly : ∀ ref : BRef, Space.ro (chkH h r zs z s out v) ref = Space.ro h ref := by
    intro ref
    rw [chkH, byte_view_ro_setI, byte_view_ro_stream_put]
  refine ⟨nextGood, ?_, ?_, ?_, ?_⟩
  · apply dataPendingInvariant_idle (s := chkS s out v) pending.sane
    change s.mode ≠ LENEXT ∧ s.mode ≠ DIST ∧ s.mode ≠ DISTEXT ∧ s.mode ≠ MATCH
    rw [mode]
    decide
  · simpa only [List.drop_zero] using buffers.consume good nextGood rfl views readonly
      (regs := l) (used := 0) (by rfl) (inputAdvance_zero l.next).symm (by omega)
      (by simpa only [List.drop_zero] using buffers.bits.byte_views views)
  · first
      | exact ByteViewSizes.of_views views readonly (HeaderTableStep.of_eq (fun _ => by header_table_eq))
      | (intro ref; rw [views])
  · simp only [chkH, setI, ZStreamRef.put_static]

/-- Default zlib and raw recovery have no gzip length trailer. The actual
LENGTH fallthrough terminates, retaining the common packet. -/
theorem inflate_LENGTH_default_boundary {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (wrapper : s.wrap = 0 ∨ s.flags = 0) :
    runX (inflate_LENGTH c) l h = .ok ((.error Ex.leave, { l with ret := Z_STREAM_END }),
      setI h zs { s with mode := DONE }) ∧
      Good (setI h zs { s with mode := DONE }) r zs z { s with mode := DONE } ∧
      DataTableInvariant (setI h zs { s with mode := DONE }) { s with mode := DONE } ∧
      DataPendingInvariant { s with mode := DONE } ∧
      DispatchBuffers (setI h zs { s with mode := DONE }) r { l with ret := Z_STREAM_END } bs ∧
      ByteViewSizes h (setI h zs { s with mode := DONE }) := by
  have nextGood : Good (setI h zs { s with mode := DONE }) r zs z { s with mode := DONE } :=
    good.decode_update (by rfl) (by change HEAD ≤ DONE ∧ DONE ≤ SYNC; decide)
  have views : ∀ ref : BRef, Space.get (setI h zs { s with mode := DONE }) ref = Space.get h ref :=
    fun ref => byte_view_get_setI h zs _ ref
  have bits : BitInv (setI h zs { s with mode := DONE }) { l with ret := Z_STREAM_END } bs :=
    ⟨buffers.bits.have_eq, (buffers.bits.byte_views views).next, buffers.bits.hold_lt⟩
  refine ⟨inflate_LENGTH_skip E.st E.hs wrapper, nextGood, ?_, ?_, ?_, ?_⟩
  · exact dataTableInvariant_inactive (by change ¬ DataTableMode DONE; unfold DataTableMode; decide)
  · apply dataPendingInvariant_idle (s := { s with mode := DONE }) pending.sane
    change DONE ≠ LENEXT ∧ DONE ≠ DIST ∧ DONE ≠ DISTEXT ∧ DONE ≠ MATCH
    decide
  · simpa only [List.drop_zero] using buffers.advance_both good nextGood rfl
      (byte_view_sizes_setI h zs _) (fun ref => byte_view_ro_setI h zs _ ref) (regs := { l with ret := Z_STREAM_END }) (used := 0) (made := 0)
      (by simp only [inputAdvance_zero]) (by rfl) (by simp only [inputAdvance_zero]) (by rfl) rfl
      (by simpa only [List.drop_zero] using bits)
  · exact byte_view_sizes_setI h zs _


/-- CHECK clears the bit buffer only after accepting the data checksum. -/
theorem DispatchBuffers.clear_bits {h : Heap} {r : ZStreamRef} {l : IL} {bs : List UInt8}
    (buffers : DispatchBuffers h r l bs) : DispatchBuffers h r { l with hold := 0, bits := 0 } bs := by
  exact ⟨buffers.input, ⟨buffers.output.range, buffers.output.nonnull, buffers.output.count,
    buffers.output.produced⟩, buffers.separate, (INITBITS_inv buffers.bits).1⟩

/-- The entire default CHECK branch uses the actual checksum callee,
accounts its output once, and either leaves or decreases the main rank.
Raw recovery skips both wrapper trailers. -/
theorem inflate_CHECK_default_rank {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (statics : Zlib.Crc32.Proofs.StaticsOK h)
    (mode : s.mode = CHECK) (wrapper : s.wrap = 0 ∨ s.flags = 0) (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state used, used ≤ bs.length ∧
      runX (inflate_CHECK c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.bits.toNat ≤ 39 ∧ after.static = h.static ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) := by
  by_cases raw : s.wrap = 0
  · let state0 := { s with mode := LENGTH }
    let heap0 := setI h zs state0
    have good0 : Good heap0 r zs z state0 :=
      good.decode_update (by rfl) (by change HEAD ≤ LENGTH ∧ LENGTH ≤ SYNC; decide)
    have E0 : Env c heap0 r zs z state0 := ⟨E.strm, E.st, good0.live.hz, good0.live.hs⟩
    have pending0 : DataPendingInvariant state0 := by
      apply dataPendingInvariant_idle (s := state0) pending.sane
      change LENGTH ≠ LENEXT ∧ LENGTH ≠ DIST ∧ LENGTH ≠ DISTEXT ∧ LENGTH ≠ MATCH
      decide
    have packet0 : DispatchBuffers heap0 r l bs := by
      simpa only [List.drop_zero] using buffers.consume good good0 rfl
        (fun ref => byte_view_get_setI h zs state0 ref) (fun ref => byte_view_ro_setI h zs state0 ref)
        (regs := l) (used := 0) (by rfl) (inputAdvance_zero l.next).symm (by omega)
        (by simpa only [List.drop_zero] using buffers.bits.decode_update zs state0)
    obtain ⟨run, current, tables, nextPending, packet, sizes⟩ :=
      inflate_LENGTH_default_boundary E0 good0 pending0 packet0 (Or.inl raw)
    refine ⟨.error Ex.leave, { l with ret := Z_STREAM_END }, _, z, { state0 with mode := DONE }, 0,
      by omega, (inflate_CHECK_nowrap E.st E.hs raw).trans run, current, tables, nextPending,
      by simpa only [List.drop_zero] using packet, (byte_view_sizes_setI h zs state0).trans sizes,
      (inputAdvance_zero l.next).symm, by rfl, rfl, rfl, incoming, by rfl, Or.inl rfl⟩
  · have flags : s.flags = 0 := wrapper.resolve_left raw
    obtain ⟨outcome, current, used, pull, usedBound, bitInv, _, bitCount, shape,
      bitBound, _, _, _, kinds, cursor⟩ := NEEDBITS_run_cursor buffers.bits 32 (by decide)
    change current.bits.toNat ≤ max l.bits.toNat 39 at bitBound
    have count : current.have_.toNat + used = l.have_.toNat := by
      rw [bitInv.have_eq, buffers.bits.have_eq, List.length_drop]
      omega
    have put : current.put = l.put := by rw [shape]
    have left : current.left = l.left := by rw [shape]
    have packet : DispatchBuffers h r current (bs.drop used) :=
      buffers.consume good good rfl (fun _ => rfl) (fun _ => rfl) (by rw [shape]; rfl)
        cursor usedBound bitInv
    obtain ⟨rr, regs, j, read, jBound, inv, _, waitRun, fullRun⟩ :=
      inflate_CHECK_views_run (l.out_ - l.left) rfl E.strm E.st E.hz E.hs raw buffers.bits statics
        (fun _ => leaveOutputView_of_cursor good buffers.output)
    rw [pull] at read
    cases read
    have jEq : j = used := by
      have one := inv.have_eq
      have two := bitInv.have_eq
      rw [List.length_drop] at one two
      omega
    subst j
    rcases kinds with normal | wait
    · obtain ⟨_, v, badRun, acceptedRun⟩ := fullRun normal
      let out := l.out_ - l.left
      let stream0 := chkZ z s out v
      let state0 := chkS s out v
      let heap0 := chkH h r zs z s out v
      obtain ⟨good0, pending0, packet0, sizes0, static0⟩ := check_account_packet good pending packet mode out v
      have E0 : Env c heap0 r zs stream0 state0 := ⟨E.strm, E.st, good0.live.hz, good0.live.hs⟩
      by_cases invalid : (s.wrap &&& 4) ≠ 0 ∧ (if s.flags ≠ 0 then current.hold else ZSWAP32 current.hold) ≠ state0.check
      · obtain ⟨i, _, run⟩ := badRun invalid.1 invalid.2
        obtain ⟨currentGood, tables, nextPending, nextPacket, sizes, static⟩ :=
          head_bad_packet good0 pending0 packet0 packet0.bits (by rfl) i
        have rebased : DispatchBuffers (badHeap heap0 r zs stream0 state0 i) r
            { current with out_ := l.left } (bs.drop used) := by
          simpa only [left] using nextPacket.rebase_output
        refine ⟨.ok (), { current with out_ := l.left }, _, _, { state0 with mode := BAD }, used,
          usedBound, run, currentGood, tables, nextPending, rebased, sizes0.trans sizes, cursor, count,
          put, left, by change current.bits.toNat ≤ 39; omega, static.trans static0, Or.inr ⟨rfl, ?_⟩⟩
        apply dispatchRank_advance (l := l) (used := used) (made := 0) count
        · change current.left.toNat + 0 = l.left.toNat
          rw [left]
          rfl
        · change current.bits.toNat ≤ l.bits.toNat + 8 * used
          omega
        · right
          change dispatchCredit BAD < dispatchCredit s.mode
          rw [mode]
          decide
      · let state1 := { state0 with mode := LENGTH }
        let heap1 := setI heap0 zs state1
        let first := { current with out_ := l.left, hold := 0, bits := 0 }
        have good1 : Good heap1 r zs stream0 state1 :=
          good0.decode_update (by rfl) (by change HEAD ≤ LENGTH ∧ LENGTH ≤ SYNC; decide)
        have E1 : Env c heap1 r zs stream0 state1 := ⟨E.strm, E.st, good1.live.hz, good1.live.hs⟩
        have pending1 : DataPendingInvariant state1 := by
          apply dataPendingInvariant_idle (s := state1) pending0.sane
          change LENGTH ≠ LENEXT ∧ LENGTH ≠ DIST ∧ LENGTH ≠ DISTEXT ∧ LENGTH ≠ MATCH
          decide
        have basePacket : DispatchBuffers heap0 r first (bs.drop used) := by
          simpa only [first, left] using packet0.rebase_output.clear_bits
        have packet1 : DispatchBuffers heap1 r first (bs.drop used) := by
          simpa only [List.drop_zero] using basePacket.consume good0 good1 rfl
            (fun ref => byte_view_get_setI heap0 zs state1 ref) (fun ref => byte_view_ro_setI heap0 zs state1 ref)
            (regs := first) (used := 0) (by rfl) (inputAdvance_zero first.next).symm (by omega)
            (by simpa only [List.drop_zero] using basePacket.bits.decode_update zs state1)
        obtain ⟨run, currentGood, tables, nextPending, nextPacket, sizes⟩ :=
          inflate_LENGTH_default_boundary E1 good1 pending1 packet1 (Or.inr flags)
        have result := (acceptedRun invalid).trans run
        refine ⟨.error Ex.leave, { first with ret := Z_STREAM_END }, _, stream0,
          { state1 with mode := DONE }, used, usedBound, result, currentGood, tables, nextPending,
          nextPacket, (sizes0.trans (byte_view_sizes_setI heap0 zs state1)).trans sizes, cursor, count,
          put, left, by change 0 ≤ 39; decide, ?_, Or.inl rfl⟩
        change heap0.static = h.static
        exact static0
    · obtain ⟨_, _, _, run⟩ := waitRun wait
      exact ⟨.error Ex.leave, current, h, z, s, used, usedBound, run, good,
        dataTableInvariant_inactive (by rw [mode]; unfold DataTableMode; decide), pending,
        packet, ByteViewSizes.refl h, cursor, count, put, left, by omega, rfl, Or.inl rfl⟩

/-- The real switch selects the DICTID branch. -/
theorem inflate_dispatch_DICTID {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL) (mode : s.mode = DICTID) :
    runX (inflate_dispatch c) l h = runX (inflate_DICTID c) l h := by
  unfold inflate_dispatch
  rw [runX_bind, runX_rdS E]
  with_reducible simp [mode, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC,
    DICTID, DICT, TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS,
    LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH]

/-- The real switch selects the DICT branch. -/
theorem inflate_dispatch_DICT {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL) (mode : s.mode = DICT) :
    runX (inflate_dispatch c) l h = runX (inflate_DICT c) l h := by
  unfold inflate_dispatch
  rw [runX_bind, runX_rdS E]
  with_reducible simp [mode, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC,
    DICTID, DICT, TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS,
    LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH]

/-- The real switch selects the CHECK branch. -/
theorem inflate_dispatch_CHECK {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL) (mode : s.mode = CHECK) :
    runX (inflate_dispatch c) l h = runX (inflate_CHECK c) l h := by
  unfold inflate_dispatch
  rw [runX_bind, runX_rdS E]
  with_reducible simp [mode, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC,
    DICTID, DICT, TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS,
    LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH]

/-- The real switch selects the LENGTH branch. -/
theorem inflate_dispatch_LENGTH {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL) (mode : s.mode = LENGTH) :
    runX (inflate_dispatch c) l h = runX (inflate_LENGTH c) l h := by
  unfold inflate_dispatch
  rw [runX_bind, runX_rdS E]
  with_reducible simp [mode, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC,
    DICTID, DICT, TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS,
    LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH]

end Zlib.Inflate.Proofs
