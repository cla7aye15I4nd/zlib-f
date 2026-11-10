import ZlibF.Proof.«inflate.c.leave-checksum-general»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual optional checksum update changes only the public Adler field.
Both translated checksum callees are discharged on the real output view. -/
theorem leaveChecksum_stream_fields {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z current : ZStream} {s : InflateState} (E : Env c h r zs current s)
    (good : Good h r zs current s) (output : LeaveOutputView h l)
    (statics : Zlib.Crc32.Proofs.StaticsOK h) (cursor : z.next_out = l.put) (count : z.avail_out = l.left) :
    ∃ after stream state, leaveChecksum c l z h = .ok ((), after) ∧
      Good after r zs stream state ∧ LeaveMetadataFrame s state ∧
      stream = { current with adler := stream.adler } := by
  by_cases update : ((s.wrap &&& 4) != 0 && l.out_ - z.avail_out != 0) = true
  · obtain ⟨ref, off, array, put, get, startBound, endBound⟩ := output
    have ptr : l.put.add (-((l.out_ - l.left).toNat : Int)) h =
        .ok (.ref ref (off - (l.out_ - l.left).toNat), h) := by
      rw [put]
      exact Ptr.sub_nat_ok get startBound endBound
    have checksum := UPDATE_CHECK_all_views statics E.hs get (by omega :
      off - (l.out_ - l.left).toNat + (l.out_ - l.left).toNat ≤ array.size) s.check
    let value := inflateChecksumValue s.flags s.check ((array.toList.drop (off - (l.out_ - l.left).toNat)).take
      (l.out_ - l.left).toNat)
    let stream := { current with adler := value }
    let state := { s with check := value }
    let after := setI (r.put h stream) zs state
    have nextGood : Good after r zs stream state := good.setZI rfl good.live.zalloc good.live.zfree
      rfl good.live.mode (good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl good.inv.bits rfl rfl rfl)
    refine ⟨after, stream, state, ?_, nextGood, by rfl, rfl⟩
    · unfold leaveChecksum
      rw [E.st, E.strm]
      simp only [bind_app, ldI_eq, E.hs, update, ↓reduceIte]
      rw [cursor, count, ptr]
      simp only []
      rw [checksum]
      simp only [bind_app, E.st, wrI_eq, E.hs, wrZ_eq, ZStreamRef.get_setI, E.hz]
      rw [ZStreamRef.put_setI]
  · have skip : ((s.wrap &&& 4) != 0 && l.out_ - z.avail_out != 0) = false := by
      cases eq : ((s.wrap &&& 4) != 0 && l.out_ - z.avail_out != 0) <;> simp_all
    refine ⟨h, current, s, ?_, good, by rfl, rfl⟩
    · unfold leaveChecksum
      rw [E.st]
      simp only [bind_app, ldI_eq, E.hs, skip, Bool.false_eq_true, ↓reduceIte, pure_app]

/-- Exact stream fields and return choice after the complete real counter,
checksum and data-type suffix. Counters may wrap as unsigned C counters do. -/
theorem leaveFinalize_stream_fields {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z current : ZStream} {s : InflateState} (E : Env c h r zs current s)
    (good : Good h r zs current s) (output : LeaveOutputView h l)
    (statics : Zlib.Crc32.Proofs.StaticsOK h) (cursor : z.next_out = l.put) (count : z.avail_out = l.left) :
    ∃ rc after stream state, leaveFinalize c l z h = .ok (rc, after) ∧
      Good after r zs stream state ∧ LeaveMetadataFrame s state ∧
      stream = { leaveCountStream current z l with adler := stream.adler, data_type := stream.data_type } ∧
      rc = (if ((l.in_ - z.avail_in == 0 && l.out_ - z.avail_out == 0 || c.flush == Z_FINISH) &&
        l.ret == Z_OK) then Z_BUF_ERROR else l.ret) ∧
      state.mode = s.mode := by
  let stream1 := leaveCountStream current z l
  let state1 := leaveCountState s z l
  let heap1 := setI (r.put h stream1) zs state1
  have good1 : Good heap1 r zs stream1 state1 := good.setZI rfl good.live.zalloc good.live.zfree
    rfl good.live.mode (good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl good.inv.bits rfl rfl rfl)
  have env1 : Env c heap1 r zs stream1 state1 := ⟨E.strm, E.st, good1.live.hz, good1.live.hs⟩
  have views1 : ∀ ref : BRef, (Space.get heap1 ref : Option (Array UInt8)) = Space.get h ref := by
    intro ref
    rw [byte_view_get_setI, byte_view_get_stream_put]
  have output1 : LeaveOutputView heap1 l := by
    obtain ⟨ref, off, array, put, get, startBound, endBound⟩ := output
    exact ⟨ref, off, array, put, by rw [views1]; exact get, startBound, endBound⟩
  have statics1 : Zlib.Crc32.Proofs.StaticsOK heap1 := by
    simpa only [Zlib.Crc32.Proofs.StaticsOK, heap1, setI, ZStreamRef.put_static] using statics
  obtain ⟨heap2, stream2, state2, checksum, good2, frame2, fields2⟩ :=
    leaveChecksum_stream_fields env1 good1 output1 statics1 cursor count
  have bits2 : state2.bits.toNat ≤ 39 := by rw [frame2]; exact good.inv.bits
  have env2 : Env c heap2 r zs stream2 state2 := ⟨E.strm, E.st, good2.live.hz, good2.live.hs⟩
  obtain ⟨dt, _, finish⟩ := leaveReturn_run (l := l) (z := z) env2 bits2
  let stream3 := { stream2 with data_type := dt }
  have same : setI (r.put heap2 stream3) zs state2 = r.put heap2 stream3 := by
    exact tcSetI_same (by simpa using good2.live.hs)
  have good3 : Good (r.put heap2 stream3) r zs stream3 state2 := by
    have result := good2.setZI (z' := stream3) (st' := state2) rfl good2.live.zalloc good2.live.zfree
      rfl good2.live.mode good2.inv
    rwa [same] at result
  refine ⟨_, r.put heap2 stream3, stream3, state2, ?_, good3,
    LeaveMetadataFrame.trans (by rfl) frame2, ?_, rfl, ?_⟩
  · rw [leaveFinalize_split, bind_app, leaveCounters_run E]
    simp only []
    rw [bind_app, checksum]
    exact finish
  · change { stream2 with data_type := dt } = _
    rw [fields2]
  · rw [frame2]
    rfl


end Zlib.Inflate.Proofs
