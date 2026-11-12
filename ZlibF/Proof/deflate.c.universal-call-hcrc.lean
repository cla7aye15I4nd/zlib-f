import ZlibF.Proof.«deflate.c.universal-call-string»

/-!
# deflate.c: the gzip header CRC stage of one `deflate` call

Batch C (`deflate_header_trailer`). With `hcrc` set, the two CRC bytes are added (after a flush if
they do not fit); then `BUSY_STATE` and the flush that must empty `pending_buf`.
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff)
set_option autoImplicit false

/-- The end of a header: `BUSY_STATE`, the flush, and the early return if bytes stay pending. -/
theorem busy_flush {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) (k : M Int32) :
    ∃ (after : Heap) (z1 : ZStream) (d1 : DeflateState) (produced : Nat),
      DGood after r ds z1 d1 ∧ (∃ buf1, TreesInvAt after ds d1 pb buf1 ∧ buf1.size = buf.size) ∧
      StreamBuffers after r ∧ StreamAccounting z z1 0 produced ∧
      (∀ i g, h.gzheaders i = some g → after.gzheaders i = some g) ∧ after.static = h.static ∧
      d1.gzhead = d.gzhead ∧ d1.bi_valid = d.bi_valid ∧ d1.pending_buf = d.pending_buf ∧
      d1.pending_buf_size = d.pending_buf_size ∧ HeaderShape d d1 ∧ StageFrame h after r ds pb d z z1 produced ∧
      z1.next_out ≠ .null ∧
      produced = min d.pending.toNat z.avail_out.toNat ∧
      d1.pending.toNat + produced = d.pending.toNat ∧
      ((busyTail (some r) (some (.tab ds)) k h = .ok (Z_OK, after) ∧ d1.pending ≠ 0 ∧ d1.last_flush = -1) ∨
       (busyTail (some r) (some (.tab ds)) k h = k after ∧ d1.status = BUSY_STATE ∧ d1.pending = 0 ∧
         d1.pending_out = d1.pending_buf ∧ d1.last_flush = d.last_flush)) := by
  obtain ⟨good1, trees1, buffers1⟩ := status_engine good trees buffers BUSY_STATE (by simp [GoodStatus])
  obtain ⟨produced, H2, z2, d2, run2, good2, ⟨buf2, trees2, size2⟩, buffers2, account2, copied, left, fields2,
    empty2, _adler2, gz2, static2, _sizes2⟩ := header_flush good1 trees1 buffers1 low cursor out
  have keys : d2.gzhead = d.gzhead ∧ d2.bi_valid = d.bi_valid ∧ d2.pending_buf = d.pending_buf ∧
      d2.pending_buf_size = d.pending_buf_size ∧ d2.status = BUSY_STATE ∧ d2.last_flush = d.last_flush := by
    rw [fields2]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have out2 : z2.next_out ≠ .null := by rw [account2.2.2.2.2.2.1]; exact advance_ne_null out _
  have shape2 : HeaderShape d d2 := HeaderShape.trans ⟨_, _, _, _, _, _, _, _, rfl⟩ ⟨_, _, _, _, _, _, _, _, fields2⟩
  have stage2 : StageFrame h H2 r ds pb d z z2 produced := by
    have s := StageFrame.trans (StageFrame.state good buffers trees.base.pbuf { d with status := BUSY_STATE })
      (StageFrame.of_flush good1 trees1 buffers1 low cursor out run2 good2.live.hz account2) (fun _ => Iff.rfl)
      good buffers
    rwa [Nat.zero_add] at s
  by_cases zero : d2.pending = 0
  · refine ⟨H2, z2, d2, produced, good2, ⟨buf2, trees2, size2⟩, buffers2, account2, gz2, static2, keys.1,
      keys.2.1, keys.2.2.1, keys.2.2.2.1, shape2, stage2, out2, copied, left, Or.inr ⟨?_, keys.2.2.2.2.1, zero, empty2 zero,
      keys.2.2.2.2.2⟩⟩
    unfold busyTail
    simp only [bind_app, wrD_eq, good.live.hs]
    rw [run2]
    simp [rdD_eq, good2.live.hs, zero]
  · obtain ⟨good5, buffers5, frame5⟩ := last_flush_frame (pb := pb) good2 trees2 buffers2 (-1)
    refine ⟨_, z2, _, produced, good5, ⟨buf2, trees_at_buffer good5 trees2.base.pbuf trees2.base.bytes, size2⟩,
      buffers5, account2, (fun i g get => by rw [frame5.gzheaders]; exact gz2 i g get),
      (by rw [frame5.static, static2]; rfl),
      keys.1, keys.2.1, keys.2.2.1, keys.2.2.2.1, shape2.trans ⟨_, _, _, _, _, _, _, _, rfl⟩,
      by
        have s := StageFrame.trans stage2 (StageFrame.state good2 buffers2 trees2.base.pbuf { d2 with last_flush := -1 })
          (HeaderShape.owned shape2) good buffers
        rwa [Nat.add_zero] at s,
      out2, copied, left, Or.inl ⟨?_, zero, rfl⟩⟩
    unfold busyTail
    simp only [bind_app, wrD_eq, good.live.hs]
    rw [run2]
    simp [rdD_eq, good2.live.hs, zero, wrD_eq]

/-- The two header CRC bytes, after a flush if they do not fit. -/
def hcrcBytes (strm : ZStreamPtr) (s : DeflateStatePtr) (d : DeflateState) (k : M Int32) : M Int32 := do
  if d.pending + 2 > d.pending_buf_size then
    flush_pending strm
    if (← rd s (·.pending)) != 0 then
      wr s (fun d => { d with last_flush := -1 })
      return Z_OK
  let a ← zrd strm (·.adler)
  put_byte s (a &&& 0xff).toUInt8
  put_byte s ((a >>> 8) &&& 0xff).toUInt8
  let r ← Zlib.Crc32.crc32 0 (Ptr.null : BPtr) 0
  zwr strm (fun z => { z with adler := r })
  k

/-- The header CRC stage with its parts named. -/
def hcrcStage' (strm : ZStreamPtr) (s : DeflateStatePtr) (k : M Int32) : M Int32 := do
  if (← rd s (·.status)) == HCRC_STATE then
    let d ← ldDeflateState s
    let gh ← ldGzHeader d.gzhead
    if gh.hcrc != 0 then hcrcBytes strm s d (busyTail strm s k)
    else busyTail strm s k
  else k

theorem hcrc_stage_split (strm : ZStreamPtr) (s : DeflateStatePtr) (k : M Int32) :
    hcrcStage strm s k = hcrcStage' strm s k := by
  delta hcrcStage hcrcStage' hcrcBytes busyTail
  exact rfl

/-- The two CRC bytes and the checksum reset. -/
def hcrcPut (strm : ZStreamPtr) (s : DeflateStatePtr) (k : M Int32) : M Int32 := do
  let a ← zrd strm (·.adler)
  put_byte s (a &&& 0xff).toUInt8
  put_byte s ((a >>> 8) &&& 0xff).toUInt8
  let r ← Zlib.Crc32.crc32 0 (Ptr.null : BPtr) 0
  zwr strm (fun z => { z with adler := r })
  k

def hcrcBytes' (strm : ZStreamPtr) (s : DeflateStatePtr) (d : DeflateState) (k : M Int32) : M Int32 := do
  if d.pending + 2 > d.pending_buf_size then
    flush_pending strm
    if (← rd s (·.pending)) != 0 then
      wr s (fun d => { d with last_flush := -1 })
      return Z_OK
    hcrcPut strm s k
  else hcrcPut strm s k

theorem hcrc_bytes_split (strm : ZStreamPtr) (s : DeflateStatePtr) (d : DeflateState) (k : M Int32) :
    hcrcBytes strm s d k = hcrcBytes' strm s d k := by
  delta hcrcBytes hcrcBytes' hcrcPut
  exact rfl

/-- **The two CRC bytes**, with room. -/
theorem hcrc_put {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf)
    (room : d.pending.toNat + 2 ≤ buf.size) (k : M Int32) :
    ∃ (after : Heap) (z1 : ZStream) (d1 : DeflateState) (buf1 : Array UInt8),
      hcrcPut (some r) (some (.tab ds)) k h = k after ∧ DGood after r ds z1 d1 ∧
      TreesInvAt after ds d1 pb buf1 ∧ buf1.size = buf.size ∧ StreamBuffers after r ∧
      StreamAccounting z z1 0 0 ∧ HeaderFrame h after r ds pb ∧
      d1 = { d with pending := d1.pending } ∧ d1.pending.toNat = d.pending.toNat + 2 := by
  obtain ⟨runs0, facts0⟩ := header_byte_eq good trees buffers cursor (by omega)
  let c0 : UInt8 := (z.adler &&& 0xff).toUInt8
  let c1 : UInt8 := ((z.adler >>> 8) &&& 0xff).toUInt8
  obtain ⟨good1, trees1, buffers1, count1, size1⟩ := facts0 c0
  obtain ⟨runs1, facts1⟩ := header_byte_eq good1 trees1 buffers1 cursor (by rw [count1, size1]; omega)
  obtain ⟨good2, trees2, buffers2, count2, size2⟩ := facts1 c1
  obtain ⟨good3, trees3, buffers3, account3⟩ := adler_engine good2 trees2 buffers2 0
  refine ⟨_, _, _, _, ?_, good3, trees3, by rw [size2, size1], buffers3, account3,
    (((HeaderFrame.byte pb good.live.hs trees.base.bytes c0).trans (HeaderFrame.byte pb good1.live.hs trees1.base.bytes c1)).trans
      (HeaderFrame.stream pb good2.live.hz _ rfl rfl)), rfl, ?_⟩
  · unfold hcrcPut
    simp only [bind_app, zrd_eq, good.live.hz]
    rw [runs0 c0]
    simp only []
    rw [runs1 c1]
    simp only [crc32_null, pure_app, zwr_eq, good2.live.hz]
  · rw [count2]; change (d.pending + 1).toNat + 1 = _; rw [count1]

/-- **The gzip header CRC stage**: returns `Z_OK` with bytes pending, or continues in
`BUSY_STATE` with nothing pending. -/
theorem hcrc_stage {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) (status : d.status = HCRC_STATE)
    {i : Nat} {g : GzHeader} (record : d.gzhead = some (.tab i)) (getg : h.gzheaders i = some g)
    (pendLe : d.pending.toNat ≤ buf.size) (k : M Int32) :
    ∃ (after : Heap) (z1 : ZStream) (d1 : DeflateState) (produced : Nat),
      StageBase h r ds pb z d buf i g after z1 d1 produced ∧
      ((hcrcStage (some r) (some (.tab ds)) k h = .ok (Z_OK, after) ∧ (1 ≤ produced ∨ z.avail_out.toNat = 0) ∧
          d1.last_flush = -1 ∧ d1.pending ≠ 0) ∨
       (hcrcStage (some r) (some (.tab ds)) k h = k after ∧ d1.status = BUSY_STATE ∧ d1.pending = 0 ∧
         d1.pending_out = d1.pending_buf ∧ (produced = 0 → d.pending.toNat = 0) ∧ d1.last_flush = d.last_flush)) := by
  have ldg : ldGzHeader d.gzhead h = .ok (g, h) := by
    rw [record]; simp only [ldGzHeader, GzHeaderRef.get, getg]
  have st : (d.status == HCRC_STATE) = true := by rw [status]; rfl
  have psize := trees.base.psize
  have bufLo : 512 ≤ buf.size := by have := trees.base.size; have := trees.base.lit_lo; omega
  have bufHi : buf.size ≤ 131072 := by have := trees.base.size; have := trees.base.lit_hi; omega
  have stageEq : ∀ K : M Int32, hcrcStage (some r) (some (.tab ds)) K h =
      (if g.hcrc != 0 then hcrcBytes' (some r) (some (.tab ds)) d (busyTail (some r) (some (.tab ds)) K)
       else busyTail (some r) (some (.tab ds)) K) h := by
    intro K
    rw [hcrc_stage_split]
    unfold hcrcStage'
    simp only [bind_app, rdD_eq, good.live.hs, st, ite_true, ldDeflateState_tab good.live.hs, ldg, hcrc_bytes_split]
  -- the busy flush from any state reached in the stage
  have finish : ∀ {H : Heap} {z2 : ZStream} {d2 : DeflateState} {buf2 : Array UInt8} {p2 : Nat},
      DGood H r ds z2 d2 → TreesInvAt H ds d2 pb buf2 → buf2.size = buf.size → StreamBuffers H r →
      StreamAccounting z z2 0 p2 → H.gzheaders i = some g → H.static = h.static →
      d2.gzhead = d.gzhead → d2.bi_valid = d.bi_valid → d2.pending_buf = d.pending_buf →
      d2.pending_buf_size = d.pending_buf_size → d2.pending_out = d2.pending_buf → z2.next_out ≠ .null →
      HeaderShape d d2 → StageFrame h H r ds pb d z z2 p2 → d2.last_flush = d.last_flush →
      (p2 = 0 → d2.pending.toNat = 0 → d.pending.toNat = 0) →
      ∃ (after : Heap) (z1 : ZStream) (d1 : DeflateState) (produced : Nat),
        StageBase h r ds pb z d buf i g after z1 d1 produced ∧
        ((busyTail (some r) (some (.tab ds)) k H = .ok (Z_OK, after) ∧ (1 ≤ produced ∨ z.avail_out.toNat = 0) ∧
           d1.last_flush = -1 ∧ d1.pending ≠ 0) ∨
         (busyTail (some r) (some (.tab ds)) k H = k after ∧ d1.status = BUSY_STATE ∧ d1.pending = 0 ∧
           d1.pending_out = d1.pending_buf ∧ (produced = 0 → d.pending.toNat = 0) ∧ d1.last_flush = d.last_flush)) := by
    intro H z2 d2 buf2 p2 good2 trees2 size2 buffers2 account2 gz2 static2 gzhead2 bits2 pbuf2 pbs2 cursor2
      out2 shape2 stage2 lfd2 zeroP
    obtain ⟨H3, z3, d3, p3, good3, trees3, buffers3, account3, gz3, static3, gzhead3, bits3, pbuf3, pbs3, shape3,
      stage3, out3, produced3, left3, outcome⟩ := busy_flush good2 trees2 buffers2 cursor2 (by rw [bits2]; exact low) out2 k
    obtain ⟨buf3, trees3', size3⟩ := trees3
    have base : StageBase h r ds pb z d buf i g H3 z3 d3 (p2 + p3) :=
      ⟨good3, ⟨buf3, trees3', size3.trans size2⟩, buffers3, stream_accounting_trans account2 account3,
        gz3 i g gz2, static3.trans static2, gzhead3.trans gzhead2, bits3.trans bits2, pbuf3.trans pbuf2,
        pbs3.trans pbs2, out3, shape2.trans shape3, StageFrame.trans stage2 stage3 (HeaderShape.owned shape2) good buffers⟩
    have a2 := account2.2.2.2.1
    rcases outcome with ⟨run3, pend3, lf3⟩ | ⟨run3, status3, zero3, cursor3, lfc⟩
    · refine ⟨H3, z3, d3, p2 + p3, base, Or.inl ⟨run3, ?_, lf3, pend3⟩⟩
      have pn : d3.pending.toNat ≠ 0 := fun e => pend3 (UInt64.toNat_inj.mp (by rw [e]; rfl))
      by_cases a0 : z.avail_out.toNat = 0
      · exact Or.inr a0
      · left
        rw [produced3] at left3 ⊢
        omega
    · refine ⟨H3, z3, d3, p2 + p3, base, Or.inr ⟨run3, status3, zero3, cursor3, fun none => ?_, lfc.trans lfd2⟩⟩
      have z0 : d3.pending.toNat = 0 := by rw [zero3]; rfl
      exact zeroP (by omega) (by omega)
  by_cases crc : g.hcrc = 0
  · obtain ⟨after, z1, d1, produced, base, outcome⟩ := finish good trees rfl buffers (stream_accounting_zero z) getg rfl
      rfl rfl rfl rfl cursor out (HeaderShape.refl d) (StageFrame.refl good buffers trees.base.pbuf) rfl (fun _ e => e)
    refine ⟨after, z1, d1, produced, base, ?_⟩
    rw [stageEq]; simp only [crc, bne_self_eq_false, Bool.false_eq_true, ite_false]; exact outcome
  · have crcT : (g.hcrc != 0) = true := bne_iff_ne.mpr crc
    by_cases big : d.pending + 2 > d.pending_buf_size
    · have bigN : buf.size < d.pending.toNat + 2 := by
        have := UInt64.lt_iff_toNat_lt.mp big
        rw [UInt64.toNat_add, show (2 : UInt64).toNat = 2 from rfl, Nat.mod_eq_of_lt (by omega)] at this
        omega
      obtain ⟨p1, H1, z1, d1, run1, good1, ⟨buf1, trees1, size1⟩, buffers1, account1, copied1, left1, fields1,
        empty1, _adler1, gz1, static1, _sizes1⟩ := header_flush good trees buffers low cursor out
      have keys1 : d1.gzhead = d.gzhead ∧ d1.bi_valid = d.bi_valid ∧ d1.pending_buf = d.pending_buf ∧
          d1.pending_buf_size = d.pending_buf_size := by
        rw [fields1]; exact ⟨rfl, rfl, rfl, rfl⟩
      have out1 : z1.next_out ≠ .null := by rw [account1.2.2.2.2.2.1]; exact advance_ne_null out _
      by_cases zero : d1.pending = 0
      · obtain ⟨H2, z2, d2, buf2, run2, good2, trees2, size2, buffers2, account2, frame2, fields2, count2⟩ :=
          hcrc_put good1 trees1 buffers1 (empty1 zero) (by rw [zero, size1]; simp; omega)
            (busyTail (some r) (some (.tab ds)) k)
        have keys2 : d2.gzhead = d.gzhead ∧ d2.bi_valid = d.bi_valid ∧ d2.pending_buf = d.pending_buf ∧
            d2.pending_buf_size = d.pending_buf_size ∧ d2.pending_out = d2.pending_buf := by
          rw [fields2]; exact ⟨keys1.1, keys1.2.1, keys1.2.2.1, keys1.2.2.2, empty1 zero⟩
        obtain ⟨after, z3, d3, produced, base, outcome⟩ := finish good2 trees2 (size2.trans size1) buffers2
          (by simpa only [Nat.add_zero] using stream_accounting_trans account1 account2)
          (by rw [frame2.gzheaders]; exact gz1 i g getg) (by rw [frame2.static, static1])
          keys2.1 keys2.2.1 keys2.2.2.1 keys2.2.2.2.1 keys2.2.2.2.2
          (by rw [account2.2.2.2.2.2.1]; exact advance_ne_null out1 _)
          (HeaderShape.trans ⟨_, _, _, _, _, _, _, _, fields1⟩ ⟨_, _, _, _, _, _, _, _, fields2⟩)
          (by
            have s := StageFrame.trans (StageFrame.of_flush good trees buffers low cursor out run1 good1.live.hz account1)
              (StageFrame.of_header frame2 good1 buffers1 trees1.base.pbuf account2 good2.live.hz)
              (HeaderShape.owned (⟨_, _, _, _, _, _, _, _, fields1⟩ : HeaderShape d d1)) good buffers
            rwa [Nat.add_zero] at s)
          (by have a := congrArg DeflateState.last_flush fields2; have b := congrArg DeflateState.last_flush fields1; simp only at a b; rw [a, b])
          (fun none _ => by
            have z0 : d1.pending.toNat = 0 := by rw [zero]; rfl
            rw [copied1] at none left1; omega)
        refine ⟨after, z3, d3, produced, base, ?_⟩
        rw [stageEq]
        simp only [crcT, ite_true]
        unfold hcrcBytes'
        simp only [big, decide_true, ite_true, bind_app]
        rw [run1]
        simp only [rdD_eq, good1.live.hs, zero, bne_self_eq_false, Bool.false_eq_true, ite_false]
        rw [run2]; exact outcome
      · obtain ⟨good5, buffers5, frame5⟩ := last_flush_frame (pb := pb) good1 trees1 buffers1 (-1)
        refine ⟨_, z1, _, p1, ⟨good5, ⟨buf1, trees_at_buffer good5 trees1.base.pbuf trees1.base.bytes, size1⟩,
          buffers5, account1, (by rw [frame5.gzheaders]; exact gz1 i g getg), (by rw [frame5.static, static1]),
          keys1.1, keys1.2.1, keys1.2.2.1, keys1.2.2.2, out1,
          HeaderShape.trans ⟨_, _, _, _, _, _, _, _, fields1⟩ ⟨_, _, _, _, _, _, _, _, rfl⟩,
          by
            have s := StageFrame.trans (StageFrame.of_flush good trees buffers low cursor out run1 good1.live.hz account1)
              (StageFrame.state good1 buffers1 trees1.base.pbuf { d1 with last_flush := -1 })
              (HeaderShape.owned (⟨_, _, _, _, _, _, _, _, fields1⟩ : HeaderShape d d1)) good buffers
            rwa [Nat.add_zero] at s⟩, Or.inl ⟨?_, ?_, rfl, zero⟩⟩
        · rw [stageEq]
          simp only [crcT, ite_true]
          unfold hcrcBytes'
          simp only [big, decide_true, ite_true, bind_app]
          rw [run1]
          simp [rdD_eq, good1.live.hs, zero, wrD_eq]
        · by_cases a0 : z.avail_out.toNat = 0
          · exact Or.inr a0
          · left; rw [copied1]; omega
    · have roomN : d.pending.toNat + 2 ≤ buf.size := by
        have := mt UInt64.lt_iff_toNat_lt.mpr big
        rw [UInt64.toNat_add, show (2 : UInt64).toNat = 2 from rfl, Nat.mod_eq_of_lt (by omega)] at this
        omega
      obtain ⟨H2, z2, d2, buf2, run2, good2, trees2, size2, buffers2, account2, frame2, fields2, count2⟩ :=
        hcrc_put good trees buffers cursor roomN (busyTail (some r) (some (.tab ds)) k)
      have keys2 : d2.gzhead = d.gzhead ∧ d2.bi_valid = d.bi_valid ∧ d2.pending_buf = d.pending_buf ∧
          d2.pending_buf_size = d.pending_buf_size ∧ d2.pending_out = d2.pending_buf := by
        rw [fields2]; exact ⟨rfl, rfl, rfl, rfl, cursor⟩
      obtain ⟨after, z3, d3, produced, base, outcome⟩ := finish good2 trees2 size2 buffers2 account2
        (by rw [frame2.gzheaders]; exact getg) frame2.static
        keys2.1 keys2.2.1 keys2.2.2.1 keys2.2.2.2.1 keys2.2.2.2.2
        (by rw [account2.2.2.2.2.2.1]; exact advance_ne_null out _)
        ⟨_, _, _, _, _, _, _, _, fields2⟩
        (StageFrame.of_header frame2 good buffers trees.base.pbuf account2 good2.live.hz)
        (by have a := congrArg DeflateState.last_flush fields2; simp only at a; rw [a])
        (fun _ e => by omega)
      refine ⟨after, z3, d3, produced, base, ?_⟩
      rw [stageEq]
      simp only [crcT, ite_true]
      unfold hcrcBytes'
      simp only [big, decide_false, ite_false]
      rw [run2]; exact outcome


end Zlib.Deflate.Universal.Call
