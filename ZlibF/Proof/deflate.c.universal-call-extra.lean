import ZlibF.Proof.«deflate.c.universal-call-flush»
import ZlibF.Proof.«deflate.c.universal-strategies»

/-!
# deflate.c: the gzip extra-field stage of one `deflate` call

Batch C (`call_frame`, `deflate_header_trailer`). The extra field is copied into `pending_buf`;
while the rest does not fit, `pending_buf` is filled, the header CRC updated and the buffer
flushed, and the stage returns `Z_OK` if the flush could not empty it.
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff)
set_option autoImplicit false

theorem advance_ne_null {p : BPtr} (ne : p ≠ .null) (n : Nat) : advance p n ≠ .null := by
  cases p with
  | null => exact absurd rfl ne
  | ref r i => simp [advance]

/-- **One iteration of the extra-field loop.** -/
theorem extra_body {H : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood H r ds z d) (trees : TreesInvAt H ds d pb buf)
    (buffers : StreamBuffers H r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) (globals : LibraryGlobals H)
    {i : Nat} {g : GzHeader} (record : d.gzhead = some (.tab i)) (getg : H.gzheaders i = some g)
    {rs : BRef} {eo : Nat} {ea : Array UInt8} (extra : g.extra = .ref rs eo)
    (srcGet : Space.get H rs = some ea) (other : rs ≠ .blk pb)
    (st : ExtraS) (notRet : st.ret = false) (span : eo + d.gzindex.toNat + st.left.toNat ≤ ea.size)
    (begBelow : st.beg.toNat ≤ d.pending.toNat) (below : d.pending.toNat < buf.size)
    (more : buf.size < d.pending.toNat + st.left.toNat)
    (small : d.gzindex.toNat + st.left.toNat < 2 ^ 16) :
    ∃ (st' : ExtraS) (after : Heap) (z' : ZStream) (d' : DeflateState) (produced : Nat),
      extraBody (some r) (some (.tab ds)) st H = .ok (st', after) ∧
      DGood after r ds z' d' ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      (∃ buf', TreesInvAt after ds d' pb buf' ∧ buf'.size = buf.size) ∧
      produced = min buf.size z.avail_out.toNat ∧ d'.pending.toNat + produced = buf.size ∧
      after.gzheaders i = some g ∧ after.static = H.static ∧
      (∃ ea', Space.get after rs = some ea' ∧ ea'.size = ea.size) ∧
      d'.status = d.status ∧ d'.gzhead = d.gzhead ∧ d'.bi_valid = d.bi_valid ∧
      d'.pending_buf = d.pending_buf ∧ d'.pending_buf_size = d.pending_buf_size ∧
      d'.gzindex.toNat = d.gzindex.toNat + (buf.size - d.pending.toNat) ∧
      (st'.ret = true → d'.pending ≠ 0 ∧ d'.last_flush = -1) ∧
      (st'.ret = false → d'.pending = 0 ∧ d'.pending_out = d'.pending_buf ∧ d'.last_flush = d.last_flush ∧
        st'.beg = 0 ∧ st'.left.toNat + (buf.size - d.pending.toNat) = st.left.toNat) ∧
      z'.next_out ≠ .null ∧ CallerKeep H after z ds pb ∧ HeaderShape d d' := by
  have psize := trees.base.psize
  have pbuf := trees.base.pbuf
  have pbsLe : d.pending.toNat ≤ d.pending_buf_size.toNat := by omega
  have copyEq : (d.pending_buf_size - d.pending).toNat = buf.size - d.pending.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr pbsLe)]; omega
  have ldg : ldGzHeader d.gzhead H = .ok (g, H) := by
    rw [record]; simp only [ldGzHeader, GzHeaderRef.get, getg]
  have pp : padd d.pending_buf d.pending.toNat H = .ok (.ref (.blk pb) d.pending.toNat, H) := by
    rw [pbuf]
    have := padd_ok' (r := BRef.blk pb) (off := 0) (n := d.pending.toNat) (h := H) trees.base.bytes (by omega)
    simpa using this
  have pe : padd g.extra d.gzindex.toNat H = .ok (.ref rs (eo + d.gzindex.toNat), H) := by
    rw [extra]; exact padd_ok' srcGet (by omega)
  obtain ⟨run1, good1, trees1, buffers1, frame1, size1⟩ :=
    pending_copy (os := eo + d.gzindex.toNat) good trees buffers cursor srcGet other (d.pending_buf_size - d.pending).toNat
      (by rw [copyEq]; omega) (by rw [copyEq]; omega) d.pending_buf_size (by rw [copyEq]; omega)
  let d1 : DeflateState := { d with pending := d.pending_buf_size }
  let H1 := setD (Zlib.Trees.Proofs.Out.setB H pb
    (copyRange buf ea d.pending.toNat (eo + d.gzindex.toNat) (d.pending_buf_size - d.pending).toNat)) ds d1
  have globals1 : LibraryGlobals H1 := by unfold LibraryGlobals at globals ⊢; rw [frame1.static, globals]
  have getg1 : H1.gzheaders i = some g := by rw [frame1.gzheaders, getg]
  obtain ⟨H2, z2, good2, trees2, buffers2, account2, frame2, run2⟩ :=
    hcrc_update good1 trees1 buffers1 globals1 (i := i) record getg1 st.beg
      (by change st.beg.toNat ≤ d.pending_buf_size.toNat; omega)
  let copy := d.pending_buf_size - d.pending
  obtain ⟨good3, trees3, buffers3, frame3⟩ := gzindex_engine good2 trees2 buffers2 (d1.gzindex + copy)
  let d3 : DeflateState := { d1 with gzindex := d1.gzindex + copy }
  let H3 := setD H2 ds d3
  have out2 : z2.next_out ≠ .null := by rw [account2.2.2.2.2.2.1]; exact advance_ne_null out _
  obtain ⟨produced, H4, z4, d4, run4, good4, trees4, buffers4, account4, copied, left, fields4, empty4,
    _adler4, gz4, static4, sizes4⟩ := header_flush good3 trees3 buffers3 low cursor out2
  have avail2 : z2.avail_out = z.avail_out := by
    have a := account2.2.2.2.1
    exact UInt32.toNat_inj.mp (by omega)
  have frame03 : HeaderFrame H H3 r ds pb := (frame1.trans frame2).trans frame3
  have view3 : Space.get H3 rs = some ea := by rw [frame03.views rs other, srcGet]
  obtain ⟨ea4, view4, sizeE4⟩ := sizes4.get rs ea view3
  have gz3 : H3.gzheaders i = some g := by rw [frame03.gzheaders, getg]
  have accountT : StreamAccounting z z4 0 produced := by
    simpa only [Nat.zero_add] using stream_accounting_trans account2 account4
  have out4 : z4.next_out ≠ .null := by rw [account4.2.2.2.2.2.1]; exact advance_ne_null out2 _
  have producedEq : produced = min buf.size z.avail_out.toNat := by
    rw [copied, avail2]
    change min (d.pending_buf_size).toNat _ = _
    rw [psize]
  have drained : d4.pending.toNat + produced = buf.size := by
    rw [left]; change (d.pending_buf_size).toNat = _; exact psize
  have gzidx : d4.gzindex.toNat = d.gzindex.toNat + (buf.size - d.pending.toNat) := by
    rw [fields4]
    change (d.gzindex + copy).toNat = _
    rw [UInt64.toNat_add, copyEq]
    have : d.gzindex.toNat + (buf.size - d.pending.toNat) < 2 ^ 64 := by
      have := UInt64.toNat_lt d.gzindex; omega
    omega
  have core : extraBody (some r) (some (.tab ds)) st H =
      (do
        if (← rd (some (.tab ds)) (·.pending)) != 0 then
          wr (some (.tab ds)) (fun d => { d with last_flush := -1 })
          return { st with ret := true }
        pure { st with beg := 0, left := st.left - copy }) H4 := by
    unfold extraBody
    simp only [bind_app, ldDeflateState_tab good.live.hs, ldg, pp, pe]
    rw [run1]
    simp only [wrD_eq, show (Zlib.Trees.Proofs.Out.setB H pb (copyRange buf ea d.pending.toNat
      (eo + d.gzindex.toNat) (d.pending_buf_size - d.pending).toNat)).dstates ds = some d from good.live.hs]
    rw [run2]
    simp only [wrD_eq, good2.live.hs]
    rw [run4]
  obtain ⟨buf4, trees4', size4⟩ := trees4
  have bits4 : d4.bi_valid = d.bi_valid := by rw [fields4]
  have common4 : d4.status = d.status ∧ d4.gzhead = d.gzhead ∧ d4.pending_buf = d.pending_buf ∧
      d4.pending_buf_size = d.pending_buf_size := by
    rw [fields4]; exact ⟨rfl, rfl, rfl, rfl⟩
  have keep4 : CallerKeep H H4 z ds pb :=
    (CallerKeep.of_frame frame03).trans (CallerKeep.of_flush good3 trees3 buffers3 low cursor out2 run4
      good4.live.hz account4) account2
  by_cases zero : d4.pending = 0
  · refine ⟨{ st with beg := 0, left := st.left - copy }, H4, z4, d4, produced, ?_, good4, buffers4, accountT,
      ⟨buf4, trees4', size4.trans size1⟩, producedEq, drained, gz4 i g gz3, ?_, ⟨ea4, view4, sizeE4⟩,
      common4.1, common4.2.1, bits4, common4.2.2.1, common4.2.2.2, gzidx, fun e => absurd (notRet.symm.trans e) (by decide), ?_, out4,
      keep4, ⟨_, _, _, _, _, _, _, _, fields4⟩⟩
    · rw [core]; simp [rdD_eq, good4.live.hs, zero]
    · rw [static4]; exact (frame03.static)
    · intro _
      refine ⟨zero, empty4 zero, by rw [fields4], rfl, ?_⟩
      change (st.left - copy).toNat + _ = _
      have lt : copy ≤ st.left := by
        apply UInt64.le_iff_toNat_le.mpr; change (d.pending_buf_size - d.pending).toNat ≤ _; rw [copyEq]; omega
      rw [UInt64.toNat_sub_of_le _ _ lt]
      change st.left.toNat - (d.pending_buf_size - d.pending).toNat + _ = _
      rw [copyEq]; omega
  · obtain ⟨good5, buffers5, frame5⟩ := last_flush_frame (pb := pb) good4 trees4' buffers4 (-1)
    refine ⟨{ st with ret := true }, _, z4, _, produced, ?_, good5, buffers5, accountT,
      ⟨buf4, ?_, size4.trans size1⟩, producedEq, drained, ?_, ?_, ?_,
      common4.1, common4.2.1, bits4, common4.2.2.1, common4.2.2.2, gzidx,
      fun _ => ⟨zero, rfl⟩, fun e => Bool.noConfusion e, out4,
      keep4.trans (CallerKeep.of_frame frame5) accountT,
      HeaderShape.trans ⟨_, _, _, _, _, _, _, _, fields4⟩ ⟨_, _, _, _, _, _, _, _, rfl⟩⟩
    · rw [core]; simp [rdD_eq, good4.live.hs, zero, wrD_eq]
    · exact trees_at_buffer good5 trees4'.base.pbuf trees4'.base.bytes
    · rw [frame5.gzheaders]; exact gz4 i g gz3
    · rw [frame5.static, static4]; exact frame03.static
    · exact ⟨ea4, by rw [frame5.views rs other]; exact view4, sizeE4⟩

/-- What holds at the head of the extra-field loop, relative to its entry (`z`, `d`, `left0`). -/
def ExtraHead (H0 : Heap) (r : ZStreamRef) (ds pb : Nat) (z : ZStream) (d : DeflateState)
    (buf : Array UInt8) (i : Nat) (g : GzHeader) (rs : BRef) (ea : Array UInt8) (left0 : Nat)
    (st : ExtraS) (H : Heap) : Prop :=
  ∃ (z' : ZStream) (d' : DeflateState) (produced : Nat) (buf' : Array UInt8) (ea' : Array UInt8),
    DGood H r ds z' d' ∧ TreesInvAt H ds d' pb buf' ∧ buf'.size = buf.size ∧ StreamBuffers H r ∧
    StreamAccounting z z' 0 produced ∧ H.gzheaders i = some g ∧ H.static = H0.static ∧
    Space.get H rs = some ea' ∧ ea'.size = ea.size ∧
    d'.status = d.status ∧ d'.gzhead = d.gzhead ∧ d'.bi_valid = d.bi_valid ∧
    d'.pending_buf = d.pending_buf ∧ d'.pending_buf_size = d.pending_buf_size ∧ z'.next_out ≠ .null ∧
    CallerKeep H0 H z ds pb ∧ HeaderShape d d' ∧
    (st.ret = true → d'.pending ≠ 0 ∧ d'.last_flush = -1 ∧ (1 ≤ produced ∨ z.avail_out.toNat = 0)) ∧
    (st.ret = false → d'.gzindex.toNat + st.left.toNat = d.gzindex.toNat + left0 ∧
      d'.pending_out = d'.pending_buf ∧ st.beg.toNat ≤ d'.pending.toNat ∧
      d'.pending.toNat < buf.size ∧ d'.last_flush = d.last_flush ∧
      (produced = 0 → d' = d ∧ z' = z ∧ H = H0))

theorem extra_cond_run {H : Heap} {ds : Nat} {d : DeflateState} (state : H.dstates ds = some d)
    (st : ExtraS) :
    extraCond (some (.tab ds)) st H =
      .ok ((!st.ret && d.pending + st.left > d.pending_buf_size, st), H) := by
  unfold extraCond
  simp only [bind_app, ldDeflateState_tab state, pure_app]

/-- **The extra-field loop.** From a loop head it ends, either after an early return (with bytes
left pending and the output full or a byte delivered) or with the rest of the field fitting in
`pending_buf`. -/
theorem extra_loop {H0 H : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} {i : Nat} {g : GzHeader} {rs : BRef} {eo : Nat} {ea : Array UInt8}
    (extra : g.extra = .ref rs eo) (other : rs ≠ .blk pb) (sizeLo : 1 ≤ buf.size)
    (left0 : Nat) (span : eo + d.gzindex.toNat + left0 ≤ ea.size)
    (small : d.gzindex.toNat + left0 < 2 ^ 16) (globals : LibraryGlobals H0)
    (record : d.gzhead = some (.tab i)) (low : d.bi_valid.toInt < 8) (psize : d.pending_buf_size.toNat = buf.size)
    (st : ExtraS) (head : ExtraHead H0 r ds pb z d buf i g rs ea left0 st H) :
    ∃ st' H', cwhile (extraCond (some (.tab ds))) (extraBody (some r) (some (.tab ds))) st H = .ok (st', H') ∧
      ExtraHead H0 r ds pb z d buf i g rs ea left0 st' H' ∧
      (st'.ret = false → ∃ d', H'.dstates ds = some d' ∧ d'.pending.toNat + st'.left.toNat ≤ buf.size) := by
  refine cwhile_measure (ExtraHead H0 r ds pb z d buf i g rs ea left0)
    (fun st' H' => ExtraHead H0 r ds pb z d buf i g rs ea left0 st' H' ∧
      (st'.ret = false → ∃ d', H'.dstates ds = some d' ∧ d'.pending.toNat + st'.left.toNat ≤ buf.size))
    (fun st H => if st.ret then 0 else st.left.toNat + 1) ?_ head (by
      unfold fuel; split
      · omega
      · rename_i notRet
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rest⟩ := head
        have := (rest (by simpa using notRet)).1
        omega)
  intro st H inv
  have inv0 := inv
  obtain ⟨z1, d1, p1, buf1, ea1, good1, trees1, bufSize1, buffers1, account1, gz1, static1, view1, eaSize1,
    status1, gzhead1, bits1, pbuf1, pbs1, out1, keep1, shape1, retFacts1, headFacts1⟩ := inv
  have bufHi : buf1.size ≤ 131072 := by have := trees1.base.size; have := trees1.base.lit_hi; omega
  have bufLo : 512 ≤ buf1.size := by have := trees1.base.size; have := trees1.base.lit_lo; omega
  have sizes1 : d1.pending_buf_size.toNat = buf1.size := trees1.base.psize
  refine ⟨_, st, H, extra_cond_run good1.live.hs st, ?_, ?_⟩
  · intro c
    have cond : st.ret = false ∧ d1.pending + st.left > d1.pending_buf_size := by
      simpa using c
    obtain ⟨notRet, gt⟩ := cond
    obtain ⟨idx1, cursor1, beg1, below1, last1, zero1⟩ := headFacts1 notRet
    have noWrap : d1.pending.toNat + st.left.toNat < 2 ^ 64 := by omega
    have more1 : buf1.size < d1.pending.toNat + st.left.toNat := by
      have := UInt64.lt_iff_toNat_lt.mp gt
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt noWrap] at this
      omega
    have globals1 : LibraryGlobals H := by unfold LibraryGlobals at globals ⊢; rw [static1, globals]
    obtain ⟨st2, H2, z2, d2, p2, run2, good2, buffers2, account2, trees2, produced2, drained2, gz2, static2,
      view2, status2, gzhead2, bits2, pbuf2, pbs2, idx2, ret2, cont2, out2, keepB, shapeB⟩ :=
      extra_body good1 trees1 buffers1 cursor1 (by rw [bits1]; exact low) out1 globals1
        (by rw [gzhead1]; exact record) gz1 extra view1 other st notRet
        (by omega) beg1 (by omega) more1 (by omega)
    obtain ⟨buf2, trees2', size2⟩ := trees2
    obtain ⟨ea2, view2', eaSize2⟩ := view2
    have avail1 : z1.avail_out.toNat + p1 = z.avail_out.toNat := account1.2.2.2.1
    refine ⟨st2, H2, run2, ?_, ?_⟩
    · refine ⟨z2, d2, p1 + p2, buf2, ea2, good2, trees2', size2.trans bufSize1, buffers2,
        stream_accounting_trans account1 account2, gz2, static2.trans static1, view2', eaSize2.trans eaSize1,
        status2.trans status1, gzhead2.trans gzhead1, bits2.trans bits1, pbuf2.trans pbuf1, pbs2.trans pbs1,
        out2, keep1.trans keepB account1, shape1.trans shapeB, ?_, ?_⟩
      · intro retTrue
        obtain ⟨pend2, lf2⟩ := ret2 retTrue
        refine ⟨pend2, lf2, ?_⟩
        by_cases zeroAvail : z.avail_out.toNat = 0
        · exact Or.inr zeroAvail
        · left
          rw [produced2]
          omega
      · intro retFalse
        obtain ⟨pend2, cur2, lf2, beg2, left2⟩ := cont2 retFalse
        refine ⟨by omega, cur2, by rw [beg2]; simp, by rw [pend2]; simp; omega, lf2.trans last1, ?_⟩
        intro none
        exfalso
        have : p2 = 0 := by omega
        rw [pend2] at drained2
        simp at drained2
        omega
    · show (if st2.ret then 0 else st2.left.toNat + 1) < (if st.ret then 0 else st.left.toNat + 1)
      rw [notRet]
      cases e : st2.ret
      · obtain ⟨_, _, _, _, left2⟩ := cont2 e
        simp only [Bool.false_eq_true, ite_false]
        omega
      · simp
  · intro c
    refine ⟨inv0, fun notRet => ⟨d1, good1.live.hs, ?_⟩⟩
    have no : ¬ (d1.pending + st.left > d1.pending_buf_size) := by
      intro gt; simp [notRet, gt] at c
    obtain ⟨idx1, _, _, below1, _, _⟩ := headFacts1 notRet
    have noWrap : d1.pending.toNat + st.left.toNat < 2 ^ 64 := by omega
    have := mt UInt64.lt_iff_toNat_lt.mpr no
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt noWrap] at this
    omega

theorem extra_len_mask (x : UInt32) : (x &&& 0xffff).toUInt64.toNat = x.toNat % 2 ^ 16 := by
  rw [UInt32.toNat_toUInt64, UInt32.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat 16

/-- **The gzip extra-field stage.** Either it returns `Z_OK` with bytes left pending (a byte was
delivered or there is no output room), or it continues in `NAME_STATE`; without a delivered byte
nothing left `pending_buf`. -/
theorem extra_stage {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) (globals : LibraryGlobals h) (status : d.status = EXTRA_STATE)
    {i : Nat} {g : GzHeader} (record : d.gzhead = some (.tab i)) (getg : h.gzheaders i = some g)
    (extraMem : g.extra ≠ .null → ∃ rs eo ea, g.extra = .ref rs eo ∧ Space.get h rs = some ea ∧
      eo + g.extra_len.toNat % 2 ^ 16 ≤ ea.size ∧ rs ≠ .blk pb)
    (progress : g.extra ≠ .null → d.gzindex.toNat ≤ g.extra_len.toNat % 2 ^ 16)
    (below : d.pending.toNat < buf.size) (k : M Int32) :
    ∃ (produced : Nat) (after : Heap) (z' : ZStream) (d' : DeflateState),
      DGood after r ds z' d' ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      (∃ buf', TreesInvAt after ds d' pb buf' ∧ buf'.size = buf.size) ∧
      after.gzheaders i = some g ∧ after.static = h.static ∧ z'.next_out ≠ .null ∧
      CallerKeep h after z ds pb ∧ HeaderShape d d' ∧
      d'.gzhead = d.gzhead ∧ d'.bi_valid = d.bi_valid ∧
      ((extraStage (some r) (some (.tab ds)) k h = .ok (Z_OK, after) ∧
          (1 ≤ produced ∨ z.avail_out.toNat = 0)) ∨
       (extraStage (some r) (some (.tab ds)) k h = k after ∧ d'.status = NAME_STATE ∧
          d'.pending_out = d'.pending_buf ∧ d'.pending.toNat ≤ buf.size ∧
          (produced = 0 → d.pending.toNat ≤ d'.pending.toNat) ∧
          (d'.gzindex = 0 ∨ (g.extra = .null ∧ d'.gzindex = d.gzindex)))) := by
  have psize := trees.base.psize
  have sizeLo : 1 ≤ buf.size := by have := trees.base.size; have := trees.base.lit_lo; omega
  have ldg : ldGzHeader d.gzhead h = .ok (g, h) := by
    rw [record]; simp only [ldGzHeader, GzHeaderRef.get, getg]
  have extraState : (d.status == EXTRA_STATE) = true := by rw [status]; rfl
  by_cases ex : g.extra = .null
  · obtain ⟨good1, trees1, buffers1⟩ := status_engine good trees buffers NAME_STATE (by simp [GoodStatus])
    refine ⟨0, _, z, _, good1, buffers1, stream_accounting_zero z, ⟨buf, trees1, rfl⟩, getg, rfl, out,
      CallerKeep.of_frame (HeaderFrame.state (r := r) pb good.live.hs _ rfl), ⟨_, _, _, _, _, _, _, _, rfl⟩, rfl, rfl,
      Or.inr ⟨?_, rfl, cursor, (by change d.pending.toNat ≤ buf.size; omega), fun _ => Nat.le_refl _,
        Or.inr ⟨ex, rfl⟩⟩⟩
    rw [extra_stage_split]
    unfold extraStage'
    simp only [bind_app, rdD_eq, good.live.hs, extraState, ite_true, ldDeflateState_tab good.live.hs, ldg,
      ex, bne_self_eq_false, Bool.false_eq_true, ite_false, wrD_eq]
  · obtain ⟨rs, eo, ea, extra, srcGet, span, other⟩ := extraMem ex
    have idx0 := progress ex
    let L := g.extra_len.toNat % 2 ^ 16
    have Lsmall : L < 2 ^ 16 := Nat.mod_lt _ (by decide)
    let st0 : ExtraS := { beg := d.pending, left := (g.extra_len &&& 0xffff).toUInt64 - d.gzindex, ret := false }
    have left0 : st0.left.toNat = L - d.gzindex.toNat := by
      change ((g.extra_len &&& 0xffff).toUInt64 - d.gzindex).toNat = _
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [extra_len_mask]; exact idx0)),
        extra_len_mask]
    have head0 : ExtraHead h r ds pb z d buf i g rs ea (L - d.gzindex.toNat) st0 h :=
      ⟨z, d, 0, buf, ea, good, trees, rfl, buffers, stream_accounting_zero z, getg, rfl, srcGet, rfl,
        rfl, rfl, rfl, rfl, rfl, out, CallerKeep.refl h z ds pb, HeaderShape.refl d, (fun e => Bool.noConfusion e),
        fun _ => ⟨(by rw [left0]), cursor, Nat.le_refl _, below, rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩⟩
    obtain ⟨st1, H1, runL, head1, exit1⟩ :=
      extra_loop extra other sizeLo (L - d.gzindex.toNat) (by omega) (by omega) globals record low psize st0 head0
    have stageEq : extraStage (some r) (some (.tab ds)) k h =
        extraCopy (some r) (some (.tab ds)) d g (do
          wr (some (.tab ds)) (fun d => { d with status := NAME_STATE })
          k) h := by
      rw [extra_stage_split]
      unfold extraStage'
      simp only [bind_app, rdD_eq, good.live.hs, extraState, ite_true, ldDeflateState_tab good.live.hs, ldg,
        show (g.extra != .null) = true from bne_iff_ne.mpr ex]
    obtain ⟨z1, d1, p1, buf1, ea1, good1, trees1, bufSize1, buffers1, account1, gz1, static1, view1, eaSize1,
      status1, gzhead1, bits1, pbuf1, pbs1, out1, keep1, shape1, retFacts1, headFacts1⟩ := head1
    cases ret1 : st1.ret
    · obtain ⟨idx1, cursor1, beg1, below1, last1, zero1⟩ := headFacts1 ret1
      obtain ⟨d1', state1', fits1⟩ := exit1 ret1
      have same1 : d1 = d1' := Option.some.inj (good1.live.hs.symm.trans state1')
      subst same1
      have pbuf1' := trees1.base.pbuf
      have small1 : st1.left.toNat < 2 ^ 16 := by omega
      have ldg1 : ldGzHeader d1.gzhead H1 = .ok (g, H1) := by
        rw [gzhead1, record]; simp only [ldGzHeader, GzHeaderRef.get, gz1]
      have pp1 : padd d1.pending_buf d1.pending.toNat H1 = .ok (.ref (.blk pb) d1.pending.toNat, H1) := by
        rw [pbuf1']
        have := padd_ok' (r := BRef.blk pb) (off := 0) (n := d1.pending.toNat) (h := H1) trees1.base.bytes
          (by omega)
        simpa using this
      have pe1 : padd g.extra d1.gzindex.toNat H1 = .ok (.ref rs (eo + d1.gzindex.toNat), H1) := by
        rw [extra]; exact padd_ok' view1 (by omega)
      have noWrap : d1.pending.toNat + st1.left.toNat < 2 ^ 64 := by
        have := trees1.base.size; have := trees1.base.lit_hi; omega
      obtain ⟨run2, good2, trees2, buffers2, frame2, size2⟩ :=
        pending_copy (os := eo + d1.gzindex.toNat) good1 trees1 buffers1 cursor1 view1 other st1.left.toNat
          (by omega) (by omega) (d1.pending + st1.left)
          (by rw [UInt64.toNat_add, Nat.mod_eq_of_lt noWrap])
      let d2 : DeflateState := { d1 with pending := d1.pending + st1.left }
      have count2 : d2.pending.toNat = d1.pending.toNat + st1.left.toNat := by
        change (d1.pending + st1.left).toNat = _; rw [UInt64.toNat_add, Nat.mod_eq_of_lt noWrap]
      have globals2 : LibraryGlobals (setD (Zlib.Trees.Proofs.Out.setB H1 pb
          (copyRange buf1 ea1 d1.pending.toNat (eo + d1.gzindex.toNat) st1.left.toNat)) ds d2) := by
        unfold LibraryGlobals at globals ⊢; rw [frame2.static, static1, globals]
      obtain ⟨H3, z3, good3, trees3, buffers3, account3, frame3, run3⟩ :=
        hcrc_update good2 trees2 buffers2 globals2 (i := i) (by change d1.gzhead = _; rw [gzhead1, record])
          (by rw [frame2.gzheaders, gz1]) st1.beg (by rw [count2]; omega)
      obtain ⟨good4, trees4, buffers4, frame4⟩ := gzindex_engine good3 trees3 buffers3 0
      obtain ⟨good5, trees5, buffers5⟩ := status_engine good4 trees4 buffers4 NAME_STATE (by simp [GoodStatus])
      have accountT : StreamAccounting z z3 0 p1 := by
        simpa only [Nat.zero_add, Nat.add_zero] using stream_accounting_trans account1 account3
      have frameT := ((frame2.trans frame3).trans frame4).trans
        (HeaderFrame.state (r := r) pb good4.live.hs { d2 with gzindex := 0, status := NAME_STATE } rfl)
      refine ⟨p1, _, z3, _, good5, buffers5, accountT, ⟨_, trees5, size2.trans bufSize1⟩, ?_, ?_, ?_,
        keep1.trans ((CallerKeep.of_frame (((frame2.trans frame3).trans frame4).trans
          (HeaderFrame.state (r := r) pb good4.live.hs _ rfl)))) account1,
        shape1.trans ⟨_, _, _, _, _, _, _, _, rfl⟩, ?_, ?_,
        Or.inr ⟨?_, rfl, cursor1, ?_, ?_, Or.inl rfl⟩⟩
      · rw [frameT.gzheaders, gz1]
      · rw [frameT.static, static1]
      · rw [account3.2.2.2.2.2.1]; exact advance_ne_null out1 _
      · exact gzhead1
      · exact bits1
      · rw [stageEq]
        unfold extraCopy
        simp only [bind_app]
        rw [runL]
        simp only [ret1, Bool.false_eq_true, ite_false, bind_app, ldDeflateState_tab good1.live.hs, ldg1, pp1, pe1]
        rw [run2]
        simp only [wrD_eq, show (Zlib.Trees.Proofs.Out.setB H1 pb (copyRange buf1 ea1 d1.pending.toNat
          (eo + d1.gzindex.toNat) st1.left.toNat)).dstates ds = some d1 from good1.live.hs]
        rw [run3]
        simp only [wrD_eq, good3.live.hs]
        simp [setD_dstates_same]
      · change d2.pending.toNat ≤ buf.size; rw [count2]; omega
      · intro none
        obtain ⟨e1, _, _⟩ := zero1 none
        change d.pending.toNat ≤ d2.pending.toNat
        rw [count2, e1]; omega
    · obtain ⟨pend1, lf1, del1⟩ := retFacts1 ret1
      refine ⟨p1, H1, z1, d1, good1, buffers1, account1, ⟨buf1, trees1, bufSize1⟩, gz1, static1, out1, keep1,
        shape1, gzhead1, bits1, Or.inl ⟨?_, del1⟩⟩
      rw [stageEq]
      unfold extraCopy
      simp only [bind_app]
      rw [runL]
      simp [ret1, pure_app]

end Zlib.Deflate.Universal.Call
