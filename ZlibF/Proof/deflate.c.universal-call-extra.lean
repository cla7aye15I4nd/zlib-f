import ZlibF.Proof.«deflate.c.universal-call-flush»

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
      produced = min buf.size z.avail_out.toNat ∧
      after.gzheaders i = some g ∧ after.static = H.static ∧
      (∃ ea', Space.get after rs = some ea' ∧ ea'.size = ea.size) ∧
      d'.status = d.status ∧ d'.gzhead = d.gzhead ∧ d'.bi_valid = d.bi_valid ∧
      d'.pending_buf = d.pending_buf ∧ d'.pending_buf_size = d.pending_buf_size ∧
      d'.gzindex.toNat = d.gzindex.toNat + (buf.size - d.pending.toNat) ∧
      (st'.ret = true → d'.pending ≠ 0 ∧ d'.last_flush = -1) ∧
      (st'.ret = false → d'.pending = 0 ∧ d'.pending_out = d'.pending_buf ∧ d'.last_flush = d.last_flush ∧
        st'.beg = 0 ∧ st'.left.toNat + (buf.size - d.pending.toNat) = st.left.toNat) ∧
      z'.next_out ≠ .null := by
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
  have frame03 : HeaderFrame H H3 pb := (frame1.trans frame2).trans frame3
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
  by_cases zero : d4.pending = 0
  · refine ⟨{ st with beg := 0, left := st.left - copy }, H4, z4, d4, produced, ?_, good4, buffers4, accountT,
      ⟨buf4, trees4', size4.trans size1⟩, producedEq, gz4 i g gz3, ?_, ⟨ea4, view4, sizeE4⟩,
      common4.1, common4.2.1, bits4, common4.2.2.1, common4.2.2.2, gzidx, fun e => absurd (notRet.symm.trans e) (by decide), ?_, out4⟩
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
      ⟨buf4, ?_, size4.trans size1⟩, producedEq, ?_, ?_, ?_,
      common4.1, common4.2.1, bits4, common4.2.2.1, common4.2.2.2, gzidx,
      fun _ => ⟨zero, rfl⟩, fun e => Bool.noConfusion e, out4⟩
    · rw [core]; simp [rdD_eq, good4.live.hs, zero, wrD_eq]
    · exact trees_at_buffer good5 trees4'.base.pbuf trees4'.base.bytes
    · rw [frame5.gzheaders]; exact gz4 i g gz3
    · rw [frame5.static, static4]; exact frame03.static
    · exact ⟨ea4, by rw [frame5.views rs other]; exact view4, sizeE4⟩

end Zlib.Deflate.Universal.Call
