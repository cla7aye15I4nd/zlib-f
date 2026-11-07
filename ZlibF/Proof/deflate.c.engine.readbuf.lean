import ZlibF.Zlib.«deflate_base.c»
import ZlibF.Proof.«deflate.c.engine.macros»
import ZlibF.Proof.«deflate.c.engine.loops»
import ZlibF.Proof.«adler32.c»
import ZlibF.Proof.«crc32.c»

/-!
# deflate.c, engine: `read_buf`

`read_buf(strm, buf, size)` copies `L = min(avail_in, size)` bytes from `next_in` to `buf`, advances `next_in`,
`total_in`, lowers `avail_in`, and updates `adler` with the Adler-32 (`wrap = 1`) or CRC-32 (`wrap = 2`) of the bytes
copied. Nothing else changes. The checksum theorems of `adler32.c` and `crc32.c` are used as proved.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate

/-- `len = strm->avail_in; if (len > size) len = size;` -/
def rbLen (avail size : UInt32) : UInt32 := if avail > size then size else avail

theorem seg_eq_take_drop (a : Array UInt8) (p n : Nat) (h : p + n ≤ a.size) :
    Zlib.Adler32.Proofs.seg a p n = (a.toList.drop p).take n := by
  apply List.ext_getElem
  · simp [Zlib.Adler32.Proofs.seg]; omega
  · intro i h1 h2
    simp [Zlib.Adler32.Proofs.seg] at h1 ⊢
    simp [getElem!_def, Array.getElem?_eq_getElem (show p + i < a.size by omega)]

theorem seg_copyRange (ba ia : Array UInt8) (bo io L : Nat) (hfit : bo + L ≤ ba.size) :
    Zlib.Adler32.Proofs.seg (copyRange ba ia bo io L) bo L = Zlib.Adler32.Proofs.seg ia io L := by
  unfold Zlib.Adler32.Proofs.seg
  apply List.map_congr_left
  intro i hi
  have hi' : i < L := List.mem_range.mp hi
  have := getElem?_copyRange ba ia bo io L (bo + i) hfit
  simp only [getElem!_def, this, show bo ≤ bo + i ∧ bo + i < bo + L by omega, and_self, ite_true,
    Nat.add_sub_cancel_left]

/-- `strm->avail_in -= len` -/
def rbDec (L : UInt32) : ZStream → ZStream := fun z => { z with avail_in := z.avail_in - L }
/-- `strm->adler = a` -/
def rbSetAd (a : UInt64) : ZStream → ZStream := fun z => { z with adler := a }
/-- `strm->next_in += len; strm->total_in += len` (the new `next_in` is `ni`) -/
def rbAdvF (ni : BPtr) (L : UInt32) : ZStream → ZStream := fun z => { z with next_in := ni, total_in := z.total_in + L.toUInt64 }

/-- `read_buf` with the length already computed (`len` is `min(avail_in, size)`). -/
def rbCore (strm : ZStreamPtr) (buf : BPtr) (len : UInt32) : M UInt32 := do
  if len == 0 then return 0
  zwr strm (rbDec len)
  memcpyB buf (← zrd strm (·.next_in)) len.toNat
  let sp ← castDeflateState (← zrd strm (·.state))
  let wrap ← rd sp (·.wrap)
  if wrap == 1 then
    let a ← zrd strm (·.adler)
    let r ← Zlib.Adler32.adler32 a buf len
    zwr strm (rbSetAd r)
  else if wrap == 2 then
    let a ← zrd strm (·.adler)
    let r ← Zlib.Crc32.crc32 a buf len
    zwr strm (rbSetAd r)
  let ni ← padd (← zrd strm (·.next_in)) len.toNat
  zwr strm (rbAdvF ni len)
  return len

theorem read_buf_eq {h : Heap} {zr : Nat} {z : ZStream} (buf : BPtr) (size : UInt32) (hz : h.streams zr = some z) :
    read_buf (some (.tab zr)) buf size h = rbCore (some (.tab zr)) buf (rbLen z.avail_in size) h := by
  have e1 : ldZStream (some (.tab zr)) h = .ok (z, h) := ldZStream_tab hz
  unfold read_buf rbCore rbLen
  simp only [zrd, bind_app, e1, pure_app]
  by_cases hg : z.avail_in > size
  · simp only [ite_eq_left hg]; rfl
  · simp only [ite_eq_right hg]; rfl

/-- No byte to copy (`min(avail_in, size) = 0`): `read_buf` returns 0 and changes nothing. -/
theorem read_buf_zero {h : Heap} {zr : Nat} {z : ZStream} (buf : BPtr) (size : UInt32)
    (hz : h.streams zr = some z) (h0 : rbLen z.avail_in size = 0) :
    read_buf (some (.tab zr)) buf size h = .ok (0, h) := by
  rw [read_buf_eq buf size hz, h0]
  simp [rbCore]

/-- The stream record after `read_buf` copied `L` bytes from `next_in` (block `ib`, offset `io`) and the checksum became `a`. -/
def rbStream (z : ZStream) (L : UInt32) (ib io : Nat) (a : UInt64) : ZStream :=
  { z with avail_in := z.avail_in - L, next_in := .ref (.blk ib) (io + L.toNat), total_in := z.total_in + L.toUInt64,
           adler := a }

/-- The last step of `read_buf`: `next_in += L`, `total_in += L`. -/
def rbAdv (z : ZStream) (L : UInt32) (ib io : Nat) : ZStream :=
  { z with next_in := .ref (.blk ib) (io + L.toNat), total_in := z.total_in + L.toUInt64 }

theorem u32_toUInt64_eq (len : UInt32) : len.toUInt64 = len.toNat.toUInt64 := by
  apply UInt64.toNat_inj.mp; simp

/-- **read_buf, the copy.** When `L = min(avail_in, size)` is not zero, the source `next_in[0 .. L)` and the
destination `buf[0 .. L)` lie in their blocks and do not overlap, and the destination block is writable, the call does
not fault, returns `L`, copies the bytes, lowers `avail_in` by `L`, advances `next_in` and `total_in` by `L`, and
changes `adler` to the checksum of the bytes copied: the Adler-32 for `wrap = 1`, the CRC-32 for `wrap = 2`, no change
otherwise. (For `wrap = 1` and `L = 1`, the value is the Adler-32 only if the old high sum is canonical, which
every stored value is; without it the value is still computed without fault.) -/
theorem read_buf_ok {h : Heap} {zr dsid ib bb io bo : Nat} {z : ZStream} {d : DeflateState} {ia ba : Array UInt8}
    (buf : BPtr) (size : UInt32)
    (hz : h.streams zr = some z) (hs : z.state = some (.deflate dsid)) (hd : h.dstates dsid = some d)
    (hL : rbLen z.avail_in size ≠ 0)
    (hin : z.next_in = .ref (.blk ib) io) (hib : h.bytes ib = some ia)
    (hbuf : buf = .ref (.blk bb) bo) (hbb : h.bytes bb = some ba) (hro : h.ro bb = false)
    (hfin : io + (rbLen z.avail_in size).toNat ≤ ia.size) (hfbuf : bo + (rbLen z.avail_in size).toNat ≤ ba.size)
    (hdis : bb ≠ ib ∨ io + (rbLen z.avail_in size).toNat ≤ bo ∨ bo + (rbLen z.avail_in size).toNat ≤ io)
    (hstat : d.wrap = 2 → Zlib.Crc32.Proofs.StaticsOK h) :
    ∃ adler' : UInt64, read_buf (some (.tab zr)) buf size h = .ok (rbLen z.avail_in size, { h with
        bytes := upd h.bytes bb (some (copyRange ba ia bo io (rbLen z.avail_in size).toNat)),
        streams := upd h.streams zr (some (rbStream z (rbLen z.avail_in size) ib io adler')) }) ∧
      (d.wrap = 1 → ((rbLen z.avail_in size).toNat ≠ 1 ∨ (z.adler >>> 16 &&& 65535).toNat < 65521) →
        adler'.toNat = Zlib.Adler32.Spec.adler32 z.adler.toNat (Zlib.Adler32.Proofs.seg ia io (rbLen z.avail_in size).toNat)) ∧
      (d.wrap = 2 → adler' = (ZlibF.Spec.crc32Update z.adler.toUInt32
        ((ia.toList.drop io).take (rbLen z.avail_in size).toNat)).toUInt64) ∧
      (d.wrap ≠ 1 → d.wrap ≠ 2 → adler' = z.adler) := by
  obtain ⟨L, hLd⟩ : ∃ L, L = rbLen z.avail_in size := ⟨_, rfl⟩
  rw [← hLd] at hL hfin hfbuf hdis ⊢
  have hL0 : L.toNat ≠ 0 := fun h0 => hL (UInt32.toNat_inj.mp (by simpa using h0))
  have hLle : L.toNat ≤ z.avail_in.toNat := by
    rw [hLd]; unfold rbLen; split
    · rename_i hg; rw [GT.gt, UInt32.lt_iff_toNat_lt] at hg; omega
    · rename_i hg; rw [GT.gt, UInt32.lt_iff_toNat_lt] at hg; omega
  have e1 : ldZStream (some (.tab zr)) h = .ok (z, h) := ldZStream_tab hz
  obtain ⟨z1, hz1⟩ : ∃ z1 : ZStream, z1 = { z with avail_in := z.avail_in - L } := ⟨_, rfl⟩
  obtain ⟨H1, hH1⟩ : ∃ H1 : Heap, H1 = { h with streams := upd h.streams zr (some z1) } := ⟨_, rfl⟩
  have hs1 : H1.streams zr = some z1 := by rw [hH1]; simp
  have e2 : zwr (some (.tab zr)) (rbDec L) h = .ok ((), H1) := by
    unfold zwr; simp only [bind_app, e1]; rw [stZStream_tab hz, hH1, hz1]; try rfl
  have hL0b : (L == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro h0; exact hL0 (by rw [h0]; rfl)
  subst hbuf
  have hdis' : bb ≠ ib ∨ bo + L.toNat ≤ io ∨ io + L.toNat ≤ bo := by
    rcases hdis with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inr h1)
    · exact Or.inr (Or.inl h1)
  -- the copy
  have e3 : zrd (some (.tab zr)) (·.next_in) H1 = .ok (Ptr.ref (BRef.blk ib) io, H1) := by
    simp [zrd, ldZStream_tab hs1, hz1, hin]
  obtain ⟨H2, hH2⟩ : ∃ H2 : Heap, H2 = { H1 with bytes := upd H1.bytes bb (some (copyRange ba ia bo io L.toNat)) } :=
    ⟨_, rfl⟩
  have e4 : memcpyB (Ptr.ref (BRef.blk bb) bo) (Ptr.ref (BRef.blk ib) io) L.toNat H1 = .ok ((), H2) := by
    have := Ptr.memcpy_ok (h := H1) (rd := BRef.blk bb) (rs := BRef.blk ib) (od := bo) (os := io) (n := L.toNat)
      (da := ba) (sa := ia) (by simpa [hH1] using hbb) (by simpa [hH1] using hib) (by simpa [hH1] using hro)
      hfbuf hfin (by simpa using hdis')
    simpa [hH2] using this
  have hs2 : H2.streams zr = some z1 := by rw [hH2]; exact hs1
  have hd2 : H2.dstates dsid = some d := by rw [hH2, hH1]; exact hd
  have e5 : zrd (some (.tab zr)) (·.state) H2 = .ok (some (StateRef.deflate dsid), H2) := by
    simp [zrd, ldZStream_tab hs2, hz1, hs]
  have e6 : rd (some (.tab dsid)) (·.wrap) H2 = .ok (d.wrap, H2) := by
    simp [rd, ldDeflateState_tab hd2]
  have hbib : ∃ X, H2.bytes ib = some X ∧ X.size = ia.size := by
    by_cases hib2 : ib = bb
    · subst hib2
      have : ba = ia := by rw [hib] at hbb; exact (Option.some.inj hbb).symm
      subst this
      exact ⟨copyRange ba ba bo io L.toNat, by rw [hH2]; simp, size_copyRange _ _ _ _ _⟩
    · exact ⟨ia, by rw [hH2, hH1]; simp [upd_ne _ _ _ _ hib2, hib], rfl⟩
  obtain ⟨X, hX, hXs⟩ := hbib
  have hbb2 : H2.bytes bb = some (copyRange ba ia bo io L.toNat) := by rw [hH2]; simp
  have hsz2 : (copyRange ba ia bo io L.toNat).size = ba.size := size_copyRange _ _ _ _ _
  -- the tail after the checksum
  have tailA : ∀ (H3 : Heap) (z2 : ZStream), H3.streams zr = some z2 → z2.next_in = Ptr.ref (BRef.blk ib) io →
      H3.bytes ib = some X →
      zrd (some (.tab zr)) (·.next_in) H3 = .ok (Ptr.ref (BRef.blk ib) io, H3) ∧
      padd (Ptr.ref (BRef.blk ib) io) L.toNat H3 = .ok (Ptr.ref (BRef.blk ib) (io + L.toNat), H3) ∧
      zwr (some (.tab zr)) (rbAdvF (Ptr.ref (BRef.blk ib) (io + L.toNat)) L) H3 =
        .ok ((), { H3 with streams := upd H3.streams zr (some (rbAdv z2 L ib io)) }) := by
    intro H3 z2 hs3 hn3 hX3
    refine ⟨by simp [zrd, ldZStream_tab hs3, hn3], padd_ok' (by simpa using hX3) (by omega), ?_⟩
    unfold zwr
    simp only [bind_app, ldZStream_tab hs3]
    rw [stZStream_tab hs3]
    simp [rbAdv, rbAdvF, hn3]
  have f0 : zrd (some (.tab zr)) (·.avail_in) h = .ok (z.avail_in, h) := by simp [zrd, e1]
  have f7 : zrd (some (.tab zr)) (·.adler) H2 = .ok (z.adler, H2) := by simp [zrd, ldZStream_tab hs2, hz1]
  have hLle32 : L.toNat < 2 ^ 32 := L.toNat_lt
  have hcheck : ∀ (adler' : UInt64) (H3 : Heap), H3 = { H2 with streams := upd H2.streams zr (some { z1 with adler := adler' }) } →
      zwr (some (.tab zr)) (rbSetAd adler') H2 = .ok ((), H3) := by
    intro adler' H3 hH3
    unfold zwr
    simp only [bind_app, ldZStream_tab hs2]
    rw [stZStream_tab hs2, hH3]
    try rfl
  have hend : ∀ (adler' : UInt64) (H3 : Heap), H3 = { H2 with streams := upd H2.streams zr (some { z1 with adler := adler' }) } →
      ({ H3 with streams := upd H3.streams zr (some (rbAdv { z1 with adler := adler' } L ib io)) } : Heap) = { h with
        bytes := upd h.bytes bb (some (copyRange ba ia bo io L.toNat)),
        streams := upd h.streams zr (some (rbStream z L ib io adler')) } := by
    intro adler' H3 hH3
    simp [hH3, hH2, hH1, hz1, upd_upd, rbStream, rbAdv, rbDec, rbSetAd]
  have htail : ∀ (adler' : UInt64) (H3 : Heap), H3 = { H2 with streams := upd H2.streams zr (some { z1 with adler := adler' }) } →
      zrd (some (.tab zr)) (·.next_in) H3 = .ok (Ptr.ref (BRef.blk ib) io, H3) ∧
      padd (Ptr.ref (BRef.blk ib) io) L.toNat H3 = .ok (Ptr.ref (BRef.blk ib) (io + L.toNat), H3) ∧
      zwr (some (.tab zr)) (rbAdvF (Ptr.ref (BRef.blk ib) (io + L.toNat)) L) H3 = .ok ((), { h with
        bytes := upd h.bytes bb (some (copyRange ba ia bo io L.toNat)),
        streams := upd h.streams zr (some (rbStream z L ib io adler')) }) := by
    intro adler' H3 hH3
    have hs3 : H3.streams zr = some { z1 with adler := adler' } := by rw [hH3]; simp
    obtain ⟨t1, t2, t3⟩ := tailA H3 _ hs3 (by rw [hz1]; exact hin) (by rw [hH3]; exact hX)
    exact ⟨t1, t2, by rw [t3, hend adler' H3 hH3]⟩
  have hhead : ∀ (m : M Unit), (m H2 = m H2) → True := fun _ _ => trivial
  by_cases hw1 : d.wrap = 1
  · obtain ⟨r, hr⟩ := Zlib.Adler32.Proofs.adler32_z_safe H2 bb _ hbb2 z.adler bo L.toNat (by omega) (by omega)
    have e7 : Zlib.Adler32.adler32 z.adler (Ptr.ref (BRef.blk bb) bo) L H2 = .ok (r, H2) := by
      unfold Zlib.Adler32.adler32; rw [u32_toUInt64_eq]; exact hr
    obtain ⟨H3, hH3⟩ : ∃ H3 : Heap, H3 = { H2 with streams := upd H2.streams zr (some { z1 with adler := r }) } := ⟨_, rfl⟩
    refine ⟨r, ?_, ?_, ?_, ?_⟩
    · rw [read_buf_eq (Ptr.ref (BRef.blk bb) bo) size hz, ← hLd]; unfold rbCore
      have hb1t : (d.wrap == 1) = true := by simpa using hw1
      simp only [bind_app, pure_app, hL0b, M_ite_app, Bool.false_eq_true, ↓reduceIte, e2, e3, e4, e5,
        castDeflateState_ok, e6, hb1t, f7, e7, hcheck r H3 hH3, (htail r H3 hH3).1, (htail r H3 hH3).2.1, (htail r H3 hH3).2.2]
    · intro _ hc
      have hv : Zlib.Adler32.Proofs.seg (copyRange ba ia bo io L.toNat) bo L.toNat = Zlib.Adler32.Proofs.seg ia io L.toNat :=
        seg_copyRange ba ia bo io L.toNat hfbuf
      have hcor : ∃ r', C.run (Zlib.Adler32.adler32_z z.adler (Ptr.ref (BRef.blk bb) bo) L.toNat.toUInt64) H2 = .ok (r', H2) ∧
          r'.toNat = Zlib.Adler32.Spec.adler32 z.adler.toNat (Zlib.Adler32.Proofs.seg (copyRange ba ia bo io L.toNat) bo L.toNat) := by
        by_cases h1 : L.toNat = 1
        · have hv' : (z.adler >>> 16 &&& 65535).toNat < 65521 := hc.resolve_left (by simpa using h1)
          exact Zlib.Adler32.Proofs.adler32_z_correct H2 bb _ hbb2 z.adler bo L.toNat (by omega) (by omega) hv'
        · exact Zlib.Adler32.Proofs.adler32_z_correct_ne_one H2 bb _ hbb2 z.adler bo L.toNat (by omega) (by omega) h1
      obtain ⟨r', hr', hspec⟩ := hcor
      have : r' = r := by
        have := hr'.symm.trans hr
        simpa using this
      rw [← this, hspec, hv]
    · intro h2; rw [hw1] at h2; exact absurd h2 (by decide)
    · intro h1; exact absurd hw1 h1
  · by_cases hw2 : d.wrap = 2
    · have hS := hstat hw2
      have hS2 : Zlib.Crc32.Proofs.StaticsOK H2 := by rw [hH2, hH1]; exact hS
      have hc := Zlib.Crc32.Proofs.crc32_z_correct H2 hS2 z.adler bb bo _ hbb2 L.toUInt64 (by rw [UInt32.toNat_toUInt64]; omega)
      obtain ⟨r, hrd⟩ : ∃ r, r = (ZlibF.Spec.crc32Update z.adler.toUInt32 (((copyRange ba ia bo io L.toNat).toList.drop bo).take L.toNat)).toUInt64 := ⟨_, rfl⟩
      have e7 : Zlib.Crc32.crc32 z.adler (Ptr.ref (BRef.blk bb) bo) L H2 = .ok (r, H2) := by
        unfold Zlib.Crc32.crc32
        have := hc
        rw [UInt32.toNat_toUInt64] at this
        unfold C.run at this
        rw [hrd]; exact this
      have hseg : ((copyRange ba ia bo io L.toNat).toList.drop bo).take L.toNat = (ia.toList.drop io).take L.toNat := by
        rw [← seg_eq_take_drop _ _ _ (by omega), ← seg_eq_take_drop _ _ _ hfin, seg_copyRange ba ia bo io L.toNat hfbuf]
      obtain ⟨H3, hH3⟩ : ∃ H3 : Heap, H3 = { H2 with streams := upd H2.streams zr (some { z1 with adler := r }) } := ⟨_, rfl⟩
      refine ⟨r, ?_, ?_, ?_, ?_⟩
      · rw [read_buf_eq (Ptr.ref (BRef.blk bb) bo) size hz, ← hLd]; unfold rbCore
        have hb1 : (d.wrap == 1) = false := by simpa using hw1
        have hb2t : (d.wrap == 2) = true := by simpa using hw2
        simp only [bind_app, pure_app, hL0b, M_ite_app, Bool.false_eq_true, ↓reduceIte, e2, e3, e4, e5,
          castDeflateState_ok, e6, hb1, hb2t, f7, e7, hcheck r H3 hH3, (htail r H3 hH3).1, (htail r H3 hH3).2.1, (htail r H3 hH3).2.2]
      · intro h1; exact absurd h1 hw1
      · intro _; rw [hrd, hseg]
      · intro _ h2; exact absurd hw2 h2
    · refine ⟨z.adler, ?_, ?_, ?_, ?_⟩
      · rw [read_buf_eq (Ptr.ref (BRef.blk bb) bo) size hz, ← hLd]; unfold rbCore
        have hb1 : (d.wrap == 1) = false := by simpa using hw1
        have hb2 : (d.wrap == 2) = false := by simpa using hw2
        have hH3 : H2 = { H2 with streams := upd H2.streams zr (some { z1 with adler := z.adler }) } := by
          have : ({ z1 with adler := z.adler } : ZStream) = z1 := by rw [hz1]
          rw [this, upd_self _ _ _ hs2]
        simp only [bind_app, pure_app, hL0b, M_ite_app, Bool.false_eq_true, ↓reduceIte, e2, e3, e4, e5,
          castDeflateState_ok, e6, hb1, hb2]
        have ht := htail z.adler H2 hH3
        simp only [ht.1, ht.2.1, ht.2.2]
      · intro h1; exact absurd h1 hw1
      · intro h1; exact absurd h1 hw2
      · intro _ _; rfl

end Zlib.Deflate.Engine.Proofs
