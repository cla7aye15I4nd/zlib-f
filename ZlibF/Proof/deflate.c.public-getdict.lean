import ZlibF.Proof.«deflate.c.life.getdict»

/-! Dictionary copy into any represented writable byte object. -/

namespace Zlib.Deflate.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Engine.Proofs

/-- `int deflateGetDictionary(z_streamp strm, Bytef *dictionary, uInt *dictLength)`
copies into any represented writable byte object when its source and destination
ranges are disjoint. The exact result describes the updated object. -/
theorem deflateGetDictionary_run_copy_general {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    {w p q b : Nat} (hL : DLive h r ds z d) (hB : DBlocks h d w p q b)
    (hfill : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (dictionary : BPtr) (hasDictLength : Bool) {ref : BRef} {off : Nat} {da wa : Array UInt8}
    (hd : dictionary = .ref ref off) (hda : Space.get h ref = some da) (hro : Space.ro h ref = false)
    (hroom : off + (dictLen d).toNat ≤ da.size) (hwa : h.bytes w = some wa)
    (hlen : (dictLen d).toNat = min (d.strstart.toNat + d.lookahead.toNat) d.w_size.toNat)
    (hne : (dictLen d) ≠ 0)
    (hdis : ref ≠ .blk w ∨ off + (dictLen d).toNat ≤ d.strstart.toNat + d.lookahead.toNat - (dictLen d).toNat ∨
      d.strstart.toNat + d.lookahead.toNat - (dictLen d).toNat + (dictLen d).toNat ≤ off)
    (hwsz : wa.size = d.window_size.toNat) :
    deflateGetDictionary (some r) dictionary hasDictLength h =
      .ok ((Z_OK, if hasDictLength then some (dictLen d) else none),
        Space.put h ref (copyRange da wa off
          (d.strstart.toNat + d.lookahead.toNat - (dictLen d).toNat) (dictLen d).toNat)) := by
  rw [getdict_unfold hL]
  have hc : (dictionary != .null && dictLen d != 0) = true := by simp [hd, hne]
  simp only [hc, ite_true]
  have hwa' : Space.get h (BRef.blk w) = some wa := hwa
  have e1 : padd d.window d.strstart.toNat h = .ok (.ref (.blk w) d.strstart.toNat, h) := by
    have := padd_ok' (r := BRef.blk w) (T := UInt8) (off := 0) (n := d.strstart.toNat) hwa' (by omega)
    rw [hB.win]; simpa using this
  have e2 : padd (.ref (.blk w) d.strstart.toNat : BPtr) d.lookahead.toNat h =
      .ok (.ref (.blk w) (d.strstart.toNat + d.lookahead.toNat), h) :=
    padd_ok' (r := BRef.blk w) (T := UInt8) (off := d.strstart.toNat) (n := d.lookahead.toNat) hwa' (by omega)
  have e3 : psub (.ref (.blk w) (d.strstart.toNat + d.lookahead.toNat) : BPtr) (dictLen d).toNat h =
      .ok (.ref (.blk w) (d.strstart.toNat + d.lookahead.toNat - (dictLen d).toNat), h) :=
    psub_ok' (r := BRef.blk w) (T := UInt8) (off := d.strstart.toNat + d.lookahead.toNat) (n := (dictLen d).toNat)
      hwa' (by omega) (by omega)
  have e4 : memcpyB dictionary (.ref (.blk w) (d.strstart.toNat + d.lookahead.toNat - (dictLen d).toNat))
      (dictLen d).toNat h = .ok ((), Space.put h ref (copyRange da wa off
          (d.strstart.toNat + d.lookahead.toNat - (dictLen d).toNat) (dictLen d).toNat)) := by
    subst hd
    have := Ptr.memcpy_ok (rd := ref) (rs := BRef.blk w) (od := off)
      (os := d.strstart.toNat + d.lookahead.toNat - (dictLen d).toNat) (n := (dictLen d).toNat) (da := da) (sa := wa)
      (by simpa using hda) (by simpa using hwa) (by simpa using hro) hroom (by omega)
      hdis
    simpa using this
  simp only [bind_app, e1, e2, e3, e4, pure_app]


theorem copyRange_extract (da wa : Array UInt8) (off src n : Nat)
    (hd : off + n ≤ da.size) (hs : src + n ≤ wa.size) :
    copyRange da wa off src n = da.extract 0 off ++ wa.extract src (src+n) ++ da.extract (off+n) da.size := by
  apply Array.ext_getElem?
  intro i
  rw [getElem?_copyRange _ _ _ _ _ _ hd]
  have hs1 : min off da.size = off := Nat.min_eq_left (by omega)
  have hs2 : min (src+n) wa.size = src+n := Nat.min_eq_left hs
  by_cases h0 : i < off
  · simp [Array.getElem?_append, Array.getElem?_extract, Array.size_extract, hs1, hs2, h0, show ¬ off ≤ i by omega, show i < da.size by omega]
  · by_cases h1 : i < off + n
    · have hsrc : src + (i - off) < wa.size := by omega
      simp [Array.getElem?_append, Array.getElem?_extract, Array.size_extract, hs1, hs2, h0, h1,
        show off ≤ i by omega, show i - off < n by omega, getElem!_pos wa (src + (i - off)) hsrc]
    · have hshift : off + n + (i - off - n) = i := by omega
      by_cases h2 : i < da.size
      · simp [Array.getElem?_append, Array.getElem?_extract, Array.size_extract, hs1, hs2, h0, h1, h2,
          show ¬ i - off < n by omega, show i - off - n < da.size - (off+n) by omega, hshift]
      · have hout : da[i]? = none := Array.getElem?_eq_none (by omega)
        simp [Array.getElem?_append, Array.getElem?_extract, Array.size_extract, hs1, hs2, h0, h1, h2,
          show ¬ i - off < n by omega, show ¬ i - off - n < da.size - (off+n) by omega, hout]

end Zlib.Deflate.Proofs
