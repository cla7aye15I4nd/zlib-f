import ZlibF.Proof.«inflate.c.dict»
import ZlibF.Proof.«deflate.c.engine.macros»

/-! General byte-object support for the dictionary query. -/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Deflate.Engine.Proofs

/-- Updating a writable byte object preserves a distinct byte-block source.
The two writes to the destination compose to the final replacement. -/
theorem getdict_put_properties {h : Heap} {rd : BRef} {old src : Array UInt8} {w : Nat}
    (hd : Space.get h rd = some old) (hro : Space.ro h rd = false)
    (hw : h.bytes w = some src) (hne : rd ≠ BRef.blk w) (a b : Array UInt8) :
    Space.get (Space.put h rd a) rd = some a ∧
    Space.get (Space.put h rd a) (BRef.blk w) = some src ∧
    Space.ro (Space.put h rd a) rd = false ∧
    Space.put (Space.put h rd a) rd b = Space.put h rd b := by
  cases rd with
  | blk x =>
    change h.ro x = false at hro
    have hx : x ≠ w := fun e => hne (by cases e; rfl)
    simp [Space.get, Space.put, Space.ro, upd_ne _ _ _ _ hx.symm, hw, hro, upd_upd]
  | str x => simp [Space.ro] at hro
  | st_dist_code => simp [Space.ro] at hro
  | st_length_code => simp [Space.ro] at hro
  | dstate_depth x =>
    cases he : h.dstates x with
    | none => simp [Space.get, he] at hd
    | some d =>
      simp [Space.get, Space.put, Space.ro, he, hw, upd_upd]

/-- `int inflateGetDictionary(z_streamp strm, Bytef *dictionary, uInt *dictLength)`
copies both chronological window segments into any distinct writable byte object.
The source remains intact and the final object is described exactly. -/
theorem inflateGetDictionary_copy_general {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    {w off : Nat} {rd : BRef} {a D : Array UInt8} {dl : Option UInt32}
    (hL : Live h r zs z st) (hw : st.window = .ref (.blk w) 0) (ha : h.bytes w = some a)
    (hd : Space.get h rd = some D) (hro : Space.ro h rd = false) (hne : rd ≠ .blk w)
    (hpos : st.whave ≠ 0) (hv : st.wnext.toNat ≤ st.whave.toNat)
    (hwh : st.whave.toNat ≤ a.size) (hfit : off + st.whave.toNat ≤ D.size) :
    inflateGetDictionary (some r) (.ref rd off) dl h =
      .ok ((Z_OK, dl.map (fun _ => st.whave)),
        Space.put h rd (getDictBytes D a off st.wnext.toNat st.whave.toNat)) := by
  have hsub : (st.whave - st.wnext).toNat = st.whave.toNat - st.wnext.toNat :=
    UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; exact hv)
  have hfirst : Ptr.add (Ptr.ref (BRef.blk w) 0) (st.wnext.toNat : Int) h =
      .ok (Ptr.ref (BRef.blk w) st.wnext.toNat, h) := by
    have hh := Ptr.add_nat_ok (a := a) (r := BRef.blk w) (off := 0) (n := st.wnext.toNat) (by simpa using ha) (by omega)
    unfold OkOn at hh
    simpa using hh
  let first := copyRange D a off st.wnext.toNat (st.whave - st.wnext).toNat
  let mid := Space.put h rd first
  have hmem1 : memcpyB (.ref rd off) (.ref (.blk w) st.wnext.toNat) (st.whave - st.wnext).toNat h =
      .ok ((), mid) := by
    exact Ptr.memcpy_ok (rd := rd) (rs := .blk w) hd (by simpa using ha) hro (by omega) (by omega) (Or.inl hne)
  obtain ⟨hdmid, hamid, hromid, hput⟩ := getdict_put_properties hd hro ha hne first
    (getDictBytes D a off st.wnext.toNat st.whave.toNat)
  have hsize : first.size = D.size := size_copyRange ..
  have hadd := Ptr.add_nat_ok (h := mid) (r := rd) (a := first) (off := off) (n := st.whave.toNat) hdmid (by omega)
  have hsub' := Ptr.sub_nat_ok (h := mid) (r := rd) (a := first) (off := off + st.whave.toNat) (n := st.wnext.toNat)
    hdmid (by omega) (by omega)
  have hmem2 : memcpyB (.ref rd (off + st.whave.toNat - st.wnext.toNat)) (.ref (.blk w) 0) st.wnext.toNat mid =
      .ok ((), Space.put mid rd (getDictBytes D a off st.wnext.toNat st.whave.toNat)) := by
    have h := Ptr.memcpy_ok (rd := rd) (rs := .blk w) (od := off + st.whave.toNat - st.wnext.toNat)
      (os := 0) (n := st.wnext.toNat) (da := first) (sa := a) hdmid hamid hromid (by omega) (by omega) (Or.inl hne)
    simpa [getDictBytes, first, mid, hsub] using h
  have hc : (st.whave != 0 && (Ptr.ref rd off : BPtr) != .null) = true := by simp [hpos]
  unfold OkOn at hadd hsub'
  unfold inflateGetDictionary
  simp only [bind_app, pure_app, ldI_eq, ldZ_eq, hL.hz, hL.zst, castI, hL.hs, stateCheck_live hL,
    bne_iff_ne, ne_eq, hpos, not_false_eq_true, not_true_eq_false, ite_false, hc, hw, hfirst, hmem1, Ptr.noConfusion, true_and,
    ite_true, hadd, hsub', hmem2, hput]
  cases dl <;> simp [hsub] <;> exact (show _ from hput)

theorem ring_copy_extract (D a : Array UInt8) (off wn wh : Nat)
    (hwn : wn ≤ wh) (ha : wh ≤ a.size) (hd : off + wh ≤ D.size) :
    getDictBytes D a off wn wh =
      D.extract 0 off ++ (a.extract wn wh ++ a.extract 0 wn) ++ D.extract (off + wh) D.size := by
  apply Array.ext_getElem?
  intro i
  have hfit1 : off + (wh - wn) ≤ D.size := by omega
  have hs1 : (copyRange D a off wn (wh - wn)).size = D.size := size_copyRange ..
  have hfit2 : off + wh - wn + wn ≤ (copyRange D a off wn (wh - wn)).size := by rw [hs1]; omega
  unfold getDictBytes
  rw [getElem?_copyRange _ _ _ _ _ _ hfit2, getElem?_copyRange _ _ _ _ _ _ hfit1]
  have hs0 : min off D.size = off := Nat.min_eq_left (by omega)
  have hs2 : min wh a.size = wh := Nat.min_eq_left ha
  have hs3 : min wn a.size = wn := Nat.min_eq_left (by omega)
  by_cases h0 : i < off
  · simp [Array.getElem?_append, Array.getElem?_extract, Array.size_extract, hs0, hs2, hs3,
      h0, show ¬ off + wh - wn ≤ i by omega, show ¬ off ≤ i by omega, show i < D.size by omega]
  · by_cases h1 : i < off + (wh - wn)
    · have hx : wn + (i-off) < a.size := by omega
      simp [Array.getElem?_append, Array.getElem?_extract, Array.size_extract, hs0, hs2, hs3,
        h0, h1, show off ≤ i by omega, show ¬ off + wh - wn ≤ i by omega,
        show i - off < wh - wn by omega, getElem!_pos a (wn + (i-off)) hx]
    · by_cases h2 : i < off + wh
      · have hx : i - (off + (wh - wn)) < a.size := by omega
        simp [Array.getElem?_append, Array.getElem?_extract, Array.size_extract, hs0, hs2, hs3,
          h0, h1, h2, show off ≤ i by omega, show off + wh - wn ≤ i by omega,
          show i < off + wh - wn + wn by omega, show ¬ i - off < wh - wn by omega,
          show i - off - (wh - wn) < wn by omega,
          show i - (off + wh - wn) = i - off - (wh - wn) by omega,
          getElem!_pos a (i - off - (wh - wn)) (by omega)]
      · by_cases h3 : i < D.size
        · simp [Array.getElem?_append, Array.getElem?_extract, Array.size_extract, hs0, hs2, hs3,
            h0, h1, h2, h3, show ¬ i < off + wh - wn + wn by omega,
            show ¬ i - off < wh - wn by omega,
            show ¬ i - off - (wh - wn) < wn by omega,
            show i - off - (wh - wn) - wn < D.size - (off + wh) by omega,
            show off + wh + (i - off - (wh - wn) - wn) = i by omega]
        · have hout : D[i]? = none := Array.getElem?_eq_none (by omega)
          simp [Array.getElem?_append, Array.getElem?_extract, Array.size_extract, hs0, hs2, hs3,
            h0, h1, h2, h3, show ¬ i < off + wh - wn + wn by omega,
            show ¬ i - off < wh - wn by omega,
            show ¬ i - off - (wh - wn) < wn by omega,
            show ¬ i - off - (wh - wn) - wn < D.size - (off + wh) by omega, hout]

end Zlib.Inflate.Proofs
