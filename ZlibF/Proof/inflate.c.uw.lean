import ZlibF.Proof.«inflate.c.window»

/-!
# inflate.c: `updatewindow`

Safety of `updatewindow` on the real translation. The window is a ring buffer; the copy is done in at most two
pieces (`uwPost`). The proofs follow the pilot (`ZlibF.Runtime.Pilot`): the cases `copy >= wsize`, the copy that fits,
the copy that wraps, and the copy that ends at the end of the window.
-/

namespace Zlib.Inflate.Spec
open C

/-- The window block and the state record after `updatewindow` copied `copy` bytes that end at offset `eo` of the
buffer `ebytes` into the ring buffer `a` of the state `st` (whose `wsize` is already set): the ring buffer is
filled in at most two pieces, as in `inflate.c`. -/
def uwPost (st : InflateState) (a ebytes : Array UInt8) (eo : Nat) (copy : UInt32) : Array UInt8 × InflateState :=
  if st.wsize ≤ copy then
    (copyRange a ebytes 0 (eo - st.wsize.toNat) st.wsize.toNat, { st with wnext := 0, whave := st.wsize })
  else if st.wsize - st.wnext > copy then
    (copyRange a ebytes st.wnext.toNat (eo - copy.toNat) copy.toNat,
      { st with
        wnext := if st.wnext + copy == st.wsize then 0 else st.wnext + copy,
        whave := if st.whave < st.wsize then st.whave + copy else st.whave })
  else if copy - (st.wsize - st.wnext) ≠ 0 then
    (copyRange (copyRange a ebytes st.wnext.toNat (eo - copy.toNat) (st.wsize - st.wnext).toNat)
        ebytes 0 (eo - (copy - (st.wsize - st.wnext)).toNat) (copy - (st.wsize - st.wnext)).toNat,
      { st with wnext := copy - (st.wsize - st.wnext), whave := st.wsize })
  else
    (copyRange a ebytes st.wnext.toNat (eo - copy.toNat) (st.wsize - st.wnext).toNat,
      { st with wnext := 0, whave := if st.whave < st.wsize then st.whave + (st.wsize - st.wnext) else st.whave })

end Zlib.Inflate.Spec

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec

/-- `updatewindow`, first branch (`copy >= wsize`) on a state whose window exists and whose `wsize` is set. -/
theorem uw_core_big {H : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState} {w eb eo : Nat}
    {a ebytes : Array UInt8} {copy : UInt32}
    (hL : Live H r zs z st) (hw : st.window = .ref (.blk w) 0) (ha : H.bytes w = some a) (hro : H.ro w = false)
    (hpos : st.wsize ≠ 0) (hsz : st.wsize.toNat ≤ a.size)
    (heb : H.bytes eb = some ebytes) (hne : w ≠ eb) (hc : st.wsize.toNat ≤ eo) (hoff : eo ≤ ebytes.size)
    (hbig : st.wsize ≤ copy) :
    updatewindow (some r) (.ref (.blk eb) eo) copy H = .ok (0, setI
      { H with bytes := upd H.bytes w (some (copyRange a ebytes 0 (eo - st.wsize.toNat) st.wsize.toNat)) } zs
      { st with wnext := 0, whave := st.wsize }) := by
  have hz := hL.hz
  have hs := hL.hs
  have hwn : (st.window == Ptr.null) = false := by rw [hw]; simp
  have hws0 : (st.wsize == 0) = false := by simpa using hpos
  have hn1 : OkOn H (Ptr.add (Ptr.ref (BRef.blk eb) eo) (-(st.wsize.toNat : Int))) (Ptr.ref (BRef.blk eb) (eo - st.wsize.toNat)) :=
    Ptr.sub_nat_ok (a := ebytes) (by simpa using heb) hc hoff
  have hcp := memcpyB_blk_ok (nb := w) (no := 0) (pb := eb) (po := eo - st.wsize.toNat) (n := st.wsize.toNat)
    (h := H) ha heb hro hne (by omega) (by omega)
  unfold updatewindow
  simp only [bind_app, pure_app, ldI_eq, ldZ_eq, wrI_eq, hz, hL.zst, castI, hs, hwn, hws0, Bool.false_eq_true, ite_false]
  have hn1' : Ptr.add (Ptr.ref (BRef.blk eb) eo) (-(st.wsize.toNat : Int)) H = .ok (Ptr.ref (BRef.blk eb) (eo - st.wsize.toNat), H) := hn1
  simp only [ge_iff_le, hbig, ite_true, bind_app, hw, hn1']
  simp only [hcp, wrI_eq, pure_app, hs]
  simp only [hw]

/-- `updatewindow`, `copy < wsize`, the copy fits before the end of the window (`wsize - wnext > copy`). -/
theorem uw_core_small1 {H : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState} {w eb eo : Nat}
    {a ebytes : Array UInt8} {copy : UInt32}
    (hL : Live H r zs z st) (hw : st.window = .ref (.blk w) 0) (ha : H.bytes w = some a) (hro : H.ro w = false)
    (hpos : st.wsize ≠ 0) (hsz : st.wsize.toNat ≤ a.size) (hwn : st.wnext.toNat < st.wsize.toNat)
    (heb : H.bytes eb = some ebytes) (hne : w ≠ eb) (hc : copy.toNat ≤ eo) (hoff : eo ≤ ebytes.size)
    (hlt : ¬ st.wsize ≤ copy) (hP : st.wsize - st.wnext > copy) :
    updatewindow (some r) (.ref (.blk eb) eo) copy H = .ok (0, setI
      { H with bytes := upd H.bytes w (some (copyRange a ebytes st.wnext.toNat (eo - copy.toNat) copy.toNat)) } zs
      { st with
        wnext := if st.wnext + copy == st.wsize then 0 else st.wnext + copy,
        whave := if st.whave < st.wsize then st.whave + copy else st.whave }) := by
  have hz := hL.hz
  have hs := hL.hs
  have hwnl : (st.window == Ptr.null) = false := by rw [hw]; simp
  have hws0 : (st.wsize == 0) = false := by simpa using hpos
  have hPn : copy.toNat < st.wsize.toNat - st.wnext.toNat := by
    have := UInt32.lt_iff_toNat_lt.mp hP
    rwa [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; omega)] at this
  have hn0 : OkOn H (Ptr.add (Ptr.ref (BRef.blk w) 0) (st.wnext.toNat : Int)) (Ptr.ref (BRef.blk w) (0 + st.wnext.toNat)) :=
    Ptr.add_nat_ok (a := a) (by simpa using ha) (by omega)
  have hn1 : OkOn H (Ptr.add (Ptr.ref (BRef.blk eb) eo) (-(copy.toNat : Int))) (Ptr.ref (BRef.blk eb) (eo - copy.toNat)) :=
    Ptr.sub_nat_ok (a := ebytes) (by simpa using heb) hc hoff
  have hcp := memcpyB_blk_ok (nb := w) (no := 0 + st.wnext.toNat) (pb := eb) (po := eo - copy.toNat) (n := copy.toNat)
    (h := H) ha heb hro hne (by omega) (by omega)
  have hn0' : Ptr.add (Ptr.ref (BRef.blk w) 0) (st.wnext.toNat : Int) H = .ok (Ptr.ref (BRef.blk w) (0 + st.wnext.toNat), H) := hn0
  have hn1' : Ptr.add (Ptr.ref (BRef.blk eb) eo) (-(copy.toNat : Int)) H = .ok (Ptr.ref (BRef.blk eb) (eo - copy.toNat), H) := hn1
  simp only [Nat.zero_add] at hcp hn0'
  unfold updatewindow
  simp only [bind_app, pure_app, ldI_eq, ldZ_eq, hz, hL.zst, castI, hs, hwnl, hws0, Bool.false_eq_true, ite_false]
  simp only [ge_iff_le, hlt, ite_false, hP, ite_true, bind_app, hw, hn0', hn1', UInt32.sub_self, bne_self_eq_false, Bool.false_eq_true]
  simp only [hcp, wrI_eq, pure_app, hs]
  by_cases c1 : st.wnext + copy = st.wsize <;> by_cases c2 : st.whave < st.wsize <;> simp [c1, c2, wrI_eq, hs, setI, hw]

/-- `updatewindow`, `copy < wsize`, the copy reaches or passes the end of the window, it wraps (second piece). -/
theorem uw_core_small2 {H : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState} {w eb eo : Nat}
    {a ebytes : Array UInt8} {copy : UInt32}
    (hL : Live H r zs z st) (hw : st.window = .ref (.blk w) 0) (ha : H.bytes w = some a) (hro : H.ro w = false)
    (hpos : st.wsize ≠ 0) (hsz : st.wsize.toNat ≤ a.size) (hwn : st.wnext.toNat < st.wsize.toNat)
    (heb : H.bytes eb = some ebytes) (hne : w ≠ eb) (hc : copy.toNat ≤ eo) (hoff : eo ≤ ebytes.size)
    (hlt : ¬ st.wsize ≤ copy) (hQ : ¬ st.wsize - st.wnext > copy) (hR : copy - (st.wsize - st.wnext) ≠ 0) :
    updatewindow (some r) (.ref (.blk eb) eo) copy H = .ok (0, setI
      { H with bytes := upd H.bytes w (some (copyRange (copyRange a ebytes st.wnext.toNat (eo - copy.toNat) (st.wsize - st.wnext).toNat)
          ebytes 0 (eo - (copy - (st.wsize - st.wnext)).toNat) (copy - (st.wsize - st.wnext)).toNat)) } zs
      { st with wnext := copy - (st.wsize - st.wnext), whave := st.wsize }) := by
  have hz := hL.hz
  have hs := hL.hs
  have hwnl : (st.window == Ptr.null) = false := by rw [hw]; simp
  have hws0 : (st.wsize == 0) = false := by simpa using hpos
  have hD : (st.wsize - st.wnext).toNat = st.wsize.toNat - st.wnext.toNat :=
    UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; omega)
  have hQn : st.wsize.toNat - st.wnext.toNat ≤ copy.toNat := by
    have : ¬ copy < st.wsize - st.wnext := hQ
    rw [UInt32.lt_iff_toNat_lt, hD] at this; omega
  have hRn : (copy - (st.wsize - st.wnext)).toNat = copy.toNat - (st.wsize.toNat - st.wnext.toNat) := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, hD]; omega), hD]
  have hlt' : copy.toNat < st.wsize.toNat := by
    have : ¬ st.wsize ≤ copy := hlt
    rw [UInt32.le_iff_toNat_le] at this; omega
  have hRpos : 0 < (copy - (st.wsize - st.wnext)).toNat := by
    have : (copy - (st.wsize - st.wnext)).toNat ≠ 0 := fun e => hR (UInt32.toNat_inj.mp (by simpa using e))
    omega
  have hn0 : OkOn H (Ptr.add (Ptr.ref (BRef.blk w) 0) (st.wnext.toNat : Int)) (Ptr.ref (BRef.blk w) (0 + st.wnext.toNat)) :=
    Ptr.add_nat_ok (a := a) (by simpa using ha) (by omega)
  have hn1 : OkOn H (Ptr.add (Ptr.ref (BRef.blk eb) eo) (-(copy.toNat : Int))) (Ptr.ref (BRef.blk eb) (eo - copy.toNat)) :=
    Ptr.sub_nat_ok (a := ebytes) (by simpa using heb) hc hoff
  have hcp1 := memcpyB_blk_ok (nb := w) (no := 0 + st.wnext.toNat) (pb := eb) (po := eo - copy.toNat)
    (n := (st.wsize - st.wnext).toNat) (h := H) ha heb hro hne (by omega) (by omega)
  have hn2 : OkOn H (Ptr.add (Ptr.ref (BRef.blk eb) eo) (-((copy - (st.wsize - st.wnext)).toNat : Int)))
      (Ptr.ref (BRef.blk eb) (eo - (copy - (st.wsize - st.wnext)).toNat)) :=
    Ptr.sub_nat_ok (a := ebytes) (by simpa using heb) (by omega) hoff
  have hn0' : Ptr.add (Ptr.ref (BRef.blk w) 0) (st.wnext.toNat : Int) H = .ok (Ptr.ref (BRef.blk w) (0 + st.wnext.toNat), H) := hn0
  have hn1' : Ptr.add (Ptr.ref (BRef.blk eb) eo) (-(copy.toNat : Int)) H = .ok (Ptr.ref (BRef.blk eb) (eo - copy.toNat), H) := hn1
  simp only [Nat.zero_add] at hcp1 hn0'
  unfold updatewindow
  simp only [bind_app, pure_app, ldI_eq, ldZ_eq, hz, hL.zst, castI, hs, hwnl, hws0, Bool.false_eq_true, ite_false]
  simp only [ge_iff_le, hlt, ite_false, hQ, bind_app, hw, hn0', hn1', hcp1]
  have hne' : ¬ (copy - (st.wsize - st.wnext) = 0) := hR
  have hA1 : (copyRange a ebytes st.wnext.toNat (eo - copy.toNat) (st.wsize - st.wnext).toNat).size = a.size := size_copyRange ..
  have hbm : ({ H with bytes := upd H.bytes w (some (copyRange a ebytes st.wnext.toNat (eo - copy.toNat) (st.wsize - st.wnext).toNat)) } : Heap).bytes eb = some ebytes := by
    simp [upd_ne _ _ _ _ hne.symm, heb]
  have hn2m : Ptr.add (Ptr.ref (BRef.blk eb) eo) (-((copy - (st.wsize - st.wnext)).toNat : Int))
      { H with bytes := upd H.bytes w (some (copyRange a ebytes st.wnext.toNat (eo - copy.toNat) (st.wsize - st.wnext).toNat)) } =
      .ok (Ptr.ref (BRef.blk eb) (eo - (copy - (st.wsize - st.wnext)).toNat), { H with bytes := upd H.bytes w (some (copyRange a ebytes st.wnext.toNat (eo - copy.toNat) (st.wsize - st.wnext).toNat)) }) :=
    Ptr.sub_nat_ok (a := ebytes) (by simpa using hbm) (by omega) hoff
  have hcp2 := memcpyB_blk_ok (nb := w) (no := 0) (pb := eb) (po := eo - (copy - (st.wsize - st.wnext)).toNat)
    (n := (copy - (st.wsize - st.wnext)).toNat)
    (h := { H with bytes := upd H.bytes w (some (copyRange a ebytes st.wnext.toNat (eo - copy.toNat) (st.wsize - st.wnext).toNat)) })
    (ob := copyRange a ebytes st.wnext.toNat (eo - copy.toNat) (st.wsize - st.wnext).toNat) (by simp) hbm (by simpa using hro) hne
    (by omega) (by omega)
  have hn2g : ∀ H' : Heap, H'.bytes eb = some ebytes →
      Ptr.add (Ptr.ref (BRef.blk eb) eo) (-((copy - (st.wsize - st.wnext)).toNat : Int)) H' =
      .ok (Ptr.ref (BRef.blk eb) (eo - (copy - (st.wsize - st.wnext)).toNat), H') := fun H' hb =>
    Ptr.sub_nat_ok (a := ebytes) (by simpa using hb) (by omega) hoff
  have hbm' : (upd H.bytes w (some (copyRange a ebytes st.wnext.toNat (eo - copy.toNat) (st.wsize - st.wnext).toNat))).get eb = some ebytes := by
    simpa using hbm
  simp only [bne_iff_ne, ne_eq, hne', not_false_eq_true, ite_true]
  rw [bind_app, hn2g _ hbm]
  simp only [bind_app, hcp2, wrI_eq, pure_app, hs, hw]
  simp [setI, upd_upd]

/-- `updatewindow`, `copy < wsize`, the copy ends exactly at the end of the window. -/
theorem uw_core_small3 {H : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState} {w eb eo : Nat}
    {a ebytes : Array UInt8} {copy : UInt32}
    (hL : Live H r zs z st) (hw : st.window = .ref (.blk w) 0) (ha : H.bytes w = some a) (hro : H.ro w = false)
    (hpos : st.wsize ≠ 0) (hsz : st.wsize.toNat ≤ a.size) (hwn : st.wnext.toNat < st.wsize.toNat)
    (heb : H.bytes eb = some ebytes) (hne : w ≠ eb) (hc : copy.toNat ≤ eo) (hoff : eo ≤ ebytes.size)
    (hlt : ¬ st.wsize ≤ copy) (hQ : ¬ st.wsize - st.wnext > copy) (hR : copy - (st.wsize - st.wnext) = 0) :
    updatewindow (some r) (.ref (.blk eb) eo) copy H = .ok (0, setI
      { H with bytes := upd H.bytes w (some (copyRange a ebytes st.wnext.toNat (eo - copy.toNat) (st.wsize - st.wnext).toNat)) } zs
      { st with wnext := 0, whave := if st.whave < st.wsize then st.whave + (st.wsize - st.wnext) else st.whave }) := by
  have hz := hL.hz
  have hs := hL.hs
  have hwnl : (st.window == Ptr.null) = false := by rw [hw]; simp
  have hws0 : (st.wsize == 0) = false := by simpa using hpos
  have hD : (st.wsize - st.wnext).toNat = st.wsize.toNat - st.wnext.toNat :=
    UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; omega)
  have hQn : st.wsize.toNat - st.wnext.toNat ≤ copy.toNat := by
    have : ¬ copy < st.wsize - st.wnext := hQ
    rw [UInt32.lt_iff_toNat_lt, hD] at this; omega
  have hRn : copy.toNat = st.wsize.toNat - st.wnext.toNat := by
    have h0 : (copy - (st.wsize - st.wnext)).toNat = 0 := by rw [hR]; rfl
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, hD]; omega), hD] at h0; omega
  have hcopy : copy = st.wsize - st.wnext := by
    apply UInt32.toNat_inj.mp; rw [hD]; exact hRn
  have hsum : st.wnext + copy = st.wsize := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_add, hRn]; have := st.wsize.toNat_lt; rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hn0 : OkOn H (Ptr.add (Ptr.ref (BRef.blk w) 0) (st.wnext.toNat : Int)) (Ptr.ref (BRef.blk w) (0 + st.wnext.toNat)) :=
    Ptr.add_nat_ok (a := a) (by simpa using ha) (by omega)
  have hn1 : OkOn H (Ptr.add (Ptr.ref (BRef.blk eb) eo) (-(copy.toNat : Int))) (Ptr.ref (BRef.blk eb) (eo - copy.toNat)) :=
    Ptr.sub_nat_ok (a := ebytes) (by simpa using heb) hc hoff
  have hcp := memcpyB_blk_ok (nb := w) (no := 0 + st.wnext.toNat) (pb := eb) (po := eo - copy.toNat)
    (n := (st.wsize - st.wnext).toNat) (h := H) ha heb hro hne (by omega) (by omega)
  have hn0' : Ptr.add (Ptr.ref (BRef.blk w) 0) (st.wnext.toNat : Int) H = .ok (Ptr.ref (BRef.blk w) (0 + st.wnext.toNat), H) := hn0
  have hn1' : Ptr.add (Ptr.ref (BRef.blk eb) eo) (-(copy.toNat : Int)) H = .ok (Ptr.ref (BRef.blk eb) (eo - copy.toNat), H) := hn1
  simp only [Nat.zero_add] at hcp hn0'
  unfold updatewindow
  simp only [bind_app, pure_app, ldI_eq, ldZ_eq, hz, hL.zst, castI, hs, hwnl, hws0, Bool.false_eq_true, ite_false]
  simp only [ge_iff_le, hlt, ite_false, hQ, bind_app, hw, hn0', hn1', hcp, hR, bne_self_eq_false, Bool.false_eq_true]
  have hsum' : st.wnext + (st.wsize - st.wnext) = st.wsize := by rw [← hcopy]; exact hsum
  by_cases c2 : st.whave < st.wsize <;> simp [c2, wrI_eq, hs, setI, hw, hsum']

theorem shl_toNat_aux {b : UInt32} (hb : b.toNat ≤ 15) : ((1 : UInt32) <<< b).toNat = 2 ^ b.toNat := W.shl_toNat b hb

/-- The state after the first two lines of `updatewindow` when `wsize` was 0. -/
def initWinS (st : InflateState) : InflateState :=
  if st.wsize == 0 then { st with wsize := (1 : UInt32) <<< st.wbits, wnext := 0, whave := 0 } else st

theorem shl32_one {b : UInt32} (hb : b.toNat ≤ 15) : shl32 1 b = pure ((1 : UInt32) <<< b) := by
  have : b < 32 := by rw [UInt32.lt_iff_toNat_lt]; have : (32 : UInt32).toNat = 32 := rfl; omega
  simp [shl32, this]

/-- Initialising `wsize` first does not change what `updatewindow` does. -/
theorem uw_init {H : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState} {w : Nat}
    (hL : Live H r zs z st) (hw : st.window = .ref (.blk w) 0) (hb : st.wbits.toNat ≤ 15) (e : BPtr) (copy : UInt32) :
    updatewindow (some r) e copy H = updatewindow (some r) e copy (setI H zs (initWinS st)) := by
  have hz := hL.hz
  have hs := hL.hs
  have hwnl : (st.window == Ptr.null) = false := by rw [hw]; simp
  have hsh := shl32_one hb
  by_cases h0 : st.wsize = 0
  · have hws0 : (st.wsize == 0) = true := by simp [h0]
    have hI : initWinS st = { st with wsize := (1 : UInt32) <<< st.wbits, wnext := 0, whave := 0 } := by
      simp [initWinS, hws0]
    have hpos : ((1 : UInt32) <<< st.wbits) ≠ 0 := by
      intro e; have := shl_toNat_aux hb; rw [e] at this; have h2 := Nat.two_pow_pos st.wbits.toNat
      have h3 : (0 : UInt32).toNat = 0 := rfl
      omega
    rw [hI]
    unfold updatewindow
    simp only [bind_app, pure_app, ldI_eq, ldZ_eq, wrI_eq, hz, hL.zst, castI, hs, hwnl, hws0, hsh, hI,
      Bool.false_eq_true, ite_false, ite_true, setI_istates_same, ZStreamRef.get_setI]
    simp only [h0, beq_self_eq_true, ite_true, hpos, beq_iff_eq, ne_eq]
    simp only [ite_false, if_false, Bool.false_eq_true, ite_true, bind_app, pure_app, wrI_eq, ldI_eq, setI_istates_same]
    done
  · have hws0 : (st.wsize == 0) = false := by simpa using h0
    have hI : initWinS st = st := by simp [initWinS, hws0]
    rw [hI]
    have : setI H zs st = H := by
      simp only [setI]; rw [upd_self _ _ _ hs]
    rw [this]

theorem zallocb_run {H : Heap} {r : ZStreamRef} {z : ZStream} (hz : r.get H = some z) (hza : z.zalloc = .fn "zcalloc") (items size : UInt32) :
    ZALLOCB (some r) items size H = Zlib.Zutil.zcalloc z.«opaque» items size H := by
  simp [ZALLOCB, ldZ_eq, hz, hza]

/-- The window is `NULL` and the allocation fails: `updatewindow` returns 1 and only the allocation counter moves. -/
theorem uw_alloc_fail {H : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    (hL : Live H r zs z st) (hza : z.zalloc = .fn "zcalloc") (hb : st.wbits.toNat ≤ 15) (hw : st.window = .null)
    (hok : ¬ H.allocOk H.nalloc = true) (e : BPtr) (copy : UInt32) :
    updatewindow (some r) e copy H = .ok (1, setI { H with nalloc := H.nalloc + 1 } zs st) := by
  have hz := hL.hz
  have hs := hL.hs
  have hsh := shl32_one hb
  unfold updatewindow
  have hf := Zlib.Zutil.Proofs.zcalloc_fail_run H z.«opaque» (1 <<< st.wbits) 1 hok
  have hf' : Zlib.Zutil.zcalloc z.«opaque» (1 <<< st.wbits) 1 H = .ok (.null, { H with nalloc := H.nalloc + 1 }) := by
    simpa [Zlib.Zutil.Proofs.failHeap] using hf
  simp only [bind_app, pure_app, ldI_eq, ldZ_eq, hz, hL.zst, castI, hs, hw, beq_self_eq_true, ite_true, hsh,
    zallocb_run hz hza, hf', wrI_eq]
  have e : ({ st with window := Ptr.null } : InflateState) = st := by rw [← hw]
  simp only [e, setI]

theorem ZStreamRef.get_allocHeap (h : Heap) (n : Nat) (r : ZStreamRef) : r.get (Zlib.Zutil.Proofs.allocHeap h n) = r.get h := by
  cases r <;> rfl

/-- The window is `NULL` and the allocation succeeds: the call continues as on the state with the new window block. -/
theorem uw_alloc_ok {H : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    (hL : Live H r zs z st) (hza : z.zalloc = .fn "zcalloc") (hb : st.wbits.toNat ≤ 15) (hw : st.window = .null)
    (hok : H.allocOk H.nalloc = true) (hF : Fresh H) (e : BPtr) (copy : UInt32) :
    updatewindow (some r) e copy H = updatewindow (some r) e copy
      (setI (Zlib.Zutil.Proofs.allocHeap H ((1 <<< st.wbits : UInt32) * 1).toNat) zs
        { st with window := .ref (.blk H.nextBlk) 0 }) := by
  have hz := hL.hz
  have hs := hL.hs
  have hsh := shl32_one hb
  have hc := Zlib.Zutil.Proofs.zcalloc_ok_run H z.«opaque» (1 <<< st.wbits) 1 hok hF
  have hne : (Ptr.ref (BRef.blk H.nextBlk) 0 == (Ptr.null : BPtr)) = false := by simp
  have hnn : (Ptr.ref (BRef.blk H.nextBlk) 0 : BPtr) ≠ Ptr.null := by simp
  have hI : (Zlib.Zutil.Proofs.allocHeap H ((1 <<< st.wbits : UInt32) * 1).toNat).istates zs = some st := by
    simpa [Zlib.Zutil.Proofs.allocHeap] using hs
  unfold updatewindow
  simp only [bind_app, pure_app, ldI_eq, ldZ_eq, hz, hL.zst, castI, hs, hw, beq_self_eq_true, ite_true, hsh,
    zallocb_run hz hza, hc, wrI_eq, hne, Bool.false_eq_true, ite_false, ZStreamRef.get_setI, setI_istates_same, hI]
  simp only [bind_app, ldI_eq, ldZ_eq, wrI_eq, setI_istates_same, hnn, ZStreamRef.get_setI, ZStreamRef.get_allocHeap, ite_false, Bool.false_eq_true, beq_iff_eq, hz, hL.zst, castI, hne, hI, hsh]
  done

/-- `updatewindow` on a state whose window block exists: `wsize` is set if it was 0, then the ring buffer is filled
(`uwPost`); the call returns 0. -/
theorem uw_main {H : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState} {w eb eo : Nat}
    {a ebytes : Array UInt8} {copy : UInt32}
    (hL : Live H r zs z st) (hw : st.window = .ref (.blk w) 0) (ha : H.bytes w = some a) (hro : H.ro w = false)
    (hwb : st.wbits.toNat ≤ 15) (hasz : a.size = 2 ^ st.wbits.toNat)
    (hws : st.wsize.toNat = 0 ∨ st.wsize.toNat = 2 ^ st.wbits.toNat)
    (hwn : st.wnext.toNat < st.wsize.toNat ∨ (st.wsize.toNat = 0 ∧ st.wnext.toNat = 0))
    (heb : H.bytes eb = some ebytes) (hne : w ≠ eb) (hc : copy.toNat ≤ eo) (hoff : eo ≤ ebytes.size) :
    updatewindow (some r) (.ref (.blk eb) eo) copy H = .ok (0, setI
      { setI H zs (initWinS st) with bytes := upd H.bytes w (some (uwPost (initWinS st) a ebytes eo copy).1) } zs
      (uwPost (initWinS st) a ebytes eo copy).2) := by
  have hpow := shl_toNat_aux hwb
  have h2pos := Nat.two_pow_pos st.wbits.toNat
  have hcase : (st.wsize = 0 ∧ initWinS st = { st with wsize := (1 : UInt32) <<< st.wbits, wnext := 0, whave := 0 }) ∨
      (st.wsize ≠ 0 ∧ initWinS st = st) := by
    by_cases h0 : st.wsize = 0
    · left; exact ⟨h0, by simp [initWinS, h0]⟩
    · right; exact ⟨h0, by simp [initWinS, h0]⟩
  have hpos : (initWinS st).wsize ≠ 0 ∧ (initWinS st).wsize.toNat = 2 ^ st.wbits.toNat ∧ (initWinS st).wnext.toNat < (initWinS st).wsize.toNat := by
    rcases hcase with ⟨h0, e⟩ | ⟨h0, e⟩
    · rw [e]
      have hz0 : ((1 : UInt32) <<< st.wbits).toNat = 2 ^ st.wbits.toNat := hpow
      refine ⟨fun hh => ?_, hz0, ?_⟩
      · have h0' : ((1 : UInt32) <<< st.wbits).toNat = 0 := by
          have hh' : ((1 : UInt32) <<< st.wbits) = 0 := hh
          rw [hh']; rfl
        omega
      · show (0 : UInt32).toNat < ((1 : UInt32) <<< st.wbits).toNat
        rw [hz0]; simp; omega
    · rw [e]
      have : st.wsize.toNat ≠ 0 := fun hh => h0 (UInt32.toNat_inj.mp (by simpa using hh))
      refine ⟨h0, by omega, by omega⟩
  have hsz1 : (initWinS st).wsize.toNat ≤ a.size := by omega
  have hwn1 := hpos.2.2
  have hpos := hpos.1
  have hL1 : Live (setI H zs (initWinS st)) r zs z (initWinS st) :=
    ⟨by simpa using hL.hz, by simp, hL.zst, by unfold initWinS; split <;> exact hL.back, by unfold initWinS; split <;> exact hL.mode,
      hL.zalloc, hL.zfree⟩
  have hw1 : (initWinS st).window = .ref (.blk w) 0 := by unfold initWinS; split <;> exact hw
  rw [uw_init hL hw hwb]
  have ha1 : (setI H zs (initWinS st)).bytes w = some a := ha
  have hro1 : (setI H zs (initWinS st)).ro w = false := hro
  have heb1 : (setI H zs (initWinS st)).bytes eb = some ebytes := heb
  by_cases hbig : (initWinS st).wsize ≤ copy
  · have := uw_core_big hL1 hw1 ha1 hro1 hpos hsz1 heb1 hne (by have := UInt32.le_iff_toNat_le.mp hbig; omega) hoff hbig
    simpa [uwPost, hbig] using this
  · by_cases hP : (initWinS st).wsize - (initWinS st).wnext > copy
    · have hlt : copy.toNat < (initWinS st).wsize.toNat := by
        have : ¬ (initWinS st).wsize ≤ copy := hbig
        rw [UInt32.le_iff_toNat_le] at this; omega
      have := uw_core_small1 hL1 hw1 ha1 hro1 hpos hsz1 hwn1 heb1 hne (by omega) hoff hbig hP
      simpa [uwPost, hbig, hP] using this
    · by_cases hR : copy - ((initWinS st).wsize - (initWinS st).wnext) = 0
      · have hlt : copy.toNat < (initWinS st).wsize.toNat := by
          have : ¬ (initWinS st).wsize ≤ copy := hbig
          rw [UInt32.le_iff_toNat_le] at this; omega
        have := uw_core_small3 hL1 hw1 ha1 hro1 hpos hsz1 hwn1 heb1 hne (by omega) hoff hbig hP hR
        simpa [uwPost, hbig, hP, hR] using this
      · have hlt : copy.toNat < (initWinS st).wsize.toNat := by
          have : ¬ (initWinS st).wsize ≤ copy := hbig
          rw [UInt32.le_iff_toNat_le] at this; omega
        have := uw_core_small2 hL1 hw1 ha1 hro1 hpos hsz1 hwn1 heb1 hne (by omega) hoff hbig hP hR
        simpa [uwPost, hbig, hP, hR] using this

/-- The ring-buffer indices after `updatewindow` (`uwPost`) keep the window invariant, and the other fields are kept. -/
theorem uwPost_arith {st : InflateState} {a ebytes : Array UInt8} {eo : Nat} {copy : UInt32}
    (hpos : st.wsize.toNat ≠ 0)
    (hv : st.whave.toNat ≤ st.wsize.toNat) (hwn : st.wnext.toNat < st.wsize.toNat)
    (heq : st.whave.toNat < st.wsize.toNat → st.wnext.toNat = st.whave.toNat)
    (hcl : copy.toNat < 2 ^ 32) (hw32 : st.wsize.toNat ≤ 2 ^ 16) :
    (uwPost st a ebytes eo copy).2.wsize = st.wsize ∧ (uwPost st a ebytes eo copy).2.wbits = st.wbits ∧
    (uwPost st a ebytes eo copy).2.window = st.window ∧ (uwPost st a ebytes eo copy).2.reqbits = st.reqbits ∧
    (uwPost st a ebytes eo copy).2.bits = st.bits ∧ (uwPost st a ebytes eo copy).2.next = st.next ∧
    (uwPost st a ebytes eo copy).2.lencode = st.lencode ∧ (uwPost st a ebytes eo copy).2.distcode = st.distcode ∧
    (uwPost st a ebytes eo copy).2.lens = st.lens ∧ (uwPost st a ebytes eo copy).2.work = st.work ∧
    (uwPost st a ebytes eo copy).2.codes = st.codes ∧ (uwPost st a ebytes eo copy).2.strm = st.strm ∧
    (uwPost st a ebytes eo copy).2.mode = st.mode ∧
    (uwPost st a ebytes eo copy).2.whave.toNat ≤ (uwPost st a ebytes eo copy).2.wsize.toNat ∧
    (uwPost st a ebytes eo copy).2.wnext.toNat < (uwPost st a ebytes eo copy).2.wsize.toNat ∧
    ((uwPost st a ebytes eo copy).2.whave.toNat < (uwPost st a ebytes eo copy).2.wsize.toNat →
      (uwPost st a ebytes eo copy).2.wnext.toNat = (uwPost st a ebytes eo copy).2.whave.toNat) := by
  have e1 := st.wsize.toNat_lt
  have e2 := st.wnext.toNat_lt
  have e3 := st.whave.toNat_lt
  unfold uwPost
  repeat' split
  all_goals
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  all_goals
    simp only [UInt32.lt_iff_toNat_lt, UInt32.le_iff_toNat_le, UInt32.toNat_add, UInt32.toNat_sub, gt_iff_lt, beq_iff_eq,
      bne_iff_ne, ne_eq, ← UInt32.toNat_inj, UInt32.toNat_zero, Nat.not_lt, Nat.not_le] at *
    omega

theorem initWinS_facts {st : InflateState} (hwb : st.wbits.toNat ≤ 15)
    (hws : st.wsize.toNat = 0 ∨ st.wsize.toNat = 2 ^ st.wbits.toNat)
    (hv : st.whave.toNat ≤ st.wsize.toNat) (hwn : st.wnext.toNat < st.wsize.toNat ∨ (st.wsize.toNat = 0 ∧ st.wnext.toNat = 0))
    (heq : st.whave.toNat < st.wsize.toNat → st.wnext.toNat = st.whave.toNat) :
    (initWinS st).wsize.toNat = 2 ^ st.wbits.toNat ∧ (initWinS st).wbits = st.wbits ∧ (initWinS st).window = st.window ∧
    (initWinS st).whave.toNat ≤ (initWinS st).wsize.toNat ∧ (initWinS st).wnext.toNat < (initWinS st).wsize.toNat ∧
    ((initWinS st).whave.toNat < (initWinS st).wsize.toNat → (initWinS st).wnext.toNat = (initWinS st).whave.toNat) ∧
    (initWinS st).reqbits = st.reqbits ∧ (initWinS st).bits = st.bits ∧ (initWinS st).next = st.next ∧
    (initWinS st).lencode = st.lencode ∧ (initWinS st).distcode = st.distcode ∧ (initWinS st).lens = st.lens ∧
    (initWinS st).work = st.work ∧ (initWinS st).codes = st.codes ∧ (initWinS st).strm = st.strm ∧
    (initWinS st).mode = st.mode := by
  have hpow := shl_toNat_aux hwb
  have h2pos := Nat.two_pow_pos st.wbits.toNat
  by_cases h0 : st.wsize = 0
  · have e : initWinS st = { st with wsize := (1 : UInt32) <<< st.wbits, wnext := 0, whave := 0 } := by simp [initWinS, h0]
    rw [e]
    refine ⟨hpow, rfl, rfl, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · show (0 : UInt32).toNat ≤ _; simp
    · show (0 : UInt32).toNat < ((1 : UInt32) <<< st.wbits).toNat; rw [hpow]; simp; omega
    · intro hh; show (0 : UInt32).toNat = (0 : UInt32).toNat; rfl
  · have e : initWinS st = st := by simp [initWinS, h0]
    have : st.wsize.toNat ≠ 0 := fun hh => h0 (UInt32.toNat_inj.mp (by simpa using hh))
    rw [e]
    refine ⟨by omega, rfl, rfl, hv, by omega, heq, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem uwPost_size (st : InflateState) (a ebytes : Array UInt8) (eo : Nat) (copy : UInt32) :
    (uwPost st a ebytes eo copy).1.size = a.size := by
  unfold uwPost
  split
  · exact size_copyRange ..
  · split
    · exact size_copyRange ..
    · split
      · rw [size_copyRange, size_copyRange]
      · exact size_copyRange ..

/-- `updatewindow` on a good stream whose window block exists (`copy` bytes that end at offset `eo` of the block `eb`,
which is not the window): it returns 0, fills the ring buffer as `uwPost` says, and the stream is good again. -/
theorem uw_post {H : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState} {w eb eo : Nat}
    {a ebytes : Array UInt8} {copy : UInt32}
    (hG : Good H r zs z st) (hw : st.window = .ref (.blk w) 0) (ha : H.bytes w = some a) (hro : H.ro w = false)
    (hasz : a.size = 2 ^ st.wbits.toNat)
    (heb : H.bytes eb = some ebytes) (hne : w ≠ eb) (hc : copy.toNat ≤ eo) (hoff : eo ≤ ebytes.size) :
    ∃ H' st', updatewindow (some r) (.ref (.blk eb) eo) copy H = .ok (0, H') ∧
      H' = setI { setI H zs (initWinS st) with bytes := upd H.bytes w (some (uwPost (initWinS st) a ebytes eo copy).1) } zs st' ∧
      st' = (uwPost (initWinS st) a ebytes eo copy).2 ∧ Good H' r zs z st' ∧ st'.window = st.window ∧
      H'.bytes w = some (uwPost (initWinS st) a ebytes eo copy).1 ∧ (uwPost (initWinS st) a ebytes eo copy).1.size = a.size ∧
      (∀ b, b ≠ w → H'.bytes b = H.bytes b) ∧ (∀ b, H'.live b ↔ H.live b) ∧ H'.nextBlk = H.nextBlk := by
  have hL := hG.live
  have hI := hG.inv
  have hmain := uw_main hL hw ha hro hI.win.wbits hasz hI.win.ws hI.win.wn heb hne hc hoff
  obtain ⟨f1, f2, f3, hv1, hwn1, heq1, f4, f5, f6, f7, f8, f16, f17, f18, f12, f13⟩ :=
    initWinS_facts hI.win.wbits hI.win.ws hI.win.hv hI.win.wn hI.win.eq
  have hwb := hI.win.wbits
  have hle : (initWinS st).wsize.toNat ≤ 2 ^ 16 := by
    rw [f1]; have := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : st.wbits.toNat ≤ 16); omega
  have hposn : (initWinS st).wsize.toNat ≠ 0 := by rw [f1]; exact Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, gv, gwn, geq⟩ :=
    uwPost_arith (st := initWinS st) (a := a) (ebytes := ebytes) (eo := eo) (copy := copy) hposn hv1 hwn1 heq1 copy.toNat_lt hle
  have hAsz := uwPost_size (initWinS st) a ebytes eo copy
  generalize hP : uwPost (initWinS st) a ebytes eo copy = P at *
  have hs1 : (setI H zs (initWinS st)).istates zs = some (initWinS st) := by simp
  have hbw : (setI H zs (initWinS st)).bytes w = some a := ha
  have hS : Shape H { setI H zs (initWinS st) with bytes := upd H.bytes w (some P.1) } :=
    (shape_setI hL.hs _).trans (shape_setB (h := setI H zs (initWinS st)) hbw P.1)
  have hS2 : Shape H (setI { setI H zs (initWinS st) with bytes := upd H.bytes w (some P.1) } zs P.2) :=
    hS.trans (shape_setI (s0 := initWinS st) (by simp) _)
  have hz0 : r.get { setI H zs (initWinS st) with bytes := upd H.bytes w (some P.1) } = some z := by
    cases r <;> simpa [ZStreamRef.get] using hL.hz
  have hs0 : ({ setI H zs (initWinS st) with bytes := upd H.bytes w (some P.1) } : Heap).istates zs = some (initWinS st) := by
    simp
  have hUh : Uniq { setI H zs (initWinS st) with bytes := upd H.bytes w (some P.1) } := hS.uniq hG.uniq
  have hFh : Fresh { setI H zs (initWinS st) with bytes := upd H.bytes w (some P.1) } := hS.fresh (by simp) hG.fresh
  have hstI : StInv { setI H zs (initWinS st) with bytes := upd H.bytes w (some P.1) } zs P.2 := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨w1, w2, w3⟩ := hI.wf
      exact ⟨by rw [g9, f16]; exact w1, by rw [g10, f17]; exact w2, by rw [g11, f18]; exact w3⟩
    · refine ⟨by rw [g2, f2]; exact hI.win.wbits, Or.inr ⟨w, P.1, by rw [g3, f3]; exact hw, by simp, by simpa using hro, ?_⟩,
        fun h0 => ?_, ?_, gv, Or.inl gwn, geq⟩
      · rw [g2, f2, hAsz, hasz]
      · rw [g3, f3, hw] at h0; cases h0
      · rw [g1, f1, g2, f2]; right; rfl
    · rw [g4, f4]; exact hI.reqbits
    · rw [g5, f5]; exact hI.bits
    · unfold PtrInv; rw [g6, f6, g7, f7, g8, f8]; exact hI.ptr
  refine ⟨_, P.2, hmain, rfl, rfl, ?_, by rw [g3, f3], by simp, hAsz, ?_, fun b => hS2.live b, by simp⟩
  · have := good_set hz0 hs0 hUh hFh hL.zst hL.zalloc hL.zfree (by rw [g12, f12]; exact hL.back)
      (by rw [g13, f13]; exact hL.mode) hstI
    rwa [ZStreamRef.put_self hz0] at this
  · intro b hb; simp [upd_ne _ _ _ _ hb]

theorem uniq_allocHeap {h : Heap} (hU : Uniq h) (hF : Fresh h) (n : Nat) : Uniq (Zlib.Zutil.Proofs.allocHeap h n) := by
  intro b
  by_cases hb : b = h.nextBlk
  · subst hb
    have := Heap.not_live.mp (hF _ (Nat.le_refl _))
    obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := this
    simp [Zlib.Zutil.Proofs.allocHeap, e1, e2, e3, e4, e5, e6]
  · have := hU b
    simpa only [Zlib.Zutil.Proofs.allocHeap, upd_ne _ _ _ _ hb] using this

/-- The state of a stream whose window `NULL` was just replaced by the new block. -/
def withWin (st : InflateState) (nb : Nat) : InflateState := { st with window := .ref (.blk nb) 0 }

/-- **updatewindow, window absent and the allocation succeeds.** The window is a new block (the next block number,
`1 << wbits` bytes of arbitrary content), then filled as `uwPost` says; the stream is good again and owns the new
block. -/
theorem uw_null_ok {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState} {eb eo : Nat}
    {ebytes : Array UInt8} {copy : UInt32}
    (hG : Good h r zs z st) (hza : z.zalloc = .fn "zcalloc") (hw : st.window = .null)
    (hok : h.allocOk h.nalloc = true) (heb : h.bytes eb = some ebytes) (hc : copy.toNat ≤ eo) (hoff : eo ≤ ebytes.size) :
    ∃ H' st', updatewindow (some r) (.ref (.blk eb) eo) copy h = .ok (0, H') ∧ Good H' r zs z st' ∧
      st'.window = .ref (.blk h.nextBlk) 0 ∧ (∃ A, H'.bytes h.nextBlk = some A) ∧
      (∀ S, h.Owns S → H'.Owns (fun b => S b ∨ b = h.nextBlk)) ∧ H'.nextBlk = h.nextBlk + 1 ∧
      (∀ b, b ≠ h.nextBlk → H'.bytes b = h.bytes b) := by
  have hL := hG.live
  have hI := hG.inv
  have hF := hG.fresh
  have hne : eb ≠ h.nextBlk := by
    intro e; have := Fresh.bytes hF (b := h.nextBlk) (Nat.le_refl _); rw [← e, heb] at this; cases this
  rw [uw_alloc_ok hL hza hI.win.wbits hw hok hF]
  have hn : ((1 <<< st.wbits : UInt32) * 1).toNat = 2 ^ st.wbits.toNat := by
    have := shl_toNat_aux hI.win.wbits
    simpa using this
  obtain ⟨A0, hA0⟩ : ∃ A0 : Array UInt8, A0 = Array.ofFn (n := ((1 <<< st.wbits : UInt32) * 1).toNat)
      fun i => Junk.of (h.garbage h.nalloc i.val) := ⟨_, rfl⟩
  have hA0sz : A0.size = 2 ^ st.wbits.toNat := by rw [hA0, Array.size_ofFn]; exact hn
  have hws0 := hI.win.nullws hw
  have hws0n : st.wsize.toNat = 0 := by rw [hws0]; rfl
  have hA := Zlib.Zutil.Proofs.allocHeap_frame h ((1 <<< st.wbits : UInt32) * 1).toNat
  have hAb : (Zlib.Zutil.Proofs.allocHeap h ((1 <<< st.wbits : UInt32) * 1).toNat).bytes h.nextBlk = some A0 := by
    rw [hA0]; simp [Zlib.Zutil.Proofs.allocHeap]
  have hAro : (Zlib.Zutil.Proofs.allocHeap h ((1 <<< st.wbits : UInt32) * 1).toNat).ro h.nextBlk = false := by
    simp [Zlib.Zutil.Proofs.allocHeap]
  have hS : Shape (Zlib.Zutil.Proofs.allocHeap h ((1 <<< st.wbits : UInt32) * 1).toNat)
      (setI (Zlib.Zutil.Proofs.allocHeap h ((1 <<< st.wbits : UInt32) * 1).toNat) zs (withWin st h.nextBlk)) :=
    shape_setI (s0 := st) (by simpa [Zlib.Zutil.Proofs.allocHeap] using hL.hs) _
  have hUa := uniq_allocHeap hG.uniq hF ((1 <<< st.wbits : UInt32) * 1).toNat
  have hFa := hA.2.1 hF
  have hG2 : Good (setI (Zlib.Zutil.Proofs.allocHeap h ((1 <<< st.wbits : UInt32) * 1).toNat) zs (withWin st h.nextBlk))
      r zs z (withWin st h.nextBlk) := by
    refine ⟨⟨?_, by simp, hL.zst, hL.back, hL.mode, hL.zalloc, hL.zfree⟩, ?_, hS.uniq hUa, hS.fresh rfl hFa⟩
    · cases r <;> simpa [ZStreamRef.get, Zlib.Zutil.Proofs.allocHeap, setI] using hL.hz
    · refine ⟨hI.wf, ⟨hI.win.wbits, Or.inr ⟨h.nextBlk, A0, rfl, ?_, ?_, ?_⟩, fun h0 => absurd h0 (by simp [withWin]), ?_, ?_, ?_, ?_⟩,
        hI.reqbits, hI.bits, hI.ptr⟩
      · simpa [setI] using hAb
      · simpa [setI] using hAro
      · exact hA0sz
      · exact Or.inl hws0n
      · have := hI.win.hv; show st.whave.toNat ≤ st.wsize.toNat; exact this
      · right; refine ⟨hws0n, ?_⟩
        have := hI.win.wn; show st.wnext.toNat = 0; omega
      · intro hh; have := hI.win.hv; show st.wnext.toNat = st.whave.toNat; have := hI.win.wn; have := hI.win.hv
        change st.whave.toNat < st.wsize.toNat at hh; omega
  have hz2 : r.get (setI (Zlib.Zutil.Proofs.allocHeap h ((1 <<< st.wbits : UInt32) * 1).toNat) zs (withWin st h.nextBlk)) = some z :=
    hG2.live.hz
  have hbe : (setI (Zlib.Zutil.Proofs.allocHeap h ((1 <<< st.wbits : UInt32) * 1).toNat) zs (withWin st h.nextBlk)).bytes eb = some ebytes := by
    simp [Zlib.Zutil.Proofs.allocHeap, setI, upd_ne _ _ _ _ hne, heb]
  obtain ⟨H', st', hrun, -, hst', hG', hw', hb', hsz', hbo, hlive, hnb⟩ := uw_post (hG := hG2) (w := h.nextBlk) (eb := eb) (eo := eo)
    (a := A0) (ebytes := ebytes) (copy := copy) rfl (by simpa [setI] using hAb) (by simpa [setI] using hAro)
    (by exact hA0sz) hbe (Ne.symm hne) hc hoff
  refine ⟨H', st', hrun, hG', by rw [hw']; rfl, ⟨_, hb'⟩, ?_, ?_, ?_⟩
  · intro S hO
    have h2 := hS.owns (hA.1 S hO)
    exact fun b => (hlive b).trans (h2 b)
  · rw [hnb]; simp [Zlib.Zutil.Proofs.allocHeap, setI]
  · intro b hb; rw [hbo b (by exact hb)]; simp [Zlib.Zutil.Proofs.allocHeap, setI, upd_ne _ _ _ _ hb]

/-- **updatewindow, safety.** On a good stream with the default allocator, whose `copy` bytes end at offset `eo` of a
byte block `eb` that is not the window (`copy ≤ eo ≤ size`, the buffer `zlib.h` gives to `inflate`), the call never
faults. It returns 0 and the stream is good again (the window block exists afterwards; if it did not before, it is
the new block `h.nextBlk` and the stream owns it), or it returns 1 because the allocation of the window failed
(window absent, oracle says no): then only the allocation counter moved and the state is unchanged. -/
theorem updatewindow_safe {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState} {eb eo : Nat}
    {ebytes : Array UInt8} {copy : UInt32}
    (hG : Good h r zs z st) (hza : z.zalloc = .fn "zcalloc") (heb : h.bytes eb = some ebytes)
    (hc : copy.toNat ≤ eo) (hoff : eo ≤ ebytes.size) (hdisj : ∀ w, st.window = .ref (.blk w) 0 → eb ≠ w) :
    ∃ v h' st', C.run (updatewindow (some r) (.ref (.blk eb) eo) copy) h = .ok (v, h') ∧ Good h' r zs z st' ∧
      ((v = 0 ∧ st'.window ≠ .null ∧
          (∀ S, h.Owns S → h'.Owns (fun b => S b ∨ (st.window = .null ∧ b = h.nextBlk)))) ∨
       (v = 1 ∧ st.window = .null ∧ ¬ h.allocOk h.nalloc = true ∧ h' = setI { h with nalloc := h.nalloc + 1 } zs st ∧ st' = st)) := by
  have hL := hG.live
  have hI := hG.inv
  rcases hI.win.block with hw | ⟨w, a, hw, ha, hro, hasz⟩
  · by_cases hok : h.allocOk h.nalloc = true
    · obtain ⟨H', st', hrun, hG', hw', -, hO, -, -⟩ := uw_null_ok hG hza hw hok heb hc hoff
      refine ⟨0, H', st', hrun, hG', Or.inl ⟨0 |> fun _ => rfl, by rw [hw']; simp, ?_⟩⟩
      intro S hOw
      have := hO S hOw
      simpa [hw] using this
    · have hrun := uw_alloc_fail hL hza hI.win.wbits hw hok (.ref (.blk eb) eo) copy
      refine ⟨1, _, st, hrun, ?_, Or.inr ⟨rfl, hw, hok, rfl, rfl⟩⟩
      have hS : Shape h { h with nalloc := h.nalloc + 1 } := Shape.refl h
      have := good_set (h0 := { h with nalloc := h.nalloc + 1 }) (z0 := z) (z' := z) (s0 := st) (st' := st) hL.hz hL.hs
        hG.uniq hG.fresh hL.zst hL.zalloc hL.zfree hL.back hL.mode (StInv.congr (h := h) rfl rfl hI)
      have hz' : r.get { h with nalloc := h.nalloc + 1 } = some z := by cases r <;> simpa [ZStreamRef.get] using hL.hz
      rwa [ZStreamRef.put_self hz'] at this
  · obtain ⟨H', st', hrun, -, -, hG', hw', -, -, -, hlive, -⟩ := uw_post hG hw ha hro hasz heb (hdisj w hw).symm hc hoff
    refine ⟨0, H', st', hrun, hG', Or.inl ⟨rfl, by rw [hw', hw]; simp, ?_⟩⟩
    intro S hO b
    rw [hlive b, hO b]
    simp [hw]

end Zlib.Inflate.Proofs
