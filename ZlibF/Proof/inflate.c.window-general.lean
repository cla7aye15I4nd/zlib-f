import ZlibF.Proof.«inflate.c.uw»
import ZlibF.Proof.«inflate.c.ring»
import ZlibF.Spec.Public.Memory

/-! General readable sources for the full-window update path. -/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec

/-- Equal source slices produce the same destination for a byte copy. -/
theorem copyRange_source_agree (dest left right : Array UInt8) (doff soff n : Nat)
    (hagree : ∀ j, j < n → left[soff + j]! = right[soff + j]!) :
    copyRange dest left doff soff n = copyRange dest right doff soff n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [copyRange_succ, copyRange_succ, ih (fun j hj => hagree j (by omega)), hagree n (by omega)]

/-- A write does not change a disjoint range of the same array. -/
theorem copyRange_read_disjoint (dest source : Array UInt8) (doff soff n read count : Nat)
    (hd : doff + n ≤ dest.size) (hs : soff + n ≤ source.size)
    (hr : read + count ≤ dest.size)
    (hdis : doff + n ≤ read ∨ read + count ≤ doff) :
    ∀ j, j < count → (copyRange dest source doff soff n)[read + j]! = dest[read + j]! := by
  intro j hj
  have he := copyRange_bang dest source doff soff n hd hs (read + j) (by omega)
  have hout : ¬ (doff ≤ read + j ∧ read + j < doff + n) := by omega
  simpa [hout] using he

/-- If the next source slice is outside the first write, a second copy from
the updated allocation has the same result as a copy from the original bytes. -/
theorem copyRange_second_source_disjoint (dest source : Array UInt8)
    (doff soff n doff2 soff2 n2 : Nat)
    (hd : doff + n ≤ dest.size) (hs : soff + n ≤ source.size)
    (hr : soff2 + n2 ≤ dest.size)
    (hdis : doff + n ≤ soff2 ∨ soff2 + n2 ≤ doff) :
    let mid := copyRange dest source doff soff n
    copyRange mid mid doff2 soff2 n2 = copyRange mid dest doff2 soff2 n2 := by
  apply copyRange_source_agree
  exact copyRange_read_disjoint dest source doff soff n soff2 n2 hd hs hr hdis

/-- Updating one byte block leaves every other represented source unchanged;
the source becomes the updated block when it is the same allocation. -/
theorem window_write_source {h : Heap} {w : Nat} {source : BRef} {bytes : Array UInt8}
    (hs : Space.get h source = some bytes) (updated : Array UInt8) :
    Space.get { h with bytes := upd h.bytes w (some updated) } source =
      some (if source = .blk w then updated else bytes) := by
  cases source with
  | blk b =>
    by_cases he : b = w
    · subst b
      simp [Space.get]
    · have hb : h.bytes b = some bytes := hs
      simp [Space.get, he, upd_ne _ _ _ _ he, hb]
  | str b =>
    have same := C.LibcBorrow.str_view_stable
      (before := h) (after := { h with bytes := upd h.bytes w (some updated) })
      (i := b) (Or.inr rfl)
    simpa only [reduceCtorEq, ite_false] using same.trans hs
  | st_dist_code => simpa [Space.get] using hs
  | st_length_code => simpa [Space.get] using hs
  | dstate_depth b => simpa [Space.get] using hs

/-- The public separation of the complete input from the window implies
separation of the final window-sized suffix used by the full-copy branch. -/
theorem uw_big_public_separation {w eo : Nat} {source : BRef} {size copy : UInt32}
    (hfit : copy.toNat ≤ eo) (hbig : size ≤ copy)
    (hsep : ZlibF.Spec.Public.Separate (.ref source (eo - copy.toNat)) copy.toNat
      (.ref (.blk w) 0) size.toNat) :
    BRef.blk w ≠ source ∨ size.toNat ≤ eo - size.toNat ∨ eo ≤ 0 := by
  have hsize : size.toNat ≤ copy.toNat := UInt32.le_iff_toNat_le.mp hbig
  simp only [ZlibF.Spec.Public.Separate] at hsep
  rcases hsep with hzero | hzero | hne | hleft | hright
  · right; left; omega
  · right; left; omega
  · left; exact Ne.symm hne
  · right; right; omega
  · right; left; omega

/-- `updatewindow` with a full-window copy reads any represented byte object.
The source and destination may be disjoint ranges of the same object. -/
theorem uw_core_big_any {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {st : InflateState} {w eo : Nat} {source : BRef} {a bytes : Array UInt8} {copy : UInt32}
    (hl : Live h r zs z st) (hw : st.window = .ref (.blk w) 0)
    (ha : h.bytes w = some a) (hro : h.ro w = false)
    (hpos : st.wsize ≠ 0) (hsz : st.wsize.toNat ≤ a.size)
    (hs : Space.get h source = some bytes) (hc : st.wsize.toNat ≤ eo) (hoff : eo ≤ bytes.size)
    (hsep : BRef.blk w ≠ source ∨ st.wsize.toNat ≤ eo - st.wsize.toNat ∨ eo ≤ 0)
    (hbig : st.wsize ≤ copy) :
    updatewindow (some r) (.ref source eo) copy h = .ok (0, setI
      { h with bytes := upd h.bytes w (some (copyRange a bytes 0 (eo - st.wsize.toNat) st.wsize.toNat)) } zs
      { st with wnext := 0, whave := st.wsize }) := by
  have hwn : (st.window == Ptr.null) = false := by rw [hw]; simp
  have hws0 : (st.wsize == 0) = false := by simpa using hpos
  have hsub : Ptr.add (Ptr.ref source eo) (-(st.wsize.toNat : Int)) h =
      .ok (Ptr.ref source (eo - st.wsize.toNat), h) := Ptr.sub_nat_ok hs hc hoff
  have hcp := Ptr.memcpy_ok (rd := BRef.blk w) (rs := source) (od := 0)
    (os := eo - st.wsize.toNat) (n := st.wsize.toNat) (da := a) (sa := bytes)
    (by simpa using ha) hs (by simpa using hro) (by omega) (by omega) (by
      rcases hsep with hne | hafter | hbefore
      · exact Or.inl hne
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (by omega)))
  have hcp' : memcpyB (.ref (.blk w) 0) (.ref source (eo - st.wsize.toNat)) st.wsize.toNat h =
      .ok ((), { h with bytes := upd h.bytes w (some (copyRange a bytes 0 (eo - st.wsize.toNat) st.wsize.toNat)) }) := by
    simpa [Space.put] using hcp
  unfold updatewindow
  simp only [bind_app, pure_app, ldI_eq, ldZ_eq, wrI_eq, hl.hz, hl.zst, castI, hl.hs,
    hwn, hws0, Bool.false_eq_true, ite_false]
  simp only [ge_iff_le, hbig, ite_true, bind_app, hw, hsub]
  simp only [hcp', wrI_eq, pure_app, hl.hs, hw]

/-- The full-copy branch under the unchanged public separation condition. -/
theorem uw_core_big_public {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {st : InflateState} {w eo : Nat} {source : BRef} {a bytes : Array UInt8} {copy : UInt32}
    (hl : Live h r zs z st) (hw : st.window = .ref (.blk w) 0)
    (ha : h.bytes w = some a) (hro : h.ro w = false)
    (hpos : st.wsize ≠ 0) (hsz : st.wsize.toNat ≤ a.size)
    (hs : Space.get h source = some bytes) (hfit : copy.toNat ≤ eo) (hoff : eo ≤ bytes.size)
    (hsep : ZlibF.Spec.Public.Separate (.ref source (eo - copy.toNat)) copy.toNat
      st.window st.wsize.toNat) (hbig : st.wsize ≤ copy) :
    updatewindow (some r) (.ref source eo) copy h = .ok (0, setI
      { h with bytes := upd h.bytes w (some (copyRange a bytes 0 (eo - st.wsize.toNat) st.wsize.toNat)) } zs
      { st with wnext := 0, whave := st.wsize }) := by
  have hsize : st.wsize.toNat ≤ copy.toNat := UInt32.le_iff_toNat_le.mp hbig
  apply uw_core_big_any hl hw ha hro hpos hsz hs (by omega) hoff
  · apply uw_big_public_separation hfit hbig
    simpa only [hw] using hsep
  · exact hbig

/-- Public input/window separation implies separation of any fitting single
copy into the initialized window, including the zero-length case. -/
theorem uw_small_public_separation {w eo wn size copy : Nat} {source : BRef}
    (hfit : copy ≤ eo) (hwindow : wn + copy ≤ size)
    (hsep : ZlibF.Spec.Public.Separate (.ref source (eo - copy)) copy (.ref (.blk w) 0) size) :
    BRef.blk w ≠ source ∨ wn + copy ≤ eo - copy ∨ (eo - copy) + copy ≤ wn := by
  simp only [ZlibF.Spec.Public.Separate] at hsep
  rcases hsep with hzero | hzero | hne | hleft | hright
  · right; omega
  · right; omega
  · exact Or.inl hne.symm
  · right; right; omega
  · right; left; omega

/-- `updatewindow` copies a short source that fits before the window end.
The source may be any represented byte object, including a disjoint slice
of the window allocation itself. -/
theorem uw_core_small1_public {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {st : InflateState} {w eo : Nat} {source : BRef} {a bytes : Array UInt8} {copy : UInt32}
    (hl : Live h r zs z st) (hw : st.window = .ref (.blk w) 0)
    (ha : h.bytes w = some a) (hro : h.ro w = false)
    (hpos : st.wsize ≠ 0) (hsz : st.wsize.toNat ≤ a.size)
    (hwn : st.wnext.toNat < st.wsize.toNat) (hs : Space.get h source = some bytes)
    (hfit : copy.toNat ≤ eo) (hoff : eo ≤ bytes.size)
    (hsep : ZlibF.Spec.Public.Separate (.ref source (eo - copy.toNat)) copy.toNat
      st.window st.wsize.toNat)
    (hlt : ¬ st.wsize ≤ copy) (hp : st.wsize - st.wnext > copy) :
    updatewindow (some r) (.ref source eo) copy h = .ok (0, setI
      { h with bytes := upd h.bytes w (some (copyRange a bytes st.wnext.toNat (eo - copy.toNat) copy.toNat)) } zs
      { st with wnext := if st.wnext + copy == st.wsize then 0 else st.wnext + copy,
                whave := if st.whave < st.wsize then st.whave + copy else st.whave }) := by
  have hwnl : (st.window == Ptr.null) = false := by rw [hw]; simp
  have hws0 : (st.wsize == 0) = false := by simpa using hpos
  have hpn : copy.toNat < st.wsize.toNat - st.wnext.toNat := by
    have he := UInt32.lt_iff_toNat_lt.mp hp
    rwa [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; omega)] at he
  have hadd : Ptr.add (Ptr.ref (BRef.blk w) 0) (st.wnext.toNat : Int) h =
      .ok (Ptr.ref (BRef.blk w) st.wnext.toNat, h) := by
    have he := Ptr.add_nat_ok (a := a) (r := BRef.blk w) (off := 0) (n := st.wnext.toNat)
      (by simpa using ha) (by omega)
    unfold OkOn at he
    simpa using he
  have hsub : Ptr.add (Ptr.ref source eo) (-(copy.toNat : Int)) h =
      .ok (Ptr.ref source (eo - copy.toNat), h) := Ptr.sub_nat_ok hs hfit hoff
  have hdis := uw_small_public_separation (source := source) (w := w) (wn := st.wnext.toNat)
    (size := st.wsize.toNat) (copy := copy.toNat) (eo := eo)
    hfit (by omega) (by simpa only [hw] using hsep)
  have hcp := Ptr.memcpy_ok (rd := BRef.blk w) (rs := source) (od := st.wnext.toNat)
    (os := eo - copy.toNat) (n := copy.toNat) (da := a) (sa := bytes)
    (by simpa using ha) hs (by simpa using hro) (by omega) (by omega) hdis
  have hcp' : memcpyB (.ref (.blk w) st.wnext.toNat) (.ref source (eo - copy.toNat)) copy.toNat h =
      .ok ((), { h with bytes := upd h.bytes w (some (copyRange a bytes st.wnext.toNat (eo - copy.toNat) copy.toNat)) }) := by
    simpa [Space.put] using hcp
  unfold updatewindow
  simp only [bind_app, pure_app, ldI_eq, ldZ_eq, hl.hz, hl.zst, castI, hl.hs, hwnl, hws0,
    Bool.false_eq_true, ite_false]
  simp only [ge_iff_le, hlt, ite_false, hp, ite_true, bind_app, hw, hadd, hsub,
    UInt32.sub_self, bne_self_eq_false, Bool.false_eq_true]
  simp only [hcp', wrI_eq, pure_app, hl.hs]
  by_cases c1 : st.wnext + copy = st.wsize <;> by_cases c2 : st.whave < st.wsize <;>
    simp [c1, c2, wrI_eq, hl.hs, setI, hw]

/-- `updatewindow` copies a short source ending exactly at the window end.
The public separation condition permits any readable object, including a
disjoint slice in the window allocation. -/
theorem uw_core_small3_public {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {st : InflateState} {w eo : Nat} {source : BRef} {a bytes : Array UInt8} {copy : UInt32}
    (hl : Live h r zs z st) (hw : st.window = .ref (.blk w) 0)
    (ha : h.bytes w = some a) (hro : h.ro w = false)
    (hpos : st.wsize ≠ 0) (hsz : st.wsize.toNat ≤ a.size)
    (hwn : st.wnext.toNat < st.wsize.toNat) (hs : Space.get h source = some bytes)
    (hfit : copy.toNat ≤ eo) (hoff : eo ≤ bytes.size)
    (hsep : ZlibF.Spec.Public.Separate (.ref source (eo - copy.toNat)) copy.toNat
      st.window st.wsize.toNat)
    (hlt : ¬ st.wsize ≤ copy) (hq : ¬ st.wsize - st.wnext > copy)
    (hr : copy - (st.wsize - st.wnext) = 0) :
    updatewindow (some r) (.ref source eo) copy h = .ok (0, setI
      { h with bytes := upd h.bytes w (some (copyRange a bytes st.wnext.toNat (eo - copy.toNat)
        (st.wsize - st.wnext).toNat)) } zs
      { st with wnext := 0, whave := if st.whave < st.wsize then st.whave + (st.wsize - st.wnext) else st.whave }) := by
  have hwnl : (st.window == Ptr.null) = false := by rw [hw]; simp
  have hws0 : (st.wsize == 0) = false := by simpa using hpos
  have hd : (st.wsize - st.wnext).toNat = st.wsize.toNat - st.wnext.toNat :=
    UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; omega)
  have hqn : st.wsize.toNat - st.wnext.toNat ≤ copy.toNat := by
    have he : ¬ copy < st.wsize - st.wnext := hq
    rw [UInt32.lt_iff_toNat_lt, hd] at he
    omega
  have hrn : copy.toNat = st.wsize.toNat - st.wnext.toNat := by
    have he : (copy - (st.wsize - st.wnext)).toNat = 0 := by rw [hr]; rfl
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, hd]; omega), hd] at he
    omega
  have hcopy : copy = st.wsize - st.wnext := by
    apply UInt32.toNat_inj.mp
    rw [hd]
    exact hrn
  have hsum : st.wnext + (st.wsize - st.wnext) = st.wsize := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_add, hd]
    have := st.wsize.toNat_lt
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hadd : Ptr.add (Ptr.ref (BRef.blk w) 0) (st.wnext.toNat : Int) h =
      .ok (Ptr.ref (BRef.blk w) st.wnext.toNat, h) := by
    have he := Ptr.add_nat_ok (a := a) (r := BRef.blk w) (off := 0) (n := st.wnext.toNat)
      (by simpa using ha) (by omega)
    unfold OkOn at he
    simpa using he
  have hsub : Ptr.add (Ptr.ref source eo) (-(copy.toNat : Int)) h =
      .ok (Ptr.ref source (eo - copy.toNat), h) := Ptr.sub_nat_ok hs hfit hoff
  have hdis := uw_small_public_separation (source := source) (w := w) (wn := st.wnext.toNat)
    (size := st.wsize.toNat) (copy := copy.toNat) (eo := eo)
    hfit (by omega) (by simpa only [hw] using hsep)
  have hcp := Ptr.memcpy_ok (rd := BRef.blk w) (rs := source) (od := st.wnext.toNat)
    (os := eo - copy.toNat) (n := copy.toNat) (da := a) (sa := bytes)
    (by simpa using ha) hs (by simpa using hro) (by omega) (by omega) hdis
  have hcp' : memcpyB (.ref (.blk w) st.wnext.toNat) (.ref source (eo - copy.toNat))
      (st.wsize - st.wnext).toNat h =
      .ok ((), { h with bytes := upd h.bytes w (some (copyRange a bytes st.wnext.toNat (eo - copy.toNat)
        (st.wsize - st.wnext).toNat)) }) := by
    simpa [Space.put, ← hcopy] using hcp
  unfold updatewindow
  simp only [bind_app, pure_app, ldI_eq, ldZ_eq, hl.hz, hl.zst, castI, hl.hs, hwnl, hws0,
    Bool.false_eq_true, ite_false]
  simp only [ge_iff_le, hlt, ite_false, hq, bind_app, hw, hadd, hsub, hcp', hr,
    bne_self_eq_false, Bool.false_eq_true]
  by_cases hwh : st.whave < st.wsize <;> simp [hwh, wrI_eq, hl.hs, setI, hw, hsum]

/-- A positive source range separated from a nonempty window either belongs
to another object or begins beyond the window. -/
theorem uw_positive_public_separation {w eo size copy : Nat} {source : BRef}
    (hfit : copy ≤ eo) (hc : 0 < copy) (hs : 0 < size)
    (hsep : ZlibF.Spec.Public.Separate (.ref source (eo - copy)) copy (.ref (.blk w) 0) size) :
    BRef.blk w ≠ source ∨ size ≤ eo - copy := by
  simp only [ZlibF.Spec.Public.Separate] at hsep
  rcases hsep with h | h | h | h | h
  · omega
  · omega
  · exact Or.inl h.symm
  · omega
  · exact Or.inr (by omega)

/-- `updatewindow` wraps a short copy into two segments under the public
separation condition, including distinct slices of the same allocation. -/
theorem uw_core_small2_public {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {st : InflateState} {w eo : Nat} {source : BRef} {a bytes : Array UInt8} {copy : UInt32}
    (hl : Live h r zs z st) (hw : st.window = .ref (.blk w) 0)
    (ha : h.bytes w = some a) (hro : h.ro w = false)
    (hpos : st.wsize ≠ 0) (hsz : st.wsize.toNat ≤ a.size)
    (hwn : st.wnext.toNat < st.wsize.toNat) (hs : Space.get h source = some bytes)
    (hfit : copy.toNat ≤ eo) (hoff : eo ≤ bytes.size)
    (hsep : ZlibF.Spec.Public.Separate (.ref source (eo - copy.toNat)) copy.toNat
      st.window st.wsize.toNat)
    (hlt : ¬ st.wsize ≤ copy) (hq : ¬ st.wsize - st.wnext > copy)
    (hr : copy - (st.wsize - st.wnext) ≠ 0) :
    updatewindow (some r) (.ref source eo) copy h = .ok (0, setI
      { h with bytes := upd h.bytes w (some (copyRange
        (copyRange a bytes st.wnext.toNat (eo - copy.toNat) (st.wsize - st.wnext).toNat)
        bytes 0 (eo - (copy - (st.wsize - st.wnext)).toNat)
        (copy - (st.wsize - st.wnext)).toNat)) } zs
      { st with wnext := copy - (st.wsize - st.wnext), whave := st.wsize }) := by
  have hwnl : (st.window == Ptr.null) = false := by rw [hw]; simp
  have hws0 : (st.wsize == 0) = false := by simpa using hpos
  have hd : (st.wsize - st.wnext).toNat = st.wsize.toNat - st.wnext.toNat :=
    UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; omega)
  have hqn : st.wsize.toNat - st.wnext.toNat ≤ copy.toNat := by
    have he : ¬ copy < st.wsize - st.wnext := hq
    rw [UInt32.lt_iff_toNat_lt, hd] at he
    omega
  have hrem : (copy - (st.wsize - st.wnext)).toNat =
      copy.toNat - (st.wsize.toNat - st.wnext.toNat) := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, hd]; omega), hd]
  have hlt' : copy.toNat < st.wsize.toNat := by
    have he : ¬ st.wsize ≤ copy := hlt
    rw [UInt32.le_iff_toNat_le] at he
    omega
  have hrempos : 0 < (copy - (st.wsize - st.wnext)).toNat := by
    have he : (copy - (st.wsize - st.wnext)).toNat ≠ 0 :=
      fun hz => hr (UInt32.toNat_inj.mp (by simpa using hz))
    omega
  have hsizepos : 0 < st.wsize.toNat := by omega
  have hcopypos : 0 < copy.toNat := by omega
  have hdis := uw_positive_public_separation (source := source) (w := w) (eo := eo)
    (size := st.wsize.toNat) (copy := copy.toNat) hfit hcopypos hsizepos
    (by simpa only [hw] using hsep)
  have hadd : Ptr.add (Ptr.ref (BRef.blk w) 0) (st.wnext.toNat : Int) h =
      .ok (Ptr.ref (BRef.blk w) st.wnext.toNat, h) := by
    have he := Ptr.add_nat_ok (a := a) (r := BRef.blk w) (off := 0) (n := st.wnext.toNat)
      (by simpa using ha) (by omega)
    unfold OkOn at he
    simpa using he
  have hsub : Ptr.add (Ptr.ref source eo) (-(copy.toNat : Int)) h =
      .ok (Ptr.ref source (eo - copy.toNat), h) := Ptr.sub_nat_ok hs hfit hoff
  let first := copyRange a bytes st.wnext.toNat (eo - copy.toNat) (st.wsize - st.wnext).toNat
  let mid : Heap := { h with bytes := upd h.bytes w (some first) }
  have hcp1 : memcpyB (.ref (.blk w) st.wnext.toNat) (.ref source (eo - copy.toNat))
      (st.wsize - st.wnext).toNat h = .ok ((), mid) := by
    have he := Ptr.memcpy_ok (rd := BRef.blk w) (rs := source) (od := st.wnext.toNat)
      (os := eo - copy.toNat) (n := (st.wsize - st.wnext).toNat) (da := a) (sa := bytes)
      (by simpa using ha) hs (by simpa using hro) (by omega) (by omega) (by
        rcases hdis with hn | ha
        · exact Or.inl hn
        · exact Or.inr (Or.inl (by omega)))
    simpa [Space.put, mid, first] using he
  have hfirstsize : first.size = a.size := size_copyRange ..
  have hmidwin : Space.get mid (BRef.blk w) = some first := by simp [mid, Space.get]
  have hmidro : Space.ro mid (BRef.blk w) = false := by simpa [mid, Space.ro] using hro
  let secondsrc := if source = .blk w then first else bytes
  have hmidread : Space.get mid source = some secondsrc := by
    simpa [mid, secondsrc] using window_write_source hs first
  have hsrcsize : secondsrc.size = bytes.size := by
    by_cases he : source = .blk w
    · subst source
      have hab : bytes = a := Option.some.inj (hs.symm.trans (by simpa using ha))
      simp [secondsrc, hab, hfirstsize]
    · simp [secondsrc, he]
  have hsub2 : Ptr.add (Ptr.ref source eo) (-((copy - (st.wsize - st.wnext)).toNat : Int)) mid =
      .ok (Ptr.ref source (eo - (copy - (st.wsize - st.wnext)).toNat), mid) :=
    Ptr.sub_nat_ok hmidread (by omega) (by omega)
  have hcp2 : memcpyB (.ref (.blk w) 0) (.ref source (eo - (copy - (st.wsize - st.wnext)).toNat))
      (copy - (st.wsize - st.wnext)).toNat mid = .ok ((),
        { mid with bytes := upd mid.bytes w (some (copyRange first bytes 0
          (eo - (copy - (st.wsize - st.wnext)).toNat) (copy - (st.wsize - st.wnext)).toNat)) }) := by
    have he := Ptr.memcpy_ok (rd := BRef.blk w) (rs := source) (od := 0)
      (os := eo - (copy - (st.wsize - st.wnext)).toNat)
      (n := (copy - (st.wsize - st.wnext)).toNat) (da := first) (sa := secondsrc)
      hmidwin hmidread hmidro (by omega) (by omega) (by
        rcases hdis with hn | ha
        · exact Or.inl hn
        · exact Or.inr (Or.inl (by omega)))
    have heq : copyRange first secondsrc 0 (eo - (copy - (st.wsize - st.wnext)).toNat)
        (copy - (st.wsize - st.wnext)).toNat =
        copyRange first bytes 0 (eo - (copy - (st.wsize - st.wnext)).toNat)
          (copy - (st.wsize - st.wnext)).toNat := by
      by_cases heq : source = .blk w
      · subst source
        have hab : bytes = a := Option.some.inj (hs.symm.trans (by simpa using ha))
        subst bytes
        have hafter : st.wsize.toNat ≤ eo - copy.toNat := by
          rcases hdis with hn | hb
          · exact (hn rfl).elim
          · exact hb
        simpa [secondsrc, first] using
          copyRange_second_source_disjoint a a st.wnext.toNat (eo - copy.toNat)
            (st.wsize - st.wnext).toNat 0 (eo - (copy - (st.wsize - st.wnext)).toNat)
            (copy - (st.wsize - st.wnext)).toNat (by omega) (by omega) (by omega) (Or.inl (by omega))
      · simp [secondsrc, heq]
    simpa [Space.put, heq] using he
  unfold updatewindow
  simp only [bind_app, pure_app, ldI_eq, ldZ_eq, hl.hz, hl.zst, castI, hl.hs, hwnl, hws0,
    Bool.false_eq_true, ite_false]
  simp only [ge_iff_le, hlt, ite_false, hq, bind_app, hw, hadd, hsub, hcp1]
  have hr' : (copy - (st.wsize - st.wnext) != 0) = true := by simpa using hr
  simp only [hr', ite_true, bind_app, hsub2, hcp2, wrI_eq, pure_app, hl.hs, hw]
  simp [mid, first, setI, upd_upd, hl.hs, hw]

#print axioms uw_core_big_any
#print axioms uw_big_public_separation
#print axioms uw_core_big_public
#print axioms uw_small_public_separation
#print axioms uw_core_small1_public
#print axioms uw_core_small3_public
#print axioms copyRange_second_source_disjoint
#print axioms window_write_source
#print axioms uw_core_small2_public
end Zlib.Inflate.Proofs
