import ZlibF.Proof.«deflate.c.base»
import ZlibF.Proof.«deflate.c.engine.macros»

/-!
# deflate.c: `deflateGetDictionary`

`deflateGetDictionary` copies the last `len = min(strstart + lookahead, w_size)` bytes of the history that the window
holds into the caller's buffer, and reports `len`. It never changes the stream or the state. The stream check refuses a
stream that is not initialised with `Z_STREAM_ERROR`.
-/

namespace Zlib.Deflate.Spec
open C

/-- The number of bytes `deflateGetDictionary` returns: the history in the window, `strstart + lookahead`, at most
`w_size` (the sum is in `unsigned`; for a state with `strstart + lookahead <= window_size <= 2^16` it does not wrap). -/
def dictLen (d : DeflateState) : UInt32 :=
  if d.strstart + d.lookahead > d.w_size then d.w_size else d.strstart + d.lookahead

/-- The caller's buffer can take the `n` bytes: it is a writable byte block with room for them at its offset, and the
range does not overlap the source range `[src, src + n)` of the window (the two may share a block only if the ranges are
disjoint, as `memcpy` requires). -/
def DictDest (h : Heap) (d : DeflateState) (src n : Nat) (dictionary : BPtr) : Prop :=
  ∃ x off da, dictionary = .ref (.blk x) off ∧ h.bytes x = some da ∧ h.ro x = false ∧ off + n ≤ da.size ∧
    ∀ w, d.window = .ref (.blk w) 0 → (x ≠ w ∨ off + n ≤ src ∨ src + n ≤ off)

end Zlib.Deflate.Spec

namespace Zlib.Deflate.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Engine.Proofs

theorem dictLen_toNat {d : DeflateState} (hw : d.window_size.toNat = 2 * d.w_size.toNat)
    (hws : d.w_size.toNat ≤ 32768) (hfill : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat) :
    (dictLen d).toNat = min (d.strstart.toNat + d.lookahead.toNat) d.w_size.toNat := by
  have hs : (d.strstart + d.lookahead).toNat = d.strstart.toNat + d.lookahead.toNat := by
    rw [UInt32.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  unfold dictLen
  by_cases hc : d.strstart + d.lookahead > d.w_size
  · simp only [hc, ite_true]
    have := UInt32.lt_iff_toNat_lt.mp hc
    omega
  · simp only [hc, ite_false]
    have : ¬ d.w_size.toNat < (d.strstart + d.lookahead).toNat := fun e => hc (UInt32.lt_iff_toNat_lt.mpr e)
    omega

theorem getdict_unfold {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (hL : DLive h r ds z d) (dictionary : BPtr) (hasDictLength : Bool) :
    deflateGetDictionary (some r) dictionary hasDictLength h =
      ((if dictionary != .null && dictLen d != 0 then
          (do let from_ ← padd (← padd d.window d.strstart.toNat) d.lookahead.toNat
              memcpyB dictionary (← psub from_ (dictLen d).toNat) (dictLen d).toNat
              pure (Z_OK, if hasDictLength then some (dictLen d) else none) : M (Int32 × Option UInt32))
        else pure (Z_OK, if hasDictLength then some (dictLen d) else none)) h) := by
  unfold deflateGetDictionary
  dsimp' [stateCheck_live hL, hL.zst, hL.hz, hL.hs, dictLen]
  split <;> split <;> simp_all

/-- No copy: the buffer is `NULL`, or the history is empty. -/
theorem deflateGetDictionary_run_nocopy {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (hL : DLive h r ds z d) (dictionary : BPtr) (hasDictLength : Bool)
    (hn : dictionary = .null ∨ dictLen d = 0) :
    deflateGetDictionary (some r) dictionary hasDictLength h =
      .ok ((Z_OK, if hasDictLength then some (dictLen d) else none), h) := by
  rw [getdict_unfold hL]
  have : ¬ (dictionary != .null && dictLen d != 0) = true := by
    rcases hn with e | e <;> simp [e]
  simp only [this]
  rfl

/-- A copy of `n = dictLen d` bytes into a good buffer. -/
theorem deflateGetDictionary_run_copy {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    {w p q b : Nat} (hL : DLive h r ds z d) (hB : DBlocks h d w p q b)
    (hfill : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (dictionary : BPtr) (hasDictLength : Bool) {x off : Nat} {da wa : Array UInt8}
    (hd : dictionary = .ref (.blk x) off) (hda : h.bytes x = some da) (hro : h.ro x = false)
    (hroom : off + (dictLen d).toNat ≤ da.size) (hwa : h.bytes w = some wa)
    (hlen : (dictLen d).toNat = min (d.strstart.toNat + d.lookahead.toNat) d.w_size.toNat)
    (hne : (dictLen d) ≠ 0)
    (hdis : x ≠ w ∨ off + (dictLen d).toNat ≤ d.strstart.toNat + d.lookahead.toNat - (dictLen d).toNat ∨
      d.strstart.toNat + d.lookahead.toNat - (dictLen d).toNat + (dictLen d).toNat ≤ off)
    (hwsz : wa.size = d.window_size.toNat) :
    deflateGetDictionary (some r) dictionary hasDictLength h =
      .ok ((Z_OK, if hasDictLength then some (dictLen d) else none),
        { h with bytes := upd h.bytes x (some (copyRange da wa off
          (d.strstart.toNat + d.lookahead.toNat - (dictLen d).toNat) (dictLen d).toNat)) }) := by
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
      (dictLen d).toNat h = .ok ((), { h with bytes := upd h.bytes x (some (copyRange da wa off
          (d.strstart.toNat + d.lookahead.toNat - (dictLen d).toNat) (dictLen d).toNat)) }) := by
    subst hd
    have := Ptr.memcpy_ok (rd := BRef.blk x) (rs := BRef.blk w) (od := off)
      (os := d.strstart.toNat + d.lookahead.toNat - (dictLen d).toNat) (n := (dictLen d).toNat) (da := da) (sa := wa)
      (by simpa using hda) (by simpa using hwa) (by simpa using hro) hroom (by omega)
      (by rcases hdis with e | e | e
          · exact Or.inl (fun hh => e (BRef.blk.inj hh))
          · exact Or.inr (Or.inl e)
          · exact Or.inr (Or.inr e))
    simpa using this
  simp only [bind_app, e1, e2, e3, e4, pure_app]


theorem getD_copyRange (da wa : Array UInt8) (off s n : Nat) (hfit : off + n ≤ da.size) (i : Nat) :
    (copyRange da wa off s n).getD i 0 = if off ≤ i ∧ i < off + n then wa.getD (s + (i - off)) 0 else da.getD i 0 := by
  rw [Array.getD_eq_getD_getElem?, getElem?_copyRange _ _ _ _ _ _ hfit]
  by_cases hi : off ≤ i ∧ i < off + n
  · simp [hi, Array.getD_eq_getD_getElem?, getElem!_def]
    split <;> simp_all <;> rfl
  · simp [hi, Array.getD_eq_getD_getElem?]

/-- **deflateGetDictionary, safety and specification.** On an initialised stream with the invariant (any stream state
reachable by the engine: `strstart + lookahead <= window_size`, the precondition `hfill`, which `deflateInit2_`,
`lm_init` and `fill_window` maintain) the call never faults and returns `Z_OK`. The length it reports (when the pointer
`dictLength` is not `NULL`, `hasDictLength`) is `min(strstart + lookahead, w_size)`; it copies that many bytes, the
last ones of the history `window[0 .. strstart + lookahead)`, to the caller's buffer `dictionary`; a `NULL` buffer
receives nothing. The buffer must be a writable byte block with room for them that overlaps the source range at most
if it lies in the window block outside it (`DictDest`); `zlib.h` says the buffer holds at least `w_size` bytes. The
stream and the state are unchanged; only the bytes of the buffer's block in `[off, off + len)` change, and no block is
allocated or freed. -/
theorem deflateGetDictionary_safe {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (hG : DGood h r ds z d) (hfill : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (dictionary : BPtr) (hasDictLength : Bool)
    (hdict : dictionary ≠ .null → dictLen d ≠ 0 →
      DictDest h d (d.strstart.toNat + d.lookahead.toNat - (dictLen d).toNat) (dictLen d).toNat dictionary) :
    ∃ h', C.run (deflateGetDictionary (some r) dictionary hasDictLength) h =
        .ok ((Z_OK, if hasDictLength then some (dictLen d) else none), h') ∧
      DGood h' r ds z d ∧
      (dictLen d).toNat = min (d.strstart.toNat + d.lookahead.toNat) d.w_size.toNat ∧
      h'.dstates = h.dstates ∧ h'.streams = h.streams ∧ h'.gzstates = h.gzstates ∧ h'.words = h.words ∧
      h'.ro = h.ro ∧ h'.gzheaders = h.gzheaders ∧ h'.istates = h.istates ∧ h'.nextBlk = h.nextBlk ∧
      h'.nalloc = h.nalloc ∧ h'.static = h.static ∧ h'.allocOk = h.allocOk ∧ h'.garbage = h.garbage ∧
      (∀ x, (∀ off, dictionary ≠ .ref (.blk x) off) → h'.bytes x = h.bytes x) ∧
      (∀ w wa, d.window = .ref (.blk w) 0 → h.bytes w = some wa → ∀ x off da, dictionary = .ref (.blk x) off →
        h.bytes x = some da → ∃ da', h'.bytes x = some da' ∧ da'.size = da.size ∧
          (∀ i, i < (dictLen d).toNat →
            da'.getD (off + i) 0 = wa.getD (d.strstart.toNat + d.lookahead.toNat - (dictLen d).toNat + i) 0) ∧
          (∀ i, (i < off ∨ off + (dictLen d).toNat ≤ i) → da'.getD i 0 = da.getD i 0)) := by
  obtain ⟨w, p, q, b, hB⟩ := hG.inv.blocks
  have hI := hG.inv
  obtain ⟨wa, hwa, hwsz⟩ := hB.wa
  have hws : d.w_size.toNat ≤ 32768 := by
    have := hI.wsize; have := hI.wbits_hi
    have : 2 ^ d.w_bits.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) hI.wbits_hi
    omega
  have hlen := dictLen_toNat hI.wsz hws hfill
  have hwsz' : wa.size = d.window_size.toNat := by have := hI.wsz; omega
  by_cases hn : dictionary = .null ∨ dictLen d = 0
  · refine ⟨h, ?_, hG, hlen, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, ?_⟩
    · rw [C.run]; exact deflateGetDictionary_run_nocopy hG.live dictionary hasDictLength hn
    · intro w' wa' hw' hwa' x off da hd hda
      refine ⟨da, hda, rfl, ?_, fun _ _ => rfl⟩
      intro i hi
      rcases hn with e | e
      · rw [e] at hd; cases hd
      · rw [e] at hi; simp at hi
  · have hnn : dictionary ≠ .null := fun e => hn (Or.inl e)
    have hne : dictLen d ≠ 0 := fun e => hn (Or.inr e)
    obtain ⟨x, off, da, hd, hda, hro, hroom, hdis⟩ := hdict hnn hne
    have hdis' := hdis w hB.win
    have hrun := deflateGetDictionary_run_copy hG.live hB hfill dictionary hasDictLength hd hda hro hroom hwa hlen hne
      hdis' hwsz'
    have hsz : (copyRange da wa off (d.strstart.toNat + d.lookahead.toNat - (dictLen d).toNat)
        (dictLen d).toNat).size = da.size := size_copyRange _ _ _ _ _
    refine ⟨_, by rw [C.run]; exact hrun, hG.bytes_set x _ da hda hsz, hlen, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, ?_, ?_⟩
    · intro y hy
      have hyx : y ≠ x := fun e => hy off (by rw [hd, e])
      simp [upd_apply, hyx]
    · intro w' wa' hw' hwa' x' off' da' hd' hda'
      rw [hd] at hd'
      cases hd'
      rw [hB.win] at hw'
      cases hw'
      rw [hwa] at hwa'
      cases hwa'
      rw [hda] at hda'
      cases hda'
      refine ⟨_, by simp, hsz, ?_, ?_⟩
      · intro i hi
        rw [getD_copyRange _ _ _ _ _ hroom]
        simp only [show off ≤ off + i ∧ off + i < off + (dictLen d).toNat by omega, and_self, ite_true]
        congr 2; omega
      · intro i hi
        rw [getD_copyRange _ _ _ _ _ hroom]
        have : ¬ (off ≤ i ∧ i < off + (dictLen d).toNat) := by omega
        simp only [this, ite_false]

/-- **deflateGetDictionary, refusal.** On a stream the check refuses (including `NULL`): `Z_STREAM_ERROR`, no length
stored, nothing changes. -/
theorem deflateGetDictionary_reject {h : Heap} {strm : ZStreamPtr} (hD : StreamDom h strm) (hN : ¬ DInitialised h strm)
    (dictionary : BPtr) (hasDictLength : Bool) :
    C.run (deflateGetDictionary strm dictionary hasDictLength) h = .ok ((Z_STREAM_ERROR, none), h) := by
  unfold deflateGetDictionary
  exact check_refuse hD hN _ _

end Zlib.Deflate.Proofs
