import ZlibF.Proof.«inflate.c.local-window-core»
import ZlibF.Proof.«inflate.c.window-state-frame»
import ZlibF.Proof.«inflate.c.window-platform»

/-! Exact actual window fields, source/table views and platform bounds with
only local typed uniqueness. Global caller-table collisions remain admitted. -/
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual fresh-window path preserves the platform byte-object bound.
The requested allocation and every ring copy have their real bounded size. -/
theorem uw_null_platform_local {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {st : InflateState} {eo : Nat} {source : BRef} {ebytes : Array UInt8} {copy : UInt32}
    (hG : LocalGood h cutoff r zs z st) (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (hza : z.zalloc = .fn "zcalloc") (hw : st.window = .null)
    (hok : h.allocOk h.nalloc = true) (heb : Space.get h source = some ebytes)
    (hc : copy.toNat ≤ eo) (hoff : eo ≤ ebytes.size) :
    ∃ after state, updatewindow (some r) (.ref source eo) copy h = .ok (0, after) ∧
      LocalGood after cutoff r zs z state ∧ ZlibF.PlatformMemory.ByteObjectsFit after ∧ after.static = h.static := by
  have hL := hG.live
  have hI := hG.inv
  have hF := hG.fresh
  have hne : source ≠ .blk h.nextBlk := by
    intro he
    subst source
    have hfresh := Fresh.bytes hF (b := h.nextBlk) (Nat.le_refl _)
    have hbytes : h.bytes h.nextBlk = some ebytes := by simpa using heb
    rw [hbytes] at hfresh
    cases hfresh
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
  have hUa := UniqueFrom.allocHeap hG.unique hF ((1 <<< st.wbits : UInt32) * 1).toNat
  have hFa := hA.2.1 hF
  have hG2 : LocalGood (setI (Zlib.Zutil.Proofs.allocHeap h ((1 <<< st.wbits : UInt32) * 1).toNat) zs (withWin st h.nextBlk))
      cutoff r zs z (withWin st h.nextBlk) := by
    refine ⟨⟨?_, by simp, hL.zst, hL.back, hL.mode, hL.zalloc, hL.zfree⟩, ?_, hS.fresh rfl hFa, hUa.of_shape hS⟩
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
  have hbe : Space.get (setI (Zlib.Zutil.Proofs.allocHeap h ((1 <<< st.wbits : UInt32) * 1).toNat) zs
      (withWin st h.nextBlk)) source = some ebytes := by
    cases source with
    | blk b =>
      have hbn : b ≠ h.nextBlk := fun he => hne (by cases he; rfl)
      simpa [Space.get, Zlib.Zutil.Proofs.allocHeap, setI, upd_ne _ _ _ _ hbn] using heb
    | str b => simpa [Space.get, staticStringBytes, Zlib.Zutil.Proofs.allocHeap, setI] using heb
    | st_dist_code => simpa [Space.get, Zlib.Zutil.Proofs.allocHeap, setI] using heb
    | st_length_code => simpa [Space.get, Zlib.Zutil.Proofs.allocHeap, setI] using heb
    | dstate_depth b => simpa [Space.get, Zlib.Zutil.Proofs.allocHeap, setI] using heb
  have hsep : ZlibF.Spec.Public.Separate (.ref source (eo - copy.toNat)) copy.toNat
      (withWin st h.nextBlk).window (2 ^ (withWin st h.nextBlk).wbits.toNat) := by
    simp [ZlibF.Spec.Public.Separate, withWin, hne]
  obtain ⟨after, state, hr, heapEq, hstate, hgood, _, _, _, _, _, _⟩ :=
    uw_post_local (hG := hG2) (w := h.nextBlk) (source := source) (eo := eo)
      (a := A0) (ebytes := ebytes) (copy := copy) rfl (by simpa [setI] using hAb)
      (by simpa [setI] using hAro) hA0sz hbe hc hoff hsep
  have allocated : ZlibF.PlatformMemory.ByteObjectsFit
      (Zlib.Zutil.Proofs.allocHeap h ((1 <<< st.wbits : UInt32) * 1).toNat) :=
    platform.zcalloc (Zlib.Zutil.Proofs.zcalloc_ok_run h z.opaque (1 <<< st.wbits) 1 hok hF)
  have powerBound := Nat.pow_le_pow_right (by decide : 0 < 2) hI.win.wbits
  have arrayBound : (uwPost (initWinS (withWin st h.nextBlk)) A0 ebytes eo copy).1.size <
      ZlibF.PlatformMemory.byteObjectLimit := by
    rw [uwPost_size, hA0sz]
    unfold ZlibF.PlatformMemory.byteObjectLimit
    omega
  refine ⟨after, state, hr, hgood, ?_, ?_⟩
  · rw [heapEq]
    exact ((allocated.with_istates _).with_bytes (block := h.nextBlk) arrayBound).with_istates _
  · rw [heapEq]
    rfl

/-- Every actual window update preserves the byte-object platform scope.
Existing-window copying, fresh allocation and genuine allocation failure
are all covered. No allocator size contract is assumed. -/
theorem updatewindow_platform_local {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} {eo : Nat} {source : BRef} {bytes : Array UInt8} {copy : UInt32} {rc : Int32}
    (good : LocalGood h cutoff r zs z s) (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (allocator : z.zalloc = .fn "zcalloc") (get : Space.get h source = some bytes)
    (count : copy.toNat ≤ eo) (bound : eo ≤ bytes.size)
    (separate : Separate (.ref source (eo - copy.toNat)) copy.toNat s.window (2 ^ s.wbits.toNat))
    (run : updatewindow (some r) (.ref source eo) copy h = .ok (rc, after)) :
    ZlibF.PlatformMemory.ByteObjectsFit after ∧ after.static = h.static := by
  rcases good.inv.win.block with window | ⟨w, a, window, array, ro, size⟩
  · by_cases alloc : h.allocOk h.nalloc = true
    · obtain ⟨result, state, executed, nextGood, fit, static⟩ :=
        uw_null_platform_local good platform allocator window alloc get count bound
      have same : after = result := congrArg Prod.snd (Except.ok.inj (run.symm.trans executed))
      simpa only [same] using And.intro fit static
    · have executed := uw_alloc_fail good.live allocator good.inv.win.wbits window alloc (.ref source eo) copy
      have same : after = setI { h with nalloc := h.nalloc + 1 } zs s :=
        congrArg Prod.snd (Except.ok.inj (run.symm.trans executed))
      rw [same]
      exact ⟨platform.of_storage_eq rfl rfl rfl, rfl⟩
  · obtain ⟨result, state, executed, heapEq, value, nextGood, rest⟩ :=
      uw_post_local good window array ro size get count bound separate
    have same : after = result := congrArg Prod.snd (Except.ok.inj (run.symm.trans executed))
    rw [same, heapEq]
    have arrayBound : (uwPost (initWinS s) a bytes eo copy).1.size < ZlibF.PlatformMemory.byteObjectLimit := by
      rw [uwPost_size]
      exact platform (BRef.blk w) a array
    exact ⟨((platform.with_istates _).with_bytes (block := w) arrayBound).with_istates _, rfl⟩


#print axioms uw_null_platform_local
#print axioms updatewindow_platform_local
end Zlib.Inflate.Local
