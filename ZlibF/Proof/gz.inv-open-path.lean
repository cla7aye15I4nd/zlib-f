import ZlibF.Proof.«gz.inv-open»

/-!
# gzlib.c: the path copy for every path length, and the open tail of `gzopen`

`gz_open` copies the caller's path with `snprintf(state->path, len + 1, "%s", path)`. For a path longer than
`INT_MAX` the formatter still writes the whole path and its NUL into the `len + 1` bytes and returns -1
(`EOVERFLOW`); the result is ignored. `openPath_snprintf_any` and `openCopyPath_run_any` are
`openPath_snprintf_short` and `openCopyPath_run` without the `INT_MAX` bound. `openAfterPath_fresh` is the
source tail after the copy when `gz_open` opens the file itself (`fd = -1`), for every accepted mode and every
`e`, `N`, `x` flag.
-/

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec ZlibF.Spec.Public.OffsetProof
set_option autoImplicit false

/-- `snprintf(dest, len + 1, "%s", path)` for every length: the whole path and its NUL are written; the result is
the length, or -1 past `INT_MAX`. -/
theorem openPath_snprintf_any (h : Heap) (d : Nat) (dest : Array UInt8)
    (fmt path : BPtr) (xs : List UInt8)
    (hp : ZlibF.Spec.Public.CString h path xs)
    (hf : ZlibF.Spec.Public.CString h fmt [37, 115])
    (hd : h.bytes d = some dest) (hro : h.ro d = false)
    (hsize : dest.size = xs.length + 1) (hlen : xs.length + 1 < 2 ^ 64)
    (hslot : h.slotUsed h.nextBlk = false) :
    snprintf (.ref (.blk d) 0) (UInt64.ofNat (xs.length + 1)) fmt [.str path] h =
      .ok ((if xs.length > 2147483647 then -1 else Int32.ofNat xs.length),
        pathFormattedHeap h d dest xs.toArray) := by
  have hr := openPath_cstring_public h path xs hp
  have hfmt : cstring fmt h = .ok (#[37, 115], h) :=
    openPath_cstring_public h fmt [37, 115] hf
  have hnonnull : path ≠ .null := by
    intro he
    rw [he] at hr
    simp [cstring, strlenB, bind_app] at hr
  have hout := Zlib.GzFs.Proofs.formatBytes_s hnonnull hr
  have hn : d ≠ h.nextBlk := by
    intro he
    have hl : h.live d := Or.inl (by simp [hd])
    exact (Heap.slotUsed_eq_false.mp hslot) (he ▸ hl)
  have hcap : (UInt64.ofNat (xs.length + 1)).toNat = xs.length + 1 := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have hcapne : UInt64.ofNat (xs.length + 1) ≠ 0 := by
    intro he
    have hz := congrArg UInt64.toNat he
    rw [hcap] at hz
    change xs.length + 1 = 0 at hz
    omega
  have hcapB : (UInt64.ofNat (xs.length + 1) != 0) = true := by simpa using hcapne
  have hget := pathBytesHeap_dest h d dest xs.toArray hd hn
  have hreadonly : (pathBytesHeap h d dest xs.toArray).ro d = false := by
    rw [pathBytesHeap_ro h d dest xs.toArray hn]; exact hro
  have hadd := Ptr.add_nat_ok (off := 0) (n := xs.length) (r := BRef.blk d) hget
    (by simp [size_copyRange, hsize])
  simp only [OkOn, Nat.zero_add] at hadd
  have hstore := Ptr.store_ok (r := BRef.blk d) (off := xs.length) (v := (0 : UInt8))
    hget hreadonly (by simp [size_copyRange, hsize])
  have hdata : (copyRange dest xs.toArray 0 0 xs.length).setIfInBounds xs.length 0 =
      (xs ++ [0]).toArray := by
    simpa using pathCopy_then_nul dest xs.toArray (by simpa using hsize)
  unfold snprintf
  simp only [bind_app, hfmt, hout]
  simp only [List.size_toArray]
  have hextract : xs.toArray.extract 0 xs.length = xs.toArray := by simp
  simp only [hcapB, ite_true, hcap, Nat.add_sub_cancel, Nat.min_self, hextract, bind_app]
  rw [path_storeBytes h d dest xs.toArray hd hro (by simp [hsize]) hslot]
  simp only []
  rw [hadd]
  simp only []
  simp only [store8]
  rw [hstore]
  simp [pure_app, pathFormattedHeap, hdata]

/-- The path copy stage for every path whose allocation the allocator can serve. -/
theorem openCopyPath_run_any (h : Heap) (fs : Fs) (i : Nat) (s : GzState)
    (path : BPtr) (fd : Int32) (ml : ModeLoop) (name : List UInt8)
    (hs : h.gzstates i = some s) (hf : Fresh h)
    (hc : ZlibF.Spec.Public.CString h path name) (hlim : name.length + 1 < C.mallocLimit)
    (hok : h.allocOk h.nalloc = true) :
    openCopyPath (some (.tab i)) path fd ml fs h =
      openAfterPath (some (.tab i)) path fd ml fs (writerFormattedHeap h i s name) := by
  have hstr := openPath_strlen_public h path name hc
  have hlim' : name.length + 1 < 2 ^ 64 := by unfold C.mallocLimit at hlim; omega
  have hcap : UInt64.ofNat name.length + 1 = UInt64.ofNat (name.length + 1) := by
    exact (UInt64.ofNat_add _ _).symm
  have hcapNat : (UInt64.ofNat name.length + 1).toNat = name.length + 1 := by
    rw [hcap, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlim']
  have hmod : (name.length + 1) % 18446744073709551616 = name.length + 1 :=
    Nat.mod_eq_of_lt hlim'
  have hpfresh := pathAllocated_fresh h i s name.length hf hs
  have hp := pathAllocated_cstring h i s name.length path name hf hc
  obtain ⟨fmt, hliteral, hfmt⟩ := writer_format_literal (pathAllocatedHeap h i s name.length)
  have hbytes : (pathAllocatedHeap h i s name.length).bytes h.nextBlk =
      some (allocatedPathBytes h name.length) := by simp [pathAllocatedHeap]
  have hro : (pathAllocatedHeap h i s name.length).ro h.nextBlk = false := by
    simp [pathAllocatedHeap]
  have hformat := openPath_snprintf_any (pathAllocatedHeap h i s name.length) h.nextBlk
    (allocatedPathBytes h name.length) fmt path name hp hfmt hbytes hro
    (by simp [allocatedPathBytes]) hlim' (Fresh.slotUsed_next hpfresh)
  unfold openCopyPath
  offsetsimp [hs, hstr, hcapNat,
    allocB, hok, hlim, Fresh.slotUsed_next hf, setS, upd_upd, hmod]
  dsimp only [pathAllocatedHeap, allocatedPathBytes] at hliteral hformat
  simp only [Zlib.GzFs.strLit] at hliteral ⊢
  erw [hliteral]
  offsetsimp []
  rw [hcap]
  erw [hformat]
  simp only [writerFormattedHeap, pathAllocatedHeap, allocatedPathBytes]

/-- The two names of the `lseek` result (the offset proofs and the open proofs each define one) are one function. -/
theorem offset_lseekRes_eq_spec (fd : Int32) (off : Int64) (wh : Int32) (w : Fs) :
    ZlibF.Spec.Public.OffsetProof.lseekRes fd off wh w = Zlib.Gzlib.Spec.lseekRes fd off wh w := rfl

/-- The `open` flags `gz_open` computes for an accepted mode, from the `e`, `N` and `x` flags of the mode loop. -/
def freshFlags (ml : ModeLoop) : ZlibF.Spec.Api.GzMode → Int32
  | .read => ml.oflag ||| O_LARGEFILE
  | .write => ml.oflag ||| (O_LARGEFILE ||| (O_WRONLY ||| O_CREAT ||| (if ml.exclusive = 0 then 0 else O_EXCL) |||
      O_TRUNC))
  | .append => ml.oflag ||| (O_LARGEFILE ||| (O_WRONLY ||| O_CREAT ||| (if ml.exclusive = 0 then 0 else O_EXCL) |||
      O_APPEND))

/-- The source tail after the path copy when `gz_open` opens the file (`fd = -1`): a refused `open` frees the path
and the record; otherwise the start or end `lseek` and `gz_reset`, exactly as with a supplied descriptor. -/
theorem openAfterPath_fresh (h : Heap) (fs : Fs) (i pb : Nat) (s : GzState) (ml : ModeLoop) (path : BPtr)
    (mode : ZlibF.Spec.Api.GzMode) (name : List UInt8) (copy : Array UInt8)
    (hs : h.gzstates i = some s) (hm : s.mode = modeCode (some mode)) (hmsg : s.msg = .null)
    (hpath : ZlibF.Spec.Public.CString h path name)
    (hprivate : s.path = .ref (.blk pb) 0) (hcopy : h.bytes pb = some copy) (hro : h.ro pb = false) :
    openAfterPath (some (.tab i)) path (-1) ml fs h =
      if (openFsResult name.toArray (freshFlags ml mode) fs).1 = -1 then
        .ok ((none, (openFsResult name.toArray (freshFlags ml mode) fs).2),
          { h with bytes := upd h.bytes pb none, gzstates := upd h.gzstates i none })
      else
        .ok ((some (.in_gzstate_x i), suppliedWorld mode (openFsResult name.toArray (freshFlags ml mode) fs).1
            (openFsResult name.toArray (freshFlags ml mode) fs).2),
          setS h i (resetRec (suppliedRecord s mode (openFsResult name.toArray (freshFlags ml mode) fs).1
            (openFsResult name.toArray (freshFlags ml mode) fs).2))) := by
  have hname := openPath_cstring_public h path name hpath
  cases mode with
  | read =>
    by_cases hf : (openFsResult name.toArray (ml.oflag ||| O_LARGEFILE) fs).1 = -1
    · unfold openAfterPath
      offsetsimp [freshFlags, hs, hm, hname, openFs_eq, hf, hprivate, hcopy, hro, freeB, freeGzState,
        setS, upd_upd, modeCode, hnd, GZ_READ, GZ_WRITE, GZ_APPEND]
    · by_cases he : (Zlib.Gzlib.Spec.lseekRes (openFsResult name.toArray (ml.oflag ||| O_LARGEFILE) fs).1 0 SEEK_CUR
          (openFsResult name.toArray (ml.oflag ||| O_LARGEFILE) fs).2).1 = -1 <;>
        unfold openAfterPath <;>
        offsetsimp [freshFlags, hs, hm, hmsg, hname, openFs_eq, hf, offset_lseekRes_eq_spec, he, suppliedWorld,
          suppliedRecord, gz_reset, gz_error, resetRec, setS, upd_upd, modeCode, hnd, GZ_READ, GZ_WRITE, GZ_APPEND]
  | write =>
    by_cases hf : (openFsResult name.toArray (ml.oflag ||| (O_LARGEFILE ||| (O_WRONLY ||| O_CREAT |||
        (if ml.exclusive = 0 then 0 else O_EXCL) ||| O_TRUNC))) fs).1 = -1
    · unfold openAfterPath
      offsetsimp [freshFlags, hs, hm, hname, openFs_eq, hf, hprivate, hcopy, hro, freeB, freeGzState,
        setS, upd_upd, modeCode, hnd, GZ_READ, GZ_WRITE, GZ_APPEND]
    · unfold openAfterPath
      offsetsimp [freshFlags, hs, hm, hmsg, hname, openFs_eq, hf, suppliedWorld, suppliedRecord,
        gz_reset, gz_error, resetRec, setS, upd_upd, modeCode, hnd, GZ_READ, GZ_WRITE, GZ_APPEND]
  | append =>
    by_cases hf : (openFsResult name.toArray (ml.oflag ||| (O_LARGEFILE ||| (O_WRONLY ||| O_CREAT |||
        (if ml.exclusive = 0 then 0 else O_EXCL) ||| O_APPEND))) fs).1 = -1
    · unfold openAfterPath
      offsetsimp [freshFlags, hs, hm, hname, openFs_eq, hf, hprivate, hcopy, hro, freeB, freeGzState,
        setS, upd_upd, modeCode, hnd, GZ_READ, GZ_WRITE, GZ_APPEND]
    · unfold openAfterPath
      offsetsimp [freshFlags, hs, hm, hmsg, hname, openFs_eq, hf, suppliedWorld, suppliedRecord,
        gz_reset, gz_error, resetRec, setS, upd_upd, modeCode, hnd, GZ_READ, GZ_WRITE, GZ_APPEND]

#print axioms openPath_snprintf_any
#print axioms openCopyPath_run_any
#print axioms openAfterPath_fresh

end Zlib.Gzlib.Proofs
