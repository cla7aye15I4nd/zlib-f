import ZlibF.Proof.«public-gz-offset»
import ZlibF.Proof.«gzlib.c.errno-owned-run»
import ZlibF.Zlib.«gzwrite.c»

/-! # Actual transparent write-error source cut

A bounded positive buffered input reaches the real descriptor refusal and error
handler without a compressor call. The ordinary initialization/history producer
is separate; no caller contract for loadBytes or gz_error is assumed.
-/
namespace Zlib.Gzwrite.DirectErrno
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzwrite Zlib.Gzlib.Spec Zlib.Gzlib.Proofs
open ZlibF.Spec.Public.OffsetProof Zlib.Gzlib.ErrnoLifetime

/-- Bytes read in order by the translated `loadBytes` loop. -/
def readSlice (a : Array UInt8) (off n : Nat) : Array UInt8 :=
  (List.range' 0 n).foldl (fun out i => out.push a[off + i]!) #[]

private theorem loadList_run {h : Heap} {r : BRef} {a : Array UInt8} {off : Nat}
    (ha : Space.get h r = some a) (xs : List Nat)
    (hb : ∀ i ∈ xs, off + i < a.size) (out : Array UInt8) :
    (forIn' xs out (fun (i : Nat) _ (out : Array UInt8) => do
      let v ← index8 (.ref r off) (i : Int)
      pure (ForInStep.yield (out.push v)))) h =
      .ok (xs.foldl (fun out i => out.push a[off + i]!) out, h) := by
  induction xs generalizing out with
  | nil => rfl
  | cons i xs ih =>
    have hi := Ptr.index_ok ha (hb i (by simp))
    have hi' : index8 (.ref r off) i h = .ok (a[off + i]!, h) := by
      rw [getElem!_pos a (off + i) (hb i (by simp))]
      exact hi
    simp only [List.forIn'_cons, bind_app, hi', pure_app, List.foldl_cons]
    exact ih (fun j hj => hb j (by simp [hj])) _

/-- The actual byte-load loop is safe for a live readable interval, returns those
bytes in order, and leaves the entire heap unchanged. -/
theorem loadBytes_readSlice {h : Heap} {r : BRef} {a : Array UInt8} {off n : Nat}
    (ha : Space.get h r = some a) (hb : off + n ≤ a.size) :
    loadBytes (.ref r off) n h = .ok (readSlice a off n, h) := by
  unfold loadBytes
  simp only [forIn, Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size]
  have hr : ∀ i ∈ List.range' 0 n, off + i < a.size := by
    intro i hi
    simp only [List.mem_range'] at hi
    omega
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [bind_app, loadList_run ha _ hr]
  rfl

@[simp] theorem readSlice_size (a : Array UInt8) (off n : Nat) :
    (readSlice a off n).size = n := by
  simp [readSlice]


private theorem fsWrite_badfd (fs : Fs) (fd : Int32) (bs : Array UInt8) (h : Heap)
    (hfd : fd < 0 ∨ (fs.fds.size : Int) ≤ fd.toInt) :
    fsWrite fd bs fs h = .ok ((-1,{fs with errno := EBADF}),h) := by
  rcases hfd with hn | hs
  · simp [fsWrite,hn,pure_app]
  · simp [fsWrite,hs,pure_app]

def reportFailure (i : Nat) : G Int32 := do
  gz_error (some (.tab i)) Z_ERRNO (← zstrerror)
  return -1

/-- Exact full direct gz_comp error run up to its actual errno handler. -/
theorem gz_comp_direct_badfd_source {h : Heap} {i b off : Nat} {s : GzState} {a : Array UInt8}
    (hs : h.gzstates i = some s) (hsize : s.size ≠ 0) (hdir : s.direct ≠ 0)
    (n : UInt32) (hav : s.strm.avail_in = n) (hn : n ≠ 0) (hmax : n ≤ 1073741824)
    (hin : s.strm.next_in = .ref (.blk b) off) (ha : h.bytes b = some a)
    (hfit : off + n.toNat ≤ a.size) (fs : Fs)
    (hfd : s.fd < 0 ∨ (fs.fds.size : Int) ≤ s.fd.toInt) (flush : Int32) :
    gz_comp (some (.tab i)) flush fs h =
      reportFailure i {fs with errno := EBADF} (setS h i {s with again := 0}) := by
  let prepared := setS h i {s with again := 0}
  have hw := fsWrite_badfd {fs with errno := 0} s.fd (readSlice a off n.toNat) prepared hfd
  have hload : loadBytes (.ref (.blk b) off) n.toNat prepared =
      .ok (readSlice a off n.toNat,prepared) := loadBytes_readSlice ha hfit
  have hset (w : Fs) (hh : Heap) : setErrno 0 w hh = .ok (((),{w with errno := 0}),hh) := rfl
  have hget (w : Fs) (hh : Heap) : getErrno w hh = .ok ((w.errno,w),hh) := rfl
  have hmax' : ¬ (1073741824 : UInt32) < n := UInt32.not_lt.mpr hmax
  have hchunk : (((0 : UInt32) - 1) >>> 2) + 1 = 1073741824 := by decide
  have hchunk' : ((-1 : UInt32) >>> 2) + 1 = 1073741824 := by decide
  unfold gz_comp
  offsetsimp [hs,hsize,hdir,hchunk,hchunk']
  rw [gwhile]
  rw [show fuel = 18446744073709551615 + 1 by decide,gwhile.go]
  offsetsimp [hs,hav,hn,hin,hmax',hload,hset,hget,hw,prepared,EBADF,EAGAIN,BLOCKED,
    reportFailure,Zlib.GzFs.Proofs.zstrerror_run]
  cases he : gz_error (some (.tab i)) Z_ERRNO
      (errnoPointer prepared {fs with errno := EBADF}) (errnoHeap prepared {fs with errno := EBADF}) with
  | error e =>
    dsimp only [errnoPointer,errnoHeap,prepared,setS,EBADF] at he ⊢
    rw [he]
  | ok result =>
    rcases result with ⟨v,final⟩
    cases v
    dsimp only [errnoPointer,errnoHeap,prepared,setS,EBADF] at he ⊢
    rw [he]
    dsimp only
    rw [gwhile.go.eq_def]
    rfl

#print axioms loadBytes_readSlice
#print axioms gz_comp_direct_badfd_source
end Zlib.Gzwrite.DirectErrno
