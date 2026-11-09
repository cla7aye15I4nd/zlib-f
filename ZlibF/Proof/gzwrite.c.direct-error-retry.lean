import ZlibF.Proof.«gzwrite.c.close-direct-cleanup»
import ZlibF.Proof.«gzwrite.c.direct-history-accounting»

/-! # Actual close-time retry of retained direct input

The earlier failed flush retains its input. gzclose_w tries the same actual
write again, then the same actual strerror/gz_error frees the old owned message
or handles NULL, and either copies a new message or records malloc refusal.
-/
namespace Zlib.Gzwrite.DirectClose
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzwrite Zlib.Gzlib.Spec Zlib.Gzlib.Proofs
open ZlibF.Spec.Public ZlibF.Spec.Public.OffsetProof Zlib.Gzlib.MessageHistory Zlib.Gzlib.MessagePrevious
open Zlib.Gzlib.ErrnoOwned

/-- Entire real direct compressor call on its retry error branch. This still
executes actual loadBytes, write, strerror, previous cleanup and message copy. -/
theorem gz_comp_retry_badfd_run {h : Heap} {i b off : Nat} {s : GzState} {a : Array UInt8} {xs : List UInt8}
    (hs : h.gzstates i = some s) (hsize : s.size ≠ 0) (hdir : s.direct ≠ 0)
    (n : UInt32) (hav : s.strm.avail_in = n) (hn : n ≠ 0) (hmax : n ≤ 1073741824)
    (hin : s.strm.next_in = .ref (.blk b) off) (ha : h.bytes b = some a)
    (hfit : off+n.toNat ≤ a.size) (fs : Fs)
    (hfd : s.fd < 0 ∨ (fs.fds.size : Int) ≤ s.fd.toInt)
    (hc : ClearableMessage h s) (hp : CString h s.path xs)
    (hpath : MallocBuffer h s.path (xs.length+1)) (sep : s.path ≠ s.msg) (hf : Fresh h)
    (hcap : h.allocOk h.nalloc = true → xs.length+(errnoCharacters EBADF).length+2 ≤ 2147483647) :
    gz_comp (some (.tab i)) Z_FINISH fs h =
      .ok ((-1,{fs with errno := EBADF}),replacementHeap (setS h i {s with again := 0})
        {fs with errno := EBADF} i {s with again := 0} xs) := by
  let prepared := setS h i {s with again := 0}
  have hs' : prepared.gzstates i = some {s with again := 0} := by simp [prepared]
  have hf' : Fresh prepared := Shape.fresh (shape_setS hs {s with again := 0}) rfl hf
  have hc' : ClearableMessage prepared {s with again := 0} := by
    simpa only [ClearableMessage,prepared,setS] using hc
  have hp' : CString prepared s.path xs := cstring_of_same_malloc_bytes hp hpath rfl
  have hpath' : MallocBuffer prepared s.path (xs.length+1) := hpath
  have handler := replacement_report_failure_run (fs := {fs with errno := EBADF})
    hs' hc' hp' hpath' sep hf' hcap
  rw [DirectErrno.gz_comp_direct_badfd_source hs hsize hdir n hav hn hmax hin ha hfit fs hfd Z_FINISH]
  exact handler

/-- Full actual writer close on the retained-input error path, including
previous-message release, either new message allocation outcome, and final
input/message/path/state cleanup despite a failed close syscall. -/
theorem gzclose_w_retry_badfd_run {h : Heap} {i b path : Nat} {s : GzState}
    {input pathBytes : Array UInt8} {xs : List UInt8}
    (hs : h.gzstates i = some s) (hm : s.mode = GZ_WRITE) (hskip : s.skip = 0)
    (hsize : s.size ≠ 0) (hdir : s.direct ≠ 0)
    (n : UInt32) (hav : s.strm.avail_in = n) (hn : n ≠ 0) (hmax : n ≤ 1073741824)
    (hin : s.«in» = .ref (.blk b) 0) (hnext : s.strm.next_in = .ref (.blk b) 0)
    (hb : h.bytes b = some input) (hro : h.ro b = false) (hfit : n.toNat ≤ input.size)
    (hp : s.path = .ref (.blk path) 0) (hbytesPath : h.bytes path = some pathBytes) (hroPath : h.ro path = false)
    (hbp : b ≠ path) (fs : Fs) (hfd : s.fd < 0 ∨ (fs.fds.size : Int) ≤ s.fd.toInt)
    (hc : ClearableMessage h s) (htext : CString h s.path xs)
    (hpath : MallocBuffer h s.path (xs.length+1)) (hpm : s.path ≠ s.msg)
    (him : s.«in» ≠ s.msg) (hf : Fresh h)
    (hcap : h.allocOk h.nalloc = true → xs.length+(errnoCharacters EBADF).length+2 ≤ 2147483647) :
    let prepared := setS h i {s with again := 0}
    let retried := replacementHeap prepared {fs with errno := EBADF} i {s with again := 0} xs
    let retryState := replacementState prepared {s with again := 0}
    gzclose_w (hnd i) fs h =
      .ok ((Z_ERRNO,{fs with errno := EBADF}),closedDirectHeap retried i retryState b path) := by
  dsimp only
  let prepared := setS h i {s with again := 0}
  let previous := {s with again := 0}
  let retried := replacementHeap prepared {fs with errno := EBADF} i previous xs
  let retryState := replacementState prepared previous
  have hsP : prepared.gzstates i = some previous := by simp [prepared,previous]
  have hfP : Fresh prepared := Shape.fresh (shape_setS hs previous) rfl hf
  have hcP : ClearableMessage prepared previous := by simpa only [ClearableMessage,prepared,previous,setS] using hc
  have comp := gz_comp_retry_badfd_run hs hsize hdir n hav hn hmax hnext hb
    (by simpa only [Nat.zero_add] using hfit) fs hfd hc htext hpath hpm hf hcap
  have observations := replacement_observations (fs := {fs with errno := EBADF}) (xs := xs) hsP hcP hfP
  have hsR : retried.gzstates i = some retryState := observations.1
  have hcR : ClearableMessage retried retryState := replacement_clearable hsP hcP hfP
  have fields := replacement_state_fields prepared previous
  have inputNe : .ref (.blk b) 0 ≠ previous.msg := fun eq => him (hin.trans eq)
  have pathNe : .ref (.blk path) 0 ≠ previous.msg := fun eq => hpm (hp.trans eq)
  have inputKeep := replacement_preserves_old_block (fs := {fs with errno := EBADF}) (xs := xs) hsP hcP hfP hb inputNe
  have pathKeep := replacement_preserves_old_block (fs := {fs with errno := EBADF}) (xs := xs) hsP hcP hfP hbytesPath pathNe
  have inR : retryState.«in» = .ref (.blk b) 0 := fields.2.2.2.2.2.1.trans hin
  have pathR : retryState.path = .ref (.blk path) 0 := fields.2.2.2.2.1.trans hp
  have inMsgR : retryState.«in» ≠ retryState.msg := by
    have ne := replacement_message_ne_old_block (s := previous) hfP hb
    intro eq
    exact ne (inR.symm.trans eq)
  have pathMsgR : retryState.path ≠ retryState.msg := by
    have ne := replacement_message_ne_old_block (s := previous) hfP hbytesPath
    intro eq
    exact ne (pathR.symm.trans eq)
  have sizeR : retryState.size ≠ 0 := fun eq => hsize (fields.2.2.1.symm.trans eq)
  have dirR : retryState.direct ≠ 0 := fun eq => hdir (fields.2.1.symm.trans eq)
  have fdR : retryState.fd < 0 ∨ (({fs with errno := EBADF} : Fs).fds.size : Int) ≤ retryState.fd.toInt := by
    rw [fields.2.2.2.2.2.2.1]
    exact hfd
  have cleanup := close_tail_badfd_run hsR sizeR dirR inR inputKeep.1 (inputKeep.2.trans hro)
    pathR pathKeep.1 (pathKeep.2.trans hroPath) hbp hcR inMsgR pathMsgR
    {fs with errno := EBADF} fdR retryState.err
  rw [gzclose_w_source hs hm hskip fs]
  dsimp only [prepared,previous,retried,retryState,Z_FINISH] at comp hsR cleanup
  unfold closeFromComp
  offsetsimp [comp,hsR,cleanup,Z_FINISH]

#print axioms gz_comp_retry_badfd_run
#print axioms gzclose_w_retry_badfd_run
end Zlib.Gzwrite.DirectClose
