import ZlibF.Proof.«gzwrite.c.comp-errno-output»
import ZlibF.Proof.«gzlib.c.errno-owned-run»

/-! # Complete resources on compressed pending-output errno

The internal one-byte bad-descriptor branch reaches the actual error handler
before deflate. Its same execution now includes both allocation outcomes,
message copy and temporary cleanup. Initialized history and arbitrary output
lengths remain separate. The formatter bound is internal, not a public change.
-/
namespace Zlib.Gzwrite.CompErrnoOwned
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzwrite
open Zlib.Gzlib.Spec Zlib.Gzlib.Proofs ZlibF.Spec.Public
open Zlib.Gzlib.ErrnoOwned Zlib.Gzwrite.CompErrno

def pendingOwnedHeap (h : Heap) (fs : Fs) (i : Nat) (s : GzState) (xs : List UInt8) : Heap :=
  ownedReportHeap (setS h i {s with again := 0}) {fs with errno := EBADF} i {s with again := 0} xs

private theorem prepared_owned (h : Heap) (i : Nat) (s : GzState) (hs : h.gzstates i = some s) (j : Nat) :
    GzOwned (setS h i {s with again := 0}) i {s with again := 0} j ↔ GzOwned h i s j := by
  simp [GzOwned, StreamOwned, ZStreamRef.get, setS, hs]

/-- Same complete actual compressed-output execution, without a deflate
contract, now resolving strerror and both real message-allocation outcomes. -/
theorem gz_comp_cached_one_badfd_owned_run {h : Heap} {i b : Nat} {s : GzState} {a : Array UInt8}
    {xs : List UInt8}
    (hs : h.gzstates i = some s) (hsize : s.size ≠ 0) (hdir : s.direct = 0)
    (hreset : s.reset = 0) (hav : s.strm.avail_out = 0)
    (hx : s.x.next = .ref (.blk b) 0) (hz : s.strm.next_out = .ref (.blk b) 1)
    (hbytes : h.bytes b = some a) (hfit : 1 ≤ a.size)
    (fs : Fs) (hfd : s.fd < 0 ∨ (fs.fds.size : Int) ≤ s.fd.toInt) (flush : Int32)
    (hm : s.msg = .null) (hp : CString h s.path xs)
    (hpath : MallocBuffer h s.path (xs.length + 1)) (hf : Fresh h)
    (hcap : h.allocOk h.nalloc = true → xs.length + (errnoCharacters EBADF).length + 2 ≤ 2147483647) :
    gz_comp (some (.tab i)) flush fs h =
      .ok ((-1,{fs with errno := EBADF}),pendingOwnedHeap h fs i s xs) := by
  have hp' : CString (setS h i {s with again := 0}) s.path xs :=
    cstring_of_same_malloc_bytes hp hpath rfl
  have hf' : Fresh (setS h i {s with again := 0}) :=
    Shape.fresh (shape_setS hs {s with again := 0}) rfl hf
  have run := report_owned_handler_run (fs := {fs with errno := EBADF})
    (show (setS h i {s with again := 0}).gzstates i = some {s with again := 0} by simp [setS])
    (show ({s with again := 0} : GzState).msg = .null from hm) hp'
    (show MallocBuffer (setS h i {s with again := 0}) s.path (xs.length + 1) from hpath) hf' hcap
  rw [gz_comp_cached_one_badfd_source hs hsize hdir hreset hav hx hz hbytes hfit fs hfd flush,
    pending_report_source, run]
  rfl

/-- Final caller frame over precisely the original owned state graph. This
is the full handler endpoint, rather than just the clear/read prefix. -/
theorem pending_owned_frame {h : Heap} {fs : Fs} {i : Nat} {s : GzState} {xs : List UInt8}
    (hs : h.gzstates i = some s) (hf : Fresh h) :
    Frame h (pendingOwnedHeap h fs i s xs) (GzOwned h i s) := by
  have hf' : Fresh (setS h i {s with again := 0}) :=
    Shape.fresh (shape_setS hs {s with again := 0}) rfl hf
  have tailFrame := report_owned_frame (fs := {fs with errno := EBADF}) (xs := xs)
    (show (setS h i {s with again := 0}).gzstates i = some {s with again := 0} by simp [setS]) hf'
  obtain ⟨a1,a2,a3,a4,a5,af⟩ := pending_prefix_frame h i s
  obtain ⟨b1,b2,b3,b4,b5,bf⟩ := tailFrame
  refine ⟨a1.trans b1,a2.trans b2,a3.trans b3,Nat.le_trans a4 b4,Nat.le_trans a5 b5,?_⟩
  intro j hl ho
  have hj : j ≠ i := fun eq => ho (Or.inl eq)
  have hl' : (setS h i {s with again := 0}).live j := (Shape.live (shape_setS hs {s with again := 0}) j).2 hl
  have ho' := fun own => ho ((prepared_owned h i s hs j).1 own)
  obtain ⟨x1,x2,x3,x4,x5,x6,x7,x8⟩ := af j hl hj
  obtain ⟨y1,y2,y3,y4,y5,y6,y7,y8⟩ := bf j hl' ho'
  exact ⟨y1.trans x1,y2.trans x2,y3.trans x3,y4.trans x4,
    y5.trans x5,y6.trans x6,y7.trans x7,y8.trans x8⟩

/-- No object is lost. The only new live object is the owned message, exactly
when the real allocation oracle accepts its malloc. -/
theorem pending_owned_live {h : Heap} {fs : Fs} {i : Nat} {s : GzState} {xs : List UInt8}
    (hs : h.gzstates i = some s) (hf : Fresh h) :
    LiveChange h (pendingOwnedHeap h fs i s xs)
      (fun b => h.allocOk h.nalloc = true ∧ b = h.nextBlk) (fun _ => False) := by
  have hf' : Fresh (setS h i {s with again := 0}) :=
    Shape.fresh (shape_setS hs {s with again := 0}) rfl hf
  intro j
  have ledger := report_owned_live (fs := {fs with errno := EBADF}) (xs := xs)
    (show (setS h i {s with again := 0}).gzstates i = some {s with again := 0} by simp [setS]) hf' j
  have unchanged : (setS h i {s with again := 0}).live j ↔ h.live j :=
    Shape.live (shape_setS hs {s with again := 0}) j
  rw [unchanged] at ledger
  exact ledger

#print axioms gz_comp_cached_one_badfd_owned_run
#print axioms pending_owned_frame
#print axioms pending_owned_live
end Zlib.Gzwrite.CompErrnoOwned
