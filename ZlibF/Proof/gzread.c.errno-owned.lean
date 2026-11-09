import ZlibF.Proof.«gzread.c.errno-retry»
import ZlibF.Proof.«gzlib.c.errno-owned-run»

/-! # Complete resources on the internal deferred errno retry

The same zero-length, again-nonzero wrapper branch is used as in errno-retry.
The external filesystem cannot produce EAGAIN, so this is an internal execution
cut, not an initialized public-history claim. The formatter success bound is
an explicit internal domain; the public goal is unchanged.
-/
namespace Zlib.Gzread.ErrnoOwned
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzread
open Zlib.Gzlib.Spec Zlib.Gzlib.Proofs ZlibF.Spec.Public
open Zlib.Gzlib.ErrnoOwned Zlib.Gzread.ErrnoRetry

def retryOwnedHeap (h : Heap) (fs : Fs) (i : Nat) (s : GzState) (xs : List UInt8) : Heap :=
  ownedReportHeap (clearRetryHeap h i s) fs i {s with err := Z_OK} xs

private theorem prepared_owned (h : Heap) (i : Nat) (s : GzState) (hs : h.gzstates i = some s) (j : Nat) :
    GzOwned (clearRetryHeap h i s) i {s with err := Z_OK} j ↔ GzOwned h i s j := by
  simp [GzOwned, StreamOwned, ZStreamRef.get, clearRetryHeap, setS, hs]

/-- Complete actual wrapper run, including the same strerror borrow, message
copy or allocation refusal, and all formatter temporary cleanup. -/
theorem gzread_zero_retry_owned_run {h : Heap} {fs : Fs} {i : Nat} {s : GzState}
    {xs : List UInt8} (buf : BPtr)
    (hs : h.gzstates i = some s) (hr : s.mode = GZ_READ)
    (ha : s.again ≠ 0) (hm : s.msg = .null)
    (hp : CString h s.path xs) (hpath : MallocBuffer h s.path (xs.length + 1))
    (hf : Fresh h)
    (hcap : h.allocOk h.nalloc = true → xs.length + (errnoCharacters fs.errno).length + 2 ≤ 2147483647) :
    gzread (some (.in_gzstate_x i)) buf 0 fs h = .ok ((-1,fs),retryOwnedHeap h fs i s xs) := by
  have hp' : CString (clearRetryHeap h i s) s.path xs :=
    cstring_of_same_malloc_bytes hp hpath rfl
  have hf' : Fresh (clearRetryHeap h i s) :=
    Shape.fresh (shape_setS hs {s with err := Z_OK}) rfl hf
  have run := report_owned_handler_run
    (show (clearRetryHeap h i s).gzstates i = some {s with err := Z_OK} by simp [clearRetryHeap])
    (show ({s with err := Z_OK} : GzState).msg = .null from hm) hp'
    (show MallocBuffer (clearRetryHeap h i s) s.path (xs.length + 1) from hpath) hf' hcap
  rw [gzread_zero_retry_source h fs i s buf hs hr ha hm, retry_report_source, run]
  rfl

/-- Final caller frame over precisely the original owned state graph. This
is the full handler endpoint, rather than just the clear/read prefix. -/
theorem retry_owned_frame {h : Heap} {fs : Fs} {i : Nat} {s : GzState} {xs : List UInt8}
    (hs : h.gzstates i = some s) (hf : Fresh h) :
    Frame h (retryOwnedHeap h fs i s xs) (GzOwned h i s) := by
  have hf' : Fresh (clearRetryHeap h i s) :=
    Shape.fresh (shape_setS hs {s with err := Z_OK}) rfl hf
  have tailFrame := report_owned_frame (fs := fs) (xs := xs)
    (show (clearRetryHeap h i s).gzstates i = some {s with err := Z_OK} by simp [clearRetryHeap]) hf'
  obtain ⟨a1,a2,a3,a4,a5,af⟩ := clear_retry_frame h i s
  obtain ⟨b1,b2,b3,b4,b5,bf⟩ := tailFrame
  refine ⟨a1.trans b1,a2.trans b2,a3.trans b3,Nat.le_trans a4 b4,Nat.le_trans a5 b5,?_⟩
  intro j hl ho
  have hj : j ≠ i := fun eq => ho (Or.inl eq)
  have hl' : (clearRetryHeap h i s).live j := (Shape.live (shape_setS hs {s with err := Z_OK}) j).2 hl
  have ho' := fun own => ho ((prepared_owned h i s hs j).1 own)
  obtain ⟨x1,x2,x3,x4,x5,x6,x7,x8⟩ := af j hl hj
  obtain ⟨y1,y2,y3,y4,y5,y6,y7,y8⟩ := bf j hl' ho'
  exact ⟨y1.trans x1,y2.trans x2,y3.trans x3,y4.trans x4,
    y5.trans x5,y6.trans x6,y7.trans x7,y8.trans x8⟩

/-- No object is lost. The only new live object is the owned message, exactly
when the real allocation oracle accepts its malloc. -/
theorem retry_owned_live {h : Heap} {fs : Fs} {i : Nat} {s : GzState} {xs : List UInt8}
    (hs : h.gzstates i = some s) (hf : Fresh h) :
    LiveChange h (retryOwnedHeap h fs i s xs)
      (fun b => h.allocOk h.nalloc = true ∧ b = h.nextBlk) (fun _ => False) := by
  have hf' : Fresh (clearRetryHeap h i s) :=
    Shape.fresh (shape_setS hs {s with err := Z_OK}) rfl hf
  intro j
  have ledger := report_owned_live (fs := fs) (xs := xs)
    (show (clearRetryHeap h i s).gzstates i = some {s with err := Z_OK} by simp [clearRetryHeap]) hf' j
  have unchanged : (clearRetryHeap h i s).live j ↔ h.live j :=
    Shape.live (shape_setS hs {s with err := Z_OK}) j
  rw [unchanged] at ledger
  exact ledger

#print axioms gzread_zero_retry_owned_run
#print axioms retry_owned_frame
#print axioms retry_owned_live
end Zlib.Gzread.ErrnoOwned
