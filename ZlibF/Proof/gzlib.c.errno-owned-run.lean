import ZlibF.Proof.«libc-errno-cstring»
import ZlibF.Proof.«gzlib.c.error-message-copy»
import ZlibF.Proof.«gzlib.c.error-message-refusal»
import ZlibF.Proof.«gzlib.c.errno-call-lifetime»

/-! # Actual errno report with owned memory effects

The path is the original private malloc CString. The new errno CString is
produced by this same real strerror call, not assumed from a caller contract.
This first endpoint has no previous message. It covers both actual allocator
outcomes; the existing formatter INT_MAX bound is conditional on success.
-/
namespace Zlib.Gzlib.ErrnoOwned
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzlib.Spec
open ZlibF.Spec.Public Zlib.GzFs.Proofs Zlib.Gzlib.ErrnoLifetime
open Zlib.Gzlib.MessageCopy Zlib.Gzlib.MessageRefusal

def errnoCharacters (e : Int32) : List UInt8 := (strerrorText e).toUTF8.data.toList

def ownedReportHeap (h : Heap) (fs : Fs) (i : Nat) (s : GzState) (xs : List UInt8) : Heap :=
  if h.allocOk h.nalloc then
    copiedMessageHeap (errnoHeap h fs) i s xs (errnoCharacters fs.errno)
  else refusedMessageHeap (errnoHeap h fs) i s

private theorem CString_block_transport {h after : Heap} {p : BPtr} {xs : List UInt8} {b : Nat}
    (hp : p = .ref (.blk b) 0) (hc : CString h p xs) (hb : after.bytes b = h.bytes b) :
    CString after p xs := by
  subst p
  refine ⟨?_, hc.2⟩
  rcases hc.1 with hn | ⟨r,off,a,hptr,ha,hfit,htext⟩
  · cases hn.1
  · cases hptr
    exact Or.inr ⟨.blk b,0,a,rfl,hb.trans ha,hfit,htext⟩

/-- Only a persistent private path is transported across strerror. This does
not assert that a malloc Frame preserves arbitrary old borrowed .str views. -/
theorem path_cstring_after_errno {h : Heap} {p : BPtr} {xs : List UInt8} {n : Nat}
    (hp : CString h p xs) (hm : MallocBuffer h p n) (fs : Fs) : CString (errnoHeap h fs) p xs := by
  obtain ⟨b,a,hptr,_,_,_⟩ := hm
  exact CString_block_transport hptr hp rfl

private theorem errno_heap_frame (h : Heap) (fs : Fs) : Frame h (errnoHeap h fs) (fun _ => False) := by
  exact ⟨rfl,rfl,rfl,Nat.le_refl _,Nat.le_refl _,fun _ _ _ => ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩

private theorem errno_heap_owned (h : Heap) (fs : Fs) (i : Nat) (s : GzState) (j : Nat) :
    GzOwned (errnoHeap h fs) i s j ↔ GzOwned h i s j := Iff.rfl

/-- Same actual adjacent call pair used at all four C sites, now with a
complete returned heap for both malloc outcomes. All signed errno values and
all previous external borrow epochs are admitted by the real CString producer. -/
theorem report_owned_run {h : Heap} {fs : Fs} {i : Nat} {s : GzState} {xs : List UInt8}
    (hs : h.gzstates i = some s) (hm : s.msg = .null) (hp : CString h s.path xs)
    (hpath : MallocBuffer h s.path (xs.length + 1)) (hf : Fresh h)
    (hcap : h.allocOk h.nalloc = true → xs.length + (errnoCharacters fs.errno).length + 2 ≤ 2147483647) :
    ((do gz_error (some (.tab i)) Z_ERRNO (← zstrerror)) : G Unit) fs h =
      .ok (((), fs), ownedReportHeap h fs i s xs) := by
  have hpBorrow := path_cstring_after_errno hp hpath fs
  have heBorrow : CString (errnoHeap h fs) (errnoPointer h fs) (errnoCharacters fs.errno) :=
    C.LibcBorrow.current_cstring _ _ _ rfl
  have hsBorrow : (errnoHeap h fs).gzstates i = some s := hs
  have hfBorrow : Fresh (errnoHeap h fs) := hf
  rw [report_source]
  cases ha : h.allocOk h.nalloc with
  | false =>
    rw [gz_error_errno_refusal_run hsBorrow hm hpBorrow heBorrow ha]
    simp [ownedReportHeap, ha]
  | true =>
    rw [gz_error_errno_copy_run hsBorrow hm hpBorrow heBorrow hfBorrow ha (hcap ha)]
    simp [ownedReportHeap, ha]

/-- The exact real handler run is available to whole callers after their
source cut. Its input CString was produced by actual strerror above. -/
theorem report_owned_handler_run {h : Heap} {fs : Fs} {i : Nat} {s : GzState} {xs : List UInt8}
    (hs : h.gzstates i = some s) (hm : s.msg = .null) (hp : CString h s.path xs)
    (hpath : MallocBuffer h s.path (xs.length + 1)) (hf : Fresh h)
    (hcap : h.allocOk h.nalloc = true → xs.length + (errnoCharacters fs.errno).length + 2 ≤ 2147483647) :
    gz_error (some (.tab i)) Z_ERRNO (errnoPointer h fs) (errnoHeap h fs) =
      .ok ((), ownedReportHeap h fs i s xs) := by
  have report := report_owned_run hs hm hp hpath hf hcap
  rw [report_source] at report
  cases run : gz_error (some (.tab i)) Z_ERRNO (errnoPointer h fs) (errnoHeap h fs) with
  | error e => rw [run] at report; contradiction
  | ok result =>
    rcases result with ⟨v, final⟩
    cases v
    rw [run] at report
    cases report
    rfl

/-- A private malloc string uses persistent block bytes, independently of
borrow metadata or record-field updates. -/
theorem cstring_of_same_malloc_bytes {h after : Heap} {p : BPtr} {xs : List UInt8} {n : Nat}
    (hp : CString h p xs) (hm : MallocBuffer h p n) (hbytes : after.bytes = h.bytes) :
    CString after p xs := by
  obtain ⟨b,a,hptr,_,_,_⟩ := hm
  exact CString_block_transport hptr hp (congrArg (fun bytes => bytes b) hbytes)

/-- Complete original malloc-object frame, after strerror and the handler.
The external borrow itself is handled by its actual lifetime theorem. -/
theorem report_owned_frame {h : Heap} {fs : Fs} {i : Nat} {s : GzState} {xs : List UInt8}
    (hs : h.gzstates i = some s) (hf : Fresh h) :
    Frame h (ownedReportHeap h fs i s xs) (GzOwned h i s) := by
  have tailFrame : Frame (errnoHeap h fs) (ownedReportHeap h fs i s xs) (GzOwned (errnoHeap h fs) i s) := by
    cases ha : h.allocOk h.nalloc with
    | false => simpa [ownedReportHeap, ha] using refused_message_owned_frame (errnoHeap h fs) i s
    | true =>
      simpa [ownedReportHeap, ha] using
        copied_message_owned_frame (xs := xs) (es := errnoCharacters fs.errno)
          (show (errnoHeap h fs).gzstates i = some s from hs) (show Fresh (errnoHeap h fs) from hf)
  obtain ⟨a1,a2,a3,a4,a5,af⟩ := errno_heap_frame h fs
  obtain ⟨b1,b2,b3,b4,b5,bf⟩ := tailFrame
  refine ⟨a1.trans b1,a2.trans b2,a3.trans b3,Nat.le_trans a4 b4,Nat.le_trans a5 b5,?_⟩
  intro j hl ho
  have hlBorrow : (errnoHeap h fs).live j := hl
  have hoBorrow : ¬GzOwned (errnoHeap h fs) i s j := fun owned => ho ((errno_heap_owned h fs i s j).1 owned)
  obtain ⟨x1,x2,x3,x4,x5,x6,x7,x8⟩ := af j hl (fun impossible => impossible)
  obtain ⟨y1,y2,y3,y4,y5,y6,y7,y8⟩ := bf j hlBorrow hoBorrow
  exact ⟨y1.trans x1,y2.trans x2,y3.trans x3,y4.trans x4,
    y5.trans x5,y6.trans x6,y7.trans x7,y8.trans x8⟩

/-- Exactly one new owned message on successful allocation, otherwise no new
live object. Strerror and the formatter leave no additional allocation behind. -/
theorem report_owned_live {h : Heap} {fs : Fs} {i : Nat} {s : GzState} {xs : List UInt8}
    (hs : h.gzstates i = some s) (hf : Fresh h) :
    LiveChange h (ownedReportHeap h fs i s xs)
      (fun b => h.allocOk h.nalloc = true ∧ b = h.nextBlk) (fun _ => False) := by
  intro j
  cases ha : h.allocOk h.nalloc with
  | false =>
    have hl := refused_message_live (errnoHeap h fs) i s (show (errnoHeap h fs).gzstates i = some s from hs) j
    rw [show (errnoHeap h fs).live j = h.live j from rfl] at hl
    simpa [LiveChange, ownedReportHeap, ha] using hl
  | true =>
    have hl := copied_message_live (xs := xs) (es := errnoCharacters fs.errno)
      (show (errnoHeap h fs).gzstates i = some s from hs) (show Fresh (errnoHeap h fs) from hf) j
    rw [show (errnoHeap h fs).live j = h.live j from rfl,
      show (errnoHeap h fs).nextBlk = h.nextBlk from rfl] at hl
    simpa [LiveChange, ownedReportHeap, ha] using hl

#print axioms report_owned_run
#print axioms report_owned_handler_run
#print axioms report_owned_frame
#print axioms report_owned_live
end Zlib.Gzlib.ErrnoOwned
