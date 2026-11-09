import ZlibF.Proof.«gzlib.c.errno-owned-run»

/-! # Error report content and subsequent borrow invalidation

These observations concern the same actual adjacent calls and final heap as
errno-owned-run. Content, resources and pointer lifetime are separate facts.
The later real strerror call invalidates the borrowed view while keeping the
copied owned message bytes and the malloc live ledger.
-/
namespace Zlib.Gzlib.ErrnoOwned
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzlib.Spec
open ZlibF.Spec.Public Zlib.GzFs.Proofs Zlib.Gzlib.ErrnoLifetime
open Zlib.Gzlib.MessageCopy Zlib.Gzlib.MessageRefusal

/-- Complete message/counter observations, including refusal. This is more
than the NULL-or-malloc-root pointer shape: the successful bytes are exact. -/
def ReportMessageOutcome (h after : Heap) (fs : Fs) (i : Nat) (s : GzState) (xs : List UInt8) : Prop :=
  if h.allocOk h.nalloc then
    after.gzstates i = some (copiedMessageState h s) ∧
    after.bytes h.nextBlk = some ((messageChars xs (errnoCharacters fs.errno)).push 0) ∧
    after.bytes (h.nextBlk + 1) = none ∧
    after.nextBlk = h.nextBlk + 2 ∧ after.nalloc = h.nalloc + 1
  else
    after.gzstates i = some (refusedMessageState s) ∧
    after.bytes = h.bytes ∧ after.nextBlk = h.nextBlk ∧ after.nalloc = h.nalloc + 1

theorem report_owned_message_outcome {h : Heap} {fs : Fs} {i : Nat} {s : GzState} {xs : List UInt8}
    (hs : h.gzstates i = some s) (hf : Fresh h) :
    ReportMessageOutcome h (ownedReportHeap h fs i s xs) fs i s xs := by
  cases ha : h.allocOk h.nalloc with
  | false => simp [ReportMessageOutcome, ownedReportHeap, ha, refusedMessageHeap, setS, errnoHeap]
  | true =>
    have facts := copied_message_observations (xs := xs) (es := errnoCharacters fs.errno)
      (show (errnoHeap h fs).gzstates i = some s from hs) (show Fresh (errnoHeap h fs) from hf)
    simpa [ReportMessageOutcome, ownedReportHeap, ha, copiedMessageState, errnoHeap] using
      And.intro facts.1 ⟨facts.2.1,facts.2.2.1,facts.2.2.2.1,facts.2.2.2.2.1⟩

/-- One same-run result provides exact content, original owned frame and live
ledger, readable current borrowed text, no retained borrowed msg pointer, and
invalidation on the next actual strerror call. No callee contract is assumed. -/
theorem report_owned_complete {h : Heap} {fs : Fs} {i : Nat} {s : GzState} {xs : List UInt8}
    (hs : h.gzstates i = some s) (hm : s.msg = .null) (hp : CString h s.path xs)
    (hpath : MallocBuffer h s.path (xs.length + 1)) (hf : Fresh h)
    (hcap : h.allocOk h.nalloc = true → xs.length + (errnoCharacters fs.errno).length + 2 ≤ 2147483647) :
    let after := ownedReportHeap h fs i s xs
    ((do gz_error (some (.tab i)) Z_ERRNO (← zstrerror)) : G Unit) fs h = .ok (((),fs),after) ∧
    ReportMessageOutcome h after fs i s xs ∧
    Frame h after (GzOwned h i s) ∧
    LiveChange h after (fun b => h.allocOk h.nalloc = true ∧ b = h.nextBlk) (fun _ => False) ∧
    Space.get after (BRef.str (libcErrnoIndex (nextErrorEpoch h) fs.errno)) =
      some (strBytes (strerrorText fs.errno)) ∧
    (∀ final, after.gzstates i = some final → final.msg ≠ errnoPointer h fs) ∧
    (∀ (nextFs : Fs) (p : BPtr) (fs' : Fs) (next : Heap),
      zstrerror nextFs after = .ok ((p,fs'),next) →
      Space.get next (BRef.str (libcErrnoIndex (nextErrorEpoch h) fs.errno)) = none ∧
      next.bytes = after.bytes ∧ next.gzstates = after.gzstates ∧
      (∀ b, next.live b ↔ after.live b)) := by
  dsimp only
  have run := report_owned_run hs hm hp hpath hf hcap
  have life := report_lifetime i h (ownedReportHeap h fs i s xs) fs fs () run
  refine ⟨run,report_owned_message_outcome hs hf,report_owned_frame hs hf,
    report_owned_live hs hf,life.2.2.1,life.2.2.2.1,?_⟩
  intro nextFs p fs' next nextRun
  rw [zstrerror_run] at nextRun
  cases nextRun
  exact ⟨life.2.2.2.2 nextFs,rfl,rfl,fun _ => Iff.rfl⟩

#print axioms report_owned_message_outcome
#print axioms report_owned_complete
end Zlib.Gzlib.ErrnoOwned
