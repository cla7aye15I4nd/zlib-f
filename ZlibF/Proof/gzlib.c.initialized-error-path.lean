import ZlibF.Proof.«gzlib.c.dopen-success»
import ZlibF.Proof.«gzlib.c.errno-owned-observations»

/-! # Actual initialization supplies the private error path

Descriptor opens produce a bounded private path rather than assuming a new
formatter bound on callers. The report below is an internal call-site cut after
that actual public initializer. Ordinary writer/reader paths must still be
connected to this cut; this is not a complete public sequence theorem.
-/
namespace Zlib.Gzlib.InitializedErrorPath
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzlib.Spec Zlib.Gzlib.Proofs
open ZlibF.Spec.Public Zlib.Gzlib.ErrnoOwned
open Zlib.Gzlib.MessageCopy Zlib.Gzlib.MessageRefusal Zlib.Gzlib.ErrnoLifetime

private theorem CString_unique {h : Heap} {p : BPtr} {xs ys : List UInt8}
    (hx : CString h p xs) (hy : CString h p ys) : xs = ys := by
  have a := Zlib.GzFs.Proofs.heapStr_of_CString hx
  have b := Zlib.GzFs.Proofs.heapStr_of_CString hy
  have arrays := Option.some.inj (a.symm.trans b)
  simpa using congrArg Array.toList arrays

/-- The existing initializer invariant already owns its observed path. Its
existential string cannot secretly have a different length or byte sequence. -/
theorem valid_observed_path_malloc {h : Heap} {i : Nat} {s : GzState} {xs : List UInt8}
    (hv : GzValid h i s) (hp : CString h s.path xs) :
    MallocBuffer h s.path (xs.length + 1) := by
  obtain ⟨ys,hy,buffer⟩ := hv.2.2.2.2.2.1
  have eq := CString_unique hp hy
  simpa [eq] using buffer

/-- A still-live private malloc path differs from the next actual allocation.
This uses freshness and that concrete byte block, without caller GlobalUniq. -/
theorem private_path_ne_fresh_message {h : Heap} {p : BPtr} {n : Nat}
    (hp : MallocBuffer h p n) (hf : Fresh h) : p ≠ .ref (.blk h.nextBlk) 0 := by
  obtain ⟨b,a,hptr,hbytes,_,_⟩ := hp
  intro eq
  rw [hptr] at eq
  cases eq
  exact hf h.nextBlk (Nat.le_refl _) (Or.inl (by rw [hbytes]; simp))

/-- The exact initialized private path stays separate from the same returned
message pointer on either allocation outcome. No global no-alias premise is
introduced: the new root follows from actual malloc freshness. -/
theorem report_owned_path_separate {h : Heap} {fs : Fs} {i : Nat} {s : GzState}
    {xs : List UInt8} {n : Nat} (hs : h.gzstates i = some s) (hf : Fresh h)
    (hp : MallocBuffer h s.path n) :
    ∀ final, (ownedReportHeap h fs i s xs).gzstates i = some final → final.path ≠ final.msg := by
  have outcome := report_owned_message_outcome (fs := fs) (xs := xs) hs hf
  intro final hfinal
  cases ha : h.allocOk h.nalloc with
  | false =>
    simp only [ReportMessageOutcome, ha, Bool.false_eq_true, ite_false] at outcome
    have eq := Option.some.inj (hfinal.symm.trans outcome.1)
    subst final
    obtain ⟨b,a,hptr,_,_,_⟩ := hp
    change s.path ≠ .null
    simp [hptr]
  | true =>
    simp only [ReportMessageOutcome, ha, ite_true] at outcome
    have eq := Option.some.inj (hfinal.symm.trans outcome.1)
    subst final
    exact private_path_ne_fresh_message hp hf

/-- All nonnegative descriptor identifiers and all signed errno texts fit the
actual formatter, by the already proved decimal/text bounds. No new caller
bound is needed, including for unknown or negative errno values. -/
theorem descriptor_report_capacity (fd errno : Int32) (hn : 0 ≤ fd.toInt) :
    (descriptorPath fd).length + (errnoCharacters errno).length + 2 ≤ 2147483647 := by
  have path := descriptorPath_length fd hn
  have text := C.LibcStrings.Proofs.errno_bytes_lt64 errno
  simp only [strBytes, Array.size_push, ByteArray.size_data] at text
  change (libcErrnoText errno).toUTF8.data.size + 1 < 64 at text
  simp only [errnoCharacters, strerrorText, Array.length_toList]
  omega

/-- The exact actual gzdopen success heap establishes a complete copied-error
entry for both allocator outcomes. The first three allocation-success facts
select that real init branch; the later message oracle is unrestricted. -/
theorem gzdopen_actual_report {h : Heap} {fs : Fs} {fd : Int32} {mode : BPtr}
    (transparent : Bool) (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h)
    (hn : 0 ≤ fd.toInt)
    (hm : CString h mode (if transparent then [119,84] else [119]))
    (ha : h.allocOk h.nalloc = true) (ha1 : h.allocOk (h.nalloc + 1) = true)
    (ha2 : h.allocOk (h.nalloc + 2) = true) :
    let entry := descriptorEntryHeap h fd
    let opened := descriptorReleased (writerOpenHeap entry transparent (descriptorPath fd) fd) h.nextBlk
    let state := writerOpenState entry transparent fd
    let after := ownedReportHeap opened fs entry.nextBlk state (descriptorPath fd)
    gzdopen fd mode fs h = .ok ((some (.in_gzstate_x entry.nextBlk),fs),opened) ∧
    ((do gz_error (some (.tab entry.nextBlk)) Z_ERRNO (← zstrerror)) : G Unit) fs opened =
      .ok (((),fs),after) ∧
    ReportMessageOutcome opened after fs entry.nextBlk state (descriptorPath fd) ∧
    Frame opened after (GzOwned opened entry.nextBlk state) ∧
    LiveChange opened after
      (fun b => opened.allocOk opened.nalloc = true ∧ b = opened.nextBlk) (fun _ => False) ∧
    (∀ final, after.gzstates entry.nextBlk = some final → final.path ≠ final.msg) ∧
    Space.get after (BRef.str (libcErrnoIndex (Zlib.GzFs.Proofs.nextErrorEpoch opened) fs.errno)) =
      some (strBytes (strerrorText fs.errno)) := by
  dsimp only
  obtain ⟨init,ho,_,_⟩ := gzdopen_writer_accounted h fs fd mode transparent hf hu hg hn hm ha ha1 ha2
  rcases ho with ⟨hv,_,_,hp,_,_,_,_,_,_,hm0,_⟩
  have privatePath := valid_observed_path_malloc hv hp
  have complete := report_owned_complete hv.1 hm0 hp privatePath hv.2.2.1
    (fun _ => descriptor_report_capacity fd fs.errno hn)
  exact ⟨init,complete.1,complete.2.1,complete.2.2.1,complete.2.2.2.1,
    report_owned_path_separate hv.1 hv.2.2.1 privatePath,complete.2.2.2.2.1⟩

#print axioms valid_observed_path_malloc
#print axioms private_path_ne_fresh_message
#print axioms report_owned_path_separate
#print axioms descriptor_report_capacity
#print axioms gzdopen_actual_report
end Zlib.Gzlib.InitializedErrorPath
