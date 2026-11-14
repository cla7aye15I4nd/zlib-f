import ZlibF.Proof.«gzfs.format-error-message»
import ZlibF.Spec.Public.Initialisation
import ZlibF.Spec.Functional.Api.Basic

/-! # Actual copied message and terminating NUL

The message destination is a writable malloc block. The actual storeBytes
allocates a temporary, copies every character, then frees that temporary;
store8 writes the final NUL. Exact heap equations retain all intermediate
updates, so allocator counts and temporary identities are not erased.
-/
namespace Zlib.GzFs.MessageStore
open C Zlib.GzFs ZlibF.Spec.Public

private theorem copyRange_step (d s : Array UInt8) (n : Nat) :
    copyRange d s 0 0 (n + 1) = (copyRange d s 0 0 n).set! n s[n]! := by
  unfold copyRange
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, Nat.zero_add]

private theorem copied_get (d s : Array UInt8) (n i : Nat) (hfit : n ≤ d.size) :
    (copyRange d s 0 0 n)[i]? = if i < n then some s[i]! else d[i]? := by
  induction n generalizing i with
  | zero => simp [copyRange]
  | succ n ih =>
    rw [copyRange_step, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, ih i (by omega)]
    have hs : (copyRange d s 0 0 n).size = d.size := size_copyRange _ _ _ _ _
    by_cases hi : n = i
    · subst hi
      simp [hs, show n < d.size by omega]
    · simp [hi]
      by_cases hn : i < n
      · simp [hn]; omega
      · simp [hn]; intro _; omega

/-- All initial malloc bytes are overwritten: chars followed by exactly NUL. -/
theorem copy_then_nul (a out : Array UInt8) (hlen : a.size = out.size + 1) :
    (copyRange a out 0 0 out.size).set! out.size 0 = out.push 0 := by
  apply Array.ext_getElem?
  intro i
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds,
    copied_get _ _ _ _ (by omega)]
  have hs : (copyRange a out 0 0 out.size).size = a.size := size_copyRange _ _ _ _ _
  by_cases hlt : i < out.size
  · have hne : out.size ≠ i := by omega
    simp [Array.getElem?_push, hs, hlen, hlt, hne, Ne.symm hne, getElem!_pos out i hlt]
  · by_cases heq : i = out.size
    · subst i
      simp [Array.getElem?_push, hs, hlen]
    · have hbig : a.size ≤ i := by omega
      simp [Array.getElem?_push, hs, hlen, hlt, heq, Ne.symm heq,
        Array.getElem?_eq_none hbig]

private def temporaryHeap (h : Heap) (out : Array UInt8) : Heap :=
  { h with bytes := upd h.bytes h.nextBlk (some out), ro := upd h.ro h.nextBlk false,
           nextBlk := h.nextBlk + 1 }
private def charactersHeap (h : Heap) (b : Nat) (a out : Array UInt8) : Heap :=
  { temporaryHeap h out with bytes := upd (temporaryHeap h out).bytes b (some (copyRange a out 0 0 out.size)) }
private def temporaryFreedHeap (h : Heap) (b : Nat) (a out : Array UInt8) : Heap :=
  { charactersHeap h b a out with bytes := upd (charactersHeap h b a out).bytes h.nextBlk none }

/-- The exact chronological byte-table updates, including the freed temporary. -/
def storedMessageHeap (h : Heap) (b : Nat) (a out : Array UInt8) : Heap :=
  { temporaryFreedHeap h b a out with bytes := upd (temporaryFreedHeap h b a out).bytes b (some (out.push 0)) }

private theorem destination_not_temporary {h : Heap} {b : Nat} {a : Array UInt8}
    (hb : h.bytes b = some a) (hslot : h.slotUsed h.nextBlk = false) : b ≠ h.nextBlk := by
  intro he
  subst b
  exact (Heap.slotUsed_eq_false.1 hslot) (Or.inl (by rw [hb]; intro hn; cases hn))

/-- Actual storeBytes, pointer advance and NUL store return this same heap.
No original malloc garbage survives in the destination. -/
theorem store_message_nul_run {h : Heap} {b : Nat} {a out : Array UInt8}
    (hb : h.bytes b = some a) (hro : h.ro b = false) (hlen : a.size = out.size + 1)
    (hn : out.isEmpty = false) (hslot : h.slotUsed h.nextBlk = false) :
    (do storeBytes (.ref (.blk b) 0) out
        let p ← (Ptr.ref (BRef.blk b) 0).add out.size
        store8 p 0) h = .ok ((), storedMessageHeap h b a out) := by
  have hne := destination_not_temporary hb hslot
  have halt : allocBytes out h = .ok (.ref (.blk h.nextBlk) 0, temporaryHeap h out) := by
    simp [allocBytes, hslot, temporaryHeap]
  have hcopy : memcpyB (.ref (.blk b) 0) (.ref (.blk h.nextBlk) 0) out.size
      (temporaryHeap h out) = .ok ((), charactersHeap h b a out) := by
    exact Ptr.memcpy_ok (h := temporaryHeap h out) (rd := BRef.blk b) (rs := BRef.blk h.nextBlk)
      (od := 0) (os := 0) (n := out.size) (da := a) (sa := out)
      (by simpa [temporaryHeap, hne] using hb)
      (by simp [temporaryHeap])
      (by simpa [temporaryHeap, hne] using hro)
      (by omega) (by simp) (Or.inl (by intro he; exact hne (BRef.blk.inj he)))
  have hfree : freeB (.ref (.blk h.nextBlk) 0) (charactersHeap h b a out) =
      .ok ((), temporaryFreedHeap h b a out) := by
    apply freeB_ok (a := out)
    · simp [charactersHeap, temporaryHeap, Ne.symm hne]
    · simp [charactersHeap, temporaryHeap]
  have hstored : storeBytes (.ref (.blk b) 0) out h = .ok ((), temporaryFreedHeap h b a out) := by
    simp only [storeBytes, hn, Bool.false_eq_true, ite_false, bind_app, halt, hcopy, hfree]
  have hget : Space.get (temporaryFreedHeap h b a out) (BRef.blk b) =
      some (copyRange a out 0 0 out.size) := by
    simp [temporaryFreedHeap, charactersHeap, temporaryHeap, hne]
  have hro' : Space.ro (temporaryFreedHeap h b a out) (BRef.blk b) = false := by
    simpa [temporaryFreedHeap, charactersHeap, temporaryHeap, hne] using hro
  have hptr : (Ptr.ref (BRef.blk b) 0).add out.size (temporaryFreedHeap h b a out) =
      .ok (.ref (.blk b) out.size, temporaryFreedHeap h b a out) := by
    simpa [OkOn] using Ptr.add_nat_ok hget (show 0 + out.size ≤ (copyRange a out 0 0 out.size).size by
      rw [size_copyRange]; omega)
  have hzero : store8 (.ref (.blk b) out.size) 0 (temporaryFreedHeap h b a out) =
      .ok ((), storedMessageHeap h b a out) := by
    have hz := Ptr.store_ok (off := out.size) (v := (0 : UInt8)) hget hro'
      (show out.size < (copyRange a out 0 0 out.size).size by rw [size_copyRange]; omega)
    change store8 (.ref (.blk b) out.size) 0 (temporaryFreedHeap h b a out) =
      .ok ((), Space.put (temporaryFreedHeap h b a out) (BRef.blk b) (out.push 0))
    rw [← copy_then_nul a out hlen]
    exact hz
  simp only [bind_app, hstored, hptr, hzero]

/-- Destination content and both resource counters are exact. -/
theorem stored_message_observations {h : Heap} {b : Nat} {a out : Array UInt8}
    (hb : h.bytes b = some a) (hslot : h.slotUsed h.nextBlk = false) :
    (storedMessageHeap h b a out).bytes b = some (out.push 0) ∧
    (storedMessageHeap h b a out).bytes h.nextBlk = none ∧
    (storedMessageHeap h b a out).nextBlk = h.nextBlk + 1 ∧
    (storedMessageHeap h b a out).nalloc = h.nalloc ∧
    (storedMessageHeap h b a out).libcErrorBorrow = h.libcErrorBorrow := by
  have hne := destination_not_temporary hb hslot
  simp [storedMessageHeap, temporaryFreedHeap, charactersHeap, temporaryHeap, Ne.symm hne]

/-- The temporary creates no net live identity. Existing objects survive. -/
theorem stored_message_live {h : Heap} {b : Nat} {a out : Array UInt8}
    (hb : h.bytes b = some a) (hslot : h.slotUsed h.nextBlk = false) :
    LiveChange h (storedMessageHeap h b a out) (fun _ => False) (fun _ => False) := by
  have hne := destination_not_temporary hb hslot
  have htmp : h.bytes h.nextBlk = none := by
    cases he : h.bytes h.nextBlk with
    | none => rfl
    | some val => exact False.elim ((Heap.slotUsed_eq_false.1 hslot) (Or.inl (by rw [he]; intro hn; cases hn)))
  intro j
  by_cases hdest : j = b
  · subst j
    simp [LiveChange, Heap.live, storedMessageHeap, temporaryFreedHeap, charactersHeap,
      temporaryHeap, hb]
  · by_cases htemp : j = h.nextBlk
    · subst j
      simp [Heap.live, storedMessageHeap, temporaryFreedHeap, charactersHeap,
        temporaryHeap, Ne.symm hne, htmp]
    · simp [Heap.live, storedMessageHeap, temporaryFreedHeap, charactersHeap,
        temporaryHeap, hdest, htemp]

/-- The full old-object frame follows the real temporary allocation and free;
only the message destination may change. -/
theorem stored_message_frame {h : Heap} {b : Nat} {a out : Array UInt8}
    (hslot : h.slotUsed h.nextBlk = false) :
    Frame h (storedMessageHeap h b a out) (fun j => j = b) := by
  refine ⟨rfl, rfl, rfl, by change h.nextBlk ≤ h.nextBlk + 1; omega, Nat.le_refl _, ?_⟩
  intro j hl hj
  have ht : j ≠ h.nextBlk := by
    intro he
    subst j
    exact (Heap.slotUsed_eq_false.1 hslot) hl
  simp [storedMessageHeap, temporaryFreedHeap, charactersHeap, temporaryHeap, hj, ht]

def errorFormatPointer : BPtr := .ref (.str 46) 0
def errorSeparatorPointer : BPtr := .ref (.str 58) 0

set_option maxRecDepth 20000 in
/-- Original closed source literal, with the original unchanged index. -/
theorem error_format_literal (h : Heap) :
    strLit "%s%s%s" h = .ok (errorFormatPointer, h) := by
  conv => lhs; cbv
  conv => rhs; cbv
  all_goals rfl

set_option maxRecDepth 20000 in
theorem error_separator_literal (h : Heap) :
    strLit ": " h = .ok (errorSeparatorPointer, h) := by
  conv => lhs; cbv
  conv => rhs; cbv
  all_goals rfl

set_option maxRecDepth 20000 in
theorem error_format_read (h : Heap) :
    cstring errorFormatPointer h = .ok (#[37,115,37,115,37,115], h) := by
  conv => lhs; cbv
  conv => rhs; cbv
  all_goals rfl

set_option maxRecDepth 20000 in
theorem error_separator_read (h : Heap) :
    cstring errorSeparatorPointer h = .ok (#[58,32], h) := by
  conv => lhs; cbv
  conv => rhs; cbv
  all_goals rfl

private theorem store_bind_assoc {α β γ : Type} (m : M α) (f : α → M β) (g : β → M γ) :
    (m >>= f) >>= g = m >>= (fun a => f a >>= g) := by
  funext h
  cases he : m h <;> simp [bind_app, he]
private theorem store_pure_bind {α β : Type} (a : α) (f : α → M β) :
    (pure a >>= f) = f a := rfl

/-- The actual formatter, byte copy and final NUL are connected. The INT_MAX
output bound is the existing snprintf model's internal successful-output
domain; it is not a new restriction on a public gzip goal. -/
theorem snprintf_error_copy_run {h : Heap} {b : Nat} {a : Array UInt8}
    {path msg : BPtr} {xs es : List UInt8}
    (hp : CString h path xs) (he : CString h msg es)
    (hb : h.bytes b = some a) (hro : h.ro b = false)
    (hlen : a.size = xs.length + es.length + 3)
    (hmax : xs.length + es.length + 2 ≤ 2147483647)
    (hslot : h.slotUsed h.nextBlk = false) :
    let out := (xs ++ [58,32] ++ es).toArray
    snprintf (.ref (.blk b) 0) (UInt64.ofNat (xs.length + es.length + 3)) errorFormatPointer
      [.str path, .str errorSeparatorPointer, .str msg] h =
        .ok (Int32.ofNat out.size, storedMessageHeap h b a out) := by
  let out := (xs ++ [58,32] ++ es).toArray
  have hsize : out.size = xs.length + es.length + 2 := by simp [out]; omega
  have hbytes : a.size = out.size + 1 := by omega
  have hread := Zlib.GzFs.Proofs.format_error_message
    (Zlib.GzFs.Proofs.cstring_of_CString hp) (error_separator_read h)
    (Zlib.GzFs.Proofs.cstring_of_CString he)
  have hformat : formatBytes #[37,115,37,115,37,115]
      [.str path, .str errorSeparatorPointer, .str msg] h = .ok (out, h) := by
    simpa [out] using hread.1
  have hnum : (UInt64.ofNat (xs.length + es.length + 3)).toNat = out.size + 1 := by
    rw [UInt64.toNat_ofNat_of_lt' (by change xs.length + es.length + 3 < 2^64; omega)]
    omega
  have hne : UInt64.ofNat (xs.length + es.length + 3) ≠ 0 := by
    intro heq
    have ht := congrArg UInt64.toNat heq
    rw [hnum] at ht
    change out.size + 1 = 0 at ht
    omega
  have hnonempty : out.isEmpty = false := by simp [Array.isEmpty, hsize]
  have hstored := store_message_nul_run hb hro hbytes hnonempty hslot
  have result : (do
      let _ ← (do storeBytes (.ref (.blk b) 0) out
                  let p ← (Ptr.ref (BRef.blk b) 0).add out.size
                  store8 p 0)
      pure (Int32.ofNat out.size)) h = .ok (Int32.ofNat out.size, storedMessageHeap h b a out) := by
    rw [bind_app, hstored]
    rfl
  change snprintf _ _ _ _ h = _
  unfold snprintf
  simp only [bind_app, error_format_read, hformat]
  simp only [show ¬ out.size > 2147483647 by omega, ite_false,
    show (UInt64.ofNat (xs.length + es.length + 3) != 0) = true by simpa only [bne_iff_ne] using hne, ite_true,
    hnum, Nat.add_sub_cancel, Nat.min_self, Array.extract_size]
  simpa only [store_bind_assoc, store_pure_bind] using result

#print axioms copy_then_nul
#print axioms store_message_nul_run
#print axioms stored_message_observations
#print axioms stored_message_live
#print axioms stored_message_frame
#print axioms error_format_read
#print axioms error_separator_read
#print axioms snprintf_error_copy_run
end Zlib.GzFs.MessageStore
