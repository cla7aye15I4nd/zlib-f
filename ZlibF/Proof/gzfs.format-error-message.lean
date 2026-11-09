import ZlibF.Proof.gzfs
import ZlibF.Spec.Public.History

/-! Fixed error-message formatting. All heap reads are connected to the real
cstring and formatBytes execution; no allocator or caller-frame claim is made. -/
namespace Zlib.GzFs.Proofs
open C Zlib.GzFs ZlibF.Spec.Public
set_option autoImplicit false

/-- The three actual string conversions retain argument order and every byte. -/
theorem formatGo_sss (res : BPtr → Option (Array UInt8)) (path sep msg : BPtr)
    (xs middle es : Array UInt8)
    (hp : argStr res path = some xs) (hs : argStr res sep = some middle)
    (hm : argStr res msg = some es) :
    formatGo #[37,115,37,115,37,115] res 7 0 [.str path, .str sep, .str msg] #[] =
      .ok (xs ++ middle ++ es) := by
  simp [formatGo, parse_sss1, parse_sss2, parse_sss3, hp, hs, hm, pad]

/-- A successful real CString read cannot have used NULL. -/
theorem cstring_nonnull {h after : Heap} {p : BPtr} {a : Array UInt8}
    (run : cstring p h = .ok (a, after)) : p ≠ .null := by
  intro null
  subst p
  simp [cstring, strlenB] at run

/-- Actual reads supply the formatter's resolver; no independent resolver
contract or extra NULL restriction is assumed. -/
theorem formatBytes_sss {h : Heap} {path sep msg : BPtr} {xs middle es : Array UInt8}
    (hp : cstring path h = .ok (xs, h)) (hs : cstring sep h = .ok (middle, h))
    (hm : cstring msg h = .ok (es, h)) :
    formatBytes #[37,115,37,115,37,115] [.str path, .str sep, .str msg] h =
      .ok (xs ++ middle ++ es, h) := by
  have pathRead : argStr (heapStr h) path = some xs := by
    simp [argStr, cstring_nonnull hp, heapStr_of hp]
  have sepRead : argStr (heapStr h) sep = some middle := by
    simp [argStr, cstring_nonnull hs, heapStr_of hs]
  have msgRead : argStr (heapStr h) msg = some es := by
    simp [argStr, cstring_nonnull hm, heapStr_of hm]
  simp only [formatBytes, show (#[37,115,37,115,37,115] : Array UInt8).size + 1 = 7 by rfl,
    formatGo_sss _ _ _ _ _ _ _ pathRead sepRead msgRead]

/-- Error messages have exactly path, colon-space, and external error bytes.
The caller's final store8 writes the extra NUL, whose complete size is given. -/
theorem format_error_message {h : Heap} {path sep msg : BPtr} {xs es : Array UInt8}
    (hp : cstring path h = .ok (xs, h)) (hs : cstring sep h = .ok (#[58,32], h))
    (hm : cstring msg h = .ok (es, h)) :
    formatBytes #[37,115,37,115,37,115] [.str path, .str sep, .str msg] h =
      .ok (xs ++ #[58,32] ++ es, h) ∧
    (xs ++ #[58,32] ++ es).size = xs.size + es.size + 2 ∧
    ((xs ++ #[58,32] ++ es).push 0).size = xs.size + es.size + 3 := by
  exact ⟨formatBytes_sss hp hs hm, by simp; omega, by simp; omega⟩

private theorem read_chars (h : Heap) (p : BPtr) (xs : List UInt8) (start : Nat)
    (out : Array UInt8)
    (reads : ∀ j (bound : j < xs.length), index8 p ((start + j : Nat) : Int) h = .ok (xs[j], h)) :
    (forIn (List.range' start xs.length) out
      (fun (i : Nat) a => do let b ← index8 p i; pure (ForInStep.yield (a.push b))) : M (Array UInt8)) h = .ok (out ++ xs.toArray, h) := by
  induction xs generalizing start out with
  | nil => simp
  | cons head tail ih =>
    have first := reads 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at first
    have rest : ∀ j (bound : j < tail.length),
        index8 p ((start + 1 + j : Nat) : Int) h = .ok (tail[j], h) := by
      intro j bound
      have later := reads (Nat.succ j) (by simp; omega)
      have pos : start + Nat.succ j = start + 1 + j := by omega
      rw [pos] at later
      simpa only [List.getElem_cons_succ] using later
    simp only [List.length_cons, List.range'_succ, List.forIn_cons, bind_app, first, pure_app]
    simpa only [List.push_append_toArray] using ih (start + 1) (out.push head) rest

/-- Public CString bytes determine the real C string read, at arbitrary
represented pointers and offsets, including the current external errno view. -/
theorem CString_reads {h : Heap} {p : BPtr} {xs : List UInt8}
    (string : CString h p xs) :
    strlenB p h = .ok (UInt64.ofNat xs.length, h) ∧
    ∀ j (bound : j < xs.length), index8 p j h = .ok (xs[j], h) := by
  rcases string with ⟨bytes, nonzero, fit⟩
  rcases bytes with ⟨null, impossible, _⟩ | ⟨r, off, a, pointer, get, bounds, content⟩
  · omega
  subst p
  have char : ∀ j, j < xs.length + 1 → a[off + j]? = (xs ++ [0])[j]? := by
    intro j bound
    have atIndex := congrArg (fun values : List UInt8 => values[j]?) content
    rw [List.getElem?_take_of_lt bound] at atIndex
    simpa only [List.getElem?_drop, Array.getElem?_toList] using atIndex.symm
  have zero : a[off + xs.length]? = some 0 := by
    simpa using char xs.length (by omega)
  have before : ∀ j, off ≤ j → j < off + xs.length → a[j]? ≠ some 0 := by
    intro j lower upper eqzero
    have atIndex := char (j - off) (by omega)
    rw [show off + (j - off) = j by omega, eqzero] at atIndex
    have zeroIn : 0 ∈ xs := by
      have inPrefix : (xs ++ [0])[j - off]? = xs[j - off]? :=
        List.getElem?_append_left (by omega)
      rw [inPrefix] at atIndex
      exact List.mem_of_getElem? atIndex.symm
    exact nonzero zeroIn
  have length := strlenB_ok get (by omega : off ≤ off + xs.length) zero before
  have reads : ∀ j (bound : j < xs.length),
      index8 (.ref r off) j h = .ok (xs[j], h) := by
    intro j bound
    have ij : off + j < a.size := by omega
    have value : a[off + j] = xs[j] := by
      have atIndex := char j (by omega)
      rw [List.getElem?_append_left bound] at atIndex
      simpa [ij, bound] using atIndex
    have actual := Ptr.index_ok get ij
    simpa only [OkOn, index8, value] using actual
  exact ⟨by simpa only [OkOn, Nat.add_sub_cancel_left] using length, reads⟩

/-- Actual strlen, including its unchanged heap, follows from caller bytes. -/
theorem strlenB_of_CString {h : Heap} {p : BPtr} {xs : List UInt8}
    (string : CString h p xs) : strlenB p h = .ok (UInt64.ofNat xs.length, h) :=
  (CString_reads string).1

/-- The actual character-copying loop reads exactly the caller CString bytes. -/
theorem cstring_of_CString {h : Heap} {p : BPtr} {xs : List UInt8}
    (string : CString h p xs) : cstring p h = .ok (xs.toArray, h) := by
  obtain ⟨length, reads⟩ := CString_reads string
  have loop := read_chars h p xs 0 #[] (by simpa using reads)
  have natLength : (UInt64.ofNat xs.length).toNat = xs.length :=
    UInt64.toNat_ofNat_of_lt string.2.2
  unfold cstring
  simp only [bind_app, length, natLength, Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [loop]
  simp

theorem heapStr_of_CString {h : Heap} {p : BPtr} {xs : List UInt8}
    (string : CString h p xs) : heapStr h p = some xs.toArray :=
  heapStr_of (cstring_of_CString string)

/-- A caller CString domain establishes the actual formatter read and exact
message bytes. The complete NUL-terminated output needs three extra bytes. -/
theorem format_error_message_CString {h : Heap} {path sep msg : BPtr} {xs es : List UInt8}
    (hp : CString h path xs) (hs : CString h sep [58,32]) (hm : CString h msg es) :
    formatBytes #[37,115,37,115,37,115] [.str path, .str sep, .str msg] h =
      .ok ((xs ++ [58,32] ++ es).toArray, h) ∧
    ((xs ++ [58,32] ++ es ++ [0]).toArray).size = xs.length + es.length + 3 := by
  refine ⟨?_, by simp; omega⟩
  simpa using formatBytes_sss (cstring_of_CString hp) (cstring_of_CString hs) (cstring_of_CString hm)

#print axioms CString_reads
#print axioms strlenB_of_CString
#print axioms heapStr_of_CString
#print axioms format_error_message_CString
#print axioms cstring_of_CString
#print axioms formatGo_sss
#print axioms formatBytes_sss
#print axioms format_error_message
end Zlib.GzFs.Proofs
