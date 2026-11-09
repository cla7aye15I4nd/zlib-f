import ZlibF.Math.«libc-errno-text»
import ZlibF.Proof.LibcBorrow
import ZlibF.Proof.«gzfs.borrowed-error»
import ZlibF.Spec.Public.History

/-! The actual active libc error view satisfies the original CString predicate. -/
namespace C.LibcBorrow
open ZlibF.Spec.Public
set_option autoImplicit false

/-- The current borrow has its exact full text and one trailing NUL. No
additional errno restriction or caller CString premise is required. -/
theorem current_cstring (h : Heap) (epoch : Nat) (e : Int32)
    (current : h.libcErrorBorrow = some (epoch, e)) :
    CString h (.ref (.str (libcErrnoIndex epoch e)) 0)
      (libcErrnoText e).toUTF8.data.toList := by
  have get := (current_view h epoch e current).1
  have small := LibcStrings.Proofs.errno_bytes_lt64 e
  refine ⟨Or.inr ⟨.str (libcErrnoIndex epoch e), 0, strBytes (libcErrnoText e),
    rfl, get, ?_, ?_⟩, LibcStrings.Proofs.errno_text_nonzero e, ?_⟩
  · simp [strBytes]
  · simp only [strBytes, Array.toList_push, List.drop_zero]
    symm
    apply List.take_of_length_le
    simp
  · simp only [strBytes, Array.size_push] at small
    simp only [Array.length_toList]
    omega

#print axioms current_cstring
end C.LibcBorrow

namespace Zlib.GzFs.Proofs
open C Zlib.GzFs ZlibF.Spec.Public
set_option autoImplicit false

/-- The pointer returned by the same actual strerror execution is a full
CString on its returned heap, for every signed errno and previous borrow. -/
theorem zstrerror_cstring {h after : Heap} {fs fs' : Fs} {p : BPtr}
    (run : zstrerror fs h = .ok ((p, fs'), after)) :
    CString after p (strerrorText fs.errno).toUTF8.data.toList := by
  rw [zstrerror_run] at run
  cases run
  exact C.LibcBorrow.current_cstring _ _ _ rfl

#print axioms zstrerror_cstring
end Zlib.GzFs.Proofs
