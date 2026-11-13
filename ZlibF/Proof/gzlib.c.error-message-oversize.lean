import ZlibF.Proof.«gzlib.c.error-message-refusal»

/-! # gz_error: the message request above PTRDIFF_MAX

`gz_error` asks `malloc` for `strlen(state->path) + strlen(msg) + 3` bytes. When that sum is at or above
`PTRDIFF_MAX + 1 = 2^63`, glibc returns NULL whatever the memory state, and `gz_error` takes its `Z_MEM_ERROR`
path: the state ends with `msg = NULL` and `err = Z_MEM_ERROR`, no block is created, and one allocator call is
counted. The heap is the one an allocation failure leaves (`MessageRefusal.refusedMessageHeap`).

The proof unfolds the runtime allocator itself; it does not use the size lemmas of `PlatformMemory`, so a runtime
mutant that drops the size test fails here on its own. Each string and its NUL are below `2^63` bytes, as the
platform scope gives for a string in one byte object, so the `size_t` sum does not wrap (two strings of
`2^63 − 1` bytes would wrap it to 1).
-/
namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzlib.Spec
open ZlibF.Spec.Public Zlib.Gzlib.MessageRefusal

private theorem oversize_view_setS (h : Heap) (i : Nat) (s : GzState) (r : BRef) :
    Space.get (setS h i s) r = Space.get h r := by
  cases r <;> rfl

private theorem oversize_strlenB_setS (h : Heap) (i : Nat) (s : GzState) (p : BPtr) :
    strlenB p (setS h i s) = match strlenB p h with
      | .error e => .error e
      | .ok (n, _) => .ok (n, setS h i s) := by
  cases p with
  | null => rfl
  | ref r off =>
    simp only [strlenB, oversize_view_setS]
    cases he : Space.get h r with
    | none => rfl
    | some a =>
      dsimp only
      cases hl : strlenFrom a off <;> simp only [hl]

private theorem oversize_cstring_nonnull {h : Heap} {p : BPtr} {xs : List UInt8} (hc : CString h p xs) :
    p ≠ .null := by
  intro hp
  rcases hc.1 with hn | ⟨r, off, a, he, _⟩
  · have := hn.2.1; omega
  · rw [hp] at he; cases he

/-- `void ZLIB_INTERNAL gz_error(gz_statep state, int err, const char *msg)`, the `Z_MEM_ERROR` path of an
oversized message. For a state with no old message, every error code other than `Z_MEM_ERROR`, a path and a
message that are C strings each lying with its NUL in fewer than `2^63` bytes, and a request `strlen(path) + strlen(msg) + 3` of at
least `2^63` bytes: `malloc` refuses the request whatever the allocation oracle says, and `gz_error` returns with
`msg = NULL` and `err = Z_MEM_ERROR`, one allocator call counted and no block created. -/
theorem gz_error_oversize_run {h : Heap} {i : Nat} {s : GzState} {err : Int32} {msg : BPtr}
    {pathText errorText : List UInt8} (hs : h.gzstates i = some s) (hm : s.msg = .null)
    (hp : CString h s.path pathText) (he : CString h msg errorText) (herr : err ≠ Z_MEM_ERROR)
    (pathSmall : pathText.length + 1 < 2 ^ 63) (errorSmall : errorText.length + 1 < 2 ^ 63)
    (big : 2 ^ 63 ≤ pathText.length + errorText.length + 3) :
    gz_error (some (.tab i)) err msg h = .ok ((), refusedMessageHeap h i s) := by
  have hp0 := Zlib.GzFs.Proofs.strlenB_of_CString hp
  have he0 := Zlib.GzFs.Proofs.strlenB_of_CString he
  have hp1 : strlenB s.path (setS h i { s with err := err }) =
      .ok (UInt64.ofNat pathText.length, setS h i { s with err := err }) := by
    rw [oversize_strlenB_setS, hp0]
  have he1 : strlenB msg (setS h i { s with err := err }) =
      .ok (UInt64.ofNat errorText.length, setS h i { s with err := err }) := by
    rw [oversize_strlenB_setS, he0]
  simp only [setS, hm] at hp1 he1
  have hn := oversize_cstring_nonnull he
  -- The `size_t` sum `strlen(path) + strlen(msg) + 3`, in the form `simp` gives it; it does not wrap.
  have hrefuse : ¬ ((pathText.length % 18446744073709551616 + errorText.length % 18446744073709551616 + 3) %
      18446744073709551616 < C.mallocLimit) := by
    unfold C.mallocLimit; omega
  have herr' : (err == Z_MEM_ERROR) = false := by simpa using herr
  simp [gz_error, bind_app, ldS_eq, updS_eq, hs, hm, hn, hp1, he1, herr', hrefuse,
    allocB, refusedMessageHeap, refusedMessageState, setS, upd_upd]

#print axioms gz_error_oversize_run
end Zlib.Gzlib.Proofs
