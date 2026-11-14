import ZlibF.Proof.«gzwrite.c.printf-error-string-regression»

/-!
# gzprintf with the handle's own error string

`GzArguments` of `gzprintf` and `gzvprintf` used to ask only that the format and its arguments format correctly on
the heap before the call. That admitted the string `gzerror` returns, which is the handle's own message: the call
frees it (`gz_error(state, Z_OK, NULL)`) before it formats the arguments, a fault in the model and a use after free in
the C (`tests/regression/gzprintf-error-string`). The history runs in `ZlibF/Proof/gzwrite.c.printf-error-string-regression.lean`
(built with the library); this file restates the result. The corrected `GzArguments` asks that the format and every
`%s` argument lie apart from the blocks the handle owns.
-/
open C Zlib.GzFs Zlib.Gzwrite Zlib.Gzwrite.PrintfErrorStringRegression

/-- The history returns; after the stalled write the handle's message is a C string, and
`gzprintf(file, "%s", message)` faults. -/
theorem regression_printf_own_message (statics : Statics) :
    (∃ r, prefixRun stallFs (callerHeap statics) = .ok r) ∧
    ∀ file m fs1 h1, prefixRun stallFs (callerHeap statics) = .ok (((file, m), fs1), h1) →
      (∃ text, cstring m h1 = .ok (text, h1)) ∧
      ∃ e, gzprintf file (.ref (.blk 2) 0) [.str m] fs1 h1 = .error e ∧ e ≠ .outOfFuel :=
  printf_own_message_faults statics

#print axioms regression_printf_own_message
