import ZlibF.Zlib.«gzwrite.c»

/-!
# gzprintf with the handle's own error string faults in the model

The counterexample to the former argument domain of `gzprintf` and `gzvprintf` (`GzArguments`, which asked only
that the format and its arguments format correctly on the heap before the call). A public history in a world whose
`write` calls fail with `EAGAIN`:

1. `gzopen("p", "wT")`, `gzbuffer(file, 8)`: a transparent writer;
2. `gzwrite(file, buf, 16)`: the write stalls, so `again = 1`, `err = Z_ERRNO`, and `gz_error` allocates the
   message `"p: Resource temporarily unavailable"`;
3. `m = gzerror(file, NULL)`: the handle's own message, a valid C string on the heap before the next call;
4. `gzprintf(file, "%s", m)`: `gzvprintf` passes its check (a stalled write), calls `gz_error(state, Z_OK, NULL)`,
   which frees the message, and then formats `m`: a fault (`Fault.ub`), where the C reads freed memory
   (`tests/regression/gzprintf-error-string`).

So the old statement of `gzvprintf_step` was false. The corrected `GzArguments` asks that the format and every `%s`
argument lie apart from the blocks the handle owns.
-/

namespace Zlib.Gzwrite.PrintfErrorStringRegression
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzwrite

/-- Block 0 the path `"p"`, block 1 the mode `"wT"`, block 2 the format `"%s"`, block 3 a 16-byte buffer. -/
def callerHeap (statics : Statics) : Heap :=
  { Heap.empty with bytes := ⟨#[some #[112, 0], some #[119, 84, 0], some #[37, 115, 0], some (Array.replicate 16 98)]⟩
                    ro := ⟨#[false, false, false, false]⟩
                    nextBlk := 4, static := statics }

/-- Every `write` fails with `EAGAIN`. -/
def stallFs : Fs := { fsizeLimit := 2 ^ 20, writeChoice := fun _ => .fail EAGAIN }

/-- The history up to `gzerror`: the handle and its message. -/
def prefixRun : G (GzFilePtr × BPtr) := do
  let file ← gzopen (.ref (.blk 0) 0) (.ref (.blk 1) 0)
  let _ ← StateT.lift (gzbuffer file 8)
  let _ ← gzwrite file (.ref (.blk 3) 0) 16
  let m ← StateT.lift (gzerror file .null)
  return (file, m)

set_option maxRecDepth 40000 in
/-- **The history**: it returns; after the stalled write the message is a C string on the heap, and `gzprintf` with it
as its `%s` argument faults. -/
theorem printf_own_message_faults (statics : Statics) :
    (∃ r, prefixRun stallFs (callerHeap statics) = .ok r) ∧
    ∀ file m fs1 h1, prefixRun stallFs (callerHeap statics) = .ok (((file, m), fs1), h1) →
      (∃ text, cstring m h1 = .ok (text, h1)) ∧
      ∃ e, gzprintf file (.ref (.blk 2) 0) [.str m] fs1 h1 = .error e ∧ e ≠ .outOfFuel := by
  have e1 : prefixRun stallFs (callerHeap statics) = prefixRun stallFs (callerHeap statics) := rfl
  conv at e1 => rhs; cbv
  refine ⟨⟨_, e1⟩, ?_⟩
  intro file m fs1 h1 hr
  rw [e1] at hr
  injection hr with hr
  injection hr with hr hh
  injection hr with hr hfs
  injection hr with hf hm
  subst hf hm hfs hh
  exact ⟨⟨_, by conv => lhs; cbv⟩, ⟨_, by conv => lhs; cbv, by decide⟩⟩

end Zlib.Gzwrite.PrintfErrorStringRegression
