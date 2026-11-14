import ZlibF.Zlib.«gzclose.c»

namespace ZlibF.Spec.Public
open C Zlib.GzFs

/-!
# gz refusals: a `NULL` handle

Every gz function that takes a `gzFile` starts with `if (file == NULL) return <value>;` (`gzgets`:
`file == NULL || buf == NULL || len < 1`; `gzclose`, `gzseek`, `gztell`, `gzoffset`, `gzprintf` and
`gzgetc_` through the function they call). `Goal.gz_sequence_safety` runs only on a real handle,
so this goal states the `NULL` case: for every heap, every file-system world and every other
argument, the call returns its documented value, the heap is unchanged (nothing is allocated,
freed or written: `gzerror` does not write `*errnum`), and the world is unchanged (no descriptor,
no `errno`). The functions in the `M` monad do not see the world at all.

The values, from `zlib.h` and the C:

| function | value on `NULL` |
|---|---|
| `gzread`, `gzputc`, `gzputs`, `gzgetc`, `gzgetc_`, `gzungetc`, `gzbuffer`, `gzrewind` | `-1` |
| `gzseek`, `gzseek64`, `gztell`, `gztell64`, `gzoffset`, `gzoffset64` | `-1` |
| `gzfread`, `gzfwrite`, `gzwrite`, `gzdirect`, `gzeof` | `0` |
| `gzgets`, `gzerror` | `NULL` |
| `gzprintf`, `gzvprintf`, `gzflush`, `gzsetparams`, `gzclose`, `gzclose_r`, `gzclose_w` | `Z_STREAM_ERROR` |
| `gzclearerr` | nothing |

`gzvprintf` is declared by `zlib.h` under "undocumented functions"; the project's scope includes
it (`docs/progress.md`, Scope, result 5), and its refusal is the one of `gzprintf`.
-/

/-- **Refusal of a `NULL` handle** by every gz function of the public interface: the documented
value, the heap and the file-system world unchanged, for every heap, world and other argument.
No precondition. `gzprintf` and `gzvprintf` quantify over the argument list.

`gzgetc` is the function `(gzgetc)(file)`. The `gzgetc` macro of `zlib.h` reads `(g)->have` first,
so the macro on `NULL` is undefined behaviour in C; the translation `Zlib.Gzread.gzgetc` is the
function, and that is what is stated here. -/
def Goal.gz_refusal : Prop :=
  (∀ (fs : Fs) (h : Heap) buf len, Zlib.Gzread.gzread none buf len fs h = .ok ((-1, fs), h)) ∧
  (∀ (fs : Fs) (h : Heap) buf size nitems,
    Zlib.Gzread.gzfread buf size nitems none fs h = .ok ((0, fs), h)) ∧
  (∀ (fs : Fs) (h : Heap) buf len, Zlib.Gzwrite.gzwrite none buf len fs h = .ok ((0, fs), h)) ∧
  (∀ (fs : Fs) (h : Heap) buf size nitems,
    Zlib.Gzwrite.gzfwrite buf size nitems none fs h = .ok ((0, fs), h)) ∧
  (∀ (fs : Fs) (h : Heap) c, Zlib.Gzwrite.gzputc none c fs h = .ok ((-1, fs), h)) ∧
  (∀ (fs : Fs) (h : Heap) str, Zlib.Gzwrite.gzputs none str fs h = .ok ((-1, fs), h)) ∧
  (∀ (fs : Fs) (h : Heap) format (va : List VaArg),
    Zlib.Gzwrite.gzprintf none format va fs h = .ok ((Z_STREAM_ERROR, fs), h)) ∧
  (∀ (fs : Fs) (h : Heap) format (va : List VaArg),
    Zlib.Gzwrite.gzvprintf none format va fs h = .ok ((Z_STREAM_ERROR, fs), h)) ∧
  (∀ (fs : Fs) (h : Heap) flush,
    Zlib.Gzwrite.gzflush none flush fs h = .ok ((Z_STREAM_ERROR, fs), h)) ∧
  (∀ (fs : Fs) (h : Heap) level strategy,
    Zlib.Gzwrite.gzsetparams none level strategy fs h = .ok ((Z_STREAM_ERROR, fs), h)) ∧
  (∀ (fs : Fs) (h : Heap), Zlib.Gzread.gzgetc none fs h = .ok ((-1, fs), h)) ∧
  (∀ (fs : Fs) (h : Heap), Zlib.Gzread.gzgetc_ none fs h = .ok ((-1, fs), h)) ∧
  (∀ (fs : Fs) (h : Heap) c, Zlib.Gzread.gzungetc c none fs h = .ok ((-1, fs), h)) ∧
  (∀ (fs : Fs) (h : Heap) buf len, Zlib.Gzread.gzgets none buf len fs h = .ok ((.null, fs), h)) ∧
  (∀ (fs : Fs) (h : Heap), Zlib.Gzread.gzdirect none fs h = .ok ((0, fs), h)) ∧
  (∀ (fs : Fs) (h : Heap) offset whence,
    Zlib.Gzlib.gzseek none offset whence fs h = .ok ((-1, fs), h)) ∧
  (∀ (fs : Fs) (h : Heap) offset whence,
    Zlib.Gzlib.gzseek64 none offset whence fs h = .ok ((-1, fs), h)) ∧
  (∀ h : Heap, Zlib.Gzlib.gztell none h = .ok (-1, h)) ∧
  (∀ h : Heap, Zlib.Gzlib.gztell64 none h = .ok (-1, h)) ∧
  (∀ (fs : Fs) (h : Heap), Zlib.Gzlib.gzoffset none fs h = .ok ((-1, fs), h)) ∧
  (∀ (fs : Fs) (h : Heap), Zlib.Gzlib.gzoffset64 none fs h = .ok ((-1, fs), h)) ∧
  (∀ (fs : Fs) (h : Heap), Zlib.Gzlib.gzrewind none fs h = .ok ((-1, fs), h)) ∧
  (∀ h : Heap, Zlib.Gzlib.gzeof none h = .ok (0, h)) ∧
  (∀ (h : Heap) errnum, Zlib.Gzlib.gzerror none errnum h = .ok (.null, h)) ∧
  (∀ h : Heap, Zlib.Gzlib.gzclearerr none h = .ok ((), h)) ∧
  (∀ (h : Heap) size, Zlib.Gzlib.gzbuffer none size h = .ok (-1, h)) ∧
  (∀ (fs : Fs) (h : Heap), Zlib.Gzclose.gzclose none fs h = .ok ((Z_STREAM_ERROR, fs), h)) ∧
  (∀ (fs : Fs) (h : Heap), Zlib.Gzread.gzclose_r none fs h = .ok ((Z_STREAM_ERROR, fs), h)) ∧
  (∀ (fs : Fs) (h : Heap), Zlib.Gzwrite.gzclose_w none fs h = .ok ((Z_STREAM_ERROR, fs), h))

end ZlibF.Spec.Public
