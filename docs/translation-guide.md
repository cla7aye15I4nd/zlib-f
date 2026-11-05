# Translation guide: zlib C to Lean 4, on the object heap

Everyone who translates a C file follows this guide, so that the whole library uses one vocabulary. The
translation is trusted (see [trusted-base.md](trusted-base.md)) and locked (see [anti-cheating.md](anti-cheating.md)):
a translation that is easier to prove but differs from the C is a bug. If a proof is hard, say so; never change the translation.

The runtime is the object heap of [pilot.md](pilot.md). The file rule is `zlib/X.c` to `ZlibF/Zlib/X.c.lean`,
and `zlib/X.h` to `ZlibF/Zlib/X.h.lean`.

## Configuration

The default x86_64 Linux build (`./configure --static`, LP64). When in doubt, preprocess with
`gcc -E -P` on the verified source (the `zlib/` submodule with `patches/*.patch` applied) and translate what remains.

## Fidelity

1. **Statement for statement.** Same names, same control flow, same evaluation order, macros expanded in source order.
   No optimisation and no restructuring beyond what the rules below require. Comment each block with the C it translates.
2. **One `def` per C function.** The first line of the docstring is the exact C signature in backticks. A `static` helper
   gets its own `def`, with the `local` or `static` in the signature.
3. **Every undefined behaviour the code can reach is a fault** (`Fault.ub`): signed overflow, an invalid shift, an access
   outside an object, a null or freed pointer, a pointer outside its array, a relational comparison of unrelated
   pointers, a store into a read-only object, overlapping `memcpy`. Unsigned arithmetic wraps.
4. **Types.** `unsigned char` is `UInt8`, `unsigned short` is `UInt16`, `unsigned` is `UInt32`, `unsigned long`, `size_t` and
   `z_size_t` are `UInt64`, `int` is `Int32`, `long`, `z_off_t`, `z_off64_t` are `Int64`. Apply the integer promotions and the
   usual arithmetic conversions explicitly (an `ush` plus an `int` is computed in `int`).
5. **Uninitialised memory.** Reading an uninitialised integer returns an arbitrary value, and the theorems hold for every
   value. A pointer in fresh memory is NULL in the model, so reading one is **not** a fault; using it as an address is.
   When a function reads a pointer field of a record that `ZALLOC` made, the translation comment names the statement
   that wrote it earlier ([safety.md](safety.md), section 3). `zmemzero` of a record is `X.zeroed` (all integers 0,
   all pointers NULL); `X.garbage` is for the content of fresh memory.
6. **Constants.** An enumerator is `X : UInt32` (right for a comparison with the `mode` field or a `type` argument)
   and `X_i : Int32` (its C type `int`; use it where it meets an `int`). A macro whose name is also an enumerator is
   `GZ_<name>`: `GZ_COPY` is the `COPY` of `gzguts.h`, and `COPY` is the enumerator of `inflate.h`.
7. **Array lengths.** The record types do not enforce the length of an array field. A theorem about a record states
   `WellFormed` (or `Heap.RecordsWellFormed`) as a hypothesis, and the invariant it preserves implies it.
8. **Block numbers.** `allocB`, `allocW`, `allocBytes`, `allocBytesRO` and `allocK` write under `nextBlk` and fault if that
   number is in use; a theorem about code that allocates carries `Fresh`, and the rules take `h.slotUsed h.nextBlk = false`
   (the tactic `fresh_slot` finds it from `Fresh h`).

## Memory: where each C object lives

| In C | In Lean |
| --- | --- |
| a struct (`z_stream`, `deflate_state`, `inflate_state`, `gz_state`, ...) | a record in the table of its kind (`streams`, `dstates`, `istates`, `gzstates`, ...), referred to by its block number |
| `p->f`, `p->f = v` | a read or a write of the field `f` of the record; no offset arithmetic |
| an array that is a field of a struct (`codes[ENOUGH]`, `lens[320]`, `dyn_ltree[...]`) | an `Array` field of the record. Copying the struct copies it |
| a pointer into such an array (`state->next`, `lencode`) | a constructor of the pointer type: the struct and an index. No address |
| a byte buffer (caller's `next_in`, `next_out`, `window`, `pending_buf`, gz buffers) | a block in the `bytes` table; a pointer is a block number and an offset |
| an array of `ush` (`head`, `prev`) | a block in the `words` table |
| a static table (`lenfix`, `distfix`, `_dist_code`, `crc_table`, ...) | a constant; a pointer to it is a constructor, a store through it is a fault |
| a local whose address is taken (`&stream`, `&got`) | a block or record allocated at its declaration and freed before every return, so a dangling use is a fault |
| a string literal (`"out of memory"`, `ZLIB_VERSION`) | `strLitRef "..."` (`Zutil.strLit`): the pointer to a static read-only array, the same every time, no allocation; the text must be a literal of the sources (`strTable`) |
| `ZALLOC`, `ZFREE` | `alloc` and `free` with the default allocator. A custom allocator is `ub "custom allocator not modelled"` for now |
| `zmemcpy`, `memcpy` of bytes | `memcpyB`: both ranges inside their blocks, the ranges disjoint. A whole-struct `memcpy` between two different objects is `copyK dst src` (it faults on the same object); `ldK` followed by `stK` does not check this |
| `zmemzero`, `memset` of bytes | `memsetB`. An array of wider elements: `Ptr.fill p 0 n` for zero, `Ptr.memset p c n` for another byte (every byte of each element is `c`). A whole struct: `stK p X.zeroed` |

The functions of the C library (`memcpy`, `memmove`, `memset`, `strlen`, `malloc`, `free`, string literals) are modelled in
`ZlibF/Runtime/Libc.lean`, and `malloc`, `free`, `memcpy` of a whole record in the generated `LibcTables.lean`.
[trusted-base.md](trusted-base.md), item 2, lists which are modelled and how each differs from the real function.
Everything else in `Runtime/` (`Space`, `Monad`, `Ptr`, `Tables`) is the C language: pointers, arithmetic, loops, the
heap tables.

The schema (the record of every struct, with all its fields in declaration order, and the static tables) is generated
from the C headers by a script, not written by hand, and lives in `ZlibF/Runtime/`. A translator asks for a new struct
or field to be added there; it does not define its own.

## Control flow

- A loop is a recursion on an explicit state record, or a `while` combinator of the runtime over the loop-carried locals.
  The measure that shows termination is part of the translation when the C bounds the loop by a counter.
- `break`, `continue`, an early `return` inside a loop: carry a control tag in the loop state.
- `goto` and a `switch` with fall-through: an explicit state machine (a program counter in the loop state). Document the mapping
  from labels to states in a comment at the top of the function.
- A `do ... while (cond)` is a loop that runs its body first.

## What a translator delivers

1. `ZlibF/Zlib/X.c.lean`, with every function of `X.c` and the header content it needs.
2. A differential test for every function (`tests/`): the Lean translation and the real C agree on the inputs of the test.
3. The result of the audit and of the differential tests, pasted into the pull request. Nothing else counts.
4. A list of the places where the translation needed a decision (a label mapping, a conversion, a modelled library call), each with
   the C line.

A translation is not proved correct by any of this. It is **evidence** that it matches the C, and the reviewer reads it against the C.
