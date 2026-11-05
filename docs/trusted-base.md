# Trusted base

A theorem here is only as good as the following, which the kernel does not check.

1. **Lean kernel** and the three standard axioms `propext`, `Classical.choice`,
   `Quot.sound` (enforced by `tests/audit/Audit.lean`).
2. **The runtime** (`ZlibF/Runtime/`) and the schema it runs on. The hand-written part is `Space.lean` (pointers,
   the update of a table), `Monad.lean` (faults, the monad, loops), `Ptr.lean` (pointer arithmetic, loads, stores,
   `memcpy`, `memset`, `strlen` on arrays) and `Alloc.lean` (`malloc` and `free` of blocks). The generated part is
   `Schema.lean` (the record of every struct, the heap, the constants) and `Tables.lean` (load, store, allocate and
   free per struct kind); both come from the C headers through `scripts/gen_schema.py`, and
   [runtime-schema.md](runtime-schema.md) lists every field and the reason for its Lean type. The heap is one table
   per kind of object; a freed block number is never reused, so a use after free and a double free are faults. Every
   undefined behaviour reachable in C becomes `Fault.ub`, with the exceptions listed below. Unsigned arithmetic is
   modular, signed arithmetic is checked by each translation, not by the monad. Loops run on a fuel bound of `2^64`;
   running out is a fault that the theorems rule out. A read of an uninitialised integer returns an arbitrary value
   (theorems hold for all values: `Heap.garbage`). The contents of the static tables are a field of the heap
   (`Statics`) that the translation of the defining file fixes.

   **Tables and in-place update.** A table of the heap (`Heap.bytes`, `words`, `ro` and one per struct kind) is a
   `Tbl`: a structure around an `Array`, read as a function of the block number (a coercion; the entry is `default`,
   that is `none` or `false`, beyond the end). `upd t k v` is the update; `upd_same`, `upd_ne`, `upd_apply`, `upd_upd`,
   `upd_self` are its rules, proved from `Tbl.get_set`. The proofs reason about `h.bytes b` and `upd` as before. The
   reason for the structure is execution: with a function as table, every store added a closure around the old table,
   the old array stayed reachable and was copied on the next store, so memory grew with the square of the block size
   (a 70000-byte `uncompress` needed more than 6 GB) and a lookup walked all earlier updates. The primitives that write
   (`Ptr.store`, `Ptr.memcpy`, `Ptr.memmove`, `Ptr.fill`) call `Space.modify`, which takes the array out of the table,
   changes it and puts it back (`Array.modify`), so a heap that is used linearly is updated in place. `Space.modify_eq`
   (a field of the class, proved for every reference type) says that `modify h r f` is `put h r (f a)` for a live array
   `a`, and `Ptr.store_ok`, `memcpy_ok`, `memmove_ok`, `fill_ok` are stated and proved with `put` as before. What to
   check in review: `Tbl.get_set`, `Tbl.modify_eq` (`Space.lean`) and the generated `modify` and `modify_eq` of each
   `Space` instance. Measured on the 64 KB block benchmark (`tests/lean/Driver/Bench.lean`, `bench_store`): 10000
   stores took 6.4 GB and 0.5 s before, 11 MB and 0.01 s after; 10^7 stores take 1.5 s and 11 MB. `adler32_z` and
   `crc32_z` over 1 MiB take 0.12 s and 36 MB; `uncompress` of a 70000-byte result takes 36 MB.

   **Limitations and decisions.** Each one is a place where the model differs from C. A theorem is sound for C only
   with the stated care.

   * *Uninitialised pointers are NULL (gap).* In C a pointer read from fresh memory is indeterminate. A fresh record
     (`allocK`, `X.garbage`) has NULL in every pointer field and the runtime does not notice that the field was never
     written: `p == NULL`, `free(p)` and copying `p` succeed. The proof must show that every pointer field it reads was
     written first. zlib zeroes the deflate and inflate states right after allocation; other records (`gz_state`)
     are checked by hand. Closing the gap needs a distinct "uninitialised" pointer value in `Ptr`, in the
     `Option SRef` pointers and in `FnPtr`, a faulting equality test for pointers, and a rewrite of every match on
     `Ptr` in the translations; it is not done.
   * *`NULL + 0` is allowed (decision).* C17 leaves it undefined and C23 defines it; the model allows it
     (`Ptr.add_null_zero`), and a proof may use that fact. `NULL - NULL` is a fault.
   * *Array lengths are not enforced.* A record field of type `Array` has any length. `WellFormed` and
     `Heap.RecordsWellFormed` state the declared lengths; a theorem carries them and the generated lemmas
     (`Heap.RecordsWellFormed.set_*`, `clear_*`, `*.put_*_wf`) show that the primitives keep them. The static tables
     have `Statics.WellFormed` for their lengths; their values are fixed by the translation (generated from the C
     tables) and are not compared with the C by the runtime.
   * *Block numbers (`Fresh`).* `allocB`, `allocW`, `allocBytes`, `allocBytesRO` and `allocK` write under `nextBlk` and
     fault if some table already uses that number, so they never overwrite a live object. The fault is not a C behaviour:
     it says that the heap is not `Fresh`, and every theorem about code that allocates carries `Fresh`. The heap has to
     be built so that no number below `nextBlk` is used in two tables (`Fresh` only speaks of the numbers from `nextBlk`
     on). The names with the suffix `Chk` are aliases.
   * *String literals.* A literal is the static array `BRef.str i` (the text of `strTable[i]` and a NUL): read-only,
     always live, never freed, in no table of the heap, unaffected by `nextBlk`, and the same pointer every time
     (`strLitRef`). `strTable` is the closed list of the string literals of the library sources (generated; the list is
     in `runtime-schema.md`). A text outside the list is a fault. Literals of other origin (the text of `strerror`) are
     not covered and use `allocBytesRO`.
   * *Read-only marking (decision).* Only byte blocks (`Heap.ro`) and the static tables and instances can be read-only.
     A block of 16-bit words or a record in a table cannot; zlib has no such object.
   * *Pointer equality (decision).* `p == q` for pointers into different arrays is false (DecidableEq of `Ptr`). In C a
     one-past-the-end pointer of one object may compare equal to the start of another, and the result is unspecified.
     Equality of a dangling pointer is not a fault. A proof must not branch on the equality of pointers into different
     objects.
   * *One value per uninitialised cell (decision).* The content of fresh memory is a function of the allocation call
     and the position, so two reads of one cell agree. In C they may differ. A proof must not rely on the equality of
     two reads of an uninitialised cell (`slide_hash` and `longest_match` do not).
   * *Whole-struct copies (rule).* `ldK` followed by `stK` copies a record without an overlap check; `memcpy(s, s, n)`
     is undefined in C. `copyK dst src` faults when both denote the same object, and a translation of `zmemcpy` of a
     whole struct uses it. There is no record-level `zmemset` primitive: use `stK p X.zeroed`.
   * *Smaller points.* `Ptr.add` checks the result only, so a pointer built by hand outside its array is not caught
     (`Ptr.ref` is a public constructor; no translation forms such a pointer). A block made by `allocBytes` can be freed
     by zlib code (there is no allocation-origin tag). `Ptr.fill` sets elements to a value; it is `memset` only for
     bytes or the value 0, and `Ptr.memset` replicates a byte. A loop that runs `2^64` times is a fault.
     A cast between the two kinds of state faults at the cast, in C at the access.
3. **The translation** (`ZlibF/Zlib/*.c.lean`) matches the C. It is written by hand,
   statement by statement. A mismatch is a translation bug, never fixed to ease
   a proof. Differential tests against the real C (`tests/`) are evidence, not proof;
   the translation guide requires one for every function, and the groups of tests are listed in `tests/list.txt`.
4. **The source** is `zlib/` at the pinned commit plus `patches/*.patch`. A
   patch exists only for a confirmed zlib bug that blocks a proof and matches an
   upstream pull request. Current: `0003-adler32-null-one.patch`
   ([madler/zlib#1364](https://github.com/madler/zlib/pull/1364)), which moves the
   `Z_NULL` check of `adler32_z` before the `len == 1` fast path.
5. **Memory model scope:** the target is LP64; allocation and typed objects are
   modelled only as far as translated functions need them.
6. **The statements.** The kernel checks that a proof proves its theorem. It does not check that
   the theorem says what [spec/](spec/index.md) says. Each theorem's docstring names the
   specification identifiers it formalises, and a reviewer reads statements, not proofs.
