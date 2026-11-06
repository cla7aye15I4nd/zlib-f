# Review of the trusted runtime

Scope: `ZlibF/Runtime/*.lean` (Space, Monad, Ptr, Alloc, Tables, Schema), `scripts/gen_schema.py`, `docs/runtime-schema.md`,
`docs/trusted-base.md`, `docs/safety.md`, `docs/translation-guide.md`, read against the pinned zlib sources (`zlib.h`,
`deflate.h`, `inflate.h`, `inftrees.h`, `gzguts.h`, `zutil.h`, `zconf.h`, `deflate.c`, `inflate.c`, `trees.c`, `uncompr.c`).

Method: source reading followed by an adversarial pass over the same files and brief.
Every retained claim was checked against the code before it was kept; claims that could not be checked from the files are marked unconfirmed. These historical notes are not independent baseline approval. No Lean build was run, so
"confirmed" means "follows from the definitions and the C text", not "a theorem was compiled". Nothing in the workspace
was edited. Severity measures damage to the claim "a successful run implies no C undefined behaviour"
(High: a materially false safety argument becomes possible; Medium: needs one more mistake in a translation or theorem,
or gives wrong C semantics; Low: completeness, spurious fault or documentation).

Summary: no primitive was found that makes a false `.ok` unavoidable for a well-formed heap. The monad and the loop
rules do not swallow faults. The gaps are at the edges: pointer values that are not tracked (uninitialised pointers,
`NULL + 0`), representation invariants the types do not enforce, schema constants with the wrong C meaning, and
documents that promise more than the code does.

## Findings (confirmed)

### R1. Uninitialised pointers are null, and the documents say they fault
Severity: High for the claim, Medium for zlib today. Locations: `Schema.lean` (`ZStream.garbage` and the other
`*.garbage` records: `next_in := default`, `state := default`, ...), `Space.lean` (`Inhabited (Ptr R)` is `null`),
`Tables.lean` (`allocK` stores `K.garbage`), against `docs/safety.md` section 3 ("A read of an uninitialised pointer is a
fault") and `docs/translation-guide.md` item 5. `docs/runtime-schema.md` ("a comparison with `NULL` is not a fault")
states the opposite, so the documents contradict each other and the code follows the weaker one.
Why wrong: a pointer read from fresh `malloc` memory is indeterminate in C. The model gives a valid null, so
`free(s->next_in)` or `if (s->window == NULL)` on a fresh record succeeds and takes the null path.
```c
z_stream *s = malloc(sizeof *s);
if (s) { free(s->next_in); free(s); }   /* indeterminate pointer passed to free */
```
`allocZStream`, `ldZStream`, `freeB s.next_in` all succeed for every garbage oracle. Quantifying over integer garbage does
not cover this. Limit on reach: this zlib zeroes both states right after allocation (`deflate.c` `zmemzero(s, sizeof(deflate_state))`,
`inflate.c` `zmemzero(state, sizeof(struct inflate_state))`), so these two paths are fine if the zero is translated. Other
allocated records (`gz_state` in `gzlib.c`, and any new one) are not checked here. Fix: either add a per-field
"initialised" mark for pointer fields (fault when a pointer is used before it is written), or make fresh records carry an
explicit `uninit` pointer constructor, and align the three documents.

### R2. `NULL + 0` is accepted (decided; recorded for completeness)
Severity: Low (known decision). `Ptr.lean` `Ptr.add` and `Ptr.add_null_zero`.
In C up to C17, `NULL + 0` is undefined; C23 defines it. gcc and clang may also derive "p is not null" from `p + n`
under `-fno-delete-null-pointer-checks`-off defaults, so code that adds to a pointer and then tests it against NULL can
be compiled differently. Counterexample: `unsigned char *p = NULL; p = p + 0; if (!p) ...`. A proof can use
`Ptr.add_null_zero` as a fact. This is the project's decision; the point here is only that the exact-UB claim in
`trusted-base.md` ("Every undefined behaviour reachable in C becomes `Fault.ub`") should name this exception. Unrelated
to this, `Ptr.diff null null` faults although C23 defines `NULL - NULL` as 0 (spurious fault, harmless).

### R3. Schema constant `COPY` has the wrong value for the gzip code
Severity: High if used, Medium by reach. `Schema.lean` line `def COPY : UInt32 := 16195`; the generator drops the macro
because the name is already an enumerator (`gen_schema.py` skips a macro whose name is in `enumerators`, and the skipped
list in `Schema.lean` names `COPY`, which its comment calls "not an integer constant expression"). The C has two meanings:
`inflate.h` enumerator `COPY` (16195) and `gzguts.h` `#define COPY 1` for `state->how`.
```c
state->how = COPY;   /* gzread.c: assigns the int 1 */
```
A translation of `gzread.c` that uses the schema name stores 16195 as an `Int32`-typed constant of the wrong type and value,
and the proof then checks the wrong state machine. `GZIP` has the same shape (macro 2 in `gzguts.h`, an empty feature flag in
`deflate.h`); its numeric value is right for the gzip files. Fix: emit per-translation-unit constants or distinct names.

### R4. Enumerator constants are given an unsigned type; in C they are `int`
Severity: Medium. `Schema.lean` ("Enumerators" block: `def HEAD : UInt32 := 16180`, `CODES`, ...) and
`docs/runtime-schema.md` (enum rule). Enumeration constants have type `int` (C11 6.7.2.2); only the object of enum type may
be `unsigned int` under gcc. The values all agree with `inflate.h` and `inftrees.h` (checked: 3 + 32 values).
```c
int x = -1;  int b = x < HEAD;   /* int < int: true */
```
With `HEAD : UInt32` the comparison is unsigned and false; `-CODES`, `HEAD - 20000` also differ. The `mode` field is correctly
`UInt32` (storage); the constants should be `Int32`, with a cast where they meet a `mode` value.

### R5. Array lengths are comments, not invariants; static tables default to empty
Severity: Medium. `Schema.lean` (`lens : Array UInt16 -- unsigned short[320]`, `codes`, `dyn_ltree`, ..., `Statics` fields
`:= #[]`) and `Tables.lean` (`stK` accepts any record). Only the `garbage` constructors build the right sizes. A record
stored with `lens.size = 321` makes `Ptr.load (.ref (.istate_lens id) 320)` succeed, while `s->lens[320]` is out of bounds in C.
A theorem is safe only if its invariant states every array length; nothing in the runtime enforces it. For `Statics` the
default heap has empty tables, so a theorem about `crc32` on `Heap.empty` faults (conservative), and a theorem that assumes
`h.static.crc_table = #[0,0]` is satisfiable (the table is wrong but the hypothesis holds). Fix: a generated `WellFormed`
predicate (all array sizes) that every record-store lemma preserves, and one generated canonical `Statics` value checked
against the C tables.

### R6. Allocation requires `Fresh`, and nothing in `M` enforces it
Severity: Medium (conditional). `Alloc.lean` `allocB`/`allocW`, `Tables.lean` `allocK`, `Schema.lean` `Fresh`.
Every allocator writes `upd table nextBlk (some ...)` without testing that the number is unused, and `allocB_owns` does not
need `Fresh`. Counterexample: `bytes 0 = some #[7]`, `nextBlk = 0`, oracle true: `allocB 1` overwrites the live block and
turns a read-only block writable (`ro := upd h.ro nextBlk false`). From `Heap.empty` the intended primitives keep `Fresh`,
so this matters only for a theorem or witness that starts from an arbitrary heap without `Fresh`. Every top-level theorem
must carry `Fresh` (and uniqueness of a block number across tables, which `Fresh` does not give for numbers below
`nextBlk`); state this in `trusted-base.md`.

### R7. Read-only marking exists only for byte blocks and named statics
Severity: Medium (low for zlib). `Schema.lean`: `Space ... WRef` has `ro _ r := false` for `.blk`; `ZStreamRef.isRo` and the
other record refs are `false` for every table constructor; `Heap.ro` is a table for bytes only; `freeW` ignores it.
`const unsigned short a[1] = {0}; ((unsigned short *)a)[0] = 1;` modelled as a `words` block succeeds. zlib has no such object
today; a harness or a witness that needs one cannot express it.

### R8. Pointer equality of different arrays is always false
Severity: Low to Medium. `Ptr` derives `DecidableEq`; `p == q` for `ref r1 o1` and `ref r2 o2` with `r1 ≠ r2` is false.
In C, comparing a one-past-the-end pointer of one object with the start of an adjacent object is unspecified and may be
true. A proof that branches on such an equality (for example `next_out == end`) can rely on an outcome the compiler need
not give. Equality of a dangling pointer is also not a fault (the pointer value is indeterminate after free in C).
Fix: an `eq` primitive that faults (or returns an arbitrary value) when the two pointers are one-past-end of one array and
start of another.

### R9. Uninitialised integers: one fixed value per cell
Severity: Medium (the semantic choice, not a bug). `Alloc.lean` fills `Junk.of (h.garbage nalloc i)`; a cell then behaves as an
ordinary value. In C an unspecified value may differ between two reads (DR 260, DR 451), and the compiler may treat a
branch on it as it likes. A proof that reads the same uninitialised cell twice and uses that the two reads are equal is
sound in the model and not in C. `slide_hash` and `longest_match` do not do this today. Also `docs/safety.md` sections 3 and 4
describe a ghost "initialised" bit that `memcpy` copies; the code has no such table (documentation mismatch, see R12).

### R10. Whole-struct copies have no overlap or provenance check
Severity: Medium (translation rule). `docs/translation-guide.md` ("A whole-struct `memcpy` is a value copy") and
`Tables.lean` (`ldK` then `stK`). `memcpy(s, s, sizeof *s)` is undefined in C, and `ldZStream s >>= stZStream s` succeeds.
The real uses are `deflateCopy` and `inflateCopy` with distinct objects (`zmemcpy(ds, ss, sizeof(deflate_state))`,
`zmemcpy(copy, state, sizeof(struct inflate_state))`), so there is no wrong result today, but the rule
should demand a `copyK src dst` primitive that faults when the two refs are equal or one lies inside the other
(`in_gzstate_strm i` against `tab j`). The same applies to `zmemzero` of a whole struct (`deflate.c`, `inflate.c`):
there is no record-level zero primitive; the translation has to write the zero record by hand, so it must be reviewed
for completeness of the zero.

### R11. Smaller primitive points
- `Ptr.add` checks only the result: a pointer built by hand as `ref r 5` into a 1-element array, then `add (-4)`, succeeds
  (C: forming the original pointer was already undefined). Only `Ptr.ref` as a public constructor allows this; the
  checked API cannot produce it. Low, unconfirmed as reachable.
- `Ptr.diff` wraps through `Int64.ofInt` instead of faulting when the difference is not a `ptrdiff_t`. Needs an array of
  2^63 elements. Low.
- `Ptr.fill`, `memcpy`, `memmove` fault on a read-only destination even for `n = 0` (C: no write, defined for non-null
  valid pointers). Spurious fault, Low.
- `Ptr.fill dst v n` accepts any `v` for any element type; C `memset(p, c, n)` writes the byte `c` into every byte, so for
  `ush` and `c = 1` the content is 0x0101. The doc limits it to `c = 0` but nothing checks that. Low.
- `Ptr.add` on a dangling pointer faults; in C the pointer value is indeterminate after `free`, so arithmetic is undefined
  anyway. Correct, mentioned for completeness. Same for the casts in `Tables.lean`: `castDeflateState` faults at the cast
  while C faults at the access (documented); conservative.
- Fuel: `cwhile` faults with `outOfFuel` after 2^64 iterations, so a defined loop of 2^64 or more iterations faults.
  Not reachable in zlib; it is a separate fault from `ub` and the loop rules require `k < fuel`. Low.
- Frees: `freeB` accepts any live writable byte block at offset 0, so a harness buffer made with `allocBytes` can be freed
  by zlib code; no allocation-origin tag. Low (harness only).
- `DeflateStateRef.put`, `InflateStateRef.put`, and the other table refs have the docstring "unchanged if it is not live"
  but the `tab` case inserts unconditionally (resurrects a freed slot). `stK` checks liveness first, so only a direct call of
  `put` is affected. Low.

### R12. Documentation that does not match the code
- `docs/safety.md` section 3 ("A read of an uninitialised pointer is a fault"), section 3 end (`memcpy` copies an
  "initialised" flag), section 4 (ghost table of initialised bits and "allocation counter"), U10 ("type tags"). The code has
  no initialised table and no type tags. `trusted-base.md` item 2 describes the code correctly.
- `Schema.lean` / `gen_schema.py` text says `lenfix` and `distfix` are "inside `fixedtables` in `inflate.c`"; in the pinned source
  they are in `inffixed.h`, included by `inftrees.c` (function `inflate_fixed`). `runtime-schema.md` says "included by
  `inftrees.c`", so the documents disagree.
- The skipped-macro comment in `Schema.lean` ("not an integer constant expression") is wrong for `COPY` (R3) and for
  `GZ_OFF_MAX`, which is a constant expression (9223372036854775807 on this target) that the evaluator cannot compute
  because of `sizeof`. Code that compares an offset with `GZ_OFF_MAX` needs the real value.
- `trusted-base.md` item 3 says differential tests are "not part of this repository yet"; `translation-guide.md`
  requires one for every function. Make one say what exists.

### R13. Static data not covered
`bl_order` (`local const uch bl_order[BL_CODES]` in `trees.c`) is not in `Statics`; `StaticTreeDesc` is hard-coded in
`gen_schema.py` rather than read from the AST, so drift in `trees.c` is not detected. The three descriptors must have
`(extra_base, elems, max_length)` = (257, 286, 15), (0, 30, 15), (0, 19, 7) (checked in `trees.c`); the defaults in `Statics`
do not say so. Low.

## Schema against the C (checked)

Record fields, order and widths: `ZStream` (14), `GzHeader` (13), `CtData`, `TreeDesc`, `DeflateState` (61, default build, no
`LIT_MEM`, no `ZLIB_DEBUG`), `Code`, `InflateState` (37), `GzFile`, `GzState` (22), `StaticTreeDesc`: no omitted, transposed or
mis-sized field. Array extents match: 573, 61, 39, 16, 573, 573, 320, 288, 1444. The `garbage` constructors use disjoint
index ranges (no two fields share a garbage index). All 77 integer macros and the one string macro match their headers for the
default branch (`LIT_BUFS` 4, `ENOUGH` 1444, `MAX_MEM_LEVEL` 9, `OS_CODE` 3, `ZLIB_VERNUM` 0x1321); all 35 enumerator values
match (types: R4). `char *` fields (`msg`, `path`) are `BPtr` (bytes); plain `char` is signed on this target, so a translation
that reads one needs an explicit sign extension (an obligation on each translation, not a defect of the schema).

## Findings not confirmed (need translation evidence)

- U1. Alignment, effective type and character views of typed objects. `uncompr.c` forms `(Bytef *)&stream.reserved`
  (when `dest` is NULL and `*destLen` is 0); `BRef` has no constructor for a byte view of a struct field, so the translation
  must invent a dummy block, which hides the aliasing. The default `crc32` word path casts a byte buffer to a wider integer
  pointer after alignment; the schema has no alignment facts.
- U2. Signed overflow, invalid shifts and division are checked by each translation, not by `M` (`Monad.lean` header).
  There is no checked-arithmetic API in the runtime, so a missing check in a translation is not visible here.
- U3. `M` is a transparent function type; a hand-written term can catch a fault or edit any heap field. This is a boundary of
  trust in the translation, not a flaw of `bind`.
- U4. Whether `Ptr.ref r off` with `off` beyond one past the end can arise from any translation (R11 first item).
- U5. Whether any zlib `ZALLOC`ed record other than the two states is read before it is written (R1).

## Checked and found correct

- `Ptr.load`/`store`: null, dangling, out of range and (for `store`) read-only all fault; one past the end is not readable.
- `memcpy` rejects null (even for `n = 0`), dangling, out of range, a read-only destination and overlapping ranges in one
  array; accepts disjoint ranges of one array; `memmove`/`copyRange` read from the original source, so both overlap
  directions are right.
- `freeB`: null is a no-op; a nonzero offset, a static or embedded array, a freed block and a read-only block all fault.
  Block numbers are not reused, so use after free and double free fault (`load_after_free`, `free_twice`).
- `bind` forwards `.error` without running the continuation; `OkOn` is equality with `.ok`; loop rules need `k < fuel`; no
  catch operator exists.
- `strlenB` faults when no NUL is inside the block.
- Struct frees: `freeZStream` rejects `in_gzstate_strm`; parent removal makes embedded refs dangling because `get` reads the
  parent table.
