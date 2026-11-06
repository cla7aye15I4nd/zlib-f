# Compressor allocation regression

These are differential execution observations, not a formal proof or a
complete argument that each tested C operation has defined standard semantics.

The compressor declares its local stream with automatic storage. It must not
consume a default-allocator call. The old translation charged an extra oracle
call for this record: failure 0 faulted instead of returning `Z_MEM_ERROR`,
and the successful call counted six allocation attempts instead of five.

Run from a checkout with its pinned submodule populated:

```sh
bash tests/regression/compress-allocation/run.sh
```

An optional first argument selects the checkout. An optional second argument
selects the evidence directory. The default evidence directory is
`regression-evidence/compress-allocation/`; generated logs and binaries are
not test source. The target is default x86_64 Linux/LP64 with linker allocation wrapping.
The runner requires the pinned Lean toolchain, a C compiler,
Python, and the usual shell utilities on `PATH`. It builds the patched pinned
C library using the existing build helper without changing the submodule.

## Comparison

There are 108 compression rows across `compress2_z`, `compress2`, `compress_z`
and `compress`, and one truncated-input `uncompress2_z` row. Normal calls,
empty input and zero-capacity null destinations sweep no failure and malloc
attempts 0 through 6. Nonempty null sources, positive-capacity null destinations,
invalid levels for level-taking entries, and null scalar pointers for `_z`
entries have explicit error-ordering rows.

The allocator wrapper is enabled only during the tested C call. It counts
failed attempts too. A fixed-size table tracks allocated pointers and frees;
a bookkeeping overflow or a live allocation carried into the next case aborts.
Each row compares the return code, stored scalar, all 64 destination bytes
(including the untouched `a5` sentinel), allocation attempts and live blocks.
The decoder row compares all 256 bytes and both scalar lengths. The Lean
harness excludes caller blocks by block number, rather than subtracting a
count that could hide a freed caller block. Zero remaining live blocks is an
independent acceptance condition, not merely a comparison between two counts.

The same comparison checks a private old-translation copy. Only its local
stream allocation call is changed back to the old call. All old differences
are retained; the runner must observe the failure-0 fault for every compression
entry. There is no failure-index shift, row alignment or discrepancy filter.
An empty, incomplete, duplicate or unexpected output protocol fails the test.

## Error-path observations

For input `[78 9c 73 04 00]`, a prefix of zlib-compressed `A`, output capacity
256, and failure at malloc attempt 1, both implementations return `Z_MEM_ERROR`
with `destLen = 1`, `sourceLen = 5`, output byte `41`, two allocation attempts
and no remaining library-owned blocks. This is evidence for specification
review: memory failure does not imply that no output was written.

Zero-capacity null-destination rows are execution observations only. The C
utility later subtracts its output pointer from the null destination. Whether
that operation is defined by the selected C language semantics remains open.
A matching result or a silent sanitizer does not establish that it is defined.

A null scalar pointer in `compress2` or `compress` is a separate C null-read
witness. Those calls are excluded from the comparison matrix. Their actual
Lean faults must be observed, and isolated sanitizer C calls must diagnose the
null read. They are not counted as matching, well-defined executions.

## Sanitizers

A second, independent patched C library and the drivers are built with
AddressSanitizer and UndefinedBehaviorSanitizer. Leak detection is explicitly
enabled; no leak suppressions are installed. The runner fails if the matrix
process exits unsuccessfully, produces sanitizer stderr, or its rows disagree.
The separate null-scalar witnesses must exit unsuccessfully with a null-read
diagnostic. Their intentional diagnostics are retained separately.

A successful regression establishes only the finite observations above.
It does not validate every caller, configuration, pointer alias or C semantic
assumption, nor does it replace the project audit or its proof obligations.
