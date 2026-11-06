# Positive CRC byte-view comparisons

The test calls both translated CRC entries on raw storage, two actual string
views, a deflate depth array and both static byte tables. Fixture bytes are
exported through `Space.get`. The native static tables are read from the
unchanged source and checked against those bytes.
Native string fixtures are byte-identical literals generated from the
exports, with their actual address residues recorded.

Every non-raw model origin from 0 through 7 is tested. The native origin
residue is recorded for each object. Only its matching model row is an ABI
comparison. The other model layouts are checked against the same bytewise
CRC result. They are not additional native layouts. Raw native storage is
explicitly aligned to match the model's existing raw-origin convention.

The matrix includes lengths 0, 1, 7, 8, 39, 40, 46, 47, 48, 79, 80 and 81
where they fit. It includes multiple offsets, complete remaining ranges and
one-past pointers with length zero. No invalid range is submitted.

Source preprocessing must select the portable little-endian N=5/W=8 path.
Optional hardware CRC branches are excluded. A baseline architecture option
is used on ARM targets. The report records the selected macros separately
for ordinary and sanitizer builds.

Run `./run.py --zlib-source SOURCE`. An optional `--output-dir NEW-DIRECTORY`
retains the independently compiled model and native projects, input matrix,
source hashes, address residues, results and sanitizer logs. The source
directory is read-only. Only a temporary project receives build outputs.

This is positive differential evidence, not a proof or a claim that the
default target configuration was executed. The report records the host and
compiler configuration. It does not repeat the public-buffer counterexample.

The address interpretation has direct proof mutants in
[`byte-address.tsv`](../../proofmut/byte-address.tsv). With a built root, run
`PROOFMUT_STRICT=1 bash tests/audit/proofmut.sh tests/proofmut/byte-address.tsv`.
Ignoring or shifting an origin must fail the unchanged address proof.
Restoring the old non-block fault must fail the general CRC-view proof.
