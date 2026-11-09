# NULL output guard behaviour review

This records an independently checked, deliberate proof mutation. It is not a
zlib bug report or a full function-correctness claim.

After actual successful default initialization, the stream has NULL input and
output, zero input and output capacity, and NO_FLUSH. The original public entry
returns STREAM_ERROR (-2). Removing only the NULL-output disjunct makes the next
zero-capacity check return BUF_ERROR (-5). The initialized private state remains
the same. Both finite native experiments subsequently returned OK from End.
That observation does not prove exact deallocation or general leak freedom.

The original effective upstream source was pin
757f0527154291bcf6bfbd6396ecde6bedd2db95 plus the reviewed inflateCopy pointer-equality
patch. Of 271 effective source files, only deflate.c changed in the mutant.
The native observation was arm64 macOS. It is finite behaviour evidence, not a
native x86_64 Linux proof, general differential test, or final acceptance.

DomainWitness.lean was independently kernel checked with only propext,
Classical.choice and Quot.sound. Its theorem has no hypotheses. It uses the
existing actual initialization producer to establish InitDomain, actual default
request/core-call history, reachability, initialized goodness, buffers, header,
and NULL/zero output on the same heap. It does not assume a caller invariant or
successful data-call contract. The reviewer reused that previously authored
initialization foundation and did not independently recertify the foundation.

The source model mutant is the same null-output-guard case as the paired scoped
diagnostic. The model original source SHA256 is
2c3dd695c03fd49ac515dd46cbf45e9eb5f4d142eb0e93999a9e7c5866f1795e;
the mutant SHA256 is
16aa23b72961a001396226734237cba5ca1ef7f40d72808c23e78d7d0aad9af6.

The independent evidence bundle digest is
ac721b5dba47ac59d2e46f25012a60b3def17e71e15544d940fc0e79284e7bc5.
Its original review digest is
bc77ae9c4c335846b292146d0fef5935aeca1631d1e96c3abefe935e0d276add.
The source witness, native harness and exact guard diff are retained beside this
record. This record binds completed independent review evidence. Approval of
the permanent admission baseline and its regenerated locks is a separate human
review step; no approved baseline is manufactured by this summary.
