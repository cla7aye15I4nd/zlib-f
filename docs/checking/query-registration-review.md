# Public query registration review

> **Historical record.** It describes the process when it was written: lock files, regenerated locks, an approved baseline and review of lock differences. Those mechanisms were removed later. There are no lock files now; see [anti-cheating](../anti-cheating.md). Read the evidence below as evidence about that snapshot only.

The source review found no type or domain blocker in the inspected snapshot. The registration changes no goal, translation or proof body.

Six added proofs have the exact target-constant types in the supplied compiled export, allowed axioms, and function docstrings. The query contracts cover all heaps; get_crc_table explicitly requires the initialized CRC globals. Both bounds cover every UInt64 input and assert the exact saturated numeric formula, not output-size adequacy. zError covers every Int32; the pinned upstream ERR_MSG macro guards both out-of-range ends before subtraction.

All twenty mutation anchors occur exactly once within the named function body. Headers/signatures and other declarations stay unchanged. The null-return syntax was independently typechecked without a build. The table below gives concrete permitted-input behavior differences.

| Mutation | Permitted input | Original | Mutant |
| --- | --- | --- | --- |
| zlibVersion-wrong-string | any heap | nonempty pinned version string | empty string |
| zlibVersion-null-pointer | any heap | read-only static version pointer | NULL |
| zlibCompileFlags-uint | any heap | 169 | 168 |
| zlibCompileFlags-ulong | any heap | 169 | 165 |
| zlibCompileFlags-pointer | any heap | 169 | 153 |
| zlibCompileFlags-offset | any heap | 169 | 105 |
| zError-lower-bound | err=-6 | incompatible version | empty text |
| zError-upper-bound | err=2 | need dictionary | empty text |
| zError-message-index | err=1 | stream end | need dictionary |
| zError-out-of-range-index | err=3 | empty text | need dictionary |
| zError-null-result | err=0 | read-only static empty-string pointer | NULL |
| get_crc_table-wrong-offset | heap with CrcGlobals | CRC table at offset zero | offset one; different first table entry |
| get_crc_table-wrong-table | heap with CrcGlobals | CRC table | x2n table; different object, size and first entry |
| get_crc_table-null-pointer | heap with CrcGlobals | CRC table pointer | NULL |
| compressBound_z-first-shift | sourceLen=2048 | 2061 | 2062 |
| compressBound_z-second-shift | sourceLen=8192 | 8207 | 8208 |
| compressBound_z-third-shift | sourceLen=16777216 | 16782349 | 16782350 |
| compressBound_z-constant | sourceLen=0 | 13 | 12 |
| compressBound_z-overflow-guard | sourceLen=0 | 13 | 18446744073709551615 |
| compressBound-wrapper-result | sourceLen=0 | 13 | 14 |

All twenty strict module mutations passed from a positive baseline. The six exact public
proofs passed fresh-kernel baseline replay and rejected every required mapped mutation.
The existing error-clearing and code-count mappings also passed their exact replays.

The four supplementary error-code boundary/index mutations remain in the strict list.
The original-proof replay of `zError-lower-bound` exceeded the kernel recursion limit.
It is not counted as a semantic rejection. The other three boundary/index exact replays
were not run. The required mapping uses the independently reviewed null-result mutation,
whose strict and original-proof replay checks both passed. No rejection rule was relaxed.

These are local registration checks. They do not establish complete C translation
fidelity, approve accumulated semantic lock changes, or report a CI pass. Current
acceptance status and remaining work are maintained in [progress](../progress.md).
