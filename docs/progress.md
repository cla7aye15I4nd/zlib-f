# Proof progress and remaining work

This page records evidence and unfinished work. For the statement and proof
architecture, read [the overview](overview.md).

## Scope

The project is finished when the planned targets below are accepted. The rest is not planned.

**Planned.** Safety only (owner's decision of 2026-11-11): two results, in this order, and then
their direct compositions. Safety means no undefined behaviour, no memory error, no leak, and
termination. A functional fact is in scope exactly when a planned safety proof depends on it;
functional results that safety does not need are not planned.

| # | Result | Targets |
| ---: | --- | --- |
| 1 | `inflate` is safe on every input and every split of the buffers, also over its call sequences. | `inflate`, the safety part of `inflate_sequence` |
| 2 | `deflate` is safe on every input and every split of the buffers, also over its call sequences. | `deflateInit2_`, `deflate`, `deflate_sequence_safety` |
| 3 | Whole-buffer compositions of 1 and 2. | the safety of `compress*`, `uncompress*` |
| 4 | The callback decoder is safe on every input and every caller protocol, also over its call sequences (owner's request of 2026-11-12). | `inflate_back_sequence_safety` |
| 5 | The gzip file interface is safe on every history of a handle, for every file-system world (owner's decision of 2026-11-12). Safety only, not functional correctness. | `gzopen`, `gzopen64`, `gzclose`, `gzclose_r`, `gzclose_w`, `gzread`, `gzfread`, `gzgetc`, `gzgetc_`, `gzungetc`, `gzgets`, `gzdirect`, `gzwrite`, `gzfwrite`, `gzputc`, `gzputs`, `gzprintf`, `gzvprintf`, `gzflush`, `gzsetparams`, `gzseek`, `gzseek64`, `gztell`, `gztell64`, through `gz_sequence_safety` |

A target that one of these needs as a step stays planned as a dependency. This holds for the
other stream calls that a sequence goal ranges over, such as `inflateSync`, `inflateCopy`,
`deflateCopy`, `deflateParams`, `deflatePrime` and `deflateSetDictionary`. `gzvprintf` is
undocumented in zlib.h, but `gzprintf` goes through it, so it is planned with result 5.

**Not planned.** No further work goes to these. Results already registered for them stay.

| Group | Targets | Reason |
| --- | --- | --- |
| Gzip file interface, functional | `gz_sequence`, `gz_initialisation_domain`, and the functional clauses of the gz calls (the bytes read or written, the return values beyond safety) | Functional. These theorems depend on a hand-made model of the file system, descriptors and `printf` formatting. The safety of the gz calls is planned (result 5). |
| Undocumented functions | `zError`, `inflateSyncPoint`, `get_crc_table`, `inflateUndermine`, `inflateValidate`, `inflateCodesUsed`, `inflateResetKeep`, `deflateResetKeep`, `gzopen_w` | zlib.h declares them under "undocumented functions (not part of the zlib API)" (`tests/audit/public-api.json`, `undocumented`). They are not required public targets, and a direct call of one is not a required operation of a sequence goal; the deflate stream domain excludes a direct `deflateResetKeep` (`docs/deviations.md`). Their registered proofs stay registered and audited. `gzvprintf` moved to result 5 (2026-11-12). Internal use is unchanged: `deflateReset` and `inflateReset` go through the `ResetKeep` lemmas. |
| Callback decoder, decoding | the decoding clauses of `inflateBack` and `inflate_back_sequence` (what reaches `out`, `Decodes`) | Functional. The safety of the callback decoder is planned (result 4). |
| Model-only statements | `Api.Goal.inflate_rejects_invalid`, the unregistered `*_refines` goals | They speak about the abstract model, not about the C. The first also rests on a detection lag of eight bytes that a counterexample refutes. Rejection of invalid input is stated against the C in result 2. |
| Other build configurations | every configuration except the default x86_64 Linux build | Each one repeats the whole proof for a different platform model. The default build carries the result. |
| More proof mutants for query functions | getters and constant queries | Mutants defend against a wrong proof setup. For a one-line query they add nothing to the planned results. |
| Functional correctness | the format part of `inflate_sequence` (`inflate` output equals the format: `ParseMeaning` and its stream and decoding sides), the `DecoderFacts` format facts behind `InflateCompletes` and the format clauses of `uncompress*`, and the deflate round-trip (`Ledger`, `ledger_*`, `completes`, `bound_before_output`, `deflate_sequence`'s decoding part) | Owner's decision of 2026-11-11, to finish sooner. A functional fact that a planned safety proof depends on stays in scope. What is already proved of it is kept and listed as checked; open rows are marked not planned in [Core proof skeletons](#core-proof-skeletons). |

A not-planned target is not claimed. Reports say "not planned", never "proved".

## Contents

- [Scope: planned and not planned](#scope)
- [All targets and dependencies](#proof-progress-graph)
- [Exact target evidence](#target-evidence)
- [Remaining work](#remaining-work)
  - [Core proof skeletons](#core-proof-skeletons)
  - [Ordered next work](#ordered-next-work)
  - [Public API prerequisites](#public-api-proof-readiness)
  - [Specification review](#specification-review)
  - [Translation review](#translation-review)
  - [Reports to recheck](#historical-reports-to-recheck)
- [Earlier checkpoints (historical)](history/progress-checkpoints.md)

The counts in the generated block below are the only current counts. Counts in review
records and in `docs/history/` describe the state when they were written.

<!-- proof-progress:start -->
## Proof progress graph

**196 fixed targets: 118 public and 78 supporting.**
Exact proofs: 143 registered and 5 local only.
These counts are not a percentage of verification effort or a final CI result.

**Input coverage colours:** ⬜ not proved · 🟦 default inputs · 🟨 common inputs · 🟩 all stated inputs.
The input ranges are defined once in [input configurations](spec/input-configurations.md).
A complete fixed-goal proof covers all inputs admitted by that exact statement.
Default/common coverage requires an exact checked scoped contract; branch lemmas
and manually assigned labels cannot grant it. Registration and CI remain separate.
A red border marks a recorded blocker without erasing other established coverage.

Every current fixed target appears once. Public APIs, internal obligations and
abstract models stay in separate groups. Solid arrows show actual proof reuse
between fixed targets, following references through auxiliary lemmas. Dotted
arrows show C calls from callee to caller. They do not make the callee's complete
API contract a proof premise: default Init can be proved independently of
universal Init2. Redundant arrows are omitted only when a path of the same kind
remains. The [evidence index](progress.md) retains every observed connection,
specification references and supporting proof families. These helpers are not
extra final targets. Missing arrows do not establish independence or enumerate
future proof obligations.

```mermaid
flowchart LR
  subgraph queries["Library queries"]
    n19["compressBound"]:::all
    n20["compressBound_z"]:::all
    n21["zlibVersion"]:::all
    n22["zlibCompileFlags"]:::all
    n23["zError"]:::all
    n30["get_crc_table"]:::all
  end
  style queries fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph checksums["Checksums"]
    n24["adler32"]:::all
    n25["adler32_z"]:::all
    n26["adler32_combine"]:::all
    n27["adler32_combine64"]:::all
    n28["crc32"]:::all
    n29["crc32_z"]:::all
    n31["crc32_combine_gen"]:::all
    n32["crc32_combine_gen64"]:::all
    n33["crc32_combine_op"]:::all
    n34["crc32_combine"]:::all
    n35["crc32_combine64"]:::all
  end
  style checksums fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph addresses["Byte-address model"]
    n138["ByteAddress<br/>address_read_is_pure"]:::all
    n139["ByteAddress<br/>raw_block_unchanged"]:::all
    n140["ByteAddress<br/>every_layout_is_<br/>representable"]:::all
    n141["ByteAddress<br/>every_existing_heap_<br/>accepts_layout"]:::all
    n142["ByteAddress<br/>mask_refines_base_plus_<br/>offset"]:::all
    n143["ByteAddress<br/>pointer_advance_<br/>preserves_low_bits"]:::all
    n144["ByteAddress<br/>first_aligned_offset"]:::all
    n145["ByteAddress<br/>byte_stores_preserve_<br/>bases"]:::all
    n146["ByteAddress<br/>byte_modifies_preserve_<br/>bases"]:::all
  end
  style addresses fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph inflate["Inflate streams"]
    n39["inflateCopy"]:::all
    n73["inflateInit2_"]:::all
    n74["inflateInit_"]:::all
    n77["inflateResetKeep"]:::all
    n78["inflateReset"]:::all
    n79["inflateReset2"]:::all
    n80["inflateEnd"]:::all
    n81["inflateGetDictionary"]:::all
    n82["inflateGetHeader"]:::all
    n87["inflateSetDictionary"]:::all
    n89["inflateSyncPoint"]:::all
    n90["inflateMark"]:::all
    n91["inflateCodesUsed"]:::all
    n92["inflateUndermine"]:::all
    n93["inflateValidate"]:::all
    n94["inflatePrime"]:::all
    n99["inflate"]:::all
    n105["inflateSync"]:::unproved
    n123["inflate_sequence_safety"]:::all
    n127["inflate_back_sequence_<br/>safety"]:::unproved
    n129["inflate_refusal<br/>Local exact proof"]:::all
  end
  style inflate fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph fast["Fast decoder obligations"]
    n149["InflateFastBodyOrigin<br/>actual_body_preserves_<br/>origin"]:::all
    n150["InflateFastBodyToken<br/>actual_body_refines_token"]:::all
    n151["InflateFastCallOrigin<br/>actual_fast_preserves_<br/>origin"]:::all
    n152["InflateFastDistanceOrigin<br/>actual_distance_block_<br/>preserves_origin"]:::all
    n153["InflateFastDistanceResult<br/>actual_distance_refines_<br/>lz77"]:::all
    n154["InflateFastDistance<br/>Semantics<br/>distance_lookup_matches_<br/>format"]:::all
    n155["InflateFast<br/>fast_safe"]:::all
    n156["InflateFast<br/>step_safe"]:::all
    n157["InflateFastLength<br/>Semantics<br/>length_lookup_matches_<br/>format"]:::all
    n158["InflateFastLengthTrace<br/>actual_body_retains_<br/>selected_length"]:::all
    n159["InflateFastMatchHistory<br/>actual_copy_match_<br/>refines_lz77"]:::all
    n160["InflateFastMatchHistory<br/>match_array_refines_lz77"]:::all
    n161["InflateFastOrigin<br/>actual_drop_preserves_<br/>origin"]:::all
    n162["InflateFastOrigin<br/>actual_pull_preserves_<br/>origin"]:::all
    n163["InflateFastOrigin<br/>actual_rollback_<br/>preserves_origin"]:::all
    n164["InflateFastOrigin<br/>drop_preserves_origin"]:::all
    n165["InflateFastOrigin<br/>initial_origin"]:::all
    n166["InflateFastOrigin<br/>pull_preserves_origin"]:::all
    n167["InflateFastOrigin<br/>rollback_preserves_origin"]:::all
  end
  style fast fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph tables["Decode-table obligations"]
    n168["InflateDecodeTable<br/>Rejection<br/>decode_table_classifies_<br/>input"]:::all
    n169["InflateDecodeTable<br/>Semantics<br/>decode_table_matches_<br/>format"]:::all
    n170["InflateDecodeTableShort<br/>short_decode_table_leaf_<br/>sound"]:::all
    n171["InflateDecodeTable<br/>Soundness<br/>decode_table_leaf_sound"]:::all
    n172["InflateDecodeTableFrame<br/>decode_table_read_<br/>preserved"]:::all
    n173["InflateDecodeTable<br/>Invariant<br/>constructor_establishes_<br/>decode_table_invariant"]:::all
    n174["InflateDecodeTable<br/>Invariant<br/>decode_table_invariant_<br/>of_prefix"]:::all
    n175["InflateDecodeTable<br/>Stability<br/>constructor_establishes_<br/>query_stability"]:::all
    n176["InflateDecodeTable<br/>Stability<br/>query_stability_of_prefix"]:::all
    n177["InflateDecodeTable<br/>Stability<br/>short_rejected_leaf_<br/>stays_invalid"]:::all
    n178["InflateFastTableFlags<br/>constructor_establishes_<br/>fast_leaf_flags"]:::all
    n179["InflateFastTableFlags<br/>fast_leaf_flags_of_prefix"]:::all
    n180["InflateFastTableFlags<br/>fixed_tables_have_fast_<br/>leaf_flags"]:::all
    n181["InflateFastTableFlags<br/>leaf_classification_<br/>agrees"]:::all
    n182["InflateTableContent<br/>inflate_table_content"]:::all
    n183["InflateTableSafety<br/>inflate_table_decoder_<br/>safe"]:::all
    n184["InflateTableExtent<br/>inflate_table_read_extent"]:::all
    n185["InflateRootTable<br/>constructor_root_bits"]:::all
    n186["InflateSubtable<br/>constructor_subtable_bits"]:::all
  end
  style tables fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph copy["Match-copy mathematics"]
    n187["LZ77CopySpec<br/>output_copy_refines_lz77"]:::all
    n188["LZ77CopySpec<br/>window_copy_refines_lz77"]:::all
    n189["LZ77HistorySpec<br/>copy_back_compose"]:::all
    n190["LZ77HistorySpec<br/>copy_back_extends_history"]:::all
    n191["LZ77HistorySpec<br/>retained_history_agrees"]:::all
    n192["LZ77HistorySpec<br/>window_distance_check_<br/>agrees"]:::all
  end
  style copy fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph deflate["Deflate streams"]
    n40["deflateCopy<br/>Local exact proof"]:::all
    n75["deflateInit2_"]:::all
    n76["deflateInit_"]:::all
    n83["deflateGetDictionary"]:::all
    n84["deflateEnd"]:::all
    n85["deflateResetKeep"]:::all
    n86["deflateReset"]:::all
    n88["deflateSetDictionary"]:::unproved
    n95["deflatePending"]:::all
    n96["deflateUsed"]:::all
    n97["deflateTune"]:::all
    n98["deflateSetHeader"]:::all
    n100["deflate"]:::all
    n101["deflateBound_z"]:::unproved
    n102["deflateBound"]:::unproved
    n103["deflatePrime"]:::unproved
    n104["deflateParams"]:::unproved
    n125["deflate_sequence_safety"]:::all
    n128["deflateCopy_safety<br/>Local exact proof"]:::all
    n130["deflate_refusal<br/>Local exact proof"]:::all
  end
  style deflate fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph back["Callback decoding"]
    n36["inflateBackInit_"]:::all
    n37["inflateBack"]:::unproved
    n38["inflateBackEnd"]:::all
  end
  style back fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph gzip["Gzip files"]
    n41["gzclose_r"]:::unproved
    n42["gzclose_w"]:::unproved
    n43["gzclose"]:::unproved
    n44["gzbuffer"]:::all
    n45["gzeof"]:::all
    n46["gztell64"]:::unproved
    n47["gztell"]:::unproved
    n48["gzoffset64"]:::all
    n49["gzoffset"]:::all
    n50["gzerror"]:::all
    n51["gzclearerr"]:::all
    n52["gzrewind"]:::all
    n53["gzseek64"]:::unproved
    n54["gzseek"]:::unproved
    n55["gzopen"]:::unproved
    n56["gzopen64"]:::unproved
    n57["gzdopen"]:::all
    n58["gzread"]:::unproved
    n59["gzfread"]:::unproved
    n60["gzgetc"]:::unproved
    n61["gzgetc_"]:::unproved
    n62["gzungetc"]:::unproved
    n63["gzgets"]:::unproved
    n64["gzdirect"]:::unproved
    n65["gzwrite"]:::unproved
    n66["gzfwrite"]:::unproved
    n67["gzputc"]:::unproved
    n68["gzputs"]:::unproved
    n69["gzvprintf"]:::unproved
    n70["gzprintf"]:::unproved
    n71["gzflush"]:::unproved
    n72["gzsetparams"]:::unproved
    n131["gz_sequence_safety"]:::unproved
  end
  style gzip fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph buffers["Whole-buffer operations"]
    n106["compress2_z"]:::unproved
    n107["compress2"]:::unproved
    n108["compress_z"]:::unproved
    n109["compress"]:::unproved
    n110["uncompress2_z"]:::unproved
    n111["uncompress2"]:::unproved
    n112["uncompress_z"]:::unproved
    n113["uncompress"]:::unproved
    n114["uncompress2_z_safe"]:::all
    n115["uncompress2_safe"]:::all
    n116["uncompress_z_safe"]:::all
    n117["uncompress_safe"]:::all
    n118["compress2_z_safety"]:::all
    n119["compress2_safety"]:::all
    n120["compress_z_safety"]:::all
    n121["compress_safety"]:::all
  end
  style buffers fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph models["Format and API models"]
    n0["Goals<br/>format_deterministic"]:::all
    n1["Goals<br/>format_prefix_free"]:::all
    n2["Goals<br/>inflate_decodes"]:::all
    n3["Goals<br/>inflate_completes"]:::all
    n4["Goals<br/>inflate_rejects_invalid"]:::unproved
    n5["Goals<br/>deflate_valid"]:::all
    n6["Goals<br/>deflate_completes"]:::all
    n7["Goals<br/>deflate_full_flush_resync"]:::all
    n8["Goals<br/>roundtrip"]:::all
    n9["Goals<br/>roundtrip_completes"]:::all
    n10["Goals<br/>dict_roundtrip"]:::all
    n11["Goals<br/>header_roundtrip"]:::all
    n12["Goals<br/>deflate_bound_adequate"]:::all
    n13["Goals<br/>compress_bound_adequate"]:::all
    n14["Goals<br/>compress_roundtrip"]:::all
    n15["Goals<br/>gz_roundtrip"]:::all
    n16["Goals<br/>gz_seek_read<br/>Local exact proof"]:::all
    n17["Concrete<br/>compress_bound_value"]:::all
    n18["Concrete<br/>compress2_z_first_alloc_<br/>failure"]:::all
    n137["Inflate<br/>inflate_deferred_distance"]:::all
  end
  style models fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph lifecycle["Lifecycles and call sequences"]
    n122["inflate_sequence"]:::unproved
    n124["deflate_sequence"]:::unproved
    n126["inflate_back_sequence"]:::unproved
    n132["gz_sequence"]:::unproved
    n133["inflate_initialisation_<br/>domain"]:::all
    n134["deflate_initialisation_<br/>domain"]:::unproved
    n135["inflate_back_<br/>initialisation_domain"]:::all
    n136["gz_initialisation_domain"]:::unproved
  end
  style lifecycle fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph internal["Internal proof obligations"]
    n147["Crc32ByteViews<br/>crc32_z_all_byte_views"]:::all
    n148["Crc32ByteViews<br/>crc32_all_byte_views"]:::all
    n193["Token<br/>rejected_has_no_symbols"]:::all
    n194["Token<br/>step_composes_symbols"]:::all
    n195["Token<br/>symbols_exposes_step"]:::all
  end
  style internal fill:#f9fafb,stroke:#9ca3af,color:#111827
  n143 --> n144
  n148 --> n28
  n148 --> n99
  n148 --> n39
  n148 --> n123
  n147 --> n29
  n149 --> n151
  n151 --> n99
  n151 --> n39
  n151 --> n123
  n152 --> n149
  n153 --> n150
  n154 --> n153
  n155 --> n151
  n156 --> n150
  n156 --> n158
  n157 --> n150
  n159 --> n153
  n160 --> n159
  n161 --> n149
  n163 --> n151
  n164 --> n152
  n164 --> n161
  n165 --> n151
  n166 --> n152
  n166 --> n162
  n167 --> n163
  n168 --> n173
  n169 --> n168
  n170 --> n173
  n171 --> n168
  n171 --> n170
  n172 --> n174
  n172 --> n176
  n172 --> n179
  n173 --> n99
  n173 --> n39
  n173 --> n123
  n174 --> n99
  n174 --> n39
  n174 --> n123
  n177 --> n154
  n177 --> n157
  n182 --> n183
  n183 --> n184
  n183 --> n185
  n184 --> n173
  n186 --> n173
  n186 --> n185
  n187 --> n160
  n188 --> n160
  n189 --> n160
  n191 --> n8
  n191 --> n9
  n5 --> n10
  n5 --> n11
  n5 --> n8
  n5 --> n9
  n3 --> n9
  n2 --> n8
  n25 --> n24
  n28 --> n119
  n28 --> n118
  n28 --> n121
  n28 --> n120
  n28 --> n100
  n28 --> n40
  n28 --> n125
  n40 --> n128
  n84 --> n119
  n84 --> n118
  n84 --> n121
  n84 --> n120
  n84 --> n125
  n99 --> n115
  n99 --> n114
  n99 --> n117
  n99 --> n116
  n36 --> n135
  n80 --> n123
  n73 --> n99
  n73 --> n39
  n73 --> n123
  n87 --> n123
  n24 -.-> n100
  n24 -.-> n85
  n24 -.-> n88
  n24 -.-> n99
  n24 -.-> n87
  n25 -.-> n24
  n107 -.-> n109
  n106 -.-> n107
  n106 -.-> n108
  n20 -.-> n19
  n28 -.-> n100
  n28 -.-> n85
  n28 -.-> n88
  n28 -.-> n99
  n35 -.-> n34
  n32 -.-> n35
  n32 -.-> n31
  n33 -.-> n35
  n29 -.-> n28
  n100 -.-> n106
  n100 -.-> n104
  n100 -.-> n42
  n100 -.-> n71
  n100 -.-> n66
  n100 -.-> n67
  n100 -.-> n68
  n100 -.-> n69
  n100 -.-> n65
  n101 -.-> n102
  n84 -.-> n75
  n75 -.-> n76
  n75 -.-> n42
  n75 -.-> n71
  n75 -.-> n66
  n75 -.-> n67
  n75 -.-> n68
  n75 -.-> n72
  n75 -.-> n69
  n75 -.-> n65
  n76 -.-> n106
  n104 -.-> n72
  n86 -.-> n75
  n85 -.-> n86
  n41 -.-> n43
  n42 -.-> n43
  n60 -.-> n61
  n48 -.-> n49
  n52 -.-> n53
  n53 -.-> n54
  n46 -.-> n47
  n69 -.-> n70
  n99 -.-> n59
  n99 -.-> n60
  n99 -.-> n63
  n99 -.-> n58
  n99 -.-> n62
  n99 -.-> n110
  n80 -.-> n41
  n80 -.-> n110
  n73 -.-> n64
  n73 -.-> n59
  n73 -.-> n60
  n73 -.-> n63
  n73 -.-> n58
  n73 -.-> n62
  n73 -.-> n74
  n74 -.-> n110
  n78 -.-> n79
  n78 -.-> n105
  n79 -.-> n73
  n77 -.-> n78
  n111 -.-> n113
  n110 -.-> n111
  n110 -.-> n112
  n23 -.-> n100
  n23 -.-> n75
  n21 -.-> n106
  click n0 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Api/Goals.lean#L42" _blank
  click n1 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Api/Goals.lean#L47" _blank
  click n2 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Api/Goals.lean#L58" _blank
  click n3 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Api/Goals.lean#L69" _blank
  click n4 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Api/Goals.lean#L84" _blank
  click n5 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Api/Goals.lean#L99" _blank
  click n6 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Api/Goals.lean#L106" _blank
  click n7 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Api/Goals.lean#L116" _blank
  click n8 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Api/Goals.lean#L134" _blank
  click n9 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Api/Goals.lean#L143" _blank
  click n10 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Api/Goals.lean#L162" _blank
  click n11 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Api/Goals.lean#L180" _blank
  click n12 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Api/Goals.lean#L189" _blank
  click n13 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Api/Goals.lean#L196" _blank
  click n14 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Api/Goals.lean#L203" _blank
  click n15 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Api/Goals.lean#L214" _blank
  click n16 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Api/Goals.lean#L221" _blank
  click n17 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Api/Concrete.lean#L57" _blank
  click n18 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Api/Concrete.lean#L67" _blank
  click n19 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Queries.lean#L35" _blank
  click n20 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Queries.lean#L40" _blank
  click n21 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Queries.lean#L46" _blank
  click n22 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Queries.lean#L53" _blank
  click n23 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Queries.lean#L59" _blank
  click n24 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Checksums.lean#L66" _blank
  click n25 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Checksums.lean#L61" _blank
  click n26 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Checksums.lean#L86" _blank
  click n27 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Checksums.lean#L90" _blank
  click n28 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Checksums.lean#L117" _blank
  click n29 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Checksums.lean#L109" _blank
  click n30 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Checksums.lean#L126" _blank
  click n31 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Checksums.lean#L140" _blank
  click n32 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Checksums.lean#L143" _blank
  click n33 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Checksums.lean#L150" _blank
  click n34 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Checksums.lean#L162" _blank
  click n35 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Checksums.lean#L165" _blank
  click n36 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Back.lean#L22" _blank
  click n37 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Back.lean#L118" _blank
  click n38 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Back.lean#L145" _blank
  click n39 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Copy.lean#L27" _blank
  click n40 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Copy.lean#L67" _blank
  click n41 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/GzClose.lean#L35" _blank
  click n42 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/GzClose.lean#L40" _blank
  click n43 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/GzClose.lean#L44" _blank
  click n44 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/GzControl.lean#L12" _blank
  click n45 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/GzControl.lean#L22" _blank
  click n46 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/GzControl.lean#L36" _blank
  click n47 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/GzControl.lean#L39" _blank
  click n48 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/GzControl.lean#L53" _blank
  click n49 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/GzControl.lean#L56" _blank
  click n50 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/GzControl.lean#L63" _blank
  click n51 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/GzControl.lean#L74" _blank
  click n52 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/GzControl.lean#L91" _blank
  click n53 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/GzControl.lean#L116" _blank
  click n54 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/GzControl.lean#L119" _blank
  click n55 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/GzOpen.lean#L65" _blank
  click n56 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/GzOpen.lean#L70" _blank
  click n57 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/GzOpen.lean#L75" _blank
  click n58 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/GzRead.lean#L22" _blank
  click n59 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/GzRead.lean#L37" _blank
  click n60 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/GzRead.lean#L58" _blank
  click n61 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/GzRead.lean#L61" _blank
  click n62 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/GzRead.lean#L66" _blank
  click n63 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/GzRead.lean#L80" _blank
  click n64 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/GzRead.lean#L103" _blank
  click n65 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/GzWrite.lean#L28" _blank
  click n66 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/GzWrite.lean#L43" _blank
  click n67 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/GzWrite.lean#L59" _blank
  click n68 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/GzWrite.lean#L71" _blank
  click n69 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/GzWrite.lean#L108" _blank
  click n70 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/GzWrite.lean#L112" _blank
  click n71 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/GzWrite.lean#L117" _blank
  click n72 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/GzWrite.lean#L134" _blank
  click n73 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Initialisation.lean#L92" _blank
  click n74 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Initialisation.lean#L97" _blank
  click n75 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Initialisation.lean#L140" _blank
  click n76 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Initialisation.lean#L147" _blank
  click n77 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Lifecycle.lean#L20" _blank
  click n78 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Lifecycle.lean#L32" _blank
  click n79 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Lifecycle.lean#L43" _blank
  click n80 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Lifecycle.lean#L60" _blank
  click n81 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Lifecycle.lean#L77" _blank
  click n82 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Lifecycle.lean#L87" _blank
  click n83 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Lifecycle.lean#L105" _blank
  click n84 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Lifecycle.lean#L115" _blank
  click n85 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Lifecycle.lean#L146" _blank
  click n86 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Lifecycle.lean#L149" _blank
  click n87 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Lifecycle.lean#L153" _blank
  click n88 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Lifecycle.lean#L175" _blank
  click n89 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/StreamQueries.lean#L53" _blank
  click n90 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/StreamQueries.lean#L62" _blank
  click n91 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/StreamQueries.lean#L73" _blank
  click n92 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/StreamQueries.lean#L81" _blank
  click n93 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/StreamQueries.lean#L89" _blank
  click n94 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/StreamQueries.lean#L100" _blank
  click n95 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/StreamQueries.lean#L113" _blank
  click n96 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/StreamQueries.lean#L124" _blank
  click n97 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/StreamQueries.lean#L132" _blank
  click n98 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/StreamQueries.lean#L145" _blank
  click n99 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Streams.lean#L35" _blank
  click n100 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Streams.lean#L87" _blank
  click n101 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Streams.lean#L154" _blank
  click n102 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Streams.lean#L158" _blank
  click n103 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Streams.lean#L168" _blank
  click n104 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Streams.lean#L186" _blank
  click n105 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Streams.lean#L209" _blank
  click n106 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Utilities.lean#L84" _blank
  click n107 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Utilities.lean#L89" _blank
  click n108 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Utilities.lean#L96" _blank
  click n109 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Utilities.lean#L101" _blank
  click n110 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Utilities.lean#L156" _blank
  click n111 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Utilities.lean#L160" _blank
  click n112 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Utilities.lean#L188" _blank
  click n113 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Utilities.lean#L192" _blank
  click n114 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Utilities.lean#L231" _blank
  click n115 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Utilities.lean#L234" _blank
  click n116 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Utilities.lean#L260" _blank
  click n117 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Utilities.lean#L263" _blank
  click n118 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Utilities.lean#L68" _blank
  click n119 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Utilities.lean#L72" _blank
  click n120 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Utilities.lean#L78" _blank
  click n121 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Utilities.lean#L107" _blank
  click n122 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Sequences.lean#L241" _blank
  click n123 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Sequences.lean#L268" _blank
  click n124 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Sequences.lean#L278" _blank
  click n125 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Sequences.lean#L259" _blank
  click n126 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Sequences.lean#L375" _blank
  click n127 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Sequences.lean#L396" _blank
  click n128 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Copy.lean#L106" _blank
  click n129 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Refusals.lean#L25" _blank
  click n130 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Refusals.lean#L45" _blank
  click n131 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/GzSafety.lean#L129" _blank
  click n132 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Sequences.lean#L425" _blank
  click n133 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Domains.lean#L24" _blank
  click n134 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Domains.lean#L37" _blank
  click n135 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Domains.lean#L53" _blank
  click n136 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Public/Domains.lean#L79" _blank
  click n137 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Api/Inflate.lean#L267" _blank
  click n138 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/ByteAddress.lean#L39" _blank
  click n139 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/ByteAddress.lean#L43" _blank
  click n140 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/ByteAddress.lean#L50" _blank
  click n141 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/ByteAddress.lean#L57" _blank
  click n142 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/ByteAddress.lean#L65" _blank
  click n143 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/ByteAddress.lean#L70" _blank
  click n144 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/ByteAddress.lean#L77" _blank
  click n145 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/ByteAddress.lean#L83" _blank
  click n146 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/ByteAddress.lean#L87" _blank
  click n147 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Crc32ByteViews.lean#L17" _blank
  click n148 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Crc32ByteViews.lean#L28" _blank
  click n149 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/InflateFastBodyOrigin.lean#L18" _blank
  click n150 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/InflateFastBodyToken.lean#L73" _blank
  click n151 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/InflateFastCallOrigin.lean#L24" _blank
  click n152 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/InflateFastDistanceOrigin.lean#L18" _blank
  click n153 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/InflateFastDistanceResult.lean#L101" _blank
  click n154 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/InflateFastDistanceSemantics.lean#L20" _blank
  click n155 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/InflateFast.lean#L70" _blank
  click n156 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/InflateFast.lean#L42" _blank
  click n157 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/InflateFastLengthSemantics.lean#L34" _blank
  click n158 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/InflateFastLengthTrace.lean#L51" _blank
  click n159 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/InflateFastMatchHistory.lean#L39" _blank
  click n160 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/InflateFastMatchHistory.lean#L25" _blank
  click n161 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/InflateFastOrigin.lean#L68" _blank
  click n162 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/InflateFastOrigin.lean#L57" _blank
  click n163 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/InflateFastOrigin.lean#L81" _blank
  click n164 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/InflateFastOrigin.lean#L38" _blank
  click n165 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/InflateFastOrigin.lean#L27" _blank
  click n166 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/InflateFastOrigin.lean#L32" _blank
  click n167 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/InflateFastOrigin.lean#L46" _blank
  click n168 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/InflateDecodeTableRejection.lean#L19" _blank
  click n169 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/InflateDecodeTableSemantics.lean#L51" _blank
  click n170 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/InflateDecodeTableShort.lean#L26" _blank
  click n171 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/InflateDecodeTableSoundness.lean#L31" _blank
  click n172 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/InflateDecodeTableFrame.lean#L20" _blank
  click n173 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/InflateDecodeTableInvariant.lean#L51" _blank
  click n174 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/InflateDecodeTableInvariant.lean#L68" _blank
  click n175 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/InflateDecodeTableStability.lean#L30" _blank
  click n176 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/InflateDecodeTableStability.lean#L43" _blank
  click n177 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/InflateDecodeTableStability.lean#L54" _blank
  click n178 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/InflateFastTableFlags.lean#L52" _blank
  click n179 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/InflateFastTableFlags.lean#L66" _blank
  click n180 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/InflateFastTableFlags.lean#L76" _blank
  click n181 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/InflateFastTableFlags.lean#L42" _blank
  click n182 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/InflateTableContent.lean#L32" _blank
  click n183 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/InflateTableSafety.lean#L28" _blank
  click n184 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/InflateTableExtent.lean#L28" _blank
  click n185 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/InflateRootTable.lean#L21" _blank
  click n186 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/InflateSubtable.lean#L26" _blank
  click n187 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Math/LZ77CopySpec.lean#L22" _blank
  click n188 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Math/LZ77CopySpec.lean#L32" _blank
  click n189 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Math/LZ77HistorySpec.lean#L21" _blank
  click n190 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Math/LZ77HistorySpec.lean#L15" _blank
  click n191 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Math/LZ77HistorySpec.lean#L29" _blank
  click n192 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Math/LZ77HistorySpec.lean#L39" _blank
  click n193 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Format/Token.lean#L84" _blank
  click n194 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Format/Token.lean#L62" _blank
  click n195 href "https://github.com/cla7aye15I4nd/zlib-f/blob/dd539a50c8a20b7591d0e8bcd801b682e232c544/ZlibF/Spec/Format/Token.lean#L73" _blank
  classDef unproved fill:#e5e7eb,color:#374151,stroke:#374151
  classDef default fill:#dbeafe,color:#1d4ed8,stroke:#1d4ed8
  classDef common fill:#fef3c7,color:#92400e,stroke:#92400e
  classDef all fill:#dcfce7,color:#166534,stroke:#166534
  classDef obstacle stroke:#b91c1c,stroke-width:3px
```

Each node opens its exact target or blocker at the fixed source snapshot
`dd539a5`. Some viewers disable diagram links; the
[evidence index](progress.md) provides ordinary links and all proof references.

No documented blockers in this snapshot.


## Target evidence

<!-- proof-link-revision: dd539a50c8a20b7591d0e8bcd801b682e232c544 -->

[Proof narrative](overview.md) · [All-target graph](#proof-progress-graph) · [Input configurations](spec/input-configurations.md)

This index contains **196 fixed targets**: public execution,
sequence and initialization targets, internal obligations and abstract models.
There is one status graph, in progress. A model result is not implementation refinement.
Input coverage and proof registration are separate. An exact local proof can
cover its complete stated domain while still awaiting registration and CI.
Internal premises remain part of the statement; green does not remove them.
A source-only candidate never grants coverage. Disallowed axioms stop generation.

Why can an isolated node be unfinished? Its proof dependencies have not been
established. Missing arrows neither prove independence nor supply a proof plan.
Some Markdown viewers disable diagram links; use these ordinary source links.

## Status key

<a id="status-registered"></a>Registered proof: an exact checked theorem is listed.
<a id="status-local"></a>Locally checked: an exact theorem exists but is not listed.
<a id="status-open"></a>Not proved: no exact theorem covers this target.
<a id="status-blocked"></a>Blocked: a documented obstacle applies to the target.
These labels do not assign input coverage or replace named-commit CI acceptance.
"All stated inputs" means every input the goal itself states. A goal can state less than zlib.h
allows: [No-fault coverage of zlib.h functions](#no-fault-coverage-of-zlibh-functions) lists the gaps.

<a id="group-queries"></a>

## Library queries

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-compressbound"></a>[compressBound](../ZlibF/Spec/Public/Queries.lean#L35) | All stated inputs / Registered proof | [Contract](../docs/spec/api/utility.md#compressbound); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.compressBound](../ZlibF/Proof/public-compress-bound.lean#L49) | — |
| <a id="target-zlibf-spec-public-goal-compressbound-z"></a>[compressBound_z](../ZlibF/Spec/Public/Queries.lean#L40) | All stated inputs / Registered proof | [Contract](../docs/spec/api/utility.md#compressbound_z); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.compressBound_z](../ZlibF/Proof/public-compress-bound.lean#L46) | — |
| <a id="target-zlibf-spec-public-goal-zlibversion"></a>[zlibVersion](../ZlibF/Spec/Public/Queries.lean#L46) | All stated inputs / Registered proof | [Contract](../docs/spec/api/utility.md#zlibversion); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.zlibVersion](../ZlibF/Proof/public-zlib-version.lean#L8) | — |
| <a id="target-zlibf-spec-public-goal-zlibcompileflags"></a>[zlibCompileFlags](../ZlibF/Spec/Public/Queries.lean#L53) | All stated inputs / Registered proof | [Contract](../docs/spec/api/utility.md#zlibcompileflags); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.zlibCompileFlags](../ZlibF/Proof/public-zlib-compile-flags.lean#L6) | — |
| <a id="target-zlibf-spec-public-goal-zerror"></a>[zError](../ZlibF/Spec/Public/Queries.lean#L59) | All stated inputs / Registered proof | [Contract](../docs/spec/api/utility.md#zerror); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.zError](../ZlibF/Proof/public-zerror.lean#L37) | — |
| <a id="target-zlibf-spec-public-goal-get-crc-table"></a>[get_crc_table](../ZlibF/Spec/Public/Checksums.lean#L126) | All stated inputs / Registered proof | [Contract](../docs/spec/api/checksums.md#get_crc_table); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.get_crc_table](../ZlibF/Proof/public-get-crc-table.lean#L13) | — |

<a id="group-checksums"></a>

## Checksums

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-adler32"></a>[adler32](../ZlibF/Spec/Public/Checksums.lean#L66) | All stated inputs / Registered proof | [Contract](../docs/spec/api/checksums.md#adler32); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.AdlerUpdateProof.adler_public](../ZlibF/Proof/public-adler-update.lean#L46) | — |
| <a id="target-zlibf-spec-public-goal-adler32-z"></a>[adler32_z](../ZlibF/Spec/Public/Checksums.lean#L61) | All stated inputs / Registered proof | [Contract](../docs/spec/api/checksums.md#adler32_z); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.AdlerUpdateProof.adler_z_public](../ZlibF/Proof/public-adler-update.lean#L36) | — |
| <a id="target-zlibf-spec-public-goal-adler32-combine"></a>[adler32_combine](../ZlibF/Spec/Public/Checksums.lean#L86) | All stated inputs / Registered proof | [Contract](../docs/spec/api/checksums.md#adler32_combine); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.AdlerCombineProof.combine_public](../ZlibF/Proof/public-adler-combine.lean#L118) | — |
| <a id="target-zlibf-spec-public-goal-adler32-combine64"></a>[adler32_combine64](../ZlibF/Spec/Public/Checksums.lean#L90) | All stated inputs / Registered proof | [Contract](../docs/spec/api/checksums.md#adler32_combine64); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.AdlerCombineProof.combine64_public](../ZlibF/Proof/public-adler-combine.lean#L121) | — |
| <a id="target-zlibf-spec-public-goal-crc32"></a>[crc32](../ZlibF/Spec/Public/Checksums.lean#L117) | All stated inputs / Registered proof | [Contract](../docs/spec/api/checksums.md#crc32); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.crc32](../ZlibF/Proof/public-crc-updates.lean#L28) | — |
| <a id="target-zlibf-spec-public-goal-crc32-z"></a>[crc32_z](../ZlibF/Spec/Public/Checksums.lean#L109) | All stated inputs / Registered proof | [Contract](../docs/spec/api/checksums.md#crc32_z); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.crc32_z](../ZlibF/Proof/public-crc-updates.lean#L18) | — |
| <a id="target-zlibf-spec-public-goal-crc32-combine-gen"></a>[crc32_combine_gen](../ZlibF/Spec/Public/Checksums.lean#L140) | All stated inputs / Registered proof | [Contract](../docs/spec/api/checksums.md#crc32_combine_gen); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.CrcCombineProof.gen](../ZlibF/Proof/public-crc-combine.lean#L76) | — |
| <a id="target-zlibf-spec-public-goal-crc32-combine-gen64"></a>[crc32_combine_gen64](../ZlibF/Spec/Public/Checksums.lean#L143) | All stated inputs / Registered proof | [Contract](../docs/spec/api/checksums.md#crc32_combine_gen64); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.CrcCombineProof.gen64](../ZlibF/Proof/public-crc-combine.lean#L82) | — |
| <a id="target-zlibf-spec-public-goal-crc32-combine-op"></a>[crc32_combine_op](../ZlibF/Spec/Public/Checksums.lean#L150) | All stated inputs / Registered proof | [Contract](../docs/spec/api/checksums.md#crc32_combine_op); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.CrcCombineProof.op](../ZlibF/Proof/public-crc-combine.lean#L88) | — |
| <a id="target-zlibf-spec-public-goal-crc32-combine"></a>[crc32_combine](../ZlibF/Spec/Public/Checksums.lean#L162) | All stated inputs / Registered proof | [Contract](../docs/spec/api/checksums.md#crc32_combine); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.CrcCombineProof.combine](../ZlibF/Proof/public-crc-combine.lean#L94) | — |
| <a id="target-zlibf-spec-public-goal-crc32-combine64"></a>[crc32_combine64](../ZlibF/Spec/Public/Checksums.lean#L165) | All stated inputs / Registered proof | [Contract](../docs/spec/api/checksums.md#crc32_combine64); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.CrcCombineProof.combine64](../ZlibF/Proof/public-crc-combine.lean#L100) | — |

<a id="group-addresses"></a>

## Byte-address model

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-c-byteaddress-spec-goal-address-read-is-pure"></a>[address_read_is_pure](../ZlibF/Spec/ByteAddress.lean#L39) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.address_read_is_pure](../ZlibF/Proof/ByteAddress.lean#L28) | — |
| <a id="target-c-byteaddress-spec-goal-raw-block-unchanged"></a>[raw_block_unchanged](../ZlibF/Spec/ByteAddress.lean#L43) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.raw_block_unchanged](../ZlibF/Proof/ByteAddress.lean#L33) | — |
| <a id="target-c-byteaddress-spec-goal-every-layout-is-representable"></a>[every_layout_is_representable](../ZlibF/Spec/ByteAddress.lean#L50) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.every_layout_is_representable](../ZlibF/Proof/ByteAddress.lean#L39) | — |
| <a id="target-c-byteaddress-spec-goal-every-existing-heap-accepts-layout"></a>[every_existing_heap_accepts_layout](../ZlibF/Spec/ByteAddress.lean#L57) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.every_existing_heap_accepts_layout](../ZlibF/Proof/ByteAddress.lean#L94) | — |
| <a id="target-c-byteaddress-spec-goal-mask-refines-base-plus-offset"></a>[mask_refines_base_plus_offset](../ZlibF/Spec/ByteAddress.lean#L65) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.mask_refines_base_plus_offset](../ZlibF/Proof/ByteAddress.lean#L54) | — |
| <a id="target-c-byteaddress-spec-goal-pointer-advance-preserves-low-bits"></a>[pointer_advance_preserves_low_bits](../ZlibF/Spec/ByteAddress.lean#L70) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.pointer_advance_preserves_low_bits](../ZlibF/Proof/ByteAddress.lean#L60) | — |
| <a id="target-c-byteaddress-spec-goal-first-aligned-offset"></a>[first_aligned_offset](../ZlibF/Spec/ByteAddress.lean#L77) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.first_aligned_offset](../ZlibF/Proof/ByteAddress.lean#L67) | — |
| <a id="target-c-byteaddress-spec-goal-byte-stores-preserve-bases"></a>[byte_stores_preserve_bases](../ZlibF/Spec/ByteAddress.lean#L83) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.byte_stores_preserve_bases](../ZlibF/Proof/ByteAddress.lean#L81) | — |
| <a id="target-c-byteaddress-spec-goal-byte-modifies-preserve-bases"></a>[byte_modifies_preserve_bases](../ZlibF/Spec/ByteAddress.lean#L87) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.byte_modifies_preserve_bases](../ZlibF/Proof/ByteAddress.lean#L88) | — |

<a id="group-inflate"></a>

## Inflate streams

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-inflatecopy"></a>[inflateCopy](../ZlibF/Spec/Public/Copy.lean#L27) | All stated inputs / Registered proof | [Contract](../docs/spec/api/inflate-stream.md#inflatecopy); [input range](spec/input-configurations.md#inflate-inputs) | [Zlib.Inflate.Proofs.inflate_copy_public](../ZlibF/Proof/public-inflate-copy.lean#L12) | — |
| <a id="target-zlibf-spec-public-goal-inflateinit2"></a>[inflateInit2_](../ZlibF/Spec/Public/Initialisation.lean#L92) | All stated inputs / Registered proof | [Contract](../docs/spec/api/inflate-stream.md#inflateinit2_); [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.Proofs.InflateInit.inflate_init2_public](../ZlibF/Proof/public-inflate-init2.lean#L19) | — |
| <a id="target-zlibf-spec-public-goal-inflateinit"></a>[inflateInit_](../ZlibF/Spec/Public/Initialisation.lean#L97) | All stated inputs / Registered proof | [Contract](../docs/spec/api/inflate-stream.md#inflateinit_); [input range](spec/input-configurations.md#inflate-inputs) | [Zlib.Inflate.Proofs.inflate_default_init_contract](../ZlibF/Proof/inflate.c.default-entry.lean#L58); [ZlibF.Spec.Public.Proofs.InflateInit.init15_public](../ZlibF/Proof/public-inflate-init.lean#L83) | — |
| <a id="target-zlibf-spec-public-goal-inflateresetkeep"></a>[inflateResetKeep](../ZlibF/Spec/Public/Lifecycle.lean#L20) | All stated inputs / Registered proof | [Contract](../docs/spec/api/inflate-stream.md#inflateresetkeep); [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateResetKeepProof.resetkeep_public](../ZlibF/Proof/public-inflate-reset-keep.lean#L8) | — |
| <a id="target-zlibf-spec-public-goal-inflatereset"></a>[inflateReset](../ZlibF/Spec/Public/Lifecycle.lean#L32) | All stated inputs / Registered proof | [Contract](../docs/spec/api/inflate-stream.md#inflatereset); [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateResetProof.reset_public](../ZlibF/Proof/public-inflate-reset.lean#L16) | — |
| <a id="target-zlibf-spec-public-goal-inflatereset2"></a>[inflateReset2](../ZlibF/Spec/Public/Lifecycle.lean#L43) | All stated inputs / Registered proof | [Contract](../docs/spec/api/inflate-stream.md#inflatereset2); [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateReset2Proof.reset2_public](../ZlibF/Proof/public-inflate-reset2.lean#L61) | — |
| <a id="target-zlibf-spec-public-goal-inflateend"></a>[inflateEnd](../ZlibF/Spec/Public/Lifecycle.lean#L60) | All stated inputs / Registered proof | [Contract](../docs/spec/api/inflate-stream.md#inflateend); [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateEndProof.inflate_end_public](../ZlibF/Proof/public-inflate-end.lean#L55) | — |
| <a id="target-zlibf-spec-public-goal-inflategetdictionary"></a>[inflateGetDictionary](../ZlibF/Spec/Public/Lifecycle.lean#L77) | All stated inputs / Registered proof | [Contract](../docs/spec/api/inflate-stream.md#inflategetdictionary); [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateDictionaryProof.inflate_getdict_public](../ZlibF/Proof/public-inflate-getdict.lean#L10) | — |
| <a id="target-zlibf-spec-public-goal-inflategetheader"></a>[inflateGetHeader](../ZlibF/Spec/Public/Lifecycle.lean#L87) | All stated inputs / Registered proof | [Contract](../docs/spec/api/inflate-stream.md#inflategetheader); [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateHeaderProof.getheader_public](../ZlibF/Proof/public-inflate-header.lean#L34) | — |
| <a id="target-zlibf-spec-public-goal-inflatesetdictionary"></a>[inflateSetDictionary](../ZlibF/Spec/Public/Lifecycle.lean#L153) | All stated inputs / Registered proof | [Contract](../docs/spec/api/inflate-stream.md#inflatesetdictionary); [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.Proofs.inflateSetDictionary_public](../ZlibF/Proof/public-inflate-setdict.lean#L92) | — |
| <a id="target-zlibf-spec-public-goal-inflatesyncpoint"></a>[inflateSyncPoint](../ZlibF/Spec/Public/StreamQueries.lean#L53) | All stated inputs / Registered proof | [Contract](../docs/spec/api/inflate-stream.md#inflatesyncpoint); [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateQueryProof.syncpoint_public](../ZlibF/Proof/public-inflate-small-queries.lean#L44) | — |
| <a id="target-zlibf-spec-public-goal-inflatemark"></a>[inflateMark](../ZlibF/Spec/Public/StreamQueries.lean#L62) | All stated inputs / Registered proof | [Contract](../docs/spec/api/inflate-stream.md#inflatemark); [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateMarkProof.mark_public](../ZlibF/Proof/public-inflate-mark.lean#L71) | — |
| <a id="target-zlibf-spec-public-goal-inflatecodesused"></a>[inflateCodesUsed](../ZlibF/Spec/Public/StreamQueries.lean#L73) | All stated inputs / Registered proof | [Contract](../docs/spec/api/inflate-stream.md#inflatecodesused); [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.Proofs.inflate_codes_used](../ZlibF/Proof/Api/QueryLayout.lean#L71) | — |
| <a id="target-zlibf-spec-public-goal-inflateundermine"></a>[inflateUndermine](../ZlibF/Spec/Public/StreamQueries.lean#L81) | All stated inputs / Registered proof | [Contract](../docs/spec/api/inflate-stream.md#inflateundermine); [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateQueryProof.undermine_public](../ZlibF/Proof/public-inflate-small-queries.lean#L60) | — |
| <a id="target-zlibf-spec-public-goal-inflatevalidate"></a>[inflateValidate](../ZlibF/Spec/Public/StreamQueries.lean#L89) | All stated inputs / Registered proof | [Contract](../docs/spec/api/inflate-stream.md#inflatevalidate); [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateQueryProof.validate_public](../ZlibF/Proof/public-inflate-small-queries.lean#L75) | — |
| <a id="target-zlibf-spec-public-goal-inflateprime"></a>[inflatePrime](../ZlibF/Spec/Public/StreamQueries.lean#L100) | All stated inputs / Registered proof | [Contract](../docs/spec/api/inflate-stream.md#inflateprime); [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflatePrimeProof.prime_public](../ZlibF/Proof/public-inflate-prime.lean#L117) | — |
| <a id="target-zlibf-spec-public-goal-inflate"></a>[inflate](../ZlibF/Spec/Public/Streams.lean#L35) | All stated inputs / Registered proof | [Contract](../docs/spec/api/inflate-stream.md#inflate); [input range](spec/input-configurations.md#inflate-inputs) | [Zlib.Inflate.Proofs.inflate_public](../ZlibF/Proof/public-inflate.lean#L10) | — |
| <a id="target-zlibf-spec-public-goal-inflatesync"></a>[inflateSync](../ZlibF/Spec/Public/Streams.lean#L209) | Not proved / Not proved | [Contract](../docs/spec/api/inflate-stream.md#inflatesync); [input range](spec/input-configurations.md#inflate-inputs) | — | [Needs: scan and history](progress.md#readiness-inflatesync) |
| <a id="target-zlibf-spec-public-goal-inflate-sequence-safety"></a>[inflate_sequence_safety](../ZlibF/Spec/Public/Sequences.lean#L268) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#inflate-inputs) | [Zlib.Inflate.Proofs.inflate_sequence_safety_public](../ZlibF/Proof/public-inflate-sequence-safety.lean#L10) | — |
| <a id="target-zlibf-spec-public-goal-inflate-back-sequence-safety"></a>[inflate_back_sequence_safety](../ZlibF/Spec/Public/Sequences.lean#L396) | Not proved / Not proved | Exact target statement; [input range](spec/input-configurations.md#inflate-inputs) | — | Prerequisites unreviewed |
| <a id="target-zlibf-spec-public-goal-inflate-refusal"></a>[inflate_refusal](../ZlibF/Spec/Public/Refusals.lean#L25) | All stated inputs / Locally checked | Exact target statement; [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.RefusalProof.inflate_refusal](../ZlibF/Proof/public-stream-refusal.lean#L46) | — |

<a id="group-fast"></a>

## Fast decoder obligations

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlib-inffast-spec-bodyorigin-goal-actual-body-preserves-origin"></a>[actual_body_preserves_origin](../ZlibF/Spec/InflateFastBodyOrigin.lean#L18) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.BodyOriginProof.actual_body_preserves_origin](../ZlibF/Proof/inffast.c.body-origin.lean#L380); [Zlib.Inffast.Proofs.actual_body_preserves_origin](../ZlibF/Proof/inffast.c.body-origin.lean#L380) | — |
| <a id="target-zlib-inffast-spec-bodytoken-goal-actual-body-refines-token"></a>[actual_body_refines_token](../ZlibF/Spec/InflateFastBodyToken.lean#L73) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.BodyTokenProof.actual_body_refines_token](../ZlibF/Proof/inffast.c.body-token.lean#L571); [Zlib.Inffast.Proofs.actual_body_refines_token](../ZlibF/Proof/inffast.c.body-token.lean#L571) | — |
| <a id="target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin"></a>[actual_fast_preserves_origin](../ZlibF/Spec/InflateFastCallOrigin.lean#L24) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_fast_preserves_origin](../ZlibF/Proof/inffast.c.call-origin.lean#L180); [ZlibF.Proof.Registration.fast_call_origin](../ZlibF/Proof/proof-registrations.lean#L14) | — |
| <a id="target-zlib-inffast-spec-distanceorigin-goal-actual-distance-block-preserves-origin"></a>[actual_distance_block_preserves_origin](../ZlibF/Spec/InflateFastDistanceOrigin.lean#L18) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_distance_block_preserves_origin](../ZlibF/Proof/inffast.c.distance-origin.lean#L327) | — |
| <a id="target-zlib-inffast-spec-distanceresult-goal-actual-distance-refines-lz77"></a>[actual_distance_refines_lz77](../ZlibF/Spec/InflateFastDistanceResult.lean#L101) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_distance_refines_lz77](../ZlibF/Proof/inffast.c.distance-result.lean#L386) | — |
| <a id="target-zlib-inffast-spec-distancesemantics-goal-distance-lookup-matches-format"></a>[distance_lookup_matches_format](../ZlibF/Spec/InflateFastDistanceSemantics.lean#L20) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.distance_lookup_matches_format](../ZlibF/Proof/inffast.c.distance-semantics.lean#L22) | — |
| <a id="target-zlib-inffast-spec-goal-fast-safe"></a>[fast_safe](../ZlibF/Spec/InflateFast.lean#L70) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.inflate_fast_safe](../ZlibF/Proof/inffast.c.final.lean#L259) | — |
| <a id="target-zlib-inffast-spec-goal-step-safe"></a>[step_safe](../ZlibF/Spec/InflateFast.lean#L42) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.inflate_fast_body_step_safe](../ZlibF/Proof/inffast.c.body.lean#L350) | — |
| <a id="target-zlib-inffast-spec-lengthsemantics-goal-length-lookup-matches-format"></a>[length_lookup_matches_format](../ZlibF/Spec/InflateFastLengthSemantics.lean#L34) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.length_lookup_matches_format](../ZlibF/Proof/inffast.c.length-semantics.lean#L22) | — |
| <a id="target-zlib-inffast-spec-lengthtrace-goal-actual-body-retains-selected-length"></a>[actual_body_retains_selected_length](../ZlibF/Spec/InflateFastLengthTrace.lean#L51) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.LengthTraceProof.actual_body_retains_selected_length](../ZlibF/Proof/inffast.c.length-trace.lean#L250); [Zlib.Inffast.Proofs.actual_body_retains_selected_length](../ZlibF/Proof/inffast.c.length-trace.lean#L250) | — |
| <a id="target-zlib-inffast-spec-matchhistory-goal-actual-copy-match-refines-lz77"></a>[actual_copy_match_refines_lz77](../ZlibF/Spec/InflateFastMatchHistory.lean#L39) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_copy_match_refines_lz77](../ZlibF/Proof/inffast.c.match-history.lean#L329) | — |
| <a id="target-zlib-inffast-spec-matchhistory-goal-match-array-refines-lz77"></a>[match_array_refines_lz77](../ZlibF/Spec/InflateFastMatchHistory.lean#L25) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.fast_match_array_refines_lz77](../ZlibF/Math/InflateFastMatchHistory.lean#L56) | — |
| <a id="target-zlib-inffast-spec-origin-goal-actual-drop-preserves-origin"></a>[actual_drop_preserves_origin](../ZlibF/Spec/InflateFastOrigin.lean#L68) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_drop_preserves_origin](../ZlibF/Proof/inffast.c.origin.lean#L138) | — |
| <a id="target-zlib-inffast-spec-origin-goal-actual-pull-preserves-origin"></a>[actual_pull_preserves_origin](../ZlibF/Spec/InflateFastOrigin.lean#L57) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_pull_preserves_origin](../ZlibF/Proof/inffast.c.origin.lean#L127) | — |
| <a id="target-zlib-inffast-spec-origin-goal-actual-rollback-preserves-origin"></a>[actual_rollback_preserves_origin](../ZlibF/Spec/InflateFastOrigin.lean#L81) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_rollback_preserves_origin](../ZlibF/Proof/inffast.c.origin.lean#L150) | — |
| <a id="target-zlib-inffast-spec-origin-goal-drop-preserves-origin"></a>[drop_preserves_origin](../ZlibF/Spec/InflateFastOrigin.lean#L38) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.drop_preserves_origin](../ZlibF/Proof/inffast.c.origin.lean#L41) | — |
| <a id="target-zlib-inffast-spec-origin-goal-initial-origin"></a>[initial_origin](../ZlibF/Spec/InflateFastOrigin.lean#L27) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.initial_origin](../ZlibF/Proof/inffast.c.origin.lean#L16) | — |
| <a id="target-zlib-inffast-spec-origin-goal-pull-preserves-origin"></a>[pull_preserves_origin](../ZlibF/Spec/InflateFastOrigin.lean#L32) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.pull_preserves_origin](../ZlibF/Proof/inffast.c.origin.lean#L21) | — |
| <a id="target-zlib-inffast-spec-origin-goal-rollback-preserves-origin"></a>[rollback_preserves_origin](../ZlibF/Spec/InflateFastOrigin.lean#L46) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.rollback_preserves_origin](../ZlibF/Proof/inffast.c.origin.lean#L83) | — |

<a id="group-tables"></a>

## Decode-table obligations

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlib-inftrees-spec-decoderejection-goal-decode-table-classifies-input"></a>[decode_table_classifies_input](../ZlibF/Spec/InflateDecodeTableRejection.lean#L19) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.decode_table_classifies_input](../ZlibF/Proof/inftrees.c.decode.short.lean#L62) | — |
| <a id="target-zlib-inftrees-spec-decodesemantics-goal-decode-table-matches-format"></a>[decode_table_matches_format](../ZlibF/Spec/InflateDecodeTableSemantics.lean#L51) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.decode_table_matches_format](../ZlibF/Proof/inftrees.c.decode.semantics.lean#L327) | — |
| <a id="target-zlib-inftrees-spec-decodeshort-goal-short-decode-table-leaf-sound"></a>[short_decode_table_leaf_sound](../ZlibF/Spec/InflateDecodeTableShort.lean#L26) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.short_decode_table_leaf_sound](../ZlibF/Proof/inftrees.c.decode.short.lean#L33) | — |
| <a id="target-zlib-inftrees-spec-decodesoundness-goal-decode-table-leaf-sound"></a>[decode_table_leaf_sound](../ZlibF/Spec/InflateDecodeTableSoundness.lean#L31) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.decode_table_leaf_sound](../ZlibF/Proof/inftrees.c.decode.soundness.lean#L244) | — |
| <a id="target-zlib-inftrees-spec-decodetableframe-goal-decode-table-read-preserved"></a>[decode_table_read_preserved](../ZlibF/Spec/InflateDecodeTableFrame.lean#L20) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.decode_table_read_preserved](../ZlibF/Proof/inftrees.c.decode.frame.lean#L55) | — |
| <a id="target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant"></a>[constructor_establishes_decode_table_invariant](../ZlibF/Spec/InflateDecodeTableInvariant.lean#L51) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.constructor_establishes_decode_table_invariant](../ZlibF/Proof/inftrees.c.decode.invariant.lean#L13) | — |
| <a id="target-zlib-inftrees-spec-decodetableinvariant-goal-decode-table-invariant-of-prefix"></a>[decode_table_invariant_of_prefix](../ZlibF/Spec/InflateDecodeTableInvariant.lean#L68) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.decode_table_invariant_of_prefix](../ZlibF/Proof/inftrees.c.decode.invariant-prefix.lean#L22) | — |
| <a id="target-zlib-inftrees-spec-decodetablestability-goal-constructor-establishes-query-stability"></a>[constructor_establishes_query_stability](../ZlibF/Spec/InflateDecodeTableStability.lean#L30) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.constructor_establishes_query_stability](../ZlibF/Proof/inftrees.c.decode.stability.lean#L190) | — |
| <a id="target-zlib-inftrees-spec-decodetablestability-goal-query-stability-of-prefix"></a>[query_stability_of_prefix](../ZlibF/Spec/InflateDecodeTableStability.lean#L43) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.query_stability_of_prefix](../ZlibF/Proof/inftrees.c.decode.stability-rejection.lean#L20) | — |
| <a id="target-zlib-inftrees-spec-decodetablestability-goal-short-rejected-leaf-stays-invalid"></a>[short_rejected_leaf_stays_invalid](../ZlibF/Spec/InflateDecodeTableStability.lean#L54) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.short_rejected_leaf_stays_invalid](../ZlibF/Proof/inftrees.c.decode.stability-rejection.lean#L31) | — |
| <a id="target-zlib-inftrees-spec-fasttableflags-goal-constructor-establishes-fast-leaf-flags"></a>[constructor_establishes_fast_leaf_flags](../ZlibF/Spec/InflateFastTableFlags.lean#L52) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.constructor_establishes_fast_leaf_flags](../ZlibF/Proof/inftrees.c.decode.fast-flags.lean#L125) | — |
| <a id="target-zlib-inftrees-spec-fasttableflags-goal-fast-leaf-flags-of-prefix"></a>[fast_leaf_flags_of_prefix](../ZlibF/Spec/InflateFastTableFlags.lean#L66) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.fast_leaf_flags_of_prefix](../ZlibF/Proof/inftrees.c.decode.fast-flags-frame.lean#L48); [ZlibF.Proof.Registration.fast_leaf_flags_of_prefix](../ZlibF/Proof/proof-registrations.lean#L20) | — |
| <a id="target-zlib-inftrees-spec-fasttableflags-goal-fixed-tables-have-fast-leaf-flags"></a>[fixed_tables_have_fast_leaf_flags](../ZlibF/Spec/InflateFastTableFlags.lean#L76) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.fixed_tables_have_fast_leaf_flags](../ZlibF/Proof/inffixed.h.fast-flags.lean#L55); [ZlibF.Proof.Registration.fixed_tables_fast_leaf_flags](../ZlibF/Proof/proof-registrations.lean#L26) | — |
| <a id="target-zlib-inftrees-spec-fasttableflags-goal-leaf-classification-agrees"></a>[leaf_classification_agrees](../ZlibF/Spec/InflateFastTableFlags.lean#L42) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.leaf_classification_agrees](../ZlibF/Proof/inftrees.c.decode.fast-flags-frame.lean#L9); [ZlibF.Proof.Registration.leaf_classification_agrees](../ZlibF/Proof/proof-registrations.lean#L32) | — |
| <a id="target-zlib-inftrees-spec-goal-inflate-table-content"></a>[inflate_table_content](../ZlibF/Spec/InflateTableContent.lean#L32) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.inflate_table_content](../ZlibF/Proof/inftrees.c.content.lean#L327) | — |
| <a id="target-zlib-inftrees-spec-goal-inflate-table-decoder-safe"></a>[inflate_table_decoder_safe](../ZlibF/Spec/InflateTableSafety.lean#L28) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.inflate_table_decoder_safe](../ZlibF/Proof/inftrees.c.decoder-safe.lean#L143) | — |
| <a id="target-zlib-inftrees-spec-goal-inflate-table-read-extent"></a>[inflate_table_read_extent](../ZlibF/Spec/InflateTableExtent.lean#L28) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.inflate_table_read_extent](../ZlibF/Proof/inftrees.c.read-extent.lean#L139) | — |
| <a id="target-zlib-inftrees-spec-roottable-goal-constructor-root-bits"></a>[constructor_root_bits](../ZlibF/Spec/InflateRootTable.lean#L21) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.constructor_root_bits](../ZlibF/Proof/inftrees.c.decode.bits.lean#L260) | — |
| <a id="target-zlib-inftrees-spec-subtable-goal-constructor-subtable-bits"></a>[constructor_subtable_bits](../ZlibF/Spec/InflateSubtable.lean#L26) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.constructor_subtable_bits](../ZlibF/Proof/inftrees.c.decode.bits.lean#L221) | — |

<a id="group-copy"></a>

## Match-copy mathematics

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-math-lz77copy-goal-output-copy-refines-lz77"></a>[output_copy_refines_lz77](../ZlibF/Math/LZ77CopySpec.lean#L22) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Math.LZ77Copy.output_copy_refines_lz77](../ZlibF/Math/LZ77Copy.lean#L65) | — |
| <a id="target-zlibf-math-lz77copy-goal-window-copy-refines-lz77"></a>[window_copy_refines_lz77](../ZlibF/Math/LZ77CopySpec.lean#L32) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Math.LZ77Copy.window_copy_refines_lz77](../ZlibF/Math/LZ77Copy.lean#L124) | — |
| <a id="target-zlibf-math-lz77history-goal-copy-back-compose"></a>[copy_back_compose](../ZlibF/Math/LZ77HistorySpec.lean#L21) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Math.LZ77History.copy_back_compose](../ZlibF/Math/LZ77History.lean#L31) | — |
| <a id="target-zlibf-math-lz77history-goal-copy-back-extends-history"></a>[copy_back_extends_history](../ZlibF/Math/LZ77HistorySpec.lean#L15) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Math.LZ77History.copy_back_extends_history](../ZlibF/Math/LZ77History.lean#L17) | — |
| <a id="target-zlibf-math-lz77history-goal-retained-history-agrees"></a>[retained_history_agrees](../ZlibF/Math/LZ77HistorySpec.lean#L29) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Math.LZ77History.retained_history_agrees](../ZlibF/Math/LZ77History.lean#L59) | — |
| <a id="target-zlibf-math-lz77history-goal-window-distance-check-agrees"></a>[window_distance_check_agrees](../ZlibF/Math/LZ77HistorySpec.lean#L39) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Math.LZ77History.window_distance_check_agrees](../ZlibF/Math/LZ77History.lean#L72) | — |

<a id="group-deflate"></a>

## Deflate streams

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-deflatecopy"></a>[deflateCopy](../ZlibF/Spec/Public/Copy.lean#L67) | All stated inputs / Locally checked | [Contract](../docs/spec/api/deflate-stream.md#deflatecopy); [input range](spec/input-configurations.md#deflate-inputs) | [Zlib.Deflate.Universal.deflate_copy_public](../ZlibF/Proof/public-deflate-copy.lean#L65) | — |
| <a id="target-zlibf-spec-public-goal-deflateinit2"></a>[deflateInit2_](../ZlibF/Spec/Public/Initialisation.lean#L140) | All stated inputs / Registered proof | [Contract](../docs/spec/api/deflate-stream.md#deflateinit2_); [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.Proofs.DeflateInit2.deflateInit2_proof](../ZlibF/Proof/public-deflate-init2.lean#L17) | — |
| <a id="target-zlibf-spec-public-goal-deflateinit"></a>[deflateInit_](../ZlibF/Spec/Public/Initialisation.lean#L147) | All stated inputs / Registered proof | [Contract](../docs/spec/api/deflate-stream.md#deflateinit_); [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.Proofs.DeflateInit.deflateInit_proof](../ZlibF/Proof/public-deflate-init.lean#L161) | — |
| <a id="target-zlibf-spec-public-goal-deflategetdictionary"></a>[deflateGetDictionary](../ZlibF/Spec/Public/Lifecycle.lean#L105) | All stated inputs / Registered proof | [Contract](../docs/spec/api/deflate-stream.md#deflategetdictionary); [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateDictionaryProof.deflate_getdict_public](../ZlibF/Proof/public-deflate-getdict.lean#L10) | — |
| <a id="target-zlibf-spec-public-goal-deflateend"></a>[deflateEnd](../ZlibF/Spec/Public/Lifecycle.lean#L115) | All stated inputs / Registered proof | [Contract](../docs/spec/api/deflate-stream.md#deflateend); [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateEndProof.deflate_end_public](../ZlibF/Proof/public-deflate-end.lean#L10) | — |
| <a id="target-zlibf-spec-public-goal-deflateresetkeep"></a>[deflateResetKeep](../ZlibF/Spec/Public/Lifecycle.lean#L146) | All stated inputs / Registered proof | [Contract](../docs/spec/api/deflate-stream.md#deflateresetkeep); [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateResetKeepProof.deflate_resetkeep_public](../ZlibF/Proof/public-deflate-reset-keep.lean#L19) | — |
| <a id="target-zlibf-spec-public-goal-deflatereset"></a>[deflateReset](../ZlibF/Spec/Public/Lifecycle.lean#L149) | All stated inputs / Registered proof | [Contract](../docs/spec/api/deflate-stream.md#deflatereset); [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateResetProof.deflate_reset_public](../ZlibF/Proof/public-deflate-reset.lean#L52) | — |
| <a id="target-zlibf-spec-public-goal-deflatesetdictionary"></a>[deflateSetDictionary](../ZlibF/Spec/Public/Lifecycle.lean#L175) | Not proved / Not proved | [Contract](../docs/spec/api/deflate-stream.md#deflatesetdictionary); [input range](spec/input-configurations.md#deflate-inputs) | — | [Start: window and hash](progress.md#readiness-deflatesetdictionary) |
| <a id="target-zlibf-spec-public-goal-deflatepending"></a>[deflatePending](../ZlibF/Spec/Public/StreamQueries.lean#L113) | All stated inputs / Registered proof | [Contract](../docs/spec/api/deflate-stream.md#deflatepending); [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateQueryProof.pending_public](../ZlibF/Proof/public-deflate-small-queries.lean#L145) | — |
| <a id="target-zlibf-spec-public-goal-deflateused"></a>[deflateUsed](../ZlibF/Spec/Public/StreamQueries.lean#L124) | All stated inputs / Registered proof | [Contract](../docs/spec/api/deflate-stream.md#deflateused); [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateQueryProof.used_public](../ZlibF/Proof/public-deflate-small-queries.lean#L48) | — |
| <a id="target-zlibf-spec-public-goal-deflatetune"></a>[deflateTune](../ZlibF/Spec/Public/StreamQueries.lean#L132) | All stated inputs / Registered proof | [Contract](../docs/spec/api/deflate-stream.md#deflatetune); [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateQueryProof.tune_public](../ZlibF/Proof/public-deflate-small-queries.lean#L61) | — |
| <a id="target-zlibf-spec-public-goal-deflatesetheader"></a>[deflateSetHeader](../ZlibF/Spec/Public/StreamQueries.lean#L145) | All stated inputs / Registered proof | [Contract](../docs/spec/api/deflate-stream.md#deflatesetheader); [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateQueryProof.header_public](../ZlibF/Proof/public-deflate-small-queries.lean#L74) | — |
| <a id="target-zlibf-spec-public-goal-deflate"></a>[deflate](../ZlibF/Spec/Public/Streams.lean#L87) | All stated inputs / Registered proof | [Contract](../docs/spec/api/deflate-stream.md#deflate); [input range](spec/input-configurations.md#deflate-inputs) | [Zlib.Deflate.Universal.deflate_safety](../ZlibF/Proof/public-deflate-goals.lean#L19) | — |
| <a id="target-zlibf-spec-public-goal-deflatebound-z"></a>[deflateBound_z](../ZlibF/Spec/Public/Streams.lean#L154) | Not proved / Not proved | [Contract](../docs/spec/api/deflate-stream.md#deflatebound_z); [input range](spec/input-configurations.md#deflate-inputs) | — | [Start: bound and header review](progress.md#readiness-deflatebound-z) |
| <a id="target-zlibf-spec-public-goal-deflatebound"></a>[deflateBound](../ZlibF/Spec/Public/Streams.lean#L158) | Not proved / Not proved | [Contract](../docs/spec/api/deflate-stream.md#deflatebound); [input range](spec/input-configurations.md#deflate-inputs) | — | [Start: bound and header review](progress.md#readiness-deflatebound-z) |
| <a id="target-zlibf-spec-public-goal-deflateprime"></a>[deflatePrime](../ZlibF/Spec/Public/Streams.lean#L168) | Not proved / Not proved | [Contract](../docs/spec/api/deflate-stream.md#deflateprime); [input range](spec/input-configurations.md#deflate-inputs) | — | [Start: compaction and bits](progress.md#readiness-deflateprime) |
| <a id="target-zlibf-spec-public-goal-deflateparams"></a>[deflateParams](../ZlibF/Spec/Public/Streams.lean#L186) | Not proved / Not proved | [Contract](../docs/spec/api/deflate-stream.md#deflateparams); [input range](spec/input-configurations.md#deflate-inputs) | — | [Needs: block flush and parameter state](progress.md#readiness-deflateparams) |
| <a id="target-zlibf-spec-public-goal-deflate-sequence-safety"></a>[deflate_sequence_safety](../ZlibF/Spec/Public/Sequences.lean#L259) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#deflate-inputs) | [Zlib.Deflate.Universal.deflate_sequence_safety](../ZlibF/Proof/public-deflate-goals.lean#L24) | — |
| <a id="target-zlibf-spec-public-goal-deflatecopy-safety"></a>[deflateCopy_safety](../ZlibF/Spec/Public/Copy.lean#L106) | All stated inputs / Locally checked | Exact target statement; [input range](spec/input-configurations.md#deflate-inputs) | [Zlib.Deflate.Universal.deflate_copy_safety](../ZlibF/Proof/public-deflate-copy.lean#L81) | — |
| <a id="target-zlibf-spec-public-goal-deflate-refusal"></a>[deflate_refusal](../ZlibF/Spec/Public/Refusals.lean#L45) | All stated inputs / Locally checked | Exact target statement; [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.RefusalProof.Deflate.deflate_refusal](../ZlibF/Proof/public-stream-refusal.lean#L89) | — |

<a id="group-back"></a>

## Callback decoding

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-inflatebackinit"></a>[inflateBackInit_](../ZlibF/Spec/Public/Back.lean#L22) | All stated inputs / Registered proof | [Contract](../docs/spec/api/inflate-back.md#inflatebackinit_); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.InflateBackInitProof.back_init_public](../ZlibF/Proof/public-infback-init.lean#L135) | — |
| <a id="target-zlibf-spec-public-goal-inflateback"></a>[inflateBack](../ZlibF/Spec/Public/Back.lean#L118) | Not proved / Not proved | [Contract](../docs/spec/api/inflate-back.md#inflateback); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: tables, window and callbacks](progress.md#readiness-inflateback) |
| <a id="target-zlibf-spec-public-goal-inflatebackend"></a>[inflateBackEnd](../ZlibF/Spec/Public/Back.lean#L145) | All stated inputs / Registered proof | [Contract](../docs/spec/api/inflate-back.md#inflatebackend); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.InflateBackEndProof.back_end_public](../ZlibF/Proof/public-infback-end.lean#L20) | — |

<a id="group-gzip"></a>

## Gzip files

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-gzclose-r"></a>[gzclose_r](../ZlibF/Spec/Public/GzClose.lean#L35) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzclose_r); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: resource history](progress.md#readiness-gzclose-r) |
| <a id="target-zlibf-spec-public-goal-gzclose-w"></a>[gzclose_w](../ZlibF/Spec/Public/GzClose.lean#L40) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzclose_w); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: flush and cleanup](progress.md#readiness-gzclose-w) |
| <a id="target-zlibf-spec-public-goal-gzclose"></a>[gzclose](../ZlibF/Spec/Public/GzClose.lean#L44) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzclose); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: flush and cleanup](progress.md#readiness-gzclose-w) |
| <a id="target-zlibf-spec-public-goal-gzbuffer"></a>[gzbuffer](../ZlibF/Spec/Public/GzControl.lean#L12) | All stated inputs / Registered proof | [Contract](../docs/spec/api/gz-file.md#gzbuffer); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.gzbuffer_public](../ZlibF/Proof/public-gzbuffer.lean#L49) | — |
| <a id="target-zlibf-spec-public-goal-gzeof"></a>[gzeof](../ZlibF/Spec/Public/GzControl.lean#L22) | All stated inputs / Registered proof | [Contract](../docs/spec/api/gz-file.md#gzeof); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.gzeof_public](../ZlibF/Proof/public-gzeof.lean#L18) | — |
| <a id="target-zlibf-spec-public-goal-gztell64"></a>[gztell64](../ZlibF/Spec/Public/GzControl.lean#L36) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gztell64); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: position history](progress.md#readiness-gztell64) |
| <a id="target-zlibf-spec-public-goal-gztell"></a>[gztell](../ZlibF/Spec/Public/GzControl.lean#L39) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gztell); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: position history](progress.md#readiness-gztell64) |
| <a id="target-zlibf-spec-public-goal-gzoffset64"></a>[gzoffset64](../ZlibF/Spec/Public/GzControl.lean#L53) | All stated inputs / Registered proof | [Contract](../docs/spec/api/gz-file.md#gzoffset64); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.OffsetProof.gzoffset64_public_goal](../ZlibF/Proof/public-gz-offset.lean#L231) | — |
| <a id="target-zlibf-spec-public-goal-gzoffset"></a>[gzoffset](../ZlibF/Spec/Public/GzControl.lean#L56) | All stated inputs / Registered proof | [Contract](../docs/spec/api/gz-file.md#gzoffset); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.OffsetProof.gzoffset_public_goal](../ZlibF/Proof/public-gz-offset.lean#L244) | — |
| <a id="target-zlibf-spec-public-goal-gzerror"></a>[gzerror](../ZlibF/Spec/Public/GzControl.lean#L63) | All stated inputs / Registered proof | [Contract](../docs/spec/api/gz-file.md#gzerror); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzErrorProof.gzerror](../ZlibF/Proof/public-gz-error.lean#L206) | — |
| <a id="target-zlibf-spec-public-goal-gzclearerr"></a>[gzclearerr](../ZlibF/Spec/Public/GzControl.lean#L74) | All stated inputs / Registered proof | [Contract](../docs/spec/api/gz-file.md#gzclearerr); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.gzclearerr](../ZlibF/Proof/gzlib.c.public-clearerr.lean#L28) | — |
| <a id="target-zlibf-spec-public-goal-gzrewind"></a>[gzrewind](../ZlibF/Spec/Public/GzControl.lean#L91) | All stated inputs / Registered proof | [Contract](../docs/spec/api/gz-file.md#gzrewind); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzRewindProof.rewind_public](../ZlibF/Proof/public-gz-rewind.lean#L76) | — |
| <a id="target-zlibf-spec-public-goal-gzseek64"></a>[gzseek64](../ZlibF/Spec/Public/GzControl.lean#L116) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzseek64); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: seek and history](progress.md#readiness-gzseek64) |
| <a id="target-zlibf-spec-public-goal-gzseek"></a>[gzseek](../ZlibF/Spec/Public/GzControl.lean#L119) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzseek); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: seek and history](progress.md#readiness-gzseek64) |
| <a id="target-zlibf-spec-public-goal-gzopen"></a>[gzopen](../ZlibF/Spec/Public/GzOpen.lean#L65) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzopen); [input range](spec/input-configurations.md#entry-inputs) | — | [Start: open and cleanup](progress.md#readiness-gzopen) |
| <a id="target-zlibf-spec-public-goal-gzopen64"></a>[gzopen64](../ZlibF/Spec/Public/GzOpen.lean#L70) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzopen64); [input range](spec/input-configurations.md#entry-inputs) | — | [Start: open and cleanup](progress.md#readiness-gzopen) |
| <a id="target-zlibf-spec-public-goal-gzdopen"></a>[gzdopen](../ZlibF/Spec/Public/GzOpen.lean#L75) | All stated inputs / Registered proof | [Contract](../docs/spec/api/gz-file.md#gzdopen); [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Gzlib.Proofs.gzdopen_complete](../ZlibF/Proof/gzlib.c.dopen-complete.lean#L28) | — |
| <a id="target-zlibf-spec-public-goal-gzread"></a>[gzread](../ZlibF/Spec/Public/GzRead.lean#L22) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzread); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: reader path proofs](progress.md#readiness-gzdirect) |
| <a id="target-zlibf-spec-public-goal-gzfread"></a>[gzfread](../ZlibF/Spec/Public/GzRead.lean#L37) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzfread); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: reader path proofs](progress.md#readiness-gzdirect) |
| <a id="target-zlibf-spec-public-goal-gzgetc"></a>[gzgetc](../ZlibF/Spec/Public/GzRead.lean#L58) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzgetc); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: reader path proofs](progress.md#readiness-gzdirect) |
| <a id="target-zlibf-spec-public-goal-gzgetc"></a>[gzgetc_](../ZlibF/Spec/Public/GzRead.lean#L61) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzgetc_); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: reader path proofs](progress.md#readiness-gzdirect) |
| <a id="target-zlibf-spec-public-goal-gzungetc"></a>[gzungetc](../ZlibF/Spec/Public/GzRead.lean#L66) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzungetc); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: reader path proofs](progress.md#readiness-gzdirect) |
| <a id="target-zlibf-spec-public-goal-gzgets"></a>[gzgets](../ZlibF/Spec/Public/GzRead.lean#L80) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzgets); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: reader path proofs](progress.md#readiness-gzdirect) |
| <a id="target-zlibf-spec-public-goal-gzdirect"></a>[gzdirect](../ZlibF/Spec/Public/GzRead.lean#L103) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzdirect); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: reader path proofs](progress.md#readiness-gzdirect) |
| <a id="target-zlibf-spec-public-goal-gzwrite"></a>[gzwrite](../ZlibF/Spec/Public/GzWrite.lean#L28) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzwrite); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: writer path proofs](progress.md#readiness-gzwrite) |
| <a id="target-zlibf-spec-public-goal-gzfwrite"></a>[gzfwrite](../ZlibF/Spec/Public/GzWrite.lean#L43) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzfwrite); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: writer path proofs](progress.md#readiness-gzwrite) |
| <a id="target-zlibf-spec-public-goal-gzputc"></a>[gzputc](../ZlibF/Spec/Public/GzWrite.lean#L59) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzputc); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: writer path proofs](progress.md#readiness-gzwrite) |
| <a id="target-zlibf-spec-public-goal-gzputs"></a>[gzputs](../ZlibF/Spec/Public/GzWrite.lean#L71) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzputs); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: writer path proofs](progress.md#readiness-gzwrite) |
| <a id="target-zlibf-spec-public-goal-gzvprintf"></a>[gzvprintf](../ZlibF/Spec/Public/GzWrite.lean#L108) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzvprintf); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: writer path proofs](progress.md#readiness-gzwrite) |
| <a id="target-zlibf-spec-public-goal-gzprintf"></a>[gzprintf](../ZlibF/Spec/Public/GzWrite.lean#L112) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzprintf); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: writer path proofs](progress.md#readiness-gzwrite) |
| <a id="target-zlibf-spec-public-goal-gzflush"></a>[gzflush](../ZlibF/Spec/Public/GzWrite.lean#L117) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzflush); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: writer path proofs](progress.md#readiness-gzwrite) |
| <a id="target-zlibf-spec-public-goal-gzsetparams"></a>[gzsetparams](../ZlibF/Spec/Public/GzWrite.lean#L134) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzsetparams); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: writer path proofs](progress.md#readiness-gzwrite) |
| <a id="target-zlibf-spec-public-goal-gz-sequence-safety"></a>[gz_sequence_safety](../ZlibF/Spec/Public/GzSafety.lean#L129) | Not proved / Not proved | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | — | Prerequisites unreviewed |

<a id="group-buffers"></a>

## Whole-buffer operations

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-compress2-z"></a>[compress2_z](../ZlibF/Spec/Public/Utilities.lean#L84) | Not proved / Not proved | [Contract](../docs/spec/api/utility.md#compress2_z); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: compressor execution](progress.md#readiness-compress2-z) |
| <a id="target-zlibf-spec-public-goal-compress2"></a>[compress2](../ZlibF/Spec/Public/Utilities.lean#L89) | Not proved / Not proved | [Contract](../docs/spec/api/utility.md#compress2); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: compressor execution](progress.md#readiness-compress2-z) |
| <a id="target-zlibf-spec-public-goal-compress-z"></a>[compress_z](../ZlibF/Spec/Public/Utilities.lean#L96) | Not proved / Not proved | [Contract](../docs/spec/api/utility.md#compress_z); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: compressor execution](progress.md#readiness-compress2-z) |
| <a id="target-zlibf-spec-public-goal-compress"></a>[compress](../ZlibF/Spec/Public/Utilities.lean#L101) | Not proved / Not proved | [Contract](../docs/spec/api/utility.md#compress); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: compressor execution](progress.md#readiness-compress2-z) |
| <a id="target-zlibf-spec-public-goal-uncompress2-z"></a>[uncompress2_z](../ZlibF/Spec/Public/Utilities.lean#L156) | Not proved / Not proved | [Contract](../docs/spec/api/utility.md#uncompress2_z); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: decoder execution](progress.md#readiness-uncompress2-z) |
| <a id="target-zlibf-spec-public-goal-uncompress2"></a>[uncompress2](../ZlibF/Spec/Public/Utilities.lean#L160) | Not proved / Not proved | [Contract](../docs/spec/api/utility.md#uncompress2); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: decoder execution](progress.md#readiness-uncompress2-z) |
| <a id="target-zlibf-spec-public-goal-uncompress-z"></a>[uncompress_z](../ZlibF/Spec/Public/Utilities.lean#L188) | Not proved / Not proved | [Contract](../docs/spec/api/utility.md#uncompress_z); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: decoder execution](progress.md#readiness-uncompress2-z) |
| <a id="target-zlibf-spec-public-goal-uncompress"></a>[uncompress](../ZlibF/Spec/Public/Utilities.lean#L192) | Not proved / Not proved | [Contract](../docs/spec/api/utility.md#uncompress); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: decoder execution](progress.md#readiness-uncompress2-z) |
| <a id="target-zlibf-spec-public-goal-uncompress2-z-safe"></a>[uncompress2_z_safe](../ZlibF/Spec/Public/Utilities.lean#L231) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.Uncompress.uncompress2_z_safe](../ZlibF/Proof/public-uncompress-safe.lean#L299) | — |
| <a id="target-zlibf-spec-public-goal-uncompress2-safe"></a>[uncompress2_safe](../ZlibF/Spec/Public/Utilities.lean#L234) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.Uncompress.uncompress2_safe](../ZlibF/Proof/public-uncompress-safe.lean#L303) | — |
| <a id="target-zlibf-spec-public-goal-uncompress-z-safe"></a>[uncompress_z_safe](../ZlibF/Spec/Public/Utilities.lean#L260) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.Uncompress.uncompress_z_safe](../ZlibF/Proof/public-uncompress-safe.lean#L307) | — |
| <a id="target-zlibf-spec-public-goal-uncompress-safe"></a>[uncompress_safe](../ZlibF/Spec/Public/Utilities.lean#L263) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.Uncompress.uncompress_safe](../ZlibF/Proof/public-uncompress-safe.lean#L313) | — |
| <a id="target-zlibf-spec-public-goal-compress2-z-safety"></a>[compress2_z_safety](../ZlibF/Spec/Public/Utilities.lean#L68) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.Compress.compress2_z_safety](../ZlibF/Proof/public-compress-safe-mid.lean#L115) | — |
| <a id="target-zlibf-spec-public-goal-compress2-safety"></a>[compress2_safety](../ZlibF/Spec/Public/Utilities.lean#L72) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.Compress.compress2_safety](../ZlibF/Proof/public-compress-safe-mid.lean#L123) | — |
| <a id="target-zlibf-spec-public-goal-compress-z-safety"></a>[compress_z_safety](../ZlibF/Spec/Public/Utilities.lean#L78) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.Compress.compress_z_safety](../ZlibF/Proof/public-compress-safe-mid.lean#L119) | — |
| <a id="target-zlibf-spec-public-goal-compress-safety"></a>[compress_safety](../ZlibF/Spec/Public/Utilities.lean#L107) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.Compress.compress_safety](../ZlibF/Proof/public-compress-safe-mid.lean#L127) | — |

<a id="group-models"></a>

## Format and API models

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-api-goal-format-deterministic"></a>[format_deterministic](../ZlibF/Spec/Api/Goals.lean#L42) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.format_deterministic](../ZlibF/Proof/Format/Api.lean#L51) | — |
| <a id="target-zlibf-spec-api-goal-format-prefix-free"></a>[format_prefix_free](../ZlibF/Spec/Api/Goals.lean#L47) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.format_prefix_free](../ZlibF/Proof/Format/Api.lean#L56) | — |
| <a id="target-zlibf-spec-api-goal-inflate-decodes"></a>[inflate_decodes](../ZlibF/Spec/Api/Goals.lean#L58) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.inflate_decodes](../ZlibF/Proof/Api/Inflate.lean#L346) | — |
| <a id="target-zlibf-spec-api-goal-inflate-completes"></a>[inflate_completes](../ZlibF/Spec/Api/Goals.lean#L69) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.inflate_completes](../ZlibF/Proof/Api/Inflate.lean#L353) | — |
| <a id="target-zlibf-spec-api-goal-inflate-rejects-invalid"></a>[inflate_rejects_invalid](../ZlibF/Spec/Api/Goals.lean#L84) | Not proved / Not proved | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | — | Prerequisites unreviewed |
| <a id="target-zlibf-spec-api-goal-deflate-valid"></a>[deflate_valid](../ZlibF/Spec/Api/Goals.lean#L99) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.deflate_valid](../ZlibF/Proof/Api/Deflate.lean#L181) | — |
| <a id="target-zlibf-spec-api-goal-deflate-completes"></a>[deflate_completes](../ZlibF/Spec/Api/Goals.lean#L106) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.deflate_completes](../ZlibF/Proof/Api/DeflateBounds.lean#L164) | — |
| <a id="target-zlibf-spec-api-goal-deflate-full-flush-resync"></a>[deflate_full_flush_resync](../ZlibF/Spec/Api/Goals.lean#L116) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.deflate_full_flush_resync](../ZlibF/Proof/Api/DeflateFlush.lean#L169) | — |
| <a id="target-zlibf-spec-api-goal-roundtrip"></a>[roundtrip](../ZlibF/Spec/Api/Goals.lean#L134) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.roundtrip](../ZlibF/Proof/Api/GzipRoundtrip.lean#L177) | — |
| <a id="target-zlibf-spec-api-goal-roundtrip-completes"></a>[roundtrip_completes](../ZlibF/Spec/Api/Goals.lean#L143) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.roundtrip_completes](../ZlibF/Proof/Api/GzipRoundtrip.lean#L186) | — |
| <a id="target-zlibf-spec-api-goal-dict-roundtrip"></a>[dict_roundtrip](../ZlibF/Spec/Api/Goals.lean#L162) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.dict_roundtrip](../ZlibF/Proof/Api/DictionaryRoundtrip.lean#L121) | — |
| <a id="target-zlibf-spec-api-goal-header-roundtrip"></a>[header_roundtrip](../ZlibF/Spec/Api/Goals.lean#L180) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.header_roundtrip](../ZlibF/Proof/Api/HeaderRoundtrip.lean#L89) | — |
| <a id="target-zlibf-spec-api-goal-deflate-bound-adequate"></a>[deflate_bound_adequate](../ZlibF/Spec/Api/Goals.lean#L189) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.deflate_bound_adequate](../ZlibF/Proof/Api/DeflateBounds.lean#L103) | — |
| <a id="target-zlibf-spec-api-goal-compress-bound-adequate"></a>[compress_bound_adequate](../ZlibF/Spec/Api/Goals.lean#L196) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.compress_bound_adequate](../ZlibF/Proof/Api/Compress.lean#L8) | — |
| <a id="target-zlibf-spec-api-goal-compress-roundtrip"></a>[compress_roundtrip](../ZlibF/Spec/Api/Goals.lean#L203) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.compress_roundtrip](../ZlibF/Proof/Api/CompressRoundtrip.lean#L32) | — |
| <a id="target-zlibf-spec-api-goal-gz-roundtrip"></a>[gz_roundtrip](../ZlibF/Spec/Api/Goals.lean#L214) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.gz_roundtrip](../ZlibF/Proof/Api/GzRoundtrip.lean#L15) | — |
| <a id="target-zlibf-spec-api-goal-gz-seek-read"></a>[gz_seek_read](../ZlibF/Spec/Api/Goals.lean#L221) | All stated inputs / Locally checked | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.gz_seek_read](../ZlibF/Proof/Api/GzSeekRead.lean#L15) | — |
| <a id="target-zlibf-spec-api-goal-compress-bound-value"></a>[compress_bound_value](../ZlibF/Spec/Api/Concrete.lean#L57) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.compress_bound_value](../ZlibF/Proof/Api/Concrete.lean#L57) | — |
| <a id="target-zlibf-spec-api-goal-compress2-z-first-alloc-failure"></a>[compress2_z_first_alloc_failure](../ZlibF/Spec/Api/Concrete.lean#L67) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.compress2_z_first_alloc_failure](../ZlibF/Proof/Api/CompressFailure.lean#L29) | — |
| <a id="target-zlibf-spec-api-goal-inflate-deferred-distance"></a>[inflate_deferred_distance](../ZlibF/Spec/Api/Inflate.lean#L267) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.inflate_deferred_distance](../ZlibF/Proof/Api/InflateCausality.lean#L244) | — |

<a id="group-lifecycle"></a>

## Lifecycles and call sequences

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-inflate-sequence"></a>[inflate_sequence](../ZlibF/Spec/Public/Sequences.lean#L241) | Not proved / Not proved | Exact target statement; [input range](spec/input-configurations.md#inflate-inputs) | — | [Needs: execution and format](progress.md#readiness-inflate-sequence) |
| <a id="target-zlibf-spec-public-goal-deflate-sequence"></a>[deflate_sequence](../ZlibF/Spec/Public/Sequences.lean#L278) | Not proved / Not proved | Exact target statement; [input range](spec/input-configurations.md#deflate-inputs) | — | [Needs: execution and format](progress.md#readiness-inflate-sequence) |
| <a id="target-zlibf-spec-public-goal-inflate-back-sequence"></a>[inflate_back_sequence](../ZlibF/Spec/Public/Sequences.lean#L375) | Not proved / Not proved | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: execution and format](progress.md#readiness-inflate-sequence) |
| <a id="target-zlibf-spec-public-goal-gz-sequence"></a>[gz_sequence](../ZlibF/Spec/Public/Sequences.lean#L425) | Not proved / Not proved | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: execution and format](progress.md#readiness-inflate-sequence) |
| <a id="target-zlibf-spec-public-goal-inflate-initialisation-domain"></a>[inflate_initialisation_domain](../ZlibF/Spec/Public/Domains.lean#L24) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.InflateInit.inflate_initialisation_domain_public](../ZlibF/Proof/public-inflate-init.lean#L263) | — |
| <a id="target-zlibf-spec-public-goal-deflate-initialisation-domain"></a>[deflate_initialisation_domain](../ZlibF/Spec/Public/Domains.lean#L37) | Not proved / Not proved | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | — | [Start: init and allocation](progress.md#readiness-deflateinit2) |
| <a id="target-zlibf-spec-public-goal-inflate-back-initialisation-domain"></a>[inflate_back_initialisation_domain](../ZlibF/Spec/Public/Domains.lean#L53) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.InflateBackInitProof.back_init_domain_public](../ZlibF/Proof/public-infback-init.lean#L230) | — |
| <a id="target-zlibf-spec-public-goal-gz-initialisation-domain"></a>[gz_initialisation_domain](../ZlibF/Spec/Public/Domains.lean#L79) | Not proved / Not proved | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | — | [Start: open and cleanup](progress.md#readiness-gzopen) |

<a id="group-internal"></a>

## Internal proof obligations

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlib-crc32-spec-byteviews-goal-crc32-z-all-byte-views"></a>[crc32_z_all_byte_views](../ZlibF/Spec/Crc32ByteViews.lean#L17) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Crc32.Proofs.crc32_z_all_byte_views](../ZlibF/Proof/crc32.c.views.lean#L567) | — |
| <a id="target-zlib-crc32-spec-byteviews-goal-crc32-all-byte-views"></a>[crc32_all_byte_views](../ZlibF/Spec/Crc32ByteViews.lean#L28) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Crc32.Proofs.crc32_all_byte_views](../ZlibF/Proof/crc32.c.views.lean#L573) | — |
| <a id="target-zlibf-spec-token-goal-rejected-has-no-symbols"></a>[rejected_has_no_symbols](../ZlibF/Spec/Format/Token.lean#L84) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Token.rejected_has_no_symbols](../ZlibF/Proof/Format/Token.lean#L49) | — |
| <a id="target-zlibf-spec-token-goal-step-composes-symbols"></a>[step_composes_symbols](../ZlibF/Spec/Format/Token.lean#L62) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Token.step_composes_symbols](../ZlibF/Proof/Format/Token.lean#L15) | — |
| <a id="target-zlibf-spec-token-goal-symbols-exposes-step"></a>[symbols_exposes_step](../ZlibF/Spec/Format/Token.lean#L73) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Token.symbols_exposes_step](../ZlibF/Proof/Format/Token.lean#L35) | — |

## Observed proof dependencies

A theorem for the destination actually uses a proof of the source target.

| Source | Destination |
| --- | --- |
| [pointer_advance_preserves_low_bits](#target-c-byteaddress-spec-goal-pointer-advance-preserves-low-bits) | [first_aligned_offset](#target-c-byteaddress-spec-goal-first-aligned-offset) |
| [crc32_all_byte_views](#target-zlib-crc32-spec-byteviews-goal-crc32-all-byte-views) | [crc32](#target-zlibf-spec-public-goal-crc32) |
| [crc32_all_byte_views](#target-zlib-crc32-spec-byteviews-goal-crc32-all-byte-views) | [inflate](#target-zlibf-spec-public-goal-inflate) |
| [crc32_all_byte_views](#target-zlib-crc32-spec-byteviews-goal-crc32-all-byte-views) | [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy) |
| [crc32_all_byte_views](#target-zlib-crc32-spec-byteviews-goal-crc32-all-byte-views) | [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) |
| [crc32_all_byte_views](#target-zlib-crc32-spec-byteviews-goal-crc32-all-byte-views) | [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe) |
| [crc32_all_byte_views](#target-zlib-crc32-spec-byteviews-goal-crc32-all-byte-views) | [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe) |
| [crc32_all_byte_views](#target-zlib-crc32-spec-byteviews-goal-crc32-all-byte-views) | [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe) |
| [crc32_all_byte_views](#target-zlib-crc32-spec-byteviews-goal-crc32-all-byte-views) | [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [crc32_z_all_byte_views](#target-zlib-crc32-spec-byteviews-goal-crc32-z-all-byte-views) | [crc32_z](#target-zlibf-spec-public-goal-crc32-z) |
| [actual_body_preserves_origin](#target-zlib-inffast-spec-bodyorigin-goal-actual-body-preserves-origin) | [actual_fast_preserves_origin](#target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin) |
| [actual_fast_preserves_origin](#target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin) | [inflate](#target-zlibf-spec-public-goal-inflate) |
| [actual_fast_preserves_origin](#target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin) | [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy) |
| [actual_fast_preserves_origin](#target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin) | [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) |
| [actual_fast_preserves_origin](#target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin) | [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe) |
| [actual_fast_preserves_origin](#target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin) | [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe) |
| [actual_fast_preserves_origin](#target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin) | [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe) |
| [actual_fast_preserves_origin](#target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin) | [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [actual_distance_block_preserves_origin](#target-zlib-inffast-spec-distanceorigin-goal-actual-distance-block-preserves-origin) | [actual_body_preserves_origin](#target-zlib-inffast-spec-bodyorigin-goal-actual-body-preserves-origin) |
| [actual_distance_refines_lz77](#target-zlib-inffast-spec-distanceresult-goal-actual-distance-refines-lz77) | [actual_body_refines_token](#target-zlib-inffast-spec-bodytoken-goal-actual-body-refines-token) |
| [distance_lookup_matches_format](#target-zlib-inffast-spec-distancesemantics-goal-distance-lookup-matches-format) | [actual_distance_refines_lz77](#target-zlib-inffast-spec-distanceresult-goal-actual-distance-refines-lz77) |
| [fast_safe](#target-zlib-inffast-spec-goal-fast-safe) | [actual_fast_preserves_origin](#target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin) |
| [step_safe](#target-zlib-inffast-spec-goal-step-safe) | [actual_body_refines_token](#target-zlib-inffast-spec-bodytoken-goal-actual-body-refines-token) |
| [step_safe](#target-zlib-inffast-spec-goal-step-safe) | [actual_body_retains_selected_length](#target-zlib-inffast-spec-lengthtrace-goal-actual-body-retains-selected-length) |
| [length_lookup_matches_format](#target-zlib-inffast-spec-lengthsemantics-goal-length-lookup-matches-format) | [actual_body_refines_token](#target-zlib-inffast-spec-bodytoken-goal-actual-body-refines-token) |
| [actual_copy_match_refines_lz77](#target-zlib-inffast-spec-matchhistory-goal-actual-copy-match-refines-lz77) | [actual_distance_refines_lz77](#target-zlib-inffast-spec-distanceresult-goal-actual-distance-refines-lz77) |
| [match_array_refines_lz77](#target-zlib-inffast-spec-matchhistory-goal-match-array-refines-lz77) | [actual_copy_match_refines_lz77](#target-zlib-inffast-spec-matchhistory-goal-actual-copy-match-refines-lz77) |
| [actual_drop_preserves_origin](#target-zlib-inffast-spec-origin-goal-actual-drop-preserves-origin) | [actual_body_preserves_origin](#target-zlib-inffast-spec-bodyorigin-goal-actual-body-preserves-origin) |
| [actual_rollback_preserves_origin](#target-zlib-inffast-spec-origin-goal-actual-rollback-preserves-origin) | [actual_fast_preserves_origin](#target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin) |
| [drop_preserves_origin](#target-zlib-inffast-spec-origin-goal-drop-preserves-origin) | [actual_distance_block_preserves_origin](#target-zlib-inffast-spec-distanceorigin-goal-actual-distance-block-preserves-origin) |
| [drop_preserves_origin](#target-zlib-inffast-spec-origin-goal-drop-preserves-origin) | [actual_drop_preserves_origin](#target-zlib-inffast-spec-origin-goal-actual-drop-preserves-origin) |
| [initial_origin](#target-zlib-inffast-spec-origin-goal-initial-origin) | [actual_fast_preserves_origin](#target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin) |
| [pull_preserves_origin](#target-zlib-inffast-spec-origin-goal-pull-preserves-origin) | [actual_body_preserves_origin](#target-zlib-inffast-spec-bodyorigin-goal-actual-body-preserves-origin) |
| [pull_preserves_origin](#target-zlib-inffast-spec-origin-goal-pull-preserves-origin) | [actual_distance_block_preserves_origin](#target-zlib-inffast-spec-distanceorigin-goal-actual-distance-block-preserves-origin) |
| [pull_preserves_origin](#target-zlib-inffast-spec-origin-goal-pull-preserves-origin) | [actual_pull_preserves_origin](#target-zlib-inffast-spec-origin-goal-actual-pull-preserves-origin) |
| [rollback_preserves_origin](#target-zlib-inffast-spec-origin-goal-rollback-preserves-origin) | [actual_rollback_preserves_origin](#target-zlib-inffast-spec-origin-goal-actual-rollback-preserves-origin) |
| [decode_table_classifies_input](#target-zlib-inftrees-spec-decoderejection-goal-decode-table-classifies-input) | [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant) |
| [decode_table_matches_format](#target-zlib-inftrees-spec-decodesemantics-goal-decode-table-matches-format) | [decode_table_classifies_input](#target-zlib-inftrees-spec-decoderejection-goal-decode-table-classifies-input) |
| [short_decode_table_leaf_sound](#target-zlib-inftrees-spec-decodeshort-goal-short-decode-table-leaf-sound) | [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant) |
| [decode_table_leaf_sound](#target-zlib-inftrees-spec-decodesoundness-goal-decode-table-leaf-sound) | [decode_table_classifies_input](#target-zlib-inftrees-spec-decoderejection-goal-decode-table-classifies-input) |
| [decode_table_leaf_sound](#target-zlib-inftrees-spec-decodesoundness-goal-decode-table-leaf-sound) | [short_decode_table_leaf_sound](#target-zlib-inftrees-spec-decodeshort-goal-short-decode-table-leaf-sound) |
| [decode_table_read_preserved](#target-zlib-inftrees-spec-decodetableframe-goal-decode-table-read-preserved) | [decode_table_invariant_of_prefix](#target-zlib-inftrees-spec-decodetableinvariant-goal-decode-table-invariant-of-prefix) |
| [decode_table_read_preserved](#target-zlib-inftrees-spec-decodetableframe-goal-decode-table-read-preserved) | [query_stability_of_prefix](#target-zlib-inftrees-spec-decodetablestability-goal-query-stability-of-prefix) |
| [decode_table_read_preserved](#target-zlib-inftrees-spec-decodetableframe-goal-decode-table-read-preserved) | [fast_leaf_flags_of_prefix](#target-zlib-inftrees-spec-fasttableflags-goal-fast-leaf-flags-of-prefix) |
| [decode_table_read_preserved](#target-zlib-inftrees-spec-decodetableframe-goal-decode-table-read-preserved) | [inflate](#target-zlibf-spec-public-goal-inflate) |
| [decode_table_read_preserved](#target-zlib-inftrees-spec-decodetableframe-goal-decode-table-read-preserved) | [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy) |
| [decode_table_read_preserved](#target-zlib-inftrees-spec-decodetableframe-goal-decode-table-read-preserved) | [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) |
| [decode_table_read_preserved](#target-zlib-inftrees-spec-decodetableframe-goal-decode-table-read-preserved) | [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe) |
| [decode_table_read_preserved](#target-zlib-inftrees-spec-decodetableframe-goal-decode-table-read-preserved) | [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe) |
| [decode_table_read_preserved](#target-zlib-inftrees-spec-decodetableframe-goal-decode-table-read-preserved) | [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe) |
| [decode_table_read_preserved](#target-zlib-inftrees-spec-decodetableframe-goal-decode-table-read-preserved) | [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant) | [inflate](#target-zlibf-spec-public-goal-inflate) |
| [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant) | [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy) |
| [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant) | [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) |
| [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant) | [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe) |
| [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant) | [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe) |
| [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant) | [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe) |
| [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant) | [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [decode_table_invariant_of_prefix](#target-zlib-inftrees-spec-decodetableinvariant-goal-decode-table-invariant-of-prefix) | [inflate](#target-zlibf-spec-public-goal-inflate) |
| [decode_table_invariant_of_prefix](#target-zlib-inftrees-spec-decodetableinvariant-goal-decode-table-invariant-of-prefix) | [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy) |
| [decode_table_invariant_of_prefix](#target-zlib-inftrees-spec-decodetableinvariant-goal-decode-table-invariant-of-prefix) | [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) |
| [decode_table_invariant_of_prefix](#target-zlib-inftrees-spec-decodetableinvariant-goal-decode-table-invariant-of-prefix) | [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe) |
| [decode_table_invariant_of_prefix](#target-zlib-inftrees-spec-decodetableinvariant-goal-decode-table-invariant-of-prefix) | [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe) |
| [decode_table_invariant_of_prefix](#target-zlib-inftrees-spec-decodetableinvariant-goal-decode-table-invariant-of-prefix) | [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe) |
| [decode_table_invariant_of_prefix](#target-zlib-inftrees-spec-decodetableinvariant-goal-decode-table-invariant-of-prefix) | [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [short_rejected_leaf_stays_invalid](#target-zlib-inftrees-spec-decodetablestability-goal-short-rejected-leaf-stays-invalid) | [distance_lookup_matches_format](#target-zlib-inffast-spec-distancesemantics-goal-distance-lookup-matches-format) |
| [short_rejected_leaf_stays_invalid](#target-zlib-inftrees-spec-decodetablestability-goal-short-rejected-leaf-stays-invalid) | [length_lookup_matches_format](#target-zlib-inffast-spec-lengthsemantics-goal-length-lookup-matches-format) |
| [inflate_table_content](#target-zlib-inftrees-spec-goal-inflate-table-content) | [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe) |
| [inflate_table_content](#target-zlib-inftrees-spec-goal-inflate-table-content) | [inflate](#target-zlibf-spec-public-goal-inflate) |
| [inflate_table_content](#target-zlib-inftrees-spec-goal-inflate-table-content) | [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy) |
| [inflate_table_content](#target-zlib-inftrees-spec-goal-inflate-table-content) | [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) |
| [inflate_table_content](#target-zlib-inftrees-spec-goal-inflate-table-content) | [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe) |
| [inflate_table_content](#target-zlib-inftrees-spec-goal-inflate-table-content) | [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe) |
| [inflate_table_content](#target-zlib-inftrees-spec-goal-inflate-table-content) | [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe) |
| [inflate_table_content](#target-zlib-inftrees-spec-goal-inflate-table-content) | [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe) | [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent) |
| [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe) | [constructor_root_bits](#target-zlib-inftrees-spec-roottable-goal-constructor-root-bits) |
| [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent) | [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant) |
| [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent) | [inflate](#target-zlibf-spec-public-goal-inflate) |
| [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent) | [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy) |
| [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent) | [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) |
| [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent) | [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe) |
| [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent) | [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe) |
| [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent) | [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe) |
| [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent) | [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [constructor_subtable_bits](#target-zlib-inftrees-spec-subtable-goal-constructor-subtable-bits) | [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant) |
| [constructor_subtable_bits](#target-zlib-inftrees-spec-subtable-goal-constructor-subtable-bits) | [constructor_root_bits](#target-zlib-inftrees-spec-roottable-goal-constructor-root-bits) |
| [output_copy_refines_lz77](#target-zlibf-math-lz77copy-goal-output-copy-refines-lz77) | [match_array_refines_lz77](#target-zlib-inffast-spec-matchhistory-goal-match-array-refines-lz77) |
| [window_copy_refines_lz77](#target-zlibf-math-lz77copy-goal-window-copy-refines-lz77) | [match_array_refines_lz77](#target-zlib-inffast-spec-matchhistory-goal-match-array-refines-lz77) |
| [copy_back_compose](#target-zlibf-math-lz77history-goal-copy-back-compose) | [match_array_refines_lz77](#target-zlib-inffast-spec-matchhistory-goal-match-array-refines-lz77) |
| [retained_history_agrees](#target-zlibf-math-lz77history-goal-retained-history-agrees) | [roundtrip](#target-zlibf-spec-api-goal-roundtrip) |
| [retained_history_agrees](#target-zlibf-math-lz77history-goal-retained-history-agrees) | [roundtrip_completes](#target-zlibf-spec-api-goal-roundtrip-completes) |
| [deflate_valid](#target-zlibf-spec-api-goal-deflate-valid) | [dict_roundtrip](#target-zlibf-spec-api-goal-dict-roundtrip) |
| [deflate_valid](#target-zlibf-spec-api-goal-deflate-valid) | [header_roundtrip](#target-zlibf-spec-api-goal-header-roundtrip) |
| [deflate_valid](#target-zlibf-spec-api-goal-deflate-valid) | [roundtrip](#target-zlibf-spec-api-goal-roundtrip) |
| [deflate_valid](#target-zlibf-spec-api-goal-deflate-valid) | [roundtrip_completes](#target-zlibf-spec-api-goal-roundtrip-completes) |
| [inflate_completes](#target-zlibf-spec-api-goal-inflate-completes) | [roundtrip_completes](#target-zlibf-spec-api-goal-roundtrip-completes) |
| [inflate_decodes](#target-zlibf-spec-api-goal-inflate-decodes) | [roundtrip](#target-zlibf-spec-api-goal-roundtrip) |
| [adler32_z](#target-zlibf-spec-public-goal-adler32-z) | [adler32](#target-zlibf-spec-public-goal-adler32) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [compress_safety](#target-zlibf-spec-public-goal-compress-safety) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [deflate](#target-zlibf-spec-public-goal-deflate) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy) | [deflateCopy_safety](#target-zlibf-spec-public-goal-deflatecopy-safety) |
| [deflateEnd](#target-zlibf-spec-public-goal-deflateend) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety) |
| [deflateEnd](#target-zlibf-spec-public-goal-deflateend) | [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety) |
| [deflateEnd](#target-zlibf-spec-public-goal-deflateend) | [compress_safety](#target-zlibf-spec-public-goal-compress-safety) |
| [deflateEnd](#target-zlibf-spec-public-goal-deflateend) | [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety) |
| [deflateEnd](#target-zlibf-spec-public-goal-deflateend) | [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [inflateBackInit_](#target-zlibf-spec-public-goal-inflatebackinit) | [inflate_back_initialisation_domain](#target-zlibf-spec-public-goal-inflate-back-initialisation-domain) |
| [inflateEnd](#target-zlibf-spec-public-goal-inflateend) | [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [inflate](#target-zlibf-spec-public-goal-inflate) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [inflateSetDictionary](#target-zlibf-spec-public-goal-inflatesetdictionary) | [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) |

## C function calls

The destination implementation calls the source entry. This does not require the complete source-entry contract as a proof premise.

| Source | Destination |
| --- | --- |
| [adler32](#target-zlibf-spec-public-goal-adler32) | [deflate](#target-zlibf-spec-public-goal-deflate) |
| [adler32](#target-zlibf-spec-public-goal-adler32) | [deflateResetKeep](#target-zlibf-spec-public-goal-deflateresetkeep) |
| [adler32](#target-zlibf-spec-public-goal-adler32) | [deflateSetDictionary](#target-zlibf-spec-public-goal-deflatesetdictionary) |
| [adler32](#target-zlibf-spec-public-goal-adler32) | [inflate](#target-zlibf-spec-public-goal-inflate) |
| [adler32](#target-zlibf-spec-public-goal-adler32) | [inflateSetDictionary](#target-zlibf-spec-public-goal-inflatesetdictionary) |
| [adler32_z](#target-zlibf-spec-public-goal-adler32-z) | [adler32](#target-zlibf-spec-public-goal-adler32) |
| [compress2](#target-zlibf-spec-public-goal-compress2) | [compress](#target-zlibf-spec-public-goal-compress) |
| [compress2_z](#target-zlibf-spec-public-goal-compress2-z) | [compress2](#target-zlibf-spec-public-goal-compress2) |
| [compress2_z](#target-zlibf-spec-public-goal-compress2-z) | [compress_z](#target-zlibf-spec-public-goal-compress-z) |
| [compressBound_z](#target-zlibf-spec-public-goal-compressbound-z) | [compressBound](#target-zlibf-spec-public-goal-compressbound) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [deflate](#target-zlibf-spec-public-goal-deflate) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [deflateResetKeep](#target-zlibf-spec-public-goal-deflateresetkeep) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [deflateSetDictionary](#target-zlibf-spec-public-goal-deflatesetdictionary) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [inflate](#target-zlibf-spec-public-goal-inflate) |
| [crc32_combine64](#target-zlibf-spec-public-goal-crc32-combine64) | [crc32_combine](#target-zlibf-spec-public-goal-crc32-combine) |
| [crc32_combine_gen64](#target-zlibf-spec-public-goal-crc32-combine-gen64) | [crc32_combine64](#target-zlibf-spec-public-goal-crc32-combine64) |
| [crc32_combine_gen64](#target-zlibf-spec-public-goal-crc32-combine-gen64) | [crc32_combine_gen](#target-zlibf-spec-public-goal-crc32-combine-gen) |
| [crc32_combine_op](#target-zlibf-spec-public-goal-crc32-combine-op) | [crc32_combine64](#target-zlibf-spec-public-goal-crc32-combine64) |
| [crc32_z](#target-zlibf-spec-public-goal-crc32-z) | [crc32](#target-zlibf-spec-public-goal-crc32) |
| [crc32_z](#target-zlibf-spec-public-goal-crc32-z) | [deflate](#target-zlibf-spec-public-goal-deflate) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [compress2_z](#target-zlibf-spec-public-goal-compress2-z) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [deflateParams](#target-zlibf-spec-public-goal-deflateparams) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [gzclose_w](#target-zlibf-spec-public-goal-gzclose-w) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [gzflush](#target-zlibf-spec-public-goal-gzflush) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [gzfwrite](#target-zlibf-spec-public-goal-gzfwrite) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [gzputc](#target-zlibf-spec-public-goal-gzputc) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [gzputs](#target-zlibf-spec-public-goal-gzputs) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [gzsetparams](#target-zlibf-spec-public-goal-gzsetparams) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [gzvprintf](#target-zlibf-spec-public-goal-gzvprintf) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [gzwrite](#target-zlibf-spec-public-goal-gzwrite) |
| [deflateBound_z](#target-zlibf-spec-public-goal-deflatebound-z) | [deflateBound](#target-zlibf-spec-public-goal-deflatebound) |
| [deflateEnd](#target-zlibf-spec-public-goal-deflateend) | [compress2_z](#target-zlibf-spec-public-goal-compress2-z) |
| [deflateEnd](#target-zlibf-spec-public-goal-deflateend) | [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) |
| [deflateEnd](#target-zlibf-spec-public-goal-deflateend) | [gzclose_w](#target-zlibf-spec-public-goal-gzclose-w) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [deflateInit_](#target-zlibf-spec-public-goal-deflateinit) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [gzclose_w](#target-zlibf-spec-public-goal-gzclose-w) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [gzflush](#target-zlibf-spec-public-goal-gzflush) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [gzfwrite](#target-zlibf-spec-public-goal-gzfwrite) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [gzputc](#target-zlibf-spec-public-goal-gzputc) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [gzputs](#target-zlibf-spec-public-goal-gzputs) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [gzsetparams](#target-zlibf-spec-public-goal-gzsetparams) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [gzvprintf](#target-zlibf-spec-public-goal-gzvprintf) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [gzwrite](#target-zlibf-spec-public-goal-gzwrite) |
| [deflateInit_](#target-zlibf-spec-public-goal-deflateinit) | [compress2_z](#target-zlibf-spec-public-goal-compress2-z) |
| [deflateParams](#target-zlibf-spec-public-goal-deflateparams) | [gzsetparams](#target-zlibf-spec-public-goal-gzsetparams) |
| [deflateReset](#target-zlibf-spec-public-goal-deflatereset) | [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) |
| [deflateReset](#target-zlibf-spec-public-goal-deflatereset) | [gzclose_w](#target-zlibf-spec-public-goal-gzclose-w) |
| [deflateReset](#target-zlibf-spec-public-goal-deflatereset) | [gzflush](#target-zlibf-spec-public-goal-gzflush) |
| [deflateReset](#target-zlibf-spec-public-goal-deflatereset) | [gzfwrite](#target-zlibf-spec-public-goal-gzfwrite) |
| [deflateReset](#target-zlibf-spec-public-goal-deflatereset) | [gzputc](#target-zlibf-spec-public-goal-gzputc) |
| [deflateReset](#target-zlibf-spec-public-goal-deflatereset) | [gzputs](#target-zlibf-spec-public-goal-gzputs) |
| [deflateReset](#target-zlibf-spec-public-goal-deflatereset) | [gzsetparams](#target-zlibf-spec-public-goal-gzsetparams) |
| [deflateReset](#target-zlibf-spec-public-goal-deflatereset) | [gzvprintf](#target-zlibf-spec-public-goal-gzvprintf) |
| [deflateReset](#target-zlibf-spec-public-goal-deflatereset) | [gzwrite](#target-zlibf-spec-public-goal-gzwrite) |
| [deflateResetKeep](#target-zlibf-spec-public-goal-deflateresetkeep) | [deflateReset](#target-zlibf-spec-public-goal-deflatereset) |
| [gzclose_r](#target-zlibf-spec-public-goal-gzclose-r) | [gzclose](#target-zlibf-spec-public-goal-gzclose) |
| [gzclose_w](#target-zlibf-spec-public-goal-gzclose-w) | [gzclose](#target-zlibf-spec-public-goal-gzclose) |
| [gzgetc](#target-zlibf-spec-public-goal-gzgetc) | [gzgetc_](#target-zlibf-spec-public-goal-gzgetc) |
| [gzoffset64](#target-zlibf-spec-public-goal-gzoffset64) | [gzoffset](#target-zlibf-spec-public-goal-gzoffset) |
| [gzrewind](#target-zlibf-spec-public-goal-gzrewind) | [gzseek64](#target-zlibf-spec-public-goal-gzseek64) |
| [gzseek64](#target-zlibf-spec-public-goal-gzseek64) | [gzseek](#target-zlibf-spec-public-goal-gzseek) |
| [gztell64](#target-zlibf-spec-public-goal-gztell64) | [gztell](#target-zlibf-spec-public-goal-gztell) |
| [gzvprintf](#target-zlibf-spec-public-goal-gzvprintf) | [gzprintf](#target-zlibf-spec-public-goal-gzprintf) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [gzfread](#target-zlibf-spec-public-goal-gzfread) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [gzgetc](#target-zlibf-spec-public-goal-gzgetc) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [gzgets](#target-zlibf-spec-public-goal-gzgets) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [gzread](#target-zlibf-spec-public-goal-gzread) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [gzungetc](#target-zlibf-spec-public-goal-gzungetc) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [uncompress2_z](#target-zlibf-spec-public-goal-uncompress2-z) |
| [inflateEnd](#target-zlibf-spec-public-goal-inflateend) | [gzclose_r](#target-zlibf-spec-public-goal-gzclose-r) |
| [inflateEnd](#target-zlibf-spec-public-goal-inflateend) | [uncompress2_z](#target-zlibf-spec-public-goal-uncompress2-z) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [gzdirect](#target-zlibf-spec-public-goal-gzdirect) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [gzfread](#target-zlibf-spec-public-goal-gzfread) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [gzgetc](#target-zlibf-spec-public-goal-gzgetc) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [gzgets](#target-zlibf-spec-public-goal-gzgets) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [gzread](#target-zlibf-spec-public-goal-gzread) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [gzungetc](#target-zlibf-spec-public-goal-gzungetc) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [inflateInit_](#target-zlibf-spec-public-goal-inflateinit) |
| [inflateInit_](#target-zlibf-spec-public-goal-inflateinit) | [uncompress2_z](#target-zlibf-spec-public-goal-uncompress2-z) |
| [inflateReset](#target-zlibf-spec-public-goal-inflatereset) | [gzdirect](#target-zlibf-spec-public-goal-gzdirect) |
| [inflateReset](#target-zlibf-spec-public-goal-inflatereset) | [gzfread](#target-zlibf-spec-public-goal-gzfread) |
| [inflateReset](#target-zlibf-spec-public-goal-inflatereset) | [gzgetc](#target-zlibf-spec-public-goal-gzgetc) |
| [inflateReset](#target-zlibf-spec-public-goal-inflatereset) | [gzgets](#target-zlibf-spec-public-goal-gzgets) |
| [inflateReset](#target-zlibf-spec-public-goal-inflatereset) | [gzread](#target-zlibf-spec-public-goal-gzread) |
| [inflateReset](#target-zlibf-spec-public-goal-inflatereset) | [gzungetc](#target-zlibf-spec-public-goal-gzungetc) |
| [inflateReset](#target-zlibf-spec-public-goal-inflatereset) | [inflateReset2](#target-zlibf-spec-public-goal-inflatereset2) |
| [inflateReset](#target-zlibf-spec-public-goal-inflatereset) | [inflateSync](#target-zlibf-spec-public-goal-inflatesync) |
| [inflateReset2](#target-zlibf-spec-public-goal-inflatereset2) | [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) |
| [inflateResetKeep](#target-zlibf-spec-public-goal-inflateresetkeep) | [inflateReset](#target-zlibf-spec-public-goal-inflatereset) |
| [uncompress2](#target-zlibf-spec-public-goal-uncompress2) | [uncompress](#target-zlibf-spec-public-goal-uncompress) |
| [uncompress2_z](#target-zlibf-spec-public-goal-uncompress2-z) | [uncompress2](#target-zlibf-spec-public-goal-uncompress2) |
| [uncompress2_z](#target-zlibf-spec-public-goal-uncompress2-z) | [uncompress_z](#target-zlibf-spec-public-goal-uncompress-z) |
| [zError](#target-zlibf-spec-public-goal-zerror) | [deflate](#target-zlibf-spec-public-goal-deflate) |
| [zError](#target-zlibf-spec-public-goal-zerror) | [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) |
| [zlibVersion](#target-zlibf-spec-public-goal-zlibversion) | [compress2_z](#target-zlibf-spec-public-goal-compress2-z) |

## Specification references

The destination target definition references the source target or implementation. This is not a proof dependency.

| Source | Destination |
| --- | --- |
| [compress](#target-zlibf-spec-public-goal-compress) | [compress_safety](#target-zlibf-spec-public-goal-compress-safety) |
| [compress2](#target-zlibf-spec-public-goal-compress2) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety) |
| [compress2_z](#target-zlibf-spec-public-goal-compress2-z) | [compress2_z_first_alloc_failure](#target-zlibf-spec-api-goal-compress2-z-first-alloc-failure) |
| [compress2_z](#target-zlibf-spec-public-goal-compress2-z) | [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety) |
| [compressBound](#target-zlibf-spec-public-goal-compressbound) | [compress_bound_value](#target-zlibf-spec-api-goal-compress-bound-value) |
| [compressBound_z](#target-zlibf-spec-public-goal-compressbound-z) | [compress_bound_value](#target-zlibf-spec-api-goal-compress-bound-value) |
| [compress_z](#target-zlibf-spec-public-goal-compress-z) | [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [crc32_all_byte_views](#target-zlib-crc32-spec-byteviews-goal-crc32-all-byte-views) |
| [crc32_z](#target-zlibf-spec-public-goal-crc32-z) | [crc32_z_all_byte_views](#target-zlib-crc32-spec-byteviews-goal-crc32-z-all-byte-views) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [deflate_refusal](#target-zlibf-spec-public-goal-deflate-refusal) |
| [deflateBound](#target-zlibf-spec-public-goal-deflatebound) | [deflate_sequence](#target-zlibf-spec-public-goal-deflate-sequence) |
| [deflateBound_z](#target-zlibf-spec-public-goal-deflatebound-z) | [deflate_sequence](#target-zlibf-spec-public-goal-deflate-sequence) |
| [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy) | [deflateCopy_safety](#target-zlibf-spec-public-goal-deflatecopy-safety) |
| [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy) | [deflate_refusal](#target-zlibf-spec-public-goal-deflate-refusal) |
| [deflateGetDictionary](#target-zlibf-spec-public-goal-deflategetdictionary) | [deflate_refusal](#target-zlibf-spec-public-goal-deflate-refusal) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [deflate_initialisation_domain](#target-zlibf-spec-public-goal-deflate-initialisation-domain) |
| [deflateParams](#target-zlibf-spec-public-goal-deflateparams) | [deflate_refusal](#target-zlibf-spec-public-goal-deflate-refusal) |
| [deflateSetDictionary](#target-zlibf-spec-public-goal-deflatesetdictionary) | [deflate_refusal](#target-zlibf-spec-public-goal-deflate-refusal) |
| [gzclose](#target-zlibf-spec-public-goal-gzclose) | [gz_sequence](#target-zlibf-spec-public-goal-gz-sequence) |
| [gzflush](#target-zlibf-spec-public-goal-gzflush) | [gz_sequence](#target-zlibf-spec-public-goal-gz-sequence) |
| [gzfread](#target-zlibf-spec-public-goal-gzfread) | [gz_sequence](#target-zlibf-spec-public-goal-gz-sequence) |
| [gzfwrite](#target-zlibf-spec-public-goal-gzfwrite) | [gz_sequence](#target-zlibf-spec-public-goal-gz-sequence) |
| [gzgetc](#target-zlibf-spec-public-goal-gzgetc) | [gz_sequence](#target-zlibf-spec-public-goal-gz-sequence) |
| [gzgets](#target-zlibf-spec-public-goal-gzgets) | [gz_sequence](#target-zlibf-spec-public-goal-gz-sequence) |
| [gzopen](#target-zlibf-spec-public-goal-gzopen) | [gz_initialisation_domain](#target-zlibf-spec-public-goal-gz-initialisation-domain) |
| [gzopen](#target-zlibf-spec-public-goal-gzopen) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [gzopen64](#target-zlibf-spec-public-goal-gzopen64) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [gzread](#target-zlibf-spec-public-goal-gzread) | [gz_sequence](#target-zlibf-spec-public-goal-gz-sequence) |
| [gzwrite](#target-zlibf-spec-public-goal-gzwrite) | [gz_sequence](#target-zlibf-spec-public-goal-gz-sequence) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [inflate_refusal](#target-zlibf-spec-public-goal-inflate-refusal) |
| [inflateBack](#target-zlibf-spec-public-goal-inflateback) | [inflate_back_sequence](#target-zlibf-spec-public-goal-inflate-back-sequence) |
| [inflateBack](#target-zlibf-spec-public-goal-inflateback) | [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety) |
| [inflateBackEnd](#target-zlibf-spec-public-goal-inflatebackend) | [inflate_back_sequence](#target-zlibf-spec-public-goal-inflate-back-sequence) |
| [inflateBackEnd](#target-zlibf-spec-public-goal-inflatebackend) | [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety) |
| [inflateBackInit_](#target-zlibf-spec-public-goal-inflatebackinit) | [inflate_back_initialisation_domain](#target-zlibf-spec-public-goal-inflate-back-initialisation-domain) |
| [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy) | [inflate_refusal](#target-zlibf-spec-public-goal-inflate-refusal) |
| [inflateEnd](#target-zlibf-spec-public-goal-inflateend) | [inflate_refusal](#target-zlibf-spec-public-goal-inflate-refusal) |
| [inflateGetDictionary](#target-zlibf-spec-public-goal-inflategetdictionary) | [inflate_refusal](#target-zlibf-spec-public-goal-inflate-refusal) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [inflate_initialisation_domain](#target-zlibf-spec-public-goal-inflate-initialisation-domain) |
| [inflateReset](#target-zlibf-spec-public-goal-inflatereset) | [inflate_refusal](#target-zlibf-spec-public-goal-inflate-refusal) |
| [inflateReset2](#target-zlibf-spec-public-goal-inflatereset2) | [inflate_refusal](#target-zlibf-spec-public-goal-inflate-refusal) |
| [inflateSetDictionary](#target-zlibf-spec-public-goal-inflatesetdictionary) | [inflate_refusal](#target-zlibf-spec-public-goal-inflate-refusal) |
| [uncompress](#target-zlibf-spec-public-goal-uncompress) | [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe) |
| [uncompress2](#target-zlibf-spec-public-goal-uncompress2) | [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe) |
| [uncompress2_z](#target-zlibf-spec-public-goal-uncompress2-z) | [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe) |
| [uncompress_z](#target-zlibf-spec-public-goal-uncompress-z) | [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |

## Proof support relationships

These are observed theorem references grouped by source family. Groups carry no whole-file proof status.
Every direct grouped connection is retained here, including arrows reduced in the graph.

| Supporting source | Direct destinations |
| --- | --- |
| API-model lemmas | compress_bound_adequate, compress_roundtrip, deflate_bound_adequate, deflate_completes, deflate_full_flush_resync, deflate_valid, dict_roundtrip, gz_roundtrip, gz_seek_read, header_roundtrip, inflate_completes, inflate_decodes, inflate_deferred_distance, roundtrip, roundtrip_completes, deflateInit2_, deflateInit_, gzdopen, api-model proofs, deflate construction proofs, deflate lifecycle proofs, gzlib.c proofs, heap-free mathematics, inflate storage and bit proofs |
| ByteAddress proofs | first_aligned_offset, mask_refines_base_plus_offset, pointer_advance_preserves_low_bits |
| LibcBorrow proofs | LibcBorrowLoops proofs, LibcBorrowPrimitives proofs, PlatformMemory proofs, borrowed-byte-frame proofs, checksum.borrow-stable proofs, deflate lifecycle proofs, deflate window and match proofs, gzfs.borrow-stable proofs, inflate mode and exit proofs, inflate storage and bit proofs, tree construction and emission proofs |
| LibcBorrowLoops proofs | checksum.borrow-stable proofs, deflate lifecycle proofs, inflate storage and bit proofs, tree construction and emission proofs |
| LibcBorrowPrimitives proofs | checksum.borrow-stable proofs, deflate lifecycle proofs, inflate storage and bit proofs, public entry composition, tree construction and emission proofs |
| LibcStrings proofs | LibcBorrow proofs |
| PlatformMemory proofs | inffast.c proofs, inflate storage and bit proofs |
| crc32_all_byte_views | inflate storage and bit proofs |
| actual_body_preserves_origin | inffast.c proofs |
| actual_fast_preserves_origin | inffast.c proofs |
| actual_distance_block_preserves_origin | inffast.c proofs |
| actual_copy_match_refines_lz77 | inffast.c proofs |
| actual_drop_preserves_origin | inffast.c proofs |
| actual_rollback_preserves_origin | inffast.c proofs |
| drop_preserves_origin | inffast.c proofs |
| pull_preserves_origin | inffast.c proofs |
| decode_table_read_preserved | inftrees.c proofs |
| constructor_establishes_decode_table_invariant | inflate storage and bit proofs, inftrees.c proofs |
| decode_table_invariant_of_prefix | inftrees.c proofs |
| inflate_table_content | inftrees.c proofs |
| inflate_table_read_extent | inflate storage and bit proofs |
| retained_history_agrees | format proofs |
| deflate_valid | api-model proofs |
| inflate_completes | api-model proofs |
| inflate_decodes | api-model proofs |
| crc32 | deflate lifecycle proofs |
| deflateEnd | deflate lifecycle proofs, public entry composition |
| inflate | public entry composition |
| inflateBackInit_ | public entry composition |
| inflateEnd | inflate storage and bit proofs |
| inflateInit2_ | inflate storage and bit proofs |
| inflateSetDictionary | inflate storage and bit proofs |
| adler32.c proofs | inflateSetDictionary, deflate lifecycle proofs, inflate entry composition, inflate storage and bit proofs, public entry composition |
| api-model proofs | compress2_z_first_alloc_failure, compress_bound_adequate, compress_bound_value, compress_roundtrip, deflate_bound_adequate, deflate_completes, deflate_full_flush_resync, deflate_valid, dict_roundtrip, gz_roundtrip, gz_seek_read, header_roundtrip, inflate_completes, inflate_decodes, inflate_deferred_distance, roundtrip, roundtrip_completes, inflateCodesUsed |
| borrowed-byte-frame proofs | inflate storage and bit proofs |
| checksum.borrow-stable proofs | deflate lifecycle proofs, inflate storage and bit proofs, tree construction and emission proofs |
| crc32.c proofs | crc32_all_byte_views, crc32_z_all_byte_views, crc32, crc32_z, deflate lifecycle proofs, inflate storage and bit proofs, public entry composition |
| deflate construction proofs | deflateInit2_, deflateInit_, deflate lifecycle proofs, deflate window and match proofs, public entry composition |
| deflate entry composition | deflate, deflateCopy, deflateCopy_safety, deflateEnd, deflateGetDictionary, deflatePending, deflateReset, deflateResetKeep, deflateSetHeader, deflateTune, deflateUsed, deflate_refusal, deflate_sequence_safety |
| deflate lifecycle proofs | deflateCopy, deflateCopy_safety, deflateEnd, deflateGetDictionary, deflateInit_, deflatePending, deflateReset, deflateResetKeep, deflateSetHeader, deflateTune, deflateUsed, deflate_refusal, deflate construction proofs, deflate entry composition, deflate window and match proofs, inffast.c proofs, inflate storage and bit proofs, public entry composition, tree construction and emission proofs |
| deflate window and match proofs | deflate, deflate_sequence_safety, deflate construction proofs, deflate entry composition, deflate lifecycle proofs, gzlib.c proofs, inflate storage and bit proofs, tree construction and emission proofs |
| deflate_base.c proofs | deflate_refusal, deflate lifecycle proofs, inflate storage and bit proofs, public entry composition |
| format proofs | short_decode_table_leaf_sound, short_rejected_leaf_stays_invalid, compress_roundtrip, format_deterministic, format_prefix_free, header_roundtrip, inflate_completes, rejected_has_no_symbols, api-model proofs, heap-free mathematics, inffast.c proofs, inftrees.c proofs, tree construction and emission proofs |
| gzfs proofs | gzlib.c proofs |
| gzfs.borrow-stable proofs | LibcBorrowLoops proofs, checksum.borrow-stable proofs, deflate lifecycle proofs, inflate storage and bit proofs, tree construction and emission proofs |
| gzfs.oracle proofs | public entry composition |
| gzlib.c proofs | gzclearerr, gzdopen, gzfs.oracle proofs, public entry composition |
| heap-free mathematics | match_array_refines_lz77, output_copy_refines_lz77, window_copy_refines_lz77, copy_back_compose, retained_history_agrees, window_distance_check_agrees, api-model proofs, deflate construction proofs, deflate lifecycle proofs, deflate window and match proofs, gzlib.c proofs, inflate storage and bit proofs, inftrees.c proofs, tree construction and emission proofs |
| infback.c proofs | inflateBackEnd, inflateBackInit_, public entry composition |
| inffast.c proofs | actual_body_preserves_origin, actual_body_refines_token, actual_fast_preserves_origin, actual_distance_block_preserves_origin, actual_distance_refines_lz77, distance_lookup_matches_format, fast_safe, step_safe, length_lookup_matches_format, actual_body_retains_selected_length, actual_copy_match_refines_lz77, match_array_refines_lz77, actual_drop_preserves_origin, actual_pull_preserves_origin, actual_rollback_preserves_origin, drop_preserves_origin, initial_origin, pull_preserves_origin, rollback_preserves_origin, output_copy_refines_lz77, heap-free mathematics, inflate storage and bit proofs, inftrees.c proofs |
| inffixed.h.fast-flags proofs | fixed_tables_have_fast_leaf_flags |
| inflate entry composition | inflateCopy, inflateEnd, inflateGetDictionary, inflateGetHeader, inflateInit2_, inflateInit_, inflateMark, inflatePrime, inflateReset, inflateReset2, inflateSetDictionary, inflateSyncPoint, inflateUndermine, inflateValidate, inflate_initialisation_domain, inflate_refusal, inflate storage and bit proofs, public entry composition |
| inflate mode and exit proofs | inffast.c proofs, inflate storage and bit proofs |
| inflate storage and bit proofs | deflateReset, deflateResetKeep, inflate, inflateBackEnd, inflateBackInit_, inflateCopy, inflateEnd, inflateGetDictionary, inflateInit2_, inflateInit_, inflateMark, inflateReset, inflateReset2, inflateResetKeep, inflateSetDictionary, inflateSyncPoint, inflateUndermine, inflateValidate, inflate_refusal, inflate_sequence_safety, api-model proofs, deflate lifecycle proofs, infback.c proofs, inffast.c proofs, inflate entry composition, inflate mode and exit proofs, public entry composition |
| inflate.c proofs | inflate mode and exit proofs, inflate storage and bit proofs |
| inftrees.c proofs | decode_table_matches_format, short_decode_table_leaf_sound, decode_table_leaf_sound, decode_table_read_preserved, constructor_establishes_decode_table_invariant, decode_table_invariant_of_prefix, constructor_establishes_query_stability, short_rejected_leaf_stays_invalid, constructor_establishes_fast_leaf_flags, leaf_classification_agrees, inflate_table_content, inflate_table_decoder_safe, inflate_table_read_extent, constructor_root_bits, constructor_subtable_bits, heap-free mathematics, inflate storage and bit proofs, tree construction and emission proofs |
| public entry composition | adler32_combine, adler32_combine64, adler32_z, compress2_safety, compress2_z_safety, compressBound, compressBound_z, compress_safety, compress_z_safety, crc32_combine, crc32_combine64, crc32_combine_gen, crc32_combine_gen64, crc32_combine_op, get_crc_table, gzbuffer, gzdopen, gzeof, gzerror, gzoffset, gzoffset64, gzrewind, inflateBackEnd, inflateBackInit_, inflate_back_initialisation_domain, inflate_refusal, uncompress2_safe, uncompress2_z_safe, uncompress_safe, uncompress_z_safe, zError, zlibVersion, adler32.c proofs, deflate lifecycle proofs, gzlib.c proofs, inflate storage and bit proofs |
| runtime object and arithmetic lemmas | byte_modifies_preserve_bases, byte_stores_preserve_bases, every_layout_is_representable, LibcBorrow proofs, LibcBorrowLoops proofs, LibcBorrowPrimitives proofs, PlatformMemory proofs, crc32_all_byte_views, crc32_z_all_byte_views, actual_body_preserves_origin, actual_body_refines_token, actual_fast_preserves_origin, actual_distance_block_preserves_origin, actual_distance_refines_lz77, fast_safe, actual_body_retains_selected_length, actual_copy_match_refines_lz77, actual_pull_preserves_origin, actual_rollback_preserves_origin, decode_table_classifies_input, decode_table_matches_format, short_decode_table_leaf_sound, decode_table_leaf_sound, constructor_establishes_decode_table_invariant, constructor_establishes_query_stability, constructor_establishes_fast_leaf_flags, inflate_table_content, inflate_table_decoder_safe, inflate_table_read_extent, constructor_root_bits, constructor_subtable_bits, compress2_z_first_alloc_failure, adler32, adler32_z, crc32, crc32_z, deflateCopy, deflateCopy_safety, deflateEnd, deflateGetDictionary, deflateInit2_, deflateInit_, deflatePending, deflateReset, deflateResetKeep, deflateSetHeader, deflateTune, deflateUsed, deflate_refusal, get_crc_table, gzclearerr, gzdopen, gzerror, gzoffset, gzoffset64, gzrewind, inflate, inflateBackEnd, inflateBackInit_, inflateCodesUsed, inflateCopy, inflateEnd, inflateGetDictionary, inflateGetHeader, inflateInit2_, inflateInit_, inflateMark, inflatePrime, inflateReset, inflateReset2, inflateResetKeep, inflateSetDictionary, inflateSyncPoint, inflateUndermine, inflateValidate, inflate_back_initialisation_domain, inflate_initialisation_domain, inflate_refusal, uncompress2_safe, uncompress2_z_safe, uncompress_safe, uncompress_z_safe, zError, zlibVersion, adler32.c proofs, api-model proofs, borrowed-byte-frame proofs, checksum.borrow-stable proofs, crc32.c proofs, deflate construction proofs, deflate entry composition, deflate lifecycle proofs, deflate window and match proofs, gzfs proofs, gzfs.borrow-stable proofs, gzlib.c proofs, heap-free mathematics, infback.c proofs, inffast.c proofs, inflate entry composition, inflate mode and exit proofs, inflate storage and bit proofs, inftrees.c proofs, public entry composition, specification lemmas, tree construction and emission proofs, zutil.c proofs |
| specification lemmas | every_existing_heap_accepts_layout, actual_body_preserves_origin, actual_body_refines_token, distance_lookup_matches_format, length_lookup_matches_format, actual_body_retains_selected_length, drop_preserves_origin, pull_preserves_origin, rollback_preserves_origin, decode_table_invariant_of_prefix, short_rejected_leaf_stays_invalid, gzdopen, gzlib.c proofs, inffast.c proofs, inflate storage and bit proofs |
| tree construction and emission proofs | deflate construction proofs, deflate entry composition, deflate lifecycle proofs, deflate window and match proofs, heap-free mathematics, public entry composition |
| zutil.c proofs | inflate_table_content, deflate construction proofs, deflate lifecycle proofs, inflate entry composition, inflate mode and exit proofs, inflate storage and bit proofs, inftrees.c proofs |

## Other registered theorems

These declarations are registered supporting execution results, lemmas or witnesses.
They are not additional fixed targets and do not grant a caller coverage colour.

| Declaration | Used by a fixed-target proof |
| --- | --- |
| [Zlib.Adler32.Proofs.adler32_combine64_safe](../ZlibF/Proof/adler32.c.lean#L977) | No fixed-target composition recorded |
| [Zlib.Adler32.Proofs.adler32_combine_c_safe](../ZlibF/Proof/adler32.c.lean#L982) | [adler32_combine](#target-zlibf-spec-public-goal-adler32-combine), [adler32_combine64](#target-zlibf-spec-public-goal-adler32-combine64) |
| [Zlib.Adler32.Proofs.adler32_combine_correct](../ZlibF/Proof/adler32.c.lean#L953) | No fixed-target composition recorded |
| [Zlib.Adler32.Proofs.adler32_combine_safe](../ZlibF/Proof/adler32.c.lean#L941) | [adler32_combine](#target-zlibf-spec-public-goal-adler32-combine), [adler32_combine64](#target-zlibf-spec-public-goal-adler32-combine64) |
| [Zlib.Adler32.Proofs.adler32_safe](../ZlibF/Proof/adler32.c.lean#L987) | No fixed-target composition recorded |
| [Zlib.Adler32.Proofs.adler32_z_correct](../ZlibF/Proof/adler32.c.lean#L786) | No fixed-target composition recorded |
| [Zlib.Adler32.Proofs.adler32_z_correct_ne_one](../ZlibF/Proof/adler32.c.lean#L798) | No fixed-target composition recorded |
| [Zlib.Adler32.Proofs.adler32_z_safe](../ZlibF/Proof/adler32.c.lean#L809) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.addrOf_safe](../ZlibF/Proof/crc32.c.lean#L2470) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.blockLittle_safe](../ZlibF/Proof/crc32.c.lean#L2464) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.braidTab_safe](../ZlibF/Proof/crc32.c.lean#L2460) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_combine64_correct](../ZlibF/Proof/crc32.c.lean#L2383) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_combine64_safe](../ZlibF/Proof/crc32.c.lean#L2377) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_combine_correct](../ZlibF/Proof/crc32.c.lean#L2398) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_combine_gen64_correct](../ZlibF/Proof/crc32.c.lean#L2334) | [crc32_combine_gen](#target-zlibf-spec-public-goal-crc32-combine-gen), [crc32_combine_gen64](#target-zlibf-spec-public-goal-crc32-combine-gen64), [crc32_combine_op](#target-zlibf-spec-public-goal-crc32-combine-op) |
| [Zlib.Crc32.Proofs.crc32_combine_gen64_safe](../ZlibF/Proof/crc32.c.lean#L2324) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_combine_gen_correct](../ZlibF/Proof/crc32.c.lean#L2353) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_combine_gen_safe](../ZlibF/Proof/crc32.c.lean#L2347) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_combine_op_correct](../ZlibF/Proof/crc32.c.lean#L2406) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_combine_op_diverges](../ZlibF/Proof/crc32.c.lean#L2371) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_combine_op_safe](../ZlibF/Proof/crc32.c.lean#L2362) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_combine_safe](../ZlibF/Proof/crc32.c.lean#L2393) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_correct](../ZlibF/Proof/crc32.c.lean#L2227) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Crc32.Proofs.crc32_null](../ZlibF/Proof/crc32.c.lean#L2223) | [crc32](#target-zlibf-spec-public-goal-crc32), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Crc32.Proofs.crc32_safe](../ZlibF/Proof/crc32.c.lean#L2236) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_z_correct](../ZlibF/Proof/crc32.c.lean#L2203) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Crc32.Proofs.crc32_z_null](../ZlibF/Proof/crc32.c.lean#L2190) | [crc32](#target-zlibf-spec-public-goal-crc32), [crc32_z](#target-zlibf-spec-public-goal-crc32-z), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Crc32.Proofs.crc32_z_safe](../ZlibF/Proof/crc32.c.lean#L2217) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crcByte_safe](../ZlibF/Proof/crc32.c.lean#L2448) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crcTab_safe](../ZlibF/Proof/crc32.c.lean#L2439) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc_word_big_safe](../ZlibF/Proof/crc32.c.lean#L2488) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc_word_correct](../ZlibF/Proof/crc32.c.lean#L2422) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc_word_safe](../ZlibF/Proof/crc32.c.lean#L2417) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.get_crc_table_correct](../ZlibF/Proof/crc32.c.lean#L2249) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.get_crc_table_safe](../ZlibF/Proof/crc32.c.lean#L2244) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.loadWord_safe](../ZlibF/Proof/crc32.c.lean#L2434) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.multmodp_correct](../ZlibF/Proof/crc32.c.lean#L2283) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.multmodp_diverges](../ZlibF/Proof/crc32.c.lean#L986) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.multmodp_safe](../ZlibF/Proof/crc32.c.lean#L2276) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.shr64_safe](../ZlibF/Proof/crc32.c.lean#L2474) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.wordAt_safe](../ZlibF/Proof/crc32.c.lean#L2455) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.x2nTab_safe](../ZlibF/Proof/crc32.c.lean#L2443) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.x2nmodp_correct](../ZlibF/Proof/crc32.c.lean#L2307) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.x2nmodp_safe](../ZlibF/Proof/crc32.c.lean#L2299) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.CommonInitializedDataTrace.cleanup](../ZlibF/Proof/deflate.c.engine.common-initialized-history-environment.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.CommonInitializedDataTrace.completed](../ZlibF/Proof/deflate.c.engine.common-initialized-data-history.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.CommonInitializedDataTrace.completes](../ZlibF/Proof/deflate.c.engine.common-initialized-history-completes.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.CommonInitializedDataTrace.completes_post](../ZlibF/Proof/deflate.c.engine.common-initialized-history-completes.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.CommonInitializedDataTrace.encoding](../ZlibF/Proof/deflate.c.engine.common-initialized-data-history.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.CommonInitializedDataTrace.environment](../ZlibF/Proof/deflate.c.engine.common-initialized-history-environment.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.CommonInitializedDataTrace.finish_continuation](../ZlibF/Proof/deflate.c.engine.common-initialized-history-completes.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.CommonInitializedEncodingState.ordinary_encoding_request](../ZlibF/Proof/deflate.c.engine.common-initialized-request.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.CommonNoFlushDataTrace.cleanup](../ZlibF/Proof/deflate.c.engine.common-no-flush-history-environment.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.CommonNoFlushDataTrace.completed](../ZlibF/Proof/deflate.c.engine.common-no-flush-data-history.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.CommonNoFlushDataTrace.completes](../ZlibF/Proof/deflate.c.engine.common-no-flush-history-completes.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.CommonNoFlushDataTrace.encoding](../ZlibF/Proof/deflate.c.engine.common-no-flush-data-history.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.CommonNoFlushDataTrace.environment](../ZlibF/Proof/deflate.c.engine.common-no-flush-history-environment.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.CommonNoFlushDataTrace.finish_continuation](../ZlibF/Proof/deflate.c.engine.common-no-flush-history-completes.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.CommonOrdinaryDataTrace.cleanup](../ZlibF/Proof/deflate.c.engine.common-ordinary-history-environment.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.CommonOrdinaryDataTrace.completed](../ZlibF/Proof/deflate.c.engine.common-ordinary-data-history.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.CommonOrdinaryDataTrace.completes](../ZlibF/Proof/deflate.c.engine.common-ordinary-history-completes.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.CommonOrdinaryDataTrace.encoding](../ZlibF/Proof/deflate.c.engine.common-ordinary-data-history.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.CommonOrdinaryDataTrace.environment](../ZlibF/Proof/deflate.c.engine.common-ordinary-history-environment.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.CommonOrdinaryDataTrace.finish_continuation](../ZlibF/Proof/deflate.c.engine.common-ordinary-history-completes.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.DefaultEncodingState.generic_basic_full_request](../ZlibF/Proof/deflate.c.engine.generic-basic-full-contract.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.DefaultFinishBoundary.follow_finish_continuation_end_status](../ZlibF/Proof/deflate.c.engine.generic-continuation-end-status.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.GenericDefaultRequestTrace.completes_with_original_birth_cleanup](../ZlibF/Proof/deflate.c.engine.generic-completion-lifetime.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.GenericDefaultRequestTrace.full_next_request_contract](../ZlibF/Proof/deflate.c.engine.generic-basic-history-full-contract.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.INSERT_STRING_ok](../ZlibF/Proof/deflate.c.engine.macros.lean#L177) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.UPDATE_HASH_ok](../ZlibF/Proof/deflate.c.engine.macros.lean#L147) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.chain_ok_of_chains](../ZlibF/Proof/deflate.c.engine.chains.lean#L194) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.chains_insert](../ZlibF/Proof/deflate.c.engine.chains.lean#L76) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.chains_slide](../ZlibF/Proof/deflate.c.engine.chains.lean#L138) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.common_initialized_level_four_complete_witness](../ZlibF/Proof/deflate.c.engine.common-initialized-data-history.lean#L93) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.common_no_flush_level_four_complete_witness](../ZlibF/Proof/deflate.c.engine.common-no-flush-history-witness.lean#L41) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.common_observed_initialization_encoding_state](../ZlibF/Proof/deflate.c.engine.common-initialized-state-init.lean#L15) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.common_observed_initialization_first_ordinary_encoding](../ZlibF/Proof/deflate.c.engine.common-initial-first-ordinary-encoding.lean#L15) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.common_observed_initialization_no_flush_encoding](../ZlibF/Proof/deflate.c.engine.common-initial-no-flush-encoding.lean#L14) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.common_ordinary_level_four_complete_witness](../ZlibF/Proof/deflate.c.engine.common-ordinary-history-witness.lean#L50) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.default_init_all_scalar_full_request_contract](../ZlibF/Proof/deflate.c.engine.all-scalar-full-contract.lean#L14) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.default_public_full_contract_witness](../ZlibF/Proof/deflate.c.engine.full-contract-witness.lean#L15) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.fill_fit](../ZlibF/Proof/deflate.c.engine.window.lean#L45) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.fill_post_room](../ZlibF/Proof/deflate.c.engine.window.lean#L40) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.form_init](../ZlibF/Proof/deflate.c.engine.hash.lean#L126) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.generic_default_public_contract](../ZlibF/Proof/deflate.c.default-public-contract.lean#L19) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.generic_default_request_trace_witness](../ZlibF/Proof/deflate.c.default-public-contract.lean#L62) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.header_ref_bound_128w](../ZlibF/Proof/deflate.c.engine.overlay-header-ref.lean#L290) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.header_ref_bound_256](../ZlibF/Proof/deflate.c.engine.overlay-header-ref.lean#L245) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.hkey_third](../ZlibF/Proof/deflate.c.engine.hash.lean#L139) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.lm_body_ok](../ZlibF/Proof/deflate.c.engine.lmbody.lean#L102) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.lm_inner_loop](../ZlibF/Proof/deflate.c.engine.lminner.lean#L114) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.lm_loop_ok](../ZlibF/Proof/deflate.c.engine.lmmain.lean#L77) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.longest_match_ok](../ZlibF/Proof/deflate.c.engine.lmmain.lean#L212) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.matchLen_agree](../ZlibF/Proof/deflate.c.engine.match.lean#L100) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.memory_fast_initialization_witness](../ZlibF/Proof/deflate.c.engine.memory-fast-initial.lean#L50) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.memory_fast_observed_initialization](../ZlibF/Proof/deflate.c.engine.memory-fast-observed-initial.lean#L49) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.memory_slow_initialized_state](../ZlibF/Proof/deflate.c.engine.memory-slow-initialized-state.lean#L62) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.memory_slow_observed_initialization](../ZlibF/Proof/deflate.c.engine.memory-slow-observed-initial.lean#L55) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.public_common_first_finish_encoding_input](../ZlibF/Proof/deflate.c.engine.common-first-finish-encoding.lean#L16) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.public_common_first_finish_encoding_state](../ZlibF/Proof/deflate.c.engine.common-first-finish-state.lean#L15) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.public_common_first_no_flush_encoding_input](../ZlibF/Proof/deflate.c.engine.common-first-input.lean#L16) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.public_common_first_no_flush_encoding_state](../ZlibF/Proof/deflate.c.engine.common-first-encoding-state.lean#L14) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.putShortMSB_ok](../ZlibF/Proof/deflate.c.engine.macros.lean#L119) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.put_byte_ok](../ZlibF/Proof/deflate.c.engine.macros.lean#L96) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.read_buf_ok](../ZlibF/Proof/deflate.c.engine.readbuf.lean#L99) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.read_buf_zero](../ZlibF/Proof/deflate.c.engine.readbuf.lean#L75) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.slide_copy](../ZlibF/Proof/deflate.c.engine.window.lean#L52) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.slide_hash_ok](../ZlibF/Proof/deflate.c.engine.slide.lean#L166) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.tinyOverlay](../ZlibF/Proof/deflate.c.engine.overlay-header-ref.lean#L352) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.tinyOverlayAt_128](../ZlibF/Proof/deflate.c.engine.overlay-header-ref.lean#L347) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.tinyOverlayAt_256](../ZlibF/Proof/deflate.c.engine.overlay-header-ref.lean#L342) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.upd3_indep](../ZlibF/Proof/deflate.c.engine.hash.lean#L45) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Deflate.Proofs.MemoryInit.public_valid_memory_init_lifecycle](../ZlibF/Proof/deflate.c.init.memory-lifecycle.lean#L13) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.MemoryInit.public_valid_memory_init_total](../ZlibF/Proof/deflate.c.init.memory-total.lean#L16) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateBound_nostate](../ZlibF/Proof/deflate.c.life.bound.lean#L330) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateBound_safe](../ZlibF/Proof/deflate.c.life.bound.lean#L319) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Deflate.Proofs.deflateBound_z_nostate](../ZlibF/Proof/deflate.c.life.bound.lean#L312) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateBound_z_safe](../ZlibF/Proof/deflate.c.life.bound.lean#L302) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Deflate.Proofs.deflateEnd_reject](../ZlibF/Proof/deflate.c.life.end.lean#L321) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateEnd_safe](../ZlibF/Proof/deflate.c.life.end.lean#L270) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflateEnd](#target-zlibf-spec-public-goal-deflateend) |
| [Zlib.Deflate.Proofs.deflatePending_reject](../ZlibF/Proof/deflate.c.life.check.lean#L173) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflatePending_safe](../ZlibF/Proof/deflate.c.life.check.lean#L146) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflatePrime_invalid_count](../ZlibF/Proof/deflate.c.prime.lean#L24) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Deflate.Proofs.deflatePrime_refused](../ZlibF/Proof/deflate.c.prime.lean#L15) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateResetKeep_reject](../ZlibF/Proof/deflate.c.life.reset.lean#L424) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateResetKeep_safe](../ZlibF/Proof/deflate.c.life.reset.lean#L367) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflateReset](#target-zlibf-spec-public-goal-deflatereset), [deflateResetKeep](#target-zlibf-spec-public-goal-deflateresetkeep), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Deflate.Proofs.deflateReset_reject](../ZlibF/Proof/deflate.c.life.reset.lean#L430) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateReset_safe](../ZlibF/Proof/deflate.c.life.reset.lean#L401) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflateReset](#target-zlibf-spec-public-goal-deflatereset), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Deflate.Proofs.deflateSetHeader_not_gzip](../ZlibF/Proof/deflate.c.life.check.lean#L92) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateSetHeader_reject](../ZlibF/Proof/deflate.c.life.check.lean#L98) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateSetHeader_safe](../ZlibF/Proof/deflate.c.life.check.lean#L83) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Deflate.Proofs.deflateStateCheck_total](../ZlibF/Proof/deflate.c.base.lean#L731) | [deflateCopy_safety](#target-zlibf-spec-public-goal-deflatecopy-safety), [deflatePending](#target-zlibf-spec-public-goal-deflatepending), [deflateSetHeader](#target-zlibf-spec-public-goal-deflatesetheader), [deflateTune](#target-zlibf-spec-public-goal-deflatetune), [deflateUsed](#target-zlibf-spec-public-goal-deflateused), [deflate_refusal](#target-zlibf-spec-public-goal-deflate-refusal) |
| [Zlib.Deflate.Proofs.deflateTune_reject](../ZlibF/Proof/deflate.c.life.check.lean#L54) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateTune_safe](../ZlibF/Proof/deflate.c.life.check.lean#L44) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Deflate.Proofs.deflateUsed_reject](../ZlibF/Proof/deflate.c.life.check.lean#L119) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateUsed_safe](../ZlibF/Proof/deflate.c.life.check.lean#L113) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.lm_init_safe](../ZlibF/Proof/deflate.c.life.reset.lean#L151) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflateReset](#target-zlibf-spec-public-goal-deflatereset), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Deflate.Universal.Call.flush_pending_cursor](../ZlibF/Proof/deflate.c.universal-flush-cursor.lean#L157) | No fixed-target composition recorded |
| [Zlib.Deflate.Universal.copy_callfacts](../ZlibF/Proof/deflate.c.universal-ops-copy.lean#L868) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Deflate.Universal.copy_header](../ZlibF/Proof/deflate.c.universal-ops-copy.lean#L857) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Deflate.Universal.copy_inv](../ZlibF/Proof/deflate.c.universal-ops-copy.lean#L848) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Deflate.Universal.prime_callfacts](../ZlibF/Proof/deflate.c.universal-ops-callfacts.lean#L97) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Deflate.Universal.resetKeep_refuse](../ZlibF/Proof/deflate.c.universal-ops-resetkeep.lean#L64) | No fixed-target composition recorded |
| [Zlib.Deflate.Universal.resetKeep_single](../ZlibF/Proof/deflate.c.universal-ops-resetkeep.lean#L31) | No fixed-target composition recorded |
| [Zlib.Deflate.Universal.reset_callfacts](../ZlibF/Proof/deflate.c.universal-ops-callfacts.lean#L41) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Deflate.Universal.setDictionary_callfacts](../ZlibF/Proof/deflate.c.universal-ops-dictionary-slid.lean#L158) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Deflate.Universal.setDictionary_header](../ZlibF/Proof/deflate.c.universal-ops-dictionary-slid.lean#L135) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Deflate.Universal.setHeader_callfacts](../ZlibF/Proof/deflate.c.universal-ops-callfacts.lean#L75) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Deflate.Universal.step_prime](../ZlibF/Proof/deflate.c.universal-ops-prime.lean#L565) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Deflate.Universal.step_reset](../ZlibF/Proof/deflate.c.universal-ops-reset.lean#L85) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Deflate.Universal.step_setDictionary](../ZlibF/Proof/deflate.c.universal-ops-dictionary-slid.lean#L121) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Deflate.Universal.tune_callfacts](../ZlibF/Proof/deflate.c.universal-ops-callfacts.lean#L62) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Gzclose.Proofs.gzclose_dispatch](../ZlibF/Proof/gzclose.c.lean#L22) | No fixed-target composition recorded |
| [Zlib.Gzclose.Proofs.gzclose_null](../ZlibF/Proof/gzclose.c.lean#L17) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.GT_OFF_run](../ZlibF/Proof/gzlib.c.simple.lean#L46) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gz_error_null_run](../ZlibF/Proof/gzlib.c.error.lean#L134) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gz_intmax_run](../ZlibF/Proof/gzlib.c.simple.lean#L43) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gz_open_alloc_failure](../ZlibF/Proof/gzlib.c.open.lean#L35) | [gzdopen](#target-zlibf-spec-public-goal-gzdopen) |
| [Zlib.Gzlib.Proofs.gz_open_null](../ZlibF/Proof/gzlib.c.open.lean#L17) | [gzdopen](#target-zlibf-spec-public-goal-gzdopen) |
| [Zlib.Gzlib.Proofs.gz_reset_run](../ZlibF/Proof/gzlib.c.error.lean#L145) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gz_reset_safe](../ZlibF/Proof/gzlib.c.error.lean#L168) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzbuffer_null](../ZlibF/Proof/gzlib.c.simple.lean#L52) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzbuffer_run](../ZlibF/Proof/gzlib.c.simple.lean#L67) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzbuffer_safe](../ZlibF/Proof/gzlib.c.simple.lean#L84) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzclearerr_null](../ZlibF/Proof/gzlib.c.simple.lean#L191) | [gzclearerr](#target-zlibf-spec-public-goal-gzclearerr) |
| [Zlib.Gzlib.Proofs.gzclearerr_run](../ZlibF/Proof/gzlib.c.simple.lean#L199) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzclearerr_safe](../ZlibF/Proof/gzlib.c.simple.lean#L210) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzdopen_alloc_failure](../ZlibF/Proof/gzlib.c.open.lean#L61) | [gzdopen](#target-zlibf-spec-public-goal-gzdopen) |
| [Zlib.Gzlib.Proofs.gzdopen_joint_witness](../ZlibF/Proof/gzlib.c.dopen-joint-witness.lean#L92) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzdopen_negative](../ZlibF/Proof/gzlib.c.open.lean#L54) | [gzdopen](#target-zlibf-spec-public-goal-gzdopen) |
| [Zlib.Gzlib.Proofs.gzeof_null](../ZlibF/Proof/gzlib.c.simple.lean#L108) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzeof_run](../ZlibF/Proof/gzlib.c.simple.lean#L111) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzerror_null_file](../ZlibF/Proof/gzlib.c.simple.lean#L159) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzerror_run](../ZlibF/Proof/gzlib.c.simple.lean#L163) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzoffset64_null](../ZlibF/Proof/gzlib.c.rewind.lean#L103) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzoffset64_run](../ZlibF/Proof/gzlib.c.rewind.lean#L107) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzoffset_eq](../ZlibF/Proof/gzlib.c.rewind.lean#L129) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzopen64_alloc_failure](../ZlibF/Proof/gzlib.c.open.lean#L48) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzopen64_null](../ZlibF/Proof/gzlib.c.open.lean#L29) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzopen_alloc_failure](../ZlibF/Proof/gzlib.c.open.lean#L42) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzopen_null](../ZlibF/Proof/gzlib.c.open.lean#L24) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzrewind_null](../ZlibF/Proof/gzlib.c.rewind.lean#L73) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzrewind_spec](../ZlibF/Proof/gzlib.c.rewind.lean#L78) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzseek64_dangling_next_ok](../ZlibF/Proof/gzlib.c.seek.lean#L1052) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzseek64_head](../ZlibF/Proof/gzlib.c.seek.lean#L374) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzseek64_head_any](../ZlibF/Proof/gzlib.c.seek.lean#L231) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzseek64_null](../ZlibF/Proof/gzlib.c.seek.lean#L923) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzseek64_refuse](../ZlibF/Proof/gzlib.c.seek.lean#L955) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzseek64_safe](../ZlibF/Proof/gzlib.c.seek.lean#L930) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzseek64_set_negpos_refuse](../ZlibF/Proof/gzlib.c.seek.lean#L986) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzseek64_write_run](../ZlibF/Proof/gzlib.c.seek.lean#L387) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzseek_eq](../ZlibF/Proof/gzlib.c.seek.lean#L968) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gztell64_null](../ZlibF/Proof/gzlib.c.simple.lean#L122) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gztell64_spec](../ZlibF/Proof/gzlib.c.simple.lean#L143) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gztell_null](../ZlibF/Proof/gzlib.c.simple.lean#L154) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gztell_run](../ZlibF/Proof/gzlib.c.simple.lean#L148) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.seekTail_back](../ZlibF/Proof/gzlib.c.seek.lean#L592) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.seekTail_copy](../ZlibF/Proof/gzlib.c.seek.lean#L428) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.seekTail_copy_ub](../ZlibF/Proof/gzlib.c.seek.lean#L1063) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.seekTail_fwd](../ZlibF/Proof/gzlib.c.seek.lean#L490) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.seekTail_fwd_empty](../ZlibF/Proof/gzlib.c.seek.lean#L1003) | No fixed-target composition recorded |
| [Zlib.Gzread.Proofs.gzclose_r_null](../ZlibF/Proof/gzread.c.close.lean#L43) | No fixed-target composition recorded |
| [Zlib.Gzread.Proofs.gzclose_r_unbuffered](../ZlibF/Proof/gzread.c.close.lean#L56) | No fixed-target composition recorded |
| [Zlib.Gzread.Proofs.gzclose_r_unbuffered_frame](../ZlibF/Proof/gzread.c.close.lean#L78) | No fixed-target composition recorded |
| [Zlib.Gzread.Proofs.gzclose_r_wrong_mode](../ZlibF/Proof/gzread.c.close.lean#L47) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.NEEDBITS_run](../ZlibF/Proof/infback.c.macros.lean#L240) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.PULLBYTE_run](../ZlibF/Proof/infback.c.macros.lean#L156) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.PULL_run](../ZlibF/Proof/infback.c.pull.lean#L16) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.ROOM_inv](../ZlibF/Proof/infback.c.stored.lean#L35) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.ROOM_run](../ZlibF/Proof/infback.c.room.lean#L27) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.TYPE_last](../ZlibF/Proof/infback.c.inv.lean#L87) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.TYPE_more](../ZlibF/Proof/infback.c.inv.lean#L145) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.backInit_witness](../ZlibF/Proof/infback.c.callbacks.lean#L143) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.badMode_run](../ZlibF/Proof/infback.c.inv.lean#L127) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.inFinite_eof](../ZlibF/Proof/infback.c.macros.lean#L304) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.inflateBackEnd_nullstream](../ZlibF/Proof/infback.c.end.lean#L23) | [inflateBackEnd](#target-zlibf-spec-public-goal-inflatebackend) |
| [Zlib.Infback.Proofs.inflateBackEnd_ok](../ZlibF/Proof/infback.c.end.lean#L35) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.inflateBackEnd_refused](../ZlibF/Proof/infback.c.end.lean#L27) | [inflateBackEnd](#target-zlibf-spec-public-goal-inflatebackend) |
| [Zlib.Infback.Proofs.inflateBackInit__nullstream](../ZlibF/Proof/infback.c.init.lean#L239) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.inflateBackInit__ok](../ZlibF/Proof/infback.c.init.lean#L147) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.inflateBackInit__safe](../ZlibF/Proof/infback.c.init.lean#L203) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.inflateBack_eof](../ZlibF/Proof/infback.c.back.lean#L133) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.inflateBack_eof_witness](../ZlibF/Proof/infback.c.back.lean#L174) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.inflateBack_nostate](../ZlibF/Proof/infback.c.back.lean#L123) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.inflateBack_nullstream](../ZlibF/Proof/infback.c.back.lean#L118) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.order_inj](../ZlibF/Proof/infback.c.pure.lean#L17) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.order_lt](../ZlibF/Proof/infback.c.pure.lean#L14) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.order_surj](../ZlibF/Proof/infback.c.pure.lean#L21) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.storedTail_run](../ZlibF/Proof/infback.c.stored.lean#L125) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.stored_body_run](../ZlibF/Proof/infback.c.stored.lean#L285) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.stored_check](../ZlibF/Proof/infback.c.pure.lean#L35) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.stored_len_toNat](../ZlibF/Proof/infback.c.pure.lean#L58) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.stored_loop_run](../ZlibF/Proof/infback.c.stored.lean#L406) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.stored_run](../ZlibF/Proof/infback.c.stored.lean#L459) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.xwhileBrk_wf](../ZlibF/Proof/infback.c.wf.lean#L16) | No fixed-target composition recorded |
| [Zlib.Inffast.Proofs.distfix_tableSafe](../ZlibF/Proof/inffast.c.tableok.lean#L98) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inffast.Proofs.lenfix_tableSafe](../ZlibF/Proof/inffast.c.tableok.lean#L84) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.BITS_run](../ZlibF/Proof/inflate.c.main.macros.lean#L224) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.BITS_toNat](../ZlibF/Proof/inflate.c.main.macros.lean#L234) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.BYTEBITS_inv](../ZlibF/Proof/inflate.c.main.macros.lean#L293) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.BYTEBITS_run](../ZlibF/Proof/inflate.c.main.macros.lean#L283) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.DROPBITS_inv](../ZlibF/Proof/inflate.c.main.macros.lean#L251) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.DROPBITS_run](../ZlibF/Proof/inflate.c.main.macros.lean#L241) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.INITBITS_inv](../ZlibF/Proof/inflate.c.main.macros.lean#L304) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.NEEDBITS_run](../ZlibF/Proof/inflate.c.main.macros.lean#L150) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.PULLBYTE_succ](../ZlibF/Proof/inflate.c.main.macros.lean#L89) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.PULLBYTE_zero](../ZlibF/Proof/inflate.c.main.macros.lean#L44) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.UPDATE_CHECK_run](../ZlibF/Proof/inflate.c.main.check.lean#L21) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.bytesBits_eq_bytesToBits](../ZlibF/Proof/inflate.c.main.bits.lean#L107) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateCodesUsed_spec](../ZlibF/Proof/inflate.c.misc.lean#L180) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflateEnd_safe](../ZlibF/Proof/inflate.c.end.lean#L119) | [inflateEnd](#target-zlibf-spec-public-goal-inflateend), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflateGetDictionary_spec](../ZlibF/Proof/inflate.c.dict.lean#L82) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateGetHeader_check](../ZlibF/Proof/inflate.c.hdr.lean#L54) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateGetHeader_nogzip](../ZlibF/Proof/inflate.c.hdr.lean#L64) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflateGetHeader_null_faults](../ZlibF/Proof/inflate.c.hdr.lean#L114) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateGetHeader_ok](../ZlibF/Proof/inflate.c.hdr.lean#L80) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflateInit2_ok](../ZlibF/Proof/inflate.c.start.lean#L237) | [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2), [inflateInit_](#target-zlibf-spec-public-goal-inflateinit), [inflate_initialisation_domain](#target-zlibf-spec-public-goal-inflate-initialisation-domain), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflateInit2_safe](../ZlibF/Proof/inflate.c.start.lean#L324) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateInit__ok](../ZlibF/Proof/inflate.c.hdr.lean#L160) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateInit__safe](../ZlibF/Proof/inflate.c.hdr.lean#L134) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateMark_spec](../ZlibF/Proof/inflate.c.misc.lean#L140) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflatePrime_spec](../ZlibF/Proof/inflate.c.misc2.lean#L28) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflateReset2_safe](../ZlibF/Proof/inflate.c.init.lean#L395) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflateResetKeep_safe](../ZlibF/Proof/inflate.c.base.lean#L521) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflateReset_safe](../ZlibF/Proof/inflate.c.reset.lean#L160) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflateSetDictionary_dataerr](../ZlibF/Proof/inflate.c.dict.lean#L222) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateSetDictionary_safe](../ZlibF/Proof/inflate.c.dict.lean#L146) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateSetDictionary_streamerr](../ZlibF/Proof/inflate.c.dict.lean#L209) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateStateCheck_total](../ZlibF/Proof/inflate.c.base.lean#L445) | [inflateCodesUsed](#target-zlibf-spec-public-goal-inflatecodesused), [inflateEnd](#target-zlibf-spec-public-goal-inflateend), [inflateMark](#target-zlibf-spec-public-goal-inflatemark), [inflatePrime](#target-zlibf-spec-public-goal-inflateprime), [inflateSyncPoint](#target-zlibf-spec-public-goal-inflatesyncpoint), [inflateUndermine](#target-zlibf-spec-public-goal-inflateundermine), [inflateValidate](#target-zlibf-spec-public-goal-inflatevalidate), [inflate_refusal](#target-zlibf-spec-public-goal-inflate-refusal), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflateSyncPoint_spec](../ZlibF/Proof/inflate.c.misc.lean#L121) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflateSync_buf_error](../ZlibF/Proof/inflate.c.sync2.lean#L131) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflateSync_check](../ZlibF/Proof/inflate.c.sync2.lean#L113) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateUndermine_safe](../ZlibF/Proof/inflate.c.misc.lean#L109) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflateValidate_safe](../ZlibF/Proof/inflate.c.misc.lean#L95) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_CHECK_nowrap](../ZlibF/Proof/inflate.c.main.check.lean#L137) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_CHECK_run](../ZlibF/Proof/inflate.c.main.check.lean#L157) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_COPY__eq](../ZlibF/Proof/inflate.c.main.stored2.lean#L82) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_COPY_done](../ZlibF/Proof/inflate.c.main.stored.lean#L22) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_COPY_leave](../ZlibF/Proof/inflate.c.main.stored2.lean#L75) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_COPY_run](../ZlibF/Proof/inflate.c.main.stored2.lean#L57) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_DONE_run](../ZlibF/Proof/inflate.c.main.simple.lean#L25) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_LENGTH_run](../ZlibF/Proof/inflate.c.main.check.lean#L80) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_LENGTH_skip](../ZlibF/Proof/inflate.c.main.check.lean#L66) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_LENLENS_eq](../ZlibF/Proof/inflate.c.main.table3.lean#L82) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_LENLENS_run](../ZlibF/Proof/inflate.c.main.table6.lean#L41) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_LIT_full](../ZlibF/Proof/inflate.c.main.simple.lean#L29) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_LIT_run](../ZlibF/Proof/inflate.c.main.simple.lean#L37) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_STORED_bad](../ZlibF/Proof/inflate.c.main.stored2.lean#L97) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_STORED_ok](../ZlibF/Proof/inflate.c.main.stored2.lean#L116) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_STORED_wait](../ZlibF/Proof/inflate.c.main.stored2.lean#L88) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_TABLE_run](../ZlibF/Proof/inflate.c.main.table.lean#L52) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_TYPEDO_head](../ZlibF/Proof/inflate.c.main.type.lean#L61) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_TYPEDO_last](../ZlibF/Proof/inflate.c.main.type.lean#L26) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_TYPEDO_wait](../ZlibF/Proof/inflate.c.main.type.lean#L37) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_TYPE_go](../ZlibF/Proof/inflate.c.main.type.lean#L19) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_TYPE_leave](../ZlibF/Proof/inflate.c.main.type.lean#L11) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.ll1_run](../ZlibF/Proof/inflate.c.main.table4.lean#L69) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.llBody_run](../ZlibF/Proof/inflate.c.main.table3.lean#L95) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.llTail_run](../ZlibF/Proof/inflate.c.main.table5.lean#L46) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.lzBody_run](../ZlibF/Proof/inflate.c.main.table4.lean#L225) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.lz_run](../ZlibF/Proof/inflate.c.main.table4.lean#L244) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.noRet_NEEDBITS](../ZlibF/Proof/inflate.c.main.table2.lean#L321) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.ring_spec](../ZlibF/Proof/inflate.c.ring.lean#L116) | [inflateSetDictionary](#target-zlibf-spec-public-goal-inflatesetdictionary) |
| [Zlib.Inflate.Proofs.syncDone_good](../ZlibF/Proof/inflate.c.sync2.lean#L372) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.syncDone_owns](../ZlibF/Proof/inflate.c.sync2.lean#L423) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.syncDone_run](../ZlibF/Proof/inflate.c.sync2.lean#L248) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.syncScan_found_iff](../ZlibF/Proof/inflate.c.sync.lean#L342) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.syncScan_spec](../ZlibF/Proof/inflate.c.sync.lean#L300) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.syncStep_spec](../ZlibF/Proof/inflate.c.sync.lean#L202) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.syncTail_run](../ZlibF/Proof/inflate.c.sync2.lean#L543) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.syncsearch_null](../ZlibF/Proof/inflate.c.sync.lean#L450) | [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) |
| [Zlib.Inflate.Proofs.syncsearch_run](../ZlibF/Proof/inflate.c.sync.lean#L381) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.syncsearch_spec](../ZlibF/Proof/inflate.c.sync.lean#L485) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.typedoTail_bad](../ZlibF/Proof/inflate.c.main.type.lean#L154) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.typedoTail_fixed](../ZlibF/Proof/inflate.c.main.type.lean#L116) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.typedoTail_fixed_trees](../ZlibF/Proof/inflate.c.main.type.lean#L132) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.typedoTail_stored](../ZlibF/Proof/inflate.c.main.type.lean#L92) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.typedoTail_table](../ZlibF/Proof/inflate.c.main.type.lean#L104) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.updatewindow_ring](../ZlibF/Proof/inflate.c.ring.lean#L197) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.updatewindow_safe](../ZlibF/Proof/inflate.c.uw.lean#L558) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.uwPost_counts](../ZlibF/Proof/inflate.c.ring.lean#L170) | [inflateSetDictionary](#target-zlibf-spec-public-goal-inflatesetdictionary) |
| [Zlib.Inflate.Proofs.uw_null_ok](../ZlibF/Proof/inflate.c.uw.lean#L492) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.uw_post](../ZlibF/Proof/inflate.c.uw.lean#L423) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.xwhileBrk_run](../ZlibF/Proof/inflate.c.main.xloop.lean#L36) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Witness.init_witness](../ZlibF/Proof/inflate.c.witness.lean#L50) | No fixed-target composition recorded |
| [Zlib.Inftrees.Proofs.Cover.bits_add_drop](../ZlibF/Proof/inftrees.c.cover.leaf.lean#L80) | No fixed-target composition recorded |
| [Zlib.Inftrees.Proofs.Cover.cell_lt_fn](../ZlibF/Proof/inftrees.c.cover.fn.lean#L210) | No fixed-target composition recorded |
| [Zlib.Inftrees.Proofs.Cover.distLeaf_of](../ZlibF/Proof/inftrees.c.cover.leaf.lean#L56) | [decode_table_matches_format](#target-zlib-inftrees-spec-decodesemantics-goal-decode-table-matches-format), [decode_table_leaf_sound](#target-zlib-inftrees-spec-decodesoundness-goal-decode-table-leaf-sound), [constructor_establishes_query_stability](#target-zlib-inftrees-spec-decodetablestability-goal-constructor-establishes-query-stability), [constructor_establishes_fast_leaf_flags](#target-zlib-inftrees-spec-fasttableflags-goal-constructor-establishes-fast-leaf-flags), [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe), [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent), [constructor_subtable_bits](#target-zlib-inftrees-spec-subtable-goal-constructor-subtable-bits), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inftrees.Proofs.Cover.group_cover](../ZlibF/Proof/inftrees.c.cover.group.lean#L64) | [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe), [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent), [constructor_subtable_bits](#target-zlib-inftrees-spec-subtable-goal-constructor-subtable-bits), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inftrees.Proofs.Cover.group_cover_fn](../ZlibF/Proof/inftrees.c.cover.fn.lean#L163) | No fixed-target composition recorded |
| [Zlib.Inftrees.Proofs.Cover.group_cover_idx](../ZlibF/Proof/inftrees.c.cover.group.lean#L161) | [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe), [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent), [constructor_subtable_bits](#target-zlib-inftrees-spec-subtable-goal-constructor-subtable-bits), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inftrees.Proofs.Cover.group_cover_idx_fn](../ZlibF/Proof/inftrees.c.cover.fn.lean#L185) | No fixed-target composition recorded |
| [Zlib.Inftrees.Proofs.Cover.invalid_leaf](../ZlibF/Proof/inftrees.c.cover.leaf.lean#L66) | [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe), [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inftrees.Proofs.Cover.lenLeaf_of](../ZlibF/Proof/inftrees.c.cover.leaf.lean#L40) | [decode_table_matches_format](#target-zlib-inftrees-spec-decodesemantics-goal-decode-table-matches-format), [decode_table_leaf_sound](#target-zlib-inftrees-spec-decodesoundness-goal-decode-table-leaf-sound), [constructor_establishes_query_stability](#target-zlib-inftrees-spec-decodetablestability-goal-constructor-establishes-query-stability), [constructor_establishes_fast_leaf_flags](#target-zlib-inftrees-spec-fasttableflags-goal-constructor-establishes-fast-leaf-flags), [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe), [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent), [constructor_subtable_bits](#target-zlib-inftrees-spec-subtable-goal-constructor-subtable-bits), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inftrees.Proofs.Cover.root_cover](../ZlibF/Proof/inftrees.c.cover.root.lean#L90) | [decode_table_matches_format](#target-zlib-inftrees-spec-decodesemantics-goal-decode-table-matches-format), [short_decode_table_leaf_sound](#target-zlib-inftrees-spec-decodeshort-goal-short-decode-table-leaf-sound), [decode_table_leaf_sound](#target-zlib-inftrees-spec-decodesoundness-goal-decode-table-leaf-sound), [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant), [constructor_establishes_query_stability](#target-zlib-inftrees-spec-decodetablestability-goal-constructor-establishes-query-stability), [constructor_establishes_fast_leaf_flags](#target-zlib-inftrees-spec-fasttableflags-goal-constructor-establishes-fast-leaf-flags), [inflate_table_content](#target-zlib-inftrees-spec-goal-inflate-table-content), [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe), [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent), [constructor_subtable_bits](#target-zlib-inftrees-spec-subtable-goal-constructor-subtable-bits), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inftrees.Proofs.Cover.root_cover_complete_fn](../ZlibF/Proof/inftrees.c.cover.fn.lean#L140) | [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe), [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent), [constructor_subtable_bits](#target-zlib-inftrees-spec-subtable-goal-constructor-subtable-bits), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inftrees.Proofs.Cover.root_cover_fn](../ZlibF/Proof/inftrees.c.cover.fn.lean#L130) | No fixed-target composition recorded |
| [Zlib.Inftrees.Proofs.Cover.root_single_fn](../ZlibF/Proof/inftrees.c.cover.fn.lean#L226) | No fixed-target composition recorded |
| [Zlib.Inftrees.Proofs.inflate_fixed_ok](../ZlibF/Proof/inftrees.c.fixed.lean#L21) | No fixed-target composition recorded |
| [Zlib.Inftrees.Proofs.inflate_table_correct_ret](../ZlibF/Proof/inftrees.c.lean#L65) | [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inftrees.Proofs.inflate_table_safe](../ZlibF/Proof/inftrees.c.lean#L34) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.GB.kraft_clamped](../ZlibF/Proof/trees.c.heap.gbtree.lean#L132) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Trees.Proofs.Out.bi_flush_spec](../ZlibF/Proof/trees.c.bits.lean#L548) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Trees.Proofs.Out.bi_reverse_correct](../ZlibF/Proof/trees.c.reverse.lean#L91) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Trees.Proofs.Out.bi_reverse_safe](../ZlibF/Proof/trees.c.reverse.lean#L51) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.Out.bi_windup_spec](../ZlibF/Proof/trees.c.bits.lean#L731) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Trees.Proofs.Out.init_block_spec](../ZlibF/Proof/trees.c.block.lean#L217) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.Out.init_block_spec0](../ZlibF/Proof/trees.c.block.lean#L102) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2), [deflateInit_](#target-zlibf-spec-public-goal-deflateinit), [deflateReset](#target-zlibf-spec-public-goal-deflatereset), [deflateResetKeep](#target-zlibf-spec-public-goal-deflateresetkeep), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Trees.Proofs.Out.send_bits_spec](../ZlibF/Proof/trees.c.bits.lean#L411) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Trees.Proofs.Out.tr_align_emit](../ZlibF/Proof/trees.c.align.lean#L42) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Trees.Proofs.Out.tr_flush_bits_emit](../ZlibF/Proof/trees.c.align.lean#L30) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.Out.tr_init_spec](../ZlibF/Proof/trees.c.block.lean#L245) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflateInit_](#target-zlibf-spec-public-goal-deflateinit), [deflateReset](#target-zlibf-spec-public-goal-deflatereset), [deflateResetKeep](#target-zlibf-spec-public-goal-deflateresetkeep), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [Zlib.Trees.Proofs.Out.tr_tally_spec](../ZlibF/Proof/trees.c.tally.lean#L327) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.gen_bitlen_correct](../ZlibF/Proof/trees.c.heap.gbtop.lean#L403) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.gen_bitlen_safe](../ZlibF/Proof/trees.c.heap.gbtop.lean#L421) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.pqdownheap_correct](../ZlibF/Proof/trees.c.heap.pqrun.lean#L313) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.pqdownheap_safe](../ZlibF/Proof/trees.c.heap.pqrun.lean#L330) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.pqremove_correct](../ZlibF/Proof/trees.c.heap.pqrun.lean#L342) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.pqremove_safe](../ZlibF/Proof/trees.c.heap.pqrun.lean#L359) | No fixed-target composition recorded |
| [Zlib.Zutil.Proofs.zError_correct](../ZlibF/Proof/zutil.c.lean#L125) | No fixed-target composition recorded |
| [Zlib.Zutil.Proofs.zError_safe](../ZlibF/Proof/zutil.c.lean#L117) | No fixed-target composition recorded |
| [Zlib.Zutil.Proofs.zcalloc_correct_none](../ZlibF/Proof/zutil.c.lean#L271) | No fixed-target composition recorded |
| [Zlib.Zutil.Proofs.zcalloc_correct_size](../ZlibF/Proof/zutil.c.lean#L262) | No fixed-target composition recorded |
| [Zlib.Zutil.Proofs.zcalloc_correct_some](../ZlibF/Proof/zutil.c.lean#L248) | No fixed-target composition recorded |
| [Zlib.Zutil.Proofs.zcalloc_safe](../ZlibF/Proof/zutil.c.lean#L234) | No fixed-target composition recorded |
| [Zlib.Zutil.Proofs.zcalloc_zcfree_no_leak](../ZlibF/Proof/zutil.c.lean#L316) | No fixed-target composition recorded |
| [Zlib.Zutil.Proofs.zcfree_correct](../ZlibF/Proof/zutil.c.lean#L290) | No fixed-target composition recorded |
| [Zlib.Zutil.Proofs.zcfree_correct_null](../ZlibF/Proof/zutil.c.lean#L308) | No fixed-target composition recorded |
| [Zlib.Zutil.Proofs.zcfree_safe](../ZlibF/Proof/zutil.c.lean#L280) | No fixed-target composition recorded |
| [Zlib.Zutil.Proofs.zlibCompileFlags_correct](../ZlibF/Proof/zutil.c.lean#L175) | No fixed-target composition recorded |
| [Zlib.Zutil.Proofs.zlibCompileFlags_safe](../ZlibF/Proof/zutil.c.lean#L169) | No fixed-target composition recorded |
| [Zlib.Zutil.Proofs.zlibVersion_correct](../ZlibF/Proof/zutil.c.lean#L159) | No fixed-target composition recorded |
| [Zlib.Zutil.Proofs.zlibVersion_safe](../ZlibF/Proof/zutil.c.lean#L134) | No fixed-target composition recorded |
| [ZlibF.Spec.Api.Proofs.Layer.ext](../ZlibF/Proof/Format/Api.lean) | [dict_roundtrip](#target-zlibf-spec-api-goal-dict-roundtrip), [format_deterministic](#target-zlibf-spec-api-goal-format-deterministic), [format_prefix_free](#target-zlibf-spec-api-goal-format-prefix-free), [inflate_completes](#target-zlibf-spec-api-goal-inflate-completes), [inflate_decodes](#target-zlibf-spec-api-goal-inflate-decodes), [inflate_deferred_distance](#target-zlibf-spec-api-goal-inflate-deferred-distance) |
| [ZlibF.Spec.Api.Proofs.inflate_deferred_distance_rejects_legacy_consistency](../ZlibF/Proof/Api/InflateCausality.lean#L229) | No fixed-target composition recorded |
| [ZlibF.Spec.Blocks.append](../ZlibF/Proof/Format/Deflate.lean) | [compress_roundtrip](#target-zlibf-spec-api-goal-compress-roundtrip), [dict_roundtrip](#target-zlibf-spec-api-goal-dict-roundtrip), [format_deterministic](#target-zlibf-spec-api-goal-format-deterministic), [format_prefix_free](#target-zlibf-spec-api-goal-format-prefix-free), [inflate_completes](#target-zlibf-spec-api-goal-inflate-completes), [inflate_decodes](#target-zlibf-spec-api-goal-inflate-decodes), [inflate_deferred_distance](#target-zlibf-spec-api-goal-inflate-deferred-distance) |
| [ZlibF.Spec.Blocks.det](../ZlibF/Proof/Format/Deflate.lean) | [compress_roundtrip](#target-zlibf-spec-api-goal-compress-roundtrip), [dict_roundtrip](#target-zlibf-spec-api-goal-dict-roundtrip), [format_deterministic](#target-zlibf-spec-api-goal-format-deterministic), [format_prefix_free](#target-zlibf-spec-api-goal-format-prefix-free), [inflate_completes](#target-zlibf-spec-api-goal-inflate-completes), [inflate_decodes](#target-zlibf-spec-api-goal-inflate-decodes), [inflate_deferred_distance](#target-zlibf-spec-api-goal-inflate-deferred-distance) |
| [ZlibF.Spec.Gzip.ext](../ZlibF/Proof/Format/Wrapper.lean) | [dict_roundtrip](#target-zlibf-spec-api-goal-dict-roundtrip), [format_deterministic](#target-zlibf-spec-api-goal-format-deterministic), [format_prefix_free](#target-zlibf-spec-api-goal-format-prefix-free), [inflate_completes](#target-zlibf-spec-api-goal-inflate-completes), [inflate_decodes](#target-zlibf-spec-api-goal-inflate-decodes), [inflate_deferred_distance](#target-zlibf-spec-api-goal-inflate-deferred-distance) |
| [ZlibF.Spec.Prefix.det](../ZlibF/Proof/Format/Deflate.lean) | No fixed-target composition recorded |
| [ZlibF.Spec.Prefix.ext](../ZlibF/Proof/Format/Deflate.lean) | [compress_roundtrip](#target-zlibf-spec-api-goal-compress-roundtrip), [dict_roundtrip](#target-zlibf-spec-api-goal-dict-roundtrip), [format_deterministic](#target-zlibf-spec-api-goal-format-deterministic), [format_prefix_free](#target-zlibf-spec-api-goal-format-prefix-free), [inflate_completes](#target-zlibf-spec-api-goal-inflate-completes), [inflate_decodes](#target-zlibf-spec-api-goal-inflate-decodes), [inflate_deferred_distance](#target-zlibf-spec-api-goal-inflate-deferred-distance) |
| [ZlibF.Spec.Proofs.prefixFree](../ZlibF/Proof/Format/Huffman.lean#L105) | [short_decode_table_leaf_sound](#target-zlib-inftrees-spec-decodeshort-goal-short-decode-table-leaf-sound), [decode_table_leaf_sound](#target-zlib-inftrees-spec-decodesoundness-goal-decode-table-leaf-sound), [constructor_establishes_query_stability](#target-zlib-inftrees-spec-decodetablestability-goal-constructor-establishes-query-stability), [short_rejected_leaf_stays_invalid](#target-zlib-inftrees-spec-decodetablestability-goal-short-rejected-leaf-stays-invalid), [constructor_establishes_fast_leaf_flags](#target-zlib-inftrees-spec-fasttableflags-goal-constructor-establishes-fast-leaf-flags), [compress_roundtrip](#target-zlibf-spec-api-goal-compress-roundtrip), [dict_roundtrip](#target-zlibf-spec-api-goal-dict-roundtrip), [format_deterministic](#target-zlibf-spec-api-goal-format-deterministic), [format_prefix_free](#target-zlibf-spec-api-goal-format-prefix-free), [inflate_completes](#target-zlibf-spec-api-goal-inflate-completes), [inflate_decodes](#target-zlibf-spec-api-goal-inflate-decodes), [inflate_deferred_distance](#target-zlibf-spec-api-goal-inflate-deferred-distance), [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [ZlibF.Spec.Public.Proofs.DeflateCore.completes](../ZlibF/Proof/deflate.c.default-core-completes.lean#L89) | No fixed-target composition recorded |
| [ZlibF.Spec.Public.Proofs.DeflateCore.correct](../ZlibF/Proof/deflate.c.default-core-completes.lean#L140) | No fixed-target composition recorded |
| [ZlibF.Spec.Public.Proofs.DeflateCore.safe_encoding_and_cleanup](../ZlibF/Proof/deflate.c.default-core.lean#L181) | No fixed-target composition recorded |
| [ZlibF.Spec.Public.Proofs.DeflateInit.default_init_witness](../ZlibF/Proof/public-deflate-init.lean#L282) | No fixed-target composition recorded |
| [ZlibF.Spec.Public.Proofs.free_writable_matches_dropWindow](../ZlibF/Proof/Api/HeapCleanup.lean#L55) | No fixed-target composition recorded |
| [ZlibF.Spec.Public.Proofs.legacy_codes_used_impossible](../ZlibF/Proof/Api/QueryLayout.lean#L123) | No fixed-target composition recorded |
| [ZlibF.Spec.Zlib.ext](../ZlibF/Proof/Format/Wrapper.lean) | [compress_roundtrip](#target-zlibf-spec-api-goal-compress-roundtrip), [dict_roundtrip](#target-zlibf-spec-api-goal-dict-roundtrip), [format_deterministic](#target-zlibf-spec-api-goal-format-deterministic), [format_prefix_free](#target-zlibf-spec-api-goal-format-prefix-free), [inflate_completes](#target-zlibf-spec-api-goal-inflate-completes), [inflate_decodes](#target-zlibf-spec-api-goal-inflate-decodes), [inflate_deferred_distance](#target-zlibf-spec-api-goal-inflate-deferred-distance) |

## Refresh

Regenerate after proof or registry changes. The generator builds and inspects
exact compiled theorem types. It never changes a proof, target or registry.
Acceptance remains subject to [checking](checking/README.md).
The view is stale only when what it shows changes: a target, a registration, a proof status, a
link or a line anchor. Its links keep the revision they were generated at until then.
<!-- proof-progress:end -->

## Remaining work

Targets with red borders have a documented blocker with evidence and a next step below.
A long proof attempt alone does not establish a blocker. Gray targets may be started;
their missing internal lemmas and history invariants are not all drawn in the graph.

### Core proof skeletons

Scope change of 2026-11-11: only safety is planned (see [Scope](#scope)). Functional rows that
were still open are marked "not planned" and carry no hours; checked rows stay as they are.

#### inflate

Safety of the inflate family (owner's decision of 2026-11-11): no undefined behaviour, no
memory error, no leak, and termination, for every reachable history. Termination is part of
every row: each theorem concludes that the call returns `.ok`, which excludes
`Fault.outOfFuel` (`docs/spec/safety.md`). "Checked" means the theorem is on `dev` with the
fast gate green; "accepted" also needs the acceptance suite. Estimates are focused hours,
with an uncertainty of about half the figure, including build time on the shared build host.
The `meaning_*` rows of the format meaning are not planned and are no longer listed; what is
proved of them stays on `dev`.

Decoder invariant `InflateInv` (`inflate.c.invariant`): it generalizes `DefaultOriginState` to
raw, zlib, gzip and automatic detection, windowBits 0, and an attached gzip header record.
`DecoderHeldBits` (outside `BAD`, `MEM` and `SYNC`, at most 32 held bits) is carried beside it
on every reachable history.

| Lemma | Meaning | State | Hours |
| --- | --- | --- | ---: |
| `inflate_public` (`public-inflate`) | The theorem of type `Goal.inflate`: one call from every reachable stream, every configuration, gzip header record included. First sorry-free on `dev` at `8b12ff6a`; fast gate green on `2dab2f5e`. | checked | 0 |
| `inflate_reachable_invariant` (`inflate.c.reachable`) | `InflateInv` and `DecoderHeldBits` on every reachable history: init, rebuffer, every stream operation, `inflateCopy`. | checked | 0 |
| `inflate_call_held` (`inflate.c.held-history`) | One `inflate` call keeps `DecoderHeldBits`. A functional fact that safety needs: the bit buffer `hold` is 32 bits wide, so the decoder must never hold more. | checked | 0 |
| Progress clause of `Goal.inflate` | `rc = Z_OK → used ≠ 0 ∨ out ≠ []`. A functional fact that the termination of the `uncompress*` loop needs; part of `inflate_public`. | checked | 0 |
| `inflate_call_safe`, `operation_safe` (`inflate.c.sequence-safety`) | Every stream operation from a reachable history writes only the stream record, its own blocks, the header record and the caller regions of `StreamWriteRegions`, and changes the live blocks exactly by its own ledger. `inflate` through `InflateCall.safe`; `inflateSync` through `inflateSync_call_safe` (a window freed by the resynchronization included); the 12 others through `inflate.c.call-safety`. | checked | 0 |
| `inflateEnd_invariant` (`inflate.c.call-safety`) | `inflateEnd` on a reachable stream returns `Z_OK`, clears the state and frees every block the stream owns. | checked | 0 |
| `inflate_sequence_safety_public` (`public-inflate-sequence-safety`) | The theorem of type `Goal.inflate_sequence_safety` (= `StreamSequenceSafety .inflate`, the safety half of `Goal.inflate_sequence`). | checked | 0 |
| `inflateInit_`, `inflateInit2_` (`public-inflate-init`, `public-inflate-init2`) | Every windowBits and allocation outcome, in the source error order; an invalid width frees its state. `inflate_init2_public` is proved; it still needs registration. | checked | 0 |
| Resets, `inflateEnd`, `inflateGetDictionary`, `inflateSetDictionary`, `inflateGetHeader`, `inflatePrime`, `inflateSyncPoint`, `inflateMark`, `inflateCodesUsed`, `inflateUndermine`, `inflateValidate` | The lifecycle and query goals, including null and invalid streams. | registered | 0 |
| `inflateSync` | Safety on every reachable history: `inflateSync_call_safe`, part of the sequence theorem. The rest of `Goal.inflateSync` is the exact marker search (`Api.syncSearch`), a functional clause that no safety proof needs. | checked (safety) | 0 |
| `inflate_copy_public` (`public-inflate-copy`, `inflate.c.copy-public`) | The theorem of type `Goal.inflateCopy`: null arguments are refused; from every reachable source both allocation failures free what they allocated and clear `dest->state`, and success gives the relocated state, the window prefix and exactly the new blocks in the ledger. Composed from the six execution lemmas of `inflate.c.copy-*`. | checked | 0 |
| Acceptance batch | `inflate_public`, `inflate_init2_public`, `inflate_sequence_safety_public` and `inflate_copy_public` registered in `tests/audit/theorems.txt`, `Goal.inflate_sequence_safety` in `tests/audit/goals.txt`; nine function-body proof mutants for `inflate`, `inflateCopy` and `inflateInit2_` in `tests/proof-mutants/public-streams.tsv`, each killed in its listed module by a local run. The acceptance suite has not yet run on a named commit. | prepared | 0 |
| Cleanup | Delete fast-path and fixed-configuration proofs that no registered theorem uses. | open | 4 |
| `uncompress*` (`public-uncompress*`) | The functional goals: all four composed on `dev` from `DecoderFacts` (`uncompress2_z_of_facts`, `uncompress2_of_facts`, `uncompress_z_of_facts`, `uncompress_of_facts`). Not planned: the format facts of `DecoderFacts` are out of scope (safety only). | not planned | 0 |
| `uncompress*_safe` (batch 3) | `Goal.uncompress2_z_safe`, `uncompress2_safe`, `uncompress_z_safe`, `uncompress_safe` (`Spec/Public/Utilities`): no undefined behaviour, termination, writes only into the output buffer (at most its capacity) and the length cells, every allocation freed on every return path, the documented return codes, `Z_MEM_ERROR` only after an allocation failure. Proved with no premise in `public-uncompress-safe` (`uncompress2_z_safe`, `uncompress2_safe`, `uncompress_z_safe`, `uncompress_safe`): every `inflate` call is `inflate_public`, every reachable stream has a decoder (`reachable_invariant_kind`); no format fact and no functional fact. The functional proof shares the run (`SafeState`, `SafeFinal`) and adds its format fact (`NoOver`). Termination: the loop's measure (unread source plus unfilled room) is below the loop fuel and falls at every `Z_OK` call, by the progress clause of `Goal.inflate` (`rc = Z_OK → used ≠ 0 ∨ out ≠ []`), a safety fact. Statement test `tests/goals/uncompress-safety` (ASan, UBSan, leak count, allocation failures; no clause violated in 9000 runs). Accepted batch: the four theorems and goals are registered (`tests/audit/theorems.txt`, `goals.txt`); four translation mutants of `uncompress2_z` (`tests/proof-mutants/api-boundary.tsv`: dropped `inflateEnd`, wrong `destLen` count, refill off by one, leak on the init error path) are each killed in `public-uncompress-safe`, where the run meets the safety facts. The proof no longer restates the program (`program`, `program_eq` removed): it runs the translation, and the loop body is described by `BodyOK` with the refill stated as a minimum. | checked | 0 |
| **Total remaining** | | | **4** |

Batch 3 statement corrections and public domains. Each changes only an internal fact of
`DecoderFacts`; no public goal (`Goal.inflate_completes`/`InflateCompletes`, the four
`uncompress*` goals, the format goals) loses any part of its domain, so no `docs/deviations.md`
row is needed.
- `d23ce2d5` `NeedDictionaryCall` gains `log.singleDictionary = true` and `ByteObjectsFit h`;
  `InflateCompletes` and the uncompress loop already assume both.
- `61995719` `TraceEvidence` excludes a zlib dictionary with a configured window larger than
  the header's. Its only use, the uncompress loop, has no dictionary. The excluded case is C
  decoding a stream that RFC 1950 (`Zlib.Decodes`) does not allow, but it is not new: it is
  zlib's default with `INFLATE_STRICT` undefined, already modelled by
  `Api.Layer.InflateAccepted` and recorded in `tests/regression/inflate-configured-window`.
- `0c56ca53` `ConsumesWithinStream` clause 2 asks for a trailer, or room and a flush other than
  `Z_BLOCK`/`Z_TREES`. `InflateCompletes` gives room and such a flush; uncompress decodes zlib.
  The excluded case (raw data, no room) is correct C behaviour, not a finding.
- `ConsumesWithinStream` clause 2 concludes `rc ≠ Z_OK ∧ rc ≠ Z_BUF_ERROR` instead of
  `Z_STREAM_END ∨ Z_MEM_ERROR`: a call refused after the end (NULL `next_out`) returns
  `Z_STREAM_ERROR` with the whole stream consumed. Every use only rules out `Z_OK` and
  `Z_BUF_ERROR`. Correct C behaviour, not a finding.
- `a974ea43` `ConsumesWithinStream` and `StopsWhenBlocked` gain `ByteObjectsFit h`; the
  protocol history records it before every call.
- `ParseMeaning`'s request clause is an implication from the token to a `needDict` stage with
  `havedict = 0`, no longer an equivalence: after `Z_NEED_DICT`, a call refused with a NULL
  `next_out` returns `Z_STREAM_ERROR`, the token becomes false and the decoder still waits
  (`tests/verification/regressions/inflate-refused-dictionary-request.lean`). Every use took
  the implication. Internal; correct C behaviour, not a finding.

Object-size limit: `StreamReachable` assumes the LP64 `PTRDIFF_MAX` limit before every inflate
call and after every caller edit, and `StreamSequenceSafety` before every call (`408c1f04`).

##### inflate, batch 1: decoding side of the format meaning

The body of a deflate stream inside one call: block headers, fixed and dynamic table installation,
the code-length table, slow symbol decoding, stored copies, the whole `inflate_fast` call, match
copies from the output and the window, and the window update at `inf_leave`. Files
`inflate.c.meaning-<topic>`. Every lemma covers every window width 8 to 15 and every wrapper;
none fixes a configuration. Statement test: `tests/goals/inflate-meaning-body` (body-mode state
fields of the real decoder against the parse position: no clause violated in about 56,000 states
of 3,200 sessions, after the corrections below).

Interface corrections agreed with the inflate owner (2026-11-10). Each made `meaning_step` false
or unprovable; the evidence is the real decoder or a counterexample state.

- P1 (`0696a247`): zlib rejects some dynamic headers only after a whole part of the header is
  read, so `dynamicBits` has no completability premise
  (`tests/goals/inflate-meaning/late-rejection.c`: three one-call sessions stop in `LENLENS` or
  `CODELENS` with `Z_OK`).
- P2 (`0696a247`): `BodyMatches` of a dynamic header gets `DynamicMatches` (counts, code-length
  code and table, lengths read so far).
- P3 (`0696a247`): `WindowMeaning` with no window requires an empty history.
- P4 (`0696a247`): `storedPad`, because `STORED` drops the pad before it waits for `LEN`; real
  decoder: raw -15, a call stopped in `STORED` with 32808 bits consumed after a header ending at
  bit 32805 (regression `tests/verification/regressions/inflate-stored-pad.lean`).
- P5 (`0696a247`): `TableMeaning` includes `StableQuery`, needed to reject an invalid code on
  fewer than 15 held bits.
- P6 (`d9fa89d1`): a stored block holds no bits, so `COPY` follows the input.
- P7 (`69b25ebe`): held-bit bounds at every waiting position, so that fewer than 8 bits at a
  block boundary is inductive; real decoder: no violation of the numeric bounds in about 32,000
  body states of 1,800 sessions.
- P8 (`03c98f14`): in a body stage `out - left` is the call's output, as `MATCH` uses it.
- P9 (`03c98f14`): `partialCopy` carries the token's distance (`0 < dist ≤ |dict ++ out|`,
  `dist ≤ 32768`).
- P11: `BodyMatches` at `.storedHeader` holds fewer than 32 bits. The `STORED` complement check
  reads bits above 32, so without the bound `stored_step` is false: raw -15, input
  `01 01 00 FE FF 01` (a valid final stored block of one byte) read whole, 45 bits held in `STORED`;
  the check goes to `BAD`. zlib holds fewer than 8 bits after `TYPEDO` and fewer than 32 after
  waiting in `STORED`.
- P12 (`123722bb`): `PendingParsed` at `.copy` admits a complete match with nothing written and no
  history bound. `MATCH` leaves for want of output room before it checks the distance, so a
  too-far distance can wait there while the call returns `Z_OK`; real decoder: raw -15, input
  `03 02` with no output room stops in `MATCH` with `Z_OK`, offset 1 and an empty window, and the
  next call reports "invalid distance too far back" (`tests/goals/inflate-meaning-body/far-match.c`,
  regression `tests/verification/regressions/inflate-unchecked-match.lean`).
- P13 (`f88873e0`): the held-bit bounds at `.none` and `.distance` exclude only valid symbols
  (at most 285, at most 29) in the held bits without their last byte. `TableMeaning` says nothing
  of the bits a reserved symbol's entry consumes (30 and 31 in `fixedDistLens`, 286 and 287 in
  `fixedLitLens`), so the bound with any symbol was not provable at a lookup that leaves for
  input; a reserved symbol leads to `BAD` instead.
- P14: the `CODELENS` clause of `DynamicMatches` also holds the converse of `Trace`: every parse
  of the header bits from no length passes through the stored lengths. `Trace` alone does not fix
  where the items of the header end, so `codelens_step` was false at a repeat error. Counterexample
  state: `HLIT = 0`, `HDIST = 3` (261 lengths); the code-length code gives symbols 2, 16, 17, 18
  length 2 (`00`, `01`, `10`, `11`); `A = [2,2,2] ++ 0^253 ++ [2]` read by items `R`; header bits
  `R ++ 01` (the code of 16, its extra bits not read); stored lengths `A ++ [2,2]`. `Trace` holds
  (the only completion is two literals 2, and `R ++ 01 00 00` also gives `A ++ 2^4`). The source
  `R ++ 01 10 ...` is valid (16 with extra 1 gives `A ++ 2^4`, a complete literal/length code with
  end-of-block and a complete distance code), but the decoder reads `10` as 17 and goes to `BAD`.
- P15: `TableMeaning` also holds `PrefixQuery` (a fitted query selects the same entry from its
  zero-padded consumed bits) and `QueryCompatible` (the fast leaf flags). At `BAD`,
  `inflate_fast` drops only the rejected token's bits and then returns the unused whole bytes, so
  the input read can end inside the bits the lookup looked at; `Inv` and `StableQuery` do not fix
  how many bits a rejected entry needs. Counterexample: a fixed block whose literal/length table
  reads `{op 64, bits 6}` for the codes of 286 and 287 keeps `Inv`, `StableQuery` and
  `QueryCompatible`, the fast call reads up to `110001`, and the code of 284 (`11000100`) continues
  it validly. Kept as a smaller kernel-checked table with `Inv` and `StableQuery` but not
  `PrefixQuery` (`tests/verification/regressions/inflate-prefix-query.lean`). The constructor
  establishes it (`constructor_establishes_prefix_query`, kept by a later builder:
  `prefix_query_of_prefix`), and so do the fixed tables (`lenfix_prefix`, `distfix_prefix`).
- Shared block (goal change). The fast decoder's `Env` required input and output in distinct
  blocks (`hsep : ib ≠ ob`). That was too narrow: input and output may be disjoint ranges of one
  block, which is defined C ([reproduction](../tests/regression/inflate-shared-block/README.md)).
  `Env.hsep` is now `ib ≠ ob ∨ (ib = ob ∧ the input range [i0, i0 + avail_in) and the output range
  [o0, o0 + avail_out) are disjoint)`. The window block stays distinct from the output block. A
  piece of the loop whose output array `A` is arbitrary now also assumes `Env.InputFrame A i`: when
  the blocks are shared, `A` keeps the original input from the cursor `i` to the end of the input.
  Registered goals whose type changed: every goal over `Env` admits the shared block
  (`step_safe`, `fast_safe`, `actual_body_preserves_origin`, `actual_body_refines_token`,
  `actual_fast_preserves_origin`, `actual_distance_block_preserves_origin`,
  `actual_distance_refines_lz77`, `distance_lookup_matches_format`,
  `length_lookup_matches_format`, `actual_body_retains_selected_length`,
  `actual_copy_match_refines_lz77`, and the `Origin` goals). `StepPre` (so `step_safe`, the
  `actual_body_*` goals and `actual_body_retains_selected_length`) gains the field
  `inputFrame`; `actual_pull_preserves_origin`, `actual_rollback_preserves_origin`,
  `actual_distance_block_preserves_origin` and `actual_distance_refines_lz77` gain the premise
  `InputFrame`. With distinct blocks the new premise is vacuous, so each new type implies the old
  one. The whole-call goals `fast_safe` and `actual_fast_preserves_origin` carry no new premise: the
  loop discharges `InputFrame` from the separation, since the decoder writes only in the output
  range (`Env.inputFrame_of_frame`, `Env.InputFrame.write`).

The body-mode clauses are checked on the real decoder by `tests/goals/inflate-meaning-body`
(about 56,000 states of 3,200 sessions, no violation).

| Lemma | Meaning | State | Hours |
| --- | --- | --- | ---: |
| `meaning_interface_body` | P1 to P4, `DynamicMatches` and suffix stability in `TableMeaning` (`inflate.c.meaning`, `0696a247`). | checked | 0 |
| `LoopMatches` (`meaning-loop`, `meaning-write`, `meaning-frame`) | The relation between mode steps inside one call: registers, input consumed in the call, held bits, stage, output since the call base, window and check of the output before the call. Shared with batch 2. Agreed with batch 2; output-write and frame lemmas. | checked | 0 |
| `lenfix_inv`, `distfix_inv`, `lenfix_stable`, `distfix_stable` (`meaning-fixed-tables`) | The static fixed tables have `DecodeTableInvariant.Inv` with the fixed code lengths, short lookups included, suffix-stable and prefix-read queries (`lenfix_prefix`, `distfix_prefix`) and compatible leaf flags. | checked | 0 |
| `lookup_meaning` (`meaning-lookup`, `meaning-length`, `meaning-distance`) | Slow `lookup1`/`lookup2` on an `Inv` table with refill: the selected leaf is the symbol of the held bits, with fewer than 15 bits available, or the input has no valid symbol. Folded into the step lemmas (`fitted_leaf_meaning`, `lookupLoop_fail`, `lookup1_len_fail`, `lookup2_len_fail`). | checked | 0 |
| `codes_lookup_meaning` (`meaning-codelens-items`) | The same for the code-length table (`CodeLengthMeaning`), the empty code-length code included (`cl_iter`). | checked | 0 |
| `table_step` (`meaning-dynamic-steps`) | `TABLE`: wait, the count rejection (`BAD`, no valid continuation), or fall-through to `LENLENS` with `LoopMatches`. No hypothesis beyond the stream record. | checked | 0 |
| `lenlens_step` (`meaning-dynamic-steps`) | `LENLENS`: code-length code lengths across calls; rejected with no completion, or fall-through to `CODELENS` with `CodeLengthMeaning`, the empty-code cells and fewer than 8 held bits. Hypothesis beyond the stream record: `WellFormed` (array sizes). | checked | 0 |
| `codelens_step` (`meaning-dynamic-steps`, `meaning-codelens-items`, `meaning-dynamic-tables`) | `CODELENS`: lengths across calls, repeats (`BAD` through the converse of the parse), end-of-block and code checks (`BAD`: no `DynamicHeader` completion), installation of both tables with `Inv`, `StableQuery`, `PrefixQuery` and `QueryCompatible`, leave for `Z_TREES` or fall-through to `LEN_`. Hypotheses beyond the stream record: `WellFormed`, `CodeLengthInvariant`, the installed table's content classification. | checked | 0 |
| `typedo_step`, `type_step` (`meaning-block`) | `TYPE`, `TYPEDO` before the final block: stored, fixed (with `lenfix_inv`), dynamic, type 3 (`BAD`, no type-3 body). The static tables come from `LibraryGlobals`. | checked | 0 |
| `stored_step` (`meaning-block`, `meaning-copy`) | `STORED`, `COPY_`, `COPY`: padding, length check and byte copies across calls. No hypothesis beyond `LoopMatches`, the stream record and the window bounds; the held-bit bound comes from `BodyMatches` (P11). | checked | 0 |
| `len_slow_step` (`meaning-length`) | `LEN_`, slow `LEN`: literal, end of block (fewer than 8 held bits), length, invalid code (`len_slow_step`, `len__step`, into `lenext_step`). Hypotheses beyond those of `match_step`: the negated fast-branch condition and `DataTablesSafe`. | checked | 0 |
| `distance_steps` (`meaning-distance`) | `LENEXT`, `DIST`, `DISTEXT`: extra bits, distance symbol, invalid distance (`lenext_step`, `dist_step`, `distext_step`, into `match_step`). Hypotheses beyond those of `match_step`: `DataTablesSafe` and the back-counter bound (`DataPendingInvariant`). | checked | 0 |
| `lit_step` (`meaning-lit`) | `LIT`: the pending literal is written. | checked | 0 |
| `match_step` (`meaning-match`) | `MATCH`: copies from the output and from the window, overlap, too far back. | checked | 0 |
| `fast_call_meaning` (`meaning-fast-token`, `meaning-fast-loop`, `meaning-fast`, `inffast.c.body-token-reject`) | One whole `inflate_fast` call from `LEN`, in the standard step shape: more tokens of the block or the end of the block give `LoopMatches`; a rejected token gives `BAD` with `LoopDoomed` (P15: the token is rejected on its own bits, `actual_body_rejects_prefix`; a distance too far for the saved window is too far for the whole history under a full window, `Token.Rejected.rebase`). Input and output are any caller byte views `DispatchBuffers` admits, also disjoint ranges of one block (`inflate_fast_entry`, shared-block goal change above). The window block differs from the output block by the caller's output range (`callerRange_slow_output`), not by a premise. Hypotheses beyond `match_step`: `Good`, `DataTablesSafe`, `DataPendingInvariant`, `DispatchBuffers`, `ByteObjectsFit`. | checked | 0 |
| `leave_window_meaning` (`meaning-leave-window`) | `updatewindow` at `inf_leave` gives `WindowMeaning` of the output after the call, the first allocation included; an allocation failure keeps the state and the old `WindowMeaning`. Hypotheses: `Good`, the default allocator, the output bytes, the output buffer not the window block. | checked | 0 |
| Cleanup | Deleted the 33 `inflate.c.fast*` modules that no registered theorem, public goal, meaning module or other module imports (the earlier semantic slices and the view frames built on them). The other `inflate.c.fast*` modules are imported by the fast path of the meaning proof. | checked | 0 |
| **Remaining for batch 1** | | | **0** |

For batch 3: ConsumesWithinStream bounds.

| Name | Meaning | State | Hours |
| --- | --- | --- | --- |
| `HeldWithin` (`heldWithin`, `meaning-held-within`) | A decoder state at a grammar stage holds no bits past the end of a valid stream its bits are comparable with; no stage lies beyond a complete stream. Batch 3's statement plus one premise, `(consumed ++ held).length % 8 = 0`, which holds at the use. No other premise. | checked | 0 |
| `LeaveShort`, `LoopRefuted` in batch 1 step lemmas (`meaning-leave-short`) | Every leave of a body step for want of input (`have = 0`) holds bits that do not complete the field its mode waits for (`LeaveShort`: fewer than the `NEEDBITS` count, `COPY` with bytes left, no complete valid symbol or code-length item of any meaning of the installed table). Every rejection (`BAD`) reads input comparable with no valid full-window stream (`LoopRefuted`, stronger than `LoopDoomed`: the stream also does not end inside the bits read). Steps: `TYPE`/`TYPEDO`, `STORED`, `COPY_`/`COPY`, `TABLE`, `LENLENS`, `CODELENS`, `LEN_`/`LEN`, `LENEXT`, `DIST`, `DISTEXT`, `MATCH`, `inflate_fast`. Both checked first on the real decoder (`tests/goals/inflate-meaning-body`: about 75,000 starved leaves, about 490 data errors on corrupted sources, no violation). `LoopBad` (batch 2) still carries `LoopDoomed` (`LoopRefuted.doomed`). | checked | 0 |
| `StopShort` | A call that consumes exactly the whole valid stream does not return `Z_OK` or `Z_BUF_ERROR` (raw: unless the output room is short or flush is `Z_BLOCK`/`Z_TREES`). Per-call part checked: a trip of the mode loop short of its field (`LeaveShort`) has not read a whole valid stream (`LoopMatches.starved_not_end`, `meaning-stop-short`). Left: the whole-call composition (`loop_meaning`, batch 3), and the stops for room or `Z_BLOCK`/`Z_TREES` (`BlockedLeave`, `wrapParsed_due`). | not planned | — |
| `FailWithin` | A call that leaves `BAD` or `MEM` did not read past the end of a valid stream the input before it began. Per-call parts checked: a rejection excludes every comparable valid stream (`LoopRefuted.not_comparable`, `meaning-stop-short`), and at every trip the input read is a beginning of every comparable valid stream (`LoopMatches.within`, `meaning-held-within`, for the `MEM` leave). Left: the whole-call composition (`loop_meaning`, batch 3). | not planned | — |

##### inflate, batch 2: stream side of the format meaning

The wrapper header, the dictionary request and installation, the trailer, the end, the assembly
of mode steps into a call and of calls into a history, and `meaning_init`, `meaning_rebuffer`,
`meaning_dictionary`, `meaning_accepted`, `meaning_prefix`. Files `inflate.c.meaning-<topic>` and
`ZlibF/Math/inflate-meaning-*`. Every lemma covers raw, zlib, gzip and automatic detection and
every accepted windowBits, 0 included. In a protocol trace no header record is attached
(`inflateGetHeader` is not a trace step), so header capture never happens; the header modes are
proved with `head = NULL`. Statement test: `tests/goals/inflate-meaning` (state fields of the
real decoder against the parse position; no fact violated in 6000 sessions).

Interface corrections, agreed with the inflate owner and on `dev` (`bd0831d3`): the header stage
admits raw data before its first call; `ConfigMatches` ties the decoder configuration to the
trace; `needDict` admits any `DICTID`; fewer than 8 bits are held at a block boundary (batch 1
proves it); a `MEM` state keeps the conclusions of `meaning_accepted` and `meaning_prefix`;
`WrapMatches` holds the stream-side stage fields (`inflate.c.meaning-stream`).

| Lemma | Meaning | State | Hours |
| --- | --- | --- | ---: |
| `ConfigMatches`, `WrapMatches` | Configuration fields and per-stage fields of the header, `needDict`, trailer and end stages (`bd0831d3`). | defined | 0 |
| `LoopMatches` | Batch 1's row; batch 2 sent the draft and composes against it. | batch 1 | 0 |
| `wrap_header_grammar` (`Math/inflate-meaning-wrap`, `meaning-wrap-steps`) | Byte steps of the zlib and gzip headers keep a completable header prefix; the decoder's waiting points are not complete headers; completion to body or `needDict`; each rejection of `HEAD`, `FLAGS`, `HCRC` has no completion. | checked | 0 |
| `wrap_trailer_grammar` (`meaning-wrap-steps`, `meaning-accept`) | End of body to trailer to done; a trailer mismatch has no completion. | checked | 0 |
| `meaning_init` (`inflate.c.meaning-init`) | `inflateInit2_` for every accepted windowBits gives the header stage with no input. | checked | 0 |
| `meaning_rebuffer` (`meaning-rebuffer`) | A caller rebuffer keeps the state, window and tables; frame lemmas for every stage. | checked | 0 |
| `head_step` | `HEAD`: raw to `TYPEDO`, zlib header (width 0 sets the width), gzip magic, every rejection. | not planned | — |
| `dictid_step`, `dict_step` (`meaning-dictid`) | `DICTID` stores the identifier and asks for the dictionary (`dictid_step`, checked; `NeedDictExit`); `DICT` asks again or enters the body (open; needs P16, `last = total = 0` in the `needDict` clause, asked of batch 1). | not planned | — |
| `gzip_fixed_steps` | `FLAGS`, `TIME`, `OS`, `EXLEN`, with the header CRC accumulator. | not planned | — |
| `gzip_field_steps` | `EXTRA`, `NAME`, `COMMENT`: byte runs across calls, CRC over the input bytes. | not planned | — |
| `hcrc_step` | `HCRC`: the header CRC check and entry to the body. | not planned | — |
| Shared loop lemmas (`meaning-bits`, `meaning-stuck`, `meaning-outcome`, `meaning-fields`) | `LoopMatches.needbits`; `LoopDoomed.of_stuck`; `LoopBad`, `TripOutcome`, `bad_trip`; held bits as little-endian bytes. | checked | 0 |
| `trailer_steps` (`meaning-trailer`, `meaning-check`) | `DONE` and gzip `LENGTH` (checked); zlib and gzip `CHECK` with the Adler-32 or CRC-32 update of the call's output, then the length field or the end (`check_step`, checked); raw `CHECK` needs P10 (end stage in `CHECK` for raw data, proposed to batch 1). | not planned | — |
| `leave_meaning` (batch 3, `meaning-leave`) | `inf_leave`: totals and check update with the call's output; window update from batch 1's lemma; `Z_MEM_ERROR`. `leave_meaning` for a loop exit with `LoopMatches` (`LeaveMeaning`), `leave_meaning_bad` for the `BAD` exit (`LeaveBad`), from `inflate_leave_values` and `checkMeaning_leave`. | checked | 0 |
| `loop_meaning` (batch 3, `meaning-run`) | The mode loop of one call, entered with `LoopMatches`, ends in a `LoopExit`: a leave with `LoopMatches`, `Z_STREAM_END`, or `Z_DATA_ERROR` with `LoopBad`, or the dictionary request. Premises: `TripMeaning` (the per-mode steps of batches 1 and 2, mode by mode) and `SideKept` (the safety facts the steps need, kept by every trip). | checked | 0 |
| `meaning_step` assembly (batch 3) | Entry, refusals, run and leave give `ParseMeaning` after the call, with the request token. | not planned | — |
| `meaning_dictionary` (`meaning-dictionary`) | `inflateSetDictionary`: refusals, identifier mismatch, `Z_MEM_ERROR`, raw installation, zlib installation in `DICT`. | checked | 0 |
| `deflate_prefix_order` (`meaning-prefix-order`, `meaning-accept`) | A parse position on a prefix of a valid stream lies on its parse (output prefix, exact end), a finished parse is a specification parse, the configured zlib window decodes like the announced one, and stage headers are the stream's header. | checked | 0 |
| `meaning_accepted` (`meaning-format`) | A finished single-dictionary epoch consumed an accepted stream. | checked | 0 |
| `meaning_prefix` (`meaning-format`) | Prefix, no data error, exact end, also after `Z_MEM_ERROR`. | checked | 0 |
| Cleanup | Generalize or delete the default-configuration header, dictionary and wrapper modules. | not planned | — |
| **Remaining for batch 2** | | | **0** |

Batch 2, gzip header modes for `inflate_call_gzip`. Checked on `dev`:
`inflate_dispatch_gzip_header_rank` (`inflate.c.gzip-header-dispatch`), the inflate owner's
interface statement, exactly. One dispatch from `FLAGS` .. `HCRC` runs without a fault for any
wrapper with gzip allowed, with or without an attached header record, and keeps the
representation, the caller packet, the header record and the footprint. Two premises are
narrower than zlib.h (`docs/deviations.md`): the record's `extra` buffer is separate from the
unread input, and in `EXTRA` the record's `extra_len` is not below the remaining length. Both
come from real C undefined behaviour in EXTRA's `zmemcpy`
(`tests/regression/inflate-gzip-extra`). Whether `Goal.inflate` keeps them as caller-domain
clauses is the owner's decision. The name and comment buffers may overlap the input.

The skeleton clause "the flags word is kept or a 16-bit word" (skeleton/inflate 5d6f00e8) is
false as stated: `inflatePrime` can leave 32 bits in the bit buffer while the decoder waits in
`FLAGS`, and the real C then writes `flags = 65544`
(`tests/regression/inflate-gzip-flags-prime`). The proved form adds the condition on the entry
bit buffer. `InflatePhase.flags` makes the same 16-bit claim over every history; the owner decides
how to correct it.

| Lemma | Meaning | State | Hours |
| --- | --- | --- | ---: |
| `HeaderFoot` (`inflate.c.gzip-header-frame`) | Pointwise footprint against the entry heap; gives `BufferFrame` and `LiveChange`. | checked | 0 |
| `GzInv` (`inflate.c.gzip-header-state`) | Step invariant: state, stream and record writes, `hbuf` and region stores, `NEEDBITS`, input consumption. | checked | 0 |
| `gz_FLAGS` .. `gz_HCRC` (`inflate.c.gzip-header-modes`) | Each mode runs to a leave in a header mode, `TYPE` or `BAD`; the `NAME`/`COMMENT` byte loop; `CRC2`, `CRC4`; `EXTRA`'s copy. | checked | 0 |
| `inflate_dispatch_gzip_header_rank` (`inflate.c.gzip-header-dispatch`) | The interface theorem. | checked | 0 |
| `inflate_dispatch_gzip_header_flags_leave_word` (`inflate.c.gzip-header-dispatch`) | A leave has no input left; the flags word is kept, or is a 16-bit word when the entry bit buffer held 0, 8 or 16 bits. | checked | 0 |
| **gzip header modes** | | | **0** |

#### deflate

The skeleton is on the branch `skeleton/deflate`, file `ZlibF/Proof/deflate.c.universal.lean`.
It type-checks: `Goal.deflateInit2_`, `Goal.deflate` and `Goal.deflate_sequence` are proved there
from the open lemmas below. State "open" means the lemma has no proof yet; "checked" means it is
proved on `dev`. Estimates are focused
hours, with an uncertainty of about half the figure, including build time on the shared host.

One invariant `DInv` holds in every reachable state, for every level, `memLevel`, `windowBits`,
strategy, tuning value and header: `DGood`, the default allocator, the shape of the window, block,
lazy match, bit and pending state, the hash state (exact chains; at level 0 after one stored slide
the chains that `slide_hash` will repair; the rolling hash once there is lookahead), and the
recorded symbols of the current block with their leaf frequencies (`SymbolLedger`), cleared block
costs (`BlockClear`) and the pending bytes below them. `DInv` and the shared statement parts
(`StrategyEntry`, `CallFrame`, `WindowSide`, `Inserted`) are on `dev` in
`ZlibF/Proof/deflate.c.universal-invariant.lean`. The scalar fields are checked against the real C
on random histories by `tests/goals/deflate/invariant.c` (evidence, not proof). Other modules use its
interface (`DInv.dgood`, `DInv.unique`, `DInv.owned`, `DInv.rebuffer`), not its fields. One
ledger `Ledger` relates a data epoch to the stream: header and complete blocks decode to a prefix
of the input, the recorded symbols mean the next part (`Trace`), the window holds the rest.

Scope (owner, 2026-11-11): deflate is proved for safety only. The functional half (the ledger,
`completes`, `bound_before_output`, the functional clauses of `Goal.deflate_sequence`) is not planned;
its definitions on `dev` (`deflate.c.universal-ledger-defs`) and its statements on the skeleton stay
as they are. The sequence target is `Goal.deflate_sequence_safety` (`StreamSequenceSafety .deflate`,
the first conjunct of `Goal.deflate_sequence`), stated beside it without weakening it.

What the three compositions still need (2026-11-11). `reachable_inv`: `init2_inv`, `DInv.rebuffer`,
`copy_inv` (checked) and `operation_step`, together with the `HeaderInv` lemmas of batch C. `operation_step`
is `operation_step_of` (checked, batch 1) once these are theorems: `deflate_call` with `CallClauses`
(inflate batch 2), `step_setDictionary` and `step_params` (batch B), `step_resetKeep` (inflate batch 1, after
the positional hash-chain correction of `DInv`, written in the shared statement and landed with batch B's
strategy rework), the `HeaderInv` lemmas of those four operations, and the history premise that a
`deflateGetDictionary` buffer is a caller byte block (inflate batch 1). `deflate_proof`: `reachable_inv`,
`DInv.unique` (checked) and `deflate_call`. `Goal.deflate_sequence_safety`: `reachable_inv`,
`operation_step`, `end_from_inv` (checked). The shared premise `TinyOverlay` (the dynamic-block
room for `memLevel` 1 and 2) is a theorem since 09f19d3f (`tinyOverlay`,
`deflate.c.engine.overlay-header-ref`), so no premise remains on this path.

Open work for the deflate safety targets (2026-11-12). The between-calls invariant is
`DInv ∧ HeaderInv ∧ CallFacts`; a direct `deflateResetKeep` is not in the domain (`docs/deviations.md`); its
single-call safety is proved (9b449103). Estimates are focused hours.

| Open item | Owner | Hours |
| --- | --- | ---: |
| `deflate_call` assembly: checked given `TinyOverlay` (`deflate_call_of`, `deflate_calls_of`, `deflate_call_header`, `deflate.c.universal-call-assemble`) | inflate batch 2 | 0 |
| Strategy exports M5–M9, M13, M14, M16, M17 and M19 (`StrategyGaps` of `deflate_call_of`) | batch B | 10 |
| `step_params`: discharge `deflateCall`, `DeflateHeaderFact` (`SlideRepair` is gone: `SlidChains` at `chainTop` landed) | inflate batch 1, batch C | 2 |
| `HeaderInv` lemma of `deflate` (its header phase; `deflateParams`, `deflateSetDictionary`: checked) | batch C | 8 |
| `CallFacts` kept by `deflate` (`deflateCalls`: `deflate_calls_of`, checked given `TinyOverlay`; the others: checked, `setDictionary_callfacts`, `params_callfacts`) | inflate batch 2 | 0 |
| Discharge `SequenceFacts` (`deflate.c.universal-sequence-safety`) and close `Goal.deflate_sequence_safety`. Every field is a theorem under `TinyOverlay` alone: `sequence_facts_of` (`deflate.c.universal-call-header-fact`; `deflateHeader` from `deflate_call_header`, batch C; `FinishProgress` proved inside `deflate_call_full`). Closed (09f19d3f): `deflate_sequence_safety : Goal.deflate_sequence_safety` and `deflate_safety : Goal.deflate` with no hypothesis (`public-deflate-goals`, from `deflate_sequence_safety_two` / `deflate_safety_two` and `tinyOverlayAt_128`, `tinyOverlayAt_256`). Acceptance registration pending (`tests/audit/pending-deflate-safety.txt`, section C). | inflate batch 1 | 0 |
| `TinyOverlay`: dynamic-block room for `memLevel` 1 and 2 (premise of the strategy lemmas and `deflate_call`). Checked with no hypothesis (09f19d3f): `tinyOverlayAt_256`, `tinyOverlayAt_128`, `tinyOverlay` (`deflate.c.engine.overlay-header-ref`), from `header_ref_bound_256 : HeaderRefBound 245` and `header_ref_bound_128w : HeaderRefBound128W 29` (row `dynamic_overlay_small`) | inflate batch 1 | 0 |
| `TinyOverlayAt` threading (inflate batch 2): checked on `dev` in four slices. `Keys.lit` (a0bdc974); `FlushSafeAt L`, `Head.safe`, strategy lemmas take the instance for their own `lit_bufsize` (836987e5); the dispatch, gap and call lemmas and `deflate_call_full` take `OverlayAt d.lit_bufsize.toNat` (e88a305d); `lit_cases`, `tinyOverlay_of_two` and `public-deflate-safety-two`: `Goal.deflate`, `Goal.deflate_sequence_safety` and the four `compress*` goals from `TinyOverlayAt 128 ∧ TinyOverlayAt 256` (4ebf31c7). `TinyOverlay` is unchanged and equals `∀ L < 512, TinyOverlayAt L` (`tinyOverlay_iff`). `compress*` with no hypothesis (4d70859a): `compress2_z_safety`, `compress_z_safety`, `compress2_safety`, `compress_safety` of exactly the goal types (`public-compress-safe-mid`), over `DeflateReachMid` (`deflateInit2_` with `memLevel ≥ 3`, then rebuffers and `deflate` calls; `init2_lit`, `KeepRel` keeps `lit_bufsize`); the `compress*` proof is generic in the reachability (`CompressReach`). Also `goalDeflate_mid`: `Goal.deflate`'s conclusion along those histories. `Goal.deflate` and `Goal.deflate_sequence_safety` close from exactly `TinyOverlayAt 128` and `TinyOverlayAt 256` (`deflate_safety_two`, `deflate_sequence_safety_two`; axioms checked); the closing commit is written out in `tests/audit/pending-deflate-safety.txt`, section C. The all-operations `memLevel ≥ 3` form is set aside (supervisor, 2026-11-12) while batch 1 assembles the two sizes | inflate batch 2 | 0 |
| **Total, excluding the open research item** | | **45** |

Evidence for the exclusion of a direct `deflateResetKeep` (evidence, not proof): inflate batch 1's real-C
checker (not in the repository; pinned zlib, ASan and UBSan, allocator blocks filled with random bytes) checks
the exact `Hashing` of `dev` (`Chains` at `chainTop`, `SlidChains`, the rolling hash) after every call of random
histories of all stream operations (`deflate` with every flush value, `deflateParams`, `deflateSetDictionary`,
`deflateReset`, `deflatePrime`, `deflateCopy`, `deflateTune`) except a direct `deflateResetKeep`. It finds 0
failures on 4.61 million states. With a direct `deflateResetKeep` in the mix it finds failures (656 in 300
histories). A run of the checker is evidence about the C; it proves nothing about the model.

| Lemma | Meaning | State | Hours |
| --- | --- | --- | ---: |
| `DInv.dgood`, `DInv.defAlloc`, `DInv.unique`, `DInv.recorded`, `DInv.bi_valid_le` | Interface: the invariant gives `DGood`, the allocator, the symbol ledger, the bit bound, and determines the state (`deflate.c.universal-invariant`). | checked | 0 |
| `DInv.owned` | The blocks the history owns are the five blocks of the state. | checked | 0 |
| `DInv.rebuffer` | Caller rebuffering keeps the invariant. | checked | 0 |
| `init2_version`, `init2_null` | Version, stream-size and `NULL` refusals for every argument (`deflate.c.init.general`). | checked | 0 |
| `init2_main` | Every signed parameter tuple: refusal, the five allocation outcomes with cleanup, success with `DeflateInitial` (`deflate.c.init.general-main`). | checked | 0 |
| `init2_inv` | A successful `deflateInit2_` establishes `DInv` (`deflate.c.universal-init`). | checked | 0 |
| `deflateInit2_proof` | The theorem of type `Goal.deflateInit2_` (`public-deflate-init2`). | checked | 0 |
| `fill_window_inv` | `fill_window`: input read with checksum, slide of window and hash tables, string insertion, high-water margin; afterwards matcher room or no input. | checked | 0 |
| `longest_match_inserted` | No fault and termination for every tuning value; a real match within the lookahead. | checked | 0 |
| `flush_block_spec` | `FLUSH_BLOCK_ONLY` at a nonzero level with nothing pending and a non-`NULL` output buffer: stored, fixed or dynamic, `send_all_trees`, `compress_block` inside the shared buffer (F9), `flush_pending`, and `DInv` afterwards. Checked on `dev` with no premise for `memLevel` 3 to 9 (`flush_block_spec_mid`, `trees.c.universal-overlay-mid`; `flush_block_spec_large` for 5 to 9), and for every `memLevel` given `TinyOverlay` (`flush_block_spec_of_tiny`); the general form takes the overlay room `DynamicOverlay` as premise (`flush_block_spec_of_overlay`). `last` is a `Bool` (0 or 1, as at every call site). The explicit-premise forms used inside a strategy are `flush_block_only_safe` and `flush_block_dinv`; they also give the output total, the kept input total and the output `BufferFrame`, and batch B's `FlushSafe` follows from `TinyOverlay` alone (`flushSafeFrame_of_tiny`). `TinyOverlay` is a theorem (`tinyOverlay`, 09f19d3f), so `flush_block_spec_of_tiny tinyOverlay` holds for every `memLevel`. | checked for every `memLevel` | 0 |
| `dynamic_overlay_small` | F9 for dynamic blocks at small `memLevel`: every prefix of the tree description and symbol codes stays below the next unread symbol (`DynamicOverlay`). Checked for `memLevel` 5 to 9 (`dynamic_overlay_large`) and 3 to 4 (`dynamic_overlay_mid`, `trees.c.universal-overlay-mid`: the trees are never clamped since their weight is below F(16)+F(15) = 1597, which caps the excess per code). Open for `memLevel` 1 and 2 (`TinyOverlay`; `smallOverlay_of_tiny`, `flushSafe_of_tiny`). There the per-code excess bound (388 and 856 bits) plus any provable header bound exceeds the budget; a proof needs an optimal-cost bound for the bit-length tree and a tighter excess bound. `tests/goals/overlay` found no violation (smallest gap 58 and 161 bytes). `TinyOverlay` takes `BlockClear` at the block start, so that `opt_len` and `static_len` mean the encoded lengths (`dynamic_opt_len`, `dynamic_static_len`, checked). Route: from the dynamic choice, `H + bitExcess ≤ 5 + G` with the gain `G = Σ (s_i − min(d_i, 24))` (`choice_gain`, checked), so `G + 30 ≤ 8 * lit_bufsize` gives the room (`dynamic_overlay_of_gain`, checked, `deflate.c.engine.overlay-gain`). The excess with actual frequencies is checked for `lit_bufsize ≤ 1024`: at most `excessFibActual (lit_bufsize + 2)`, each length or distance code at the longest length its frequency allows under the Fibonacci bound (`excess_fib_actual`, `deflate.c.engine.overlay-fib-actual`). `TinyOverlay` follows from two open hypotheses with a header bound `Hb` as parameter (`tiny_overlay_of`, checked, `deflate.c.engine.overlay-tiny`): `HeaderFibBound Hb` (the header is at most `Hb`, for the 7-bit bit-length tree with zlib's repair) and `LinkC Hb` (if `G + 30 > 8 * lit_bufsize`, then `Hb` + the excess at actual frequencies + 25 fits `8 * lit_bufsize`). Route decision (2026-11-12, `tests/goals/overlay-adversarial`): no overwrite found in targeted, sanitizer-checked blocks; tightest worst-order room 266 bits at `memLevel` 1 (header 645, excess 88) and 1023 bits at `memLevel` 2. `HeaderFibBound` with the plain Fibonacci bound is false: zlib's 7-bit repair of the bit-length tree costs more than Huffman (57 bits in the first search, a frequency-24 symbol gets length 7; 136 bits on arbitrary histograms of weight ≤ 316), so a header bound has the form `cost_zlib ≤ Σ f·κ + Δ` for a fixed complete reference code `κ`, with `Δ` the repair excess (to prove; see the lemma list below). `memLevel` 2 then needs no `LinkC` and no dynamic choice: a linear programme over code-length histograms (Kraft, Fibonacci frequency bound, symbol and zero-run counts, excess per occurrence) bounds header + excess by 1863 with one reference code against 2023, so `Δ ≤ 146` sufficed (`certificate/header_lp.py`); batch 3's sharper programme below needs `Δ ≤ 132`. `memLevel` 1 stays open: the same programme with the dynamic choice gives 1020 against 999, and 1013 after branching on length-1 codes (the rich-match branch); a deeper branch or a sharper Huffman fact is needed. Splitting on the number of distinct codes does not help: the choice side fails at 70 codes and the header side needs the same bit-length analysis. Lemma list (2026-11-12). The certificate consumes `(dynamicHeaderBits ready mb).length ≤ 71 + Δ + Σ_k blScanCount ready k · (κ0 k + blExtraBits k)` with κ0 = [2,7,7,5,5,4,4,4,4,3,4,4,7,7,7,7,7,3,7] (complete); batch 3's certificate leaves `Δ ≤ 171` (target `HeaderRefBound Δ`). Batch 1, the header bound (`HeaderRefBound Δ` at `lit_bufsize` 256, Δ ≤ 171, and its twin at 128, Δ ≤ 110, for `TinyOverlayAt 256` and `TinyOverlayAt 128`): H1, the bit-length tree that `build_tree` builds (before the 7-bit repair) costs at most any reference code with Kraft sum ≤ 1: checked on the heap tree (`PShape.depth_cost_le_kraft`, `deflate.c.engine.overlay-reference`; heap-free `ZlibF.Math.HuffmanReference`); H1-link and H2a, checked for every `max_length ≤ 15`, in particular the 7-bit tree: `build_tree` returns the heap tree, its weights and the rank-cost bound `Σ_r w·len ≤ Σ_r w·δ + repairExtra` (true depths `δ`; `repairExtra` is the sum of the weights of the ranks that the repair steps lengthen) (`ws_build_tree_rank_initialized`, `BTRankOrigins`, `trees.c.build.rank-cost`; heap-free `HuffmanAbstract.repair_cost_le`, `ZlibF.Math.HuffmanRepairCost`), and with H1, over the leaves of the tree, `Σ w·len ≤ Σ w·ℓ + repairExtra` for every reference code `ℓ` with Kraft sum ≤ 1 (`BTRankOrigins.cost_le_kraft`, `trees.c.build.rank-reference`); H2b, the constant, checked with per-rank Fibonacci caps at the clamped depth (`rank_cap`, `ZlibF.Math.HuffmanRepairCap`) and a generated case analysis over the clamped histograms (164 with at most 13 leaves, 535 with at most 15; `ZlibF/Math/RepairCap13*`, `RepairCap15*`, generator `tests/goals/overlay-adversarial/certificate/repair_caps.py`, test `regenerate-caps.sh`): for a tree of weight `W ≤ 316`, `repairExtra ≤ 29 + W/2` with at most 13 leaves and `≤ 245` with at most 15 (`BTRankOrigins.cost_le_kraft_cap13`, `_cap15`, `trees.c.build.rank-cap`); so `Σ w·len ≤ Σ w·ℓ + 29 + W/2` at 128, inside batch 3's `71 + W/2`, and `+ 245` at 256, inside 642 once the memLevel 2 certificate uses the region and choice rows (inside the current 171 it is not); the bit-length tree weighs up to about 316 (a dynamic `memLevel` 1 block on the real C has 274), so the earlier `Δ ≤ 72` from `W ≤ 130` was wrong; H3 at both sizes, 4–8 h, including the dummy leaves of a tree with fewer than two used symbols. Test results (real `trees.c`, adversarial bit-length histograms): at 256 the largest Δ found is 55 with bit-length symbols 12 to 15 absent and 136 with all 19 symbols; at 128 it is 14 (batch 3 found 47); on real blocks 13 (`memLevel` 2) and 4 (`memLevel` 1). Batch 3: R1, R2, R4, R5, R6 for `lit_bufsize` 128 (its section in this row). Batch 3, checked: the scan counts and the certificate replay. At `lit_bufsize = 256` every prepared block has `71 + refHeaderCost + bitExcess ≤ 1852` (`ref_header_excess_256`, `deflate.c.engine.overlay-mem2`; heap-free certificate `DeflateOverlayCertificate.certificate`, generated by `tests/goals/overlay-adversarial/certificate/overlay_cert.py`; per-entry scan bound `scan_cost_le`; forced leaves only at index ≤ 2 and Kraft from `build_tree`, `trees.c.build.dummy`), so the overlay room holds from the one open hypothesis `HeaderRefBound Δ` with `Δ ≤ 171` (`dynamic_overlay_256`). `refHeaderCost` is the cost of the scanned bit-length symbols under the reference code `κ0`. `memLevel` 1, checked (batch 3): `H + bitExcess ≤ 999` at `lit_bufsize = 128` from `HeaderRefBound128 Δ` with `Δ ≤ 132` (`header_excess_128`, `dynamic_overlay_128`, `deflate.c.engine.overlay-mem1`), with the region scan (`scan_cost_region`), the choice row per code (`choice_row`), the two-leaf fact for forced leaves (`trees.c.build.two-leaves`) and the generated certificate `DeflateOverlayCertificate128` (three cases, `overlay_cert128.py`). memLevel 2 with the region scan and the choice row (`DeflateOverlayCertificate256`, `dynamic_overlay_256c`, `deflate.c.engine.overlay-mem2c`) needs only `Δ ≤ 640`. So `TinyOverlay` follows from the two header bounds (`tiny_overlay_of_headers`, `deflate.c.engine.overlay-tiny-headers`): `HeaderRefBound Δ₂` with `Δ₂ ≤ 640` and `HeaderRefBound128 Δ₁` with `Δ₁ ≤ 132`, κ1 = [2,8,8,6,5,4,3,4,4,3 | 7,3,3]. Or, with the memLevel 1 repair excess growing with the number `W` of bit-length symbols, from `HeaderRefBound128W α` (`α ≤ 60`, the header at most `71 + α + W/2 + refHeaderCost128`) and `HeaderRefBound Δ₂` (`tiny_overlay_of_headers_w`, certificate `DeflateOverlayCertificate128W`, `deflate.c.engine.overlay-mem1w`). Small-block lengths are at most 9 (128) and 11 (256), `prepared_lengths_128`/`_256`. H3, checked (09f19d3f, batch 1): `BTRankLeaves` (`trees.c.build.rank-leaves`) adds to `BTRankOrigins` the heap leaves, the returned lengths, their Kraft sum and the two-leaf fact for the actual `build_tree`; `BTRankLeaves.cost_le_15` / `cost_le_13` bound the scanned frequencies at the 7-bit lengths by a reference code over an allowed symbol set (+245 at most 15 symbols, +29 + W/2 at most 13), the root weight being the sum of the leaves (`SibTree.root_weight`, `ZlibF.Math.HuffmanRootWeight`); a tree with a forced leaf has two leaves of length 1 and needs no repair term. With symbols 12..15 (256) or 10..15 (128) absent (`scanFreq_absent`, `prepared_lengths_*`) and `W ≤ 316` (`blScanCount_mass_le`): `header_ref_bound_256 : HeaderRefBound 245`, `header_ref_bound_128w : HeaderRefBound128W 29` (`deflate.c.engine.overlay-header-ref`), hence `tinyOverlayAt_256`, `tinyOverlayAt_128`, `tinyOverlay`. | checked for every `memLevel` (09f19d3f) | 0 |
| `stored_spec` | `deflate_stored`: direct copies, window retention, buffered stored blocks; `DInv`, caller buffers and stream accounting afterwards (`deflate.c.universal-stored-tail`). | checked | 0 |
| `fast_spec`, `slow_spec` | `deflate_fast` and `deflate_slow` with lazy matching, with stream accounting (`deflate.c.universal-strategy-specs`, `deflate.c.universal-slow`). Checked with batch C's `TinyOverlay` as the only premise, as `rle_spec` and `huff_spec`. | checked; `TinyOverlay` is a theorem (`tinyOverlay`, 09f19d3f) | 0 |
| `rle_spec`, `huff_spec` | `deflate_rle` and `deflate_huff`, with stream accounting (`deflate.c.universal-strategy-specs`). Checked with batch C's `TinyOverlay` as the only premise (the open `memLevel` 1, 2 case of `dynamic_overlay_small`). | checked; `TinyOverlay` is a theorem (`tinyOverlay`, 09f19d3f) | 0 |
| `call_frame` | A `deflate` call keeps level, `w_bits`, `hash_bits` and `gzhead`, changes `wrap` only with output, and on a zlib or gzip stream in `INIT_STATE` or `GZIP_STATE` that is not refused delivers a byte (used by `bound_before_output`). | open | 4 |
| `deflate_header_trailer` | Parts of one `deflate` call, as companion lemmas over the translation, each keeping `DGood`, `TreesInvAt` and the caller buffers for every parameter: the entry flush (`deflate.c.universal-call-entry`); the header stages chained into `header_phase` (`deflate.c.universal-call-headerphase`) for every entry status, with `HeaderEntry` from `ActiveHeader` (`fresh_header_entry`, `resumed_header_entry`); the flush markers (`marker_tail`); the trailer (`trailer_phase`). Each part also gives its heap frame for `deflate_call`: `StageFrame` (`deflate.c.universal-call-stageframe`: counts, totals, the output `BufferFrame`, heap shape, only the stream root, the state record, `pending_buf` and the output block changed; `StageFrame.call_facts`), `MarkerFrame` for the markers (the `head` block may change after `CLEAR_HASH`), the record shape `HeaderShape`, `HeaderInv d → HeaderInv d'` and `last_flush = -1` on an early `Z_OK`. The lift to `DInv` is `deflate_call`'s (`DInv.lift_empty`, owner 2). | checked | 0 |
| `deflate_call` | One `deflate` call (`DInv ∧ HeaderInv ∧ CallFacts` in and out): refusals, dispatch to the strategies, assembly of the parts, every clause of `Goal.deflate` including the `Z_FINISH` progress clause, and the owned blocks kept. `deflate_call_full` (`deflate.c.universal-call-assemble`) composes the `KeepRel` frame (`-call-keep-*`), the entry phase (`-call-entry-all`), the early returns (`-call-early`), the header step from the pre-call invariant (`-call-headerstep`), the strategy, marker and trailer tail (`-call-tail`, `-call-tailstep`) and the two entry cases (`cont_empty`, `cont_pending`). Corollaries: `deflate_call_of : DeflateCallFact`, `deflate_calls_of : DeflateCallsFact`, `deflate_call_header` (`HeaderInv` after a call). Only hypothesis: `TinyOverlay` (batch C). | checked; `TinyOverlay` is a theorem (`tinyOverlay`, 09f19d3f) | 0 |
| `operation_step` | Every other stream operation keeps the invariant with its frame: `deflateParams` (inner `deflate(Z_BLOCK)`, slide or clearing), `deflateSetDictionary`, `deflatePrime`, resets, `deflateSetHeader`, `deflateTune`, queries, bounds. Owners: `deflateSetDictionary` and `deflateParams` inflate batch 1 (from batch B; `deflate.c.universal-ops-dictionary`, `-params` by batch B, `-dictionary-slid`, `-params-general`); `deflatePrime`, resets and the dispatch batch 1 (`-prime`, `-reset`, `-dispatch`); the rest the deflate owner (`deflate.c.universal-ops`). Checked as `operation_step_of` (`deflate.c.universal-ops-dispatch`), the case split with these hypotheses: `deflate_call` plus the clause that the call keeps the five owned blocks (the skeleton statement lacks it; the allocation ledger needs it), `step_setDictionary` and `step_params` (which reads `CallFacts`), the header facts `HeaderInv` and the between-calls facts `CallFacts`. The `deflateGetDictionary` buffer may be any writable caller range, a byte block or the `depth` array of another deflate state record (`step_getDictionary`, `deflate.c.universal-ops-caller-view`, a frame argument). | checked given hypotheses | 0 (dispatch) |
| `step_params` | `deflateParams` keeps the invariant in every case (`deflate.c.universal-ops-params-general`; refusal and the change without a flush are batch B's, `-params`): the change before the first `deflate` call, `deflate(Z_BLOCK)` then the flush test (`Z_STREAM_ERROR`, `Z_BUF_ERROR` with the call's heap) or the change, and the level-0 repair (`slide_hash` for one pending slide, `CLEAR_HASH` for more). Companions `params_header`, `params_callfacts` and `params_body`. Owner: inflate batch 1. Hypotheses: `deflate_call` as in `operation_step_of` (and the header phase of `deflate`, or its `CallFacts`, for the companions), and `CallFacts d` of the entry state (P1 and P1b before the first `deflate` call; P2, P3, P6 come from `Shape`). With one pending slide, `SlidChains` holds at `chainTop` (`DInv`), so the repair after `slide_hash` is a congruence (`slide_repair`). | checked given hypotheses | 0 |
| `step_setDictionary` | `deflateSetDictionary` keeps the invariant in every case (`deflate.c.universal-ops-dictionary-slid`; the body with `matches = 0` is batch B's `setdict_body`). Header companions `setDictionary_header` (the statement of `SequenceFacts.setDictionaryHeader`) and `setDictionary_body`. Owner: inflate batch 1. The level-0 case with pending stored slides (`matches` 1 or 2, batch B's Finding 1) is `slid_body`: the body through a table view (`setdict_body_v`, `deflate.c.universal-ops-dictionary-view`; `fill_window_input_v`, `deflate.c.universal-window-view`; `deflate.c.engine.view-chains`), with the slid view for one slide and no chain fact for two. An inserted position appears in the slid view as `str - w_size` or `NIL` and is never followed (`chains_insert_slid`). The view uses the insertion frontier `strstart - insert` of the current `SlidChains`; if `SlidChains` moves to `chainTop` (Finding 2), the end frontier must follow. No premise. | checked | 0 |
| `resetKeep_single` | A direct `deflateResetKeep` call (outside the sequence domain, a deviation set by the deflate owner) from `DInv`: no fault, `Z_OK`, and exactly the writes of the stream record and the state record (`rkZ`, `rkPost`); window, `prev`, `head`, `pending_buf` unchanged, no allocation; refusal `resetKeep_refuse` (`deflate.c.universal-ops-resetkeep`). Owner: inflate batch 1. | checked | 0 |
| `step_reset` | `deflateReset` keeps the invariant with its frame (`deflate.c.universal-ops-reset`). The `deflateResetKeep` part, `step_resetKeep`, is blocked: `DInv.Hashing` is false after `deflateResetKeep` (reported). The call keeps `strstart`, `insert` and the hash tables but sets `lookahead = 0`, so chain heads at `strstart - 1` and `strstart - 2` lie above `chainTop`. | checked (`deflateReset`); blocked (`deflateResetKeep`) | 2 |
| `step_prime` | `deflatePrime` on a stream not yet started keeps the invariant: the compaction of pending bytes and the bit loop (`deflate.c.universal-ops-prime`). It takes the header facts `HeaderInv` beside `DInv` (no recorded symbol before the header). | checked | 0 |
| `copy_inv` | `deflateCopy` gives the destination the invariant (`deflate.c.universal-ops-copy`): the success path (`copy_cut`; the failure paths return `Z_STREAM_ERROR` or `Z_MEM_ERROR`), the new blocks, the window up to `high_water`, the partial copy of `prev` (`chains_copy`; tested on the real C first: no followed chain slot outside the copied part in 21005 copies). | checked | 0 |
| `operation_header` | The header facts `HeaderInv` (in a header state no symbol is recorded; from `EXTRA_STATE` to `HCRC_STATE` the gzip record is attached) hold after every stream operation. Checked on `dev` (`deflate.c.universal-header-inv`): `init2_header`, `tune_header`, `setHeader_header`, `reset_header`, `prime_header`. Open: `deflateSetDictionary` (needs the state fields from batch B's `setdict_body`), `deflateParams`, and `deflate` itself (the header phase). Checked as `operation_header_of` (`deflate.c.universal-ops-header`), the case split over every operation, with these hypotheses: the header lemmas of `deflate`, `deflateParams`, `deflateSetDictionary`, and the premise `CallFacts` (which `params_header` reads). A direct `deflateResetKeep` is not a stream operation. | checked given hypotheses | 0 (case split) |
| `operation_callfacts` | The between-calls facts `CallFacts` hold after every stream operation. Checked (`deflate.c.universal-ops-callfacts`, inflate batch 1): `reset_callfacts`, `prime_callfacts`, `tune_callfacts`, `setHeader_callfacts`, the queries (state unchanged), `copy_callfacts` (`-ops-copy`); `init2_inv` gives them at initialization. `setDictionary_callfacts` (`-ops-dictionary-slid`), `params_callfacts` (`-ops-params-general`, given `SlideRepair`). Checked as `operation_callfacts_of`, with the hypothesis for `deflate`. | checked given hypotheses | 2 |
| `copy_header` | `deflateCopy` copies the state record, so `HeaderInv` holds in the copy (`deflate.c.universal-ops-copy`, the skeleton statement). | checked | 0 |
| `copy_failure` | `deflateCopy` with a failed allocation (the state record, or any subset of the four buffer requests, which all run before the null test) returns `Z_MEM_ERROR`, frees every block it allocated, clears `dest->state`, and leaves the source and the other live blocks unchanged (`deflate.c.copy-failure`). | checked | 0 |
| `copy_success` | With every allocation successful, `deflateCopy` returns `Z_OK`: the destination is `DGood`, its state is `copiedDeflate`, the window, `head`, the copied part of `prev`, the pending bytes and the symbols are copied, and the ledger grows by exactly the five new blocks (`deflate.c.copy-success`, from `copy_tail_run`). | checked | 0 |
| `deflate_copy_public`, `deflate_copy_safety` (`public-deflate-copy`) | The theorems of type `Goal.deflateCopy` and `Goal.deflateCopy_safety`: null arguments refused; from a reachable source, `copy_failure` or `copy_success`. Statement tested on the real C first (`tests/goals/deflate-copy`: 144000 combinations, every subset of the five allocations failing, no violation). `Goal.deflateCopy_safety` adds zlib.h's refusal of an inconsistent source (`deflateCopy_refused`). Registered, with five structural public mutants (`tests/proof-mutants/public-streams.tsv`), each rejected by the kernel replay. | checked | 0 |
| `inflate_refusal`, `deflate_refusal` (`public-stream-refusal`) | The theorems of type `Goal.inflate_refusal` and `Goal.deflate_refusal`: a `NULL` or inconsistent stream (state `NULL`, `zalloc` or `zfree` `NULL`, or a live state the check refuses) is refused with `Z_STREAM_ERROR` by `inflate`, `inflateEnd`, `inflateReset`, `inflateReset2`, `inflateGetDictionary`, `inflateSetDictionary`, `inflateCopy`, `deflate`, `deflateSetDictionary`, `deflateParams`, `deflateGetDictionary` and `deflateCopy`, without a change (`inflate` makes and frees its local array; a copy clears `dest->state`). Statement tested on the real C first (`tests/goals/stream-refusal`: 192 calls, no violation). Registered; refusal mutants in `tests/proof-mutants/stream-refusal.tsv`. | checked | 0 |
| `reachable_inv` | Induction over `StreamReachable`: `DInv`, `HeaderInv` and `CallFacts` hold in every reachable state (`reachable_inv_of`, `deflate.c.universal-sequence-safety`). | checked in skeleton | 0 |
| `deflate_proof` | The theorem of type `Goal.deflate`. Checked as `deflate_proof_of (facts : SequenceFacts) : Goal.deflate` (`deflate.c.universal-deflate-proof`): `reachable_inv_of`, `DInv.unique`, the field `deflateCall`. It becomes `Goal.deflate` once the fields of `SequenceFacts` are theorems. `CallFacts.finishBits` (M18) is checked. | checked given hypotheses | 0 |
| **Subtotal `Goal.deflateInit2_` and `Goal.deflate`** | | | **150** |
| `end_from_inv` | `deflateEnd` from the invariant (reuses `deflate_end_public`). `deflate.c.universal-end`. | checked | 0 |
| `Ledger` | Final design of the ledger: header, block prefix, current block (symbols or stored window bytes), lazy literal, window contents, finished stream. | not planned (scope: safety) | 0 |
| `ledger_init`, `ledger_rebuffer` | Initialization establishes the ledger; rebuffering keeps it. | not planned (scope: safety) | 0 |
| `ledger_dictionary` | A preset dictionary before data: window and `DICTID`. | not planned (scope: safety) | 0 |
| `ledger_flush_pending` | The pending flush moves pending bytes to the caller; the ledger keeps its meaning. | not planned (scope: safety) | 0 |
| `ledger_header` | Header phase: zlib header with `DICTID` or gzip header, possibly interrupted; ends in the data phase with no block. | not planned (scope: safety) | 0 |
| `ledger_fill_window` | `fill_window`: read bytes join the accepted input and the lookahead; a slide keeps the window/data relation and the block start. | not planned (scope: safety) | 0 |
| `ledger_block_fixed` | A fixed block (`FLUSH_BLOCK_ONLY`) decodes to the open block's symbols, non-final or final. | not planned (scope: safety) | 0 |
| `ledger_block_dynamic` | A dynamic block decodes to the open block's symbols (tree description and codes). | not planned (scope: safety) | 0 |
| `ledger_block_stored` | A stored block from the window decodes to the window bytes of the block. | not planned (scope: safety) | 0 |
| `ledger_fast` | `deflate_fast`: the recorded symbols mean the input they cover, across fills and block flushes. | not planned (scope: safety) | 0 |
| `ledger_slow` | `deflate_slow`, with the lazy literal. | not planned (scope: safety) | 0 |
| `ledger_rle` | `deflate_rle`. | not planned (scope: safety) | 0 |
| `ledger_huff` | `deflate_huff`. | not planned (scope: safety) | 0 |
| `ledger_stored` | `deflate_stored`: buffered stored blocks and the direct copy to the caller. | not planned (scope: safety) | 0 |
| `ledger_align` | `Z_PARTIAL_FLUSH`: `_tr_align` appends an empty fixed block. | not planned (scope: safety) | 0 |
| `ledger_empty_stored` | `Z_SYNC_FLUSH`/`Z_FULL_FLUSH`: an empty stored block; hash clearing after a full flush. | not planned (scope: safety) | 0 |
| `ledger_trailer` | The trailer completes the stream from the checksum and the count. | not planned (scope: safety) | 0 |
| `ledger_step` | Assembly of the lemmas above along `deflate_phases`, with refusals and `Z_BUF_ERROR` returns. | not planned (scope: safety) | 0 |
| `trace_ledger` | Induction over `DeflateDataTrace`. | not planned (scope: safety) | 0 |
| `ledger_finished` | A finished epoch decodes to its input (`DecodesFor`). | not planned (scope: safety) | 0 |
| `ledger_flush` | A completed sync or full flush: input consumed, `FlushedFor`, restart after a full flush. | not planned (scope: safety) | 0 |
| `ledger_adler` | `adler` is the checksum of the accepted input. | not planned (scope: safety) | 0 |
| `bound_before_output` | `deflateBound` and `deflateBound_z` return the model bound before output. Checked part: every returning `deflate` call keeps `level`, `w_bits`, `hash_bits`, `gzhead`, `strm`, `|wrap|` and a valid status of every state record (`par_deflate`, `deflate.c.universal-params-deflate`). Open: the same frame for `deflateSetDictionary` (with its `strstart` effect), and the fact that an accepted call on a fresh zlib or gzip stream delivers output (asked of batch D). | not planned (scope: safety) | 0 |
| `completes` | `DeflateCompletes`: the worst-case expansion of every strategy and block choice stays within the bound, also across several `Z_FINISH` calls. | not planned (scope: safety) | 0 |
| `deflate_sequence_proof` | The theorem of type `Goal.deflate_sequence`. | not planned (scope: safety) | 0 |
| `deflate_sequence_safety_proof` | The theorem of type `Goal.deflate_sequence_safety` (`StreamSequenceSafety .deflate`), from `reachable_inv` and `operation_step`. | checked in skeleton | 0 |
| **Subtotal `Goal.deflate_sequence_safety`** | | | **0** |
| `compress*` | `Goal.compress*_safety` (`CompressorSafety`, the safety half of `CompressorContract`): proved in `public-compress-safe*` (`compress2_z_safety_of`, `compress2_safety_of`, `compress_z_safety_of`, `compress_safety_of`) from two explicit hypotheses, `Goal.deflate` and `DeflateLoopFacts`; `deflateInit_` and `deflateEnd` enter through their proved lemmas. Termination: the measure (unread source plus unfilled room) is below the loop fuel and falls at every `Z_OK` call, by `DeflateLoopFacts` for `Z_NO_FLUSH` (the call has input) and by the `Z_FINISH` progress clause of `Goal.deflate`. Each theorem is closed in one line once `Goal.deflate` and `DeflateLoopFacts` are. Under `TinyOverlay` alone: `compress2_z_safety_tiny`, `compress2_safety_tiny`, `compress_z_safety_tiny`, `compress_safety_tiny` (`public-compress-safe-call`, checked). The two call facts of `compress*_safety_of_tiny` are clauses of `deflate_call_full`: `CallProgress` (`call_progress_of`: an accepted call with input and output room before `FINISH_STATE` changes `avail_in` or `avail_out`) and `CallKeepsGzhead` (`call_keeps_gzhead_of`: `KeepRel.gz`, every state write of the call keeps `gzhead`). `memLevel` is 8 in `compress`, so `TinyOverlay` never applies there, but the deflate chain takes it as a global hypothesis. | checked (conditional) | 0 |
| `DeflateLoopFacts` (deflate owner) | Four facts about one `deflate` call that `Goal.deflate` does not state: progress of a `Z_NO_FLUSH` call with input and room, `Z_BUF_ERROR` or a written byte for new input after the first `Z_FINISH`, and, for every call, the gzip header pointer and the owned blocks kept (`public-compress-safe-init`). Derived in `public-compress-loop-facts` (`deflate_loop_facts_of`) from the skeleton statements `reachable_inv`, `deflate_call` (`CallClauses`), `call_frame`, and `FinishedNewInput` (new input after the first `Z_FINISH`), proved against the translation in `public-compress-finished` (`finished_new_input`, from the entry-phase lemmas and a frame of `flush_pending`); `deflate_loop_facts` needs only the three skeleton statements. | checked (conditional) | 0 |
| **Total** | | | **150** |

Batch C, gzip header stages for `call_frame` and `deflate_header_trailer`. `Goal.deflate` admitted a
gzip header name or comment that overlaps the bytes the call writes: the output range, or the
stream's `pending_buf`. On the real C a flush, or a header byte, overwrites the string's NUL and
the name loop reads past the buffer (`tests/regression/deflate-gzip-name-output`, both layouts
reproduced with sanitizers). zlib.h does not say whether either layout is permitted. The goal now
excludes both through `DeflateHeaderApart`, a conjunct of `ActiveHeader` (`docs/deviations.md`):
while the header is written, the input, output, extra field, name and comment are pairwise
separate byte ranges, and the header regions lie outside the stream's own storage.

Independent batches for additional owners. Each batch depends only on the statements of the
other batches (on `skeleton/deflate`), not on their proofs, and lives in its own files. The
invariant `DInv` and its interface belong to batch A; a change to `DInv` is announced to the others.

| Batch | Lemmas | Files | Hours |
| --- | --- | --- | ---: |
| A. Initialization and history (operations: `deflateSetDictionary`, `deflateParams` by the batch B owner; `deflatePrime`, resets, `copy_inv` and the `operation_step` case split by the inflate batch 1 owner) | `init2_inv`, `DInv.owned`, `DInv.rebuffer`, `operation_step`, `copy_inv` | `deflate.c.init.general`, `deflate.c.universal-ops` | 67 |
| B. Window and strategies | `fill_window_inv`, `longest_match_inserted`, `stored_spec`, `fast_spec`, `slow_spec`, `rle_spec`, `huff_spec` | `deflate.c.universal-window`, `deflate.c.universal-strategies` | 0 |
| C. Block emission and bounds | `flush_block_spec`, `bound_before_output`, `completes`, `call_frame`, `end_from_inv`, `deflate_header_trailer` | `trees.c.universal-block`, `deflate.c.universal-bound` | 156 |
| D. The call and the ledger | `deflate_call`, `Ledger`, `ledger_init`, `ledger_rebuffer`, `ledger_dictionary`, `ledger_step` and its 14 parts (`ledger_header` … `ledger_trailer`), `ledger_finished`, `ledger_flush`, `ledger_adler` | `deflate.c.universal-call`, `deflate.c.universal-ledger` | 227 |

`compress*` (12 hours) follows once A to D are checked.

Interface for an owner of batch B or C. Start from the branch `skeleton/deflate`, file
`ZlibF/Proof/deflate.c.universal.lean`.

- **Statements.** B: section 4, `stored_spec` to `huff_spec` (`fill_window_inv` and `longest_match_inserted` are checked). C: section 4, `flush_block_spec`;
  section 7, `bound_before_output` and `completes` (its statement is `DeflateCompletes` in
  `ZlibF/Spec/Public/Sequences.lean`).
- **What a lemma may assume.** The invariant `DInv` and `StrategyEntry` (on `dev`,
  `deflate.c.universal-invariant`),
  the other premises written in the lemma, and checked modules on `dev`: `deflate.c.engine.chains`,
  `lmbody`, `macros`, the `trees.c.*` modules and `ZlibF/Math/Deflate*`. B may use the statement
  of `flush_block_spec` from the skeleton; nothing else in the skeleton is a premise.
- **Changing `DInv`.** `DInv` belongs to batch A. If a proof needs a fact that `DInv` does not
  carry, write it as a premise of that lemma and tell A; A adds it to `DInv` and proves that every
  operation keeps it. Do not change `DInv` or another batch's statement directly.
- **Files.** Proofs go to the batch's own files on `dev` (table above); the skeleton then
  replaces its `sorry` by the checked theorem.

Coupling, to keep in mind: the B and C statements are safety only. Batch D needs their functional
content as well (what recorded symbols mean for B; that an emitted block decodes to its symbols
for C). D will state these companion lemmas next to the safety lemmas before B or C reach them;
the owner who proves an execution is best placed to prove its companion. `completes` needs the
output size of every block (C) and the behaviour of every strategy across `Z_FINISH` calls (B),
so it is the least independent lemma; start it after `flush_block_spec` and the strategy lemmas.

Existing proof families, measured against the skeleton:

| Family | Decision |
| --- | --- |
| `deflate.c.engine.chains`, `lmbody`, `macros` and the slide and insertion lemmas | Already parametric (window 2^9 to 2^15, any hash parameters). Fit `fill_window_inv` and `longest_match_inserted`. Keep. |
| `deflate.c.engine.*` default, common and generic-foreign histories (`DefaultDataTrace`, `Common*DataTrace`, `EngineStart`) | Tied to window 15, `memLevel` 8, strategy 0 or to level 6. They cannot serve the universal lemmas. Delete once those lemmas are checked, except files that a registered theorem needs (about 60 registered engine theorems). |
| `deflate.c.init.*` | Fixed buffer sizes. The default proof is the template for `init2_main`; generalize. Keep the default modules that `deflateInit_proof` needs. |
| `trees.c.*` | Parametric in the block and its descriptors (`gen_codes`, `build_tree`, `scan_tree`, `build_bl_tree`, `send_tree`, `send_code` checked). Fit `flush_block_spec`; `send_all_trees`, `compress_block` and F9 remain. Keep. |
| `ZlibF/Math/Deflate*`, `Huffman*` | Heap-free: symbols and their meaning, block prefixes, overlay and budget bounds, Huffman depth bounds. Fit the ledger and F9. Keep. |

#### gz

Safety of the gzip file interface (result 5, owner's decision of 2026-11-12): no undefined
behaviour, no memory error, no leak of a block or of the descriptor, and termination, on every
history of a handle. The goal `Goal.gz_sequence_safety` and its definitions (`GzHistory`,
`GzCloseSafe`, `GzOpenSafe`, `GzDopenSafe`) are on `dev` in `ZlibF/Spec/Public/GzSafety.lean`
(`61fc2678`), over `GzInv` and `GzCallSafe` of `gz.inv-model`. The assembly is on `dev`:
`gz_sequence_safety_of` (`gz.sequence-safety`, `7d3c6b80`) has the conclusion `Goal.gz_sequence_safety`
and one premise, `GzReadLeaves`: the six open read leaves `gzread_step`, `gzfread_step`, `gzgetc_step`,
`gzungetc_step`, `gzgets_step`, `gzdirect_step`, each with the skeleton's exact statement. Every other
leaf is used from `dev` directly; no loop rule is used. The skeleton is on the branch `skeleton/gz`,
commit `17770416`, after a merge of `dev`: files `gz.skeleton-model.lean` (the two loop rules only),
`gz.skeleton-read.lean` (the open read leaves) and `gz.skeleton.lean` (`gz_sequence_safety_of` applied to
the read leaves). It type-checks: `Goal.gz_sequence_safety` is proved there from the open lemmas below. A skeleton leaf that `dev` proves with exactly its
statement is deleted from the skeleton (or closed by the `dev` theorem) and listed as checked.
The goal ranges over every open (`gzopen`, `gzopen64`, `gzdopen`), every public call of
`GzOperation`, every close, caller edits outside the handle and changes of the file-system world
between calls, for every value of the OS-call oracle.

A read leaf is open while `dev`'s theorem differs from the skeleton statement. The column
"Difference" names what differs, so that the read side can align the statement (a correction of
the skeleton statement, with evidence) or add an adapter lemma.

Statement corrections of `GzInv` against the skeleton text. Both make a clause weaker, because the
skeleton's clause was false; each has a checked regression. The no-fault and frame clauses of the goal
are unchanged.
- `GzCommon.next` constrains `x.next` only while output is buffered (`x.have ≠ 0`) (`7c32d275`;
  regression `tests/verification/regressions/gz-next-caller.c`, with patch 0005).
- `GzReadInv.copyDirect` allows `direct = 0 ∨ direct = 1` under `how = COPY` (`a351cd66`; regression
  `tests/verification/regressions/gz-copy-direct.c`).

| Lemma | Meaning | State | Hours | Owner |
| --- | --- | --- | ---: | --- |
| `GzInv.caller`, `GzInv.gz_error`, `GzInv.gz_reset`, `GzInv.put_scalars` | Interface lemmas of `GzInv`. | checked: `gz.inv-frame`, `gzlib.c.error-inv-premises`, `gz.inv-reset`, `gz.inv-put-scalars` | 0 | batch 1, deflate owner |
| `gwhile_partial`, `gdoWhile_partial` | Partial-correctness loop rules (`gz.skeleton-model`); no proof uses them yet. | open | 2 | unassigned |
| `gzopen_safe` | `gzopen` returns; NULL leaves nothing; a handle is in `GzInv` with only its descriptor new. | checked: `gzopen_safe` (`gz.inv-open-fresh`, `5252a412`) | 0 | batch C |
| `gzopen64_safe` | `gzopen64` is `gzopen`. | checked: `gzopen64_safe` (`gz.inv-open-fresh`, `5252a412`) | 0 | batch C |
| `gzdopen_safe` | As `gzopen_safe`, with no descriptor opened or closed. | checked: `gzdopen_safe` (`gz.inv-open`, `8c2bba51`) | 0 | batch C |
| `gzclose_dispatch_inv` | `gzclose` is `gzclose_r` or `gzclose_w` by mode. | checked: `gzclose_dispatch_inv` (`gz.inv-queries`) | 0 | batch 1 |
| `gzclose_step` | `gzclose` from the dispatch and the two close steps. | checked: `gzclose_step` (`gz.inv-close`, `fdb8c613`) | 0 | batch C |
| `gzseek64_step`, `gzseek_step` | Seek is safe on `GzInv`. | checked: `gzseek64_step`, `gzseek_step` (`gz.inv-seek`) | 0 | batch 1 |
| `gztell64_step`, `gztell_step`, `gzeof_step`, `gzbuffer_step` | Tell, eof and buffer; with `post_unchanged`, `safe_of_unchanged`. | checked: same names (`gz.inv-queries`) | 0 | batch 1 |
| `gzerror_step` | `gzerror` stores the code in the caller's cell. | checked: `gzerror_step` (`gz.inv-frame`) | 0 | batch 1 |
| `gzclearerr_step` | `gzclearerr` through `gz_error`. | checked: `gzclearerr_step` (`gz.inv-clearerr`) | 0 | batch 1 |
| `gzoffset64_step`, `gzoffset_step` | One `lseek` (M3); nothing else changes. | checked: same names (`gz.inv-offset-rewind`, `646b1ab6`) | 0 | batch C |
| `gzrewind_step` | `lseek` (M3) and `gz_reset`. | checked: `gzrewind_step` (`gz.inv-offset-rewind`, `646b1ab6`) | 0 | batch C |
| `history_inv`, `operation_safe`, `close_safe`, `gz_sequence_safety` | Assembly, re-checked under `dev`'s `GzInv` and `GzSafety`. | checked given hypotheses: `gz_sequence_safety_of` (`gz.sequence-safety`, `7d3c6b80`), premise `GzReadLeaves` (the six open read leaves below); `gz_sequence_safety` on the skeleton | 0 | batch C |
| `gz_init_safe`, `gz_comp_safe`, `gz_zero_safe`, `gz_write_safe`, `gz_vacate_safe` | Write-side helpers. | checked: same names (`gzwrite.c.safety`) | 0 | batch C |
| `gzwrite_step`, `gzfwrite_step`, `gzputc_step`, `gzputs_step`, `gzvprintf_step`, `gzprintf_step`, `gzflush_step`, `gzsetparams_step` | Write-side public calls. | checked: same names (`gzwrite.c.safety`) | 0 | batch C |
| `gzclose_w_step` | Finish, `deflateEnd`, frees, descriptor released. | checked: `gzclose_w_step` (`gzwrite.c.safety`, stated with `GzCloseSafe`) | 0 | batch C |
| `deflate_quiet` | `deflate` with no input stops (`DeflateQuiet`). Used by the write proofs on `dev` directly; no skeleton leaf is left. | checked: `Zlib.Deflate.Universal.Quiet.deflate_quiet_holds` | 0 | batch 3 |
| `gzclose_r_step` | `inflateEnd`, frees, descriptor released. | checked: `GzRead.gzclose_r_step_safe` (`gz.read-close`), the statement written out; `GzRead.Close.Released` is `GzReleased` by `rfl` | 0 | read side (deflate owner) |
| `gz_skip_have_safe` | Skip consumption of buffered bytes. | checked: `gz_skip_have_safe` (`gzread.c.skip-have`) | 0 | read side (deflate owner) |
| `gz_load_safe` | The `read` loop (M1). Difference: `GzRead.gz_load_safe` (`gz.read-load-error`) has the extra hypotheses `hm` (`mode = GZ_READ`), `hsz` (`size ≠ 0`), `hroot` (the buffer is a data buffer or not owned) and `heofin` (`eof ≠ 0 → avail_in = 0`), and a stronger conclusion. | open (align) | 1 | read side (deflate owner) |
| `gz_avail_safe` | Refill `in`. Difference: `GzRead.gz_avail_safe` (`gz.read-avail`) has the extra hypothesis `hm` (`mode = GZ_READ`), and a stronger conclusion. | open (align) | 0.5 | read side (deflate owner) |
| `gz_look_safe` | Lazy buffers, `inflateInit2`, COPY. Difference: `GzRead.gz_look_safe : GzLookSpec` takes `GzInvUpToOutput` (weaker than `GzInv`) and the premises `how = LOOK` and `MsgLit s`; its post is over `GzInvOut`, not `GzInv`. | open (align) | 2 | read side (deflate owner) |
| `gz_decomp_safe` | Inflate steps. Difference: `gz_decomp_safe_of` needs the premise `InflateHeadUsesInput`; `GzDecompSpec` adds the premises `MsgLit s` and `out.length ≠ 0`, replaces the separation premise (`out` not owned, or `out = s.out`), and terminates under `ReadsBounded`, not unconditionally. | open (align, one premise) | 3 | read side (deflate owner) |
| `gz_fetch_safe` | The dispatcher. Difference: `gz_fetch_safe_of` needs `GzLookSpec` and `GzDecompSpec`; `GzFetchSafe` takes `GzInvUpToOutput` and the premises `err ≠ Z_STREAM_END`, `how = COPY → avail_in = 0`, `MsgLit s`; post over `GzInvOut`; termination under `ReadsBounded`, not `ReadsFinite`. | open (align, callee premises) | 2 | read side (deflate owner) |
| `gz_skip_safe` | The skip loop. Difference: `gz_skip_safe_of` needs `GzFetchSpec`, `GzFetchProgress` (and `GzErrorSpec`, `GzErrorOwn`, proved); it takes `GzInvUpToSkip` (weaker than `GzInv`). | open (callee premises) | 1 | read side (deflate owner) |
| `gz_read_safe` | Three paths, caller range, `x.pos` (F-1). No `dev` theorem. | open | 12 | read side (deflate owner) |
| `gzread_step`, `gzfread_step` | Wrappers of `gz_read`. No `dev` theorem. | open | 4 | read side (deflate owner) |
| `gzgetc_step` (`gzgetc__step` from it) | One byte. Difference: `GetcUngetc.gzgetc_step_of` needs the premise `GzReadSpec`. | open (callee premise) | 1 | read side (deflate owner) |
| `gzungetc_step` | Push back inside `out`. Difference: `GetcUngetc.gzungetc_step_of` needs `GzLookSpec'` and `GzSkipSpec'`. | open (callee premises) | 1 | read side (deflate owner) |
| `gzgets_step` | Bounded `memchr`, copy, NUL. No `dev` theorem. | open | 6 | read side (deflate owner) |
| `gzdirect_step` | One `gz_look` and `gz_skip_have`. No `dev` theorem. | open | 3 | read side (deflate owner) |
| Merge the `deflate.c.quiet-*` restated copies | Cleanup, not on the critical path. | open | 4 | later |
| **Total remaining** | batch C 0; read side 36.5; unassigned 2 | | **38.5** | |


### No-fault coverage of zlib.h functions

One row for each function that zlib.h documents. Each row names the checked theorem that shows the
call does not fault, and the route: its own goal, a sequence goal (the call is a `StreamOperation`),
the End clause of `StreamSequenceSafety`, or open. Snapshot of `dev` at `10bd366a`, 2026-11-13.
"Registered" means listed in `tests/audit/theorems.txt`, so an acceptance candidate, not accepted.
Re-check a row when its theorem or goal changes.

Model-wide premises that every stream or utility route shares, which are not repeated per row:
the default allocator (`DefaultOrNull`/`DefAlloc`/`zfree = zcfree`; a declared target
restriction), heap well-formedness (`Fresh`, `Uniq`, `LibraryGlobals`), and, for inflate, the
utilities and inflateBack, `ByteObjectsFit` (the platform row in `docs/deviations.md`).

Abbreviations:
- **SeqI** = `Goal.inflate_sequence_safety`: `Zlib.Inflate.Proofs.inflate_sequence_safety_public`
  (`public-inflate-sequence-safety.lean`, registered).
- **SeqD** = `Goal.deflate_sequence_safety`: `Zlib.Deflate.Universal.deflate_sequence_safety`
  (`public-deflate-goals.lean`, registered).
- Both cover only `p = some r` with `StreamReachable r` (and `StreamArguments`). Neither covers a
  NULL stream or an inconsistent stream (zalloc/zfree NULL, state NULL, or a state the check
  refuses). zlib.h documents those as `Z_STREAM_ERROR` refusals, and `docs/spec/safety.md` A1
  keeps documented null refusals in scope. The column "refusal" says whether any theorem
  covers that case.

#### Stream: deflate

| function | route | theorem (Lean name, file) | registered? | domain gap or note |
| --- | --- | --- | --- | --- |
| deflateInit_ (macro deflateInit) | own goal | `ZlibF.Spec.Public.Proofs.DeflateInit.deflateInit_proof`, `public-deflate-init.lean` | yes | Full: bad version (`VersionValue`, NULL or a readable first byte), wrong `stream_size` (any `p`), NULL strm, every level, allocation failures. |
| deflateInit2_ (macro deflateInit2) | own goal | `ZlibF.Spec.Public.Proofs.DeflateInit2.deflateInit2_proof`, `public-deflate-init2.lean` | yes | Full, as for deflateInit_, plus every method/windowBits/memLevel/strategy. `Goal.deflate_initialisation_domain` (nonvacuity) has no theorem. |
| deflate | own goal + SeqD | `Zlib.Deflate.Universal.deflate_safety`, `public-deflate-goals.lean` | yes | Reachable + `DGood` + `StreamBuffers` + `ActiveHeader` (separation rows). Refusal: `Goal.deflate_refusal` (checked) covers NULL and inconsistent streams. |
| deflateEnd | own goal + End clause of SeqD | `ZlibF.Spec.Public.DeflateEndProof.deflate_end_public`, `public-deflate-end.lean`; clause 3 of SeqD | yes | Own goal needs `DGood`. Refusal: `Zlib.Deflate.Proofs.deflateEnd_reject` (`deflate.c.life.end.lean`, registered) covers NULL, zalloc/zfree NULL, state NULL and a refused live state. So it is covered: never initialised (model pointers are NULL), NULL, state NULL, and after a failed copy. It is not a goal-typed theorem. |
| deflateSetDictionary | SeqD | SeqD | yes | Own `Goal.deflateSetDictionary`: no theorem. Refusal: `Goal.deflate_refusal` (checked) covers NULL and inconsistent streams. |
| deflateGetDictionary | own goal + SeqD | `ZlibF.Spec.Public.DeflateDictionaryProof.deflate_getdict_public`, `public-deflate-getdict.lean` | yes | Own goal needs `DGood` and a destination separate from the window. Refusal: `Zlib.Deflate.Proofs.deflateGetDictionary_reject` (`deflate.c.life.getdict.lean`) is checked but **not registered**. |
| deflateCopy | own goal | `Zlib.Deflate.Universal.deflate_copy_public` / `deflate_copy_safety`, `public-deflate-copy.lean` | yes | Not a `StreamOperation`; `StreamReachable.deflateCopy` only feeds clause 1 of SeqD. Gap: `source ≠ dest` (deviation row). An inconsistent source is covered by `Goal.deflate_refusal` (checked). |
| deflateReset | own goal + SeqD | `ZlibF.Spec.Public.DeflateResetProof.deflate_reset_public`, `public-deflate-reset.lean` | yes | Refusal: `Zlib.Deflate.Proofs.deflateReset_reject` (registered). |
| deflateParams | SeqD | SeqD | yes | Own `Goal.deflateParams`: no theorem. Refusal: `Goal.deflate_refusal` (checked) covers NULL and inconsistent streams. |
| deflateTune | own goal + SeqD | `ZlibF.Spec.Public.DeflateQueryProof.tune_public`, `public-deflate-small-queries.lean` | yes | Full (`CheckedDeflate` includes the refusals). |
| deflateBound | SeqD | SeqD | yes | Own `Goal.deflateBound`: no theorem. SeqD needs `ActiveHeader ∧ DeflateHeaderLive`. Refusal: `deflateBound_nostate` (registered). |
| deflateBound_z | SeqD | SeqD | yes | Same as deflateBound (`deflateBound_z_nostate`, registered). |
| deflatePending | own goal + SeqD | `ZlibF.Spec.Public.DeflateQueryProof.pending_public` | yes | Full. |
| deflateUsed | own goal + SeqD | `ZlibF.Spec.Public.DeflateQueryProof.used_public` | yes | Full. |
| deflatePrime | SeqD | SeqD | yes | Own `Goal.deflatePrime`: no theorem. SeqD needs `DeflateNotStarted`, which is zlib.h's own ordering rule. Refusal: `deflatePrime_refused` (registered). |
| deflateSetHeader | own goal + SeqD | `ZlibF.Spec.Public.DeflateQueryProof.header_public` | yes | Full. SeqD needs `DeflateNotStarted` (zlib.h order). |

#### Stream: inflate

| function | route | theorem (Lean name, file) | registered? | domain gap or note |
| --- | --- | --- | --- | --- |
| inflateInit_ (macro inflateInit) | own goal | `ZlibF.Spec.Public.Proofs.InflateInit.init15_public`, `public-inflate-init.lean` | yes | Full: bad version or size, NULL strm, allocation failure. |
| inflateInit2_ (macro inflateInit2) | own goal | `ZlibF.Spec.Public.Proofs.InflateInit.inflate_init2_public`, `public-inflate-init2.lean` | yes | Full, every `windowBits`. |
| inflate | own goal + SeqI | `Zlib.Inflate.Proofs.inflate_public`, `public-inflate.lean` | yes | Reachable + `Good` + `ByteObjectsFit` + `StreamBuffers` + `ActiveHeader`. Refusal: `Goal.inflate_refusal` (checked) covers NULL and inconsistent streams. |
| inflateEnd | own goal + End clause of SeqI | `ZlibF.Spec.Public.InflateEndProof.inflate_end_public`, `public-inflate-end.lean`; clause 3 of SeqI | yes | Own goal needs `Good`. Refusal: `Goal.inflate_refusal` (checked) covers NULL and inconsistent streams. |
| inflateSetDictionary | own goal + SeqI | `ZlibF.Spec.Public.Proofs.inflateSetDictionary_public`, `public-inflate-setdict.lean` | yes | Own goal needs `Good`, `zalloc = zcalloc`, and a dictionary separate from the window (deviation row). Refusal: `Goal.inflate_refusal` (checked) covers NULL and inconsistent streams. |
| inflateGetDictionary | own goal + SeqI | `ZlibF.Spec.Public.InflateDictionaryProof.inflate_getdict_public` | yes | Own goal needs `Good` and a destination separate from the window. Refusal: `Goal.inflate_refusal` (checked) covers NULL and inconsistent streams. |
| inflateSync | SeqI | SeqI | yes | Own `Goal.inflateSync`: no theorem. Refusal: `inflateSync_check` (registered). |
| inflateCopy | own goal | `Zlib.Inflate.Proofs.inflate_copy_public`, `public-inflate-copy.lean` | yes | Not a `StreamOperation`. Gap: `source ≠ dest` (deviation row). An inconsistent source is covered by `Goal.inflate_refusal` (checked). |
| inflateReset | own goal + SeqI | `ZlibF.Spec.Public.InflateResetProof.reset_public` | yes | Own goal needs `InflateView`. Refusal: `Goal.inflate_refusal` (checked) covers NULL and inconsistent streams. |
| inflateReset2 | own goal + SeqI | `ZlibF.Spec.Public.InflateReset2Proof.reset2_public` | yes | Every `windowBits`. Refusal: `Goal.inflate_refusal` (checked) covers NULL and inconsistent streams. |
| inflatePrime | own goal + SeqI | `ZlibF.Spec.Public.InflatePrimeProof.prime_public` | yes | Full (`CheckedInflate`). The accepted branch needs `s.bits ≤ 39`, a fact of the invariant. |
| inflateMark | own goal + SeqI | `ZlibF.Spec.Public.InflateMarkProof.mark_public` | yes | Full. |
| inflateGetHeader | own goal + SeqI | `ZlibF.Spec.Public.InflateHeaderProof.getheader_public` | yes | Full on `InflateView`. A gzip-capable stream needs `head ≠ NULL`: C dereferences it, and zlib.h does not offer NULL. SeqI also needs `p ≠ none`. Refusal: `inflateGetHeader_check` (registered). |

#### Callback decoder

| function | route | theorem (Lean name, file) | registered? | domain gap or note |
| --- | --- | --- | --- | --- |
| inflateBackInit_ (macro inflateBackInit) | own goal | `ZlibF.Spec.Public.InflateBackInitProof.back_init_public`, `public-infback-init.lean` | yes | Full: bad version or size, NULL strm, NULL window, bad `windowBits`, allocation failure. The success branch needs a writable window of `2^wb` bytes (zlib.h's own rule). |
| inflateBack | sequence (`Goal.inflate_back_sequence_safety`) | **none unconditional**. Only `inflate_back_sequence_safety_of (fast : FastOk)`, `infback.c.safety-reach.lean` | no | **Open**: `LEN_fast_p` and `fast_alias` are open (progress.md, about 15 h). Own `Goal.inflateBack` (functional) is not planned. NULL strm and state NULL are covered (`inflateBack_nullstream`, `inflateBack_nostate`, registered). The goal also narrows: `inputBound < 2^48`, the window is a slice of a heap byte block, every input chunk lies in a heap byte block (deviation rows). |
| inflateBackEnd | own goal | `ZlibF.Spec.Public.InflateBackEndProof.back_end_public`, `public-infback-end.lean` | yes | Full: NULL, state NULL or zfree NULL, and `BackValid`. Clause 4 of the inflateBack sequence goal is also proved inside the conditional theorem only. |

#### Checksums

| function | route | theorem | registered? | domain gap or note |
| --- | --- | --- | --- | --- |
| adler32 | own goal | `ZlibF.Spec.Public.AdlerUpdateProof.adler_public`, `public-adler-update.lean` | yes | **Narrower**: NULL `buf` only with `len = 0` (`AdlerBufferBytes`, deviation row). With `len = 1`, C reads `buf[0]`, a real fault (upstream PR #1364 was closed and a zlib.h restriction was announced). NULL with `len ≥ 2` is safe in C but unproved. |
| adler32_z | own goal | `...AdlerUpdateProof.adler_z_public` | yes | Same as adler32. |
| adler32_combine / _combine64 | own goal | `...AdlerCombineProof.combine_public` / `combine64_public` | yes | Full. |
| crc32 / crc32_z | own goal | `ZlibF.Spec.Public.Proofs.crc32` / `crc32_z`, `public-crc-updates.lean` | yes | Full (`BufferBytes` includes NULL with any length). `CrcGlobals` is a premise of the model's static data. |
| crc32_combine / _combine64 | own goal | `...CrcCombineProof.combine` / `combine64` | yes | Full. |
| crc32_combine_gen / _gen64 | own goal | `...CrcCombineProof.gen` / `gen64` | yes | Full. |
| crc32_combine_op | own goal | `...CrcCombineProof.op` | yes | `op` must come from `crc32_combine_gen` (matches zlib.h). |
| get_crc_table | own goal | `ZlibF.Spec.Public.Proofs.get_crc_table` | yes | Undocumented in zlib.h (not required). |

#### Utilities

| function | route | theorem | registered? | domain gap or note |
| --- | --- | --- | --- | --- |
| compress / compress_z / compress2 / compress2_z | safety goals `Goal.compress*_safety` | `ZlibF.Spec.Public.Proofs.Compress.compress_safety`, `compress_z_safety`, `compress2_safety`, `compress2_z_safety`, `public-compress-safe-mid.lean` | yes | Source separate from dest (deviation row). The length cell is modelled as an `Option` scalar, so aliasing the cell with data is outside the model (deviation row). Every level. The functional `Goal.compress*` (not planned) have no theorem. |
| uncompress / uncompress_z / uncompress2 / uncompress2_z | safety goals `Goal.uncompress*_safe` | `ZlibF.Spec.Public.Proofs.Uncompress.uncompress_safe` etc., `public-uncompress-safe.lean` | yes | `UtilitySeparation`: data and length cells pairwise separate (deviation row). The functional `Goal.uncompress*` (not planned) have no theorem. |
| compressBound / compressBound_z | own goal | `ZlibF.Spec.Public.Proofs.compressBound` / `compressBound_z` | yes | Full. |
| zlibVersion | own goal | `ZlibF.Spec.Public.Proofs.zlibVersion` | yes | Full. |
| zlibCompileFlags | own goal | `ZlibF.Spec.Public.Proofs.zlibCompileFlags` | yes | Full. |
| zError | own goal | `ZlibF.Spec.Public.Proofs.zError` | yes | Undocumented (not required). |

#### Gzip file interface

There is **no registered gz safety goal on dev**. `Goal.gz_sequence_safety` is defined on `dev` in
`ZlibF/Spec/Public/GzSafety.lean` (`61fc2678`) and proved only on branch `skeleton/gz`, from open
lemmas. It is in neither `goals.txt` nor `public-api.json` `safety_goals`. `Goal.gz_sequence` (functional) is not planned and has no
theorem. The registered own-goal theorems below are functional contracts over `GzValid`,
`GzReachable` or a live `gzstates` entry, and some over `RegularOs fs` (the deterministic
regular-file world, not every OS-call oracle world).

| function | route | theorem | registered? | domain gap or note |
| --- | --- | --- | --- | --- |
| gzopen, gzopen64 | open | none (`gzopen_null`, `gzopen*_alloc_failure` registered) | partial only | Path-open branch is open. |
| gzdopen | own goal | `Zlib.Gzlib.Proofs.gzdopen_complete`, `gzlib.c.dopen-complete.lean` | yes | Every `fd`. Mode is NULL or a C string. Not shown for every oracle world. |
| gzbuffer | own goal | `ZlibF.Spec.Public.Proofs.gzbuffer_public` | yes | NULL and any live handle. |
| gzeof | own goal | `ZlibF.Spec.Public.Proofs.gzeof_public` | yes | NULL and any live handle. |
| gzerror | own goal | `ZlibF.Spec.Public.GzErrorProof.gzerror` | yes | Needs `GzValid`. That invariant is not yet derived for every history (only gzdopen establishes it). |
| gzclearerr | own goal | `ZlibF.Spec.Public.Proofs.gzclearerr` | yes | Needs `GzValid` (same remark). |
| gzoffset, gzoffset64 | own goal | `ZlibF.Spec.Public.OffsetProof.gzoffset_public_goal` / `gzoffset64_public_goal` | yes | Needs `GzReachable`, `GzValid` and `RegularOs fs` (deviation row "Gz file data"). |
| gzrewind | own goal | `ZlibF.Spec.Public.GzRewindProof.rewind_public` | yes | Needs `GzReachable`, `GzValid` and `RegularOs fs`. |
| gzseek, gzseek64 | open | pieces: `gzseek64_safe` (needs `GzGood`, `PosInv`, ...) registered; `gzseek64_step` checked (`gz.inv-seek`) | partial only | |
| gztell, gztell64 | open | `gztell64_spec` registered, but needs `PosInv`, which no history theorem derives | partial only | |
| gzclose | open | `gzclose_null`, `gzclose_dispatch` registered | partial only | |
| gzclose_r | open | `gzclose_r_step_safe` (`gz.read-close.lean`, over `GzInv`), checked, unregistered | no | `GzInv` is not derived from histories. |
| gzclose_w | open | none | no | |
| gzread, gzfread, gzgetc, gzgetc_, gzungetc, gzgets, gzdirect | open | none at public level (internal `gz_look_safe`, `gz_fetch_safe_of`, `gzungetc_step_of` checked) | no | The `gzgetc` macro's inline path (reads `have`, `next`, `pos`) is not translated. It needs a handle invariant (**to confirm**). |
| gzwrite, gzfwrite, gzputc, gzputs, gzprintf, gzflush, gzsetparams | open | none at public level | no | |

#### Miscounts and open items

Documented functions with no checked no-fault theorem for their full documented domain:

1. **inflateBack**: open. Only `inflate_back_sequence_safety_of (FastOk)`; `LEN_fast_p` and `fast_alias` are open. progress.md also lists the target row as "Not proved".
2. **deflateCopy**: registered. `source ≠ dest` is assumed (deviation row).
3. **inflateEnd**: closed. NULL, state NULL, after `End`, after a failed init and the destination of a failed copy are covered by `Goal.inflate_refusal` (checked).
4. **inflateCopy**: closed. An inconsistent source is covered by `Goal.inflate_refusal` (checked).
5. **NULL or inconsistent stream refusal**: closed. `Goal.inflate_refusal` and `Goal.deflate_refusal` (checked) cover `inflate`, `deflate`, `inflateEnd`, `inflateReset`, `inflateReset2`, `inflateGetDictionary`, `inflateSetDictionary`, `inflateCopy`, `deflateSetDictionary`, `deflateParams`, `deflateGetDictionary` and `deflateCopy`. These goals and `deflateGetDictionary_reject` are registered.
6. **deflateParams, deflateSetDictionary, deflatePrime, deflateBound, deflateBound_z, inflateSync**: no own-goal theorem. No-fault on reachable streams comes only through SeqI or SeqD. That suffices for planned safety, but per-call own goals stay open.
7. **adler32, adler32_z**: domain narrower than zlib.h (NULL only with `len = 0`). `len = 1` is a real C fault (deviation row). NULL with `len ≥ 2` is safe but unproved.
8. **Every gz function except** gzdopen, gzbuffer, gzeof, gzerror, gzclearerr, gzoffset(64), gzrewind: open (gzopen, gzopen64, gzclose, gzclose_r, gzclose_w, gzread, gzfread, gzgetc, gzgetc_, gzungetc, gzgets, gzdirect, gzwrite, gzfwrite, gzputc, gzputs, gzprintf, gzflush, gzsetparams, gzseek, gzseek64, gztell, gztell64). The registered gz theorems rest on `GzValid` or `GzReachable` (and `RegularOs` for gzoffset and gzrewind), not on every history and every oracle world. No gz safety goal is registered on dev (`Goal.gz_sequence_safety` is defined in `GzSafety.lean` and proved only on `skeleton/gz`).
9. Related, not a function: `Goal.deflate_initialisation_domain` (nonvacuity) has no theorem.

### Ordered next work

Rows 9 to 12 are planned work: see [Scope](#scope). Start with row 11, then rows 9 and 12.
Rows 1 to 5 and 13 are the gzip file interface: their safety is planned (result 5) and follows
the [gz skeleton](#gz), not this table; their functional contracts are not planned. Rows 6 to 8 and 10 are done
only when a sequence goal needs them.

Ordered. "Prerequisite" is what must be proved first; it is never an assumed contract.
"Owner PR" is the pull request that carries the work once one exists.

| # | Target | Prerequisite | Owner PR |
| ---: | --- | --- | --- |
| 1 | `gzopen`, `gzopen64`, `gz_initialisation_domain` | Statement corrected (see [gzip open path length](#gzip-open-path-length)). Next: the path-open (`fd = -1`) branch of `gz_open`: `fsOpen` outcomes and the append/read seeks, reusing the `gzdopen` composition | — |
| 2 | `gztell`, `gztell64` | `PosInv` from every permitted gz history (open, read, write, seek, pushback) | — |
| 3 | `gzclose_r` | Reader buffer ownership over histories, then `inflateEnd` on an initialized reader | — |
| 4 | `gzseek`, `gzseek64` | `PosInv` and buffer invariants from item 2; transparent and buffered paths | — |
| 5 | Transparent paths of `gzread`, `gzfread`, `gzgetc`, `gzgetc_`, `gzgets`, `gzungetc`, `gzdirect`, `gzwrite`, `gzfwrite`, `gzputc`, `gzputs`, `gzprintf`, `gzvprintf`, `gzflush`, `gzsetparams` | Lazy setup and buffer invariants; compressed paths wait for items 12–13 | — |
| 6 | `deflatePrime` | Pending-byte compaction and bit insertion under `DGood` | — |
| 7 | `deflateBound`, `deflateBound_z` | Execution formulas against the saturated bound, including header strings | — |
| 8 | `deflateSetDictionary` | Window fill, hash insertion and input restoration under `DGood` | — |
| 9 | `deflateInit2_`, `deflate_initialisation_domain` | Parameter normalization, five allocations, cleanup, `DGood` establishment for every parameter tuple | — |
| 10 | `inflateCopy`, `deflateCopy` | Allocation failures, buffer copies, pointer relocation, independent ownership | — |
| 11 | `inflate` → `inflate_sequence` → `inflateSync`, `uncompress*`, `inflateBack`, `inflate_back_sequence` | Table meaning from actual `inflate_table`; one dispatch-loop invariant over every mode | — |
| 12 | `deflate` → `deflate_sequence` → `deflateParams`, `compress*` | `fill_window`/sliding; one strategy-loop invariant parametric in level, `memLevel`, `windowBits`; block emission | — |
| 13 | Compressed gz paths, `gzclose_w`, `gzclose`, `gz_sequence` | Items 11 and 12 | — |

Statement corrections come first when they change what must be proved. Open:
`Api.Goal.inflate_rejects_invalid`, which rests on `detectLag = 8` (a checked counterexample shows
the constant is wrong; [API model](design/api-model.md)). The gzip open path length question below is corrected.
`inflateInit2_` and `Api.Goal.gz_seek_read` are corrected and checked; they await registration.

Earlier narrative checkpoints (per-area notes on inflate, deflate, trees, CRC, the harness and
integration) are kept in [progress checkpoints](history/progress-checkpoints.md). They are
historical; the counts in them are not current.

### Public API proof readiness

**Gray means unproved, not blocked. Start independent work now.** Green callees do not
establish the caller's own preconditions, loops, results or memory effects. A directly
callable API can still have a false contract or a confirmed source defect; only evidence
of that kind warrants a blocker border. Do not infer readiness solely from missing arrows.

The [evidence index](progress.md) separates proof references, C calls and specification
references. The work below names composition obligations, **to confirm** against
the exact targets. It does not introduce public assumptions or grant input coverage.

##### deflate, batch B: positional hash chains (stopped, 2026-11-12)

The work aimed to remove the exclusion of a direct `deflateResetKeep` (`docs/deviations.md`) with a
positional hash-chain invariant. It stopped by the owner's decision: the real C reads outside the
window on such a history (`docs/findings/deflate-copy-pending-prev`): `deflateResetKeep` and
`deflate(Z_BLOCK)` leave two chain heads waiting for insertion, `deflateCopy` copies `prev` only below
the frontier, and a `Z_RLE` or `Z_HUFFMAN_ONLY` flush on the copy ends with `insert = 0`, so
`longest_match` later follows an uninitialised slot. So no invariant that admits a direct
`deflateResetKeep` can hold. `DInv` stays exact and the exclusion stays. There is no zlib patch: the bug
does not block the proof of the proved domain.

What stays on `dev` (slice 1, cc359062, checked): `PosChains`/`ReachS` with insertion, slide and the walk
of `longest_match` (`deflate.c.engine.pos-chains`), the safety-only `longest_match_safe` (no byte
agreement; termination by `chain_length`, `deflate.c.engine.lm-safe`, `-lm-pos`), `insert_string_pos` and the
pending insertion of `fill_window` on the positional chains (`-insert-pos`, `-fill-insert-pos`). Nothing on
the safety path uses them. The branch `worker/poschains` (invariant, `fill_window`, flush and rebuffer
switched; strategies not) is closed by the deflate owner and not merged; the positional generalisation
is now batch B's (2026-11-12), in slices that keep `dev` building, with the exact chains as corollaries.
`worker/slid-chaintop` is closed: its content is on `dev` (`SlidChains` at `chainTop`). A second reason
the first positional branch could not have closed as planned: the
positional invariant gives no step for the `insert = 0` at the end of `deflate_huff` and `deflate_rle`,
which the exact invariant gets from its frontier `chainTop`.

Checked with the finding: no chain head waits for insertion in the proved domain
(`DInv.heads_inserted`, `DInv.slid_heads_inserted`, `deflate.c.universal-heads`).

#### Open, query and close prerequisites

Opening a file does not require the complete engine. Its main work is the common `gz_open`
mode loop, real allocations, string copying, descriptor effects and invariant establishment.
For a tell query, the missing producer is the position invariant over permitted histories.
For close, it is ownership over those histories, including allocation failures.

Local execution proofs now cover:

- [Open entries](../ZlibF/Proof/gzlib.c.open.lean): NULL arguments, negative descriptors
  and first-allocation failure. They give the unchanged file system and exact heap,
  including the allocation-attempt counter.
- [Reader close](../ZlibF/Proof/gzread.c.close.lean): NULL, wrong mode and complete
  unbuffered execution under `GzGood`, including descriptor errors, freeing the message,
  path and handle, and a frame over unrelated allocations.
- [Priming entry](../ZlibF/Proof/deflate.c.prime.lean): refused streams and invalid bit
  counts, before pending-byte compaction.

These are scoped internal results, not proofs of the complete public targets. In particular,
`GzGood` still has to be derived from the permitted public histories. Do not replace a gray
public node with green on the strength of one branch.

#### inflateBack

Safety of the callback decoder (owner's request of 2026-11-12): `Goal.inflate_back_sequence_safety`
(`ZlibF/Spec/Public/Sequences.lean`), stated beside the unchanged `Goal.inflate_back_sequence`. The
call-backs are the goal's `CallbackProtocol`: arbitrary caller code that returns, changes only its
own blocks and the window slice it must keep, hands out readable input outside the window, and
offers a finite total input (`inputBound`). The goal adds `inputBound < 2^48` (loop fuel;
`docs/deviations.md`). Statement test: `tests/goals/infback-callbacks` (ASan/UBSan, 30000 cases,
no report). Skeleton: branch `skeleton/inflate-back`, `ZlibF/Proof/infback.c.safety-skeleton.lean`
(type-checks; lemma proofs open). The earlier internal contract `CbContract` is narrower than the
protocol, so the call-back lemmas are restated over `PInv`; their bit algebra is reused.
Issue (not planned, functional goal): `Goal.inflateBack` has no bound on `inputBound`, so a
protocol whose input exceeds the loop fuel makes it false in the model.
Needed invariant: `inflate_fast` assumes `state->bits < 8` on entry. `inflate.c` checks it before the
fast path (upstream e7bb978); `infback.c` does not, so the proof shows that fewer than 8 bits are
held when a round starts in `TYPE`, `TABLE` or `LEN` (row `BitsShort`). With 8 or more bits held,
`inflate_fast` could move `next` back before the chunk `in` gave. Evidence:
`tests/goals/infback-callbacks/bits8.sh` (60000 cases, no trap).
Goal corrections (46ce3a0a, 200f80e1): the histories are `BackSafeReachable`. The window is a
slice of a heap byte block; every byte object has fewer than `2^63` bytes on the heap of a call
and after each call-back step (`BackPlatform`); every input chunk lies in a heap byte block
(`BackFirstChunk`, `BackPlatform`); a caller edit between calls keeps the read-only flag of a live
block. Deviation rows: "Callback decoder window", "Callback decoder input chunks", the platform
row and "Callbacks". Candidate generalisation, not planned now: an input chunk at any byte reference
(a caller's structure field, static data) for both decoders together, `inflate` and `inflateBack`;
both rest on `inflate_fast`, whose entry takes a raw byte block.
Composition (6f9575e7): `inflate_back_sequence_safety_of` proves the goal from `FastOk`, the fast
path of `case LEN` on the invariant; `LEN_fast_p` and `fast_alias` are what is left.

| Lemma | Meaning | State | Hours |
| --- | --- | --- | ---: |
| `PInv` frames | The loop invariant over the caller protocol: `CallbackFrame` and the live set compose across call-back calls and library writes; `PInv` survives a state or register write | checked (dd5f9e1e) | 0 |
| `PULL_p` | `PULL()`: `in` only on an empty chunk; the protocol's `inStep` gives the chunk and the log entry; `Z_BUF_ERROR` on 0 | checked (dd5f9e1e) | 0 |
| `PULLBYTE_p`, `NEEDBITS_p` | One byte into `hold`, and `NEEDBITS(k)` for `k ≤ 32` (bit algebra of `inflate.c.main.macros`) | checked (52ae3999) | 0 |
| `ROOM_p` | `ROOM()`: `out` on the full window (`outStep`), `whave = wsize`, restart at the window; `Z_BUF_ERROR` on refusal | checked (7971d171) | 0 |
| `TYPE_p` | `case TYPE`: last flag and block type, `DONE` after the last block | checked (472c8a15) | 0 |
| `STORED_p` | `case STORED`: length check and the copy through `PULL` and `ROOM`; the chunk may share the window's block | checked (eec477cd) | 0 |
| `TABLE_p` | `case TABLE`: header, code-length code, decoded lengths, three `inflate_table` calls, tables installed (`TablesOk`, with the decode invariant and query stability), and the fall-through into `LEN` | checked (650c8931) | 0 |
| `BitsShort` | Fewer than 8 bits held at the start of a round in `TYPE`, `TABLE`, `LEN` (`Short` in `Round`): lookups with pull witnesses, `consumed_gt` from `StableQuery` and `PrefixQuery`, the code-length decoding of `TABLE` by `CodeLengthContents` | checked (57c7fabd, 9e93b576) | 0 |
| `fast_alias` | `inflate_fast` with the output inside the window block (`wnext = 0`): `Env.hwin` of `Goal.fast_safe` asks for a separate window block; plan: allow the output block with `wnext = 0` and copy through `Src.out` (`cpyG`), the exact-content lemmas keeping the separate case | open | 12 |
| `LEN_slow_p` | `case LEN` without the fast path: literal, end of block, length/distance with the distance check and the copy through `ROOM`, invalid codes | checked (06e4a17d) | 0 |
| `LEN_fast_p` | `case LEN` with the fast path: `RESTORE`, `fast_alias`, `LOAD` | open | 3 |
| `dispatch_p` | One round of the dispatch: every mode reachable from `PInv`; the measure falls or the call leaves with one of three results; the fast path is the premise `LenFast` until `LEN_fast_p` | checked (650c8931) | 0 |
| `loop_p` | The dispatch loop ends within the fuel (`backMeasure < 2^64` from `inputBound < 2^48`) | checked (650c8931) | 0 |
| `back_call` | One call: prologue, `loop_p`, epilogue (the last partial window to `out`, `next_in`, `avail_in`): `back_call_partial` (a call that returns, any input) and `back_call_total` (input below `2^48`) | checked (3a2a8753, f91f401d) | 0 |
| `back_null`, `back_end` | Null stream; `inflateBackEnd` on a reachable history (`back_end_public`) | checked (6f9575e7) | 0 |
| `back_reach_valid` | Every reachable history leaves a valid state over the caller's window (init, rebuffer, `back_call_partial` with the loop rule without a measure) | checked (6f9575e7) | 0 |
| **Total** | | | **15** |

#### Next work for every unfinished public target

"Start" means work can begin without a complete engine theorem. "Compose" names a
prerequisite for full closure; independent branches can still proceed. No row grants
checked status or assumes a callee's specification.

<!-- proof-readiness:start -->
| Public targets | Proof work shown in graph | Next work and missing prerequisite |
| --- | --- | --- |
| `gzopen`, `gzopen64`, `gz_initialisation_domain`  | Start: open and cleanup | <a id="readiness-gzopen"></a> **Statement corrected:** see [gzip open path length](#gzip-open-path-length). **Start:** the path-open branch of `gz_open` (`fsOpen` outcomes, append and read seeks), reusing the registered `gzdopen` mode loop, allocation and `OpenState` composition. Entry/failure branches are locally checked above. |
| `gztell64`, `gztell`  | Needs: position history | <a id="readiness-gztell64"></a> **Compose:** derive `PosInv` from reads, writes, seeking and pushback; then reuse the existing arithmetic execution proof. |
| `gzclose_r`  | Needs: resource history | <a id="readiness-gzclose-r"></a> **Start:** initialized-buffer cleanup and its ownership producer over histories. Unbuffered execution and frame are locally checked; `inflateEnd` alone is insufficient. |
| `gzclose_w`, `gzclose`  | Needs: flush and cleanup | <a id="readiness-gzclose-w"></a> **Compose:** actual zero-fill/final compression and file writes, all cleanup/error paths, then dispatch using both complete close results. |
| `gzseek64`, `gzseek`  | Needs: seek and history | <a id="readiness-gzseek64"></a> **Start:** position/pointer history invariants, buffered and transparent paths, exact error frames. Negative-position reachability and historical overflow reports remain **to confirm**. |
| `gzdirect`, `gzread`, `gzfread`, `gzgetc`, `gzgetc_`, `gzgets`, `gzungetc`  | Needs: reader path proofs | <a id="readiness-gzdirect"></a> **Start:** common lazy setup, transparent reads and buffer/history invariants. **Compose:** actual decoder execution for compressed paths, then EOF/count/pushback/error clauses. `gzdirect` needs detection and init, not the full data-decoding loop. |
| `gzwrite`, `gzfwrite`, `gzputc`, `gzputs`, `gzvprintf`, `gzprintf`, `gzflush`, `gzsetparams`  | Needs: writer path proofs | <a id="readiness-gzwrite"></a> **Start:** buffering, formatting, transparent writes and failures. **Compose:** actual compressor execution for compressed output and parameter changes. |
| `deflateInit2_`, `deflate_initialisation_domain`  | Start: init and allocation | <a id="readiness-deflateinit2"></a> **Start:** parameter normalization, five allocations, all failure cleanup, actual `DGood`/tree establishment and witnesses. Reset proofs require the invariant; they do not establish it for fresh storage. |
| `deflatePrime`  | Start: compaction and bits | <a id="readiness-deflateprime"></a> **Start:** pending-byte compaction, checked shifts, bit insertion/flush and invariant/frame preservation. Refusal branches are locally checked; accepted counts remain open. |
| `deflateBound_z`, `deflateBound`  | Start: bound and header review | <a id="readiness-deflatebound-z"></a> **Start:** connect existing execution formulas to the saturated mathematical bound, including header strings and extra lengths. The historical extra-length report is **to confirm**, not a newly confirmed blocker. |
| `deflateSetDictionary`  | Start: window and hash | <a id="readiness-deflatesetdictionary"></a> **Start:** window fill, hash-chain insertion, saved-input restoration, then checksum and exact state/frame effects. Green checksum calls cover only that part. |
| `inflateCopy`, `deflateCopy`  | Start: copy and relocation | <a id="readiness-inflatecopy"></a> **Start:** allocation failures, buffer copies, pointer relocation and independent ownership. Resolve the recorded copy/history investigations before claiming the full domain; do not add silent premises. |
| `deflateParams` | Needs: block flush and parameter state | <a id="readiness-deflateparams"></a> **Compose:** actual old-block flushing, return-code handling and canonical tuning-row updates. Check exact state preservation on refusal before full closure. |
| `inflateSync`  | Needs: scan and history | <a id="readiness-inflatesync"></a> **Start:** compose existing first/resume scans, held bits, marker search, reset and accounting/frame results. Derive window/reset premises from histories. |
| `compress2_z`, `compress2`, `compress_z`, `compress`  | Needs: compressor execution | <a id="readiness-compress2-z"></a> **Start:** arguments, scalar lengths and cleanup. **Compose:** actual init/compress/end with exact output, then wrappers. Abstract roundtrip is insufficient. |
| `uncompress2_z`, `uncompress2`, `uncompress_z`, `uncompress`  | Needs: decoder execution | <a id="readiness-uncompress2-z"></a> **Start:** scalar results, insufficient space and cleanup. **Compose:** actual init/decompress/end, exact consumption/output, then wrappers. |
| `inflate`, `deflate`  | Needs: dispatch invariants | <a id="readiness-inflate"></a> **Compose:** decoder-table or hash-chain meaning, dispatch invariants, loop termination and output/accounting. Green checksums do not establish these premises. |
| `inflate_sequence`, `deflate_sequence`, `inflate_back_sequence`, `gz_sequence`  | Needs: execution and format | <a id="readiness-inflate-sequence"></a> **Compose:** actual per-call safety, history preservation, independent format refinement and completion across input/output splits. |
| `inflateBack` | Needs: tables, window and callbacks | <a id="readiness-inflateback"></a> **Compose:** compressed TABLE/LEN execution, output inside the window, public callback ownership, loop termination and exact input/output accounting. Existing stored and entry paths can progress independently. |
<!-- proof-readiness:end -->

The immediate order is independent entry/cleanup and arithmetic paths, then common open,
position and ownership invariants, then complete function composition. Callback compressed
blocks can progress alongside these. Record an unknown prerequisite here with its exact
question; do not invent a dependency or treat elapsed time as evidence of a blocker.


### Specification review

#### Gzip seek mode

Corrected. `GzSeek` used to let a successful seek return a handle in the other mode, so
the abstract `gz_seek_read` goal was false. The relation now keeps the mode. The goal has a
[locally checked proof](../ZlibF/Proof/Api/GzSeekRead.lean), and the former counterexample is a
[regression](../tests/verification/regressions/gz-seek-mode.lean). Registration and CI on a
named commit remain. This was a model issue, not a zlib issue.

#### Inflate initialization cleanup

Corrected. For an invalid window parameter the `inflateInit2_` goal required a structurally
unchanged state table, but allocation followed by free lengthens that table. That branch now
compares every object table entry by entry (`SameObjectsUpToTableShape`); no C operation
observes the table length. The goal has a
[locally checked proof](../ZlibF/Proof/public-inflate-init2.lean), and the former counterexample
is a [regression](../tests/verification/regressions/inflate-init2-table-shape.lean).
Registration and CI on a named commit remain. This was a contract issue, not a zlib issue.

#### Decompression utility cleanup

Corrected. `UncompressCounted` and `UncompressSingle` compared the final heap with
`SameObjects`, which requires equal object tables, including their physical length.
`uncompress2_z` allocates a local `z_stream` and a local 8-byte block before its argument
checks and frees both on every path; a freed entry stays in the table as an empty entry. Even
the null-argument refusal therefore made the four decompression goals false. They now compare
tables entry by entry (`SameObjectsUpToTableShape`, moved to `Spec/Public/Memory.lean`), as
the `inflateInit2_` contract does. The counterexample is a
[regression](../tests/verification/regressions/uncompress-table-shape.lean). This was a contract
issue, not a zlib issue. `CompressorContract` had the same pattern (`compress2_z` also frees a
local `z_stream`).

The same four contracts also lacked the heap representation condition `Uniq` (one object per
block identity below `nextBlk`), which [the trusted base](trusted-base.md) requires of every
initial heap and which every public stream history already assumes (`InitDomain`,
`StreamReachable`). It is now a premise. It does not narrow the C domain: every C state has such
a representation.

Corrected for the compressors too. `CompressorContract` and `CompressorSafety` had both defects.
The local `z_stream` of `compress2_z` is freed on every path after the argument checks, so its
empty entry made the goals false even when `deflateInit` refuses the level before allocating
(level 10 on the public caller witness:
[regression](../tests/verification/regressions/compress-table-shape.lean)). They now use
`SameObjectsUpToTableShape`. They also lacked `Uniq`, which the `deflateInit` contract and the
`deflate` stream history (`StreamReachable.deflateInit`) assume; it is now a premise. Statement test
of `CompressorSafety`: `tests/goals/compress-safety` (ASan, UBSan, leak count, allocation
failures, invalid levels; no clause violated in 9000 runs).

Review the corrected shared `Uncompress2` relation independently. The deferred-distance and
exact-free corrections have independent counterexamples and checked regression proofs;
implementation refinement remains open. Its former empty-output clause on memory failure and
extension clause on buffer error have been removed using the existing paired counterexample.
Complete the older abstract gz and dictionary models before using them as complete operational
refinements; the concrete public targets do not assume their callee contracts.

#### Gzip open path length

Corrected on 2026-11-13. `gz_open` copies the caller path with `malloc(len + 1)` and
`snprintf(state->path, len + 1, "%s", path)`. Two halves:

- `snprintf` past `INT_MAX`: the model `snprintf` returns -1 there, as glibc does
  ([trusted base](trusted-base.md), Formatting). No fault, no statement change.
- `malloc` above `PTRDIFF_MAX`: the runtime allocator now refuses a request of `2^63` bytes or
  more, as glibc 2.43 does ([trusted base](trusted-base.md), Allocation size). A path of
  `2^63 − 1` bytes then makes `gzopen` return NULL without an oracle failure and without calling
  `open`. The old second clause of `OpenContract` admitted that path and demanded an invalid
  mode, an oracle failure or a failed `open`, so it was false of the corrected model. The
  checked counterexample is the
  [regression](../tests/verification/regressions/gzopen-path-ptrdiff.lean)
  (`old_open_clause_false`). `Goal.gz_initialisation_domain` was false for the same path: it
  promised a handle under `NoAllocationFailure h`.

Correction, in its own commit. `OpenContract` (`Goal.gzopen`, `Goal.gzopen64`), second clause:
old premises `Fresh h → Uniq h → LibraryGlobals h → FileSystem fs → CString h path name →
CString h mode flags`; new premises add `ZlibF.PlatformMemory.ByteObjectsFit h` after
`FileSystem fs`. `Goal.gz_initialisation_domain`, first clause: old premises `... FileSystem fs →
NoAllocationFailure h → CString h path name → ...`; new premises add `ByteObjectsFit h` after
`NoAllocationFailure h`. With it, the path and its NUL lie in one object below `2^63` bytes, so
the copy is never refused for its size and `len + 1` does not wrap. The witness clause and
`Goal.gzdopen` (a 19-byte path) are unchanged. None of the three goals was proved or registered.
The premise is the accepted platform scope ([deviations](deviations.md), row "Platform
byte-object scope").

#### Gzip library findings with local fixes

Library reports of 2026-11-12, kept here until the owner decides whether F-1 and W7 move to
`README.md` as confirmed findings. Each has a local patch, approved by the owner on 2026-11-12 and
not yet submitted upstream ([patches](../patches/README.md)).

- F-1, [gzread position overflow](findings/gzread-pos-overflow/README.md): after a transparent
  `gzseek` to `INT64_MAX` on Linux `/dev/zero`, `gzread` overflows the signed `x.pos`. Confirmed
  by UBSan on x86_64 Linux. Patch 0004.
- W7, [gzwrite position overflow](findings/gzwrite-pos-overflow/README.md): a transparent writer
  on `/dev/null` that seeks to `INT64_MAX - 10` overflows `x.pos` in `gzwrite` (and in `gzputc` at
  `INT64_MAX`). Confirmed by UBSan on x86_64 Linux with the real device. Patch 0004.
- R-3, [x.next never written](findings/gz-reset-next-uninitialised/README.md): `gzseek` and
  `gzdirect` right after `gzopen` advance the never-written `x.next` by zero. Undefined by the
  letter of C; no sanitizer report. Patch 0005.
- R-4, [x.next dangling after a direct read](findings/gz-next-dangling-after-direct-read/README.md):
  after a large `gzread` into a buffer the caller then frees, `gzseek` and `gzdirect` advance
  `x.next` by zero inside the freed buffer. Undefined by the letter of C; no sanitizer report.
  Patch 0005.

The translations of `gzread.c`, `gzwrite.c` and `gzlib.c` follow both patches. Only 0005 has a
differential row (a direct read into a freed buffer, then `gzdirect` and `gzseek`); 0004 needs a
device, which the file model cannot express. `tests/audit/theorems.txt` still lists
`seekTail_dangling_ub` and `gzseek64_dangling_next_ub`, which no longer exist; their removal is for
a human.

#### Gzip offset and rewind on the OS-call oracle

Corrected in `caad9db4` under the owner's delegation; the evidence is recorded here. The OS-call
oracle lets an `lseek` return any value in `[0, 2^63 - 1]` without moving the descriptor (M3), as
Linux does on some devices. Three registered goals state the descriptor position after `lseek`:

- `Goal.gzoffset64` and `Goal.gzoffset` (`OffsetContract`, `Spec/Public/GzControl.lean`). Old: for
  every reachable handle in `GzValid` and every world with `FileSystem fs`, the call returns, keeps
  the heap, changes the world only in `errno` (`{ fs' with errno := fs.errno } = fs`), and returns
  the descriptor position less the buffered input of a reader (-1 for a bad descriptor). New: the
  same under the added premise `RegularOs fs`, and the world changes only in `errno` and the call
  counter (`{ fs' with errno := fs.errno, nos := fs.nos } = fs`).
- `Goal.gzrewind`. Old: for every reachable handle in `GzValid`, the call returns -1 with the heap
  kept, or 0 with the reset state and the descriptor at the saved start; a writer or a serious
  error gives -1 with the world kept. New: the same under the added premise `RegularOs fs`.

Reason. Every oracle call advances the call counter `nos`, so the old world clause of the offset
contract is false for every handle (by the definition of `fsLseek`). An oracle `lseek` returns a
value unrelated to the descriptor, so the value clauses hold only when every later call is regular:
`RegularOs fs` (`Spec/Public/GzState.lean`). Checked counterexample: the
[regression](../tests/verification/regressions/gz-offset-regular-world.lean). In a world admitted
by `FileSystem` whose `lseek` returns 77 without moving, `gzdopen(3, "r")` records the start 77;
`gzoffset64` and `gzoffset` then return 77 while the descriptor is at 0, and `gzrewind` returns 0
while the descriptor stays at 0. The old three statements are false, and so is the corrected offset
contract without `RegularOs`. This was a model change, not a zlib issue.

The three goals are now functional contracts of the regular-file instance. Their safety on every
world (every oracle) is part of `Goal.gz_sequence_safety` (`GzSafety.lean`), proved on the branch `skeleton/gz`. Its call
dispatch (`operation_safe` in `gz.skeleton.lean`) takes `gzoffset64`, `gzoffset` and `gzrewind` as
next calls through `gzoffset64_step`, `gzoffset_step` and `gzrewind_step`. Each is `GzCallSafe` for
every `fs`, with no `RegularOs` and no read budget: no fault, a result, the open descriptors kept,
`GzInv` kept, and only the handle's blocks changed. The three step lemmas are open on the skeleton,
and `gzrewind_step` relies on the local patch for R-3. Until they are checked, the safety of these
calls on a non-regular world is not proved. They cannot reuse the registered proofs as they stand,
since those now assume `RegularOs`.

### Translation review

Review the C language edition and implementation extensions used by the selected
build. In particular, establish definedness for reachable null-plus-zero and
null-minus-null operations. The current model permits some of them, and the
`Ptr.diff` source comment incorrectly attributes null subtraction to C23. The
[comparison table](spec/safety.md#null-pointers-and-pointer-differences) records
the actual definitions and language references. This documentation change does
not alter the runtime or establish that a reachable upstream bug exists.

Continue the statement-by-statement review beyond the corrected compressor automatic storage. The
compressor slide now checks signed subtraction in source order. Its
[internal-state regression](../tests/regression/deflate-slide/README.md) compares three defined
boundaries and rejects an artificial overflow in both C and Lean. Restoring unchecked subtraction
changes only the overflow observation. Reachability of that artificial state is not claimed;
derive the signed bound from legal call histories. The source-level selected-depth reread in tree merging has been restored with a
[six-case regression](../tests/regression/trees-depth-read/README.md) and a required structural
check that rejects the former cached expression. Prove the temporal initialization history of
internal depth reads. Review scalar-pointer aliasing and the null-minus-null special case in
compressor pointer subtraction (**to confirm**).

### Observations

**`gz_comp` spins on a `write` that returns 0.** In both write loops of `gz_comp`
(`gzwrite.c`: the transparent loop `while (strm->avail_in)` and the write-out loop
`while (strm->next_out > state->x.next)`), a `write` that returns 0 for a nonempty buffer
advances nothing and is not an error, so the loop repeats the same call. If the system keeps
returning 0, the C never returns. This is a reading of the code; a `write` that returns 0
forever was not run. Linux is not known to return 0 for a nonzero count on regular files, pipes
or sockets (**to confirm** for other file types), so the gz safety proof assumes it (trusted
base, "Gz OS facts"). The fault-injection harness of the gz safety study checked the other side:
with a `write` that returns 0 on 10 % of nonempty calls (40 histories, ASan and UBSan), every
history ended with no report and no leak, because each loop eventually gets a positive result.
Behaviour of the library, not a safety finding; worth an upstream note only if a platform is
known that returns 0. Scope: `gzwrite`, `gzfwrite`, `gzputc`, `gzputs`, `gzprintf`, `gzflush`,
`gzsetparams`, `gzclose_w`.

**A string returned by `gzerror` is freed by the next call that reaches `gz_error`.**
Unconfirmed finding, a documentation gap, not a code bug. zlib.h says only that later calls of
`gzerror` may invalidate the returned string. In fact `gzerror` returns `state->msg`, and every
call that reaches `gz_error` frees it: `gzprintf`, `gzvprintf`, `gzputs`, `gzwrite`, `gzread` and
others reset the error with `gz_error(state, Z_OK, NULL)` before they use their arguments. A caller
that passes that string back to the same handle gets a use after free:
`gzprintf(f, "%s", gzerror(f, &e))` after a stalled write reads freed memory in `vsnprintf`
([reproduction](../tests/regression/gzprintf-error-string/README.md), ASan). No patch. The proved
domain keeps caller strings and buffers apart from the handle's blocks (`GzRange`, and the
separation clause of `GzArguments` for `gzprintf`/`gzvprintf`, [deviations](deviations.md)).

### Historical reports to recheck

Recheck gzip extra-length arithmetic, partial-read recovery, negative-position
seeking, lost parameter changes, failed-finish recovery and forward seek after EOF
against the current pin. Conditional seek fault lemmas do not prove reachability:
establish signed-position and borrowed-pointer conditions from actual call histories.
The `inflateBack` history report remains unconfirmed for that callback API;
ordinary-inflate sanitizer examples do not settle it.
The external string allocator and fixed loop fuel also need review before full
gzip ownership or arbitrary finite callback termination is claimed.
A suspected defect is not permission to exclude a public case.
[Findings](findings.md) records evidence and confidence; current patches are in
[patches/README.md](../patches/README.md). No blanket UB patch is applied.

The [architecture guide](design/architecture.md#design-decisions) records design decisions
D1–D6. The [safety specification](spec/safety.md#uninitialised-memory) defines
the fresh-memory obligations.

