# Proof progress and remaining work

This page records evidence and unfinished work. For the statement and proof
architecture, read [the overview](overview.md).

## Scope

The project is finished when the planned targets below are accepted. The rest is not planned.

**Planned.** Three results, in this order, and then their direct compositions.

| # | Result | Targets |
| ---: | --- | --- |
| 1 | `inflate` is safe on every input: no undefined behaviour, no memory error, no leak, and it terminates, for every input and every split of the buffers. | `inflate`, the safety part of `inflate_sequence` |
| 2 | `inflate` produces exactly the bytes the format defines. It rejects no valid stream and accepts no invalid one. | the format part of `inflate_sequence` |
| 3 | `deflate` is safe, and its output decodes to its input. | `deflateInit2_`, `deflate`, `deflate_sequence` |
| 4 | Whole-buffer compositions of 1 to 3. | `compress*`, `uncompress*` |

A target that one of these needs as a step stays planned as a dependency. This holds for the
other stream calls that a sequence goal ranges over, such as `inflateSync`, `inflateCopy`,
`deflateCopy`, `deflateParams`, `deflatePrime` and `deflateSetDictionary`.

**Not planned.** No further work goes to these. Results already registered for them stay.

| Group | Targets | Reason |
| --- | --- | --- |
| Gzip file interface | `gzopen`, `gzopen64`, `gzclose*`, `gzread`, `gzfread`, `gzgetc`, `gzgetc_`, `gzgets`, `gzungetc`, `gzdirect`, `gzwrite`, `gzfwrite`, `gzputc`, `gzputs`, `gzprintf`, `gzvprintf`, `gzflush`, `gzsetparams`, `gzseek*`, `gztell*`, `gz_sequence`, `gz_initialisation_domain` | A theorem here depends on a hand-made model of the file system, descriptors and `printf` formatting. That model is assumed, not proved, so the result says less than it costs. The file layer adds no compression logic to the three results above. |
| Callback decoder | `inflateBack`, `inflate_back_sequence` | A rarely used interface. It repeats the decoding argument of result 2 under a different buffer protocol. |
| Model-only statements | `Api.Goal.inflate_rejects_invalid`, the unregistered `*_refines` goals | They speak about the abstract model, not about the C. The first also rests on a detection lag of eight bytes that a counterexample refutes. Rejection of invalid input is stated against the C in result 2. |
| Other build configurations | every configuration except the default x86_64 Linux build | Each one repeats the whole proof for a different platform model. The default build carries the result. |
| More proof mutants for query functions | getters and constant queries | Mutants defend against a wrong proof setup. For a one-line query they add nothing to the three results. |

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

**181 fixed targets: 103 public and 78 supporting.**
Exact proofs: 128 registered and 0 local only.
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
    n123["ByteAddress<br/>address_read_is_pure"]:::all
    n124["ByteAddress<br/>raw_block_unchanged"]:::all
    n125["ByteAddress<br/>every_layout_is_<br/>representable"]:::all
    n126["ByteAddress<br/>every_existing_heap_<br/>accepts_layout"]:::all
    n127["ByteAddress<br/>mask_refines_base_plus_<br/>offset"]:::all
    n128["ByteAddress<br/>pointer_advance_<br/>preserves_low_bits"]:::all
    n129["ByteAddress<br/>first_aligned_offset"]:::all
    n130["ByteAddress<br/>byte_stores_preserve_<br/>bases"]:::all
    n131["ByteAddress<br/>byte_modifies_preserve_<br/>bases"]:::all
  end
  style addresses fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph inflate["Inflate streams"]
    n39["inflateCopy"]:::unproved
    n73["inflateInit2_<br/>Blocked"]:::unproved
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
    n99["inflate"]:::unproved
    n105["inflateSync"]:::unproved
  end
  style inflate fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph fast["Fast decoder obligations"]
    n134["InflateFastBodyOrigin<br/>actual_body_preserves_<br/>origin"]:::all
    n135["InflateFastBodyToken<br/>actual_body_refines_token"]:::all
    n136["InflateFastCallOrigin<br/>actual_fast_preserves_<br/>origin"]:::all
    n137["InflateFastDistanceOrigin<br/>actual_distance_block_<br/>preserves_origin"]:::all
    n138["InflateFastDistanceResult<br/>actual_distance_refines_<br/>lz77"]:::all
    n139["InflateFastDistance<br/>Semantics<br/>distance_lookup_matches_<br/>format"]:::all
    n140["InflateFast<br/>fast_safe"]:::all
    n141["InflateFast<br/>step_safe"]:::all
    n142["InflateFastLength<br/>Semantics<br/>length_lookup_matches_<br/>format"]:::all
    n143["InflateFastLengthTrace<br/>actual_body_retains_<br/>selected_length"]:::all
    n144["InflateFastMatchHistory<br/>actual_copy_match_<br/>refines_lz77"]:::all
    n145["InflateFastMatchHistory<br/>match_array_refines_lz77"]:::all
    n146["InflateFastOrigin<br/>actual_drop_preserves_<br/>origin"]:::all
    n147["InflateFastOrigin<br/>actual_pull_preserves_<br/>origin"]:::all
    n148["InflateFastOrigin<br/>actual_rollback_<br/>preserves_origin"]:::all
    n149["InflateFastOrigin<br/>drop_preserves_origin"]:::all
    n150["InflateFastOrigin<br/>initial_origin"]:::all
    n151["InflateFastOrigin<br/>pull_preserves_origin"]:::all
    n152["InflateFastOrigin<br/>rollback_preserves_origin"]:::all
  end
  style fast fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph tables["Decode-table obligations"]
    n153["InflateDecodeTable<br/>Rejection<br/>decode_table_classifies_<br/>input"]:::all
    n154["InflateDecodeTable<br/>Semantics<br/>decode_table_matches_<br/>format"]:::all
    n155["InflateDecodeTableShort<br/>short_decode_table_leaf_<br/>sound"]:::all
    n156["InflateDecodeTable<br/>Soundness<br/>decode_table_leaf_sound"]:::all
    n157["InflateDecodeTableFrame<br/>decode_table_read_<br/>preserved"]:::all
    n158["InflateDecodeTable<br/>Invariant<br/>constructor_establishes_<br/>decode_table_invariant"]:::all
    n159["InflateDecodeTable<br/>Invariant<br/>decode_table_invariant_<br/>of_prefix"]:::all
    n160["InflateDecodeTable<br/>Stability<br/>constructor_establishes_<br/>query_stability"]:::all
    n161["InflateDecodeTable<br/>Stability<br/>query_stability_of_prefix"]:::all
    n162["InflateDecodeTable<br/>Stability<br/>short_rejected_leaf_<br/>stays_invalid"]:::all
    n163["InflateFastTableFlags<br/>constructor_establishes_<br/>fast_leaf_flags"]:::all
    n164["InflateFastTableFlags<br/>fast_leaf_flags_of_prefix"]:::all
    n165["InflateFastTableFlags<br/>fixed_tables_have_fast_<br/>leaf_flags"]:::all
    n166["InflateFastTableFlags<br/>leaf_classification_<br/>agrees"]:::all
    n167["InflateTableContent<br/>inflate_table_content"]:::all
    n168["InflateTableSafety<br/>inflate_table_decoder_<br/>safe"]:::all
    n169["InflateTableExtent<br/>inflate_table_read_extent"]:::all
    n170["InflateRootTable<br/>constructor_root_bits"]:::all
    n171["InflateSubtable<br/>constructor_subtable_bits"]:::all
  end
  style tables fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph copy["Match-copy mathematics"]
    n172["LZ77CopySpec<br/>output_copy_refines_lz77"]:::all
    n173["LZ77CopySpec<br/>window_copy_refines_lz77"]:::all
    n174["LZ77HistorySpec<br/>copy_back_compose"]:::all
    n175["LZ77HistorySpec<br/>copy_back_extends_history"]:::all
    n176["LZ77HistorySpec<br/>retained_history_agrees"]:::all
    n177["LZ77HistorySpec<br/>window_distance_check_<br/>agrees"]:::all
  end
  style copy fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph deflate["Deflate streams"]
    n40["deflateCopy"]:::unproved
    n75["deflateInit2_"]:::unproved
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
    n100["deflate"]:::unproved
    n101["deflateBound_z"]:::unproved
    n102["deflateBound"]:::unproved
    n103["deflatePrime"]:::unproved
    n104["deflateParams"]:::unproved
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
    n16["Goals<br/>gz_seek_read<br/>Blocked"]:::unproved
    n17["Concrete<br/>compress_bound_value"]:::all
    n18["Concrete<br/>compress2_z_first_alloc_<br/>failure"]:::all
    n122["Inflate<br/>inflate_deferred_distance"]:::all
  end
  style models fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph lifecycle["Lifecycles and call sequences"]
    n114["inflate_sequence"]:::unproved
    n115["deflate_sequence"]:::unproved
    n116["inflate_back_sequence"]:::unproved
    n117["gz_sequence"]:::unproved
    n118["inflate_initialisation_<br/>domain"]:::all
    n119["deflate_initialisation_<br/>domain"]:::unproved
    n120["inflate_back_<br/>initialisation_domain"]:::all
    n121["gz_initialisation_domain"]:::unproved
  end
  style lifecycle fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph internal["Internal proof obligations"]
    n132["Crc32ByteViews<br/>crc32_z_all_byte_views"]:::all
    n133["Crc32ByteViews<br/>crc32_all_byte_views"]:::all
    n178["Token<br/>rejected_has_no_symbols"]:::all
    n179["Token<br/>step_composes_symbols"]:::all
    n180["Token<br/>symbols_exposes_step"]:::all
  end
  style internal fill:#f9fafb,stroke:#9ca3af,color:#111827
  n128 --> n129
  n133 --> n28
  n132 --> n29
  n134 --> n136
  n137 --> n134
  n138 --> n135
  n139 --> n138
  n140 --> n136
  n141 --> n135
  n141 --> n140
  n141 --> n143
  n142 --> n135
  n144 --> n138
  n145 --> n144
  n146 --> n134
  n148 --> n136
  n149 --> n137
  n149 --> n146
  n150 --> n136
  n151 --> n137
  n151 --> n147
  n152 --> n148
  n153 --> n158
  n154 --> n153
  n155 --> n158
  n156 --> n153
  n156 --> n155
  n157 --> n159
  n157 --> n161
  n157 --> n164
  n162 --> n139
  n162 --> n142
  n167 --> n168
  n168 --> n169
  n168 --> n170
  n169 --> n158
  n171 --> n158
  n171 --> n170
  n172 --> n145
  n173 --> n145
  n174 --> n145
  n176 --> n8
  n176 --> n9
  n5 --> n10
  n5 --> n11
  n5 --> n8
  n5 --> n9
  n3 --> n9
  n2 --> n8
  n25 --> n24
  n36 --> n120
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
  click n0 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Api/Goals.lean#L42" _blank
  click n1 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Api/Goals.lean#L47" _blank
  click n2 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Api/Goals.lean#L58" _blank
  click n3 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Api/Goals.lean#L69" _blank
  click n4 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Api/Goals.lean#L84" _blank
  click n5 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Api/Goals.lean#L99" _blank
  click n6 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Api/Goals.lean#L106" _blank
  click n7 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Api/Goals.lean#L116" _blank
  click n8 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Api/Goals.lean#L134" _blank
  click n9 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Api/Goals.lean#L143" _blank
  click n10 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Api/Goals.lean#L162" _blank
  click n11 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Api/Goals.lean#L180" _blank
  click n12 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Api/Goals.lean#L189" _blank
  click n13 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Api/Goals.lean#L196" _blank
  click n14 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Api/Goals.lean#L203" _blank
  click n15 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Api/Goals.lean#L214" _blank
  class n16 obstacle
  click n16 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/docs/progress.md#gzip-seek-mode" _blank
  click n17 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Api/Concrete.lean#L57" _blank
  click n18 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Api/Concrete.lean#L67" _blank
  click n19 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Queries.lean#L35" _blank
  click n20 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Queries.lean#L40" _blank
  click n21 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Queries.lean#L46" _blank
  click n22 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Queries.lean#L53" _blank
  click n23 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Queries.lean#L59" _blank
  click n24 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Checksums.lean#L66" _blank
  click n25 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Checksums.lean#L61" _blank
  click n26 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Checksums.lean#L86" _blank
  click n27 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Checksums.lean#L90" _blank
  click n28 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Checksums.lean#L117" _blank
  click n29 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Checksums.lean#L109" _blank
  click n30 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Checksums.lean#L126" _blank
  click n31 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Checksums.lean#L140" _blank
  click n32 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Checksums.lean#L143" _blank
  click n33 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Checksums.lean#L150" _blank
  click n34 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Checksums.lean#L162" _blank
  click n35 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Checksums.lean#L165" _blank
  click n36 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Back.lean#L22" _blank
  click n37 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Back.lean#L115" _blank
  click n38 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Back.lean#L142" _blank
  click n39 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Copy.lean#L27" _blank
  click n40 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Copy.lean#L67" _blank
  click n41 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/GzClose.lean#L35" _blank
  click n42 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/GzClose.lean#L40" _blank
  click n43 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/GzClose.lean#L44" _blank
  click n44 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/GzControl.lean#L12" _blank
  click n45 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/GzControl.lean#L22" _blank
  click n46 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/GzControl.lean#L36" _blank
  click n47 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/GzControl.lean#L39" _blank
  click n48 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/GzControl.lean#L53" _blank
  click n49 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/GzControl.lean#L56" _blank
  click n50 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/GzControl.lean#L63" _blank
  click n51 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/GzControl.lean#L74" _blank
  click n52 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/GzControl.lean#L91" _blank
  click n53 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/GzControl.lean#L116" _blank
  click n54 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/GzControl.lean#L119" _blank
  click n55 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/GzOpen.lean#L61" _blank
  click n56 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/GzOpen.lean#L65" _blank
  click n57 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/GzOpen.lean#L70" _blank
  click n58 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/GzRead.lean#L22" _blank
  click n59 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/GzRead.lean#L37" _blank
  click n60 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/GzRead.lean#L58" _blank
  click n61 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/GzRead.lean#L61" _blank
  click n62 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/GzRead.lean#L66" _blank
  click n63 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/GzRead.lean#L80" _blank
  click n64 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/GzRead.lean#L103" _blank
  click n65 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/GzWrite.lean#L28" _blank
  click n66 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/GzWrite.lean#L43" _blank
  click n67 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/GzWrite.lean#L59" _blank
  click n68 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/GzWrite.lean#L71" _blank
  click n69 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/GzWrite.lean#L102" _blank
  click n70 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/GzWrite.lean#L106" _blank
  click n71 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/GzWrite.lean#L111" _blank
  click n72 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/GzWrite.lean#L128" _blank
  class n73 obstacle
  click n73 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/docs/progress.md#inflate-initialization-cleanup" _blank
  click n74 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Initialisation.lean#L95" _blank
  click n75 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Initialisation.lean#L138" _blank
  click n76 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Initialisation.lean#L145" _blank
  click n77 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Lifecycle.lean#L20" _blank
  click n78 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Lifecycle.lean#L32" _blank
  click n79 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Lifecycle.lean#L43" _blank
  click n80 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Lifecycle.lean#L60" _blank
  click n81 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Lifecycle.lean#L77" _blank
  click n82 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Lifecycle.lean#L87" _blank
  click n83 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Lifecycle.lean#L105" _blank
  click n84 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Lifecycle.lean#L115" _blank
  click n85 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Lifecycle.lean#L146" _blank
  click n86 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Lifecycle.lean#L149" _blank
  click n87 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Lifecycle.lean#L153" _blank
  click n88 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Lifecycle.lean#L175" _blank
  click n89 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/StreamQueries.lean#L53" _blank
  click n90 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/StreamQueries.lean#L62" _blank
  click n91 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/StreamQueries.lean#L73" _blank
  click n92 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/StreamQueries.lean#L81" _blank
  click n93 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/StreamQueries.lean#L89" _blank
  click n94 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/StreamQueries.lean#L100" _blank
  click n95 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/StreamQueries.lean#L113" _blank
  click n96 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/StreamQueries.lean#L124" _blank
  click n97 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/StreamQueries.lean#L132" _blank
  click n98 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/StreamQueries.lean#L145" _blank
  click n99 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Streams.lean#L28" _blank
  click n100 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Streams.lean#L56" _blank
  click n101 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Streams.lean#L110" _blank
  click n102 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Streams.lean#L114" _blank
  click n103 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Streams.lean#L124" _blank
  click n104 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Streams.lean#L142" _blank
  click n105 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Streams.lean#L165" _blank
  click n106 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Utilities.lean#L44" _blank
  click n107 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Utilities.lean#L49" _blank
  click n108 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Utilities.lean#L56" _blank
  click n109 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Utilities.lean#L61" _blank
  click n110 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Utilities.lean#L108" _blank
  click n111 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Utilities.lean#L112" _blank
  click n112 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Utilities.lean#L139" _blank
  click n113 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Utilities.lean#L143" _blank
  click n114 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Sequences.lean#L211" _blank
  click n115 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Sequences.lean#L225" _blank
  click n116 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Sequences.lean#L252" _blank
  click n117 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Sequences.lean#L264" _blank
  click n118 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Domains.lean#L24" _blank
  click n119 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Domains.lean#L37" _blank
  click n120 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Domains.lean#L53" _blank
  click n121 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Public/Domains.lean#L77" _blank
  click n122 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Api/Inflate.lean#L267" _blank
  click n123 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/ByteAddress.lean#L39" _blank
  click n124 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/ByteAddress.lean#L43" _blank
  click n125 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/ByteAddress.lean#L50" _blank
  click n126 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/ByteAddress.lean#L57" _blank
  click n127 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/ByteAddress.lean#L65" _blank
  click n128 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/ByteAddress.lean#L70" _blank
  click n129 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/ByteAddress.lean#L77" _blank
  click n130 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/ByteAddress.lean#L83" _blank
  click n131 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/ByteAddress.lean#L87" _blank
  click n132 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Crc32ByteViews.lean#L17" _blank
  click n133 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Crc32ByteViews.lean#L28" _blank
  click n134 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/InflateFastBodyOrigin.lean#L18" _blank
  click n135 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/InflateFastBodyToken.lean#L73" _blank
  click n136 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/InflateFastCallOrigin.lean#L24" _blank
  click n137 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/InflateFastDistanceOrigin.lean#L18" _blank
  click n138 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/InflateFastDistanceResult.lean#L101" _blank
  click n139 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/InflateFastDistanceSemantics.lean#L20" _blank
  click n140 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/InflateFast.lean#L68" _blank
  click n141 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/InflateFast.lean#L40" _blank
  click n142 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/InflateFastLengthSemantics.lean#L34" _blank
  click n143 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/InflateFastLengthTrace.lean#L51" _blank
  click n144 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/InflateFastMatchHistory.lean#L39" _blank
  click n145 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/InflateFastMatchHistory.lean#L25" _blank
  click n146 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/InflateFastOrigin.lean#L68" _blank
  click n147 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/InflateFastOrigin.lean#L57" _blank
  click n148 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/InflateFastOrigin.lean#L81" _blank
  click n149 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/InflateFastOrigin.lean#L38" _blank
  click n150 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/InflateFastOrigin.lean#L27" _blank
  click n151 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/InflateFastOrigin.lean#L32" _blank
  click n152 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/InflateFastOrigin.lean#L46" _blank
  click n153 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/InflateDecodeTableRejection.lean#L19" _blank
  click n154 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/InflateDecodeTableSemantics.lean#L51" _blank
  click n155 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/InflateDecodeTableShort.lean#L26" _blank
  click n156 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/InflateDecodeTableSoundness.lean#L31" _blank
  click n157 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/InflateDecodeTableFrame.lean#L20" _blank
  click n158 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/InflateDecodeTableInvariant.lean#L51" _blank
  click n159 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/InflateDecodeTableInvariant.lean#L68" _blank
  click n160 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/InflateDecodeTableStability.lean#L30" _blank
  click n161 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/InflateDecodeTableStability.lean#L43" _blank
  click n162 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/InflateDecodeTableStability.lean#L54" _blank
  click n163 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/InflateFastTableFlags.lean#L52" _blank
  click n164 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/InflateFastTableFlags.lean#L66" _blank
  click n165 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/InflateFastTableFlags.lean#L76" _blank
  click n166 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/InflateFastTableFlags.lean#L42" _blank
  click n167 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/InflateTableContent.lean#L32" _blank
  click n168 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/InflateTableSafety.lean#L28" _blank
  click n169 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/InflateTableExtent.lean#L28" _blank
  click n170 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/InflateRootTable.lean#L21" _blank
  click n171 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/InflateSubtable.lean#L26" _blank
  click n172 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Math/LZ77CopySpec.lean#L22" _blank
  click n173 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Math/LZ77CopySpec.lean#L32" _blank
  click n174 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Math/LZ77HistorySpec.lean#L21" _blank
  click n175 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Math/LZ77HistorySpec.lean#L15" _blank
  click n176 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Math/LZ77HistorySpec.lean#L29" _blank
  click n177 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Math/LZ77HistorySpec.lean#L39" _blank
  click n178 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Format/Token.lean#L84" _blank
  click n179 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Format/Token.lean#L62" _blank
  click n180 href "https://github.com/cla7aye15I4nd/zlib-f/blob/9c5be8dfa641db9b804acb7587c03a0629fd4b74/ZlibF/Spec/Format/Token.lean#L73" _blank
  classDef unproved fill:#e5e7eb,color:#374151,stroke:#374151
  classDef default fill:#dbeafe,color:#1d4ed8,stroke:#1d4ed8
  classDef common fill:#fef3c7,color:#92400e,stroke:#92400e
  classDef all fill:#dcfce7,color:#166534,stroke:#166534
  classDef obstacle stroke:#b91c1c,stroke-width:3px
```

Each node opens its exact target or blocker at the fixed source snapshot
`9c5be8d`. Some viewers disable diagram links; the
[evidence index](progress.md) provides ordinary links and all proof references.

| Blocked targets | Reason and next step |
| --- | --- |
| [gz_seek_read](./progress.md#target-zlibf-spec-api-goal-gz-seek-read) | [Gzip seek mode](./progress.md#gzip-seek-mode) |
| [inflateInit2_](./progress.md#target-zlibf-spec-public-goal-inflateinit2) | [Inflate initialization cleanup](./progress.md#inflate-initialization-cleanup) |


## Target evidence

<!-- proof-link-revision: 9c5be8dfa641db9b804acb7587c03a0629fd4b74 -->

[Proof narrative](overview.md) · [All-target graph](#proof-progress-graph) · [Input configurations](spec/input-configurations.md)

This index contains **181 fixed targets**: public execution,
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
| <a id="target-zlibf-spec-public-goal-inflatecopy"></a>[inflateCopy](../ZlibF/Spec/Public/Copy.lean#L27) | Not proved / Not proved | [Contract](../docs/spec/api/inflate-stream.md#inflatecopy); [input range](spec/input-configurations.md#inflate-inputs) | — | [Start: copy and relocation](progress.md#readiness-inflatecopy) |
| <a id="target-zlibf-spec-public-goal-inflateinit2"></a>[inflateInit2_](../ZlibF/Spec/Public/Initialisation.lean#L90) | Not proved / Blocked | [Contract](../docs/spec/api/inflate-stream.md#inflateinit2_); [input range](spec/input-configurations.md#inflate-inputs) | — [Blocker: Inflate initialization cleanup](progress.md#inflate-initialization-cleanup) | [Blocked: cleanup contract](progress.md#readiness-inflateinit2) |
| <a id="target-zlibf-spec-public-goal-inflateinit"></a>[inflateInit_](../ZlibF/Spec/Public/Initialisation.lean#L95) | All stated inputs / Registered proof | [Contract](../docs/spec/api/inflate-stream.md#inflateinit_); [input range](spec/input-configurations.md#inflate-inputs) | [Zlib.Inflate.Proofs.inflate_default_init_contract](../ZlibF/Proof/inflate.c.default-entry.lean#L58); [ZlibF.Spec.Public.Proofs.InflateInit.init15_public](../ZlibF/Proof/public-inflate-init.lean#L83) | — |
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
| <a id="target-zlibf-spec-public-goal-inflate"></a>[inflate](../ZlibF/Spec/Public/Streams.lean#L28) | Not proved / Not proved | [Contract](../docs/spec/api/inflate-stream.md#inflate); [input range](spec/input-configurations.md#inflate-inputs) | — | [Needs: dispatch invariants](progress.md#readiness-inflate) |
| <a id="target-zlibf-spec-public-goal-inflatesync"></a>[inflateSync](../ZlibF/Spec/Public/Streams.lean#L165) | Not proved / Not proved | [Contract](../docs/spec/api/inflate-stream.md#inflatesync); [input range](spec/input-configurations.md#inflate-inputs) | — | [Needs: scan and history](progress.md#readiness-inflatesync) |

<a id="group-fast"></a>

## Fast decoder obligations

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlib-inffast-spec-bodyorigin-goal-actual-body-preserves-origin"></a>[actual_body_preserves_origin](../ZlibF/Spec/InflateFastBodyOrigin.lean#L18) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.BodyOriginProof.actual_body_preserves_origin](../ZlibF/Proof/inffast.c.body-origin.lean#L374); [Zlib.Inffast.Proofs.actual_body_preserves_origin](../ZlibF/Proof/inffast.c.body-origin.lean#L374) | — |
| <a id="target-zlib-inffast-spec-bodytoken-goal-actual-body-refines-token"></a>[actual_body_refines_token](../ZlibF/Spec/InflateFastBodyToken.lean#L73) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.BodyTokenProof.actual_body_refines_token](../ZlibF/Proof/inffast.c.body-token.lean#L564); [Zlib.Inffast.Proofs.actual_body_refines_token](../ZlibF/Proof/inffast.c.body-token.lean#L564) | — |
| <a id="target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin"></a>[actual_fast_preserves_origin](../ZlibF/Spec/InflateFastCallOrigin.lean#L24) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_fast_preserves_origin](../ZlibF/Proof/inffast.c.call-origin.lean#L176); [ZlibF.Proof.Registration.fast_call_origin](../ZlibF/Proof/proof-registrations.lean#L14) | — |
| <a id="target-zlib-inffast-spec-distanceorigin-goal-actual-distance-block-preserves-origin"></a>[actual_distance_block_preserves_origin](../ZlibF/Spec/InflateFastDistanceOrigin.lean#L18) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_distance_block_preserves_origin](../ZlibF/Proof/inffast.c.distance-origin.lean#L324) | — |
| <a id="target-zlib-inffast-spec-distanceresult-goal-actual-distance-refines-lz77"></a>[actual_distance_refines_lz77](../ZlibF/Spec/InflateFastDistanceResult.lean#L101) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_distance_refines_lz77](../ZlibF/Proof/inffast.c.distance-result.lean#L382) | — |
| <a id="target-zlib-inffast-spec-distancesemantics-goal-distance-lookup-matches-format"></a>[distance_lookup_matches_format](../ZlibF/Spec/InflateFastDistanceSemantics.lean#L20) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.distance_lookup_matches_format](../ZlibF/Proof/inffast.c.distance-semantics.lean#L22) | — |
| <a id="target-zlib-inffast-spec-goal-fast-safe"></a>[fast_safe](../ZlibF/Spec/InflateFast.lean#L68) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.inflate_fast_safe](../ZlibF/Proof/inffast.c.final.lean#L257) | — |
| <a id="target-zlib-inffast-spec-goal-step-safe"></a>[step_safe](../ZlibF/Spec/InflateFast.lean#L40) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.inflate_fast_body_step_safe](../ZlibF/Proof/inffast.c.body.lean#L315) | — |
| <a id="target-zlib-inffast-spec-lengthsemantics-goal-length-lookup-matches-format"></a>[length_lookup_matches_format](../ZlibF/Spec/InflateFastLengthSemantics.lean#L34) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.length_lookup_matches_format](../ZlibF/Proof/inffast.c.length-semantics.lean#L22) | — |
| <a id="target-zlib-inffast-spec-lengthtrace-goal-actual-body-retains-selected-length"></a>[actual_body_retains_selected_length](../ZlibF/Spec/InflateFastLengthTrace.lean#L51) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.LengthTraceProof.actual_body_retains_selected_length](../ZlibF/Proof/inffast.c.length-trace.lean#L247); [Zlib.Inffast.Proofs.actual_body_retains_selected_length](../ZlibF/Proof/inffast.c.length-trace.lean#L247) | — |
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
| <a id="target-zlib-inftrees-spec-goal-inflate-table-decoder-safe"></a>[inflate_table_decoder_safe](../ZlibF/Spec/InflateTableSafety.lean#L28) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.inflate_table_decoder_safe](../ZlibF/Proof/inftrees.c.decoder-safe.lean#L93) | — |
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
| <a id="target-zlibf-spec-public-goal-deflatecopy"></a>[deflateCopy](../ZlibF/Spec/Public/Copy.lean#L67) | Not proved / Not proved | [Contract](../docs/spec/api/deflate-stream.md#deflatecopy); [input range](spec/input-configurations.md#deflate-inputs) | — | [Start: copy and relocation](progress.md#readiness-inflatecopy) |
| <a id="target-zlibf-spec-public-goal-deflateinit2"></a>[deflateInit2_](../ZlibF/Spec/Public/Initialisation.lean#L138) | Not proved / Not proved | [Contract](../docs/spec/api/deflate-stream.md#deflateinit2_); [input range](spec/input-configurations.md#deflate-inputs) | — | [Start: init and allocation](progress.md#readiness-deflateinit2) |
| <a id="target-zlibf-spec-public-goal-deflateinit"></a>[deflateInit_](../ZlibF/Spec/Public/Initialisation.lean#L145) | All stated inputs / Registered proof | [Contract](../docs/spec/api/deflate-stream.md#deflateinit_); [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.Proofs.DeflateInit.deflateInit_proof](../ZlibF/Proof/public-deflate-init.lean#L161) | — |
| <a id="target-zlibf-spec-public-goal-deflategetdictionary"></a>[deflateGetDictionary](../ZlibF/Spec/Public/Lifecycle.lean#L105) | All stated inputs / Registered proof | [Contract](../docs/spec/api/deflate-stream.md#deflategetdictionary); [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateDictionaryProof.deflate_getdict_public](../ZlibF/Proof/public-deflate-getdict.lean#L10) | — |
| <a id="target-zlibf-spec-public-goal-deflateend"></a>[deflateEnd](../ZlibF/Spec/Public/Lifecycle.lean#L115) | All stated inputs / Registered proof | [Contract](../docs/spec/api/deflate-stream.md#deflateend); [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateEndProof.deflate_end_public](../ZlibF/Proof/public-deflate-end.lean#L10) | — |
| <a id="target-zlibf-spec-public-goal-deflateresetkeep"></a>[deflateResetKeep](../ZlibF/Spec/Public/Lifecycle.lean#L146) | All stated inputs / Registered proof | [Contract](../docs/spec/api/deflate-stream.md#deflateresetkeep); [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateResetKeepProof.deflate_resetkeep_public](../ZlibF/Proof/public-deflate-reset-keep.lean#L19) | — |
| <a id="target-zlibf-spec-public-goal-deflatereset"></a>[deflateReset](../ZlibF/Spec/Public/Lifecycle.lean#L149) | All stated inputs / Registered proof | [Contract](../docs/spec/api/deflate-stream.md#deflatereset); [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateResetProof.deflate_reset_public](../ZlibF/Proof/public-deflate-reset.lean#L52) | — |
| <a id="target-zlibf-spec-public-goal-deflatesetdictionary"></a>[deflateSetDictionary](../ZlibF/Spec/Public/Lifecycle.lean#L175) | Not proved / Not proved | [Contract](../docs/spec/api/deflate-stream.md#deflatesetdictionary); [input range](spec/input-configurations.md#deflate-inputs) | — | [Start: window and hash](progress.md#readiness-deflatesetdictionary) |
| <a id="target-zlibf-spec-public-goal-deflatepending"></a>[deflatePending](../ZlibF/Spec/Public/StreamQueries.lean#L113) | All stated inputs / Registered proof | [Contract](../docs/spec/api/deflate-stream.md#deflatepending); [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateQueryProof.pending_public](../ZlibF/Proof/public-deflate-small-queries.lean#L145) | — |
| <a id="target-zlibf-spec-public-goal-deflateused"></a>[deflateUsed](../ZlibF/Spec/Public/StreamQueries.lean#L124) | All stated inputs / Registered proof | [Contract](../docs/spec/api/deflate-stream.md#deflateused); [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateQueryProof.used_public](../ZlibF/Proof/public-deflate-small-queries.lean#L48) | — |
| <a id="target-zlibf-spec-public-goal-deflatetune"></a>[deflateTune](../ZlibF/Spec/Public/StreamQueries.lean#L132) | All stated inputs / Registered proof | [Contract](../docs/spec/api/deflate-stream.md#deflatetune); [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateQueryProof.tune_public](../ZlibF/Proof/public-deflate-small-queries.lean#L61) | — |
| <a id="target-zlibf-spec-public-goal-deflatesetheader"></a>[deflateSetHeader](../ZlibF/Spec/Public/StreamQueries.lean#L145) | All stated inputs / Registered proof | [Contract](../docs/spec/api/deflate-stream.md#deflatesetheader); [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateQueryProof.header_public](../ZlibF/Proof/public-deflate-small-queries.lean#L74) | — |
| <a id="target-zlibf-spec-public-goal-deflate"></a>[deflate](../ZlibF/Spec/Public/Streams.lean#L56) | Not proved / Not proved | [Contract](../docs/spec/api/deflate-stream.md#deflate); [input range](spec/input-configurations.md#deflate-inputs) | — | [Needs: dispatch invariants](progress.md#readiness-inflate) |
| <a id="target-zlibf-spec-public-goal-deflatebound-z"></a>[deflateBound_z](../ZlibF/Spec/Public/Streams.lean#L110) | Not proved / Not proved | [Contract](../docs/spec/api/deflate-stream.md#deflatebound_z); [input range](spec/input-configurations.md#deflate-inputs) | — | [Start: bound and header review](progress.md#readiness-deflatebound-z) |
| <a id="target-zlibf-spec-public-goal-deflatebound"></a>[deflateBound](../ZlibF/Spec/Public/Streams.lean#L114) | Not proved / Not proved | [Contract](../docs/spec/api/deflate-stream.md#deflatebound); [input range](spec/input-configurations.md#deflate-inputs) | — | [Start: bound and header review](progress.md#readiness-deflatebound-z) |
| <a id="target-zlibf-spec-public-goal-deflateprime"></a>[deflatePrime](../ZlibF/Spec/Public/Streams.lean#L124) | Not proved / Not proved | [Contract](../docs/spec/api/deflate-stream.md#deflateprime); [input range](spec/input-configurations.md#deflate-inputs) | — | [Start: compaction and bits](progress.md#readiness-deflateprime) |
| <a id="target-zlibf-spec-public-goal-deflateparams"></a>[deflateParams](../ZlibF/Spec/Public/Streams.lean#L142) | Not proved / Not proved | [Contract](../docs/spec/api/deflate-stream.md#deflateparams); [input range](spec/input-configurations.md#deflate-inputs) | — | [Needs: block flush and parameter state](progress.md#readiness-deflateparams) |

<a id="group-back"></a>

## Callback decoding

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-inflatebackinit"></a>[inflateBackInit_](../ZlibF/Spec/Public/Back.lean#L22) | All stated inputs / Registered proof | [Contract](../docs/spec/api/inflate-back.md#inflatebackinit_); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.InflateBackInitProof.back_init_public](../ZlibF/Proof/public-infback-init.lean#L135) | — |
| <a id="target-zlibf-spec-public-goal-inflateback"></a>[inflateBack](../ZlibF/Spec/Public/Back.lean#L115) | Not proved / Not proved | [Contract](../docs/spec/api/inflate-back.md#inflateback); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: tables, window and callbacks](progress.md#readiness-inflateback) |
| <a id="target-zlibf-spec-public-goal-inflatebackend"></a>[inflateBackEnd](../ZlibF/Spec/Public/Back.lean#L142) | All stated inputs / Registered proof | [Contract](../docs/spec/api/inflate-back.md#inflatebackend); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.InflateBackEndProof.back_end_public](../ZlibF/Proof/public-infback-end.lean#L20) | — |

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
| <a id="target-zlibf-spec-public-goal-gzoffset64"></a>[gzoffset64](../ZlibF/Spec/Public/GzControl.lean#L53) | All stated inputs / Registered proof | [Contract](../docs/spec/api/gz-file.md#gzoffset64); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.OffsetProof.gzoffset64_public_goal](../ZlibF/Proof/public-gz-offset.lean#L199) | — |
| <a id="target-zlibf-spec-public-goal-gzoffset"></a>[gzoffset](../ZlibF/Spec/Public/GzControl.lean#L56) | All stated inputs / Registered proof | [Contract](../docs/spec/api/gz-file.md#gzoffset); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.OffsetProof.gzoffset_public_goal](../ZlibF/Proof/public-gz-offset.lean#L211) | — |
| <a id="target-zlibf-spec-public-goal-gzerror"></a>[gzerror](../ZlibF/Spec/Public/GzControl.lean#L63) | All stated inputs / Registered proof | [Contract](../docs/spec/api/gz-file.md#gzerror); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzErrorProof.gzerror](../ZlibF/Proof/public-gz-error.lean#L206) | — |
| <a id="target-zlibf-spec-public-goal-gzclearerr"></a>[gzclearerr](../ZlibF/Spec/Public/GzControl.lean#L74) | All stated inputs / Registered proof | [Contract](../docs/spec/api/gz-file.md#gzclearerr); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.gzclearerr](../ZlibF/Proof/gzlib.c.public-clearerr.lean#L28) | — |
| <a id="target-zlibf-spec-public-goal-gzrewind"></a>[gzrewind](../ZlibF/Spec/Public/GzControl.lean#L91) | All stated inputs / Registered proof | [Contract](../docs/spec/api/gz-file.md#gzrewind); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzRewindProof.rewind_public](../ZlibF/Proof/public-gz-rewind.lean#L67) | — |
| <a id="target-zlibf-spec-public-goal-gzseek64"></a>[gzseek64](../ZlibF/Spec/Public/GzControl.lean#L116) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzseek64); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: seek and history](progress.md#readiness-gzseek64) |
| <a id="target-zlibf-spec-public-goal-gzseek"></a>[gzseek](../ZlibF/Spec/Public/GzControl.lean#L119) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzseek); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: seek and history](progress.md#readiness-gzseek64) |
| <a id="target-zlibf-spec-public-goal-gzopen"></a>[gzopen](../ZlibF/Spec/Public/GzOpen.lean#L61) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzopen); [input range](spec/input-configurations.md#entry-inputs) | — | [Start: open and cleanup](progress.md#readiness-gzopen) |
| <a id="target-zlibf-spec-public-goal-gzopen64"></a>[gzopen64](../ZlibF/Spec/Public/GzOpen.lean#L65) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzopen64); [input range](spec/input-configurations.md#entry-inputs) | — | [Start: open and cleanup](progress.md#readiness-gzopen) |
| <a id="target-zlibf-spec-public-goal-gzdopen"></a>[gzdopen](../ZlibF/Spec/Public/GzOpen.lean#L70) | All stated inputs / Registered proof | [Contract](../docs/spec/api/gz-file.md#gzdopen); [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Gzlib.Proofs.gzdopen_complete](../ZlibF/Proof/gzlib.c.dopen-complete.lean#L28) | — |
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
| <a id="target-zlibf-spec-public-goal-gzvprintf"></a>[gzvprintf](../ZlibF/Spec/Public/GzWrite.lean#L102) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzvprintf); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: writer path proofs](progress.md#readiness-gzwrite) |
| <a id="target-zlibf-spec-public-goal-gzprintf"></a>[gzprintf](../ZlibF/Spec/Public/GzWrite.lean#L106) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzprintf); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: writer path proofs](progress.md#readiness-gzwrite) |
| <a id="target-zlibf-spec-public-goal-gzflush"></a>[gzflush](../ZlibF/Spec/Public/GzWrite.lean#L111) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzflush); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: writer path proofs](progress.md#readiness-gzwrite) |
| <a id="target-zlibf-spec-public-goal-gzsetparams"></a>[gzsetparams](../ZlibF/Spec/Public/GzWrite.lean#L128) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzsetparams); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: writer path proofs](progress.md#readiness-gzwrite) |

<a id="group-buffers"></a>

## Whole-buffer operations

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-compress2-z"></a>[compress2_z](../ZlibF/Spec/Public/Utilities.lean#L44) | Not proved / Not proved | [Contract](../docs/spec/api/utility.md#compress2_z); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: compressor execution](progress.md#readiness-compress2-z) |
| <a id="target-zlibf-spec-public-goal-compress2"></a>[compress2](../ZlibF/Spec/Public/Utilities.lean#L49) | Not proved / Not proved | [Contract](../docs/spec/api/utility.md#compress2); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: compressor execution](progress.md#readiness-compress2-z) |
| <a id="target-zlibf-spec-public-goal-compress-z"></a>[compress_z](../ZlibF/Spec/Public/Utilities.lean#L56) | Not proved / Not proved | [Contract](../docs/spec/api/utility.md#compress_z); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: compressor execution](progress.md#readiness-compress2-z) |
| <a id="target-zlibf-spec-public-goal-compress"></a>[compress](../ZlibF/Spec/Public/Utilities.lean#L61) | Not proved / Not proved | [Contract](../docs/spec/api/utility.md#compress); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: compressor execution](progress.md#readiness-compress2-z) |
| <a id="target-zlibf-spec-public-goal-uncompress2-z"></a>[uncompress2_z](../ZlibF/Spec/Public/Utilities.lean#L108) | Not proved / Not proved | [Contract](../docs/spec/api/utility.md#uncompress2_z); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: decoder execution](progress.md#readiness-uncompress2-z) |
| <a id="target-zlibf-spec-public-goal-uncompress2"></a>[uncompress2](../ZlibF/Spec/Public/Utilities.lean#L112) | Not proved / Not proved | [Contract](../docs/spec/api/utility.md#uncompress2); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: decoder execution](progress.md#readiness-uncompress2-z) |
| <a id="target-zlibf-spec-public-goal-uncompress-z"></a>[uncompress_z](../ZlibF/Spec/Public/Utilities.lean#L139) | Not proved / Not proved | [Contract](../docs/spec/api/utility.md#uncompress_z); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: decoder execution](progress.md#readiness-uncompress2-z) |
| <a id="target-zlibf-spec-public-goal-uncompress"></a>[uncompress](../ZlibF/Spec/Public/Utilities.lean#L143) | Not proved / Not proved | [Contract](../docs/spec/api/utility.md#uncompress); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: decoder execution](progress.md#readiness-uncompress2-z) |

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
| <a id="target-zlibf-spec-api-goal-gz-seek-read"></a>[gz_seek_read](../ZlibF/Spec/Api/Goals.lean#L221) | Not proved / Blocked | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | — [Blocker: Gzip seek mode](progress.md#gzip-seek-mode) | — |
| <a id="target-zlibf-spec-api-goal-compress-bound-value"></a>[compress_bound_value](../ZlibF/Spec/Api/Concrete.lean#L57) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.compress_bound_value](../ZlibF/Proof/Api/Concrete.lean#L57) | — |
| <a id="target-zlibf-spec-api-goal-compress2-z-first-alloc-failure"></a>[compress2_z_first_alloc_failure](../ZlibF/Spec/Api/Concrete.lean#L67) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.compress2_z_first_alloc_failure](../ZlibF/Proof/Api/CompressFailure.lean#L29) | — |
| <a id="target-zlibf-spec-api-goal-inflate-deferred-distance"></a>[inflate_deferred_distance](../ZlibF/Spec/Api/Inflate.lean#L267) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.inflate_deferred_distance](../ZlibF/Proof/Api/InflateCausality.lean#L244) | — |

<a id="group-lifecycle"></a>

## Lifecycles and call sequences

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-inflate-sequence"></a>[inflate_sequence](../ZlibF/Spec/Public/Sequences.lean#L211) | Not proved / Not proved | Exact target statement; [input range](spec/input-configurations.md#inflate-inputs) | — | [Needs: execution and format](progress.md#readiness-inflate-sequence) |
| <a id="target-zlibf-spec-public-goal-deflate-sequence"></a>[deflate_sequence](../ZlibF/Spec/Public/Sequences.lean#L225) | Not proved / Not proved | Exact target statement; [input range](spec/input-configurations.md#deflate-inputs) | — | [Needs: execution and format](progress.md#readiness-inflate-sequence) |
| <a id="target-zlibf-spec-public-goal-inflate-back-sequence"></a>[inflate_back_sequence](../ZlibF/Spec/Public/Sequences.lean#L252) | Not proved / Not proved | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: execution and format](progress.md#readiness-inflate-sequence) |
| <a id="target-zlibf-spec-public-goal-gz-sequence"></a>[gz_sequence](../ZlibF/Spec/Public/Sequences.lean#L264) | Not proved / Not proved | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: execution and format](progress.md#readiness-inflate-sequence) |
| <a id="target-zlibf-spec-public-goal-inflate-initialisation-domain"></a>[inflate_initialisation_domain](../ZlibF/Spec/Public/Domains.lean#L24) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.InflateInit.inflate_initialisation_domain_public](../ZlibF/Proof/public-inflate-init.lean#L263) | — |
| <a id="target-zlibf-spec-public-goal-deflate-initialisation-domain"></a>[deflate_initialisation_domain](../ZlibF/Spec/Public/Domains.lean#L37) | Not proved / Not proved | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | — | [Start: init and allocation](progress.md#readiness-deflateinit2) |
| <a id="target-zlibf-spec-public-goal-inflate-back-initialisation-domain"></a>[inflate_back_initialisation_domain](../ZlibF/Spec/Public/Domains.lean#L53) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.InflateBackInitProof.back_init_domain_public](../ZlibF/Proof/public-infback-init.lean#L230) | — |
| <a id="target-zlibf-spec-public-goal-gz-initialisation-domain"></a>[gz_initialisation_domain](../ZlibF/Spec/Public/Domains.lean#L77) | Not proved / Not proved | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | — | [Start: open and cleanup](progress.md#readiness-gzopen) |

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
| [crc32_z_all_byte_views](#target-zlib-crc32-spec-byteviews-goal-crc32-z-all-byte-views) | [crc32_z](#target-zlibf-spec-public-goal-crc32-z) |
| [actual_body_preserves_origin](#target-zlib-inffast-spec-bodyorigin-goal-actual-body-preserves-origin) | [actual_fast_preserves_origin](#target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin) |
| [actual_distance_block_preserves_origin](#target-zlib-inffast-spec-distanceorigin-goal-actual-distance-block-preserves-origin) | [actual_body_preserves_origin](#target-zlib-inffast-spec-bodyorigin-goal-actual-body-preserves-origin) |
| [actual_distance_refines_lz77](#target-zlib-inffast-spec-distanceresult-goal-actual-distance-refines-lz77) | [actual_body_refines_token](#target-zlib-inffast-spec-bodytoken-goal-actual-body-refines-token) |
| [distance_lookup_matches_format](#target-zlib-inffast-spec-distancesemantics-goal-distance-lookup-matches-format) | [actual_distance_refines_lz77](#target-zlib-inffast-spec-distanceresult-goal-actual-distance-refines-lz77) |
| [fast_safe](#target-zlib-inffast-spec-goal-fast-safe) | [actual_fast_preserves_origin](#target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin) |
| [step_safe](#target-zlib-inffast-spec-goal-step-safe) | [actual_body_refines_token](#target-zlib-inffast-spec-bodytoken-goal-actual-body-refines-token) |
| [step_safe](#target-zlib-inffast-spec-goal-step-safe) | [fast_safe](#target-zlib-inffast-spec-goal-fast-safe) |
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
| [short_rejected_leaf_stays_invalid](#target-zlib-inftrees-spec-decodetablestability-goal-short-rejected-leaf-stays-invalid) | [distance_lookup_matches_format](#target-zlib-inffast-spec-distancesemantics-goal-distance-lookup-matches-format) |
| [short_rejected_leaf_stays_invalid](#target-zlib-inftrees-spec-decodetablestability-goal-short-rejected-leaf-stays-invalid) | [length_lookup_matches_format](#target-zlib-inffast-spec-lengthsemantics-goal-length-lookup-matches-format) |
| [inflate_table_content](#target-zlib-inftrees-spec-goal-inflate-table-content) | [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe) |
| [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe) | [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent) |
| [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe) | [constructor_root_bits](#target-zlib-inftrees-spec-roottable-goal-constructor-root-bits) |
| [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent) | [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant) |
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
| [inflateBackInit_](#target-zlibf-spec-public-goal-inflatebackinit) | [inflate_back_initialisation_domain](#target-zlibf-spec-public-goal-inflate-back-initialisation-domain) |

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
| [compress2_z](#target-zlibf-spec-public-goal-compress2-z) | [compress2_z_first_alloc_failure](#target-zlibf-spec-api-goal-compress2-z-first-alloc-failure) |
| [compressBound](#target-zlibf-spec-public-goal-compressbound) | [compress_bound_value](#target-zlibf-spec-api-goal-compress-bound-value) |
| [compressBound_z](#target-zlibf-spec-public-goal-compressbound-z) | [compress_bound_value](#target-zlibf-spec-api-goal-compress-bound-value) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [crc32_all_byte_views](#target-zlib-crc32-spec-byteviews-goal-crc32-all-byte-views) |
| [crc32_z](#target-zlibf-spec-public-goal-crc32-z) | [crc32_z_all_byte_views](#target-zlib-crc32-spec-byteviews-goal-crc32-z-all-byte-views) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [deflate_initialisation_domain](#target-zlibf-spec-public-goal-deflate-initialisation-domain) |
| [gzclose](#target-zlibf-spec-public-goal-gzclose) | [gz_sequence](#target-zlibf-spec-public-goal-gz-sequence) |
| [gzflush](#target-zlibf-spec-public-goal-gzflush) | [gz_sequence](#target-zlibf-spec-public-goal-gz-sequence) |
| [gzfread](#target-zlibf-spec-public-goal-gzfread) | [gz_sequence](#target-zlibf-spec-public-goal-gz-sequence) |
| [gzfwrite](#target-zlibf-spec-public-goal-gzfwrite) | [gz_sequence](#target-zlibf-spec-public-goal-gz-sequence) |
| [gzgetc](#target-zlibf-spec-public-goal-gzgetc) | [gz_sequence](#target-zlibf-spec-public-goal-gz-sequence) |
| [gzgets](#target-zlibf-spec-public-goal-gzgets) | [gz_sequence](#target-zlibf-spec-public-goal-gz-sequence) |
| [gzopen](#target-zlibf-spec-public-goal-gzopen) | [gz_initialisation_domain](#target-zlibf-spec-public-goal-gz-initialisation-domain) |
| [gzread](#target-zlibf-spec-public-goal-gzread) | [gz_sequence](#target-zlibf-spec-public-goal-gz-sequence) |
| [gzwrite](#target-zlibf-spec-public-goal-gzwrite) | [gz_sequence](#target-zlibf-spec-public-goal-gz-sequence) |
| [inflateBack](#target-zlibf-spec-public-goal-inflateback) | [inflate_back_sequence](#target-zlibf-spec-public-goal-inflate-back-sequence) |
| [inflateBackEnd](#target-zlibf-spec-public-goal-inflatebackend) | [inflate_back_sequence](#target-zlibf-spec-public-goal-inflate-back-sequence) |
| [inflateBackInit_](#target-zlibf-spec-public-goal-inflatebackinit) | [inflate_back_initialisation_domain](#target-zlibf-spec-public-goal-inflate-back-initialisation-domain) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [inflate_initialisation_domain](#target-zlibf-spec-public-goal-inflate-initialisation-domain) |

## Proof support relationships

These are observed theorem references grouped by source family. Groups carry no whole-file proof status.
Every direct grouped connection is retained here, including arrows reduced in the graph.

| Supporting source | Direct destinations |
| --- | --- |
| API-model lemmas | compress_bound_adequate, compress_roundtrip, deflate_bound_adequate, deflate_completes, deflate_full_flush_resync, deflate_valid, dict_roundtrip, gz_roundtrip, header_roundtrip, inflate_completes, inflate_decodes, inflate_deferred_distance, roundtrip, roundtrip_completes, deflateInit_, gzdopen, api-model proofs, deflate construction proofs, gzlib.c proofs, heap-free mathematics |
| ByteAddress proofs | first_aligned_offset, mask_refines_base_plus_offset, pointer_advance_preserves_low_bits |
| LibcBorrow proofs | inflate storage and bit proofs |
| actual_body_preserves_origin | inffast.c proofs |
| actual_distance_block_preserves_origin | inffast.c proofs |
| step_safe | inffast.c proofs |
| actual_copy_match_refines_lz77 | inffast.c proofs |
| actual_drop_preserves_origin | inffast.c proofs |
| actual_rollback_preserves_origin | inffast.c proofs |
| drop_preserves_origin | inffast.c proofs |
| pull_preserves_origin | inffast.c proofs |
| inflate_table_content | inftrees.c proofs |
| retained_history_agrees | format proofs |
| deflate_valid | api-model proofs |
| inflate_completes | api-model proofs |
| inflate_decodes | api-model proofs |
| inflateBackInit_ | public entry composition |
| adler32.c proofs | inflateSetDictionary, inflate entry composition, inflate storage and bit proofs, public entry composition |
| api-model proofs | output_copy_refines_lz77, retained_history_agrees, compress2_z_first_alloc_failure, compress_bound_adequate, compress_bound_value, compress_roundtrip, deflate_bound_adequate, deflate_completes, deflate_full_flush_resync, deflate_valid, dict_roundtrip, gz_roundtrip, header_roundtrip, inflate_completes, inflate_decodes, inflate_deferred_distance, roundtrip, roundtrip_completes, inflateCodesUsed, heap-free mathematics |
| crc32.c proofs | crc32_all_byte_views, crc32_z_all_byte_views, crc32, crc32_z, public entry composition |
| deflate construction proofs | deflateInit_ |
| deflate entry composition | deflateEnd, deflateGetDictionary, deflatePending, deflateReset, deflateResetKeep, deflateSetHeader, deflateTune, deflateUsed |
| deflate lifecycle proofs | deflateEnd, deflateGetDictionary, deflateInit_, deflatePending, deflateReset, deflateResetKeep, deflateSetHeader, deflateTune, deflateUsed, deflate construction proofs, deflate entry composition |
| deflate window and match proofs | deflate lifecycle proofs, gzlib.c proofs, inflate storage and bit proofs |
| format proofs | short_decode_table_leaf_sound, short_rejected_leaf_stays_invalid, compress_roundtrip, format_deterministic, format_prefix_free, header_roundtrip, inflate_completes, rejected_has_no_symbols, api-model proofs, heap-free mathematics, inffast.c proofs, inftrees.c proofs |
| gzfs proofs | gzlib.c proofs |
| gzlib.c proofs | gzclearerr, gzdopen, public entry composition |
| heap-free mathematics | match_array_refines_lz77, output_copy_refines_lz77, window_copy_refines_lz77, copy_back_compose, retained_history_agrees, window_distance_check_agrees, api-model proofs, gzlib.c proofs, inftrees.c proofs |
| infback.c proofs | inflateBackEnd, inflateBackInit_, public entry composition |
| inffast.c proofs | actual_body_preserves_origin, actual_body_refines_token, actual_fast_preserves_origin, actual_distance_block_preserves_origin, actual_distance_refines_lz77, distance_lookup_matches_format, fast_safe, step_safe, length_lookup_matches_format, actual_body_retains_selected_length, actual_copy_match_refines_lz77, match_array_refines_lz77, actual_drop_preserves_origin, actual_pull_preserves_origin, actual_rollback_preserves_origin, drop_preserves_origin, initial_origin, pull_preserves_origin, rollback_preserves_origin, output_copy_refines_lz77, heap-free mathematics, inftrees.c proofs |
| inffixed.h.fast-flags proofs | fixed_tables_have_fast_leaf_flags |
| inflate entry composition | inflateEnd, inflateGetDictionary, inflateGetHeader, inflateInit_, inflateMark, inflatePrime, inflateReset, inflateReset2, inflateSetDictionary, inflateSyncPoint, inflateUndermine, inflateValidate, inflate_initialisation_domain |
| inflate storage and bit proofs | deflateReset, deflateResetKeep, inflateBackEnd, inflateBackInit_, inflateEnd, inflateGetDictionary, inflateInit_, inflateMark, inflateReset, inflateReset2, inflateResetKeep, inflateSetDictionary, inflateSyncPoint, inflateUndermine, inflateValidate, api-model proofs, infback.c proofs, inflate entry composition, public entry composition |
| inftrees.c proofs | decode_table_matches_format, short_decode_table_leaf_sound, decode_table_leaf_sound, decode_table_read_preserved, constructor_establishes_decode_table_invariant, decode_table_invariant_of_prefix, constructor_establishes_query_stability, short_rejected_leaf_stays_invalid, constructor_establishes_fast_leaf_flags, leaf_classification_agrees, inflate_table_content, inflate_table_decoder_safe, inflate_table_read_extent, constructor_root_bits, constructor_subtable_bits, heap-free mathematics |
| public entry composition | adler32_combine, adler32_combine64, adler32_z, compressBound, compressBound_z, crc32_combine, crc32_combine64, crc32_combine_gen, crc32_combine_gen64, crc32_combine_op, get_crc_table, gzbuffer, gzdopen, gzeof, gzerror, gzoffset, gzoffset64, gzrewind, inflateBackEnd, inflateBackInit_, inflate_back_initialisation_domain, zError, zlibVersion, adler32.c proofs, gzlib.c proofs |
| runtime object and arithmetic lemmas | byte_modifies_preserve_bases, byte_stores_preserve_bases, every_layout_is_representable, LibcBorrow proofs, crc32_all_byte_views, crc32_z_all_byte_views, actual_body_preserves_origin, actual_body_refines_token, actual_fast_preserves_origin, actual_distance_block_preserves_origin, actual_distance_refines_lz77, fast_safe, step_safe, actual_body_retains_selected_length, actual_copy_match_refines_lz77, actual_pull_preserves_origin, actual_rollback_preserves_origin, decode_table_classifies_input, decode_table_matches_format, short_decode_table_leaf_sound, decode_table_leaf_sound, constructor_establishes_decode_table_invariant, constructor_establishes_query_stability, constructor_establishes_fast_leaf_flags, inflate_table_content, inflate_table_decoder_safe, inflate_table_read_extent, constructor_root_bits, constructor_subtable_bits, compress2_z_first_alloc_failure, adler32, adler32_z, crc32, crc32_z, deflateEnd, deflateGetDictionary, deflateInit_, deflatePending, deflateReset, deflateResetKeep, deflateSetHeader, deflateTune, deflateUsed, get_crc_table, gzclearerr, gzdopen, gzerror, gzoffset, gzoffset64, gzrewind, inflateBackEnd, inflateBackInit_, inflateCodesUsed, inflateEnd, inflateGetDictionary, inflateGetHeader, inflateInit_, inflateMark, inflatePrime, inflateReset, inflateReset2, inflateResetKeep, inflateSetDictionary, inflateSyncPoint, inflateUndermine, inflateValidate, inflate_back_initialisation_domain, inflate_initialisation_domain, zError, zlibVersion, adler32.c proofs, api-model proofs, crc32.c proofs, deflate construction proofs, deflate entry composition, deflate lifecycle proofs, deflate window and match proofs, gzfs proofs, gzlib.c proofs, infback.c proofs, inffast.c proofs, inflate entry composition, inflate storage and bit proofs, inftrees.c proofs, public entry composition, tree construction and emission proofs, zutil.c proofs |
| specification lemmas | every_existing_heap_accepts_layout, actual_body_refines_token, distance_lookup_matches_format, length_lookup_matches_format, actual_body_retains_selected_length, drop_preserves_origin, pull_preserves_origin, rollback_preserves_origin, decode_table_invariant_of_prefix, short_rejected_leaf_stays_invalid, gzdopen, gzlib.c proofs, inffast.c proofs |
| tree construction and emission proofs | deflate construction proofs, deflate lifecycle proofs |
| zutil.c proofs | inflate_table_content, deflate construction proofs, deflate lifecycle proofs, inflate entry composition, inflate storage and bit proofs, inftrees.c proofs |

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
| [Zlib.Crc32.Proofs.crc32_correct](../ZlibF/Proof/crc32.c.lean#L2227) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_null](../ZlibF/Proof/crc32.c.lean#L2223) | [crc32](#target-zlibf-spec-public-goal-crc32) |
| [Zlib.Crc32.Proofs.crc32_safe](../ZlibF/Proof/crc32.c.lean#L2236) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_z_correct](../ZlibF/Proof/crc32.c.lean#L2203) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_z_null](../ZlibF/Proof/crc32.c.lean#L2190) | [crc32](#target-zlibf-spec-public-goal-crc32), [crc32_z](#target-zlibf-spec-public-goal-crc32-z) |
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
| [Zlib.Deflate.Engine.Proofs.INSERT_STRING_ok](../ZlibF/Proof/deflate.c.engine.macros.lean#L177) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.UPDATE_HASH_ok](../ZlibF/Proof/deflate.c.engine.macros.lean#L147) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.chain_ok_of_chains](../ZlibF/Proof/deflate.c.engine.chains.lean#L194) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.chains_insert](../ZlibF/Proof/deflate.c.engine.chains.lean#L76) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.chains_slide](../ZlibF/Proof/deflate.c.engine.chains.lean#L138) | No fixed-target composition recorded |
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
| [Zlib.Deflate.Engine.Proofs.form_init](../ZlibF/Proof/deflate.c.engine.hash.lean#L126) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.generic_default_public_contract](../ZlibF/Proof/deflate.c.default-public-contract.lean#L19) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.generic_default_request_trace_witness](../ZlibF/Proof/deflate.c.default-public-contract.lean#L62) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.hkey_third](../ZlibF/Proof/deflate.c.engine.hash.lean#L139) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.lm_body_ok](../ZlibF/Proof/deflate.c.engine.lmbody.lean#L102) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.lm_inner_loop](../ZlibF/Proof/deflate.c.engine.lminner.lean#L36) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.lm_loop_ok](../ZlibF/Proof/deflate.c.engine.lmmain.lean#L77) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.longest_match_ok](../ZlibF/Proof/deflate.c.engine.lmmain.lean#L212) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.matchLen_agree](../ZlibF/Proof/deflate.c.engine.match.lean#L100) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.memory_fast_initialization_witness](../ZlibF/Proof/deflate.c.engine.memory-fast-initial.lean#L50) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.memory_fast_observed_initialization](../ZlibF/Proof/deflate.c.engine.memory-fast-observed-initial.lean#L49) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.memory_slow_initialized_state](../ZlibF/Proof/deflate.c.engine.memory-slow-initialized-state.lean#L62) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.memory_slow_observed_initialization](../ZlibF/Proof/deflate.c.engine.memory-slow-observed-initial.lean#L55) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.public_common_first_finish_encoding_input](../ZlibF/Proof/deflate.c.engine.common-first-finish-encoding.lean#L16) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.public_common_first_finish_encoding_state](../ZlibF/Proof/deflate.c.engine.common-first-finish-state.lean#L15) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.public_common_first_no_flush_encoding_input](../ZlibF/Proof/deflate.c.engine.common-first-input.lean#L16) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.public_common_first_no_flush_encoding_state](../ZlibF/Proof/deflate.c.engine.common-first-encoding-state.lean#L14) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.putShortMSB_ok](../ZlibF/Proof/deflate.c.engine.macros.lean#L119) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.put_byte_ok](../ZlibF/Proof/deflate.c.engine.macros.lean#L96) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.read_buf_ok](../ZlibF/Proof/deflate.c.engine.readbuf.lean#L99) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.read_buf_zero](../ZlibF/Proof/deflate.c.engine.readbuf.lean#L75) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.slide_copy](../ZlibF/Proof/deflate.c.engine.window.lean#L52) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.slide_hash_ok](../ZlibF/Proof/deflate.c.engine.slide.lean#L166) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.upd3_indep](../ZlibF/Proof/deflate.c.engine.hash.lean#L45) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.MemoryInit.public_valid_memory_init_lifecycle](../ZlibF/Proof/deflate.c.init.memory-lifecycle.lean#L13) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.MemoryInit.public_valid_memory_init_total](../ZlibF/Proof/deflate.c.init.memory-total.lean#L16) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateBound_nostate](../ZlibF/Proof/deflate.c.life.bound.lean#L330) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateBound_safe](../ZlibF/Proof/deflate.c.life.bound.lean#L319) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateBound_z_nostate](../ZlibF/Proof/deflate.c.life.bound.lean#L312) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateBound_z_safe](../ZlibF/Proof/deflate.c.life.bound.lean#L302) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateEnd_reject](../ZlibF/Proof/deflate.c.life.end.lean#L321) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateEnd_safe](../ZlibF/Proof/deflate.c.life.end.lean#L270) | [deflateEnd](#target-zlibf-spec-public-goal-deflateend) |
| [Zlib.Deflate.Proofs.deflatePending_reject](../ZlibF/Proof/deflate.c.life.check.lean#L173) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflatePending_safe](../ZlibF/Proof/deflate.c.life.check.lean#L146) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflatePrime_invalid_count](../ZlibF/Proof/deflate.c.prime.lean#L24) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflatePrime_refused](../ZlibF/Proof/deflate.c.prime.lean#L15) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateResetKeep_reject](../ZlibF/Proof/deflate.c.life.reset.lean#L424) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateResetKeep_safe](../ZlibF/Proof/deflate.c.life.reset.lean#L367) | [deflateReset](#target-zlibf-spec-public-goal-deflatereset), [deflateResetKeep](#target-zlibf-spec-public-goal-deflateresetkeep) |
| [Zlib.Deflate.Proofs.deflateReset_reject](../ZlibF/Proof/deflate.c.life.reset.lean#L430) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateReset_safe](../ZlibF/Proof/deflate.c.life.reset.lean#L401) | [deflateReset](#target-zlibf-spec-public-goal-deflatereset) |
| [Zlib.Deflate.Proofs.deflateSetHeader_not_gzip](../ZlibF/Proof/deflate.c.life.check.lean#L92) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateSetHeader_reject](../ZlibF/Proof/deflate.c.life.check.lean#L98) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateSetHeader_safe](../ZlibF/Proof/deflate.c.life.check.lean#L83) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateStateCheck_total](../ZlibF/Proof/deflate.c.base.lean#L731) | [deflatePending](#target-zlibf-spec-public-goal-deflatepending), [deflateSetHeader](#target-zlibf-spec-public-goal-deflatesetheader), [deflateTune](#target-zlibf-spec-public-goal-deflatetune), [deflateUsed](#target-zlibf-spec-public-goal-deflateused) |
| [Zlib.Deflate.Proofs.deflateTune_reject](../ZlibF/Proof/deflate.c.life.check.lean#L54) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateTune_safe](../ZlibF/Proof/deflate.c.life.check.lean#L44) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateUsed_reject](../ZlibF/Proof/deflate.c.life.check.lean#L119) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateUsed_safe](../ZlibF/Proof/deflate.c.life.check.lean#L113) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.lm_init_safe](../ZlibF/Proof/deflate.c.life.reset.lean#L151) | [deflateReset](#target-zlibf-spec-public-goal-deflatereset) |
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
| [Zlib.Gzlib.Proofs.gzoffset64_null](../ZlibF/Proof/gzlib.c.rewind.lean#L110) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzoffset64_run](../ZlibF/Proof/gzlib.c.rewind.lean#L114) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzoffset_eq](../ZlibF/Proof/gzlib.c.rewind.lean#L136) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzopen64_alloc_failure](../ZlibF/Proof/gzlib.c.open.lean#L48) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzopen64_null](../ZlibF/Proof/gzlib.c.open.lean#L29) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzopen_alloc_failure](../ZlibF/Proof/gzlib.c.open.lean#L42) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzopen_null](../ZlibF/Proof/gzlib.c.open.lean#L24) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzrewind_null](../ZlibF/Proof/gzlib.c.rewind.lean#L80) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzrewind_spec](../ZlibF/Proof/gzlib.c.rewind.lean#L85) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzseek64_cur_negpos_ub](../ZlibF/Proof/gzlib.c.seek.lean#L867) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzseek64_dangling_next_ub](../ZlibF/Proof/gzlib.c.seek.lean#L952) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzseek64_head](../ZlibF/Proof/gzlib.c.seek.lean#L177) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzseek64_null](../ZlibF/Proof/gzlib.c.seek.lean#L805) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzseek64_refuse](../ZlibF/Proof/gzlib.c.seek.lean#L837) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzseek64_safe](../ZlibF/Proof/gzlib.c.seek.lean#L812) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzseek64_set_negpos_ub](../ZlibF/Proof/gzlib.c.seek.lean#L889) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzseek64_write_run](../ZlibF/Proof/gzlib.c.seek.lean#L232) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzseek_eq](../ZlibF/Proof/gzlib.c.seek.lean#L850) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gztell64_null](../ZlibF/Proof/gzlib.c.simple.lean#L122) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gztell64_spec](../ZlibF/Proof/gzlib.c.simple.lean#L143) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gztell_null](../ZlibF/Proof/gzlib.c.simple.lean#L154) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gztell_run](../ZlibF/Proof/gzlib.c.simple.lean#L148) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.seekTail_back](../ZlibF/Proof/gzlib.c.seek.lean#L475) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.seekTail_copy](../ZlibF/Proof/gzlib.c.seek.lean#L315) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.seekTail_copy_ub](../ZlibF/Proof/gzlib.c.seek.lean#L962) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.seekTail_dangling_ub](../ZlibF/Proof/gzlib.c.seek.lean#L919) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.seekTail_fwd](../ZlibF/Proof/gzlib.c.seek.lean#L376) | No fixed-target composition recorded |
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
| [Zlib.Inffast.Proofs.distfix_tableSafe](../ZlibF/Proof/inffast.c.tableok.lean#L82) | No fixed-target composition recorded |
| [Zlib.Inffast.Proofs.lenfix_tableSafe](../ZlibF/Proof/inffast.c.tableok.lean#L75) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.BITS_run](../ZlibF/Proof/inflate.c.main.macros.lean#L224) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.BITS_toNat](../ZlibF/Proof/inflate.c.main.macros.lean#L234) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.BYTEBITS_inv](../ZlibF/Proof/inflate.c.main.macros.lean#L293) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.BYTEBITS_run](../ZlibF/Proof/inflate.c.main.macros.lean#L283) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.DROPBITS_inv](../ZlibF/Proof/inflate.c.main.macros.lean#L251) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.DROPBITS_run](../ZlibF/Proof/inflate.c.main.macros.lean#L241) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.INITBITS_inv](../ZlibF/Proof/inflate.c.main.macros.lean#L304) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.NEEDBITS_run](../ZlibF/Proof/inflate.c.main.macros.lean#L150) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.PULLBYTE_succ](../ZlibF/Proof/inflate.c.main.macros.lean#L89) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.PULLBYTE_zero](../ZlibF/Proof/inflate.c.main.macros.lean#L44) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.UPDATE_CHECK_run](../ZlibF/Proof/inflate.c.main.check.lean#L21) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.bytesBits_eq_bytesToBits](../ZlibF/Proof/inflate.c.main.bits.lean#L107) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateCodesUsed_spec](../ZlibF/Proof/inflate.c.misc.lean#L180) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateEnd_safe](../ZlibF/Proof/inflate.c.end.lean#L119) | [inflateEnd](#target-zlibf-spec-public-goal-inflateend) |
| [Zlib.Inflate.Proofs.inflateGetDictionary_spec](../ZlibF/Proof/inflate.c.dict.lean#L82) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateGetHeader_check](../ZlibF/Proof/inflate.c.hdr.lean#L54) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateGetHeader_nogzip](../ZlibF/Proof/inflate.c.hdr.lean#L64) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateGetHeader_null_faults](../ZlibF/Proof/inflate.c.hdr.lean#L114) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateGetHeader_ok](../ZlibF/Proof/inflate.c.hdr.lean#L80) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateInit2_ok](../ZlibF/Proof/inflate.c.start.lean#L237) | [inflateInit_](#target-zlibf-spec-public-goal-inflateinit), [inflate_initialisation_domain](#target-zlibf-spec-public-goal-inflate-initialisation-domain) |
| [Zlib.Inflate.Proofs.inflateInit2_safe](../ZlibF/Proof/inflate.c.start.lean#L324) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateInit__ok](../ZlibF/Proof/inflate.c.hdr.lean#L160) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateInit__safe](../ZlibF/Proof/inflate.c.hdr.lean#L134) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateMark_spec](../ZlibF/Proof/inflate.c.misc.lean#L140) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflatePrime_spec](../ZlibF/Proof/inflate.c.misc2.lean#L28) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateReset2_safe](../ZlibF/Proof/inflate.c.init.lean#L395) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateResetKeep_safe](../ZlibF/Proof/inflate.c.base.lean#L521) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateReset_safe](../ZlibF/Proof/inflate.c.reset.lean#L160) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateSetDictionary_dataerr](../ZlibF/Proof/inflate.c.dict.lean#L222) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateSetDictionary_safe](../ZlibF/Proof/inflate.c.dict.lean#L146) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateSetDictionary_streamerr](../ZlibF/Proof/inflate.c.dict.lean#L209) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateStateCheck_total](../ZlibF/Proof/inflate.c.base.lean#L445) | [inflateCodesUsed](#target-zlibf-spec-public-goal-inflatecodesused), [inflateEnd](#target-zlibf-spec-public-goal-inflateend), [inflateMark](#target-zlibf-spec-public-goal-inflatemark), [inflatePrime](#target-zlibf-spec-public-goal-inflateprime), [inflateSyncPoint](#target-zlibf-spec-public-goal-inflatesyncpoint), [inflateUndermine](#target-zlibf-spec-public-goal-inflateundermine), [inflateValidate](#target-zlibf-spec-public-goal-inflatevalidate) |
| [Zlib.Inflate.Proofs.inflateSyncPoint_spec](../ZlibF/Proof/inflate.c.misc.lean#L121) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateSync_buf_error](../ZlibF/Proof/inflate.c.sync2.lean#L131) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateSync_check](../ZlibF/Proof/inflate.c.sync2.lean#L113) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateUndermine_safe](../ZlibF/Proof/inflate.c.misc.lean#L109) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateValidate_safe](../ZlibF/Proof/inflate.c.misc.lean#L95) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_CHECK_nowrap](../ZlibF/Proof/inflate.c.main.check.lean#L137) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_CHECK_run](../ZlibF/Proof/inflate.c.main.check.lean#L157) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_COPY__eq](../ZlibF/Proof/inflate.c.main.stored2.lean#L82) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_COPY_done](../ZlibF/Proof/inflate.c.main.stored.lean#L22) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_COPY_leave](../ZlibF/Proof/inflate.c.main.stored2.lean#L75) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_COPY_run](../ZlibF/Proof/inflate.c.main.stored2.lean#L57) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_DONE_run](../ZlibF/Proof/inflate.c.main.simple.lean#L25) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_LENGTH_run](../ZlibF/Proof/inflate.c.main.check.lean#L80) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_LENGTH_skip](../ZlibF/Proof/inflate.c.main.check.lean#L66) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_LENLENS_eq](../ZlibF/Proof/inflate.c.main.table3.lean#L82) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_LENLENS_run](../ZlibF/Proof/inflate.c.main.table6.lean#L41) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_LIT_full](../ZlibF/Proof/inflate.c.main.simple.lean#L29) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_LIT_run](../ZlibF/Proof/inflate.c.main.simple.lean#L37) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_STORED_bad](../ZlibF/Proof/inflate.c.main.stored2.lean#L97) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_STORED_ok](../ZlibF/Proof/inflate.c.main.stored2.lean#L116) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_STORED_wait](../ZlibF/Proof/inflate.c.main.stored2.lean#L88) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_TABLE_run](../ZlibF/Proof/inflate.c.main.table.lean#L52) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_TYPEDO_head](../ZlibF/Proof/inflate.c.main.type.lean#L61) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_TYPEDO_last](../ZlibF/Proof/inflate.c.main.type.lean#L26) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_TYPEDO_wait](../ZlibF/Proof/inflate.c.main.type.lean#L37) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_TYPE_go](../ZlibF/Proof/inflate.c.main.type.lean#L19) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_TYPE_leave](../ZlibF/Proof/inflate.c.main.type.lean#L11) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.ll1_run](../ZlibF/Proof/inflate.c.main.table4.lean#L69) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.llBody_run](../ZlibF/Proof/inflate.c.main.table3.lean#L95) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.llTail_run](../ZlibF/Proof/inflate.c.main.table5.lean#L46) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.lzBody_run](../ZlibF/Proof/inflate.c.main.table4.lean#L225) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.lz_run](../ZlibF/Proof/inflate.c.main.table4.lean#L244) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.noRet_NEEDBITS](../ZlibF/Proof/inflate.c.main.table2.lean#L321) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.ring_spec](../ZlibF/Proof/inflate.c.ring.lean#L116) | [inflateSetDictionary](#target-zlibf-spec-public-goal-inflatesetdictionary) |
| [Zlib.Inflate.Proofs.syncDone_good](../ZlibF/Proof/inflate.c.sync2.lean#L372) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.syncDone_owns](../ZlibF/Proof/inflate.c.sync2.lean#L423) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.syncDone_run](../ZlibF/Proof/inflate.c.sync2.lean#L248) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.syncScan_found_iff](../ZlibF/Proof/inflate.c.sync.lean#L342) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.syncScan_spec](../ZlibF/Proof/inflate.c.sync.lean#L300) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.syncStep_spec](../ZlibF/Proof/inflate.c.sync.lean#L202) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.syncTail_run](../ZlibF/Proof/inflate.c.sync2.lean#L543) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.syncsearch_null](../ZlibF/Proof/inflate.c.sync.lean#L450) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.syncsearch_run](../ZlibF/Proof/inflate.c.sync.lean#L381) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.syncsearch_spec](../ZlibF/Proof/inflate.c.sync.lean#L485) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.typedoTail_bad](../ZlibF/Proof/inflate.c.main.type.lean#L154) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.typedoTail_fixed](../ZlibF/Proof/inflate.c.main.type.lean#L116) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.typedoTail_fixed_trees](../ZlibF/Proof/inflate.c.main.type.lean#L132) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.typedoTail_stored](../ZlibF/Proof/inflate.c.main.type.lean#L92) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.typedoTail_table](../ZlibF/Proof/inflate.c.main.type.lean#L104) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.updatewindow_ring](../ZlibF/Proof/inflate.c.ring.lean#L197) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.updatewindow_safe](../ZlibF/Proof/inflate.c.uw.lean#L558) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.uwPost_counts](../ZlibF/Proof/inflate.c.ring.lean#L170) | [inflateSetDictionary](#target-zlibf-spec-public-goal-inflatesetdictionary) |
| [Zlib.Inflate.Proofs.uw_null_ok](../ZlibF/Proof/inflate.c.uw.lean#L492) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.uw_post](../ZlibF/Proof/inflate.c.uw.lean#L423) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.xwhileBrk_run](../ZlibF/Proof/inflate.c.main.xloop.lean#L36) | No fixed-target composition recorded |
| [Zlib.Inflate.Witness.init_witness](../ZlibF/Proof/inflate.c.witness.lean#L50) | No fixed-target composition recorded |
| [Zlib.Inftrees.Proofs.Cover.bits_add_drop](../ZlibF/Proof/inftrees.c.cover.leaf.lean#L80) | No fixed-target composition recorded |
| [Zlib.Inftrees.Proofs.Cover.cell_lt_fn](../ZlibF/Proof/inftrees.c.cover.fn.lean#L210) | No fixed-target composition recorded |
| [Zlib.Inftrees.Proofs.Cover.distLeaf_of](../ZlibF/Proof/inftrees.c.cover.leaf.lean#L56) | [decode_table_matches_format](#target-zlib-inftrees-spec-decodesemantics-goal-decode-table-matches-format), [decode_table_leaf_sound](#target-zlib-inftrees-spec-decodesoundness-goal-decode-table-leaf-sound), [constructor_establishes_query_stability](#target-zlib-inftrees-spec-decodetablestability-goal-constructor-establishes-query-stability), [constructor_establishes_fast_leaf_flags](#target-zlib-inftrees-spec-fasttableflags-goal-constructor-establishes-fast-leaf-flags), [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe), [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent), [constructor_subtable_bits](#target-zlib-inftrees-spec-subtable-goal-constructor-subtable-bits) |
| [Zlib.Inftrees.Proofs.Cover.group_cover](../ZlibF/Proof/inftrees.c.cover.group.lean#L64) | [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe), [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent), [constructor_subtable_bits](#target-zlib-inftrees-spec-subtable-goal-constructor-subtable-bits) |
| [Zlib.Inftrees.Proofs.Cover.group_cover_fn](../ZlibF/Proof/inftrees.c.cover.fn.lean#L163) | No fixed-target composition recorded |
| [Zlib.Inftrees.Proofs.Cover.group_cover_idx](../ZlibF/Proof/inftrees.c.cover.group.lean#L161) | [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe), [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent), [constructor_subtable_bits](#target-zlib-inftrees-spec-subtable-goal-constructor-subtable-bits) |
| [Zlib.Inftrees.Proofs.Cover.group_cover_idx_fn](../ZlibF/Proof/inftrees.c.cover.fn.lean#L185) | No fixed-target composition recorded |
| [Zlib.Inftrees.Proofs.Cover.invalid_leaf](../ZlibF/Proof/inftrees.c.cover.leaf.lean#L66) | [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe), [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent) |
| [Zlib.Inftrees.Proofs.Cover.lenLeaf_of](../ZlibF/Proof/inftrees.c.cover.leaf.lean#L40) | [decode_table_matches_format](#target-zlib-inftrees-spec-decodesemantics-goal-decode-table-matches-format), [decode_table_leaf_sound](#target-zlib-inftrees-spec-decodesoundness-goal-decode-table-leaf-sound), [constructor_establishes_query_stability](#target-zlib-inftrees-spec-decodetablestability-goal-constructor-establishes-query-stability), [constructor_establishes_fast_leaf_flags](#target-zlib-inftrees-spec-fasttableflags-goal-constructor-establishes-fast-leaf-flags), [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe), [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent), [constructor_subtable_bits](#target-zlib-inftrees-spec-subtable-goal-constructor-subtable-bits) |
| [Zlib.Inftrees.Proofs.Cover.root_cover](../ZlibF/Proof/inftrees.c.cover.root.lean#L90) | [decode_table_matches_format](#target-zlib-inftrees-spec-decodesemantics-goal-decode-table-matches-format), [short_decode_table_leaf_sound](#target-zlib-inftrees-spec-decodeshort-goal-short-decode-table-leaf-sound), [decode_table_leaf_sound](#target-zlib-inftrees-spec-decodesoundness-goal-decode-table-leaf-sound), [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant), [constructor_establishes_query_stability](#target-zlib-inftrees-spec-decodetablestability-goal-constructor-establishes-query-stability), [constructor_establishes_fast_leaf_flags](#target-zlib-inftrees-spec-fasttableflags-goal-constructor-establishes-fast-leaf-flags), [inflate_table_content](#target-zlib-inftrees-spec-goal-inflate-table-content), [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe), [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent), [constructor_subtable_bits](#target-zlib-inftrees-spec-subtable-goal-constructor-subtable-bits) |
| [Zlib.Inftrees.Proofs.Cover.root_cover_complete_fn](../ZlibF/Proof/inftrees.c.cover.fn.lean#L140) | [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe), [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent), [constructor_subtable_bits](#target-zlib-inftrees-spec-subtable-goal-constructor-subtable-bits) |
| [Zlib.Inftrees.Proofs.Cover.root_cover_fn](../ZlibF/Proof/inftrees.c.cover.fn.lean#L130) | No fixed-target composition recorded |
| [Zlib.Inftrees.Proofs.Cover.root_single_fn](../ZlibF/Proof/inftrees.c.cover.fn.lean#L226) | No fixed-target composition recorded |
| [Zlib.Inftrees.Proofs.inflate_fixed_ok](../ZlibF/Proof/inftrees.c.fixed.lean#L21) | No fixed-target composition recorded |
| [Zlib.Inftrees.Proofs.inflate_table_correct_ret](../ZlibF/Proof/inftrees.c.lean#L65) | No fixed-target composition recorded |
| [Zlib.Inftrees.Proofs.inflate_table_safe](../ZlibF/Proof/inftrees.c.lean#L34) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.GB.kraft_clamped](../ZlibF/Proof/trees.c.heap.gbtree.lean#L132) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.Out.bi_flush_spec](../ZlibF/Proof/trees.c.bits.lean#L548) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.Out.bi_reverse_correct](../ZlibF/Proof/trees.c.reverse.lean#L91) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.Out.bi_reverse_safe](../ZlibF/Proof/trees.c.reverse.lean#L51) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.Out.bi_windup_spec](../ZlibF/Proof/trees.c.bits.lean#L731) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.Out.init_block_spec](../ZlibF/Proof/trees.c.block.lean#L217) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.Out.init_block_spec0](../ZlibF/Proof/trees.c.block.lean#L102) | [deflateInit_](#target-zlibf-spec-public-goal-deflateinit), [deflateReset](#target-zlibf-spec-public-goal-deflatereset), [deflateResetKeep](#target-zlibf-spec-public-goal-deflateresetkeep) |
| [Zlib.Trees.Proofs.Out.send_bits_spec](../ZlibF/Proof/trees.c.bits.lean#L411) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.Out.tr_align_emit](../ZlibF/Proof/trees.c.align.lean#L42) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.Out.tr_flush_bits_emit](../ZlibF/Proof/trees.c.align.lean#L30) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.Out.tr_init_spec](../ZlibF/Proof/trees.c.block.lean#L245) | [deflateInit_](#target-zlibf-spec-public-goal-deflateinit), [deflateReset](#target-zlibf-spec-public-goal-deflatereset), [deflateResetKeep](#target-zlibf-spec-public-goal-deflateresetkeep) |
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
| [ZlibF.Spec.Proofs.prefixFree](../ZlibF/Proof/Format/Huffman.lean#L105) | [short_decode_table_leaf_sound](#target-zlib-inftrees-spec-decodeshort-goal-short-decode-table-leaf-sound), [decode_table_leaf_sound](#target-zlib-inftrees-spec-decodesoundness-goal-decode-table-leaf-sound), [constructor_establishes_query_stability](#target-zlib-inftrees-spec-decodetablestability-goal-constructor-establishes-query-stability), [short_rejected_leaf_stays_invalid](#target-zlib-inftrees-spec-decodetablestability-goal-short-rejected-leaf-stays-invalid), [constructor_establishes_fast_leaf_flags](#target-zlib-inftrees-spec-fasttableflags-goal-constructor-establishes-fast-leaf-flags), [compress_roundtrip](#target-zlibf-spec-api-goal-compress-roundtrip), [dict_roundtrip](#target-zlibf-spec-api-goal-dict-roundtrip), [format_deterministic](#target-zlibf-spec-api-goal-format-deterministic), [format_prefix_free](#target-zlibf-spec-api-goal-format-prefix-free), [inflate_completes](#target-zlibf-spec-api-goal-inflate-completes), [inflate_decodes](#target-zlibf-spec-api-goal-inflate-decodes), [inflate_deferred_distance](#target-zlibf-spec-api-goal-inflate-deferred-distance) |
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

Input fingerprint: `e8795a5547f48a2a36e89d0f4aabc11404b34104eea776bc1b75b551d39acb1b`.
<!-- proof-progress:end -->

## Remaining work

Targets with red borders have a documented blocker with evidence and a next step below.
A long proof attempt alone does not establish a blocker. Gray targets may be started;
their missing internal lemmas and history invariants are not all drawn in the graph.

### Core proof skeletons

#### inflate

The skeleton is on the branch `skeleton/inflate`. It type-checks: `Goal.inflate` and
`Goal.inflate_sequence` are proved there from the open lemmas below, and nothing else is open.
"Checked" means the lemma is on `dev` with the fast gate green; "checked in skeleton" means a
composition proved on the skeleton branch from the open lemmas. Estimates are focused hours,
with an uncertainty of about half the figure, including build time on the shared build host.

Decoder invariant `InflateInv` (`inflate.c.invariant`): it generalizes `DefaultOriginState` to
raw, zlib, gzip and automatic detection, windowBits 0, and an attached gzip header record. It
has no object-size field, because `StreamReachable` does not carry one.

| Lemma | Meaning | State | Hours |
| --- | --- | --- | ---: |
| `InflateInv.of_origin`, `InflateInv.of_good`, `InflateConfig.cases` | The default relation is an instance; the heap determines the decoder; every state is default, has width 0, or allows gzip. | checked | 0 |
| `InflateInv.to_origin` (`inflate.c.invariant-bridge`) | With the default configuration and request and the platform object-size limit, `InflateInv` gives back `DefaultOriginState`. | checked | 0 |
| Object-size preservation (`inflate.c.platform-preservation`) | Every stream operation except `inflate` and `inflateCopy` keeps `ByteObjectsFit`; init is covered by `inflate_domain_general_platform`. | checked | 0 |
| `inflate_call_refused` (`inflate.c.call-refused`) | A null output, null input with input pending, or `SYNC`: `Z_STREAM_ERROR`; only the local array is made and freed. | checked | 0 |
| `inflate_default_view_public_error_clauses` (`inflate.c.default-error-clauses`, `inflate.c.leave-cause-run`) | The new `Z_STREAM_ERROR`, `Z_BUF_ERROR` and progress clauses in the default configuration. Every leave with `ret == Z_OK` has no input, no output space, or a `Z_BLOCK`/`Z_TREES` stop. | checked | 0 |
| `inflate_call_default` (`inflate.c.call-default`) | One call in the default configuration, from the existing contract. | checked | 0 |
| `inflate_call_request` | One call in the default configuration with a request that differs (header-chosen width, raw after `inflateSync`). `DefaultStateJ` now records the request as `InflateInv` does, so `inflate_call_default` covers it; the legacy default-history proofs that needed the strict request were removed. | checked | 0 |
| `inflate_call_header_width` | One call with windowBits 0: the zlib header sets the width. `DefaultStateJ` admits width 0 before the header (no window, unread flags); HEAD sets the width after the size check; a loop that stops before the dictionary stage wrote nothing, so `inf_leave` does not update a window without a width. Covered by `inflate_call_default` for raw and zlib wrappers. | checked | 0 |
| `inflate_call_gzip` | One call with gzip allowed: detection, eight header modes, header record writes, CRC-32 and length trailer. | open | 45 |
| `inflate_call`, `inflate_step_invariant` | Case split over the four lemmas above. | checked in skeleton | 0 |
| `inflateInit2_invariant_of` | Every successful `inflateInit2_`, every accepted windowBits. | checked | 0 |
| `rebuffer_invariant` | A caller rebuffer keeps the invariant. | checked | 0 |
| `inflate_preserves` | `inflate` as a `Call` preserves the invariant (from `inflate_step_invariant`). | open | 1 |
| The 13 other `*_preserves` lemmas | Resets, prime, dictionary get and set, header attach, sync, queries, validate, undermine. | checked | 0 |
| `inflateCopy_invariant` | The copy destination has the invariant. | checked | 0 |
| `operation_preserves`, `reachable_invariant_kind`, `inflate_reachable_invariant`, `inflate_public` | Case split, induction over `StreamReachable`, and the theorem of type `Goal.inflate`. | checked in skeleton | 0 |
| **Remaining for `Goal.inflate`** | | | **46** |
| `inflate_call_safe` (`InflateCall.safe`, `inflate.c.call-safe`) | The written output and header regions lie inside the caller regions of `StreamWriteRegions`; owned blocks are kept. Checked from `InflateCall`; the skeleton applies it to `inflate_call`. | checked | 0 |
| 12 `*_call_safe` lemmas (`inflate.c.call-safety`) | Frame and ledger of every stream operation except `inflate` and `inflateSync`. | checked | 0 |
| `inflateSync_call_safe` (`inflate.c.sync-call-safe`) | Frame and ledger of `inflateSync`, including a window freed by the resynchronization; the call returns in every configuration. | checked | 0 |
| `inflateEnd_invariant` | `inflateEnd` releases everything the stream owns. | checked | 0 |
| `operation_safe`, `inflate_sequence_safety` | Case split and assembly of `StreamSequenceSafety .inflate`. | checked in skeleton | 0 |
| `ParseMeaning` (`inflate.c.meaning`) | The format meaning of a decoder state: a prefix grammar of deflate and the wrappers, and the decoder state of each position. Defined; the lemmas below prove against it. | defined | 0 |
| `meaning_init`, `meaning_rebuffer` | Initialization establishes it; rebuffering keeps it. | open | 6 |
| `meaning_step` | Functional correctness of one `inflate` call: headers 10, stored blocks 8, fixed blocks 6, code lengths 12, table meaning 20, slow symbol decoding 12, `inflate_fast` 20, window and dictionary copies 12, trailer 8, loop assembly 12. Existing semantic modules cover parts of the code-length and fast-path work. | open | 120 |
| `meaning_dictionary` | `inflateSetDictionary` keeps the meaning. | open | 8 |
| `meaning_of_trace`, `inflate_sequence_format` | Induction over the protocol trace and assembly. | checked in skeleton | 0 |
| `meaning_accepted` | A finished epoch consumed an accepted stream. | open | 6 |
| `meaning_prefix` | Prefix, no data error, exact end on a valid stream. | open | 8 |
| `TraceEvidence` (`inflate.c.completes-interface`) | Every admitted history: the output is justified by a checked bit prefix of the consumed input and determined by it, valid input or not. From `ParseMeaning`. | open | 8 |
| `ConsumesWithinStream` | A call offered input comparable with a valid stream reads only bytes of the stream; reading its last byte returns `Z_STREAM_END` or `Z_MEM_ERROR`. | open | 4 |
| `StopsWhenBlocked` | On a valid stream, a call returning `Z_OK` or `Z_BUF_ERROR` with input left has a full output and output still due. | open | 6 |
| `NeedDictionaryCall` | `Z_NEED_DICT` only in `DICT` with no dictionary, no output, from a zlib header with `FDICT`. | open | 3 |
| `MemErrorAllocates` (`inflate.c.completes-percall`) | Outside `MEM`, a `Z_MEM_ERROR` return that leaves the decoder in `MEM` (as `Goal.inflate` states) reports an allocator failure in the call. Theorem `mem_error_allocates`. | checked | 0 |
| `InflateKeepsObjectSize` | One `inflate` call keeps `ByteObjectsFit` (the missing case of the object-size preservation row). Theorem `inflate_keeps_object_size`. | checked | 0 |
| `CallKeepsControl` | One `inflate` call never enters `SYNC`, enters `MEM` only with `Z_MEM_ERROR`, keeps the header record and its own blocks, and owns afterwards only its old blocks or blocks that were not live (a new window). Theorem `call_keeps_control`. The three facts come from `call_inflate` (`inflate.c.completes-keep-run`): every successful run of the translated `inflate`, with no invariant premise, keeps the allocation metadata, the byte-object sizes and the control fields of every decoder record. | checked | 0 |
| `inflate_completes_proof` | `InflateCompletes`, proved on `dev` from `DecoderFacts` (`inflate_completes_of_facts`, through `inflate_completes_reachable`). The protocol trace and `InflateCompletes` now carry `ByteObjectsFit` (`ad4c1ffd`). | composed | 0 |
| `inflate_sequence_public` | The theorem of type `Goal.inflate_sequence`. | checked in skeleton | 0 |
| **Remaining for `Goal.inflate_sequence`** | | | **169** |
| Statement tests | `tests/goals/inflate`: every clause of `Goal.inflate`, the format clauses of `Goal.inflate_sequence` and `InflateCompletes` against the real zlib, also under ASan and UBSan. No clause violated in 6000 sessions. | done | 0 |
| Cleanup | Delete fast-path and fixed-configuration proofs the skeleton does not use. | open | 4 |
| `uncompress*` (`public-uncompress*`) | All four goals proved on `dev` from `DecoderFacts` (`uncompress2_z_of_facts`, `uncompress2_of_facts`, `uncompress_z_of_facts`, `uncompress_of_facts`): refusal, init failure, the call loop with its bound, exact stores and cleanup, wrappers. They become the goals once the remaining decoder facts above (`TraceEvidence`, `ConsumesWithinStream`, `StopsWhenBlocked`, `NeedDictionaryCall`) and the decoder goals are proved. | composed | 0 |
| **Total remaining** | | | **219** |

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
- P15 (open, proposed): at `BAD`, `fast_call_meaning` needs `LoopDoomed` for the input read after
  the fast call, but `inflate_fast` returns the unused whole bytes, also bits its table lookup
  looked at, and `TableMeaning` does not fix how many bits a rejected entry needs. Counterexample
  state: a fixed block (`fixedLitLens`) whose literal/length table is a valid `inflate_table` result
  except that the root entries read by the codes of 286 and 287 (`1100011x`) are `{op 64, bits 6}`
  instead of `bits 8`. `Inv`, `StableQuery` and `QueryCompatible` still hold (a padded 6-bit query
  `110001` reads the entry of 284, which needs 8 bits). With the 6 held bits `110001` at fast
  entry, the body pulls 2 bytes (22 bits), drops 6 on the rejected entry, and the epilogue returns
  both bytes: the read input ends after `110001`, and the code of 284 (`11000100`) continues it
  validly. Proposed addition to `TableMeaning` (a constructor obligation, true of `inflate_table`
  and the fixed tables, which replicate an entry over the bits it does not use): `PrefixQuery`, a
  full-width read `(entry, consumed)` is also the read of the zero-padded first `consumed` bits.
  With it, `short_rejected_leaf_stays_invalid` gives the rejection on the read bits. The proof also
  needs a per-pass result that states, at `BAD`, the bits the rejected token consumed: the
  registered `actual_body_refines_token` states the rejection on the whole remaining input only
  (its proof has the consumed bits, in `LengthTrace.End` and `DistanceResult.Outcome`).

The body-mode clauses are checked on the real decoder by `tests/goals/inflate-meaning-body`
(about 56,000 states of 3,200 sessions, no violation).

| Lemma | Meaning | State | Hours |
| --- | --- | --- | ---: |
| `meaning_interface_body` | P1 to P4, `DynamicMatches` and suffix stability in `TableMeaning` (`inflate.c.meaning`, `0696a247`). | checked | 0 |
| `LoopMatches` (`meaning-loop`, `meaning-write`, `meaning-frame`) | The relation between mode steps inside one call: registers, input consumed in the call, held bits, stage, output since the call base, window and check of the output before the call. Shared with batch 2. Agreed with batch 2; output-write and frame lemmas. | checked | 0 |
| `lenfix_inv`, `distfix_inv`, `lenfix_stable`, `distfix_stable` (`meaning-fixed-tables`) | The static fixed tables have `DecodeTableInvariant.Inv` with the fixed code lengths, short lookups included, and suffix-stable queries. | checked | 0 |
| `lookup_meaning` (`meaning-lookup`, `meaning-length`, `meaning-distance`) | Slow `lookup1`/`lookup2` on an `Inv` table with refill: the selected leaf is the symbol of the held bits, with fewer than 15 bits available, or the input has no valid symbol. Folded into the step lemmas (`fitted_leaf_meaning`, `lookupLoop_fail`, `lookup1_len_fail`, `lookup2_len_fail`). | checked | 0 |
| `codes_lookup_meaning` (`meaning-codelens-items`) | The same for the code-length table (`CodeLengthMeaning`), the empty code-length code included (`cl_iter`). | checked | 0 |
| `table_step` (`meaning-dynamic-steps`) | `TABLE`: wait, the count rejection (`BAD`, no valid continuation), or fall-through to `LENLENS` with `LoopMatches`. No hypothesis beyond the stream record. | checked | 0 |
| `lenlens_step` (`meaning-dynamic-steps`) | `LENLENS`: code-length code lengths across calls; rejected with no completion, or fall-through to `CODELENS` with `CodeLengthMeaning`, the empty-code cells and fewer than 8 held bits. Hypothesis beyond the stream record: `WellFormed` (array sizes). | checked | 0 |
| `codelens_step` (`meaning-dynamic-steps`, `meaning-codelens-items`, `meaning-dynamic-tables`) | `CODELENS`: lengths across calls, repeats (`BAD` through the converse of the parse), end-of-block and code checks (`BAD`: no `DynamicHeader` completion), installation of both tables with `Inv` and `StableQuery`, leave for `Z_TREES` or fall-through to `LEN_`. Hypotheses beyond the stream record: `WellFormed`, `CodeLengthInvariant`, the installed table's content classification. | checked | 0 |
| `typedo_step`, `type_step` (`meaning-block`) | `TYPE`, `TYPEDO` before the final block: stored, fixed (with `lenfix_inv`), dynamic, type 3 (`BAD`, no type-3 body). The static tables come from `LibraryGlobals`. | checked | 0 |
| `stored_step` (`meaning-block`, `meaning-copy`) | `STORED`, `COPY_`, `COPY`: padding, length check and byte copies across calls. No hypothesis beyond `LoopMatches`, the stream record and the window bounds; the held-bit bound comes from `BodyMatches` (P11). | checked | 0 |
| `len_slow_step` (`meaning-length`) | `LEN_`, slow `LEN`: literal, end of block (fewer than 8 held bits), length, invalid code (`len_slow_step`, `len__step`, into `lenext_step`). Hypotheses beyond those of `match_step`: the negated fast-branch condition and `DataTablesSafe`. | checked | 0 |
| `distance_steps` (`meaning-distance`) | `LENEXT`, `DIST`, `DISTEXT`: extra bits, distance symbol, invalid distance (`lenext_step`, `dist_step`, `distext_step`, into `match_step`). Hypotheses beyond those of `match_step`: `DataTablesSafe` and the back-counter bound (`DataPendingInvariant`). | checked | 0 |
| `lit_step` (`meaning-lit`) | `LIT`: the pending literal is written. | checked | 0 |
| `match_step` (`meaning-match`) | `MATCH`: copies from the output and from the window, overlap, too far back. | checked | 0 |
| `fast_call_meaning` (`meaning-fast-token`, `meaning-fast-loop`, `meaning-fast`) | One whole `inflate_fast` call from `LEN`. Checked: `fast_call_steps`, the registered per-pass token and origin results composed over the loop and the epilogue; more tokens of the block or the end of the block give `LoopMatches`, a rejected token gives `BAD`. Open: `LoopDoomed` at `BAD` (P15). Hypotheses beyond `match_step`: `Good`, `DataTablesSafe`, `DataPendingInvariant`, `DispatchBuffers`, `ByteObjectsFit`, the fast leaf flags `FastFlags` (proposed addition to `TableMeaning`), input and output in distinct raw blocks (deviations, fast decoder helpers). | open | 8 |
| `leave_window_meaning` (`meaning-leave-window`) | `updatewindow` at `inf_leave` gives `WindowMeaning` of the output after the call, the first allocation included; an allocation failure keeps the state and the old `WindowMeaning`. Hypotheses: `Good`, the default allocator, the output bytes, the output buffer not the window block. | checked | 0 |
| Cleanup | Generalize or delete default-configuration `inflate.c.fast*` modules the skeleton does not use. | open | 3 |
| **Remaining for batch 1** | | | **11** |

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
| `head_step` | `HEAD`: raw to `TYPEDO`, zlib header (width 0 sets the width), gzip magic, every rejection. | open | 8 |
| `dictid_step`, `dict_step` | `DICTID` stores the identifier; `DICT` asks for the dictionary or enters the body. | open | 4 |
| `gzip_fixed_steps` | `FLAGS`, `TIME`, `OS`, `EXLEN`, with the header CRC accumulator. | open | 6 |
| `gzip_field_steps` | `EXTRA`, `NAME`, `COMMENT`: byte runs across calls, CRC over the input bytes. | open | 8 |
| `hcrc_step` | `HCRC`: the header CRC check and entry to the body. | open | 2 |
| Shared loop lemmas (`meaning-bits`, `meaning-stuck`, `meaning-outcome`, `meaning-fields`) | `LoopMatches.needbits`; `LoopDoomed.of_stuck`; `LoopBad`, `TripOutcome`, `bad_trip`; held bits as little-endian bytes. | checked | 0 |
| `trailer_steps` (`meaning-trailer`) | `DONE` and gzip `LENGTH` (checked); `CHECK` with the Adler-32 or CRC-32 update of the call's output (open); raw `CHECK` needs P10 (end stage in `CHECK` for raw data, proposed to batch 1). | open | 4 |
| `leave_meaning` | `inf_leave`: totals and check update with the call's output; window update from batch 1's lemma; `Z_MEM_ERROR`. | open | 6 |
| `loop_meaning` | The mode loop of one call keeps `CallMeaning`, with batch 1's body steps as hypotheses. | open | 10 |
| `meaning_step` assembly | Entry, refusals, run and leave give `ParseMeaning` after the call, with the request token. | open | 6 |
| `meaning_dictionary` (`meaning-dictionary`) | `inflateSetDictionary`: refusals, identifier mismatch, `Z_MEM_ERROR`, raw installation, zlib installation in `DICT`. | checked | 0 |
| `deflate_prefix_order` (`meaning-prefix-order`, `meaning-accept`) | A parse position on a prefix of a valid stream lies on its parse (output prefix, exact end), a finished parse is a specification parse, the configured zlib window decodes like the announced one, and stage headers are the stream's header. | checked | 0 |
| `meaning_accepted` (`meaning-format`) | A finished single-dictionary epoch consumed an accepted stream. | checked | 0 |
| `meaning_prefix` (`meaning-format`) | Prefix, no data error, exact end, also after `Z_MEM_ERROR`. | checked | 0 |
| Cleanup | Generalize or delete the default-configuration header, dictionary and wrapper modules. | open | 3 |
| **Remaining for batch 2** | | | **57** |

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

| Lemma | Meaning | State | Hours |
| --- | --- | --- | ---: |
| `HeaderFoot` (`inflate.c.gzip-header-frame`) | Pointwise footprint against the entry heap; gives `BufferFrame` and `LiveChange`. | checked | 0 |
| `GzInv` (`inflate.c.gzip-header-state`) | Step invariant: state, stream and record writes, `hbuf` and region stores, `NEEDBITS`, input consumption. | checked | 0 |
| `gz_FLAGS` .. `gz_HCRC` (`inflate.c.gzip-header-modes`) | Each mode runs to a leave in a header mode, `TYPE` or `BAD`; the `NAME`/`COMMENT` byte loop; `CRC2`, `CRC4`; `EXTRA`'s copy. | checked | 0 |
| `inflate_dispatch_gzip_header_rank` (`inflate.c.gzip-header-dispatch`) | The interface theorem. | checked | 0 |
| **gzip header modes** | | | **0** |

#### deflate

The skeleton is on the branch `skeleton/deflate`, file `ZlibF/Proof/deflate.c.universal.lean`.
It type-checks: `Goal.deflateInit2_`, `Goal.deflate` and `Goal.deflate_sequence` are proved there
from the open lemmas below. State "open" means the lemma has no proof yet; "checked" means it is
proved on `dev`. Estimates are focused
hours, with an uncertainty of about half the figure, including build time on the shared host.

One invariant `DInv` holds in every reachable state, for every level, `memLevel`, `windowBits`,
strategy, tuning value and header: `DGood`, the default allocator, the window and match shape,
the hash chains up to the insertion frontier (`HeapChains`, for any content of unwritten `prev`
cells), at most 7 waiting bits, and the recorded symbols of the current block: their bytes and the
leaf frequencies of `dyn_ltree` and `dyn_dtree` describe the same list (`SymbolLedger`), their
distances are within `MAX_DIST`, and the pending bytes lie below them. `DInv` and its interface
are on `dev` in `ZlibF/Proof/deflate.c.universal-invariant.lean`. Other modules use its
interface (`DInv.dgood`, `DInv.unique`, `DInv.owned`, `DInv.rebuffer`), not its fields. One
ledger `Ledger` relates a data epoch to the stream: header and complete blocks decode to a prefix
of the input, the recorded symbols mean the next part (`Trace`), the window holds the rest.

| Lemma | Meaning | State | Hours |
| --- | --- | --- | ---: |
| `DInv.dgood`, `DInv.defAlloc`, `DInv.unique`, `DInv.recorded`, `DInv.bi_valid_le` | Interface: the invariant gives `DGood`, the allocator, the symbol ledger, the bit bound, and determines the state (`deflate.c.universal-invariant`). | checked | 0 |
| `DInv.owned` | The blocks the history owns are the five blocks of the state. | open | 1 |
| `DInv.rebuffer` | Caller rebuffering keeps the invariant. | open | 3 |
| `init2_version`, `init2_null` | Version, stream-size and `NULL` refusals for every argument (`deflate.c.init.general`). | checked | 0 |
| `init2_main` | Every signed parameter tuple: refusal, the five allocation outcomes with cleanup, success with `DeflateInitial` (`deflate.c.init.general-main`). | checked | 0 |
| `init2_inv` | A successful `deflateInit2_` establishes `DInv`. | open | 8 |
| `deflateInit2_proof` | The theorem of type `Goal.deflateInit2_` (`public-deflate-init2`). | checked | 0 |
| `fill_window_spec` | `fill_window`: input read with checksum, slide of window and hash tables, string insertion, high-water margin; afterwards matcher room or no input. | open | 30 |
| `longest_match_spec` | No fault and termination for every tuning value; a real match within the lookahead. | open | 12 |
| `flush_block_spec` | `FLUSH_BLOCK_ONLY` at a nonzero level with nothing pending and a non-`NULL` output buffer: stored, fixed or dynamic, `send_all_trees`, `compress_block` inside the shared buffer (F9, every `memLevel`; 1 to 4 have no known argument yet), `flush_pending`. The execution is checked on `dev` for every `memLevel` and both output pointer kinds (`flush_block_only_safe`, `trees.c.universal-flush`), with the dynamic overlay room as the premise `DynamicOverlay`. Open: the assembly from `DInv` to `DInv`, which needs `BlockClear` and the empty-pending cursor in `DInv` (asked of batch A), and `dynamic_overlay_small`. | open | 60 |
| `dynamic_overlay_small` | F9 for dynamic blocks at `memLevel` 1 to 4: every prefix of the tree description and symbol codes stays below the next unread symbol (`DynamicOverlay`). Checked for `memLevel` 5 to 9 (`dynamic_overlay_large`). No argument is known; `tests/goals/overlay` found no violation (smallest gap 58, 161, 404, 906 bytes for `memLevel` 1 to 4). If no proof is found, the supervisor decides between more work and a documented precondition. | open | in `flush_block_spec` |
| `stored_spec` | `deflate_stored`: direct copies, window retention, buffered stored blocks. | open | 30 |
| `fast_spec`, `slow_spec` | `deflate_fast` and `deflate_slow` with lazy matching. | open | 45 |
| `rle_spec`, `huff_spec` | `deflate_rle` and `deflate_huff`. | open | 18 |
| `deflate_call` | One `deflate` call: refusals, pending flush, zlib and gzip headers with interruption, dispatch, flush markers, full-flush hash clearing, trailer, and every clause of `Goal.deflate`. | open | 40 |
| `operation_step` | Every other stream operation keeps the invariant with its frame: `deflateParams` (inner `deflate(Z_BLOCK)`, slide or clearing), `deflateSetDictionary`, `deflatePrime`, resets, `deflateSetHeader`, `deflateTune`, queries, bounds. | open | 45 |
| `copy_inv` | `deflateCopy` gives the destination the invariant. | open | 12 |
| `reachable_inv` | Induction over `StreamReachable`. | checked in skeleton | 0 |
| `deflate_proof` | The theorem of type `Goal.deflate`. | checked in skeleton | 0 |
| **Subtotal `Goal.deflateInit2_` and `Goal.deflate`** | | | **304** |
| `end_from_inv` | `deflateEnd` from the invariant (reuses `deflate_end_public`). | open | 2 |
| `Ledger` | Final design of the ledger: header, block prefix, current block (symbols or stored window bytes), lazy literal, window contents, finished stream. | open | 16 |
| `ledger_init`, `ledger_rebuffer` | Initialization establishes the ledger; rebuffering keeps it. | open | 7 |
| `ledger_dictionary` | A preset dictionary before data: window and `DICTID`. | open | 12 |
| `ledger_step` | Functional correctness of one call: symbol meaning for each strategy 40, fixed and dynamic block encoding 35, stored blocks and the direct stored path 30, flush markers 8, headers and trailers 12, window and slide bookkeeping 15, assembly 20. Existing tree and Math modules cover parts of the encoding work. | open | 160 |
| `trace_ledger` | Induction over `DeflateDataTrace`. | checked in skeleton | 0 |
| `ledger_finished` | A finished epoch decodes to its input (`DecodesFor`). | open | 6 |
| `ledger_flush` | A completed sync or full flush: input consumed, `FlushedFor`, restart after a full flush. | open | 16 |
| `ledger_adler` | `adler` is the checksum of the accepted input. | open | 6 |
| `bound_before_output` | `deflateBound` and `deflateBound_z` return the model bound before output. | open | 10 |
| `completes` | `DeflateCompletes`: the worst-case expansion of every strategy and block choice stays within the bound, also across several `Z_FINISH` calls. | open | 60 |
| `deflate_sequence_proof` | The theorem of type `Goal.deflate_sequence`. | checked in skeleton | 0 |
| **Subtotal `Goal.deflate_sequence`** | | | **295** |
| `compress*` | Compositions of init, one `Z_FINISH` call and end. | open | 12 |
| **Total** | | | **611** |

Independent batches for additional owners. Each batch depends only on the statements of the
other batches (on `skeleton/deflate`), not on their proofs, and lives in its own files. The
invariant `DInv` and its interface belong to batch A; a change to `DInv` is announced to the others.

| Batch | Lemmas | Files | Hours |
| --- | --- | --- | ---: |
| A. Initialization and history | `init2_inv`, `DInv.owned`, `DInv.rebuffer`, `operation_step`, `copy_inv`, `end_from_inv` | `deflate.c.init.general`, `deflate.c.universal-ops` | 71 |
| B. Window and strategies | `fill_window_spec`, `longest_match_spec`, `stored_spec`, `fast_spec`, `slow_spec`, `rle_spec`, `huff_spec` | `deflate.c.universal-window`, `deflate.c.universal-strategies` | 135 |
| C. Block emission and bounds | `flush_block_spec`, `bound_before_output`, `completes` | `trees.c.universal-block`, `deflate.c.universal-bound` | 130 |
| D. The call and the ledger | `deflate_call`, `Ledger`, `ledger_init`, `ledger_rebuffer`, `ledger_dictionary`, `ledger_step`, `ledger_finished`, `ledger_flush`, `ledger_adler` | `deflate.c.universal-call`, `deflate.c.universal-ledger` | 263 |

`compress*` (12 hours) follows once A to D are checked.

Interface for an owner of batch B or C. Start from the branch `skeleton/deflate`, file
`ZlibF/Proof/deflate.c.universal.lean`.

- **Statements.** B: section 4, `fill_window_spec` to `huff_spec`. C: section 4, `flush_block_spec`;
  section 7, `bound_before_output` and `completes` (its statement is `DeflateCompletes` in
  `ZlibF/Spec/Public/Sequences.lean`).
- **What a lemma may assume.** The invariant `DInv` (on `dev`, `deflate.c.universal-invariant`),
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
| `deflate.c.engine.chains`, `lmbody`, `macros` and the slide and insertion lemmas | Already parametric (window 2^9 to 2^15, any hash parameters). Fit `fill_window_spec` and `longest_match_spec`. Keep. |
| `deflate.c.engine.*` default, common and generic-foreign histories (`DefaultDataTrace`, `Common*DataTrace`, `EngineStart`) | Tied to window 15, `memLevel` 8, strategy 0 or to level 6. They cannot serve the universal lemmas. Delete once those lemmas are checked, except files that a registered theorem needs (about 60 registered engine theorems). |
| `deflate.c.init.*` | Fixed buffer sizes. The default proof is the template for `init2_main`; generalize. Keep the default modules that `deflateInit_proof` needs. |
| `trees.c.*` | Parametric in the block and its descriptors (`gen_codes`, `build_tree`, `scan_tree`, `build_bl_tree`, `send_tree`, `send_code` checked). Fit `flush_block_spec`; `send_all_trees`, `compress_block` and F9 remain. Keep. |
| `ZlibF/Math/Deflate*`, `Huffman*` | Heap-free: symbols and their meaning, block prefixes, overlay and budget bounds, Huffman depth bounds. Fit the ledger and F9. Keep. |

### Ordered next work

Only rows 9 to 12 are planned work: see [Scope](#scope). Start with row 11, then rows 9 and 12.
Rows 1 to 5 and 13 are the gzip file interface and are not planned. Rows 6 to 8 and 10 are done
only when a sequence goal needs them.

Ordered. "Prerequisite" is what must be proved first; it is never an assumed contract.
"Owner PR" is the pull request that carries the work once one exists.

| # | Target | Prerequisite | Owner PR |
| ---: | --- | --- | --- |
| 1 | `gzopen`, `gzopen64`, `gz_initialisation_domain` | Statement question first (see [gzip open path length](#gzip-open-path-length)). Then the path-open (`fd = -1`) branch of `gz_open`: `fsOpen` outcomes and the append/read seeks, reusing the `gzdopen` composition | — |
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
the constant is wrong; [API model](design/api-model.md)), and the gzip open path length question below.
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

#### Callback decoder prerequisites

`inflateBack` need not wait for the complete ordinary `inflate` target. Setup and teardown
are already registered. Existing entry, bit-input, window-flush and stored-block arguments
can be reused. Compressed blocks and the full public callback protocol still need composition.

A fast-path theorem requiring separate output and history buffers does not cover output
inside the window. A table return-code theorem does not establish installed entry contents.
The [callback proof guide](proof/callbacks.md) locates the reusable arguments and
states the limits of their callback domain. These missing premises do not stop independent
work on another block type or error path.

#### Next work for every unfinished public target

"Start" means work can begin without a complete engine theorem. "Compose" names a
prerequisite for full closure; independent branches can still proceed. No row grants
checked status or assumes a callee's specification.

<!-- proof-readiness:start -->
| Public targets | Proof work shown in graph | Next work and missing prerequisite |
| --- | --- | --- |
| `gzopen`, `gzopen64`, `gz_initialisation_domain`  | Start: open and cleanup | <a id="readiness-gzopen"></a> **Statement question first:** see [gzip open path length](#gzip-open-path-length). **Start:** the path-open branch of `gz_open` (`fsOpen` outcomes, append and read seeks), reusing the registered `gzdopen` mode loop, allocation and `OpenState` composition. Entry/failure branches are locally checked above. |
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
| `inflateInit2_`  | Locally checked: awaiting registration | <a id="readiness-inflateinit2"></a> The cleanup contract is [corrected](#inflate-initialization-cleanup) and the proof is locally checked. **Next:** register it, add its proof mutants and regenerate the locks. |
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
issue, not a zlib issue. `CompressorContract` has the same pattern (`compress2_z` also frees a
local `z_stream`); **to confirm** by its owner.

The same four contracts also lacked the heap representation condition `Uniq` (one object per
block identity below `nextBlk`), which [the trusted base](trusted-base.md) requires of every
initial heap and which every public stream history already assumes (`InitDomain`,
`StreamReachable`). It is now a premise. It does not narrow the C domain: every C state has such
a representation. `CompressorContract` lacks it too.

Review the corrected shared `Uncompress2` relation independently. The deferred-distance and
exact-free corrections have independent counterexamples and checked regression proofs;
implementation refinement remains open. Its former empty-output clause on memory failure and
extension clause on buffer error have been removed using the existing paired counterexample.
Complete the older abstract gz and dictionary models before using them as complete operational
refinements; the concrete public targets do not assume their callee contracts.

#### Gzip open path length

Unconfirmed statement report; the owner decides. `gz_open` copies the caller path with
`snprintf(state->path, len + 1, "%s", path)`. The model `vsnprintf` in
[`gzfs.lean`](../ZlibF/Zlib/gzfs.lean) raises `Fault.ub` when the output is longer than
`INT_MAX` bytes. `Goal.gzopen`, `Goal.gzopen64` and `Goal.gz_initialisation_domain` admit every
`CString` path (length below `2^64`) and, with successful allocation, require a non-faulting
result. A path of at least `2^31` bytes therefore makes all three statements false in the model.
The existing descriptor-open lemmas already carry `name.length ≤ 2147483647`; `gzdopen` is
unaffected because its path is short. On the target platform, POSIX `snprintf` returns `-1`
with `EOVERFLOW` rather than undefined behaviour; ISO C leaves the case undefined. Two
corrections are possible: add the path-length premise to these three statements and to
[deviations](deviations.md), or model POSIX `vsnprintf` in the trusted external model.
A checked counterexample is not yet written.

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

