# Project status and remaining work

[Documentation](README.md) · [API](api/README.md) · [Checking](checking/README.md)

**Work in progress. Full zlib verification is not complete.**
This is the single current-status and remaining-work page.
The first target is the default LP64 Linux static build with the default allocator.
Other upstream configurations remain goals. Compiler/OS correctness and performance
are outside the proof.

<!-- proof-progress:start -->
## Proof progress graph

**181 fixed targets: 103 public and 78 supporting.**
Exact proofs: 78 registered and 33 local only.
These counts are not a percentage of verification effort or a final CI result.

**Input coverage colours:** ⬜ not proved · 🟦 default inputs · 🟨 common inputs · 🟩 all stated inputs.
The input ranges are defined once in [input configurations](input-configurations.md).
A complete fixed-goal proof covers all inputs admitted by that exact statement.
Default/common coverage requires an exact checked scoped contract; branch lemmas
and manually assigned labels cannot grant it. Registration and CI remain separate.
A red border marks a recorded blocker without erasing other established coverage.

Every current fixed target appears once. Public APIs, internal obligations and
abstract models stay in separate groups. Only actual proof-reference arrows are
drawn: source proof → destination proof. C calls and specification references
are separate tables in [the evidence index](progress.md).
Positions group related targets; they do not express dependency. Missing arrows
do not establish independence or enumerate the internal helper obligations.

```mermaid
flowchart TB
  subgraph queries["Library queries"]
    n19["compressBound"]:::all
    n20["compressBound_z"]:::all
    n21["zlibVersion"]:::all
    n22["zlibCompileFlags"]:::all
    n23["zError"]:::all
    n30["get_crc_table"]:::all
    n19 ~~~ n20
    n20 ~~~ n21
    n21 ~~~ n22
    n22 ~~~ n23
    n23 ~~~ n30
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
    n24 ~~~ n25
    n25 ~~~ n26
    n26 ~~~ n27
    n27 ~~~ n28
    n28 ~~~ n29
    n29 ~~~ n31
    n31 ~~~ n32
    n32 ~~~ n33
    n33 ~~~ n34
    n34 ~~~ n35
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
    n123 ~~~ n124
    n124 ~~~ n125
    n125 ~~~ n126
    n126 ~~~ n127
    n127 ~~~ n128
    n128 ~~~ n129
    n129 ~~~ n130
    n130 ~~~ n131
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
    n39 ~~~ n73
    n73 ~~~ n74
    n74 ~~~ n77
    n77 ~~~ n78
    n78 ~~~ n79
    n79 ~~~ n80
    n80 ~~~ n81
    n81 ~~~ n82
    n82 ~~~ n87
    n87 ~~~ n89
    n89 ~~~ n90
    n90 ~~~ n91
    n91 ~~~ n92
    n92 ~~~ n93
    n93 ~~~ n94
    n94 ~~~ n99
    n99 ~~~ n105
  end
  style inflate fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph fast["Fast decoder obligations"]
    n134["InflateFastBodyOrigin<br/>actual_body_preserves_<br/>origin<br/>Local exact proof"]:::all
    n135["InflateFastBodyToken<br/>actual_body_refines_token<br/>Local exact proof"]:::all
    n136["InflateFastCallOrigin<br/>actual_fast_preserves_<br/>origin<br/>Local exact proof"]:::all
    n137["InflateFastDistanceOrigin<br/>actual_distance_block_<br/>preserves_origin<br/>Local exact proof"]:::all
    n138["InflateFastDistanceResult<br/>actual_distance_refines_<br/>lz77<br/>Local exact proof"]:::all
    n139["InflateFastDistance<br/>Semantics<br/>distance_lookup_matches_<br/>format<br/>Local exact proof"]:::all
    n140["InflateFast<br/>fast_safe<br/>Local exact proof"]:::all
    n141["InflateFast<br/>step_safe<br/>Local exact proof"]:::all
    n142["InflateFastLength<br/>Semantics<br/>length_lookup_matches_<br/>format<br/>Local exact proof"]:::all
    n143["InflateFastLengthTrace<br/>actual_body_retains_<br/>selected_length<br/>Local exact proof"]:::all
    n144["InflateFastMatchHistory<br/>actual_copy_match_<br/>refines_lz77<br/>Local exact proof"]:::all
    n145["InflateFastMatchHistory<br/>match_array_refines_lz77<br/>Local exact proof"]:::all
    n146["InflateFastOrigin<br/>actual_drop_preserves_<br/>origin<br/>Local exact proof"]:::all
    n147["InflateFastOrigin<br/>actual_pull_preserves_<br/>origin<br/>Local exact proof"]:::all
    n148["InflateFastOrigin<br/>actual_rollback_<br/>preserves_origin<br/>Local exact proof"]:::all
    n149["InflateFastOrigin<br/>drop_preserves_origin<br/>Local exact proof"]:::all
    n150["InflateFastOrigin<br/>initial_origin<br/>Local exact proof"]:::all
    n151["InflateFastOrigin<br/>pull_preserves_origin<br/>Local exact proof"]:::all
    n152["InflateFastOrigin<br/>rollback_preserves_origin<br/>Local exact proof"]:::all
    n134 ~~~ n135
    n135 ~~~ n136
    n136 ~~~ n137
    n137 ~~~ n138
    n138 ~~~ n139
    n139 ~~~ n140
    n140 ~~~ n141
    n141 ~~~ n142
    n142 ~~~ n143
    n143 ~~~ n144
    n144 ~~~ n145
    n145 ~~~ n146
    n146 ~~~ n147
    n147 ~~~ n148
    n148 ~~~ n149
    n149 ~~~ n150
    n150 ~~~ n151
    n151 ~~~ n152
  end
  style fast fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph tables["Decode-table obligations"]
    n153["InflateDecodeTable<br/>Rejection<br/>decode_table_classifies_<br/>input"]:::unproved
    n154["InflateDecodeTable<br/>Semantics<br/>decode_table_matches_<br/>format"]:::unproved
    n155["InflateDecodeTableShort<br/>short_decode_table_leaf_<br/>sound"]:::unproved
    n156["InflateDecodeTable<br/>Soundness<br/>decode_table_leaf_sound"]:::unproved
    n157["InflateDecodeTableFrame<br/>decode_table_read_<br/>preserved<br/>Local exact proof"]:::all
    n158["InflateDecodeTable<br/>Invariant<br/>constructor_establishes_<br/>decode_table_invariant"]:::unproved
    n159["InflateDecodeTable<br/>Invariant<br/>decode_table_invariant_<br/>of_prefix"]:::unproved
    n160["InflateDecodeTable<br/>Stability<br/>constructor_establishes_<br/>query_stability"]:::unproved
    n161["InflateDecodeTable<br/>Stability<br/>query_stability_of_prefix<br/>Local exact proof"]:::all
    n162["InflateDecodeTable<br/>Stability<br/>short_rejected_leaf_<br/>stays_invalid<br/>Local exact proof"]:::all
    n163["InflateFastTableFlags<br/>constructor_establishes_<br/>fast_leaf_flags"]:::unproved
    n164["InflateFastTableFlags<br/>fast_leaf_flags_of_prefix"]:::unproved
    n165["InflateFastTableFlags<br/>fixed_tables_have_fast_<br/>leaf_flags"]:::unproved
    n166["InflateFastTableFlags<br/>leaf_classification_<br/>agrees"]:::unproved
    n167["InflateTableContent<br/>inflate_table_content"]:::unproved
    n168["InflateTableSafety<br/>inflate_table_decoder_<br/>safe"]:::unproved
    n169["InflateTableExtent<br/>inflate_table_read_extent"]:::unproved
    n170["InflateRootTable<br/>constructor_root_bits"]:::unproved
    n171["InflateSubtable<br/>constructor_subtable_bits"]:::unproved
    n153 ~~~ n154
    n154 ~~~ n155
    n155 ~~~ n156
    n156 ~~~ n157
    n157 ~~~ n158
    n158 ~~~ n159
    n159 ~~~ n160
    n160 ~~~ n161
    n161 ~~~ n162
    n162 ~~~ n163
    n163 ~~~ n164
    n164 ~~~ n165
    n165 ~~~ n166
    n166 ~~~ n167
    n167 ~~~ n168
    n168 ~~~ n169
    n169 ~~~ n170
    n170 ~~~ n171
  end
  style tables fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph copy["Match-copy mathematics"]
    n172["LZ77CopySpec<br/>output_copy_refines_lz77<br/>Local exact proof"]:::all
    n173["LZ77CopySpec<br/>window_copy_refines_lz77<br/>Local exact proof"]:::all
    n174["LZ77HistorySpec<br/>copy_back_compose<br/>Local exact proof"]:::all
    n175["LZ77HistorySpec<br/>copy_back_extends_history<br/>Local exact proof"]:::all
    n176["LZ77HistorySpec<br/>retained_history_agrees<br/>Local exact proof"]:::all
    n177["LZ77HistorySpec<br/>window_distance_check_<br/>agrees<br/>Local exact proof"]:::all
    n172 ~~~ n173
    n173 ~~~ n174
    n174 ~~~ n175
    n175 ~~~ n176
    n176 ~~~ n177
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
    n40 ~~~ n75
    n75 ~~~ n76
    n76 ~~~ n83
    n83 ~~~ n84
    n84 ~~~ n85
    n85 ~~~ n86
    n86 ~~~ n88
    n88 ~~~ n95
    n95 ~~~ n96
    n96 ~~~ n97
    n97 ~~~ n98
    n98 ~~~ n100
    n100 ~~~ n101
    n101 ~~~ n102
    n102 ~~~ n103
    n103 ~~~ n104
  end
  style deflate fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph back["Callback decoding"]
    n36["inflateBackInit_"]:::all
    n37["inflateBack"]:::unproved
    n38["inflateBackEnd"]:::all
    n36 ~~~ n37
    n37 ~~~ n38
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
    n57["gzdopen"]:::unproved
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
    n41 ~~~ n42
    n42 ~~~ n43
    n43 ~~~ n44
    n44 ~~~ n45
    n45 ~~~ n46
    n46 ~~~ n47
    n47 ~~~ n48
    n48 ~~~ n49
    n49 ~~~ n50
    n50 ~~~ n51
    n51 ~~~ n52
    n52 ~~~ n53
    n53 ~~~ n54
    n54 ~~~ n55
    n55 ~~~ n56
    n56 ~~~ n57
    n57 ~~~ n58
    n58 ~~~ n59
    n59 ~~~ n60
    n60 ~~~ n61
    n61 ~~~ n62
    n62 ~~~ n63
    n63 ~~~ n64
    n64 ~~~ n65
    n65 ~~~ n66
    n66 ~~~ n67
    n67 ~~~ n68
    n68 ~~~ n69
    n69 ~~~ n70
    n70 ~~~ n71
    n71 ~~~ n72
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
    n106 ~~~ n107
    n107 ~~~ n108
    n108 ~~~ n109
    n109 ~~~ n110
    n110 ~~~ n111
    n111 ~~~ n112
    n112 ~~~ n113
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
    n10["Goals<br/>dict_roundtrip<br/>Local exact proof"]:::all
    n11["Goals<br/>header_roundtrip<br/>Local exact proof"]:::all
    n12["Goals<br/>deflate_bound_adequate"]:::all
    n13["Goals<br/>compress_bound_adequate"]:::all
    n14["Goals<br/>compress_roundtrip"]:::all
    n15["Goals<br/>gz_roundtrip"]:::all
    n16["Goals<br/>gz_seek_read<br/>Blocked"]:::unproved
    n17["Concrete<br/>compress_bound_value"]:::all
    n18["Concrete<br/>compress2_z_first_alloc_<br/>failure"]:::all
    n122["Inflate<br/>inflate_deferred_distance"]:::all
    n0 ~~~ n1
    n1 ~~~ n2
    n2 ~~~ n3
    n3 ~~~ n4
    n4 ~~~ n5
    n5 ~~~ n6
    n6 ~~~ n7
    n7 ~~~ n8
    n8 ~~~ n9
    n9 ~~~ n10
    n10 ~~~ n11
    n11 ~~~ n12
    n12 ~~~ n13
    n13 ~~~ n14
    n14 ~~~ n15
    n15 ~~~ n16
    n16 ~~~ n17
    n17 ~~~ n18
    n18 ~~~ n122
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
    n114 ~~~ n115
    n115 ~~~ n116
    n116 ~~~ n117
    n117 ~~~ n118
    n118 ~~~ n119
    n119 ~~~ n120
    n120 ~~~ n121
  end
  style lifecycle fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph internal["Internal proof obligations"]
    n132["Crc32ByteViews<br/>crc32_z_all_byte_views"]:::all
    n133["Crc32ByteViews<br/>crc32_all_byte_views"]:::all
    n178["Token<br/>rejected_has_no_symbols<br/>Local exact proof"]:::all
    n179["Token<br/>step_composes_symbols<br/>Local exact proof"]:::all
    n180["Token<br/>symbols_exposes_step<br/>Local exact proof"]:::all
    n132 ~~~ n133
    n133 ~~~ n178
    n178 ~~~ n179
    n179 ~~~ n180
  end
  style internal fill:#f9fafb,stroke:#9ca3af,color:#111827
  click n0 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Api/Goals.lean#L42" "Open exact target statement" _blank
  click n1 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Api/Goals.lean#L47" "Open exact target statement" _blank
  click n2 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Api/Goals.lean#L58" "Open exact target statement" _blank
  click n3 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Api/Goals.lean#L69" "Open exact target statement" _blank
  click n4 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Api/Goals.lean#L84" "Open exact target statement" _blank
  click n5 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Api/Goals.lean#L99" "Open exact target statement" _blank
  click n6 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Api/Goals.lean#L106" "Open exact target statement" _blank
  click n7 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Api/Goals.lean#L116" "Open exact target statement" _blank
  click n8 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Api/Goals.lean#L134" "Open exact target statement" _blank
  click n9 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Api/Goals.lean#L143" "Open exact target statement" _blank
  click n10 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Api/Goals.lean#L162" "Open exact target statement" _blank
  click n11 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Api/Goals.lean#L180" "Open exact target statement" _blank
  click n12 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Api/Goals.lean#L189" "Open exact target statement" _blank
  click n13 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Api/Goals.lean#L196" "Open exact target statement" _blank
  click n14 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Api/Goals.lean#L203" "Open exact target statement" _blank
  click n15 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Api/Goals.lean#L214" "Open exact target statement" _blank
  class n16 obstacle
  click n16 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/docs/overview.md#gzip-seek-mode" "Open blocker reason" _blank
  click n17 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Api/Concrete.lean#L57" "Open exact target statement" _blank
  click n18 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Api/Concrete.lean#L67" "Open exact target statement" _blank
  click n19 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Queries.lean#L35" "Open exact target statement" _blank
  click n20 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Queries.lean#L40" "Open exact target statement" _blank
  click n21 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Queries.lean#L46" "Open exact target statement" _blank
  click n22 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Queries.lean#L53" "Open exact target statement" _blank
  click n23 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Queries.lean#L59" "Open exact target statement" _blank
  click n24 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Checksums.lean#L66" "Open exact target statement" _blank
  click n25 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Checksums.lean#L61" "Open exact target statement" _blank
  click n26 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Checksums.lean#L86" "Open exact target statement" _blank
  click n27 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Checksums.lean#L90" "Open exact target statement" _blank
  click n28 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Checksums.lean#L117" "Open exact target statement" _blank
  click n29 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Checksums.lean#L109" "Open exact target statement" _blank
  click n30 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Checksums.lean#L126" "Open exact target statement" _blank
  click n31 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Checksums.lean#L140" "Open exact target statement" _blank
  click n32 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Checksums.lean#L143" "Open exact target statement" _blank
  click n33 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Checksums.lean#L150" "Open exact target statement" _blank
  click n34 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Checksums.lean#L162" "Open exact target statement" _blank
  click n35 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Checksums.lean#L165" "Open exact target statement" _blank
  click n36 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Back.lean#L22" "Open exact target statement" _blank
  click n37 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Back.lean#L115" "Open exact target statement" _blank
  click n38 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Back.lean#L142" "Open exact target statement" _blank
  click n39 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Copy.lean#L27" "Open exact target statement" _blank
  click n40 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Copy.lean#L67" "Open exact target statement" _blank
  click n41 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/GzClose.lean#L35" "Open exact target statement" _blank
  click n42 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/GzClose.lean#L40" "Open exact target statement" _blank
  click n43 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/GzClose.lean#L44" "Open exact target statement" _blank
  click n44 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/GzControl.lean#L12" "Open exact target statement" _blank
  click n45 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/GzControl.lean#L22" "Open exact target statement" _blank
  click n46 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/GzControl.lean#L36" "Open exact target statement" _blank
  click n47 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/GzControl.lean#L39" "Open exact target statement" _blank
  click n48 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/GzControl.lean#L53" "Open exact target statement" _blank
  click n49 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/GzControl.lean#L56" "Open exact target statement" _blank
  click n50 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/GzControl.lean#L63" "Open exact target statement" _blank
  click n51 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/GzControl.lean#L74" "Open exact target statement" _blank
  click n52 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/GzControl.lean#L91" "Open exact target statement" _blank
  click n53 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/GzControl.lean#L116" "Open exact target statement" _blank
  click n54 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/GzControl.lean#L119" "Open exact target statement" _blank
  click n55 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/GzOpen.lean#L61" "Open exact target statement" _blank
  click n56 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/GzOpen.lean#L65" "Open exact target statement" _blank
  click n57 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/GzOpen.lean#L70" "Open exact target statement" _blank
  click n58 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/GzRead.lean#L22" "Open exact target statement" _blank
  click n59 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/GzRead.lean#L37" "Open exact target statement" _blank
  click n60 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/GzRead.lean#L58" "Open exact target statement" _blank
  click n61 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/GzRead.lean#L61" "Open exact target statement" _blank
  click n62 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/GzRead.lean#L66" "Open exact target statement" _blank
  click n63 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/GzRead.lean#L80" "Open exact target statement" _blank
  click n64 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/GzRead.lean#L103" "Open exact target statement" _blank
  click n65 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/GzWrite.lean#L28" "Open exact target statement" _blank
  click n66 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/GzWrite.lean#L43" "Open exact target statement" _blank
  click n67 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/GzWrite.lean#L59" "Open exact target statement" _blank
  click n68 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/GzWrite.lean#L71" "Open exact target statement" _blank
  click n69 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/GzWrite.lean#L102" "Open exact target statement" _blank
  click n70 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/GzWrite.lean#L106" "Open exact target statement" _blank
  click n71 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/GzWrite.lean#L111" "Open exact target statement" _blank
  click n72 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/GzWrite.lean#L128" "Open exact target statement" _blank
  class n73 obstacle
  click n73 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/docs/overview.md#inflate-initialization-cleanup" "Open blocker reason" _blank
  click n74 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Initialisation.lean#L95" "Open exact target statement" _blank
  click n75 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Initialisation.lean#L138" "Open exact target statement" _blank
  click n76 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Initialisation.lean#L145" "Open exact target statement" _blank
  click n77 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Lifecycle.lean#L20" "Open exact target statement" _blank
  click n78 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Lifecycle.lean#L32" "Open exact target statement" _blank
  click n79 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Lifecycle.lean#L43" "Open exact target statement" _blank
  click n80 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Lifecycle.lean#L60" "Open exact target statement" _blank
  click n81 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Lifecycle.lean#L77" "Open exact target statement" _blank
  click n82 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Lifecycle.lean#L87" "Open exact target statement" _blank
  click n83 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Lifecycle.lean#L105" "Open exact target statement" _blank
  click n84 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Lifecycle.lean#L115" "Open exact target statement" _blank
  click n85 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Lifecycle.lean#L146" "Open exact target statement" _blank
  click n86 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Lifecycle.lean#L149" "Open exact target statement" _blank
  click n87 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Lifecycle.lean#L153" "Open exact target statement" _blank
  click n88 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Lifecycle.lean#L175" "Open exact target statement" _blank
  click n89 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/StreamQueries.lean#L53" "Open exact target statement" _blank
  click n90 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/StreamQueries.lean#L62" "Open exact target statement" _blank
  click n91 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/StreamQueries.lean#L73" "Open exact target statement" _blank
  click n92 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/StreamQueries.lean#L81" "Open exact target statement" _blank
  click n93 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/StreamQueries.lean#L89" "Open exact target statement" _blank
  click n94 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/StreamQueries.lean#L100" "Open exact target statement" _blank
  click n95 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/StreamQueries.lean#L113" "Open exact target statement" _blank
  click n96 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/StreamQueries.lean#L124" "Open exact target statement" _blank
  click n97 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/StreamQueries.lean#L132" "Open exact target statement" _blank
  click n98 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/StreamQueries.lean#L145" "Open exact target statement" _blank
  click n99 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Streams.lean#L24" "Open exact target statement" _blank
  click n100 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Streams.lean#L51" "Open exact target statement" _blank
  click n101 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Streams.lean#L105" "Open exact target statement" _blank
  click n102 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Streams.lean#L109" "Open exact target statement" _blank
  click n103 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Streams.lean#L119" "Open exact target statement" _blank
  click n104 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Streams.lean#L137" "Open exact target statement" _blank
  click n105 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Streams.lean#L160" "Open exact target statement" _blank
  click n106 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Utilities.lean#L40" "Open exact target statement" _blank
  click n107 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Utilities.lean#L45" "Open exact target statement" _blank
  click n108 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Utilities.lean#L52" "Open exact target statement" _blank
  click n109 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Utilities.lean#L57" "Open exact target statement" _blank
  click n110 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Utilities.lean#L103" "Open exact target statement" _blank
  click n111 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Utilities.lean#L107" "Open exact target statement" _blank
  click n112 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Utilities.lean#L132" "Open exact target statement" _blank
  click n113 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Utilities.lean#L136" "Open exact target statement" _blank
  click n114 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Sequences.lean#L158" "Open exact target statement" _blank
  click n115 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Sequences.lean#L172" "Open exact target statement" _blank
  click n116 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Sequences.lean#L199" "Open exact target statement" _blank
  click n117 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Sequences.lean#L211" "Open exact target statement" _blank
  click n118 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Domains.lean#L24" "Open exact target statement" _blank
  click n119 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Domains.lean#L37" "Open exact target statement" _blank
  click n120 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Domains.lean#L53" "Open exact target statement" _blank
  click n121 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Public/Domains.lean#L77" "Open exact target statement" _blank
  click n122 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Api/Inflate.lean#L267" "Open exact target statement" _blank
  click n123 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/ByteAddress.lean#L39" "Open exact target statement" _blank
  click n124 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/ByteAddress.lean#L43" "Open exact target statement" _blank
  click n125 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/ByteAddress.lean#L50" "Open exact target statement" _blank
  click n126 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/ByteAddress.lean#L57" "Open exact target statement" _blank
  click n127 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/ByteAddress.lean#L65" "Open exact target statement" _blank
  click n128 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/ByteAddress.lean#L70" "Open exact target statement" _blank
  click n129 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/ByteAddress.lean#L77" "Open exact target statement" _blank
  click n130 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/ByteAddress.lean#L83" "Open exact target statement" _blank
  click n131 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/ByteAddress.lean#L87" "Open exact target statement" _blank
  click n132 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Crc32ByteViews.lean#L17" "Open exact target statement" _blank
  click n133 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Crc32ByteViews.lean#L28" "Open exact target statement" _blank
  click n134 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/InflateFastBodyOrigin.lean#L18" "Open exact target statement" _blank
  click n135 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/InflateFastBodyToken.lean#L73" "Open exact target statement" _blank
  click n136 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/InflateFastCallOrigin.lean#L24" "Open exact target statement" _blank
  click n137 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/InflateFastDistanceOrigin.lean#L18" "Open exact target statement" _blank
  click n138 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/InflateFastDistanceResult.lean#L101" "Open exact target statement" _blank
  click n139 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/InflateFastDistanceSemantics.lean#L20" "Open exact target statement" _blank
  click n140 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/InflateFast.lean#L68" "Open exact target statement" _blank
  click n141 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/InflateFast.lean#L40" "Open exact target statement" _blank
  click n142 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/InflateFastLengthSemantics.lean#L34" "Open exact target statement" _blank
  click n143 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/InflateFastLengthTrace.lean#L51" "Open exact target statement" _blank
  click n144 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/InflateFastMatchHistory.lean#L39" "Open exact target statement" _blank
  click n145 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/InflateFastMatchHistory.lean#L25" "Open exact target statement" _blank
  click n146 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/InflateFastOrigin.lean#L68" "Open exact target statement" _blank
  click n147 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/InflateFastOrigin.lean#L57" "Open exact target statement" _blank
  click n148 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/InflateFastOrigin.lean#L81" "Open exact target statement" _blank
  click n149 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/InflateFastOrigin.lean#L38" "Open exact target statement" _blank
  click n150 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/InflateFastOrigin.lean#L27" "Open exact target statement" _blank
  click n151 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/InflateFastOrigin.lean#L32" "Open exact target statement" _blank
  click n152 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/InflateFastOrigin.lean#L46" "Open exact target statement" _blank
  click n153 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/InflateDecodeTableRejection.lean#L19" "Open exact target statement" _blank
  click n154 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/InflateDecodeTableSemantics.lean#L51" "Open exact target statement" _blank
  click n155 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/InflateDecodeTableShort.lean#L26" "Open exact target statement" _blank
  click n156 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/InflateDecodeTableSoundness.lean#L31" "Open exact target statement" _blank
  click n157 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/InflateDecodeTableFrame.lean#L20" "Open exact target statement" _blank
  click n158 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/InflateDecodeTableInvariant.lean#L51" "Open exact target statement" _blank
  click n159 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/InflateDecodeTableInvariant.lean#L68" "Open exact target statement" _blank
  click n160 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/InflateDecodeTableStability.lean#L30" "Open exact target statement" _blank
  click n161 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/InflateDecodeTableStability.lean#L43" "Open exact target statement" _blank
  click n162 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/InflateDecodeTableStability.lean#L54" "Open exact target statement" _blank
  click n163 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/InflateFastTableFlags.lean#L52" "Open exact target statement" _blank
  click n164 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/InflateFastTableFlags.lean#L66" "Open exact target statement" _blank
  click n165 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/InflateFastTableFlags.lean#L76" "Open exact target statement" _blank
  click n166 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/InflateFastTableFlags.lean#L42" "Open exact target statement" _blank
  click n167 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/InflateTableContent.lean#L32" "Open exact target statement" _blank
  click n168 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/InflateTableSafety.lean#L28" "Open exact target statement" _blank
  click n169 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/InflateTableExtent.lean#L28" "Open exact target statement" _blank
  click n170 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/InflateRootTable.lean#L21" "Open exact target statement" _blank
  click n171 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/InflateSubtable.lean#L26" "Open exact target statement" _blank
  click n172 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Math/LZ77CopySpec.lean#L22" "Open exact target statement" _blank
  click n173 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Math/LZ77CopySpec.lean#L32" "Open exact target statement" _blank
  click n174 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Math/LZ77HistorySpec.lean#L21" "Open exact target statement" _blank
  click n175 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Math/LZ77HistorySpec.lean#L15" "Open exact target statement" _blank
  click n176 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Math/LZ77HistorySpec.lean#L29" "Open exact target statement" _blank
  click n177 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Math/LZ77HistorySpec.lean#L39" "Open exact target statement" _blank
  click n178 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Format/Token.lean#L84" "Open exact target statement" _blank
  click n179 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Format/Token.lean#L62" "Open exact target statement" _blank
  click n180 href "https://github.com/cla7aye15I4nd/zlib-f/blob/87f98689ee25635b430144ee2826922cfc10ec2b/ZlibF/Spec/Format/Token.lean#L73" "Open exact target statement" _blank
  classDef unproved fill:#e5e7eb,color:#374151,stroke:#374151
  classDef default fill:#dbeafe,color:#1d4ed8,stroke:#1d4ed8
  classDef common fill:#fef3c7,color:#92400e,stroke:#92400e
  classDef all fill:#dcfce7,color:#166534,stroke:#166534
  classDef obstacle stroke:#b91c1c,stroke-width:3px
```

Each node opens its exact target or blocker at the fixed source snapshot
`87f9868`. Some viewers disable diagram links; the
[evidence index](progress.md) provides ordinary links and all proof references.

| Blocked targets | Reason and next step |
| --- | --- |
| [gz_seek_read](./progress.md#target-zlibf-spec-api-goal-gz-seek-read) | [Gzip seek mode](./overview.md#gzip-seek-mode) |
| [inflateInit2_](./progress.md#target-zlibf-spec-public-goal-inflateinit2) | [Inflate initialization cleanup](./overview.md#inflate-initialization-cleanup) |
<!-- proof-progress:end -->

## Recorded checkpoint

The inventory has 95 default-build API entries, four lifecycle targets and four
initialisation-domain targets. A proposition's presence is not a proof.
The latest local declaration audit recognizes 78 registered targets across
398 listed theorems and 20,399 project declarations. The earlier registration batch
covers 59 existing exact proofs: six queries, nine checksum entries, 29 stream or
gzip entries, two initialization-domain goals and 13 abstract model goals.
The [registration review](checking/registration-review.md) records scope and checks.
Earlier format/query and CRC/address/view registrations remain intact.
The audit also tracks 47 internal obligations that were already defined but missing
from the registry. They are internal targets, not additional public APIs.
These are local checks. Final acceptance requires the full audit and CI on a named commit.

The next registration batch has 33 locally checked targets: 31 internal obligations
and the two later dictionary/header model results. Review their exact scopes and
required mutation evidence before registration. Keep mathematical model results
separate from execution/refinement claims about the translated C.

Recorded local work also covers version/flags/error/bound/CRC-table queries;
gzip EOF, buffering, offsets and error queries; inflate state, mark and priming
queries; deflate used-bit, tuning, header and pending queries; internal fast-decoder
safety, bit-source composition and token-output refinement; and canonical-code/leaf/heap tree prefixes.
Further local proofs cover `gzrewind`, `inflateGetHeader`, `inflateResetKeep`,
`inflateReset`, `inflateReset2`, `inflateEnd`, `inflateBackEnd`, `deflateEnd` and
`deflateGetDictionary`, `inflateGetDictionary`, `deflateResetKeep` and `deflateReset`.
Their direct source mutants fail the corresponding function proofs.
The `inflateInit_`, `inflateBackInit_` and both corresponding initialization-domain goals
also check in Lean. Seven initialization mutants fail their function proofs.
The `inflateSetDictionary` goal also checks in Lean; seven source mutants fail
its function proofs.
The abstract-model goals `deflate_bound_adequate` and `deflate_completes` also
check in Lean. These model results do not establish refinement of the C translation.
The abstract `compress_roundtrip` and `gz_roundtrip` goals also check in Lean.
They do not prove the translated buffer or file operations.
The abstract `inflate_completes` goal also checks in Lean, including allocation
failure. It does not establish refinement of translated inflate.
The abstract `deflate_full_flush_resync` goal checks in Lean. It does not establish
refinement of translated deflate.
The abstract `roundtrip` and `roundtrip_completes` goals check in Lean for all
compatible wrappers. Refinement of the C implementation remains open.
The abstract `dict_roundtrip` goal also checks in Lean, including dictionary
identifier mismatches. It does not establish implementation refinement.
The abstract `header_roundtrip` goal also checks in Lean using gzip header
prefix uniqueness. The implementation-level header proof remains open.
The `adler32_combine` and `adler32_combine64` goals also check in Lean;
three negative-length and entry-point mutants fail their function proofs.
The `adler32` and `adler32_z` update goals check in Lean under the documented
zero-length NULL-query restriction. Five update and wrapper mutants fail their proofs.
Five CRC combination and generated-operator goals also check in Lean; one direct
mutation per entry fails its matching function proof.
Source-order corrections and direct proof mutants accompany their stated scopes.
These results do not complete public inflate/deflate or arbitrary call-sequence
correctness. Registration, reviewed locks and acceptance on a named commit remain
separate. A build count is not a completion percentage.

## Remaining work

Targets with red borders have a documented blocker with evidence and a next step below.
A long proof attempt alone does not establish a blocker. Gray targets may be started;
their missing internal lemmas and history invariants are not all drawn in the graph.

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
The [callback migration record](proof/callbacks.md) locates the reusable arguments and
states the limits of their callback domain. These missing premises do not stop independent
work on another block type or error path.

#### Next work for every unfinished public target

"Start" means work can begin without a complete engine theorem. "Compose" names a
prerequisite for full closure; independent branches can still proceed. No row grants
checked status or assumes a callee's specification.

<!-- proof-readiness:start -->
| Public targets | Proof work shown in graph | Next work and missing prerequisite |
| --- | --- | --- |
| `gzopen`, `gzopen64`, `gzdopen`, `gz_initialisation_domain`  | Start: open and cleanup | <a id="readiness-gzopen"></a> **Start:** common mode loop, allocation outcomes, path formatting/copy, descriptor effects, `OpenState` and witnesses. Entry/failure branches are locally checked above. |
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
| `inflateInit2_`  | Blocked: cleanup contract | <a id="readiness-inflateinit2"></a> The confirmed cleanup-contract counterexample is [recorded below](#inflate-initialization-cleanup). Successful init and independent targets can proceed. |
<!-- proof-readiness:end -->

The immediate order is independent entry/cleanup and arithmetic paths, then common open,
position and ownership invariants, then complete function composition. Callback compressed
blocks can progress alongside these. Record an unknown prerequisite here with its exact
question; do not invent a dependency or treat elapsed time as evidence of a blocker.


### Integration

Review the focused function-manual scopes and regenerate the documentation source-policy lock in a
reviewed audit update. Independently review the new source and kernel-syntax locks and the first
verification baseline. Maintain repository protections for the four checks and protected-path
review. Register newly checked results only after their required checks.

### Public contracts

Independently approve the 103 target statements, caller domains and representation limits before
accepting a verification baseline. Extend the ordinary data-epoch refinement to advanced raw
dictionary replacement and all header/priming/recovery combinations; retain their exact per-entry
effects and unconditional sequence safety. No final correctness claim may silently drop those
obligations.

### Specification review

#### Gzip seek mode
<!-- proof-blocker: ZlibF.Spec.Api.Goal.gz_seek_read -->

The abstract `gz_seek_read` goal is false: `GzSeek` permits the resulting handle
to change from read mode to write mode, so the subsequent modeled read can return no data.
The [checked counterexample](../tests/verification/counterexamples/gz-seek-mode.lean)
uses an opened two-byte reader. Review the seek relation before proving this goal.
This is a model issue, not a confirmed zlib issue.

#### Inflate initialization cleanup
<!-- proof-blocker: ZlibF.Spec.Public.Goal.inflateInit2_ -->

The current `inflateInit2_` goal is false for an invalid window parameter. Its
`SameObjects` postcondition requires a structurally unchanged state table, but allocation
followed by free expands that table. The [checked counterexample](../tests/verification/counterexamples/inflate-init2-table-shape.lean)
uses a valid caller heap and proves the sizes are four and zero. Review the contract and
model before proving this goal. This is not a confirmed zlib issue.

Review the corrected shared `Uncompress2` relation independently. The deferred-distance and
exact-free corrections have independent counterexamples and checked regression proofs;
implementation refinement remains open. Its former empty-output clause on memory failure and
extension clause on buffer error have been removed using the existing paired counterexample.
Complete the older abstract gz and dictionary models before using them as complete operational
refinements; the concrete public targets do not assume their callee contracts.

### Translation review

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

### CRC address model

The CRC translation now observes a stable origin residue for every represented static or
embedded byte array. Local proofs cover all residues, seeds and readable lengths for both
public CRC update entries, with the same immutable-heap result. The original 47-byte static
input is now a [positive regression](../tests/verification/regressions/crc-static-address.lean).
The public contracts and caller domains are unchanged. Local evidence still needs final
acceptance checks on the integrated commit.

Extend the representation relation to general ABI layout, effective types, scalar-cell aliases
and byte views of other records. The current address abstraction represents only the low
three bits observed by the CRC alignment test; it is not a complete address-space model.

### Inflate causal model

Complete the universal output and unknown-dictionary refinement against the C. The earlier
whole-lookahead consistency is false; the supporting-bit-prefix correction is reviewed. The fixed
data-error detection lag of eight bytes also has a counterexample; derive a justified replacement
rather than raising the constant without proof. Register the checked `inflate_decodes` model proof,
then establish these conditions for actual decoder runs. Prove the general negative-value priming
bridge, beyond the checked model witnesses and finite execution matrix.

### Differential harness

Keep the new allocation-failure and negative-prime regressions in automated validation. The
test-owned gz handles, input line and deflate buffers are now released. Normal and unsuppressed
sanitizer runs compare all 47,890 inputs. A cleanup mutation confirms that the harness still reports
library state leaked by a missing end call.

### Proof mutants

Complete the remaining legacy lists. Every newly proved public entry must supply direct translation
mutants in the locked mapping and demonstrate failure in its function proof. Unproved entries
acquire their records with their proofs.

### Decode tables

Connect the proved canonical-code coverage and entry-shape lemmas to the heap written by
`inflate_table`; establish the table predicates used by the decoders.

### Inflate

The locally checked internal fast body now emits one independent literal/copy token, ends the
block, or rejects an invalid length code, invalid distance code or too-far match without output.
The actual distance result preserves exact remaining bits and equates copying with independent
bytewise history copying. The token relation has checked composition, decomposition and rejection
results against the original format grammar. Whole-fast-call bit origin also checks through the
loop, byte rollback and final writeback. All these results retain the original safety conclusions.

Establish table meaning, suffix stability, compatible leaf flags and saved-window history from
actual construction, installation and init. Complete whole-fast-call output composition and cover
all legal buffer views. Finish the other decode modes, across-call composition, copy and recovery.
These remain internal-domain results, not registered public proofs. The public inflate and sequence
goals remain open.

### Inflate back

Finish table construction, compressed blocks, callback composition and the complete function.

### Deflate

Finish general initialization (`deflateInit2_`), dictionary setting, priming, copying, `fill_window`,
strategy loops and the complete function. The recovered dictionary-query proof builds and rejects
three translation mutants in its own proof; registration remains.

The exact `Goal.deflateInit_` now has a locally checked proof in
`public-deflate-init`. It expands the actual fixed-parameter call at window
15, memory level 8 and strategy 0. Compression level remains arbitrary.
The proof covers version and parameter refusal, all five allocation
outcomes, failure cleanup, the old-object frame and the exact live-object
ledger. Successful execution establishes `DGood`; it is not a caller
premise. A concrete default caller successfully returns that invariant.
The universal `deflateInit2_` theorem remains open and is not a dependency.

The complete root build, full fresh kernel replay, allowed-axiom inspection
and zero-placeholder scan pass locally. Three direct wrapper mutants
reject the original exact public proof in a fresh kernel. Wrong-symbol-limit
and dropped-cleanup mutants retain the synchronized whole-source equality
but fail their execution proofs with type errors. Resource failures are
not counted. The strict entry mutation list also passes.

The exact default-entry proof and its concrete witness are registered.
Generated locks add 72 semantic records and two theorem-type records.
Existing semantic and theorem-type records are unchanged. Acceptance on
a named CI commit remains. These are local results, not CI approval.

### Trees

Actual `gen_codes`, leaf preparation, heap ordering, and the complete merge/root-storage
prefix have checked internal execution proofs. Node bounds and queue facts derive from the
actual descriptor/reset/scan/repair/order execution. Old heap contents, lengths and depths
remain unrestricted. Each merge executes child selection, tail stores, frequency/depth
updates, parent stores and sift-down in source order. The loop terminates and the final root
store has its exact state effect. Actual callee execution theorems are used.

The actual forest and final root store now establish the bit-length representation premises.
The complete actual `build_tree` executes both code-generation calls under explicit storage
and static-table conditions. The installed literal, distance and bit-length descriptors
discharge the table conditions. Every originally nonzero-frequency symbol receives a positive
limited length and its exact reversed canonical word, which fits that length. No callee
contract is assumed. The actual lengths and stored words now agree with the independent
format's canonical codes and complete-code rule. Its decoder returns each originally used
symbol and preserves every trailing bit suffix.

The constructor's exact frame preserves the caller's output invariant and existing bits.
Actual construction followed by sending one used symbol composes on the same heap, with
independently decodable output. Its fifteen-bit room condition is an explicit internal
obligation; derive it from the block/overlay bound. Initialization and arbitrary legal call
histories remain open. These are internal-state results, not a public deflate theorem.

Actual `scan_tree` terminates, writes its sentinel and records exact wrapping frequency
increments for every run. Actual `build_bl_tree` composes both scans, bit-length-tree
construction, the descending search and the unsigned cost update. Source-code words and
descriptors are preserved. Generic search returns 2..18. Actual block initialization and
source-tree construction establish the stronger 3..18 range, literal/distance count ranges
257..286 and 1..30, and all nineteen bit-length values at most seven. A new call-composition
proof retains the END_BLOCK frequency and unchanged bit-length tree through any list of valid
actual tallies that fits the current block. Actual `init_block`, those tallies and all three
constructors then establish the same header-field ranges on one returned heap. This proves
neither the strategy's input-to-tally history nor preservation across block flushes.

The complete actual `send_tree` now terminates and emits exactly the shared run-length
model. The direct-repeat loop includes its final signed decrement. All repetition branches,
the early continue, next-length reads and the final for-loop iteration execute in source
order. The exact heap frame retains both tree arrays and the existing output prefix.
Actual bit-length construction now supplies the two senders' source capacities, length
bounds and fitted words for every positively scanned symbol. Each such word also has its
independent symbol-decoding result on every suffix. These data follow on one returned heap
from actual `init_block`, any legal within-block tally list and all three constructors.
Exact total bit room remains an internal obligation. Finish `send_all_trees`, independent
run-length/header decoding and the output/symbol overlay bound; individual word decoding
does not establish decoding of the complete run-length sequence.

Three code-assignment, eleven scan/reset/repair, five heapify/descriptor, and seventeen
merge/guard/root-store mutants fail their execution proofs. Complete source equality still
checks independently for the synchronized variants. The three code-assignment mutants also
reject with the complete constructor in the build target. Three direct `send_code` mutations
of its length entry, code entry and emitted length fail its emission proof with the complete
build/send composition as the build target. Five scan and eight bit-length-construction
mutants fail their execution proofs while synchronized whole-function equalities still check.
Three tally mutations of the literal index, match index and full-buffer flag fail their
execution proofs while the complete source equality still checks. Eight `send_tree`
mutations of the repeat decrement, first-code decrement, zero-run threshold, extra-bit
width/base, continue guard, next read and final iteration fail their execution proofs.
Their complete synchronized source equalities still check. These results are not registered
or CI-approved. Finish tree-description emission, full bit-cost refinement, block compression
and the overlay bound, including the small memory levels.

### Other APIs

Finish the compression utilities and the gz read/write/open paths.

### End-to-end claims

Instantiate the heap API, connect the history invariant to the format model, and prove sequence
safety, ownership, termination and functional correctness on the supported configurations.

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
D1–D6, including D5's fresh-memory choice cited by the generated schema.

## Objectives

| ID | Required property |
| --- | --- |
| P1 | Safety and no leaks. |
| P2 | Termination without fuel exhaustion. |
| P3 | Frame: only permitted storage changes. |
| P4 | Invariants and ownership across legal call sequences. |
| P5 | Functional correctness against independent specifications. |
| P6 | Coverage of every upstream CI configuration. |
| C1 | Checksum updates and combinations match their definitions. |
| C2 | Decoding produces justified prefixes, completes under stated conditions and safely reports detected invalid data; memory failure and incomplete input remain explicit. |
| C3 | Completed compression encodes accepted input; compatible decoding recovers it across permitted parameters, splits and flushes. |
| C4 | Header capture and dictionary checks have exact API effects; checksum equality is not dictionary byte equality. |
| C5 | Output-bound adequacy under its documented conditions, separately from numeric equality. |
| C6 | Independent copied ownership and matching continuation; specified reset behaviour. |
| C7 | Gzip data, positions and cleanup across read/write/seek/close histories. |

## Working rules

| ID | Rule |
| --- | --- |
| R1 | Prove actual callees; never assume their contracts. |
| R2 | Init establishes the shared invariant; top-level claims also need witnesses. |
| R3 | Carry safety and functional history through the same actual states. |
| R4 | Connect execution, translation and independent specifications by refinement. |
| R5 | Allowed axioms only; no placeholders or unchecked proof shortcuts. |
| R6 | State narrower domains explicitly and record them in deviations. |
| R7 | Correct translation mismatches for fidelity, never to ease a proof. |
| R8 | Retain C naming/source correspondence; separate heap-free mathematics. |

## Acceptance

Fix the questions, review the baseline, prove exact targets with init/non-vacuity
and proof mutants, then pass final checks on a named commit. The
[checking guide](checking/README.md) defines each stage. Tests are finite evidence.
Read [design](design/README.md), [proof method](proof/method.md),
[safety](safety.md), [trusted base](trusted-base.md) and [limits](deviations.md)
for the full requirements.
