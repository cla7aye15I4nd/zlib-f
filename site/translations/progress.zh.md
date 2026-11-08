<!-- source-sha256: 682c2908b6a765d13de10cc584f1ad12c2ea15c86a7d71996ec0512daf71f5a2 -->
# 证明进度与剩余工作

本页集中记录证明证据和剩余工作。要了解目标陈述和证明的整体结构，请先读[总览](overview.md)。

## 目录

- [全部目标及其依赖](#proof-progress-graph)
- [确切目标的证据](#target-evidence)
- [当前证明范围](#recorded-checkpoint)
- [剩余工作](#remaining-work)
  - [公开 API 的前置证明义务](#public-api-proof-readiness)
  - [规格审查](#specification-review)
  - [解压](#inflate)
  - [压缩](#deflate)
  - [编码树](#trees)
  - [端到端结论](#end-to-end-claims)

<!-- proof-progress:start -->
## 证明进度图

**共有 181 个固定目标：103 个公开目标，78 个支撑目标。**
精确覆盖相应目标的证明中，81 个已登记，46 个仅在本地检查。
这些数字按目标计数，不表示验证工作量的完成百分比，也不代表最终 CI 结果。

**输入覆盖范围的颜色：** ⬜ 未证明 · 🟦 默认输入 · 🟨 常见输入 · 🟩 目标陈述所允许的全部输入。
各档范围统一定义在[输入配置](spec/input-configurations.md)中。
完整的固定目标证明，必须覆盖该目标的确切陈述所允许的全部输入。
若只证明默认输入或常见输入，也必须有经过检查、明确限定范围的契约；局部分支引理和手工填写的标签不能代替这种证明。
输入覆盖范围、证明是否登记、CI 是否通过，是三件不同的事。
红色边框表示已记录的阻碍，不会抹去该目标已经建立的其他覆盖结果。

每个当前固定目标只出现一次。公开 API、内部证明义务和抽象模型分组呈现。
实线表示固定目标之间实际存在的证明复用关系，追踪范围包含经辅助引理间接发生的引用。
虚线表示 C 函数调用，方向由被调用者指向调用者。它并不表示可以把被调用者的完整 API 契约当作证明前提：例如，默认初始化 `Init` 可以独立于通用初始化 `Init2` 完成证明。
只有在同类路径仍然存在时，图中才会省略冗余箭头。[证据索引](progress.md)保留了每条观察到的连接、规格引用和支撑证明族。
这些辅助证明不是额外的最终目标。缺少箭头既不能说明两个目标彼此独立，也不能列全今后需要完成的证明义务。

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
  end
  style fast fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph tables["Decode-table obligations"]
    n153["InflateDecodeTable<br/>Rejection<br/>decode_table_classifies_<br/>input<br/>Local exact proof"]:::all
    n154["InflateDecodeTable<br/>Semantics<br/>decode_table_matches_<br/>format<br/>Local exact proof"]:::all
    n155["InflateDecodeTableShort<br/>short_decode_table_leaf_<br/>sound<br/>Local exact proof"]:::all
    n156["InflateDecodeTable<br/>Soundness<br/>decode_table_leaf_sound<br/>Local exact proof"]:::all
    n157["InflateDecodeTableFrame<br/>decode_table_read_<br/>preserved<br/>Local exact proof"]:::all
    n158["InflateDecodeTable<br/>Invariant<br/>constructor_establishes_<br/>decode_table_invariant<br/>Local exact proof"]:::all
    n159["InflateDecodeTable<br/>Invariant<br/>decode_table_invariant_<br/>of_prefix<br/>Local exact proof"]:::all
    n160["InflateDecodeTable<br/>Stability<br/>constructor_establishes_<br/>query_stability<br/>Local exact proof"]:::all
    n161["InflateDecodeTable<br/>Stability<br/>query_stability_of_prefix<br/>Local exact proof"]:::all
    n162["InflateDecodeTable<br/>Stability<br/>short_rejected_leaf_<br/>stays_invalid<br/>Local exact proof"]:::all
    n163["InflateFastTableFlags<br/>constructor_establishes_<br/>fast_leaf_flags<br/>Local exact proof"]:::all
    n164["InflateFastTableFlags<br/>fast_leaf_flags_of_prefix<br/>Local exact proof"]:::all
    n165["InflateFastTableFlags<br/>fixed_tables_have_fast_<br/>leaf_flags<br/>Local exact proof"]:::all
    n166["InflateFastTableFlags<br/>leaf_classification_<br/>agrees<br/>Local exact proof"]:::all
    n167["InflateTableContent<br/>inflate_table_content"]:::all
    n168["InflateTableSafety<br/>inflate_table_decoder_<br/>safe"]:::all
    n169["InflateTableExtent<br/>inflate_table_read_extent"]:::all
    n170["InflateRootTable<br/>constructor_root_bits<br/>Local exact proof"]:::all
    n171["InflateSubtable<br/>constructor_subtable_bits<br/>Local exact proof"]:::all
  end
  style tables fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph copy["Match-copy mathematics"]
    n172["LZ77CopySpec<br/>output_copy_refines_lz77<br/>Local exact proof"]:::all
    n173["LZ77CopySpec<br/>window_copy_refines_lz77<br/>Local exact proof"]:::all
    n174["LZ77HistorySpec<br/>copy_back_compose<br/>Local exact proof"]:::all
    n175["LZ77HistorySpec<br/>copy_back_extends_history<br/>Local exact proof"]:::all
    n176["LZ77HistorySpec<br/>retained_history_agrees<br/>Local exact proof"]:::all
    n177["LZ77HistorySpec<br/>window_distance_check_<br/>agrees<br/>Local exact proof"]:::all
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
    n178["Token<br/>rejected_has_no_symbols<br/>Local exact proof"]:::all
    n179["Token<br/>step_composes_symbols<br/>Local exact proof"]:::all
    n180["Token<br/>symbols_exposes_step<br/>Local exact proof"]:::all
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
  click n0 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Api/Goals.lean#L42" _blank
  click n1 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Api/Goals.lean#L47" _blank
  click n2 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Api/Goals.lean#L58" _blank
  click n3 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Api/Goals.lean#L69" _blank
  click n4 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Api/Goals.lean#L84" _blank
  click n5 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Api/Goals.lean#L99" _blank
  click n6 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Api/Goals.lean#L106" _blank
  click n7 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Api/Goals.lean#L116" _blank
  click n8 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Api/Goals.lean#L134" _blank
  click n9 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Api/Goals.lean#L143" _blank
  click n10 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Api/Goals.lean#L162" _blank
  click n11 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Api/Goals.lean#L180" _blank
  click n12 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Api/Goals.lean#L189" _blank
  click n13 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Api/Goals.lean#L196" _blank
  click n14 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Api/Goals.lean#L203" _blank
  click n15 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Api/Goals.lean#L214" _blank
  class n16 obstacle
  click n16 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/docs/progress.md#gzip-seek-mode" _blank
  click n17 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Api/Concrete.lean#L57" _blank
  click n18 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Api/Concrete.lean#L67" _blank
  click n19 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Queries.lean#L35" _blank
  click n20 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Queries.lean#L40" _blank
  click n21 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Queries.lean#L46" _blank
  click n22 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Queries.lean#L53" _blank
  click n23 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Queries.lean#L59" _blank
  click n24 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Checksums.lean#L66" _blank
  click n25 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Checksums.lean#L61" _blank
  click n26 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Checksums.lean#L86" _blank
  click n27 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Checksums.lean#L90" _blank
  click n28 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Checksums.lean#L117" _blank
  click n29 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Checksums.lean#L109" _blank
  click n30 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Checksums.lean#L126" _blank
  click n31 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Checksums.lean#L140" _blank
  click n32 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Checksums.lean#L143" _blank
  click n33 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Checksums.lean#L150" _blank
  click n34 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Checksums.lean#L162" _blank
  click n35 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Checksums.lean#L165" _blank
  click n36 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Back.lean#L22" _blank
  click n37 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Back.lean#L115" _blank
  click n38 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Back.lean#L142" _blank
  click n39 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Copy.lean#L27" _blank
  click n40 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Copy.lean#L67" _blank
  click n41 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/GzClose.lean#L35" _blank
  click n42 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/GzClose.lean#L40" _blank
  click n43 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/GzClose.lean#L44" _blank
  click n44 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/GzControl.lean#L12" _blank
  click n45 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/GzControl.lean#L22" _blank
  click n46 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/GzControl.lean#L36" _blank
  click n47 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/GzControl.lean#L39" _blank
  click n48 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/GzControl.lean#L53" _blank
  click n49 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/GzControl.lean#L56" _blank
  click n50 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/GzControl.lean#L63" _blank
  click n51 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/GzControl.lean#L74" _blank
  click n52 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/GzControl.lean#L91" _blank
  click n53 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/GzControl.lean#L116" _blank
  click n54 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/GzControl.lean#L119" _blank
  click n55 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/GzOpen.lean#L61" _blank
  click n56 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/GzOpen.lean#L65" _blank
  click n57 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/GzOpen.lean#L70" _blank
  click n58 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/GzRead.lean#L22" _blank
  click n59 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/GzRead.lean#L37" _blank
  click n60 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/GzRead.lean#L58" _blank
  click n61 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/GzRead.lean#L61" _blank
  click n62 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/GzRead.lean#L66" _blank
  click n63 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/GzRead.lean#L80" _blank
  click n64 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/GzRead.lean#L103" _blank
  click n65 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/GzWrite.lean#L28" _blank
  click n66 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/GzWrite.lean#L43" _blank
  click n67 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/GzWrite.lean#L59" _blank
  click n68 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/GzWrite.lean#L71" _blank
  click n69 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/GzWrite.lean#L102" _blank
  click n70 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/GzWrite.lean#L106" _blank
  click n71 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/GzWrite.lean#L111" _blank
  click n72 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/GzWrite.lean#L128" _blank
  class n73 obstacle
  click n73 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/docs/progress.md#inflate-initialization-cleanup" _blank
  click n74 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Initialisation.lean#L95" _blank
  click n75 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Initialisation.lean#L138" _blank
  click n76 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Initialisation.lean#L145" _blank
  click n77 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Lifecycle.lean#L20" _blank
  click n78 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Lifecycle.lean#L32" _blank
  click n79 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Lifecycle.lean#L43" _blank
  click n80 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Lifecycle.lean#L60" _blank
  click n81 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Lifecycle.lean#L77" _blank
  click n82 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Lifecycle.lean#L87" _blank
  click n83 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Lifecycle.lean#L105" _blank
  click n84 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Lifecycle.lean#L115" _blank
  click n85 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Lifecycle.lean#L146" _blank
  click n86 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Lifecycle.lean#L149" _blank
  click n87 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Lifecycle.lean#L153" _blank
  click n88 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Lifecycle.lean#L175" _blank
  click n89 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/StreamQueries.lean#L53" _blank
  click n90 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/StreamQueries.lean#L62" _blank
  click n91 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/StreamQueries.lean#L73" _blank
  click n92 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/StreamQueries.lean#L81" _blank
  click n93 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/StreamQueries.lean#L89" _blank
  click n94 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/StreamQueries.lean#L100" _blank
  click n95 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/StreamQueries.lean#L113" _blank
  click n96 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/StreamQueries.lean#L124" _blank
  click n97 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/StreamQueries.lean#L132" _blank
  click n98 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/StreamQueries.lean#L145" _blank
  click n99 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Streams.lean#L28" _blank
  click n100 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Streams.lean#L56" _blank
  click n101 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Streams.lean#L110" _blank
  click n102 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Streams.lean#L114" _blank
  click n103 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Streams.lean#L124" _blank
  click n104 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Streams.lean#L142" _blank
  click n105 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Streams.lean#L165" _blank
  click n106 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Utilities.lean#L40" _blank
  click n107 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Utilities.lean#L45" _blank
  click n108 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Utilities.lean#L52" _blank
  click n109 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Utilities.lean#L57" _blank
  click n110 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Utilities.lean#L103" _blank
  click n111 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Utilities.lean#L107" _blank
  click n112 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Utilities.lean#L132" _blank
  click n113 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Utilities.lean#L136" _blank
  click n114 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Sequences.lean#L160" _blank
  click n115 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Sequences.lean#L174" _blank
  click n116 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Sequences.lean#L201" _blank
  click n117 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Sequences.lean#L213" _blank
  click n118 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Domains.lean#L24" _blank
  click n119 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Domains.lean#L37" _blank
  click n120 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Domains.lean#L53" _blank
  click n121 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Public/Domains.lean#L77" _blank
  click n122 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Api/Inflate.lean#L267" _blank
  click n123 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/ByteAddress.lean#L39" _blank
  click n124 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/ByteAddress.lean#L43" _blank
  click n125 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/ByteAddress.lean#L50" _blank
  click n126 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/ByteAddress.lean#L57" _blank
  click n127 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/ByteAddress.lean#L65" _blank
  click n128 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/ByteAddress.lean#L70" _blank
  click n129 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/ByteAddress.lean#L77" _blank
  click n130 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/ByteAddress.lean#L83" _blank
  click n131 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/ByteAddress.lean#L87" _blank
  click n132 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Crc32ByteViews.lean#L17" _blank
  click n133 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Crc32ByteViews.lean#L28" _blank
  click n134 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/InflateFastBodyOrigin.lean#L18" _blank
  click n135 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/InflateFastBodyToken.lean#L73" _blank
  click n136 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/InflateFastCallOrigin.lean#L24" _blank
  click n137 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/InflateFastDistanceOrigin.lean#L18" _blank
  click n138 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/InflateFastDistanceResult.lean#L101" _blank
  click n139 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/InflateFastDistanceSemantics.lean#L20" _blank
  click n140 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/InflateFast.lean#L68" _blank
  click n141 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/InflateFast.lean#L40" _blank
  click n142 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/InflateFastLengthSemantics.lean#L34" _blank
  click n143 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/InflateFastLengthTrace.lean#L51" _blank
  click n144 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/InflateFastMatchHistory.lean#L39" _blank
  click n145 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/InflateFastMatchHistory.lean#L25" _blank
  click n146 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/InflateFastOrigin.lean#L68" _blank
  click n147 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/InflateFastOrigin.lean#L57" _blank
  click n148 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/InflateFastOrigin.lean#L81" _blank
  click n149 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/InflateFastOrigin.lean#L38" _blank
  click n150 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/InflateFastOrigin.lean#L27" _blank
  click n151 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/InflateFastOrigin.lean#L32" _blank
  click n152 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/InflateFastOrigin.lean#L46" _blank
  click n153 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/InflateDecodeTableRejection.lean#L19" _blank
  click n154 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/InflateDecodeTableSemantics.lean#L51" _blank
  click n155 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/InflateDecodeTableShort.lean#L26" _blank
  click n156 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/InflateDecodeTableSoundness.lean#L31" _blank
  click n157 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/InflateDecodeTableFrame.lean#L20" _blank
  click n158 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/InflateDecodeTableInvariant.lean#L51" _blank
  click n159 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/InflateDecodeTableInvariant.lean#L68" _blank
  click n160 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/InflateDecodeTableStability.lean#L30" _blank
  click n161 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/InflateDecodeTableStability.lean#L43" _blank
  click n162 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/InflateDecodeTableStability.lean#L54" _blank
  click n163 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/InflateFastTableFlags.lean#L52" _blank
  click n164 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/InflateFastTableFlags.lean#L66" _blank
  click n165 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/InflateFastTableFlags.lean#L76" _blank
  click n166 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/InflateFastTableFlags.lean#L42" _blank
  click n167 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/InflateTableContent.lean#L32" _blank
  click n168 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/InflateTableSafety.lean#L28" _blank
  click n169 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/InflateTableExtent.lean#L28" _blank
  click n170 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/InflateRootTable.lean#L21" _blank
  click n171 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/InflateSubtable.lean#L26" _blank
  click n172 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Math/LZ77CopySpec.lean#L22" _blank
  click n173 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Math/LZ77CopySpec.lean#L32" _blank
  click n174 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Math/LZ77HistorySpec.lean#L21" _blank
  click n175 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Math/LZ77HistorySpec.lean#L15" _blank
  click n176 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Math/LZ77HistorySpec.lean#L29" _blank
  click n177 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Math/LZ77HistorySpec.lean#L39" _blank
  click n178 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Format/Token.lean#L84" _blank
  click n179 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Format/Token.lean#L62" _blank
  click n180 href "https://github.com/cla7aye15I4nd/zlib-f/blob/4220db49af198b9a387c32f8b559b891ead20b2c/ZlibF/Spec/Format/Token.lean#L73" _blank
  classDef unproved fill:#e5e7eb,color:#374151,stroke:#374151
  classDef default fill:#dbeafe,color:#1d4ed8,stroke:#1d4ed8
  classDef common fill:#fef3c7,color:#92400e,stroke:#92400e
  classDef all fill:#dcfce7,color:#166534,stroke:#166534
  classDef obstacle stroke:#b91c1c,stroke-width:3px
```

展开组件后，再展开一个目标，即可查看它的输入范围、状态和双向依赖。[证据索引](progress.md)保留提交 `4220db4` 的目标与证明链接。

| 存在阻碍的目标 | 原因与下一步 |
| --- | --- |
| [gz_seek_read](./progress.md#target-zlibf-spec-api-goal-gz-seek-read) | [gzip 定位模式](./progress.md#gzip-seek-mode) |
| [inflateInit2_](./progress.md#target-zlibf-spec-public-goal-inflateinit2) | [解压初始化的清理](./progress.md#inflate-initialization-cleanup) |


## 目标证据

<!-- proof-link-revision: 4220db49af198b9a387c32f8b559b891ead20b2c -->

[证明讲解](overview.md) · [全部目标图](#proof-progress-graph) · [输入配置](spec/input-configurations.md)

本索引包含 **181 个固定目标**，分为公开接口执行、调用序列、初始化、实现层义务和抽象模型。每个目标分别列出输入范围、登记情况、证明正文和剩余工作。

抽象模型研究输入输出的数学关系；实现目标还要证明真实执行符合这些关系。一个本地证明完成后，仍需登记，并在具体提交上通过 CI 验收。所有证明都保留命题中写明的前置条件。

依赖区展示记录中已经建立的联系。未完成目标还需要哪些证明，见本页后面的具体工作清单。出现不允许的公理时，生成过程会停止。

## 状态说明

<a id="status-registered"></a>已登记证明：存在精确覆盖该目标、经过检查且列入登记表的定理。
<a id="status-local"></a>本地已检查：存在精确覆盖该目标的定理，但尚未列入登记表。
<a id="status-open"></a>未证明：还没有精确覆盖该目标的定理。
<a id="status-blocked"></a>存在阻碍：已有文档记录影响该目标的具体障碍。
输入覆盖范围单独列出；CI 验收对应具体提交。

<a id="group-queries"></a>

## 库信息查询

| 目标陈述 | 覆盖范围／证据状态 | 契约／输入范围 | 证明证据 | 已审查的后续工作 |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-compressbound"></a>[compressBound](../ZlibF/Spec/Public/Queries.lean#L35) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/utility.md#compressbound); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.compressBound](../ZlibF/Proof/public-compress-bound.lean#L49) | — |
| <a id="target-zlibf-spec-public-goal-compressbound-z"></a>[compressBound_z](../ZlibF/Spec/Public/Queries.lean#L40) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/utility.md#compressbound_z); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.compressBound_z](../ZlibF/Proof/public-compress-bound.lean#L46) | — |
| <a id="target-zlibf-spec-public-goal-zlibversion"></a>[zlibVersion](../ZlibF/Spec/Public/Queries.lean#L46) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/utility.md#zlibversion); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.zlibVersion](../ZlibF/Proof/public-zlib-version.lean#L8) | — |
| <a id="target-zlibf-spec-public-goal-zlibcompileflags"></a>[zlibCompileFlags](../ZlibF/Spec/Public/Queries.lean#L53) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/utility.md#zlibcompileflags); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.zlibCompileFlags](../ZlibF/Proof/public-zlib-compile-flags.lean#L6) | — |
| <a id="target-zlibf-spec-public-goal-zerror"></a>[zError](../ZlibF/Spec/Public/Queries.lean#L59) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/utility.md#zerror); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.zError](../ZlibF/Proof/public-zerror.lean#L37) | — |
| <a id="target-zlibf-spec-public-goal-get-crc-table"></a>[get_crc_table](../ZlibF/Spec/Public/Checksums.lean#L126) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/checksums.md#get_crc_table); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.get_crc_table](../ZlibF/Proof/public-get-crc-table.lean#L13) | — |

<a id="group-checksums"></a>

## 校验和

| 目标陈述 | 覆盖范围／证据状态 | 契约／输入范围 | 证明证据 | 已审查的后续工作 |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-adler32"></a>[adler32](../ZlibF/Spec/Public/Checksums.lean#L66) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/checksums.md#adler32); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.AdlerUpdateProof.adler_public](../ZlibF/Proof/public-adler-update.lean#L46) | — |
| <a id="target-zlibf-spec-public-goal-adler32-z"></a>[adler32_z](../ZlibF/Spec/Public/Checksums.lean#L61) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/checksums.md#adler32_z); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.AdlerUpdateProof.adler_z_public](../ZlibF/Proof/public-adler-update.lean#L36) | — |
| <a id="target-zlibf-spec-public-goal-adler32-combine"></a>[adler32_combine](../ZlibF/Spec/Public/Checksums.lean#L86) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/checksums.md#adler32_combine); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.AdlerCombineProof.combine_public](../ZlibF/Proof/public-adler-combine.lean#L118) | — |
| <a id="target-zlibf-spec-public-goal-adler32-combine64"></a>[adler32_combine64](../ZlibF/Spec/Public/Checksums.lean#L90) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/checksums.md#adler32_combine64); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.AdlerCombineProof.combine64_public](../ZlibF/Proof/public-adler-combine.lean#L121) | — |
| <a id="target-zlibf-spec-public-goal-crc32"></a>[crc32](../ZlibF/Spec/Public/Checksums.lean#L117) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/checksums.md#crc32); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.crc32](../ZlibF/Proof/public-crc-updates.lean#L28) | — |
| <a id="target-zlibf-spec-public-goal-crc32-z"></a>[crc32_z](../ZlibF/Spec/Public/Checksums.lean#L109) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/checksums.md#crc32_z); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.crc32_z](../ZlibF/Proof/public-crc-updates.lean#L18) | — |
| <a id="target-zlibf-spec-public-goal-crc32-combine-gen"></a>[crc32_combine_gen](../ZlibF/Spec/Public/Checksums.lean#L140) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/checksums.md#crc32_combine_gen); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.CrcCombineProof.gen](../ZlibF/Proof/public-crc-combine.lean#L76) | — |
| <a id="target-zlibf-spec-public-goal-crc32-combine-gen64"></a>[crc32_combine_gen64](../ZlibF/Spec/Public/Checksums.lean#L143) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/checksums.md#crc32_combine_gen64); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.CrcCombineProof.gen64](../ZlibF/Proof/public-crc-combine.lean#L82) | — |
| <a id="target-zlibf-spec-public-goal-crc32-combine-op"></a>[crc32_combine_op](../ZlibF/Spec/Public/Checksums.lean#L150) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/checksums.md#crc32_combine_op); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.CrcCombineProof.op](../ZlibF/Proof/public-crc-combine.lean#L88) | — |
| <a id="target-zlibf-spec-public-goal-crc32-combine"></a>[crc32_combine](../ZlibF/Spec/Public/Checksums.lean#L162) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/checksums.md#crc32_combine); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.CrcCombineProof.combine](../ZlibF/Proof/public-crc-combine.lean#L94) | — |
| <a id="target-zlibf-spec-public-goal-crc32-combine64"></a>[crc32_combine64](../ZlibF/Spec/Public/Checksums.lean#L165) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/checksums.md#crc32_combine64); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.CrcCombineProof.combine64](../ZlibF/Proof/public-crc-combine.lean#L100) | — |

<a id="group-addresses"></a>

## 字节地址模型

| 目标陈述 | 覆盖范围／证据状态 | 契约／输入范围 | 证明证据 | 已审查的后续工作 |
| --- | --- | --- | --- | --- |
| <a id="target-c-byteaddress-spec-goal-address-read-is-pure"></a>[address_read_is_pure](../ZlibF/Spec/ByteAddress.lean#L39) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.address_read_is_pure](../ZlibF/Proof/ByteAddress.lean#L28) | — |
| <a id="target-c-byteaddress-spec-goal-raw-block-unchanged"></a>[raw_block_unchanged](../ZlibF/Spec/ByteAddress.lean#L43) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.raw_block_unchanged](../ZlibF/Proof/ByteAddress.lean#L33) | — |
| <a id="target-c-byteaddress-spec-goal-every-layout-is-representable"></a>[every_layout_is_representable](../ZlibF/Spec/ByteAddress.lean#L50) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.every_layout_is_representable](../ZlibF/Proof/ByteAddress.lean#L39) | — |
| <a id="target-c-byteaddress-spec-goal-every-existing-heap-accepts-layout"></a>[every_existing_heap_accepts_layout](../ZlibF/Spec/ByteAddress.lean#L57) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.every_existing_heap_accepts_layout](../ZlibF/Proof/ByteAddress.lean#L94) | — |
| <a id="target-c-byteaddress-spec-goal-mask-refines-base-plus-offset"></a>[mask_refines_base_plus_offset](../ZlibF/Spec/ByteAddress.lean#L65) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.mask_refines_base_plus_offset](../ZlibF/Proof/ByteAddress.lean#L54) | — |
| <a id="target-c-byteaddress-spec-goal-pointer-advance-preserves-low-bits"></a>[pointer_advance_preserves_low_bits](../ZlibF/Spec/ByteAddress.lean#L70) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.pointer_advance_preserves_low_bits](../ZlibF/Proof/ByteAddress.lean#L60) | — |
| <a id="target-c-byteaddress-spec-goal-first-aligned-offset"></a>[first_aligned_offset](../ZlibF/Spec/ByteAddress.lean#L77) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.first_aligned_offset](../ZlibF/Proof/ByteAddress.lean#L67) | — |
| <a id="target-c-byteaddress-spec-goal-byte-stores-preserve-bases"></a>[byte_stores_preserve_bases](../ZlibF/Spec/ByteAddress.lean#L83) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.byte_stores_preserve_bases](../ZlibF/Proof/ByteAddress.lean#L81) | — |
| <a id="target-c-byteaddress-spec-goal-byte-modifies-preserve-bases"></a>[byte_modifies_preserve_bases](../ZlibF/Spec/ByteAddress.lean#L87) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.byte_modifies_preserve_bases](../ZlibF/Proof/ByteAddress.lean#L88) | — |

<a id="group-inflate"></a>

## 解压流

| 目标陈述 | 覆盖范围／证据状态 | 契约／输入范围 | 证明证据 | 已审查的后续工作 |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-inflatecopy"></a>[inflateCopy](../ZlibF/Spec/Public/Copy.lean#L27) | 未证明 / 未证明 | [契约](../docs/spec/api/inflate-stream.md#inflatecopy); [输入范围](spec/input-configurations.md#inflate-inputs) | — | [起点：复制与指针重定位](progress.md#readiness-inflatecopy) |
| <a id="target-zlibf-spec-public-goal-inflateinit2"></a>[inflateInit2_](../ZlibF/Spec/Public/Initialisation.lean#L90) | 未证明 / 存在阻碍 | [契约](../docs/spec/api/inflate-stream.md#inflateinit2_); [输入范围](spec/input-configurations.md#inflate-inputs) | — [阻碍：解压初始化的清理](progress.md#inflate-initialization-cleanup) | [阻碍：清理契约](progress.md#readiness-inflateinit2) |
| <a id="target-zlibf-spec-public-goal-inflateinit"></a>[inflateInit_](../ZlibF/Spec/Public/Initialisation.lean#L95) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/inflate-stream.md#inflateinit_); [输入范围](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.Proofs.InflateInit.init15_public](../ZlibF/Proof/public-inflate-init.lean#L83) | — |
| <a id="target-zlibf-spec-public-goal-inflateresetkeep"></a>[inflateResetKeep](../ZlibF/Spec/Public/Lifecycle.lean#L20) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/inflate-stream.md#inflateresetkeep); [输入范围](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateResetKeepProof.resetkeep_public](../ZlibF/Proof/public-inflate-reset-keep.lean#L8) | — |
| <a id="target-zlibf-spec-public-goal-inflatereset"></a>[inflateReset](../ZlibF/Spec/Public/Lifecycle.lean#L32) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/inflate-stream.md#inflatereset); [输入范围](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateResetProof.reset_public](../ZlibF/Proof/public-inflate-reset.lean#L16) | — |
| <a id="target-zlibf-spec-public-goal-inflatereset2"></a>[inflateReset2](../ZlibF/Spec/Public/Lifecycle.lean#L43) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/inflate-stream.md#inflatereset2); [输入范围](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateReset2Proof.reset2_public](../ZlibF/Proof/public-inflate-reset2.lean#L61) | — |
| <a id="target-zlibf-spec-public-goal-inflateend"></a>[inflateEnd](../ZlibF/Spec/Public/Lifecycle.lean#L60) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/inflate-stream.md#inflateend); [输入范围](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateEndProof.inflate_end_public](../ZlibF/Proof/public-inflate-end.lean#L55) | — |
| <a id="target-zlibf-spec-public-goal-inflategetdictionary"></a>[inflateGetDictionary](../ZlibF/Spec/Public/Lifecycle.lean#L77) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/inflate-stream.md#inflategetdictionary); [输入范围](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateDictionaryProof.inflate_getdict_public](../ZlibF/Proof/public-inflate-getdict.lean#L10) | — |
| <a id="target-zlibf-spec-public-goal-inflategetheader"></a>[inflateGetHeader](../ZlibF/Spec/Public/Lifecycle.lean#L87) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/inflate-stream.md#inflategetheader); [输入范围](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateHeaderProof.getheader_public](../ZlibF/Proof/public-inflate-header.lean#L34) | — |
| <a id="target-zlibf-spec-public-goal-inflatesetdictionary"></a>[inflateSetDictionary](../ZlibF/Spec/Public/Lifecycle.lean#L153) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/inflate-stream.md#inflatesetdictionary); [输入范围](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.Proofs.inflateSetDictionary_public](../ZlibF/Proof/public-inflate-setdict.lean#L92) | — |
| <a id="target-zlibf-spec-public-goal-inflatesyncpoint"></a>[inflateSyncPoint](../ZlibF/Spec/Public/StreamQueries.lean#L53) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/inflate-stream.md#inflatesyncpoint); [输入范围](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateQueryProof.syncpoint_public](../ZlibF/Proof/public-inflate-small-queries.lean#L44) | — |
| <a id="target-zlibf-spec-public-goal-inflatemark"></a>[inflateMark](../ZlibF/Spec/Public/StreamQueries.lean#L62) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/inflate-stream.md#inflatemark); [输入范围](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateMarkProof.mark_public](../ZlibF/Proof/public-inflate-mark.lean#L71) | — |
| <a id="target-zlibf-spec-public-goal-inflatecodesused"></a>[inflateCodesUsed](../ZlibF/Spec/Public/StreamQueries.lean#L73) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/inflate-stream.md#inflatecodesused); [输入范围](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.Proofs.inflate_codes_used](../ZlibF/Proof/Api/QueryLayout.lean#L71) | — |
| <a id="target-zlibf-spec-public-goal-inflateundermine"></a>[inflateUndermine](../ZlibF/Spec/Public/StreamQueries.lean#L81) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/inflate-stream.md#inflateundermine); [输入范围](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateQueryProof.undermine_public](../ZlibF/Proof/public-inflate-small-queries.lean#L60) | — |
| <a id="target-zlibf-spec-public-goal-inflatevalidate"></a>[inflateValidate](../ZlibF/Spec/Public/StreamQueries.lean#L89) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/inflate-stream.md#inflatevalidate); [输入范围](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateQueryProof.validate_public](../ZlibF/Proof/public-inflate-small-queries.lean#L75) | — |
| <a id="target-zlibf-spec-public-goal-inflateprime"></a>[inflatePrime](../ZlibF/Spec/Public/StreamQueries.lean#L100) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/inflate-stream.md#inflateprime); [输入范围](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflatePrimeProof.prime_public](../ZlibF/Proof/public-inflate-prime.lean#L117) | — |
| <a id="target-zlibf-spec-public-goal-inflate"></a>[inflate](../ZlibF/Spec/Public/Streams.lean#L28) | 未证明 / 未证明 | [契约](../docs/spec/api/inflate-stream.md#inflate); [输入范围](spec/input-configurations.md#inflate-inputs) | — | [所需：状态分派不变量](progress.md#readiness-inflate) |
| <a id="target-zlibf-spec-public-goal-inflatesync"></a>[inflateSync](../ZlibF/Spec/Public/Streams.lean#L165) | 未证明 / 未证明 | [契约](../docs/spec/api/inflate-stream.md#inflatesync); [输入范围](spec/input-configurations.md#inflate-inputs) | — | [所需：扫描与状态序列证明](progress.md#readiness-inflatesync) |

<a id="group-fast"></a>

## 快速解码器的证明义务

| 目标陈述 | 覆盖范围／证据状态 | 契约／输入范围 | 证明证据 | 已审查的后续工作 |
| --- | --- | --- | --- | --- |
| <a id="target-zlib-inffast-spec-bodyorigin-goal-actual-body-preserves-origin"></a>[actual_body_preserves_origin](../ZlibF/Spec/InflateFastBodyOrigin.lean#L18) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.BodyOriginProof.actual_body_preserves_origin](../ZlibF/Proof/inffast.c.body-origin.lean#L374); [Zlib.Inffast.Proofs.actual_body_preserves_origin](../ZlibF/Proof/inffast.c.body-origin.lean#L374) | — |
| <a id="target-zlib-inffast-spec-bodytoken-goal-actual-body-refines-token"></a>[actual_body_refines_token](../ZlibF/Spec/InflateFastBodyToken.lean#L73) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.BodyTokenProof.actual_body_refines_token](../ZlibF/Proof/inffast.c.body-token.lean#L564); [Zlib.Inffast.Proofs.actual_body_refines_token](../ZlibF/Proof/inffast.c.body-token.lean#L564) | — |
| <a id="target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin"></a>[actual_fast_preserves_origin](../ZlibF/Spec/InflateFastCallOrigin.lean#L24) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_fast_preserves_origin](../ZlibF/Proof/inffast.c.call-origin.lean#L176) | — |
| <a id="target-zlib-inffast-spec-distanceorigin-goal-actual-distance-block-preserves-origin"></a>[actual_distance_block_preserves_origin](../ZlibF/Spec/InflateFastDistanceOrigin.lean#L18) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_distance_block_preserves_origin](../ZlibF/Proof/inffast.c.distance-origin.lean#L324) | — |
| <a id="target-zlib-inffast-spec-distanceresult-goal-actual-distance-refines-lz77"></a>[actual_distance_refines_lz77](../ZlibF/Spec/InflateFastDistanceResult.lean#L101) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_distance_refines_lz77](../ZlibF/Proof/inffast.c.distance-result.lean#L382) | — |
| <a id="target-zlib-inffast-spec-distancesemantics-goal-distance-lookup-matches-format"></a>[distance_lookup_matches_format](../ZlibF/Spec/InflateFastDistanceSemantics.lean#L20) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.distance_lookup_matches_format](../ZlibF/Proof/inffast.c.distance-semantics.lean#L22) | — |
| <a id="target-zlib-inffast-spec-goal-fast-safe"></a>[fast_safe](../ZlibF/Spec/InflateFast.lean#L68) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.inflate_fast_safe](../ZlibF/Proof/inffast.c.final.lean#L257) | — |
| <a id="target-zlib-inffast-spec-goal-step-safe"></a>[step_safe](../ZlibF/Spec/InflateFast.lean#L40) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.inflate_fast_body_step_safe](../ZlibF/Proof/inffast.c.body.lean#L315) | — |
| <a id="target-zlib-inffast-spec-lengthsemantics-goal-length-lookup-matches-format"></a>[length_lookup_matches_format](../ZlibF/Spec/InflateFastLengthSemantics.lean#L34) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.length_lookup_matches_format](../ZlibF/Proof/inffast.c.length-semantics.lean#L22) | — |
| <a id="target-zlib-inffast-spec-lengthtrace-goal-actual-body-retains-selected-length"></a>[actual_body_retains_selected_length](../ZlibF/Spec/InflateFastLengthTrace.lean#L51) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.LengthTraceProof.actual_body_retains_selected_length](../ZlibF/Proof/inffast.c.length-trace.lean#L247); [Zlib.Inffast.Proofs.actual_body_retains_selected_length](../ZlibF/Proof/inffast.c.length-trace.lean#L247) | — |
| <a id="target-zlib-inffast-spec-matchhistory-goal-actual-copy-match-refines-lz77"></a>[actual_copy_match_refines_lz77](../ZlibF/Spec/InflateFastMatchHistory.lean#L39) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_copy_match_refines_lz77](../ZlibF/Proof/inffast.c.match-history.lean#L329) | — |
| <a id="target-zlib-inffast-spec-matchhistory-goal-match-array-refines-lz77"></a>[match_array_refines_lz77](../ZlibF/Spec/InflateFastMatchHistory.lean#L25) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.fast_match_array_refines_lz77](../ZlibF/Math/InflateFastMatchHistory.lean#L56) | — |
| <a id="target-zlib-inffast-spec-origin-goal-actual-drop-preserves-origin"></a>[actual_drop_preserves_origin](../ZlibF/Spec/InflateFastOrigin.lean#L68) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_drop_preserves_origin](../ZlibF/Proof/inffast.c.origin.lean#L138) | — |
| <a id="target-zlib-inffast-spec-origin-goal-actual-pull-preserves-origin"></a>[actual_pull_preserves_origin](../ZlibF/Spec/InflateFastOrigin.lean#L57) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_pull_preserves_origin](../ZlibF/Proof/inffast.c.origin.lean#L127) | — |
| <a id="target-zlib-inffast-spec-origin-goal-actual-rollback-preserves-origin"></a>[actual_rollback_preserves_origin](../ZlibF/Spec/InflateFastOrigin.lean#L81) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_rollback_preserves_origin](../ZlibF/Proof/inffast.c.origin.lean#L150) | — |
| <a id="target-zlib-inffast-spec-origin-goal-drop-preserves-origin"></a>[drop_preserves_origin](../ZlibF/Spec/InflateFastOrigin.lean#L38) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.drop_preserves_origin](../ZlibF/Proof/inffast.c.origin.lean#L41) | — |
| <a id="target-zlib-inffast-spec-origin-goal-initial-origin"></a>[initial_origin](../ZlibF/Spec/InflateFastOrigin.lean#L27) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.initial_origin](../ZlibF/Proof/inffast.c.origin.lean#L16) | — |
| <a id="target-zlib-inffast-spec-origin-goal-pull-preserves-origin"></a>[pull_preserves_origin](../ZlibF/Spec/InflateFastOrigin.lean#L32) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.pull_preserves_origin](../ZlibF/Proof/inffast.c.origin.lean#L21) | — |
| <a id="target-zlib-inffast-spec-origin-goal-rollback-preserves-origin"></a>[rollback_preserves_origin](../ZlibF/Spec/InflateFastOrigin.lean#L46) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.rollback_preserves_origin](../ZlibF/Proof/inffast.c.origin.lean#L83) | — |

<a id="group-tables"></a>

## 解码表的证明义务

| 目标陈述 | 覆盖范围／证据状态 | 契约／输入范围 | 证明证据 | 已审查的后续工作 |
| --- | --- | --- | --- | --- |
| <a id="target-zlib-inftrees-spec-decoderejection-goal-decode-table-classifies-input"></a>[decode_table_classifies_input](../ZlibF/Spec/InflateDecodeTableRejection.lean#L19) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.decode_table_classifies_input](../ZlibF/Proof/inftrees.c.decode.short.lean#L62) | — |
| <a id="target-zlib-inftrees-spec-decodesemantics-goal-decode-table-matches-format"></a>[decode_table_matches_format](../ZlibF/Spec/InflateDecodeTableSemantics.lean#L51) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.decode_table_matches_format](../ZlibF/Proof/inftrees.c.decode.semantics.lean#L327) | — |
| <a id="target-zlib-inftrees-spec-decodeshort-goal-short-decode-table-leaf-sound"></a>[short_decode_table_leaf_sound](../ZlibF/Spec/InflateDecodeTableShort.lean#L26) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.short_decode_table_leaf_sound](../ZlibF/Proof/inftrees.c.decode.short.lean#L33) | — |
| <a id="target-zlib-inftrees-spec-decodesoundness-goal-decode-table-leaf-sound"></a>[decode_table_leaf_sound](../ZlibF/Spec/InflateDecodeTableSoundness.lean#L31) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.decode_table_leaf_sound](../ZlibF/Proof/inftrees.c.decode.soundness.lean#L244) | — |
| <a id="target-zlib-inftrees-spec-decodetableframe-goal-decode-table-read-preserved"></a>[decode_table_read_preserved](../ZlibF/Spec/InflateDecodeTableFrame.lean#L20) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.decode_table_read_preserved](../ZlibF/Proof/inftrees.c.decode.frame.lean#L55) | — |
| <a id="target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant"></a>[constructor_establishes_decode_table_invariant](../ZlibF/Spec/InflateDecodeTableInvariant.lean#L51) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.constructor_establishes_decode_table_invariant](../ZlibF/Proof/inftrees.c.decode.invariant.lean#L13) | — |
| <a id="target-zlib-inftrees-spec-decodetableinvariant-goal-decode-table-invariant-of-prefix"></a>[decode_table_invariant_of_prefix](../ZlibF/Spec/InflateDecodeTableInvariant.lean#L68) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.decode_table_invariant_of_prefix](../ZlibF/Proof/inftrees.c.decode.invariant-prefix.lean#L22) | — |
| <a id="target-zlib-inftrees-spec-decodetablestability-goal-constructor-establishes-query-stability"></a>[constructor_establishes_query_stability](../ZlibF/Spec/InflateDecodeTableStability.lean#L30) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.constructor_establishes_query_stability](../ZlibF/Proof/inftrees.c.decode.stability.lean#L190) | — |
| <a id="target-zlib-inftrees-spec-decodetablestability-goal-query-stability-of-prefix"></a>[query_stability_of_prefix](../ZlibF/Spec/InflateDecodeTableStability.lean#L43) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.query_stability_of_prefix](../ZlibF/Proof/inftrees.c.decode.stability-rejection.lean#L20) | — |
| <a id="target-zlib-inftrees-spec-decodetablestability-goal-short-rejected-leaf-stays-invalid"></a>[short_rejected_leaf_stays_invalid](../ZlibF/Spec/InflateDecodeTableStability.lean#L54) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.short_rejected_leaf_stays_invalid](../ZlibF/Proof/inftrees.c.decode.stability-rejection.lean#L31) | — |
| <a id="target-zlib-inftrees-spec-fasttableflags-goal-constructor-establishes-fast-leaf-flags"></a>[constructor_establishes_fast_leaf_flags](../ZlibF/Spec/InflateFastTableFlags.lean#L52) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.constructor_establishes_fast_leaf_flags](../ZlibF/Proof/inftrees.c.decode.fast-flags.lean#L125) | — |
| <a id="target-zlib-inftrees-spec-fasttableflags-goal-fast-leaf-flags-of-prefix"></a>[fast_leaf_flags_of_prefix](../ZlibF/Spec/InflateFastTableFlags.lean#L66) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.fast_leaf_flags_of_prefix](../ZlibF/Proof/inftrees.c.decode.fast-flags-frame.lean#L48) | — |
| <a id="target-zlib-inftrees-spec-fasttableflags-goal-fixed-tables-have-fast-leaf-flags"></a>[fixed_tables_have_fast_leaf_flags](../ZlibF/Spec/InflateFastTableFlags.lean#L76) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.fixed_tables_have_fast_leaf_flags](../ZlibF/Proof/inffixed.h.fast-flags.lean#L55) | — |
| <a id="target-zlib-inftrees-spec-fasttableflags-goal-leaf-classification-agrees"></a>[leaf_classification_agrees](../ZlibF/Spec/InflateFastTableFlags.lean#L42) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.leaf_classification_agrees](../ZlibF/Proof/inftrees.c.decode.fast-flags-frame.lean#L9) | — |
| <a id="target-zlib-inftrees-spec-goal-inflate-table-content"></a>[inflate_table_content](../ZlibF/Spec/InflateTableContent.lean#L32) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.inflate_table_content](../ZlibF/Proof/inftrees.c.content.lean#L327) | — |
| <a id="target-zlib-inftrees-spec-goal-inflate-table-decoder-safe"></a>[inflate_table_decoder_safe](../ZlibF/Spec/InflateTableSafety.lean#L28) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.inflate_table_decoder_safe](../ZlibF/Proof/inftrees.c.decoder-safe.lean#L93) | — |
| <a id="target-zlib-inftrees-spec-goal-inflate-table-read-extent"></a>[inflate_table_read_extent](../ZlibF/Spec/InflateTableExtent.lean#L28) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.inflate_table_read_extent](../ZlibF/Proof/inftrees.c.read-extent.lean#L139) | — |
| <a id="target-zlib-inftrees-spec-roottable-goal-constructor-root-bits"></a>[constructor_root_bits](../ZlibF/Spec/InflateRootTable.lean#L21) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.constructor_root_bits](../ZlibF/Proof/inftrees.c.decode.bits.lean#L260) | — |
| <a id="target-zlib-inftrees-spec-subtable-goal-constructor-subtable-bits"></a>[constructor_subtable_bits](../ZlibF/Spec/InflateSubtable.lean#L26) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.constructor_subtable_bits](../ZlibF/Proof/inftrees.c.decode.bits.lean#L221) | — |

<a id="group-copy"></a>

## 回引用复制

| 目标陈述 | 覆盖范围／证据状态 | 契约／输入范围 | 证明证据 | 已审查的后续工作 |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-math-lz77copy-goal-output-copy-refines-lz77"></a>[output_copy_refines_lz77](../ZlibF/Math/LZ77CopySpec.lean#L22) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Math.LZ77Copy.output_copy_refines_lz77](../ZlibF/Math/LZ77Copy.lean#L65) | — |
| <a id="target-zlibf-math-lz77copy-goal-window-copy-refines-lz77"></a>[window_copy_refines_lz77](../ZlibF/Math/LZ77CopySpec.lean#L32) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Math.LZ77Copy.window_copy_refines_lz77](../ZlibF/Math/LZ77Copy.lean#L124) | — |
| <a id="target-zlibf-math-lz77history-goal-copy-back-compose"></a>[copy_back_compose](../ZlibF/Math/LZ77HistorySpec.lean#L21) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Math.LZ77History.copy_back_compose](../ZlibF/Math/LZ77History.lean#L31) | — |
| <a id="target-zlibf-math-lz77history-goal-copy-back-extends-history"></a>[copy_back_extends_history](../ZlibF/Math/LZ77HistorySpec.lean#L15) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Math.LZ77History.copy_back_extends_history](../ZlibF/Math/LZ77History.lean#L17) | — |
| <a id="target-zlibf-math-lz77history-goal-retained-history-agrees"></a>[retained_history_agrees](../ZlibF/Math/LZ77HistorySpec.lean#L29) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Math.LZ77History.retained_history_agrees](../ZlibF/Math/LZ77History.lean#L59) | — |
| <a id="target-zlibf-math-lz77history-goal-window-distance-check-agrees"></a>[window_distance_check_agrees](../ZlibF/Math/LZ77HistorySpec.lean#L39) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Math.LZ77History.window_distance_check_agrees](../ZlibF/Math/LZ77History.lean#L72) | — |

<a id="group-deflate"></a>

## 压缩流

| 目标陈述 | 覆盖范围／证据状态 | 契约／输入范围 | 证明证据 | 已审查的后续工作 |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-deflatecopy"></a>[deflateCopy](../ZlibF/Spec/Public/Copy.lean#L67) | 未证明 / 未证明 | [契约](../docs/spec/api/deflate-stream.md#deflatecopy); [输入范围](spec/input-configurations.md#deflate-inputs) | — | [起点：复制与指针重定位](progress.md#readiness-inflatecopy) |
| <a id="target-zlibf-spec-public-goal-deflateinit2"></a>[deflateInit2_](../ZlibF/Spec/Public/Initialisation.lean#L138) | 未证明 / 未证明 | [契约](../docs/spec/api/deflate-stream.md#deflateinit2_); [输入范围](spec/input-configurations.md#deflate-inputs) | — | [起点：初始化与分配](progress.md#readiness-deflateinit2) |
| <a id="target-zlibf-spec-public-goal-deflateinit"></a>[deflateInit_](../ZlibF/Spec/Public/Initialisation.lean#L145) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/deflate-stream.md#deflateinit_); [输入范围](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.Proofs.DeflateInit.deflateInit_proof](../ZlibF/Proof/public-deflate-init.lean#L161) | — |
| <a id="target-zlibf-spec-public-goal-deflategetdictionary"></a>[deflateGetDictionary](../ZlibF/Spec/Public/Lifecycle.lean#L105) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/deflate-stream.md#deflategetdictionary); [输入范围](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateDictionaryProof.deflate_getdict_public](../ZlibF/Proof/public-deflate-getdict.lean#L10) | — |
| <a id="target-zlibf-spec-public-goal-deflateend"></a>[deflateEnd](../ZlibF/Spec/Public/Lifecycle.lean#L115) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/deflate-stream.md#deflateend); [输入范围](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateEndProof.deflate_end_public](../ZlibF/Proof/public-deflate-end.lean#L10) | — |
| <a id="target-zlibf-spec-public-goal-deflateresetkeep"></a>[deflateResetKeep](../ZlibF/Spec/Public/Lifecycle.lean#L146) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/deflate-stream.md#deflateresetkeep); [输入范围](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateResetKeepProof.deflate_resetkeep_public](../ZlibF/Proof/public-deflate-reset-keep.lean#L19) | — |
| <a id="target-zlibf-spec-public-goal-deflatereset"></a>[deflateReset](../ZlibF/Spec/Public/Lifecycle.lean#L149) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/deflate-stream.md#deflatereset); [输入范围](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateResetProof.deflate_reset_public](../ZlibF/Proof/public-deflate-reset.lean#L52) | — |
| <a id="target-zlibf-spec-public-goal-deflatesetdictionary"></a>[deflateSetDictionary](../ZlibF/Spec/Public/Lifecycle.lean#L175) | 未证明 / 未证明 | [契约](../docs/spec/api/deflate-stream.md#deflatesetdictionary); [输入范围](spec/input-configurations.md#deflate-inputs) | — | [起点：窗口与哈希](progress.md#readiness-deflatesetdictionary) |
| <a id="target-zlibf-spec-public-goal-deflatepending"></a>[deflatePending](../ZlibF/Spec/Public/StreamQueries.lean#L113) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/deflate-stream.md#deflatepending); [输入范围](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateQueryProof.pending_public](../ZlibF/Proof/public-deflate-small-queries.lean#L145) | — |
| <a id="target-zlibf-spec-public-goal-deflateused"></a>[deflateUsed](../ZlibF/Spec/Public/StreamQueries.lean#L124) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/deflate-stream.md#deflateused); [输入范围](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateQueryProof.used_public](../ZlibF/Proof/public-deflate-small-queries.lean#L48) | — |
| <a id="target-zlibf-spec-public-goal-deflatetune"></a>[deflateTune](../ZlibF/Spec/Public/StreamQueries.lean#L132) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/deflate-stream.md#deflatetune); [输入范围](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateQueryProof.tune_public](../ZlibF/Proof/public-deflate-small-queries.lean#L61) | — |
| <a id="target-zlibf-spec-public-goal-deflatesetheader"></a>[deflateSetHeader](../ZlibF/Spec/Public/StreamQueries.lean#L145) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/deflate-stream.md#deflatesetheader); [输入范围](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateQueryProof.header_public](../ZlibF/Proof/public-deflate-small-queries.lean#L74) | — |
| <a id="target-zlibf-spec-public-goal-deflate"></a>[deflate](../ZlibF/Spec/Public/Streams.lean#L56) | 未证明 / 未证明 | [契约](../docs/spec/api/deflate-stream.md#deflate); [输入范围](spec/input-configurations.md#deflate-inputs) | — | [所需：状态分派不变量](progress.md#readiness-inflate) |
| <a id="target-zlibf-spec-public-goal-deflatebound-z"></a>[deflateBound_z](../ZlibF/Spec/Public/Streams.lean#L110) | 未证明 / 未证明 | [契约](../docs/spec/api/deflate-stream.md#deflatebound_z); [输入范围](spec/input-configurations.md#deflate-inputs) | — | [起点：容量上界与头部审查](progress.md#readiness-deflatebound-z) |
| <a id="target-zlibf-spec-public-goal-deflatebound"></a>[deflateBound](../ZlibF/Spec/Public/Streams.lean#L114) | 未证明 / 未证明 | [契约](../docs/spec/api/deflate-stream.md#deflatebound); [输入范围](spec/input-configurations.md#deflate-inputs) | — | [起点：容量上界与头部审查](progress.md#readiness-deflatebound-z) |
| <a id="target-zlibf-spec-public-goal-deflateprime"></a>[deflatePrime](../ZlibF/Spec/Public/Streams.lean#L124) | 未证明 / 未证明 | [契约](../docs/spec/api/deflate-stream.md#deflateprime); [输入范围](spec/input-configurations.md#deflate-inputs) | — | [起点：缓冲区整理与位操作](progress.md#readiness-deflateprime) |
| <a id="target-zlibf-spec-public-goal-deflateparams"></a>[deflateParams](../ZlibF/Spec/Public/Streams.lean#L142) | 未证明 / 未证明 | [契约](../docs/spec/api/deflate-stream.md#deflateparams); [输入范围](spec/input-configurations.md#deflate-inputs) | — | [所需：块刷新与参数状态](progress.md#readiness-deflateparams) |

<a id="group-back"></a>

## 回调解码

| 目标陈述 | 覆盖范围／证据状态 | 契约／输入范围 | 证明证据 | 已审查的后续工作 |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-inflatebackinit"></a>[inflateBackInit_](../ZlibF/Spec/Public/Back.lean#L22) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/inflate-back.md#inflatebackinit_); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.InflateBackInitProof.back_init_public](../ZlibF/Proof/public-infback-init.lean#L135) | — |
| <a id="target-zlibf-spec-public-goal-inflateback"></a>[inflateBack](../ZlibF/Spec/Public/Back.lean#L115) | 未证明 / 未证明 | [契约](../docs/spec/api/inflate-back.md#inflateback); [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：解码表、窗口与回调证明](progress.md#readiness-inflateback) |
| <a id="target-zlibf-spec-public-goal-inflatebackend"></a>[inflateBackEnd](../ZlibF/Spec/Public/Back.lean#L142) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/inflate-back.md#inflatebackend); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.InflateBackEndProof.back_end_public](../ZlibF/Proof/public-infback-end.lean#L20) | — |

<a id="group-gzip"></a>

## gzip 文件

| 目标陈述 | 覆盖范围／证据状态 | 契约／输入范围 | 证明证据 | 已审查的后续工作 |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-gzclose-r"></a>[gzclose_r](../ZlibF/Spec/Public/GzClose.lean#L35) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzclose_r); [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：资源归属](progress.md#readiness-gzclose-r) |
| <a id="target-zlibf-spec-public-goal-gzclose-w"></a>[gzclose_w](../ZlibF/Spec/Public/GzClose.lean#L40) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzclose_w); [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：刷新与清理证明](progress.md#readiness-gzclose-w) |
| <a id="target-zlibf-spec-public-goal-gzclose"></a>[gzclose](../ZlibF/Spec/Public/GzClose.lean#L44) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzclose); [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：刷新与清理证明](progress.md#readiness-gzclose-w) |
| <a id="target-zlibf-spec-public-goal-gzbuffer"></a>[gzbuffer](../ZlibF/Spec/Public/GzControl.lean#L12) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/gz-file.md#gzbuffer); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.gzbuffer_public](../ZlibF/Proof/public-gzbuffer.lean#L49) | — |
| <a id="target-zlibf-spec-public-goal-gzeof"></a>[gzeof](../ZlibF/Spec/Public/GzControl.lean#L22) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/gz-file.md#gzeof); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.gzeof_public](../ZlibF/Proof/public-gzeof.lean#L18) | — |
| <a id="target-zlibf-spec-public-goal-gztell64"></a>[gztell64](../ZlibF/Spec/Public/GzControl.lean#L36) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gztell64); [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：位置约束](progress.md#readiness-gztell64) |
| <a id="target-zlibf-spec-public-goal-gztell"></a>[gztell](../ZlibF/Spec/Public/GzControl.lean#L39) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gztell); [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：位置约束](progress.md#readiness-gztell64) |
| <a id="target-zlibf-spec-public-goal-gzoffset64"></a>[gzoffset64](../ZlibF/Spec/Public/GzControl.lean#L53) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/gz-file.md#gzoffset64); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.OffsetProof.gzoffset64_public_goal](../ZlibF/Proof/public-gz-offset.lean#L199) | — |
| <a id="target-zlibf-spec-public-goal-gzoffset"></a>[gzoffset](../ZlibF/Spec/Public/GzControl.lean#L56) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/gz-file.md#gzoffset); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.OffsetProof.gzoffset_public_goal](../ZlibF/Proof/public-gz-offset.lean#L211) | — |
| <a id="target-zlibf-spec-public-goal-gzerror"></a>[gzerror](../ZlibF/Spec/Public/GzControl.lean#L63) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/gz-file.md#gzerror); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzErrorProof.gzerror](../ZlibF/Proof/public-gz-error.lean#L197) | — |
| <a id="target-zlibf-spec-public-goal-gzclearerr"></a>[gzclearerr](../ZlibF/Spec/Public/GzControl.lean#L74) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/gz-file.md#gzclearerr); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.gzclearerr](../ZlibF/Proof/gzlib.c.public-clearerr.lean#L28) | — |
| <a id="target-zlibf-spec-public-goal-gzrewind"></a>[gzrewind](../ZlibF/Spec/Public/GzControl.lean#L91) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/gz-file.md#gzrewind); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzRewindProof.rewind_public](../ZlibF/Proof/public-gz-rewind.lean#L67) | — |
| <a id="target-zlibf-spec-public-goal-gzseek64"></a>[gzseek64](../ZlibF/Spec/Public/GzControl.lean#L116) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzseek64); [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：定位与状态序列证明](progress.md#readiness-gzseek64) |
| <a id="target-zlibf-spec-public-goal-gzseek"></a>[gzseek](../ZlibF/Spec/Public/GzControl.lean#L119) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzseek); [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：定位与状态序列证明](progress.md#readiness-gzseek64) |
| <a id="target-zlibf-spec-public-goal-gzopen"></a>[gzopen](../ZlibF/Spec/Public/GzOpen.lean#L61) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzopen); [输入范围](spec/input-configurations.md#entry-inputs) | — | [起点：打开与清理](progress.md#readiness-gzopen) |
| <a id="target-zlibf-spec-public-goal-gzopen64"></a>[gzopen64](../ZlibF/Spec/Public/GzOpen.lean#L65) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzopen64); [输入范围](spec/input-configurations.md#entry-inputs) | — | [起点：打开与清理](progress.md#readiness-gzopen) |
| <a id="target-zlibf-spec-public-goal-gzdopen"></a>[gzdopen](../ZlibF/Spec/Public/GzOpen.lean#L70) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzdopen); [输入范围](spec/input-configurations.md#entry-inputs) | — | [起点：打开与清理](progress.md#readiness-gzopen) |
| <a id="target-zlibf-spec-public-goal-gzread"></a>[gzread](../ZlibF/Spec/Public/GzRead.lean#L22) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzread); [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：读取路径证明](progress.md#readiness-gzdirect) |
| <a id="target-zlibf-spec-public-goal-gzfread"></a>[gzfread](../ZlibF/Spec/Public/GzRead.lean#L37) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzfread); [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：读取路径证明](progress.md#readiness-gzdirect) |
| <a id="target-zlibf-spec-public-goal-gzgetc"></a>[gzgetc](../ZlibF/Spec/Public/GzRead.lean#L58) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzgetc); [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：读取路径证明](progress.md#readiness-gzdirect) |
| <a id="target-zlibf-spec-public-goal-gzgetc"></a>[gzgetc_](../ZlibF/Spec/Public/GzRead.lean#L61) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzgetc_); [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：读取路径证明](progress.md#readiness-gzdirect) |
| <a id="target-zlibf-spec-public-goal-gzungetc"></a>[gzungetc](../ZlibF/Spec/Public/GzRead.lean#L66) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzungetc); [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：读取路径证明](progress.md#readiness-gzdirect) |
| <a id="target-zlibf-spec-public-goal-gzgets"></a>[gzgets](../ZlibF/Spec/Public/GzRead.lean#L80) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzgets); [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：读取路径证明](progress.md#readiness-gzdirect) |
| <a id="target-zlibf-spec-public-goal-gzdirect"></a>[gzdirect](../ZlibF/Spec/Public/GzRead.lean#L103) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzdirect); [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：读取路径证明](progress.md#readiness-gzdirect) |
| <a id="target-zlibf-spec-public-goal-gzwrite"></a>[gzwrite](../ZlibF/Spec/Public/GzWrite.lean#L28) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzwrite); [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：写入路径证明](progress.md#readiness-gzwrite) |
| <a id="target-zlibf-spec-public-goal-gzfwrite"></a>[gzfwrite](../ZlibF/Spec/Public/GzWrite.lean#L43) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzfwrite); [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：写入路径证明](progress.md#readiness-gzwrite) |
| <a id="target-zlibf-spec-public-goal-gzputc"></a>[gzputc](../ZlibF/Spec/Public/GzWrite.lean#L59) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzputc); [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：写入路径证明](progress.md#readiness-gzwrite) |
| <a id="target-zlibf-spec-public-goal-gzputs"></a>[gzputs](../ZlibF/Spec/Public/GzWrite.lean#L71) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzputs); [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：写入路径证明](progress.md#readiness-gzwrite) |
| <a id="target-zlibf-spec-public-goal-gzvprintf"></a>[gzvprintf](../ZlibF/Spec/Public/GzWrite.lean#L102) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzvprintf); [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：写入路径证明](progress.md#readiness-gzwrite) |
| <a id="target-zlibf-spec-public-goal-gzprintf"></a>[gzprintf](../ZlibF/Spec/Public/GzWrite.lean#L106) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzprintf); [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：写入路径证明](progress.md#readiness-gzwrite) |
| <a id="target-zlibf-spec-public-goal-gzflush"></a>[gzflush](../ZlibF/Spec/Public/GzWrite.lean#L111) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzflush); [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：写入路径证明](progress.md#readiness-gzwrite) |
| <a id="target-zlibf-spec-public-goal-gzsetparams"></a>[gzsetparams](../ZlibF/Spec/Public/GzWrite.lean#L128) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzsetparams); [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：写入路径证明](progress.md#readiness-gzwrite) |

<a id="group-buffers"></a>

## 完整缓冲区操作

| 目标陈述 | 覆盖范围／证据状态 | 契约／输入范围 | 证明证据 | 已审查的后续工作 |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-compress2-z"></a>[compress2_z](../ZlibF/Spec/Public/Utilities.lean#L40) | 未证明 / 未证明 | [契约](../docs/spec/api/utility.md#compress2_z); [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：压缩器执行证明](progress.md#readiness-compress2-z) |
| <a id="target-zlibf-spec-public-goal-compress2"></a>[compress2](../ZlibF/Spec/Public/Utilities.lean#L45) | 未证明 / 未证明 | [契约](../docs/spec/api/utility.md#compress2); [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：压缩器执行证明](progress.md#readiness-compress2-z) |
| <a id="target-zlibf-spec-public-goal-compress-z"></a>[compress_z](../ZlibF/Spec/Public/Utilities.lean#L52) | 未证明 / 未证明 | [契约](../docs/spec/api/utility.md#compress_z); [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：压缩器执行证明](progress.md#readiness-compress2-z) |
| <a id="target-zlibf-spec-public-goal-compress"></a>[compress](../ZlibF/Spec/Public/Utilities.lean#L57) | 未证明 / 未证明 | [契约](../docs/spec/api/utility.md#compress); [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：压缩器执行证明](progress.md#readiness-compress2-z) |
| <a id="target-zlibf-spec-public-goal-uncompress2-z"></a>[uncompress2_z](../ZlibF/Spec/Public/Utilities.lean#L103) | 未证明 / 未证明 | [契约](../docs/spec/api/utility.md#uncompress2_z); [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：解码器执行证明](progress.md#readiness-uncompress2-z) |
| <a id="target-zlibf-spec-public-goal-uncompress2"></a>[uncompress2](../ZlibF/Spec/Public/Utilities.lean#L107) | 未证明 / 未证明 | [契约](../docs/spec/api/utility.md#uncompress2); [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：解码器执行证明](progress.md#readiness-uncompress2-z) |
| <a id="target-zlibf-spec-public-goal-uncompress-z"></a>[uncompress_z](../ZlibF/Spec/Public/Utilities.lean#L132) | 未证明 / 未证明 | [契约](../docs/spec/api/utility.md#uncompress_z); [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：解码器执行证明](progress.md#readiness-uncompress2-z) |
| <a id="target-zlibf-spec-public-goal-uncompress"></a>[uncompress](../ZlibF/Spec/Public/Utilities.lean#L136) | 未证明 / 未证明 | [契约](../docs/spec/api/utility.md#uncompress); [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：解码器执行证明](progress.md#readiness-uncompress2-z) |

<a id="group-models"></a>

## 格式与 API 模型

| 目标陈述 | 覆盖范围／证据状态 | 契约／输入范围 | 证明证据 | 已审查的后续工作 |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-api-goal-format-deterministic"></a>[format_deterministic](../ZlibF/Spec/Api/Goals.lean#L42) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.format_deterministic](../ZlibF/Proof/Format/Api.lean#L51) | — |
| <a id="target-zlibf-spec-api-goal-format-prefix-free"></a>[format_prefix_free](../ZlibF/Spec/Api/Goals.lean#L47) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.format_prefix_free](../ZlibF/Proof/Format/Api.lean#L56) | — |
| <a id="target-zlibf-spec-api-goal-inflate-decodes"></a>[inflate_decodes](../ZlibF/Spec/Api/Goals.lean#L58) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.inflate_decodes](../ZlibF/Proof/Api/Inflate.lean#L346) | — |
| <a id="target-zlibf-spec-api-goal-inflate-completes"></a>[inflate_completes](../ZlibF/Spec/Api/Goals.lean#L69) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.inflate_completes](../ZlibF/Proof/Api/Inflate.lean#L353) | — |
| <a id="target-zlibf-spec-api-goal-inflate-rejects-invalid"></a>[inflate_rejects_invalid](../ZlibF/Spec/Api/Goals.lean#L84) | 未证明 / 未证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | — | 前置义务尚未审查 |
| <a id="target-zlibf-spec-api-goal-deflate-valid"></a>[deflate_valid](../ZlibF/Spec/Api/Goals.lean#L99) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.deflate_valid](../ZlibF/Proof/Api/Deflate.lean#L181) | — |
| <a id="target-zlibf-spec-api-goal-deflate-completes"></a>[deflate_completes](../ZlibF/Spec/Api/Goals.lean#L106) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.deflate_completes](../ZlibF/Proof/Api/DeflateBounds.lean#L164) | — |
| <a id="target-zlibf-spec-api-goal-deflate-full-flush-resync"></a>[deflate_full_flush_resync](../ZlibF/Spec/Api/Goals.lean#L116) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.deflate_full_flush_resync](../ZlibF/Proof/Api/DeflateFlush.lean#L169) | — |
| <a id="target-zlibf-spec-api-goal-roundtrip"></a>[roundtrip](../ZlibF/Spec/Api/Goals.lean#L134) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.roundtrip](../ZlibF/Proof/Api/GzipRoundtrip.lean#L177) | — |
| <a id="target-zlibf-spec-api-goal-roundtrip-completes"></a>[roundtrip_completes](../ZlibF/Spec/Api/Goals.lean#L143) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.roundtrip_completes](../ZlibF/Proof/Api/GzipRoundtrip.lean#L186) | — |
| <a id="target-zlibf-spec-api-goal-dict-roundtrip"></a>[dict_roundtrip](../ZlibF/Spec/Api/Goals.lean#L162) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.dict_roundtrip](../ZlibF/Proof/Api/DictionaryRoundtrip.lean#L121) | — |
| <a id="target-zlibf-spec-api-goal-header-roundtrip"></a>[header_roundtrip](../ZlibF/Spec/Api/Goals.lean#L180) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.header_roundtrip](../ZlibF/Proof/Api/HeaderRoundtrip.lean#L89) | — |
| <a id="target-zlibf-spec-api-goal-deflate-bound-adequate"></a>[deflate_bound_adequate](../ZlibF/Spec/Api/Goals.lean#L189) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.deflate_bound_adequate](../ZlibF/Proof/Api/DeflateBounds.lean#L103) | — |
| <a id="target-zlibf-spec-api-goal-compress-bound-adequate"></a>[compress_bound_adequate](../ZlibF/Spec/Api/Goals.lean#L196) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.compress_bound_adequate](../ZlibF/Proof/Api/Compress.lean#L8) | — |
| <a id="target-zlibf-spec-api-goal-compress-roundtrip"></a>[compress_roundtrip](../ZlibF/Spec/Api/Goals.lean#L203) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.compress_roundtrip](../ZlibF/Proof/Api/CompressRoundtrip.lean#L32) | — |
| <a id="target-zlibf-spec-api-goal-gz-roundtrip"></a>[gz_roundtrip](../ZlibF/Spec/Api/Goals.lean#L214) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.gz_roundtrip](../ZlibF/Proof/Api/GzRoundtrip.lean#L15) | — |
| <a id="target-zlibf-spec-api-goal-gz-seek-read"></a>[gz_seek_read](../ZlibF/Spec/Api/Goals.lean#L221) | 未证明 / 存在阻碍 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | — [阻碍：gzip 定位模式](progress.md#gzip-seek-mode) | — |
| <a id="target-zlibf-spec-api-goal-compress-bound-value"></a>[compress_bound_value](../ZlibF/Spec/Api/Concrete.lean#L57) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.compress_bound_value](../ZlibF/Proof/Api/Concrete.lean#L57) | — |
| <a id="target-zlibf-spec-api-goal-compress2-z-first-alloc-failure"></a>[compress2_z_first_alloc_failure](../ZlibF/Spec/Api/Concrete.lean#L67) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.compress2_z_first_alloc_failure](../ZlibF/Proof/Api/CompressFailure.lean#L29) | — |
| <a id="target-zlibf-spec-api-goal-inflate-deferred-distance"></a>[inflate_deferred_distance](../ZlibF/Spec/Api/Inflate.lean#L267) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.inflate_deferred_distance](../ZlibF/Proof/Api/InflateCausality.lean#L244) | — |

<a id="group-lifecycle"></a>

## 生命周期与调用序列

| 目标陈述 | 覆盖范围／证据状态 | 契约／输入范围 | 证明证据 | 已审查的后续工作 |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-inflate-sequence"></a>[inflate_sequence](../ZlibF/Spec/Public/Sequences.lean#L160) | 未证明 / 未证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#inflate-inputs) | — | [所需：执行与格式证明](progress.md#readiness-inflate-sequence) |
| <a id="target-zlibf-spec-public-goal-deflate-sequence"></a>[deflate_sequence](../ZlibF/Spec/Public/Sequences.lean#L174) | 未证明 / 未证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#deflate-inputs) | — | [所需：执行与格式证明](progress.md#readiness-inflate-sequence) |
| <a id="target-zlibf-spec-public-goal-inflate-back-sequence"></a>[inflate_back_sequence](../ZlibF/Spec/Public/Sequences.lean#L201) | 未证明 / 未证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：执行与格式证明](progress.md#readiness-inflate-sequence) |
| <a id="target-zlibf-spec-public-goal-gz-sequence"></a>[gz_sequence](../ZlibF/Spec/Public/Sequences.lean#L213) | 未证明 / 未证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：执行与格式证明](progress.md#readiness-inflate-sequence) |
| <a id="target-zlibf-spec-public-goal-inflate-initialisation-domain"></a>[inflate_initialisation_domain](../ZlibF/Spec/Public/Domains.lean#L24) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.InflateInit.inflate_initialisation_domain_public](../ZlibF/Proof/public-inflate-init.lean#L263) | — |
| <a id="target-zlibf-spec-public-goal-deflate-initialisation-domain"></a>[deflate_initialisation_domain](../ZlibF/Spec/Public/Domains.lean#L37) | 未证明 / 未证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | — | [起点：初始化与分配](progress.md#readiness-deflateinit2) |
| <a id="target-zlibf-spec-public-goal-inflate-back-initialisation-domain"></a>[inflate_back_initialisation_domain](../ZlibF/Spec/Public/Domains.lean#L53) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.InflateBackInitProof.back_init_domain_public](../ZlibF/Proof/public-infback-init.lean#L230) | — |
| <a id="target-zlibf-spec-public-goal-gz-initialisation-domain"></a>[gz_initialisation_domain](../ZlibF/Spec/Public/Domains.lean#L77) | 未证明 / 未证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | — | [起点：打开与清理](progress.md#readiness-gzopen) |

<a id="group-internal"></a>

## 内部证明义务

| 目标陈述 | 覆盖范围／证据状态 | 契约／输入范围 | 证明证据 | 已审查的后续工作 |
| --- | --- | --- | --- | --- |
| <a id="target-zlib-crc32-spec-byteviews-goal-crc32-z-all-byte-views"></a>[crc32_z_all_byte_views](../ZlibF/Spec/Crc32ByteViews.lean#L17) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Crc32.Proofs.crc32_z_all_byte_views](../ZlibF/Proof/crc32.c.views.lean#L567) | — |
| <a id="target-zlib-crc32-spec-byteviews-goal-crc32-all-byte-views"></a>[crc32_all_byte_views](../ZlibF/Spec/Crc32ByteViews.lean#L28) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Crc32.Proofs.crc32_all_byte_views](../ZlibF/Proof/crc32.c.views.lean#L573) | — |
| <a id="target-zlibf-spec-token-goal-rejected-has-no-symbols"></a>[rejected_has_no_symbols](../ZlibF/Spec/Format/Token.lean#L84) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Token.rejected_has_no_symbols](../ZlibF/Proof/Format/Token.lean#L49) | — |
| <a id="target-zlibf-spec-token-goal-step-composes-symbols"></a>[step_composes_symbols](../ZlibF/Spec/Format/Token.lean#L62) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Token.step_composes_symbols](../ZlibF/Proof/Format/Token.lean#L15) | — |
| <a id="target-zlibf-spec-token-goal-symbols-exposes-step"></a>[symbols_exposes_step](../ZlibF/Spec/Format/Token.lean#L73) | 陈述所允许的全部输入 / 本地已检查 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Token.symbols_exposes_step](../ZlibF/Proof/Format/Token.lean#L35) | — |

## 已观察到的证明依赖

左列是被复用的来源目标，右列是使用它的目标。右列目标的定理实际使用了左列目标的证明。

| 来源 | 目标 |
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

## C 函数调用

右列目标对应的实现调用左列入口。这种调用关系不意味着，证明时必须把左列入口的完整契约作为前提。

| 来源 | 目标 |
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

## 规格中的引用

右列目标的定义引用左列目标或实现。这里记录的是定义中的引用，不是证明依赖。

| 来源 | 目标 |
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

## 辅助证明的引用关系

这里把已观察到的定理引用按来源类别分组。一个分组不表示对应文件已经整体证明。
本表保留分组之间的全部直接连接，包括总览图为简化显示而省去的箭头。

| 辅助证明来源 | 直接引用它的目标 |
| --- | --- |
| API 模型引理 | compress_bound_adequate, compress_roundtrip, deflate_bound_adequate, deflate_completes, deflate_full_flush_resync, deflate_valid, dict_roundtrip, gz_roundtrip, header_roundtrip, inflate_completes, inflate_decodes, inflate_deferred_distance, roundtrip, roundtrip_completes, deflateInit_, API 模型证明, deflate 状态构造证明 |
| ByteAddress 字节地址模型证明 | first_aligned_offset, mask_refines_base_plus_offset, pointer_advance_preserves_low_bits |
| actual_body_preserves_origin | inffast.c 的证明 |
| actual_distance_block_preserves_origin | inffast.c 的证明 |
| step_safe | inffast.c 的证明 |
| actual_copy_match_refines_lz77 | inffast.c 的证明 |
| actual_drop_preserves_origin | inffast.c 的证明 |
| actual_rollback_preserves_origin | inffast.c 的证明 |
| drop_preserves_origin | inffast.c 的证明 |
| pull_preserves_origin | inffast.c 的证明 |
| inflate_table_content | inftrees.c 的证明 |
| retained_history_agrees | 格式证明 |
| deflate_valid | API 模型证明 |
| inflate_completes | API 模型证明 |
| inflate_decodes | API 模型证明 |
| inflateBackInit_ | 公开入口组合证明 |
| adler32.c 的证明 | inflateSetDictionary, inflate 入口组合证明, inflate 存储与读位证明, 公开入口组合证明 |
| API 模型证明 | output_copy_refines_lz77, retained_history_agrees, compress2_z_first_alloc_failure, compress_bound_adequate, compress_bound_value, compress_roundtrip, deflate_bound_adequate, deflate_completes, deflate_full_flush_resync, deflate_valid, dict_roundtrip, gz_roundtrip, header_roundtrip, inflate_completes, inflate_decodes, inflate_deferred_distance, roundtrip, roundtrip_completes, inflateCodesUsed, 不涉及堆的数学证明 |
| crc32.c 的证明 | crc32_all_byte_views, crc32_z_all_byte_views, crc32, crc32_z, 公开入口组合证明 |
| deflate 状态构造证明 | deflateInit_ |
| deflate 入口组合证明 | deflateEnd, deflateGetDictionary, deflatePending, deflateReset, deflateResetKeep, deflateSetHeader, deflateTune, deflateUsed |
| deflate 生命周期证明 | deflateEnd, deflateGetDictionary, deflateInit_, deflatePending, deflateReset, deflateResetKeep, deflateSetHeader, deflateTune, deflateUsed, deflate 状态构造证明, deflate 入口组合证明 |
| deflate 窗口与匹配证明 | deflate 生命周期证明, inflate 存储与读位证明 |
| 格式证明 | short_decode_table_leaf_sound, short_rejected_leaf_stays_invalid, compress_roundtrip, format_deterministic, format_prefix_free, header_roundtrip, inflate_completes, rejected_has_no_symbols, API 模型证明, 不涉及堆的数学证明, inffast.c 的证明, inftrees.c 的证明 |
| gzlib.c 的证明 | gzclearerr, 公开入口组合证明 |
| 不涉及堆的数学证明 | match_array_refines_lz77, output_copy_refines_lz77, window_copy_refines_lz77, copy_back_compose, retained_history_agrees, window_distance_check_agrees, API 模型证明, inftrees.c 的证明 |
| infback.c 的证明 | inflateBackEnd, inflateBackInit_, 公开入口组合证明 |
| inffast.c 的证明 | actual_body_preserves_origin, actual_body_refines_token, actual_fast_preserves_origin, actual_distance_block_preserves_origin, actual_distance_refines_lz77, distance_lookup_matches_format, fast_safe, step_safe, length_lookup_matches_format, actual_body_retains_selected_length, actual_copy_match_refines_lz77, match_array_refines_lz77, actual_drop_preserves_origin, actual_pull_preserves_origin, actual_rollback_preserves_origin, drop_preserves_origin, initial_origin, pull_preserves_origin, rollback_preserves_origin, output_copy_refines_lz77, 不涉及堆的数学证明, inftrees.c 的证明 |
| inffixed.h.fast-flags 的证明 | fixed_tables_have_fast_leaf_flags |
| inflate 入口组合证明 | inflateEnd, inflateGetDictionary, inflateGetHeader, inflateInit_, inflateMark, inflatePrime, inflateReset, inflateReset2, inflateSetDictionary, inflateSyncPoint, inflateUndermine, inflateValidate, inflate_initialisation_domain |
| inflate 存储与读位证明 | deflateReset, deflateResetKeep, inflateBackEnd, inflateBackInit_, inflateEnd, inflateGetDictionary, inflateInit_, inflateMark, inflateReset, inflateReset2, inflateResetKeep, inflateSetDictionary, inflateSyncPoint, inflateUndermine, inflateValidate, API 模型证明, infback.c 的证明, inflate 入口组合证明, 公开入口组合证明 |
| inftrees.c 的证明 | decode_table_matches_format, short_decode_table_leaf_sound, decode_table_leaf_sound, decode_table_read_preserved, constructor_establishes_decode_table_invariant, decode_table_invariant_of_prefix, constructor_establishes_query_stability, short_rejected_leaf_stays_invalid, constructor_establishes_fast_leaf_flags, leaf_classification_agrees, inflate_table_content, inflate_table_decoder_safe, inflate_table_read_extent, constructor_root_bits, constructor_subtable_bits, 不涉及堆的数学证明 |
| 公开入口组合证明 | adler32_combine, adler32_combine64, adler32_z, compressBound, compressBound_z, crc32_combine, crc32_combine64, crc32_combine_gen, crc32_combine_gen64, crc32_combine_op, get_crc_table, gzbuffer, gzeof, gzerror, gzoffset, gzoffset64, gzrewind, inflateBackEnd, inflateBackInit_, inflate_back_initialisation_domain, zError, zlibVersion, adler32.c 的证明 |
| 运行时对象与算术引理 | byte_modifies_preserve_bases, byte_stores_preserve_bases, every_layout_is_representable, crc32_all_byte_views, crc32_z_all_byte_views, actual_body_preserves_origin, actual_body_refines_token, actual_fast_preserves_origin, actual_distance_block_preserves_origin, actual_distance_refines_lz77, fast_safe, step_safe, actual_body_retains_selected_length, actual_copy_match_refines_lz77, actual_pull_preserves_origin, actual_rollback_preserves_origin, decode_table_classifies_input, decode_table_matches_format, short_decode_table_leaf_sound, decode_table_leaf_sound, constructor_establishes_decode_table_invariant, constructor_establishes_query_stability, constructor_establishes_fast_leaf_flags, inflate_table_content, inflate_table_decoder_safe, inflate_table_read_extent, constructor_root_bits, constructor_subtable_bits, compress2_z_first_alloc_failure, adler32, adler32_z, crc32, crc32_z, deflateEnd, deflateGetDictionary, deflateInit_, deflatePending, deflateReset, deflateResetKeep, deflateSetHeader, deflateTune, deflateUsed, get_crc_table, gzclearerr, gzerror, gzoffset, gzoffset64, gzrewind, inflateBackEnd, inflateBackInit_, inflateCodesUsed, inflateEnd, inflateGetDictionary, inflateGetHeader, inflateInit_, inflateMark, inflatePrime, inflateReset, inflateReset2, inflateResetKeep, inflateSetDictionary, inflateSyncPoint, inflateUndermine, inflateValidate, inflate_back_initialisation_domain, inflate_initialisation_domain, zError, zlibVersion, adler32.c 的证明, API 模型证明, crc32.c 的证明, deflate 状态构造证明, deflate 入口组合证明, deflate 生命周期证明, deflate 窗口与匹配证明, gzlib.c 的证明, infback.c 的证明, inffast.c 的证明, inflate 入口组合证明, inflate 存储与读位证明, inftrees.c 的证明, 公开入口组合证明, 编码树构造与输出证明, zutil.c 的证明 |
| 规格引理 | every_existing_heap_accepts_layout, actual_body_refines_token, distance_lookup_matches_format, length_lookup_matches_format, actual_body_retains_selected_length, drop_preserves_origin, pull_preserves_origin, rollback_preserves_origin, decode_table_invariant_of_prefix, short_rejected_leaf_stays_invalid, inffast.c 的证明 |
| 编码树构造与输出证明 | deflate 状态构造证明, deflate 生命周期证明 |
| zutil.c 的证明 | inflate_table_content, deflate 状态构造证明, deflate 生命周期证明, inflate 入口组合证明, inflate 存储与读位证明, inftrees.c 的证明 |

## 其他已登记定理

这些声明是已经登记的辅助执行结果、引理或见证。
它们不是额外的固定目标，也不能单凭这些声明就为调用者标记某种输入覆盖状态。

| 声明 | 使用该声明的固定目标证明 |
| --- | --- |
| [Zlib.Adler32.Proofs.adler32_combine64_safe](../ZlibF/Proof/adler32.c.lean#L977) | 未记录到固定目标的组合关系 |
| [Zlib.Adler32.Proofs.adler32_combine_c_safe](../ZlibF/Proof/adler32.c.lean#L982) | [adler32_combine](#target-zlibf-spec-public-goal-adler32-combine), [adler32_combine64](#target-zlibf-spec-public-goal-adler32-combine64) |
| [Zlib.Adler32.Proofs.adler32_combine_correct](../ZlibF/Proof/adler32.c.lean#L953) | 未记录到固定目标的组合关系 |
| [Zlib.Adler32.Proofs.adler32_combine_safe](../ZlibF/Proof/adler32.c.lean#L941) | [adler32_combine](#target-zlibf-spec-public-goal-adler32-combine), [adler32_combine64](#target-zlibf-spec-public-goal-adler32-combine64) |
| [Zlib.Adler32.Proofs.adler32_safe](../ZlibF/Proof/adler32.c.lean#L987) | 未记录到固定目标的组合关系 |
| [Zlib.Adler32.Proofs.adler32_z_correct](../ZlibF/Proof/adler32.c.lean#L786) | 未记录到固定目标的组合关系 |
| [Zlib.Adler32.Proofs.adler32_z_correct_ne_one](../ZlibF/Proof/adler32.c.lean#L798) | 未记录到固定目标的组合关系 |
| [Zlib.Adler32.Proofs.adler32_z_safe](../ZlibF/Proof/adler32.c.lean#L809) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.addrOf_safe](../ZlibF/Proof/crc32.c.lean#L2470) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.blockLittle_safe](../ZlibF/Proof/crc32.c.lean#L2464) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.braidTab_safe](../ZlibF/Proof/crc32.c.lean#L2460) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.crc32_combine64_correct](../ZlibF/Proof/crc32.c.lean#L2383) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.crc32_combine64_safe](../ZlibF/Proof/crc32.c.lean#L2377) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.crc32_combine_correct](../ZlibF/Proof/crc32.c.lean#L2398) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.crc32_combine_gen64_correct](../ZlibF/Proof/crc32.c.lean#L2334) | [crc32_combine_gen](#target-zlibf-spec-public-goal-crc32-combine-gen), [crc32_combine_gen64](#target-zlibf-spec-public-goal-crc32-combine-gen64), [crc32_combine_op](#target-zlibf-spec-public-goal-crc32-combine-op) |
| [Zlib.Crc32.Proofs.crc32_combine_gen64_safe](../ZlibF/Proof/crc32.c.lean#L2324) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.crc32_combine_gen_correct](../ZlibF/Proof/crc32.c.lean#L2353) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.crc32_combine_gen_safe](../ZlibF/Proof/crc32.c.lean#L2347) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.crc32_combine_op_correct](../ZlibF/Proof/crc32.c.lean#L2406) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.crc32_combine_op_diverges](../ZlibF/Proof/crc32.c.lean#L2371) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.crc32_combine_op_safe](../ZlibF/Proof/crc32.c.lean#L2362) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.crc32_combine_safe](../ZlibF/Proof/crc32.c.lean#L2393) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.crc32_correct](../ZlibF/Proof/crc32.c.lean#L2227) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.crc32_null](../ZlibF/Proof/crc32.c.lean#L2223) | [crc32](#target-zlibf-spec-public-goal-crc32) |
| [Zlib.Crc32.Proofs.crc32_safe](../ZlibF/Proof/crc32.c.lean#L2236) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.crc32_z_correct](../ZlibF/Proof/crc32.c.lean#L2203) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.crc32_z_null](../ZlibF/Proof/crc32.c.lean#L2190) | [crc32](#target-zlibf-spec-public-goal-crc32), [crc32_z](#target-zlibf-spec-public-goal-crc32-z) |
| [Zlib.Crc32.Proofs.crc32_z_safe](../ZlibF/Proof/crc32.c.lean#L2217) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.crcByte_safe](../ZlibF/Proof/crc32.c.lean#L2448) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.crcTab_safe](../ZlibF/Proof/crc32.c.lean#L2439) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.crc_word_big_safe](../ZlibF/Proof/crc32.c.lean#L2488) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.crc_word_correct](../ZlibF/Proof/crc32.c.lean#L2422) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.crc_word_safe](../ZlibF/Proof/crc32.c.lean#L2417) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.get_crc_table_correct](../ZlibF/Proof/crc32.c.lean#L2249) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.get_crc_table_safe](../ZlibF/Proof/crc32.c.lean#L2244) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.loadWord_safe](../ZlibF/Proof/crc32.c.lean#L2434) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.multmodp_correct](../ZlibF/Proof/crc32.c.lean#L2283) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.multmodp_diverges](../ZlibF/Proof/crc32.c.lean#L986) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.multmodp_safe](../ZlibF/Proof/crc32.c.lean#L2276) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.shr64_safe](../ZlibF/Proof/crc32.c.lean#L2474) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.wordAt_safe](../ZlibF/Proof/crc32.c.lean#L2455) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.x2nTab_safe](../ZlibF/Proof/crc32.c.lean#L2443) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.x2nmodp_correct](../ZlibF/Proof/crc32.c.lean#L2307) | 未记录到固定目标的组合关系 |
| [Zlib.Crc32.Proofs.x2nmodp_safe](../ZlibF/Proof/crc32.c.lean#L2299) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.INSERT_STRING_ok](../ZlibF/Proof/deflate.c.engine.macros.lean#L177) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.UPDATE_HASH_ok](../ZlibF/Proof/deflate.c.engine.macros.lean#L147) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.chain_ok_of_chains](../ZlibF/Proof/deflate.c.engine.chains.lean#L194) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.chains_insert](../ZlibF/Proof/deflate.c.engine.chains.lean#L76) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.chains_slide](../ZlibF/Proof/deflate.c.engine.chains.lean#L138) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.default_init_all_scalar_full_request_contract](../ZlibF/Proof/deflate.c.engine.all-scalar-full-contract.lean#L14) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.default_public_full_contract_witness](../ZlibF/Proof/deflate.c.engine.full-contract-witness.lean#L15) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.fill_fit](../ZlibF/Proof/deflate.c.engine.window.lean#L45) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.fill_post_room](../ZlibF/Proof/deflate.c.engine.window.lean#L40) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.form_init](../ZlibF/Proof/deflate.c.engine.hash.lean#L126) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.hkey_third](../ZlibF/Proof/deflate.c.engine.hash.lean#L139) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.lm_body_ok](../ZlibF/Proof/deflate.c.engine.lmbody.lean#L102) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.lm_inner_loop](../ZlibF/Proof/deflate.c.engine.lminner.lean#L36) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.lm_loop_ok](../ZlibF/Proof/deflate.c.engine.lmmain.lean#L77) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.longest_match_ok](../ZlibF/Proof/deflate.c.engine.lmmain.lean#L212) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.matchLen_agree](../ZlibF/Proof/deflate.c.engine.match.lean#L100) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.putShortMSB_ok](../ZlibF/Proof/deflate.c.engine.macros.lean#L119) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.put_byte_ok](../ZlibF/Proof/deflate.c.engine.macros.lean#L96) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.read_buf_ok](../ZlibF/Proof/deflate.c.engine.readbuf.lean#L99) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.read_buf_zero](../ZlibF/Proof/deflate.c.engine.readbuf.lean#L75) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.slide_copy](../ZlibF/Proof/deflate.c.engine.window.lean#L52) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.slide_hash_ok](../ZlibF/Proof/deflate.c.engine.slide.lean#L166) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.upd3_indep](../ZlibF/Proof/deflate.c.engine.hash.lean#L45) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Proofs.deflateBound_nostate](../ZlibF/Proof/deflate.c.life.bound.lean#L330) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Proofs.deflateBound_safe](../ZlibF/Proof/deflate.c.life.bound.lean#L319) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Proofs.deflateBound_z_nostate](../ZlibF/Proof/deflate.c.life.bound.lean#L312) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Proofs.deflateBound_z_safe](../ZlibF/Proof/deflate.c.life.bound.lean#L302) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Proofs.deflateEnd_reject](../ZlibF/Proof/deflate.c.life.end.lean#L321) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Proofs.deflateEnd_safe](../ZlibF/Proof/deflate.c.life.end.lean#L270) | [deflateEnd](#target-zlibf-spec-public-goal-deflateend) |
| [Zlib.Deflate.Proofs.deflatePending_reject](../ZlibF/Proof/deflate.c.life.check.lean#L173) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Proofs.deflatePending_safe](../ZlibF/Proof/deflate.c.life.check.lean#L146) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Proofs.deflatePrime_invalid_count](../ZlibF/Proof/deflate.c.prime.lean#L24) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Proofs.deflatePrime_refused](../ZlibF/Proof/deflate.c.prime.lean#L15) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Proofs.deflateResetKeep_reject](../ZlibF/Proof/deflate.c.life.reset.lean#L424) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Proofs.deflateResetKeep_safe](../ZlibF/Proof/deflate.c.life.reset.lean#L367) | [deflateReset](#target-zlibf-spec-public-goal-deflatereset), [deflateResetKeep](#target-zlibf-spec-public-goal-deflateresetkeep) |
| [Zlib.Deflate.Proofs.deflateReset_reject](../ZlibF/Proof/deflate.c.life.reset.lean#L430) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Proofs.deflateReset_safe](../ZlibF/Proof/deflate.c.life.reset.lean#L401) | [deflateReset](#target-zlibf-spec-public-goal-deflatereset) |
| [Zlib.Deflate.Proofs.deflateSetHeader_not_gzip](../ZlibF/Proof/deflate.c.life.check.lean#L92) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Proofs.deflateSetHeader_reject](../ZlibF/Proof/deflate.c.life.check.lean#L98) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Proofs.deflateSetHeader_safe](../ZlibF/Proof/deflate.c.life.check.lean#L83) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Proofs.deflateStateCheck_total](../ZlibF/Proof/deflate.c.base.lean#L731) | [deflatePending](#target-zlibf-spec-public-goal-deflatepending), [deflateSetHeader](#target-zlibf-spec-public-goal-deflatesetheader), [deflateTune](#target-zlibf-spec-public-goal-deflatetune), [deflateUsed](#target-zlibf-spec-public-goal-deflateused) |
| [Zlib.Deflate.Proofs.deflateTune_reject](../ZlibF/Proof/deflate.c.life.check.lean#L54) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Proofs.deflateTune_safe](../ZlibF/Proof/deflate.c.life.check.lean#L44) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Proofs.deflateUsed_reject](../ZlibF/Proof/deflate.c.life.check.lean#L119) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Proofs.deflateUsed_safe](../ZlibF/Proof/deflate.c.life.check.lean#L113) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Proofs.lm_init_safe](../ZlibF/Proof/deflate.c.life.reset.lean#L151) | [deflateReset](#target-zlibf-spec-public-goal-deflatereset) |
| [Zlib.Gzclose.Proofs.gzclose_dispatch](../ZlibF/Proof/gzclose.c.lean#L22) | 未记录到固定目标的组合关系 |
| [Zlib.Gzclose.Proofs.gzclose_null](../ZlibF/Proof/gzclose.c.lean#L17) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.GT_OFF_run](../ZlibF/Proof/gzlib.c.simple.lean#L46) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gz_error_null_run](../ZlibF/Proof/gzlib.c.error.lean#L134) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gz_intmax_run](../ZlibF/Proof/gzlib.c.simple.lean#L43) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gz_open_alloc_failure](../ZlibF/Proof/gzlib.c.open.lean#L35) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gz_open_null](../ZlibF/Proof/gzlib.c.open.lean#L17) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gz_reset_run](../ZlibF/Proof/gzlib.c.error.lean#L145) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gz_reset_safe](../ZlibF/Proof/gzlib.c.error.lean#L168) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzbuffer_null](../ZlibF/Proof/gzlib.c.simple.lean#L52) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzbuffer_run](../ZlibF/Proof/gzlib.c.simple.lean#L67) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzbuffer_safe](../ZlibF/Proof/gzlib.c.simple.lean#L84) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzclearerr_null](../ZlibF/Proof/gzlib.c.simple.lean#L191) | [gzclearerr](#target-zlibf-spec-public-goal-gzclearerr) |
| [Zlib.Gzlib.Proofs.gzclearerr_run](../ZlibF/Proof/gzlib.c.simple.lean#L199) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzclearerr_safe](../ZlibF/Proof/gzlib.c.simple.lean#L210) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzdopen_alloc_failure](../ZlibF/Proof/gzlib.c.open.lean#L61) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzdopen_negative](../ZlibF/Proof/gzlib.c.open.lean#L54) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzeof_null](../ZlibF/Proof/gzlib.c.simple.lean#L108) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzeof_run](../ZlibF/Proof/gzlib.c.simple.lean#L111) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzerror_null_file](../ZlibF/Proof/gzlib.c.simple.lean#L159) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzerror_run](../ZlibF/Proof/gzlib.c.simple.lean#L163) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzoffset64_null](../ZlibF/Proof/gzlib.c.rewind.lean#L110) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzoffset64_run](../ZlibF/Proof/gzlib.c.rewind.lean#L114) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzoffset_eq](../ZlibF/Proof/gzlib.c.rewind.lean#L136) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzopen64_alloc_failure](../ZlibF/Proof/gzlib.c.open.lean#L48) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzopen64_null](../ZlibF/Proof/gzlib.c.open.lean#L29) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzopen_alloc_failure](../ZlibF/Proof/gzlib.c.open.lean#L42) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzopen_null](../ZlibF/Proof/gzlib.c.open.lean#L24) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzrewind_null](../ZlibF/Proof/gzlib.c.rewind.lean#L80) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzrewind_spec](../ZlibF/Proof/gzlib.c.rewind.lean#L85) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzseek64_cur_negpos_ub](../ZlibF/Proof/gzlib.c.seek.lean#L867) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzseek64_dangling_next_ub](../ZlibF/Proof/gzlib.c.seek.lean#L952) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzseek64_head](../ZlibF/Proof/gzlib.c.seek.lean#L177) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzseek64_null](../ZlibF/Proof/gzlib.c.seek.lean#L805) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzseek64_refuse](../ZlibF/Proof/gzlib.c.seek.lean#L837) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzseek64_safe](../ZlibF/Proof/gzlib.c.seek.lean#L812) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzseek64_set_negpos_ub](../ZlibF/Proof/gzlib.c.seek.lean#L889) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzseek64_write_run](../ZlibF/Proof/gzlib.c.seek.lean#L232) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzseek_eq](../ZlibF/Proof/gzlib.c.seek.lean#L850) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gztell64_null](../ZlibF/Proof/gzlib.c.simple.lean#L122) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gztell64_spec](../ZlibF/Proof/gzlib.c.simple.lean#L143) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gztell_null](../ZlibF/Proof/gzlib.c.simple.lean#L154) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gztell_run](../ZlibF/Proof/gzlib.c.simple.lean#L148) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.seekTail_back](../ZlibF/Proof/gzlib.c.seek.lean#L475) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.seekTail_copy](../ZlibF/Proof/gzlib.c.seek.lean#L315) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.seekTail_copy_ub](../ZlibF/Proof/gzlib.c.seek.lean#L962) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.seekTail_dangling_ub](../ZlibF/Proof/gzlib.c.seek.lean#L919) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.seekTail_fwd](../ZlibF/Proof/gzlib.c.seek.lean#L376) | 未记录到固定目标的组合关系 |
| [Zlib.Gzread.Proofs.gzclose_r_null](../ZlibF/Proof/gzread.c.close.lean#L43) | 未记录到固定目标的组合关系 |
| [Zlib.Gzread.Proofs.gzclose_r_unbuffered](../ZlibF/Proof/gzread.c.close.lean#L56) | 未记录到固定目标的组合关系 |
| [Zlib.Gzread.Proofs.gzclose_r_unbuffered_frame](../ZlibF/Proof/gzread.c.close.lean#L78) | 未记录到固定目标的组合关系 |
| [Zlib.Gzread.Proofs.gzclose_r_wrong_mode](../ZlibF/Proof/gzread.c.close.lean#L47) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.NEEDBITS_run](../ZlibF/Proof/infback.c.macros.lean#L240) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.PULLBYTE_run](../ZlibF/Proof/infback.c.macros.lean#L156) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.PULL_run](../ZlibF/Proof/infback.c.pull.lean#L16) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.ROOM_inv](../ZlibF/Proof/infback.c.stored.lean#L35) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.ROOM_run](../ZlibF/Proof/infback.c.room.lean#L27) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.TYPE_last](../ZlibF/Proof/infback.c.inv.lean#L87) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.TYPE_more](../ZlibF/Proof/infback.c.inv.lean#L145) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.backInit_witness](../ZlibF/Proof/infback.c.callbacks.lean#L143) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.badMode_run](../ZlibF/Proof/infback.c.inv.lean#L127) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.inFinite_eof](../ZlibF/Proof/infback.c.macros.lean#L304) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.inflateBackEnd_nullstream](../ZlibF/Proof/infback.c.end.lean#L23) | [inflateBackEnd](#target-zlibf-spec-public-goal-inflatebackend) |
| [Zlib.Infback.Proofs.inflateBackEnd_ok](../ZlibF/Proof/infback.c.end.lean#L35) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.inflateBackEnd_refused](../ZlibF/Proof/infback.c.end.lean#L27) | [inflateBackEnd](#target-zlibf-spec-public-goal-inflatebackend) |
| [Zlib.Infback.Proofs.inflateBackInit__nullstream](../ZlibF/Proof/infback.c.init.lean#L239) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.inflateBackInit__ok](../ZlibF/Proof/infback.c.init.lean#L147) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.inflateBackInit__safe](../ZlibF/Proof/infback.c.init.lean#L203) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.inflateBack_eof](../ZlibF/Proof/infback.c.back.lean#L133) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.inflateBack_eof_witness](../ZlibF/Proof/infback.c.back.lean#L174) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.inflateBack_nostate](../ZlibF/Proof/infback.c.back.lean#L123) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.inflateBack_nullstream](../ZlibF/Proof/infback.c.back.lean#L118) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.order_inj](../ZlibF/Proof/infback.c.pure.lean#L17) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.order_lt](../ZlibF/Proof/infback.c.pure.lean#L14) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.order_surj](../ZlibF/Proof/infback.c.pure.lean#L21) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.storedTail_run](../ZlibF/Proof/infback.c.stored.lean#L125) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.stored_body_run](../ZlibF/Proof/infback.c.stored.lean#L285) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.stored_check](../ZlibF/Proof/infback.c.pure.lean#L35) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.stored_len_toNat](../ZlibF/Proof/infback.c.pure.lean#L58) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.stored_loop_run](../ZlibF/Proof/infback.c.stored.lean#L406) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.stored_run](../ZlibF/Proof/infback.c.stored.lean#L459) | 未记录到固定目标的组合关系 |
| [Zlib.Infback.Proofs.xwhileBrk_wf](../ZlibF/Proof/infback.c.wf.lean#L16) | 未记录到固定目标的组合关系 |
| [Zlib.Inffast.Proofs.distfix_tableSafe](../ZlibF/Proof/inffast.c.tableok.lean#L82) | 未记录到固定目标的组合关系 |
| [Zlib.Inffast.Proofs.lenfix_tableSafe](../ZlibF/Proof/inffast.c.tableok.lean#L75) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.BITS_run](../ZlibF/Proof/inflate.c.main.macros.lean#L224) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.BITS_toNat](../ZlibF/Proof/inflate.c.main.macros.lean#L234) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.BYTEBITS_inv](../ZlibF/Proof/inflate.c.main.macros.lean#L293) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.BYTEBITS_run](../ZlibF/Proof/inflate.c.main.macros.lean#L283) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.DROPBITS_inv](../ZlibF/Proof/inflate.c.main.macros.lean#L251) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.DROPBITS_run](../ZlibF/Proof/inflate.c.main.macros.lean#L241) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.INITBITS_inv](../ZlibF/Proof/inflate.c.main.macros.lean#L304) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.NEEDBITS_run](../ZlibF/Proof/inflate.c.main.macros.lean#L150) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.PULLBYTE_succ](../ZlibF/Proof/inflate.c.main.macros.lean#L89) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.PULLBYTE_zero](../ZlibF/Proof/inflate.c.main.macros.lean#L44) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.UPDATE_CHECK_run](../ZlibF/Proof/inflate.c.main.check.lean#L21) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.bytesBits_eq_bytesToBits](../ZlibF/Proof/inflate.c.main.bits.lean#L107) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflateCodesUsed_spec](../ZlibF/Proof/inflate.c.misc.lean#L180) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflateEnd_safe](../ZlibF/Proof/inflate.c.end.lean#L119) | [inflateEnd](#target-zlibf-spec-public-goal-inflateend) |
| [Zlib.Inflate.Proofs.inflateGetDictionary_spec](../ZlibF/Proof/inflate.c.dict.lean#L82) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflateGetHeader_check](../ZlibF/Proof/inflate.c.hdr.lean#L54) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflateGetHeader_nogzip](../ZlibF/Proof/inflate.c.hdr.lean#L64) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflateGetHeader_null_faults](../ZlibF/Proof/inflate.c.hdr.lean#L114) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflateGetHeader_ok](../ZlibF/Proof/inflate.c.hdr.lean#L80) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflateInit2_ok](../ZlibF/Proof/inflate.c.start.lean#L237) | [inflateInit_](#target-zlibf-spec-public-goal-inflateinit), [inflate_initialisation_domain](#target-zlibf-spec-public-goal-inflate-initialisation-domain) |
| [Zlib.Inflate.Proofs.inflateInit2_safe](../ZlibF/Proof/inflate.c.start.lean#L324) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflateInit__ok](../ZlibF/Proof/inflate.c.hdr.lean#L160) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflateInit__safe](../ZlibF/Proof/inflate.c.hdr.lean#L134) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflateMark_spec](../ZlibF/Proof/inflate.c.misc.lean#L140) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflatePrime_spec](../ZlibF/Proof/inflate.c.misc2.lean#L28) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflateReset2_safe](../ZlibF/Proof/inflate.c.init.lean#L395) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflateResetKeep_safe](../ZlibF/Proof/inflate.c.base.lean#L521) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflateReset_safe](../ZlibF/Proof/inflate.c.reset.lean#L160) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflateSetDictionary_dataerr](../ZlibF/Proof/inflate.c.dict.lean#L222) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflateSetDictionary_safe](../ZlibF/Proof/inflate.c.dict.lean#L146) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflateSetDictionary_streamerr](../ZlibF/Proof/inflate.c.dict.lean#L209) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflateStateCheck_total](../ZlibF/Proof/inflate.c.base.lean#L445) | [inflateCodesUsed](#target-zlibf-spec-public-goal-inflatecodesused), [inflateEnd](#target-zlibf-spec-public-goal-inflateend), [inflateMark](#target-zlibf-spec-public-goal-inflatemark), [inflatePrime](#target-zlibf-spec-public-goal-inflateprime), [inflateSyncPoint](#target-zlibf-spec-public-goal-inflatesyncpoint), [inflateUndermine](#target-zlibf-spec-public-goal-inflateundermine), [inflateValidate](#target-zlibf-spec-public-goal-inflatevalidate) |
| [Zlib.Inflate.Proofs.inflateSyncPoint_spec](../ZlibF/Proof/inflate.c.misc.lean#L121) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflateSync_buf_error](../ZlibF/Proof/inflate.c.sync2.lean#L131) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflateSync_check](../ZlibF/Proof/inflate.c.sync2.lean#L113) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflateUndermine_safe](../ZlibF/Proof/inflate.c.misc.lean#L109) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflateValidate_safe](../ZlibF/Proof/inflate.c.misc.lean#L95) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflate_CHECK_nowrap](../ZlibF/Proof/inflate.c.main.check.lean#L137) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflate_CHECK_run](../ZlibF/Proof/inflate.c.main.check.lean#L157) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflate_COPY__eq](../ZlibF/Proof/inflate.c.main.stored2.lean#L82) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflate_COPY_done](../ZlibF/Proof/inflate.c.main.stored.lean#L22) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflate_COPY_leave](../ZlibF/Proof/inflate.c.main.stored2.lean#L75) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflate_COPY_run](../ZlibF/Proof/inflate.c.main.stored2.lean#L57) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflate_DONE_run](../ZlibF/Proof/inflate.c.main.simple.lean#L25) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflate_LENGTH_run](../ZlibF/Proof/inflate.c.main.check.lean#L80) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflate_LENGTH_skip](../ZlibF/Proof/inflate.c.main.check.lean#L66) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflate_LENLENS_eq](../ZlibF/Proof/inflate.c.main.table3.lean#L77) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflate_LENLENS_run](../ZlibF/Proof/inflate.c.main.table6.lean#L41) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflate_LIT_full](../ZlibF/Proof/inflate.c.main.simple.lean#L29) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflate_LIT_run](../ZlibF/Proof/inflate.c.main.simple.lean#L37) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflate_STORED_bad](../ZlibF/Proof/inflate.c.main.stored2.lean#L97) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflate_STORED_ok](../ZlibF/Proof/inflate.c.main.stored2.lean#L116) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflate_STORED_wait](../ZlibF/Proof/inflate.c.main.stored2.lean#L88) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflate_TABLE_run](../ZlibF/Proof/inflate.c.main.table.lean#L52) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflate_TYPEDO_head](../ZlibF/Proof/inflate.c.main.type.lean#L61) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflate_TYPEDO_last](../ZlibF/Proof/inflate.c.main.type.lean#L26) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflate_TYPEDO_wait](../ZlibF/Proof/inflate.c.main.type.lean#L37) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflate_TYPE_go](../ZlibF/Proof/inflate.c.main.type.lean#L19) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.inflate_TYPE_leave](../ZlibF/Proof/inflate.c.main.type.lean#L11) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.ll1_run](../ZlibF/Proof/inflate.c.main.table4.lean#L69) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.llBody_run](../ZlibF/Proof/inflate.c.main.table3.lean#L90) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.llTail_run](../ZlibF/Proof/inflate.c.main.table5.lean#L46) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.lzBody_run](../ZlibF/Proof/inflate.c.main.table4.lean#L225) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.lz_run](../ZlibF/Proof/inflate.c.main.table4.lean#L244) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.noRet_NEEDBITS](../ZlibF/Proof/inflate.c.main.table2.lean#L321) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.ring_spec](../ZlibF/Proof/inflate.c.ring.lean#L116) | [inflateSetDictionary](#target-zlibf-spec-public-goal-inflatesetdictionary) |
| [Zlib.Inflate.Proofs.syncDone_good](../ZlibF/Proof/inflate.c.sync2.lean#L372) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.syncDone_owns](../ZlibF/Proof/inflate.c.sync2.lean#L423) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.syncDone_run](../ZlibF/Proof/inflate.c.sync2.lean#L248) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.syncScan_found_iff](../ZlibF/Proof/inflate.c.sync.lean#L342) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.syncScan_spec](../ZlibF/Proof/inflate.c.sync.lean#L300) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.syncStep_spec](../ZlibF/Proof/inflate.c.sync.lean#L202) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.syncTail_run](../ZlibF/Proof/inflate.c.sync2.lean#L543) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.syncsearch_null](../ZlibF/Proof/inflate.c.sync.lean#L450) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.syncsearch_run](../ZlibF/Proof/inflate.c.sync.lean#L381) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.syncsearch_spec](../ZlibF/Proof/inflate.c.sync.lean#L485) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.typedoTail_bad](../ZlibF/Proof/inflate.c.main.type.lean#L154) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.typedoTail_fixed](../ZlibF/Proof/inflate.c.main.type.lean#L116) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.typedoTail_fixed_trees](../ZlibF/Proof/inflate.c.main.type.lean#L132) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.typedoTail_stored](../ZlibF/Proof/inflate.c.main.type.lean#L92) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.typedoTail_table](../ZlibF/Proof/inflate.c.main.type.lean#L104) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.updatewindow_ring](../ZlibF/Proof/inflate.c.ring.lean#L197) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.updatewindow_safe](../ZlibF/Proof/inflate.c.uw.lean#L558) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.uwPost_counts](../ZlibF/Proof/inflate.c.ring.lean#L170) | [inflateSetDictionary](#target-zlibf-spec-public-goal-inflatesetdictionary) |
| [Zlib.Inflate.Proofs.uw_null_ok](../ZlibF/Proof/inflate.c.uw.lean#L492) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.uw_post](../ZlibF/Proof/inflate.c.uw.lean#L423) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Proofs.xwhileBrk_run](../ZlibF/Proof/inflate.c.main.xloop.lean#L36) | 未记录到固定目标的组合关系 |
| [Zlib.Inflate.Witness.init_witness](../ZlibF/Proof/inflate.c.witness.lean#L50) | 未记录到固定目标的组合关系 |
| [Zlib.Inftrees.Proofs.Cover.bits_add_drop](../ZlibF/Proof/inftrees.c.cover.leaf.lean#L80) | 未记录到固定目标的组合关系 |
| [Zlib.Inftrees.Proofs.Cover.cell_lt_fn](../ZlibF/Proof/inftrees.c.cover.fn.lean#L210) | 未记录到固定目标的组合关系 |
| [Zlib.Inftrees.Proofs.Cover.distLeaf_of](../ZlibF/Proof/inftrees.c.cover.leaf.lean#L56) | [decode_table_matches_format](#target-zlib-inftrees-spec-decodesemantics-goal-decode-table-matches-format), [decode_table_leaf_sound](#target-zlib-inftrees-spec-decodesoundness-goal-decode-table-leaf-sound), [constructor_establishes_query_stability](#target-zlib-inftrees-spec-decodetablestability-goal-constructor-establishes-query-stability), [constructor_establishes_fast_leaf_flags](#target-zlib-inftrees-spec-fasttableflags-goal-constructor-establishes-fast-leaf-flags), [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe), [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent), [constructor_subtable_bits](#target-zlib-inftrees-spec-subtable-goal-constructor-subtable-bits) |
| [Zlib.Inftrees.Proofs.Cover.group_cover](../ZlibF/Proof/inftrees.c.cover.group.lean#L64) | [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe), [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent), [constructor_subtable_bits](#target-zlib-inftrees-spec-subtable-goal-constructor-subtable-bits) |
| [Zlib.Inftrees.Proofs.Cover.group_cover_fn](../ZlibF/Proof/inftrees.c.cover.fn.lean#L163) | 未记录到固定目标的组合关系 |
| [Zlib.Inftrees.Proofs.Cover.group_cover_idx](../ZlibF/Proof/inftrees.c.cover.group.lean#L161) | [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe), [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent), [constructor_subtable_bits](#target-zlib-inftrees-spec-subtable-goal-constructor-subtable-bits) |
| [Zlib.Inftrees.Proofs.Cover.group_cover_idx_fn](../ZlibF/Proof/inftrees.c.cover.fn.lean#L185) | 未记录到固定目标的组合关系 |
| [Zlib.Inftrees.Proofs.Cover.invalid_leaf](../ZlibF/Proof/inftrees.c.cover.leaf.lean#L66) | [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe), [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent) |
| [Zlib.Inftrees.Proofs.Cover.lenLeaf_of](../ZlibF/Proof/inftrees.c.cover.leaf.lean#L40) | [decode_table_matches_format](#target-zlib-inftrees-spec-decodesemantics-goal-decode-table-matches-format), [decode_table_leaf_sound](#target-zlib-inftrees-spec-decodesoundness-goal-decode-table-leaf-sound), [constructor_establishes_query_stability](#target-zlib-inftrees-spec-decodetablestability-goal-constructor-establishes-query-stability), [constructor_establishes_fast_leaf_flags](#target-zlib-inftrees-spec-fasttableflags-goal-constructor-establishes-fast-leaf-flags), [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe), [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent), [constructor_subtable_bits](#target-zlib-inftrees-spec-subtable-goal-constructor-subtable-bits) |
| [Zlib.Inftrees.Proofs.Cover.root_cover](../ZlibF/Proof/inftrees.c.cover.root.lean#L90) | [decode_table_matches_format](#target-zlib-inftrees-spec-decodesemantics-goal-decode-table-matches-format), [short_decode_table_leaf_sound](#target-zlib-inftrees-spec-decodeshort-goal-short-decode-table-leaf-sound), [decode_table_leaf_sound](#target-zlib-inftrees-spec-decodesoundness-goal-decode-table-leaf-sound), [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant), [constructor_establishes_query_stability](#target-zlib-inftrees-spec-decodetablestability-goal-constructor-establishes-query-stability), [constructor_establishes_fast_leaf_flags](#target-zlib-inftrees-spec-fasttableflags-goal-constructor-establishes-fast-leaf-flags), [inflate_table_content](#target-zlib-inftrees-spec-goal-inflate-table-content), [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe), [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent), [constructor_subtable_bits](#target-zlib-inftrees-spec-subtable-goal-constructor-subtable-bits) |
| [Zlib.Inftrees.Proofs.Cover.root_cover_complete_fn](../ZlibF/Proof/inftrees.c.cover.fn.lean#L140) | [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe), [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent), [constructor_subtable_bits](#target-zlib-inftrees-spec-subtable-goal-constructor-subtable-bits) |
| [Zlib.Inftrees.Proofs.Cover.root_cover_fn](../ZlibF/Proof/inftrees.c.cover.fn.lean#L130) | 未记录到固定目标的组合关系 |
| [Zlib.Inftrees.Proofs.Cover.root_single_fn](../ZlibF/Proof/inftrees.c.cover.fn.lean#L226) | 未记录到固定目标的组合关系 |
| [Zlib.Inftrees.Proofs.inflate_fixed_ok](../ZlibF/Proof/inftrees.c.fixed.lean#L21) | 未记录到固定目标的组合关系 |
| [Zlib.Inftrees.Proofs.inflate_table_correct_ret](../ZlibF/Proof/inftrees.c.lean#L65) | 未记录到固定目标的组合关系 |
| [Zlib.Inftrees.Proofs.inflate_table_safe](../ZlibF/Proof/inftrees.c.lean#L34) | 未记录到固定目标的组合关系 |
| [Zlib.Trees.Proofs.GB.kraft_clamped](../ZlibF/Proof/trees.c.heap.gbtree.lean#L132) | 未记录到固定目标的组合关系 |
| [Zlib.Trees.Proofs.Out.bi_flush_spec](../ZlibF/Proof/trees.c.bits.lean#L548) | 未记录到固定目标的组合关系 |
| [Zlib.Trees.Proofs.Out.bi_reverse_correct](../ZlibF/Proof/trees.c.reverse.lean#L91) | 未记录到固定目标的组合关系 |
| [Zlib.Trees.Proofs.Out.bi_reverse_safe](../ZlibF/Proof/trees.c.reverse.lean#L51) | 未记录到固定目标的组合关系 |
| [Zlib.Trees.Proofs.Out.bi_windup_spec](../ZlibF/Proof/trees.c.bits.lean#L731) | 未记录到固定目标的组合关系 |
| [Zlib.Trees.Proofs.Out.init_block_spec](../ZlibF/Proof/trees.c.block.lean#L217) | 未记录到固定目标的组合关系 |
| [Zlib.Trees.Proofs.Out.init_block_spec0](../ZlibF/Proof/trees.c.block.lean#L102) | [deflateInit_](#target-zlibf-spec-public-goal-deflateinit), [deflateReset](#target-zlibf-spec-public-goal-deflatereset), [deflateResetKeep](#target-zlibf-spec-public-goal-deflateresetkeep) |
| [Zlib.Trees.Proofs.Out.send_bits_spec](../ZlibF/Proof/trees.c.bits.lean#L411) | 未记录到固定目标的组合关系 |
| [Zlib.Trees.Proofs.Out.tr_align_emit](../ZlibF/Proof/trees.c.align.lean#L42) | 未记录到固定目标的组合关系 |
| [Zlib.Trees.Proofs.Out.tr_flush_bits_emit](../ZlibF/Proof/trees.c.align.lean#L30) | 未记录到固定目标的组合关系 |
| [Zlib.Trees.Proofs.Out.tr_init_spec](../ZlibF/Proof/trees.c.block.lean#L245) | [deflateInit_](#target-zlibf-spec-public-goal-deflateinit), [deflateReset](#target-zlibf-spec-public-goal-deflatereset), [deflateResetKeep](#target-zlibf-spec-public-goal-deflateresetkeep) |
| [Zlib.Trees.Proofs.Out.tr_tally_spec](../ZlibF/Proof/trees.c.tally.lean#L327) | 未记录到固定目标的组合关系 |
| [Zlib.Trees.Proofs.gen_bitlen_correct](../ZlibF/Proof/trees.c.heap.gbtop.lean#L403) | 未记录到固定目标的组合关系 |
| [Zlib.Trees.Proofs.gen_bitlen_safe](../ZlibF/Proof/trees.c.heap.gbtop.lean#L421) | 未记录到固定目标的组合关系 |
| [Zlib.Trees.Proofs.pqdownheap_correct](../ZlibF/Proof/trees.c.heap.pqrun.lean#L313) | 未记录到固定目标的组合关系 |
| [Zlib.Trees.Proofs.pqdownheap_safe](../ZlibF/Proof/trees.c.heap.pqrun.lean#L330) | 未记录到固定目标的组合关系 |
| [Zlib.Trees.Proofs.pqremove_correct](../ZlibF/Proof/trees.c.heap.pqrun.lean#L342) | 未记录到固定目标的组合关系 |
| [Zlib.Trees.Proofs.pqremove_safe](../ZlibF/Proof/trees.c.heap.pqrun.lean#L359) | 未记录到固定目标的组合关系 |
| [Zlib.Zutil.Proofs.zError_correct](../ZlibF/Proof/zutil.c.lean#L121) | 未记录到固定目标的组合关系 |
| [Zlib.Zutil.Proofs.zError_safe](../ZlibF/Proof/zutil.c.lean#L113) | 未记录到固定目标的组合关系 |
| [Zlib.Zutil.Proofs.zcalloc_correct_none](../ZlibF/Proof/zutil.c.lean#L265) | 未记录到固定目标的组合关系 |
| [Zlib.Zutil.Proofs.zcalloc_correct_size](../ZlibF/Proof/zutil.c.lean#L256) | 未记录到固定目标的组合关系 |
| [Zlib.Zutil.Proofs.zcalloc_correct_some](../ZlibF/Proof/zutil.c.lean#L242) | 未记录到固定目标的组合关系 |
| [Zlib.Zutil.Proofs.zcalloc_safe](../ZlibF/Proof/zutil.c.lean#L228) | 未记录到固定目标的组合关系 |
| [Zlib.Zutil.Proofs.zcalloc_zcfree_no_leak](../ZlibF/Proof/zutil.c.lean#L310) | 未记录到固定目标的组合关系 |
| [Zlib.Zutil.Proofs.zcfree_correct](../ZlibF/Proof/zutil.c.lean#L284) | 未记录到固定目标的组合关系 |
| [Zlib.Zutil.Proofs.zcfree_correct_null](../ZlibF/Proof/zutil.c.lean#L302) | 未记录到固定目标的组合关系 |
| [Zlib.Zutil.Proofs.zcfree_safe](../ZlibF/Proof/zutil.c.lean#L274) | 未记录到固定目标的组合关系 |
| [Zlib.Zutil.Proofs.zlibCompileFlags_correct](../ZlibF/Proof/zutil.c.lean#L169) | 未记录到固定目标的组合关系 |
| [Zlib.Zutil.Proofs.zlibCompileFlags_safe](../ZlibF/Proof/zutil.c.lean#L163) | 未记录到固定目标的组合关系 |
| [Zlib.Zutil.Proofs.zlibVersion_correct](../ZlibF/Proof/zutil.c.lean#L153) | 未记录到固定目标的组合关系 |
| [Zlib.Zutil.Proofs.zlibVersion_safe](../ZlibF/Proof/zutil.c.lean#L130) | 未记录到固定目标的组合关系 |
| [ZlibF.Spec.Api.Proofs.Layer.ext](../ZlibF/Proof/Format/Api.lean) | [dict_roundtrip](#target-zlibf-spec-api-goal-dict-roundtrip), [format_deterministic](#target-zlibf-spec-api-goal-format-deterministic), [format_prefix_free](#target-zlibf-spec-api-goal-format-prefix-free), [inflate_completes](#target-zlibf-spec-api-goal-inflate-completes), [inflate_decodes](#target-zlibf-spec-api-goal-inflate-decodes), [inflate_deferred_distance](#target-zlibf-spec-api-goal-inflate-deferred-distance) |
| [ZlibF.Spec.Api.Proofs.inflate_deferred_distance_rejects_legacy_consistency](../ZlibF/Proof/Api/InflateCausality.lean#L229) | 未记录到固定目标的组合关系 |
| [ZlibF.Spec.Blocks.append](../ZlibF/Proof/Format/Deflate.lean) | [compress_roundtrip](#target-zlibf-spec-api-goal-compress-roundtrip), [dict_roundtrip](#target-zlibf-spec-api-goal-dict-roundtrip), [format_deterministic](#target-zlibf-spec-api-goal-format-deterministic), [format_prefix_free](#target-zlibf-spec-api-goal-format-prefix-free), [inflate_completes](#target-zlibf-spec-api-goal-inflate-completes), [inflate_decodes](#target-zlibf-spec-api-goal-inflate-decodes), [inflate_deferred_distance](#target-zlibf-spec-api-goal-inflate-deferred-distance) |
| [ZlibF.Spec.Blocks.det](../ZlibF/Proof/Format/Deflate.lean) | [compress_roundtrip](#target-zlibf-spec-api-goal-compress-roundtrip), [dict_roundtrip](#target-zlibf-spec-api-goal-dict-roundtrip), [format_deterministic](#target-zlibf-spec-api-goal-format-deterministic), [format_prefix_free](#target-zlibf-spec-api-goal-format-prefix-free), [inflate_completes](#target-zlibf-spec-api-goal-inflate-completes), [inflate_decodes](#target-zlibf-spec-api-goal-inflate-decodes), [inflate_deferred_distance](#target-zlibf-spec-api-goal-inflate-deferred-distance) |
| [ZlibF.Spec.Gzip.ext](../ZlibF/Proof/Format/Wrapper.lean) | [dict_roundtrip](#target-zlibf-spec-api-goal-dict-roundtrip), [format_deterministic](#target-zlibf-spec-api-goal-format-deterministic), [format_prefix_free](#target-zlibf-spec-api-goal-format-prefix-free), [inflate_completes](#target-zlibf-spec-api-goal-inflate-completes), [inflate_decodes](#target-zlibf-spec-api-goal-inflate-decodes), [inflate_deferred_distance](#target-zlibf-spec-api-goal-inflate-deferred-distance) |
| [ZlibF.Spec.Prefix.det](../ZlibF/Proof/Format/Deflate.lean) | 未记录到固定目标的组合关系 |
| [ZlibF.Spec.Prefix.ext](../ZlibF/Proof/Format/Deflate.lean) | [compress_roundtrip](#target-zlibf-spec-api-goal-compress-roundtrip), [dict_roundtrip](#target-zlibf-spec-api-goal-dict-roundtrip), [format_deterministic](#target-zlibf-spec-api-goal-format-deterministic), [format_prefix_free](#target-zlibf-spec-api-goal-format-prefix-free), [inflate_completes](#target-zlibf-spec-api-goal-inflate-completes), [inflate_decodes](#target-zlibf-spec-api-goal-inflate-decodes), [inflate_deferred_distance](#target-zlibf-spec-api-goal-inflate-deferred-distance) |
| [ZlibF.Spec.Proofs.prefixFree](../ZlibF/Proof/Format/Huffman.lean#L105) | [short_decode_table_leaf_sound](#target-zlib-inftrees-spec-decodeshort-goal-short-decode-table-leaf-sound), [decode_table_leaf_sound](#target-zlib-inftrees-spec-decodesoundness-goal-decode-table-leaf-sound), [constructor_establishes_query_stability](#target-zlib-inftrees-spec-decodetablestability-goal-constructor-establishes-query-stability), [short_rejected_leaf_stays_invalid](#target-zlib-inftrees-spec-decodetablestability-goal-short-rejected-leaf-stays-invalid), [constructor_establishes_fast_leaf_flags](#target-zlib-inftrees-spec-fasttableflags-goal-constructor-establishes-fast-leaf-flags), [compress_roundtrip](#target-zlibf-spec-api-goal-compress-roundtrip), [dict_roundtrip](#target-zlibf-spec-api-goal-dict-roundtrip), [format_deterministic](#target-zlibf-spec-api-goal-format-deterministic), [format_prefix_free](#target-zlibf-spec-api-goal-format-prefix-free), [inflate_completes](#target-zlibf-spec-api-goal-inflate-completes), [inflate_decodes](#target-zlibf-spec-api-goal-inflate-decodes), [inflate_deferred_distance](#target-zlibf-spec-api-goal-inflate-deferred-distance) |
| [ZlibF.Spec.Public.Proofs.DeflateInit.default_init_witness](../ZlibF/Proof/public-deflate-init.lean#L282) | 未记录到固定目标的组合关系 |
| [ZlibF.Spec.Public.Proofs.free_writable_matches_dropWindow](../ZlibF/Proof/Api/HeapCleanup.lean#L55) | 未记录到固定目标的组合关系 |
| [ZlibF.Spec.Public.Proofs.legacy_codes_used_impossible](../ZlibF/Proof/Api/QueryLayout.lean#L123) | 未记录到固定目标的组合关系 |
| [ZlibF.Spec.Zlib.ext](../ZlibF/Proof/Format/Wrapper.lean) | [compress_roundtrip](#target-zlibf-spec-api-goal-compress-roundtrip), [dict_roundtrip](#target-zlibf-spec-api-goal-dict-roundtrip), [format_deterministic](#target-zlibf-spec-api-goal-format-deterministic), [format_prefix_free](#target-zlibf-spec-api-goal-format-prefix-free), [inflate_completes](#target-zlibf-spec-api-goal-inflate-completes), [inflate_decodes](#target-zlibf-spec-api-goal-inflate-decodes), [inflate_deferred_distance](#target-zlibf-spec-api-goal-inflate-deferred-distance) |

## 更新记录

证明或登记表发生变化后，需要重新生成本页。生成过程会编译并检查
定理的精确类型，不会修改证明、目标或登记表。
结果是否通过项目验收，仍须依据[检查规则](checking/README.md)。

输入指纹：`528c7db39919e766d66d60e9594967f1b09ef2d7a16e499e3f2f042dea7cbeea`。
<!-- proof-progress:end -->

## 当前证明范围

当前证明范围包括默认初始化、限定平台范围的快速解码接口，以及解码表的内容、安全性和读取范围。上方索引列出每个目标的证明状态和定义域。完整公开 `inflate` 与 `deflate` 目标仍未完成。

CI 验收必须对应一个明确的提交。请查看[主分支运行记录](https://github.com/cla7aye15I4nd/zlib-f/actions?query=branch%3Amain)和[检查规则](checking/README.md)；合并或本地构建本身都不足以说明最终验收通过。平台的对象大小前提是已经接受的[环境假设](spec/platform.md)，不是尚待决定的范围问题。

## 剩余工作

红色边框表示已经记录了阻碍证明的问题，下文给出证据和下一步。证明尝试耗时很长，本身不构成这种阻碍。灰色目标可以开始推进；它们缺少的内部引理和调用序列不变量并没有全部画在图中。

### 公开 API 的证明准备情况

**灰色表示尚未证明，不表示无法推进。可以立即开展独立工作。** 被调用函数呈绿色，并不意味着调用者自身的前置条件、循环、返回结果和内存效果已经建立。一个能直接调用的 API，仍可能存在错误的契约或已确认的源码缺陷；只有这类证据才足以给目标加上阻碍边框。不能只凭图中缺少箭头判断证明准备情况。

[证据索引](progress.md)区分证明引用、C 调用和规格引用。下面列出需要组合的证明义务，这些义务与精确目标的连接尚未完成。它们不会引入新的公开调用假设，也不会赋予目标任何已检查的输入覆盖范围。

#### 打开、查询与关闭操作的前提

证明打开文件不需要先完成整个引擎。主要工作在公共辅助函数 `gz_open`：模式解析循环、真实分配、字符串复制、文件描述符效果，以及初始化不变量。位置查询尚缺的基础，是覆盖所有允许调用序列的位置不变量。关闭操作尚缺的基础，是覆盖这些调用序列的所有权事实，其中也包括分配失败。

目前本地执行证明已覆盖：

- [打开入口](../ZlibF/Proof/gzlib.c.open.lean)：NULL 参数、负文件描述符和第一次分配失败。结论给出未改变的文件系统和精确堆状态，也包括分配尝试计数器。
- [读模式关闭](../ZlibF/Proof/gzread.c.close.lean)：NULL、模式不匹配，以及在 `GzGood` 条件下完整的未缓冲执行。范围包含文件描述符错误，释放消息、路径和句柄，以及无关分配保持不变的框架性质。
- [位预置入口](../ZlibF/Proof/deflate.c.prime.lean)：在压紧待输出字节之前，拒绝流状态和非法位数的分支。

这些是具有明确内部范围的结果，并不是完整公开目标的证明。特别是，仍须从允许的公开调用序列推出 `GzGood`。不能凭一个分支的结果，就把灰色公开节点改成绿色。

#### 回调解码器的前提

`inflateBack` 不必等待普通 `inflate` 的完整目标。建立和释放状态的操作已经登记。现有的入口、位输入、窗口交付和 stored 块论证可以复用；压缩块和完整的公开回调协议仍需组合证明。

要求输出缓冲区与状态序列缓冲区分离的快速路径定理，并不覆盖输出位于窗口内部的情形。关于解码表返回码的定理，也不能建立已安装表项的内容。[回调证明指南](proof/callbacks.md)标出可复用论证，并说明其回调定义域的限制。缺少这些前提，不妨碍独立推进其他块类型或错误路径。

#### 每个未完成公开目标的下一步

“开始”表示无需等待完整引擎定理就能开展的工作。“组合”列出完整收束目标所需的前提；其他独立分支仍可推进。表中任何一行都不授予已检查状态，也不把被调用函数的规格当作假设。

<!-- proof-readiness:start -->
| 公开目标 | 图中所示证明工作 | 下一步与缺少的前提 |
| --- | --- | --- |
| `gzopen`, `gzopen64`, `gzdopen`, `gz_initialisation_domain` | 开始：打开与清理 | <a id="readiness-gzopen"></a> **开始：**公共模式循环、各分配结果、路径格式化与复制、文件描述符效果、`OpenState` 和具体见证。上文的入口与失败分支已经过本地检查。 |
| `gztell64`, `gztell` | 需要：位置约束 | <a id="readiness-gztell64"></a> **组合：**从读取、写入、定位和回退字节的调用序列推出位置不变量 `PosInv`，再复用现有算术执行证明。 |
| `gzclose_r` | 需要：资源归属 | <a id="readiness-gzclose-r"></a> **开始：**已初始化缓冲区的清理，以及从调用序列建立其所有权的证明。未缓冲执行及框架性质已有本地检查；仅有 `inflateEnd` 还不够。 |
| `gzclose_w`, `gzclose` | 需要：交付与清理 | <a id="readiness-gzclose-w"></a> **组合：**实际补零、最终压缩和文件写入，全部清理与错误路径，再利用两个完整的关闭结果证明分派操作。 |
| `gzseek64`, `gzseek` | 需要：定位与状态序列 | <a id="readiness-gzseek64"></a> **开始：**位置与指针的状态序列不变量、缓冲和透明模式路径，以及精确的错误框架性质。负位置的可达性与溢出复核复核尚未完成。 |
| `gzdirect`, `gzread`, `gzfread`, `gzgetc`, `gzgetc_`, `gzgets`, `gzungetc` | 需要：读取路径证明 | <a id="readiness-gzdirect"></a> **开始：**公共延迟准备、透明模式读取，以及缓冲区与状态序列不变量。**组合：**压缩路径中的实际解码执行，再建立 EOF、计数、字节回退和错误条款。`gzdirect` 需要格式探测与初始化，不需要完整的数据解码循环。 |
| `gzwrite`, `gzfwrite`, `gzputc`, `gzputs`, `gzvprintf`, `gzprintf`, `gzflush`, `gzsetparams` | 需要：写入路径证明 | <a id="readiness-gzwrite"></a> **开始：**缓冲、格式化、透明模式写入及失败情况。**组合：**压缩输出与参数变更中的实际压缩器执行。 |
| `deflateInit2_`, `deflate_initialisation_domain` | 开始：初始化与分配 | <a id="readiness-deflateinit2"></a> **开始：**参数归一化、五次分配、全部失败清理、实际建立 `DGood` 和树状态，以及具体见证。重置证明要求不变量已经成立，并不会为新分配的存储建立它。 |
| `deflatePrime` | 开始：压紧与位操作 | <a id="readiness-deflateprime"></a> **开始：**待输出字节的压紧、带检查的移位、位插入与交付，以及不变量和框架性质的保持。拒绝分支已有本地检查；接受的位数范围仍未完成。 |
| `deflateBound_z`, `deflateBound` | 开始：上界与头部审查 | <a id="readiness-deflatebound-z"></a> **开始：**把现有执行公式连接到具有饱和语义的数学上界，包括头部字符串与额外字段长度。额外长度复核复核尚未完成，并不是新确认的阻碍。 |
| `deflateSetDictionary` | 开始：窗口与哈希 | <a id="readiness-deflatesetdictionary"></a> **开始：**填充窗口、插入哈希链、恢复保存的输入，再处理校验和以及精确的状态和框架效果。绿色校验和调用只覆盖其中的校验和部分。 |
| `inflateCopy`, `deflateCopy` | 开始：复制与重定位 | <a id="readiness-inflatecopy"></a> **开始：**分配失败、缓冲区复制、指针重定位及独立所有权。在声称覆盖完整定义域之前，解决已记录的复制与状态序列调查；不能悄悄增加前提。 |
| `deflateParams` | 需要：块交付与参数状态 | <a id="readiness-deflateparams"></a> **组合：**实际交付旧块、处理返回码，并更新规范的调参表行。在完整收束之前，检查拒绝路径精确保持了哪些状态。 |
| `inflateSync` | 需要：扫描与状态序列 | <a id="readiness-inflatesync"></a> **开始：**组合现有的首次扫描与恢复扫描、暂存位、标记搜索、重置，以及记账和框架结果。从调用序列推出窗口与重置前提。 |
| `compress2_z`, `compress2`, `compress_z`, `compress` | 需要：压缩器执行 | <a id="readiness-compress2-z"></a> **开始：**参数、标量长度和清理。**组合：**实际初始化、压缩和结束操作及精确输出，再处理外层封装。抽象的往返性质还不够。 |
| `uncompress2_z`, `uncompress2`, `uncompress_z`, `uncompress` | 需要：解码器执行 | <a id="readiness-uncompress2-z"></a> **开始：**标量结果、空间不足和清理。**组合：**实际初始化、解压和结束操作、精确消费量与输出，再处理外层封装。 |
| `inflate`, `deflate` | 需要：分派不变量 | <a id="readiness-inflate"></a> **组合：**解码表或哈希链的含义、分派不变量、循环终止，以及输出和记账。绿色校验和目标不能建立这些前提。 |
| `inflate_sequence`, `deflate_sequence`, `inflate_back_sequence`, `gz_sequence` | 需要：执行与格式 | <a id="readiness-inflate-sequence"></a> **组合：**每次实际调用的安全性、状态序列保持、向独立格式模型的精化，以及跨输入输出分块的完成性质。 |
| `inflateBack` | 需要：表、窗口与回调 | <a id="readiness-inflateback"></a> **组合：**压缩块的 TABLE/LEN 执行、窗口内部的输出、公开回调所有权、循环终止和精确的输入输出记账。现有 stored 块和入口路径仍可独立推进。 |
| `inflateInit2_` | 阻碍：清理契约 | <a id="readiness-inflateinit2"></a> 已确认的清理契约反例[记录在下文](#inflate-initialization-cleanup)。成功初始化和其他独立目标仍可推进。 |
<!-- proof-readiness:end -->

近期顺序是：先推进独立的入口、清理和算术路径，再建立公共的打开、位置和所有权不变量，最后完成整函数组合。回调压缩块可以并行推进。如果某个前提尚不清楚，应在这里记录精确问题；不能凭空制造依赖，也不能把经过的时间当作存在阻碍的证据。

### 集成

审查各函数手册的具体范围，并在经过评审的审计更新中重新生成文档来源策略锁。独立审查新增的源码锁、内核语法锁和首个验证基线。维护四项检查和受保护路径评审所需的仓库保护。新检查结果只有完成各自必需的检查后，才能登记。

### 公开契约

接受验证基线之前，须独立批准 103 个目标的陈述、调用者定义域和表示限制。把普通数据阶段的精化扩展到高级 raw 字典替换，以及所有头部、位预置和恢复组合；保留各入口精确的效果和无条件调用序列安全性。任何最终正确性声明都不能悄悄删去这些义务。

### 规格审查

#### Gzip 定位模式
<!-- proof-blocker: ZlibF.Spec.Api.Goal.gz_seek_read -->

抽象目标 `gz_seek_read` 不成立：关系 `GzSeek` 允许返回的句柄从读取模式变为写入模式，因此模型中的后续读取可能不返回数据。[经过检查的反例](../tests/verification/counterexamples/gz-seek-mode.lean)使用一个已经打开、包含两个字节的读取句柄。证明该目标之前，需要审查定位关系。这是模型问题，不是已确认的 zlib 问题。

#### Inflate 初始化清理
<!-- proof-blocker: ZlibF.Spec.Public.Goal.inflateInit2_ -->

当前的 `inflateInit2_` 目标在窗口参数非法时不成立。后置条件 `SameObjects` 要求状态表的结构完全不变，但分配后再释放仍会扩展这个表。[经过检查的反例](../tests/verification/counterexamples/inflate-init2-table-shape.lean)使用合法的调用者堆，并证明两个表的大小分别为四和零。证明该目标之前，需要审查契约和模型。这不是已确认的 zlib 问题。

独立审查已经修正的共享关系 `Uncompress2`。延迟距离处理和精确释放的修正，都有独立反例和经过检查的回归证明；实现精化仍未完成。原先在内存失败时要求输出为空的条款，以及在缓冲区错误时要求扩展输出的条款，已依据现有成对反例移除。在把较早的抽象 gz 和字典模型当作完整操作精化之前，还须完成它们；具体公开目标不会假设被调用函数的契约成立。

### 翻译审查

审查所选构建采用的 C 语言版本和实现扩展。尤其需要确认可达的“空指针加零”和“空指针减空指针”操作是否具有定义。当前模型允许其中一些操作，而 `Ptr.diff` 的源码注释错误地把空指针相减归于 C23。[对照表](spec/safety.md#null-pointers-and-pointer-differences)记录了实际定义和语言依据。这次文档修改不会改变运行时，也不能证明存在可达的上游缺陷。

在已修正压缩器自动存储的基础上，继续逐语句审查。压缩器的窗口滑动现在按源码顺序检查有符号减法。[内部状态回归](../tests/regression/deflate-slide/README.md)比较三个有定义的边界情形，并在 C 和 Lean 中都拒绝一个人为构造的溢出。恢复不受检查的减法，只会改变溢出情形的观察结果。这里没有声称该人为状态实际可达；仍须从合法调用序列推出有符号运算的边界。

树合并中针对所选深度的源码级重新读取已经恢复，并有[六例回归](../tests/regression/trees-depth-read/README.md)和必需的结构检查；该检查会拒绝先前缓存表达式的写法。仍须证明内部深度读取之前的初始化时序。审查标量与指针的别名，以及压缩器指针相减时空指针减空指针的特殊情况；该项审查未完成。

### CRC 地址模型

CRC 翻译现在为模型表示的每个静态或内嵌字节数组保留稳定的起始地址余数。两个公开 CRC 更新入口的本地证明，都覆盖所有余数、种子和可读长度，并给出同样的堆不变结论。原先的 47 字节静态输入，现在作为[正向回归](../tests/verification/regressions/crc-static-address.lean)。公开契约和调用者定义域没有改变。本地证据仍须在集成提交上完成最终验收检查。

把表示关系扩展到一般 ABI 布局、有效类型、标量存储单元别名，以及其他记录的字节视图。当前地址抽象只表示 CRC 对齐测试观察到的低三位，不是完整的地址空间模型。

### Inflate 因果模型

对照 C，完成通用输出精化和未知字典精化。先前要求整个预读区一致的条件不成立；改用支持当前结论的比特前缀，这项修正已经过评审。数据错误检测固定滞后八字节的说法也有反例；需要推导有依据的替代条件，不能直接提高常数。登记已经检查的 `inflate_decodes` 模型证明，再为实际解码器执行建立这些条件。除了已检查的模型见证和有限执行矩阵，还须证明通用的负值位预置衔接。

### 差分测试框架

在自动验证中保留新增的分配失败和负值位预置回归。测试拥有的 gz 句柄、输入行和 deflate 缓冲区现在都会释放。普通运行与未抑制报告的运行时检查器运行，都比较全部 47,890 个输入。一个清理变异确认：如果缺少结束调用，框架仍会报告库状态泄漏。

### 证明变异

补齐其余旧列表。每个新证明的公开入口，都必须在锁定映射中提供直接针对翻译的变异，并展示它们在对应函数证明中失败。尚未证明的入口应在取得证明时一并建立这些记录。

### 解码表

把已证明的规范码覆盖和表项形状引理，连接到 `inflate_table` 实际写出的堆；建立解码器使用的表谓词。

### Inflate

对于实际构造的表，内部码长根表查找已有执行范围受限的结果。它最多读取一个输入字节，保持精确的输入游标和比特流，并在输入耗尽时退出。这个辅助结果没有完成 CODELENS、分派不变量或公开 `inflate` 目标。见[查表证明](../ZlibF/Proof/inflate.c.lookup-codes.lean)和[游标证明](../ZlibF/Proof/inflate.c.input-cursor.lean)。

实际窗口更新函数在已有窗口、新分配和真正分配失败三种情况下，都保持逐字节对象的平台大小界和静态存储。它使用已证明的默认分配器和环形复制。平台大小界是环境前提；该定理证明操作保持了它。它还没有完成公开 `inflate` 目标、所有权、记账或完整的调用者框架性质。见[窗口证明](../ZlibF/Proof/inflate.c.window-platform.lean)。

经过本地检查的内部快速路径主体，现在会产生一个独立的字面量或复制记号，结束块，或者在不产生输出的情况下拒绝非法长度码、非法距离码或距离过远的匹配。实际距离结果保持精确的剩余比特，并把复制结果等同于独立的逐字节状态序列复制。记号关系针对原始格式文法，已有经过检查的组合、分解和拒绝结果。整个快速调用的比特来源，也已贯穿循环、字节回退和最终写回进行检查。所有这些结果都保留了相同的安全性结论。

从实际构造、安装和初始化过程，建立表的含义、后缀稳定性、相容的叶标志和窗口中保留的字节。完成整个快速调用的输出组合，并覆盖所有合法缓冲区视图。完成其他解码模式、跨调用组合、复制和恢复。这些仍是内部定义域上的结果，并不是已登记的公开证明。公开 `inflate` 及其调用序列目标仍未完成。

### 回调解码

完成表构造、压缩块、回调组合和完整函数。

### Deflate

完成通用初始化 `deflateInit2_`、字典设置、位预置、复制、`fill_window`、策略循环和完整函数。恢复的字典查询证明可以构建，并在自身证明中拒绝三个翻译变异；登记仍待完成。

精确目标 `Goal.deflateInit_` 现在在 `public-deflate-init` 中有经过本地检查的证明。它展开实际的固定参数调用：窗口指数 15、内存级别 8、策略 0；压缩级别仍可任意选择。证明覆盖版本与参数拒绝、五次分配的全部结果、失败清理、调用前的对象的框架性质和精确的存活对象账目。成功执行会建立 `DGood`，而不是把它作为调用者前提。一个具体的默认调用者能够成功返回该不变量。通用 `deflateInit2_` 定理仍未完成，也不是这项结果的依赖。

完整根构建、全新的完整内核重放、允许公理检查和零占位符扫描均在本地通过。三个直接包装层变异，在全新内核中使原始精确公开证明遭到拒绝。错误符号上限和遗漏清理这两个变异，仍保有同步后的完整源码相等性，但其执行证明因类型错误失败。资源不足造成的失败不计入结果。严格入口变异列表也已通过。

精确的默认入口证明及其具体见证已经登记。生成的锁增加了 72 条语义记录和两条定理类型记录，原有语义记录和定理类型记录没有改变。仍须在一个明确的 CI 提交上验收。这些是本地结果，不是 CI 批准。

### 树构造

实际的 `gen_codes`、叶准备、堆排序，以及完整的合并与根存储前缀，都已有经过检查的内部执行证明。节点边界和队列事实，来自实际的描述符、重置、扫描、修复和排序执行。输入堆中的数组内容、码长和深度仍不受限制。每次合并都按源码顺序选择子节点、写入尾部、更新频率与深度、写入父节点并执行向下调整。循环会终止，最终根存储具有精确的状态效果。这里使用实际被调用函数的执行定理。

实际森林和最终根存储现在会建立码长表示所需的前提。在明确的存储和静态表条件下，完整的实际 `build_tree` 执行两次编码生成调用。已安装的字面量、距离和位长描述符满足表条件。每个初始频率非零的符号，都得到正的受限码长，以及能够放入该长度的精确反转规范码字。这里没有假设被调用函数的契约。实际码长和存储的码字，现在与独立格式中的规范码及完整编码规则一致。其解码器会返回每个最初使用过的符号，并保留其后的任意比特后缀。

构造器的精确框架性质保持调用者的输出不变量和已有比特。实际构造再发送一个使用过的符号，可以在同一个堆上组合，并产生可独立解码的输出。它要求有十五比特可用空间，这是明确的内部义务；仍须从块与共享存储界推出这个条件。初始化与任意合法调用序列仍未完成。这些是内部状态结果，不是公开 `deflate` 定理。

实际 `scan_tree` 会终止、写入哨兵，并为每段连续游程记录精确的频率递增，运算遵循无符号回绕。实际 `build_bl_tree` 组合两次扫描、位长树构造、降序搜索和无符号成本更新，并保持源树码字及描述符。通用搜索返回 2..18；实际块初始化和源树构造建立了更强的 3..18 范围、字面量与距离计数范围 257..286 和 1..30，以及全部十九个位长值都不超过七的性质。

调用组合证明表明：对当前块能够容纳的任意合法实际符号记账列表，END_BLOCK 频率与位长树都保持不变。实际 `init_block`、这些记账操作和全部三个构造器，随后在同一个返回堆上建立相同的头部字段范围。这并没有证明策略从输入产生符号记账的状态序列，也没有证明跨块交付的保持性。

完整的实际 `send_tree` 现在会终止，并且精确输出共享游程编码模型描述的内容。直接重复循环包含最后一次有符号递减。所有重复分支、提前继续、下一个码长的读取和 for 循环的最后一次迭代，都按源码顺序执行。精确堆框架性质保持两棵树数组和已有输出前缀。实际位长构造现在为两个发送过程提供源容量、码长界，以及每个扫描频率为正的符号能够放入对应码长的码字。每个这样的码字，对任意后缀也都有独立的符号解码结果。

这些数据来自同一个返回堆：先实际执行 `init_block`，再执行任意合法的块内符号记账列表，最后执行全部三个构造器。精确的总比特空间仍是内部义务。还须完成 `send_all_trees`、独立的游程与头部解码，以及输出和符号共用存储的边界证明。单个码字可解码，并不代表完整游程序列已经可解码。

三个编码赋值变异、十一个扫描／重置／修复变异、五个堆调整／描述符变异，以及十七个合并／守卫／根存储变异，都会使相应执行证明失败。同步变体的完整源码相等性仍可独立检查。三个编码赋值变异，也会在构建目标包含完整构造器时被拒绝。

针对 `send_code` 的三个直接变异，分别改变码长表项、码字表项和发送长度；当构建目标包含完整构造与发送组合时，它们会使发送证明失败。五个扫描变异和八个位长构造变异会使各自的执行证明失败，而同步后的整函数相等性仍然通过。三个符号记账变异，分别改变字面量下标、匹配下标和缓冲区满标志；它们使执行证明失败，完整源码相等性仍然通过。

八个 `send_tree` 变异涉及重复递减、首个码字后的计数递减、零游程阈值、额外位的宽度与基数、continue 守卫、下次读取和最后迭代；它们会使执行证明失败。各变异完整且同步的源码相等性仍然通过。这些结果没有登记，也未获得 CI 批准。还须完成树描述发送、完整位成本精化、块压缩和共享存储边界，包括较小内存级别的情形。

### 其他 API

完成压缩辅助接口，以及 gz 的读取、写入和打开路径。

### 端到端声明

实例化堆 API，把状态序列不变量连接到格式模型，并在支持的配置上证明调用序列安全性、所有权、终止性和功能正确性。

### 边界情况复核

对照当前固定版本，复查 gzip 额外长度算术、部分读取后的恢复、负位置定位、参数变更丢失、结束失败后的恢复，以及 EOF 之后的向前定位。带条件的定位故障引理，不能证明状态可达；须从实际调用序列建立有符号位置与借用指针条件。

`inflateBack` 边界情况针对回调 API 的复核尚未完成；还需要该接口自身的复现，普通 inflate 的内存检查示例不足以完成这一步。在声称完整 gzip 所有权，或任意有限回调都会终止之前，还须审查外部字符串分配器和固定循环执行额度。怀疑存在缺陷，不等于可以把某种公开调用情形排除在外。

[发现记录](findings.md)保存证据和置信度；当前补丁见 [patches/README.md](../patches/README.md)。没有应用一揽子未定义行为补丁。

[架构指南](design/architecture.md#design-decisions)记录设计决策 D1–D6。[安全规格](spec/safety.md#uninitialised-memory)定义新分配内存的证明义务。
