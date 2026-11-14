<!-- source-sha256: 5186ffabe544611ff1f84385f1ebc96c07e505f293141fdad1611c4ea7a6d6ff -->
# 证明进度与剩余工作

本页集中记录证明证据和剩余工作。要了解目标陈述和证明的整体结构，请先读[总览](overview.md)。

## 范围

下列计划内目标全部通过验收时，项目即告完成。其余部分不在计划内。

**计划内。** 只证安全（所有者 2026-11-11 的决定）：两项结论，按此顺序进行，然后是它们的直接组合。安全指没有未定义行为、没有内存错误、没有泄漏，并且一定终止。计划内的安全证明所依赖的功能性事实恰好在范围内；安全不需要的功能性结论不在计划内。

| # | 结论 | 目标 |
| ---: | --- | --- |
| 1 | `inflate` 对任何输入和任意缓冲区切分都安全，也包括它的调用序列。 | `inflate`，以及 `inflate_sequence` 的安全部分 |
| 2 | `deflate` 对任何输入和任意缓冲区切分都安全，也包括它的调用序列。 | `deflateInit2_`、`deflate`、`deflate_sequence_safety` |
| 3 | 第 1、2 项在完整缓冲区上的组合。 | `compress*`、`uncompress*` 的安全 |
| 4 | 回调解码器对任何输入和任何调用者协议都安全，也包括它的调用序列（所有者 2026-11-12 的要求）。 | `inflate_back_sequence_safety` |
| 5 | gzip 文件接口在一个句柄的每条调用历史上、对每个文件系统世界都安全（所有者 2026-11-12 的决定）。只证安全，不证功能正确性。 | `gzopen`、`gzopen64`、`gzclose`、`gzclose_r`、`gzclose_w`、`gzread`、`gzfread`、`gzgetc`、`gzgetc_`、`gzungetc`、`gzgets`、`gzdirect`、`gzwrite`、`gzfwrite`、`gzputc`、`gzputs`、`gzprintf`、`gzvprintf`、`gzflush`、`gzsetparams`、`gzseek`、`gzseek64`、`gztell`、`gztell64`，经由 `gz_sequence_safety` |

上述结论在证明中需要的目标，作为依赖仍在计划内。sequence 目标所涉及的其他流调用属于这种情况，例如 `inflateSync`、`inflateCopy`、`deflateCopy`、`deflateParams`、`deflatePrime` 和 `deflateSetDictionary`。`gzvprintf` 在 zlib.h 中未文档化，但 `gzprintf` 经过它，所以它随第 5 项结论一起在计划内。

**不在计划内。** 不再为这些目标投入工作。已经登记的相关结果保留。

| 分组 | 目标 | 原因 |
| --- | --- | --- |
| gzip 文件接口的功能部分 | `gz_sequence`、`gz_initialisation_domain`，以及各 gz 调用的功能条款（读出或写入的字节、安全之外的返回值） | 功能性。这些定理依赖一个人工建立的文件系统、描述符和 `printf` 格式化模型。gz 调用的安全在计划内（第 5 项）。 |
| 未文档化函数 | `zError`、`inflateSyncPoint`、`get_crc_table`、`inflateUndermine`、`inflateValidate`、`inflateCodesUsed`、`inflateResetKeep`、`deflateResetKeep`、`gzopen_w` | zlib.h 把它们声明在 `/* undocumented functions (not part of the zlib API) */` 之下（`tests/audit/public-api.json` 的 `undocumented`）。它们不是必需的公开目标，直接调用其中之一也不是序列目标必需的操作；deflate 流定义域排除直接调用 `deflateResetKeep`（`docs/deviations.md`）。已登记的证明继续登记并接受审计。`gzvprintf` 已移入第 5 项（2026-11-12）。内部用法不变：`deflateReset` 和 `inflateReset` 经过 `ResetKeep` 引理。 |
| 回调解码器的解码部分 | `inflateBack` 与 `inflate_back_sequence` 的解码条款（交给 `out` 的内容、`Decodes`） | 功能性。回调解码器的安全在计划内（第 4 项）。 |
| 仅关于模型的陈述 | `Api.Goal.inflate_rejects_invalid`，以及未登记的 `*_refines` 目标 | 它们说的是抽象模型，不是 C 代码。前者还依赖八字节的检测延迟，而该延迟已被反例否定。对非法输入的拒绝已在第 2 项结论中针对 C 代码陈述。 |
| 其他构建配置 | 默认 x86_64 Linux 构建之外的所有配置 | 每一种配置都要针对不同的平台模型重做整个证明。结论由默认构建承载。 |
| 为查询函数增加证明变异体 | 取值函数和常量查询 | 变异体用来防止证明的设置有误。对只有一行的查询函数，它们不会为计划内的结论增加任何内容。 |
| 功能正确性 | `inflate_sequence` 的格式部分（`inflate` 的输出等于格式：`ParseMeaning` 及其流侧与解码侧），`InflateCompletes` 背后的 `DecoderFacts` 格式事实与 `uncompress*` 的格式条款，以及 deflate 的往返（`Ledger`、`ledger_*`、`completes`、`bound_before_output`、`deflate_sequence` 的解码部分） | 所有者 2026-11-11 的决定，为了更快完成。计划内的安全证明所依赖的功能性事实仍在范围内。已经证明的部分保留并列为已检查；未完成的行在[核心证明骨架](#core-proof-skeletons)中标为不在计划内。 |

不在计划内的目标不作任何声明。报告中写"不在计划内"，绝不写"已证明"。

## 目录

- [范围：计划内与不在计划内](#scope)
- [全部目标及其依赖](#proof-progress-graph)
- [确切目标的证据](#target-evidence)
- [剩余工作](#remaining-work)
  - [核心证明骨架](#core-proof-skeletons)
  - [按顺序的下一步工作](#ordered-next-work)
  - [公开 API 的前置证明义务](#public-api-proof-readiness)
  - [规格审查](#specification-review)
  - [翻译审查](#translation-review)
  - [待复核的报告](#historical-reports-to-recheck)
- [早先的检查点（历史）](history/progress-checkpoints.zh.md)

下方生成区块中的数字是唯一的当前数字。审查记录和 `docs/history/` 中的数字反映写作时的状态。

<!-- proof-progress:start -->
## 证明进度图

**共有 181 个固定目标：103 个公开目标，78 个支撑目标。**
精确覆盖相应目标的证明中，128 个已登记，0 个仅在本地检查。
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

展开组件后，再展开一个目标，即可查看它的输入范围、状态和双向依赖。[证据索引](progress.md)保留提交 `9c5be8d` 的目标与证明链接。

| 存在阻碍的目标 | 原因与下一步 |
| --- | --- |
| [gz_seek_read](./progress.md#target-zlibf-spec-api-goal-gz-seek-read) | [gzip 定位模式](./progress.md#gzip-seek-mode) |
| [inflateInit2_](./progress.md#target-zlibf-spec-public-goal-inflateinit2) | [解压初始化的清理](./progress.md#inflate-initialization-cleanup) |



## 目标证据

<!-- proof-link-revision: 9c5be8dfa641db9b804acb7587c03a0629fd4b74 -->

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
| <a id="target-zlibf-spec-public-goal-inflateinit2"></a>[inflateInit2_](../ZlibF/Spec/Public/Initialisation.lean#L90) | 未证明 / 存在阻碍 | [契约](../docs/spec/api/inflate-stream.md#inflateinit2_); [输入范围](spec/input-configurations.md#inflate-inputs) | — [Blocker: Inflate initialization cleanup](progress.md#inflate-initialization-cleanup) | — |
| <a id="target-zlibf-spec-public-goal-inflateinit"></a>[inflateInit_](../ZlibF/Spec/Public/Initialisation.lean#L95) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/inflate-stream.md#inflateinit_); [输入范围](spec/input-configurations.md#inflate-inputs) | [Zlib.Inflate.Proofs.inflate_default_init_contract](../ZlibF/Proof/inflate.c.default-entry.lean#L58); [ZlibF.Spec.Public.Proofs.InflateInit.init15_public](../ZlibF/Proof/public-inflate-init.lean#L83) | — |
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
| <a id="target-zlib-inffast-spec-bodyorigin-goal-actual-body-preserves-origin"></a>[actual_body_preserves_origin](../ZlibF/Spec/InflateFastBodyOrigin.lean#L18) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.BodyOriginProof.actual_body_preserves_origin](../ZlibF/Proof/inffast.c.body-origin.lean#L374); [Zlib.Inffast.Proofs.actual_body_preserves_origin](../ZlibF/Proof/inffast.c.body-origin.lean#L374) | — |
| <a id="target-zlib-inffast-spec-bodytoken-goal-actual-body-refines-token"></a>[actual_body_refines_token](../ZlibF/Spec/InflateFastBodyToken.lean#L73) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.BodyTokenProof.actual_body_refines_token](../ZlibF/Proof/inffast.c.body-token.lean#L564); [Zlib.Inffast.Proofs.actual_body_refines_token](../ZlibF/Proof/inffast.c.body-token.lean#L564) | — |
| <a id="target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin"></a>[actual_fast_preserves_origin](../ZlibF/Spec/InflateFastCallOrigin.lean#L24) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_fast_preserves_origin](../ZlibF/Proof/inffast.c.call-origin.lean#L176); [ZlibF.Proof.Registration.fast_call_origin](../ZlibF/Proof/proof-registrations.lean#L14) | — |
| <a id="target-zlib-inffast-spec-distanceorigin-goal-actual-distance-block-preserves-origin"></a>[actual_distance_block_preserves_origin](../ZlibF/Spec/InflateFastDistanceOrigin.lean#L18) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_distance_block_preserves_origin](../ZlibF/Proof/inffast.c.distance-origin.lean#L324) | — |
| <a id="target-zlib-inffast-spec-distanceresult-goal-actual-distance-refines-lz77"></a>[actual_distance_refines_lz77](../ZlibF/Spec/InflateFastDistanceResult.lean#L101) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_distance_refines_lz77](../ZlibF/Proof/inffast.c.distance-result.lean#L382) | — |
| <a id="target-zlib-inffast-spec-distancesemantics-goal-distance-lookup-matches-format"></a>[distance_lookup_matches_format](../ZlibF/Spec/InflateFastDistanceSemantics.lean#L20) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.distance_lookup_matches_format](../ZlibF/Proof/inffast.c.distance-semantics.lean#L22) | — |
| <a id="target-zlib-inffast-spec-goal-fast-safe"></a>[fast_safe](../ZlibF/Spec/InflateFast.lean#L68) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.inflate_fast_safe](../ZlibF/Proof/inffast.c.final.lean#L257) | — |
| <a id="target-zlib-inffast-spec-goal-step-safe"></a>[step_safe](../ZlibF/Spec/InflateFast.lean#L40) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.inflate_fast_body_step_safe](../ZlibF/Proof/inffast.c.body.lean#L315) | — |
| <a id="target-zlib-inffast-spec-lengthsemantics-goal-length-lookup-matches-format"></a>[length_lookup_matches_format](../ZlibF/Spec/InflateFastLengthSemantics.lean#L34) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.length_lookup_matches_format](../ZlibF/Proof/inffast.c.length-semantics.lean#L22) | — |
| <a id="target-zlib-inffast-spec-lengthtrace-goal-actual-body-retains-selected-length"></a>[actual_body_retains_selected_length](../ZlibF/Spec/InflateFastLengthTrace.lean#L51) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.LengthTraceProof.actual_body_retains_selected_length](../ZlibF/Proof/inffast.c.length-trace.lean#L247); [Zlib.Inffast.Proofs.actual_body_retains_selected_length](../ZlibF/Proof/inffast.c.length-trace.lean#L247) | — |
| <a id="target-zlib-inffast-spec-matchhistory-goal-actual-copy-match-refines-lz77"></a>[actual_copy_match_refines_lz77](../ZlibF/Spec/InflateFastMatchHistory.lean#L39) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_copy_match_refines_lz77](../ZlibF/Proof/inffast.c.match-history.lean#L329) | — |
| <a id="target-zlib-inffast-spec-matchhistory-goal-match-array-refines-lz77"></a>[match_array_refines_lz77](../ZlibF/Spec/InflateFastMatchHistory.lean#L25) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.fast_match_array_refines_lz77](../ZlibF/Math/InflateFastMatchHistory.lean#L56) | — |
| <a id="target-zlib-inffast-spec-origin-goal-actual-drop-preserves-origin"></a>[actual_drop_preserves_origin](../ZlibF/Spec/InflateFastOrigin.lean#L68) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_drop_preserves_origin](../ZlibF/Proof/inffast.c.origin.lean#L138) | — |
| <a id="target-zlib-inffast-spec-origin-goal-actual-pull-preserves-origin"></a>[actual_pull_preserves_origin](../ZlibF/Spec/InflateFastOrigin.lean#L57) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_pull_preserves_origin](../ZlibF/Proof/inffast.c.origin.lean#L127) | — |
| <a id="target-zlib-inffast-spec-origin-goal-actual-rollback-preserves-origin"></a>[actual_rollback_preserves_origin](../ZlibF/Spec/InflateFastOrigin.lean#L81) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_rollback_preserves_origin](../ZlibF/Proof/inffast.c.origin.lean#L150) | — |
| <a id="target-zlib-inffast-spec-origin-goal-drop-preserves-origin"></a>[drop_preserves_origin](../ZlibF/Spec/InflateFastOrigin.lean#L38) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.drop_preserves_origin](../ZlibF/Proof/inffast.c.origin.lean#L41) | — |
| <a id="target-zlib-inffast-spec-origin-goal-initial-origin"></a>[initial_origin](../ZlibF/Spec/InflateFastOrigin.lean#L27) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.initial_origin](../ZlibF/Proof/inffast.c.origin.lean#L16) | — |
| <a id="target-zlib-inffast-spec-origin-goal-pull-preserves-origin"></a>[pull_preserves_origin](../ZlibF/Spec/InflateFastOrigin.lean#L32) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.pull_preserves_origin](../ZlibF/Proof/inffast.c.origin.lean#L21) | — |
| <a id="target-zlib-inffast-spec-origin-goal-rollback-preserves-origin"></a>[rollback_preserves_origin](../ZlibF/Spec/InflateFastOrigin.lean#L46) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.rollback_preserves_origin](../ZlibF/Proof/inffast.c.origin.lean#L83) | — |

<a id="group-tables"></a>

## 解码表的证明义务

| 目标陈述 | 覆盖范围／证据状态 | 契约／输入范围 | 证明证据 | 已审查的后续工作 |
| --- | --- | --- | --- | --- |
| <a id="target-zlib-inftrees-spec-decoderejection-goal-decode-table-classifies-input"></a>[decode_table_classifies_input](../ZlibF/Spec/InflateDecodeTableRejection.lean#L19) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.decode_table_classifies_input](../ZlibF/Proof/inftrees.c.decode.short.lean#L62) | — |
| <a id="target-zlib-inftrees-spec-decodesemantics-goal-decode-table-matches-format"></a>[decode_table_matches_format](../ZlibF/Spec/InflateDecodeTableSemantics.lean#L51) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.decode_table_matches_format](../ZlibF/Proof/inftrees.c.decode.semantics.lean#L327) | — |
| <a id="target-zlib-inftrees-spec-decodeshort-goal-short-decode-table-leaf-sound"></a>[short_decode_table_leaf_sound](../ZlibF/Spec/InflateDecodeTableShort.lean#L26) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.short_decode_table_leaf_sound](../ZlibF/Proof/inftrees.c.decode.short.lean#L33) | — |
| <a id="target-zlib-inftrees-spec-decodesoundness-goal-decode-table-leaf-sound"></a>[decode_table_leaf_sound](../ZlibF/Spec/InflateDecodeTableSoundness.lean#L31) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.decode_table_leaf_sound](../ZlibF/Proof/inftrees.c.decode.soundness.lean#L244) | — |
| <a id="target-zlib-inftrees-spec-decodetableframe-goal-decode-table-read-preserved"></a>[decode_table_read_preserved](../ZlibF/Spec/InflateDecodeTableFrame.lean#L20) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.decode_table_read_preserved](../ZlibF/Proof/inftrees.c.decode.frame.lean#L55) | — |
| <a id="target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant"></a>[constructor_establishes_decode_table_invariant](../ZlibF/Spec/InflateDecodeTableInvariant.lean#L51) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.constructor_establishes_decode_table_invariant](../ZlibF/Proof/inftrees.c.decode.invariant.lean#L13) | — |
| <a id="target-zlib-inftrees-spec-decodetableinvariant-goal-decode-table-invariant-of-prefix"></a>[decode_table_invariant_of_prefix](../ZlibF/Spec/InflateDecodeTableInvariant.lean#L68) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.decode_table_invariant_of_prefix](../ZlibF/Proof/inftrees.c.decode.invariant-prefix.lean#L22) | — |
| <a id="target-zlib-inftrees-spec-decodetablestability-goal-constructor-establishes-query-stability"></a>[constructor_establishes_query_stability](../ZlibF/Spec/InflateDecodeTableStability.lean#L30) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.constructor_establishes_query_stability](../ZlibF/Proof/inftrees.c.decode.stability.lean#L190) | — |
| <a id="target-zlib-inftrees-spec-decodetablestability-goal-query-stability-of-prefix"></a>[query_stability_of_prefix](../ZlibF/Spec/InflateDecodeTableStability.lean#L43) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.query_stability_of_prefix](../ZlibF/Proof/inftrees.c.decode.stability-rejection.lean#L20) | — |
| <a id="target-zlib-inftrees-spec-decodetablestability-goal-short-rejected-leaf-stays-invalid"></a>[short_rejected_leaf_stays_invalid](../ZlibF/Spec/InflateDecodeTableStability.lean#L54) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.short_rejected_leaf_stays_invalid](../ZlibF/Proof/inftrees.c.decode.stability-rejection.lean#L31) | — |
| <a id="target-zlib-inftrees-spec-fasttableflags-goal-constructor-establishes-fast-leaf-flags"></a>[constructor_establishes_fast_leaf_flags](../ZlibF/Spec/InflateFastTableFlags.lean#L52) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.constructor_establishes_fast_leaf_flags](../ZlibF/Proof/inftrees.c.decode.fast-flags.lean#L125) | — |
| <a id="target-zlib-inftrees-spec-fasttableflags-goal-fast-leaf-flags-of-prefix"></a>[fast_leaf_flags_of_prefix](../ZlibF/Spec/InflateFastTableFlags.lean#L66) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.fast_leaf_flags_of_prefix](../ZlibF/Proof/inftrees.c.decode.fast-flags-frame.lean#L48); [ZlibF.Proof.Registration.fast_leaf_flags_of_prefix](../ZlibF/Proof/proof-registrations.lean#L20) | — |
| <a id="target-zlib-inftrees-spec-fasttableflags-goal-fixed-tables-have-fast-leaf-flags"></a>[fixed_tables_have_fast_leaf_flags](../ZlibF/Spec/InflateFastTableFlags.lean#L76) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.fixed_tables_have_fast_leaf_flags](../ZlibF/Proof/inffixed.h.fast-flags.lean#L55); [ZlibF.Proof.Registration.fixed_tables_fast_leaf_flags](../ZlibF/Proof/proof-registrations.lean#L26) | — |
| <a id="target-zlib-inftrees-spec-fasttableflags-goal-leaf-classification-agrees"></a>[leaf_classification_agrees](../ZlibF/Spec/InflateFastTableFlags.lean#L42) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.leaf_classification_agrees](../ZlibF/Proof/inftrees.c.decode.fast-flags-frame.lean#L9); [ZlibF.Proof.Registration.leaf_classification_agrees](../ZlibF/Proof/proof-registrations.lean#L32) | — |
| <a id="target-zlib-inftrees-spec-goal-inflate-table-content"></a>[inflate_table_content](../ZlibF/Spec/InflateTableContent.lean#L32) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.inflate_table_content](../ZlibF/Proof/inftrees.c.content.lean#L327) | — |
| <a id="target-zlib-inftrees-spec-goal-inflate-table-decoder-safe"></a>[inflate_table_decoder_safe](../ZlibF/Spec/InflateTableSafety.lean#L28) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.inflate_table_decoder_safe](../ZlibF/Proof/inftrees.c.decoder-safe.lean#L93) | — |
| <a id="target-zlib-inftrees-spec-goal-inflate-table-read-extent"></a>[inflate_table_read_extent](../ZlibF/Spec/InflateTableExtent.lean#L28) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.inflate_table_read_extent](../ZlibF/Proof/inftrees.c.read-extent.lean#L139) | — |
| <a id="target-zlib-inftrees-spec-roottable-goal-constructor-root-bits"></a>[constructor_root_bits](../ZlibF/Spec/InflateRootTable.lean#L21) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.constructor_root_bits](../ZlibF/Proof/inftrees.c.decode.bits.lean#L260) | — |
| <a id="target-zlib-inftrees-spec-subtable-goal-constructor-subtable-bits"></a>[constructor_subtable_bits](../ZlibF/Spec/InflateSubtable.lean#L26) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.constructor_subtable_bits](../ZlibF/Proof/inftrees.c.decode.bits.lean#L221) | — |

<a id="group-copy"></a>

## 回引用复制

| 目标陈述 | 覆盖范围／证据状态 | 契约／输入范围 | 证明证据 | 已审查的后续工作 |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-math-lz77copy-goal-output-copy-refines-lz77"></a>[output_copy_refines_lz77](../ZlibF/Math/LZ77CopySpec.lean#L22) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Math.LZ77Copy.output_copy_refines_lz77](../ZlibF/Math/LZ77Copy.lean#L65) | — |
| <a id="target-zlibf-math-lz77copy-goal-window-copy-refines-lz77"></a>[window_copy_refines_lz77](../ZlibF/Math/LZ77CopySpec.lean#L32) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Math.LZ77Copy.window_copy_refines_lz77](../ZlibF/Math/LZ77Copy.lean#L124) | — |
| <a id="target-zlibf-math-lz77history-goal-copy-back-compose"></a>[copy_back_compose](../ZlibF/Math/LZ77HistorySpec.lean#L21) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Math.LZ77History.copy_back_compose](../ZlibF/Math/LZ77History.lean#L31) | — |
| <a id="target-zlibf-math-lz77history-goal-copy-back-extends-history"></a>[copy_back_extends_history](../ZlibF/Math/LZ77HistorySpec.lean#L15) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Math.LZ77History.copy_back_extends_history](../ZlibF/Math/LZ77History.lean#L17) | — |
| <a id="target-zlibf-math-lz77history-goal-retained-history-agrees"></a>[retained_history_agrees](../ZlibF/Math/LZ77HistorySpec.lean#L29) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Math.LZ77History.retained_history_agrees](../ZlibF/Math/LZ77History.lean#L59) | — |
| <a id="target-zlibf-math-lz77history-goal-window-distance-check-agrees"></a>[window_distance_check_agrees](../ZlibF/Math/LZ77HistorySpec.lean#L39) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Math.LZ77History.window_distance_check_agrees](../ZlibF/Math/LZ77History.lean#L72) | — |

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
| <a id="target-zlibf-spec-public-goal-gzerror"></a>[gzerror](../ZlibF/Spec/Public/GzControl.lean#L63) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/gz-file.md#gzerror); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzErrorProof.gzerror](../ZlibF/Proof/public-gz-error.lean#L206) | — |
| <a id="target-zlibf-spec-public-goal-gzclearerr"></a>[gzclearerr](../ZlibF/Spec/Public/GzControl.lean#L74) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/gz-file.md#gzclearerr); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.gzclearerr](../ZlibF/Proof/gzlib.c.public-clearerr.lean#L28) | — |
| <a id="target-zlibf-spec-public-goal-gzrewind"></a>[gzrewind](../ZlibF/Spec/Public/GzControl.lean#L91) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/gz-file.md#gzrewind); [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzRewindProof.rewind_public](../ZlibF/Proof/public-gz-rewind.lean#L67) | — |
| <a id="target-zlibf-spec-public-goal-gzseek64"></a>[gzseek64](../ZlibF/Spec/Public/GzControl.lean#L116) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzseek64); [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：定位与状态序列证明](progress.md#readiness-gzseek64) |
| <a id="target-zlibf-spec-public-goal-gzseek"></a>[gzseek](../ZlibF/Spec/Public/GzControl.lean#L119) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzseek); [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：定位与状态序列证明](progress.md#readiness-gzseek64) |
| <a id="target-zlibf-spec-public-goal-gzopen"></a>[gzopen](../ZlibF/Spec/Public/GzOpen.lean#L61) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzopen); [输入范围](spec/input-configurations.md#entry-inputs) | — | [起点：打开与清理](progress.md#readiness-gzopen) |
| <a id="target-zlibf-spec-public-goal-gzopen64"></a>[gzopen64](../ZlibF/Spec/Public/GzOpen.lean#L65) | 未证明 / 未证明 | [契约](../docs/spec/api/gz-file.md#gzopen64); [输入范围](spec/input-configurations.md#entry-inputs) | — | [起点：打开与清理](progress.md#readiness-gzopen) |
| <a id="target-zlibf-spec-public-goal-gzdopen"></a>[gzdopen](../ZlibF/Spec/Public/GzOpen.lean#L70) | 陈述所允许的全部输入 / 已登记证明 | [契约](../docs/spec/api/gz-file.md#gzdopen); [输入范围](spec/input-configurations.md#entry-inputs) | [Zlib.Gzlib.Proofs.gzdopen_complete](../ZlibF/Proof/gzlib.c.dopen-complete.lean#L28) | — |
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
| <a id="target-zlibf-spec-public-goal-compress2-z"></a>[compress2_z](../ZlibF/Spec/Public/Utilities.lean#L44) | 未证明 / 未证明 | [契约](../docs/spec/api/utility.md#compress2_z); [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：压缩器执行证明](progress.md#readiness-compress2-z) |
| <a id="target-zlibf-spec-public-goal-compress2"></a>[compress2](../ZlibF/Spec/Public/Utilities.lean#L49) | 未证明 / 未证明 | [契约](../docs/spec/api/utility.md#compress2); [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：压缩器执行证明](progress.md#readiness-compress2-z) |
| <a id="target-zlibf-spec-public-goal-compress-z"></a>[compress_z](../ZlibF/Spec/Public/Utilities.lean#L56) | 未证明 / 未证明 | [契约](../docs/spec/api/utility.md#compress_z); [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：压缩器执行证明](progress.md#readiness-compress2-z) |
| <a id="target-zlibf-spec-public-goal-compress"></a>[compress](../ZlibF/Spec/Public/Utilities.lean#L61) | 未证明 / 未证明 | [契约](../docs/spec/api/utility.md#compress); [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：压缩器执行证明](progress.md#readiness-compress2-z) |
| <a id="target-zlibf-spec-public-goal-uncompress2-z"></a>[uncompress2_z](../ZlibF/Spec/Public/Utilities.lean#L108) | 未证明 / 未证明 | [契约](../docs/spec/api/utility.md#uncompress2_z); [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：解码器执行证明](progress.md#readiness-uncompress2-z) |
| <a id="target-zlibf-spec-public-goal-uncompress2"></a>[uncompress2](../ZlibF/Spec/Public/Utilities.lean#L112) | 未证明 / 未证明 | [契约](../docs/spec/api/utility.md#uncompress2); [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：解码器执行证明](progress.md#readiness-uncompress2-z) |
| <a id="target-zlibf-spec-public-goal-uncompress-z"></a>[uncompress_z](../ZlibF/Spec/Public/Utilities.lean#L139) | 未证明 / 未证明 | [契约](../docs/spec/api/utility.md#uncompress_z); [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：解码器执行证明](progress.md#readiness-uncompress2-z) |
| <a id="target-zlibf-spec-public-goal-uncompress"></a>[uncompress](../ZlibF/Spec/Public/Utilities.lean#L143) | 未证明 / 未证明 | [契约](../docs/spec/api/utility.md#uncompress); [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：解码器执行证明](progress.md#readiness-uncompress2-z) |

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
| <a id="target-zlibf-spec-api-goal-dict-roundtrip"></a>[dict_roundtrip](../ZlibF/Spec/Api/Goals.lean#L162) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.dict_roundtrip](../ZlibF/Proof/Api/DictionaryRoundtrip.lean#L121) | — |
| <a id="target-zlibf-spec-api-goal-header-roundtrip"></a>[header_roundtrip](../ZlibF/Spec/Api/Goals.lean#L180) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.header_roundtrip](../ZlibF/Proof/Api/HeaderRoundtrip.lean#L89) | — |
| <a id="target-zlibf-spec-api-goal-deflate-bound-adequate"></a>[deflate_bound_adequate](../ZlibF/Spec/Api/Goals.lean#L189) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.deflate_bound_adequate](../ZlibF/Proof/Api/DeflateBounds.lean#L103) | — |
| <a id="target-zlibf-spec-api-goal-compress-bound-adequate"></a>[compress_bound_adequate](../ZlibF/Spec/Api/Goals.lean#L196) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.compress_bound_adequate](../ZlibF/Proof/Api/Compress.lean#L8) | — |
| <a id="target-zlibf-spec-api-goal-compress-roundtrip"></a>[compress_roundtrip](../ZlibF/Spec/Api/Goals.lean#L203) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.compress_roundtrip](../ZlibF/Proof/Api/CompressRoundtrip.lean#L32) | — |
| <a id="target-zlibf-spec-api-goal-gz-roundtrip"></a>[gz_roundtrip](../ZlibF/Spec/Api/Goals.lean#L214) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.gz_roundtrip](../ZlibF/Proof/Api/GzRoundtrip.lean#L15) | — |
| <a id="target-zlibf-spec-api-goal-gz-seek-read"></a>[gz_seek_read](../ZlibF/Spec/Api/Goals.lean#L221) | 未证明 / 存在阻碍 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | — [Blocker: Gzip seek mode](progress.md#gzip-seek-mode) | — |
| <a id="target-zlibf-spec-api-goal-compress-bound-value"></a>[compress_bound_value](../ZlibF/Spec/Api/Concrete.lean#L57) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.compress_bound_value](../ZlibF/Proof/Api/Concrete.lean#L57) | — |
| <a id="target-zlibf-spec-api-goal-compress2-z-first-alloc-failure"></a>[compress2_z_first_alloc_failure](../ZlibF/Spec/Api/Concrete.lean#L67) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.compress2_z_first_alloc_failure](../ZlibF/Proof/Api/CompressFailure.lean#L29) | — |
| <a id="target-zlibf-spec-api-goal-inflate-deferred-distance"></a>[inflate_deferred_distance](../ZlibF/Spec/Api/Inflate.lean#L267) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.inflate_deferred_distance](../ZlibF/Proof/Api/InflateCausality.lean#L244) | — |

<a id="group-lifecycle"></a>

## 生命周期与调用序列

| 目标陈述 | 覆盖范围／证据状态 | 契约／输入范围 | 证明证据 | 已审查的后续工作 |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-inflate-sequence"></a>[inflate_sequence](../ZlibF/Spec/Public/Sequences.lean#L211) | 未证明 / 未证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#inflate-inputs) | — | [所需：执行与格式证明](progress.md#readiness-inflate-sequence) |
| <a id="target-zlibf-spec-public-goal-deflate-sequence"></a>[deflate_sequence](../ZlibF/Spec/Public/Sequences.lean#L225) | 未证明 / 未证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#deflate-inputs) | — | [所需：执行与格式证明](progress.md#readiness-inflate-sequence) |
| <a id="target-zlibf-spec-public-goal-inflate-back-sequence"></a>[inflate_back_sequence](../ZlibF/Spec/Public/Sequences.lean#L252) | 未证明 / 未证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：执行与格式证明](progress.md#readiness-inflate-sequence) |
| <a id="target-zlibf-spec-public-goal-gz-sequence"></a>[gz_sequence](../ZlibF/Spec/Public/Sequences.lean#L264) | 未证明 / 未证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | — | [所需：执行与格式证明](progress.md#readiness-inflate-sequence) |
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
| <a id="target-zlibf-spec-token-goal-rejected-has-no-symbols"></a>[rejected_has_no_symbols](../ZlibF/Spec/Format/Token.lean#L84) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Token.rejected_has_no_symbols](../ZlibF/Proof/Format/Token.lean#L49) | — |
| <a id="target-zlibf-spec-token-goal-step-composes-symbols"></a>[step_composes_symbols](../ZlibF/Spec/Format/Token.lean#L62) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Token.step_composes_symbols](../ZlibF/Proof/Format/Token.lean#L15) | — |
| <a id="target-zlibf-spec-token-goal-symbols-exposes-step"></a>[symbols_exposes_step](../ZlibF/Spec/Format/Token.lean#L73) | 陈述所允许的全部输入 / 已登记证明 | 确切目标陈述; [输入范围](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Token.symbols_exposes_step](../ZlibF/Proof/Format/Token.lean#L35) | — |

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
| API 模型引理 | compress_bound_adequate, compress_roundtrip, deflate_bound_adequate, deflate_completes, deflate_full_flush_resync, deflate_valid, dict_roundtrip, gz_roundtrip, header_roundtrip, inflate_completes, inflate_decodes, inflate_deferred_distance, roundtrip, roundtrip_completes, deflateInit_, gzdopen, API 模型证明, deflate 状态构造证明, gzlib.c 的证明, 不涉及堆的数学证明 |
| ByteAddress 字节地址模型证明 | first_aligned_offset, mask_refines_base_plus_offset, pointer_advance_preserves_low_bits |
| LibcBorrow 证明 | inflate 存储与读位证明 |
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
| deflate 窗口与匹配证明 | deflate 生命周期证明, gzlib.c 的证明, inflate 存储与读位证明 |
| 格式证明 | short_decode_table_leaf_sound, short_rejected_leaf_stays_invalid, compress_roundtrip, format_deterministic, format_prefix_free, header_roundtrip, inflate_completes, rejected_has_no_symbols, API 模型证明, 不涉及堆的数学证明, inffast.c 的证明, inftrees.c 的证明 |
| gzfs 的证明 | gzlib.c 的证明 |
| gzlib.c 的证明 | gzclearerr, gzdopen, 公开入口组合证明 |
| 不涉及堆的数学证明 | match_array_refines_lz77, output_copy_refines_lz77, window_copy_refines_lz77, copy_back_compose, retained_history_agrees, window_distance_check_agrees, API 模型证明, gzlib.c 的证明, inftrees.c 的证明 |
| infback.c 的证明 | inflateBackEnd, inflateBackInit_, 公开入口组合证明 |
| inffast.c 的证明 | actual_body_preserves_origin, actual_body_refines_token, actual_fast_preserves_origin, actual_distance_block_preserves_origin, actual_distance_refines_lz77, distance_lookup_matches_format, fast_safe, step_safe, length_lookup_matches_format, actual_body_retains_selected_length, actual_copy_match_refines_lz77, match_array_refines_lz77, actual_drop_preserves_origin, actual_pull_preserves_origin, actual_rollback_preserves_origin, drop_preserves_origin, initial_origin, pull_preserves_origin, rollback_preserves_origin, output_copy_refines_lz77, 不涉及堆的数学证明, inftrees.c 的证明 |
| inffixed.h.fast-flags 的证明 | fixed_tables_have_fast_leaf_flags |
| inflate 入口组合证明 | inflateEnd, inflateGetDictionary, inflateGetHeader, inflateInit_, inflateMark, inflatePrime, inflateReset, inflateReset2, inflateSetDictionary, inflateSyncPoint, inflateUndermine, inflateValidate, inflate_initialisation_domain |
| inflate 存储与读位证明 | deflateReset, deflateResetKeep, inflateBackEnd, inflateBackInit_, inflateEnd, inflateGetDictionary, inflateInit_, inflateMark, inflateReset, inflateReset2, inflateResetKeep, inflateSetDictionary, inflateSyncPoint, inflateUndermine, inflateValidate, API 模型证明, infback.c 的证明, inflate 入口组合证明, 公开入口组合证明 |
| inftrees.c 的证明 | decode_table_matches_format, short_decode_table_leaf_sound, decode_table_leaf_sound, decode_table_read_preserved, constructor_establishes_decode_table_invariant, decode_table_invariant_of_prefix, constructor_establishes_query_stability, short_rejected_leaf_stays_invalid, constructor_establishes_fast_leaf_flags, leaf_classification_agrees, inflate_table_content, inflate_table_decoder_safe, inflate_table_read_extent, constructor_root_bits, constructor_subtable_bits, 不涉及堆的数学证明 |
| 公开入口组合证明 | adler32_combine, adler32_combine64, adler32_z, compressBound, compressBound_z, crc32_combine, crc32_combine64, crc32_combine_gen, crc32_combine_gen64, crc32_combine_op, get_crc_table, gzbuffer, gzdopen, gzeof, gzerror, gzoffset, gzoffset64, gzrewind, inflateBackEnd, inflateBackInit_, inflate_back_initialisation_domain, zError, zlibVersion, adler32.c 的证明, gzlib.c 的证明 |
| 运行时对象与算术引理 | byte_modifies_preserve_bases, byte_stores_preserve_bases, every_layout_is_representable, LibcBorrow 证明, crc32_all_byte_views, crc32_z_all_byte_views, actual_body_preserves_origin, actual_body_refines_token, actual_fast_preserves_origin, actual_distance_block_preserves_origin, actual_distance_refines_lz77, fast_safe, step_safe, actual_body_retains_selected_length, actual_copy_match_refines_lz77, actual_pull_preserves_origin, actual_rollback_preserves_origin, decode_table_classifies_input, decode_table_matches_format, short_decode_table_leaf_sound, decode_table_leaf_sound, constructor_establishes_decode_table_invariant, constructor_establishes_query_stability, constructor_establishes_fast_leaf_flags, inflate_table_content, inflate_table_decoder_safe, inflate_table_read_extent, constructor_root_bits, constructor_subtable_bits, compress2_z_first_alloc_failure, adler32, adler32_z, crc32, crc32_z, deflateEnd, deflateGetDictionary, deflateInit_, deflatePending, deflateReset, deflateResetKeep, deflateSetHeader, deflateTune, deflateUsed, get_crc_table, gzclearerr, gzdopen, gzerror, gzoffset, gzoffset64, gzrewind, inflateBackEnd, inflateBackInit_, inflateCodesUsed, inflateEnd, inflateGetDictionary, inflateGetHeader, inflateInit_, inflateMark, inflatePrime, inflateReset, inflateReset2, inflateResetKeep, inflateSetDictionary, inflateSyncPoint, inflateUndermine, inflateValidate, inflate_back_initialisation_domain, inflate_initialisation_domain, zError, zlibVersion, adler32.c 的证明, API 模型证明, crc32.c 的证明, deflate 状态构造证明, deflate 入口组合证明, deflate 生命周期证明, deflate 窗口与匹配证明, gzfs proofs, gzlib.c 的证明, infback.c 的证明, inffast.c 的证明, inflate 入口组合证明, inflate 存储与读位证明, inftrees.c 的证明, 公开入口组合证明, 编码树构造与输出证明, zutil.c 的证明 |
| 规格引理 | every_existing_heap_accepts_layout, actual_body_refines_token, distance_lookup_matches_format, length_lookup_matches_format, actual_body_retains_selected_length, drop_preserves_origin, pull_preserves_origin, rollback_preserves_origin, decode_table_invariant_of_prefix, short_rejected_leaf_stays_invalid, gzdopen, gzlib.c 的证明, inffast.c 的证明 |
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
| [Zlib.Deflate.Engine.Proofs.CommonInitializedDataTrace.cleanup](../ZlibF/Proof/deflate.c.engine.common-initialized-history-environment.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.CommonInitializedDataTrace.completed](../ZlibF/Proof/deflate.c.engine.common-initialized-data-history.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.CommonInitializedDataTrace.completes](../ZlibF/Proof/deflate.c.engine.common-initialized-history-completes.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.CommonInitializedDataTrace.completes_post](../ZlibF/Proof/deflate.c.engine.common-initialized-history-completes.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.CommonInitializedDataTrace.encoding](../ZlibF/Proof/deflate.c.engine.common-initialized-data-history.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.CommonInitializedDataTrace.environment](../ZlibF/Proof/deflate.c.engine.common-initialized-history-environment.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.CommonInitializedDataTrace.finish_continuation](../ZlibF/Proof/deflate.c.engine.common-initialized-history-completes.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.CommonInitializedEncodingState.ordinary_encoding_request](../ZlibF/Proof/deflate.c.engine.common-initialized-request.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.CommonNoFlushDataTrace.cleanup](../ZlibF/Proof/deflate.c.engine.common-no-flush-history-environment.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.CommonNoFlushDataTrace.completed](../ZlibF/Proof/deflate.c.engine.common-no-flush-data-history.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.CommonNoFlushDataTrace.completes](../ZlibF/Proof/deflate.c.engine.common-no-flush-history-completes.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.CommonNoFlushDataTrace.encoding](../ZlibF/Proof/deflate.c.engine.common-no-flush-data-history.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.CommonNoFlushDataTrace.environment](../ZlibF/Proof/deflate.c.engine.common-no-flush-history-environment.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.CommonNoFlushDataTrace.finish_continuation](../ZlibF/Proof/deflate.c.engine.common-no-flush-history-completes.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.CommonOrdinaryDataTrace.cleanup](../ZlibF/Proof/deflate.c.engine.common-ordinary-history-environment.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.CommonOrdinaryDataTrace.completed](../ZlibF/Proof/deflate.c.engine.common-ordinary-data-history.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.CommonOrdinaryDataTrace.completes](../ZlibF/Proof/deflate.c.engine.common-ordinary-history-completes.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.CommonOrdinaryDataTrace.encoding](../ZlibF/Proof/deflate.c.engine.common-ordinary-data-history.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.CommonOrdinaryDataTrace.environment](../ZlibF/Proof/deflate.c.engine.common-ordinary-history-environment.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.CommonOrdinaryDataTrace.finish_continuation](../ZlibF/Proof/deflate.c.engine.common-ordinary-history-completes.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.DefaultEncodingState.generic_basic_full_request](../ZlibF/Proof/deflate.c.engine.generic-basic-full-contract.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.DefaultFinishBoundary.follow_finish_continuation_end_status](../ZlibF/Proof/deflate.c.engine.generic-continuation-end-status.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.GenericDefaultRequestTrace.completes_with_original_birth_cleanup](../ZlibF/Proof/deflate.c.engine.generic-completion-lifetime.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.GenericDefaultRequestTrace.full_next_request_contract](../ZlibF/Proof/deflate.c.engine.generic-basic-history-full-contract.lean) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.INSERT_STRING_ok](../ZlibF/Proof/deflate.c.engine.macros.lean#L177) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.UPDATE_HASH_ok](../ZlibF/Proof/deflate.c.engine.macros.lean#L147) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.chain_ok_of_chains](../ZlibF/Proof/deflate.c.engine.chains.lean#L194) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.chains_insert](../ZlibF/Proof/deflate.c.engine.chains.lean#L76) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.chains_slide](../ZlibF/Proof/deflate.c.engine.chains.lean#L138) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.common_initialized_level_four_complete_witness](../ZlibF/Proof/deflate.c.engine.common-initialized-data-history.lean#L93) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.common_no_flush_level_four_complete_witness](../ZlibF/Proof/deflate.c.engine.common-no-flush-history-witness.lean#L41) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.common_observed_initialization_encoding_state](../ZlibF/Proof/deflate.c.engine.common-initialized-state-init.lean#L15) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.common_observed_initialization_first_ordinary_encoding](../ZlibF/Proof/deflate.c.engine.common-initial-first-ordinary-encoding.lean#L15) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.common_observed_initialization_no_flush_encoding](../ZlibF/Proof/deflate.c.engine.common-initial-no-flush-encoding.lean#L14) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.common_ordinary_level_four_complete_witness](../ZlibF/Proof/deflate.c.engine.common-ordinary-history-witness.lean#L50) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.default_init_all_scalar_full_request_contract](../ZlibF/Proof/deflate.c.engine.all-scalar-full-contract.lean#L14) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.default_public_full_contract_witness](../ZlibF/Proof/deflate.c.engine.full-contract-witness.lean#L15) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.fill_fit](../ZlibF/Proof/deflate.c.engine.window.lean#L45) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.fill_post_room](../ZlibF/Proof/deflate.c.engine.window.lean#L40) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.form_init](../ZlibF/Proof/deflate.c.engine.hash.lean#L126) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.generic_default_public_contract](../ZlibF/Proof/deflate.c.default-public-contract.lean#L19) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.generic_default_request_trace_witness](../ZlibF/Proof/deflate.c.default-public-contract.lean#L62) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.hkey_third](../ZlibF/Proof/deflate.c.engine.hash.lean#L139) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.lm_body_ok](../ZlibF/Proof/deflate.c.engine.lmbody.lean#L102) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.lm_inner_loop](../ZlibF/Proof/deflate.c.engine.lminner.lean#L36) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.lm_loop_ok](../ZlibF/Proof/deflate.c.engine.lmmain.lean#L77) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.longest_match_ok](../ZlibF/Proof/deflate.c.engine.lmmain.lean#L212) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.matchLen_agree](../ZlibF/Proof/deflate.c.engine.match.lean#L100) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.memory_fast_initialization_witness](../ZlibF/Proof/deflate.c.engine.memory-fast-initial.lean#L50) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.memory_fast_observed_initialization](../ZlibF/Proof/deflate.c.engine.memory-fast-observed-initial.lean#L49) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.memory_slow_initialized_state](../ZlibF/Proof/deflate.c.engine.memory-slow-initialized-state.lean#L62) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.memory_slow_observed_initialization](../ZlibF/Proof/deflate.c.engine.memory-slow-observed-initial.lean#L55) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.public_common_first_finish_encoding_input](../ZlibF/Proof/deflate.c.engine.common-first-finish-encoding.lean#L16) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.public_common_first_finish_encoding_state](../ZlibF/Proof/deflate.c.engine.common-first-finish-state.lean#L15) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.public_common_first_no_flush_encoding_input](../ZlibF/Proof/deflate.c.engine.common-first-input.lean#L16) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.public_common_first_no_flush_encoding_state](../ZlibF/Proof/deflate.c.engine.common-first-encoding-state.lean#L14) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.putShortMSB_ok](../ZlibF/Proof/deflate.c.engine.macros.lean#L119) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.put_byte_ok](../ZlibF/Proof/deflate.c.engine.macros.lean#L96) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.read_buf_ok](../ZlibF/Proof/deflate.c.engine.readbuf.lean#L99) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.read_buf_zero](../ZlibF/Proof/deflate.c.engine.readbuf.lean#L75) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.slide_copy](../ZlibF/Proof/deflate.c.engine.window.lean#L52) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.slide_hash_ok](../ZlibF/Proof/deflate.c.engine.slide.lean#L166) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Engine.Proofs.upd3_indep](../ZlibF/Proof/deflate.c.engine.hash.lean#L45) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Proofs.MemoryInit.public_valid_memory_init_lifecycle](../ZlibF/Proof/deflate.c.init.memory-lifecycle.lean#L13) | 未记录到固定目标的组合关系 |
| [Zlib.Deflate.Proofs.MemoryInit.public_valid_memory_init_total](../ZlibF/Proof/deflate.c.init.memory-total.lean#L16) | 未记录到固定目标的组合关系 |
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
| [Zlib.Gzlib.Proofs.gz_open_alloc_failure](../ZlibF/Proof/gzlib.c.open.lean#L35) | [gzdopen](#target-zlibf-spec-public-goal-gzdopen) |
| [Zlib.Gzlib.Proofs.gz_open_null](../ZlibF/Proof/gzlib.c.open.lean#L17) | [gzdopen](#target-zlibf-spec-public-goal-gzdopen) |
| [Zlib.Gzlib.Proofs.gz_reset_run](../ZlibF/Proof/gzlib.c.error.lean#L145) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gz_reset_safe](../ZlibF/Proof/gzlib.c.error.lean#L168) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzbuffer_null](../ZlibF/Proof/gzlib.c.simple.lean#L52) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzbuffer_run](../ZlibF/Proof/gzlib.c.simple.lean#L67) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzbuffer_safe](../ZlibF/Proof/gzlib.c.simple.lean#L84) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzclearerr_null](../ZlibF/Proof/gzlib.c.simple.lean#L191) | [gzclearerr](#target-zlibf-spec-public-goal-gzclearerr) |
| [Zlib.Gzlib.Proofs.gzclearerr_run](../ZlibF/Proof/gzlib.c.simple.lean#L199) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzclearerr_safe](../ZlibF/Proof/gzlib.c.simple.lean#L210) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzdopen_alloc_failure](../ZlibF/Proof/gzlib.c.open.lean#L61) | [gzdopen](#target-zlibf-spec-public-goal-gzdopen) |
| [Zlib.Gzlib.Proofs.gzdopen_joint_witness](../ZlibF/Proof/gzlib.c.dopen-joint-witness.lean#L92) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzdopen_negative](../ZlibF/Proof/gzlib.c.open.lean#L54) | [gzdopen](#target-zlibf-spec-public-goal-gzdopen) |
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
| [Zlib.Gzlib.Proofs.gzseek64_head_any](../ZlibF/Proof/gzlib.c.seek.lean#L189) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzseek64_dangling_next_ok](../ZlibF/Proof/gzlib.c.seek.lean#L1010) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzseek64_head](../ZlibF/Proof/gzlib.c.seek.lean#L177) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzseek64_null](../ZlibF/Proof/gzlib.c.seek.lean#L805) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzseek64_refuse](../ZlibF/Proof/gzlib.c.seek.lean#L837) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzseek64_safe](../ZlibF/Proof/gzlib.c.seek.lean#L812) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzseek64_set_negpos_refuse](../ZlibF/Proof/gzlib.c.seek.lean#L945) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzseek64_write_run](../ZlibF/Proof/gzlib.c.seek.lean#L232) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gzseek_eq](../ZlibF/Proof/gzlib.c.seek.lean#L850) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gztell64_null](../ZlibF/Proof/gzlib.c.simple.lean#L122) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gztell64_spec](../ZlibF/Proof/gzlib.c.simple.lean#L143) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gztell_null](../ZlibF/Proof/gzlib.c.simple.lean#L154) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.gztell_run](../ZlibF/Proof/gzlib.c.simple.lean#L148) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.seekTail_back](../ZlibF/Proof/gzlib.c.seek.lean#L475) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.seekTail_copy](../ZlibF/Proof/gzlib.c.seek.lean#L315) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.seekTail_copy_ub](../ZlibF/Proof/gzlib.c.seek.lean#L962) | 未记录到固定目标的组合关系 |
| [Zlib.Gzlib.Proofs.seekTail_fwd_empty](../ZlibF/Proof/gzlib.c.seek.lean#L962) | 未记录到固定目标的组合关系 |
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
| [Zlib.Inflate.Proofs.inflate_LENLENS_eq](../ZlibF/Proof/inflate.c.main.table3.lean#L82) | 未记录到固定目标的组合关系 |
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
| [Zlib.Inflate.Proofs.llBody_run](../ZlibF/Proof/inflate.c.main.table3.lean#L95) | 未记录到固定目标的组合关系 |
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
| [Zlib.Zutil.Proofs.zError_correct](../ZlibF/Proof/zutil.c.lean#L125) | 未记录到固定目标的组合关系 |
| [Zlib.Zutil.Proofs.zError_safe](../ZlibF/Proof/zutil.c.lean#L117) | 未记录到固定目标的组合关系 |
| [Zlib.Zutil.Proofs.zcalloc_correct_none](../ZlibF/Proof/zutil.c.lean#L271) | 未记录到固定目标的组合关系 |
| [Zlib.Zutil.Proofs.zcalloc_correct_size](../ZlibF/Proof/zutil.c.lean#L262) | 未记录到固定目标的组合关系 |
| [Zlib.Zutil.Proofs.zcalloc_correct_some](../ZlibF/Proof/zutil.c.lean#L248) | 未记录到固定目标的组合关系 |
| [Zlib.Zutil.Proofs.zcalloc_safe](../ZlibF/Proof/zutil.c.lean#L234) | 未记录到固定目标的组合关系 |
| [Zlib.Zutil.Proofs.zcalloc_zcfree_no_leak](../ZlibF/Proof/zutil.c.lean#L316) | 未记录到固定目标的组合关系 |
| [Zlib.Zutil.Proofs.zcfree_correct](../ZlibF/Proof/zutil.c.lean#L290) | 未记录到固定目标的组合关系 |
| [Zlib.Zutil.Proofs.zcfree_correct_null](../ZlibF/Proof/zutil.c.lean#L308) | 未记录到固定目标的组合关系 |
| [Zlib.Zutil.Proofs.zcfree_safe](../ZlibF/Proof/zutil.c.lean#L280) | 未记录到固定目标的组合关系 |
| [Zlib.Zutil.Proofs.zlibCompileFlags_correct](../ZlibF/Proof/zutil.c.lean#L175) | 未记录到固定目标的组合关系 |
| [Zlib.Zutil.Proofs.zlibCompileFlags_safe](../ZlibF/Proof/zutil.c.lean#L169) | 未记录到固定目标的组合关系 |
| [Zlib.Zutil.Proofs.zlibVersion_correct](../ZlibF/Proof/zutil.c.lean#L159) | 未记录到固定目标的组合关系 |
| [Zlib.Zutil.Proofs.zlibVersion_safe](../ZlibF/Proof/zutil.c.lean#L134) | 未记录到固定目标的组合关系 |
| [ZlibF.Spec.Api.Proofs.Layer.ext](../ZlibF/Proof/Format/Api.lean) | [dict_roundtrip](#target-zlibf-spec-api-goal-dict-roundtrip), [format_deterministic](#target-zlibf-spec-api-goal-format-deterministic), [format_prefix_free](#target-zlibf-spec-api-goal-format-prefix-free), [inflate_completes](#target-zlibf-spec-api-goal-inflate-completes), [inflate_decodes](#target-zlibf-spec-api-goal-inflate-decodes), [inflate_deferred_distance](#target-zlibf-spec-api-goal-inflate-deferred-distance) |
| [ZlibF.Spec.Api.Proofs.inflate_deferred_distance_rejects_legacy_consistency](../ZlibF/Proof/Api/InflateCausality.lean#L229) | 未记录到固定目标的组合关系 |
| [ZlibF.Spec.Blocks.append](../ZlibF/Proof/Format/Deflate.lean) | [compress_roundtrip](#target-zlibf-spec-api-goal-compress-roundtrip), [dict_roundtrip](#target-zlibf-spec-api-goal-dict-roundtrip), [format_deterministic](#target-zlibf-spec-api-goal-format-deterministic), [format_prefix_free](#target-zlibf-spec-api-goal-format-prefix-free), [inflate_completes](#target-zlibf-spec-api-goal-inflate-completes), [inflate_decodes](#target-zlibf-spec-api-goal-inflate-decodes), [inflate_deferred_distance](#target-zlibf-spec-api-goal-inflate-deferred-distance) |
| [ZlibF.Spec.Blocks.det](../ZlibF/Proof/Format/Deflate.lean) | [compress_roundtrip](#target-zlibf-spec-api-goal-compress-roundtrip), [dict_roundtrip](#target-zlibf-spec-api-goal-dict-roundtrip), [format_deterministic](#target-zlibf-spec-api-goal-format-deterministic), [format_prefix_free](#target-zlibf-spec-api-goal-format-prefix-free), [inflate_completes](#target-zlibf-spec-api-goal-inflate-completes), [inflate_decodes](#target-zlibf-spec-api-goal-inflate-decodes), [inflate_deferred_distance](#target-zlibf-spec-api-goal-inflate-deferred-distance) |
| [ZlibF.Spec.Gzip.ext](../ZlibF/Proof/Format/Wrapper.lean) | [dict_roundtrip](#target-zlibf-spec-api-goal-dict-roundtrip), [format_deterministic](#target-zlibf-spec-api-goal-format-deterministic), [format_prefix_free](#target-zlibf-spec-api-goal-format-prefix-free), [inflate_completes](#target-zlibf-spec-api-goal-inflate-completes), [inflate_decodes](#target-zlibf-spec-api-goal-inflate-decodes), [inflate_deferred_distance](#target-zlibf-spec-api-goal-inflate-deferred-distance) |
| [ZlibF.Spec.Prefix.det](../ZlibF/Proof/Format/Deflate.lean) | 未记录到固定目标的组合关系 |
| [ZlibF.Spec.Prefix.ext](../ZlibF/Proof/Format/Deflate.lean) | [compress_roundtrip](#target-zlibf-spec-api-goal-compress-roundtrip), [dict_roundtrip](#target-zlibf-spec-api-goal-dict-roundtrip), [format_deterministic](#target-zlibf-spec-api-goal-format-deterministic), [format_prefix_free](#target-zlibf-spec-api-goal-format-prefix-free), [inflate_completes](#target-zlibf-spec-api-goal-inflate-completes), [inflate_decodes](#target-zlibf-spec-api-goal-inflate-decodes), [inflate_deferred_distance](#target-zlibf-spec-api-goal-inflate-deferred-distance) |
| [ZlibF.Spec.Proofs.prefixFree](../ZlibF/Proof/Format/Huffman.lean#L105) | [short_decode_table_leaf_sound](#target-zlib-inftrees-spec-decodeshort-goal-short-decode-table-leaf-sound), [decode_table_leaf_sound](#target-zlib-inftrees-spec-decodesoundness-goal-decode-table-leaf-sound), [constructor_establishes_query_stability](#target-zlib-inftrees-spec-decodetablestability-goal-constructor-establishes-query-stability), [short_rejected_leaf_stays_invalid](#target-zlib-inftrees-spec-decodetablestability-goal-short-rejected-leaf-stays-invalid), [constructor_establishes_fast_leaf_flags](#target-zlib-inftrees-spec-fasttableflags-goal-constructor-establishes-fast-leaf-flags), [compress_roundtrip](#target-zlibf-spec-api-goal-compress-roundtrip), [dict_roundtrip](#target-zlibf-spec-api-goal-dict-roundtrip), [format_deterministic](#target-zlibf-spec-api-goal-format-deterministic), [format_prefix_free](#target-zlibf-spec-api-goal-format-prefix-free), [inflate_completes](#target-zlibf-spec-api-goal-inflate-completes), [inflate_decodes](#target-zlibf-spec-api-goal-inflate-decodes), [inflate_deferred_distance](#target-zlibf-spec-api-goal-inflate-deferred-distance) |
| [ZlibF.Spec.Public.Proofs.DeflateCore.completes](../ZlibF/Proof/deflate.c.default-core-completes.lean#L89) | 未记录到固定目标的组合关系 |
| [ZlibF.Spec.Public.Proofs.DeflateCore.correct](../ZlibF/Proof/deflate.c.default-core-completes.lean#L140) | 未记录到固定目标的组合关系 |
| [ZlibF.Spec.Public.Proofs.DeflateCore.safe_encoding_and_cleanup](../ZlibF/Proof/deflate.c.default-core.lean#L181) | 未记录到固定目标的组合关系 |
| [ZlibF.Spec.Public.Proofs.DeflateInit.default_init_witness](../ZlibF/Proof/public-deflate-init.lean#L282) | 未记录到固定目标的组合关系 |
| [ZlibF.Spec.Public.Proofs.free_writable_matches_dropWindow](../ZlibF/Proof/Api/HeapCleanup.lean#L55) | 未记录到固定目标的组合关系 |
| [ZlibF.Spec.Public.Proofs.legacy_codes_used_impossible](../ZlibF/Proof/Api/QueryLayout.lean#L123) | 未记录到固定目标的组合关系 |
| [ZlibF.Spec.Zlib.ext](../ZlibF/Proof/Format/Wrapper.lean) | [compress_roundtrip](#target-zlibf-spec-api-goal-compress-roundtrip), [dict_roundtrip](#target-zlibf-spec-api-goal-dict-roundtrip), [format_deterministic](#target-zlibf-spec-api-goal-format-deterministic), [format_prefix_free](#target-zlibf-spec-api-goal-format-prefix-free), [inflate_completes](#target-zlibf-spec-api-goal-inflate-completes), [inflate_decodes](#target-zlibf-spec-api-goal-inflate-decodes), [inflate_deferred_distance](#target-zlibf-spec-api-goal-inflate-deferred-distance) |

## 更新记录

证明或登记表发生变化后，需要重新生成本页。生成过程会编译并检查
定理的精确类型，不会修改证明、目标或登记表。
结果是否通过项目验收，仍须依据[检查规则](checking/README.md)。

输入指纹：`e8795a5547f48a2a36e89d0f4aabc11404b34104eea776bc1b75b551d39acb1b`。
<!-- proof-progress:end -->

## 剩余工作

红色边框表示已经记录了阻碍证明的问题，下文给出证据和下一步。证明尝试耗时很长，本身不构成这种阻碍。灰色目标可以开始推进；它们缺少的内部引理和调用序列不变量并没有全部画在图中。

### 核心证明骨架

2026-11-11 的范围变更：只有安全在计划内（见[范围](#scope)）。仍未完成的功能性行标为"不在计划内"，不计工时；已检查的行保持不变。

#### inflate

inflate 系列的安全性（所有者 2026-11-11 的决定）：在每个可达历史上，无未定义行为、无内存错误、无泄漏，并且会终止。终止是每一行的一部分：每个定理都断言调用返回 `.ok`，这排除了 `Fault.outOfFuel`（`docs/spec/safety.md`）。“已检查”指定理在 `dev` 上且快速门禁为绿；“已验收”还需要验收套件。估计以专注工作的小时数计，不确定度约为数值的一半，包含共享构建主机上的构建时间。格式含义的 `meaning_*` 各行不在计划内，已不再列出；它们已证明的部分仍保留在 `dev` 上。

解码器不变量 `InflateInv`（`inflate.c.invariant`）：它把 `DefaultOriginState` 推广到 raw、zlib、gzip 与自动检测、windowBits 为 0，以及已附加的 gzip 头记录。`DecoderHeldBits`（在 `BAD`、`MEM` 与 `SYNC` 之外，至多持有 32 位）在每个可达历史上与它一起携带。

| 引理 | 含义 | 状态 | 小时 |
| --- | --- | --- | ---: |
| `inflate_public`（`public-inflate`） | 类型为 `Goal.inflate` 的定理：从每个可达流、每种配置（包括 gzip 头记录）出发的一次调用。首次在 `dev` 上无 sorry 是 `8b12ff6a`；快速门禁在 `2dab2f5e` 上为绿。 | checked | 0 |
| `inflate_reachable_invariant`（`inflate.c.reachable`） | 每个可达历史上的 `InflateInv` 与 `DecoderHeldBits`：初始化、重设缓冲区、每个流操作、`inflateCopy`。 | checked | 0 |
| `inflate_call_held`（`inflate.c.held-history`） | 一次 `inflate` 调用保持 `DecoderHeldBits`。这是安全性所需的功能事实：位缓冲区 `hold` 宽 32 位，所以解码器绝不能持有更多位。 | checked | 0 |
| `Goal.inflate` 的进展子句 | `rc = Z_OK → used ≠ 0 ∨ out ≠ []`。这是 `uncompress*` 循环的终止所需的功能事实；属于 `inflate_public`。 | checked | 0 |
| `inflate_call_safe`、`operation_safe`（`inflate.c.sequence-safety`） | 从可达历史出发的每个流操作只写流记录、它自己的块、头记录以及 `StreamWriteRegions` 中的调用者区域，并且恰好按它自己的账目改变活动块。`inflate` 经由 `InflateCall.safe`；`inflateSync` 经由 `inflateSync_call_safe`（包括重新同步时释放的窗口）；其余 12 个经由 `inflate.c.call-safety`。 | checked | 0 |
| `inflateEnd_invariant`（`inflate.c.call-safety`） | 对可达流调用 `inflateEnd` 返回 `Z_OK`，清除状态并释放流所拥有的每个块。 | checked | 0 |
| `inflate_sequence_safety_public`（`public-inflate-sequence-safety`） | 类型为 `Goal.inflate_sequence_safety` 的定理（= `StreamSequenceSafety .inflate`，即 `Goal.inflate_sequence` 的安全性一半）。 | checked | 0 |
| `inflateInit_`、`inflateInit2_`（`public-inflate-init`、`public-inflate-init2`） | 每个 windowBits 与每种分配结果，按源码中的错误顺序；无效宽度会释放其状态。`inflate_init2_public` 已证明；它还需要登记。 | checked | 0 |
| 各种重置、`inflateEnd`、`inflateGetDictionary`、`inflateSetDictionary`、`inflateGetHeader`、`inflatePrime`、`inflateSyncPoint`、`inflateMark`、`inflateCodesUsed`、`inflateUndermine`、`inflateValidate` | 生命周期与查询目标，包括空流与无效流。 | 已登记 | 0 |
| `inflateSync` | 每个可达历史上的安全性：`inflateSync_call_safe`，属于序列定理。`Goal.inflateSync` 的其余部分是精确的标记搜索（`Api.syncSearch`），这是任何安全证明都不需要的功能子句。 | checked (safety) | 0 |
| `inflate_copy_public`（`public-inflate-copy`、`inflate.c.copy-public`） | 类型为 `Goal.inflateCopy` 的定理：空参数被拒绝；从每个可达源出发，两种分配失败都释放已分配的内容并清除 `dest->state`，成功则给出重定位后的状态、窗口前缀，以及账目中恰好新增的块。由 `inflate.c.copy-*` 的六个执行引理组合而成。 | checked | 0 |
| 验收批次 | `inflate_public`、`inflate_init2_public`、`inflate_sequence_safety_public` 与 `inflate_copy_public` 已登记在 `tests/audit/theorems.txt`，`Goal.inflate_sequence_safety` 已登记在 `tests/audit/goals.txt`；`tests/proof-mutants/public-streams.tsv` 中有针对 `inflate`、`inflateCopy` 与 `inflateInit2_` 的九个函数体证明变异，每个都经本地运行在其所列模块中被杀死。验收套件尚未在某个指名的提交上运行。 | prepared | 0 |
| 清理 | 删除没有任何已登记定理使用的快速路径与固定配置证明。 | open | 4 |
| `uncompress*`（`public-uncompress*`） | 功能目标：四个都在 `dev` 上由 `DecoderFacts` 组合得到（`uncompress2_z_of_facts`、`uncompress2_of_facts`、`uncompress_z_of_facts`、`uncompress_of_facts`）。不计划：`DecoderFacts` 的格式事实不在范围内（只证安全）。 | not planned | 0 |
| `uncompress*_safe`（batch 3） | `Goal.uncompress2_z_safe`、`uncompress2_safe`、`uncompress_z_safe`、`uncompress_safe`（`Spec/Public/Utilities`）：无未定义行为，会终止，只写输出缓冲区（不超过容量）与长度单元，每条返回路径都释放全部分配，返回文档规定的返回码，只在分配失败后返回 `Z_MEM_ERROR`。已在 `public-uncompress-safe` 中无前提证明（`uncompress2_z_safe`、`uncompress2_safe`、`uncompress_z_safe`、`uncompress_safe`）：每次 `inflate` 调用用 `inflate_public`，每个可达流都有解码器（`reachable_invariant_kind`）；不用格式事实，也不用功能事实。功能证明共用这段运行（`SafeState`、`SafeFinal`），另加它的格式事实（`NoOver`）。终止：循环的度量（未读源字节加未填空间）低于循环燃料，并在每次 `Z_OK` 调用后下降，依据 `Goal.inflate` 的进展子句（`rc = Z_OK → used ≠ 0 ∨ out ≠ []`），这是安全事实。陈述测试 `tests/goals/uncompress-safety`（ASan、UBSan、泄漏计数、分配失败；9000 次运行无子句被违反）。验收批次：四个定理和目标已登记（`tests/audit/theorems.txt`、`goals.txt`）；`uncompress2_z` 的四个翻译变异（`tests/proof-mutants/api-boundary.tsv`：去掉 `inflateEnd`、`destLen` 计数错误、补充量差一、初始化出错路径泄漏）都在 `public-uncompress-safe` 中被杀死，位置是运行与安全事实相遇之处。证明不再复述程序（删除了 `program`、`program_eq`）：它运行翻译本身，循环体由 `BodyOK` 描述，补充量写成最小值。 | checked | 0 |
| **剩余合计** | | | **4** |

批次 3 的陈述更正与公开目标的定义域。每一项只改变 `DecoderFacts` 的内部事实；没有公开目标（`Goal.inflate_completes`/`InflateCompletes`、四个 `uncompress*` 目标、格式目标）失去其定义域的任何部分，因此不需要 `docs/deviations.md` 条目。
- `d23ce2d5` `NeedDictionaryCall` 增加 `log.singleDictionary = true` 与 `ByteObjectsFit h`；`InflateCompletes` 与 uncompress 循环已经假设二者。
- `61995719` `TraceEvidence` 排除配置窗口大于头部窗口的 zlib 字典。其唯一用途 uncompress 循环不使用字典。被排除的情形是 C 解码了 RFC 1950（`Zlib.Decodes`）不允许的流，但这不是新发现：它是 zlib 在未定义 `INFLATE_STRICT` 时的默认行为，已由 `Api.Layer.InflateAccepted` 建模，并记录于 `tests/regression/inflate-configured-window`。
- `0c56ca53` `ConsumesWithinStream` 第二个子句要求流有尾部，或有输出空间且 flush 不是 `Z_BLOCK`/`Z_TREES`。`InflateCompletes` 提供空间与这样的 flush；uncompress 解码 zlib。被排除的情形（原始数据、无空间）是 C 的正确行为，不是发现。
- `ConsumesWithinStream` 第二个子句的结论由 `Z_STREAM_END ∨ Z_MEM_ERROR` 改为 `rc ≠ Z_OK ∧ rc ≠ Z_BUF_ERROR`：流结束后被拒绝的调用（`next_out` 为 NULL）在整个流已被消费时返回 `Z_STREAM_ERROR`。所有用途只排除 `Z_OK` 与 `Z_BUF_ERROR`。这是 C 的正确行为，不是发现。
- `a974ea43` `ConsumesWithinStream` 与 `StopsWhenBlocked` 增加 `ByteObjectsFit h`；协议历史在每次调用前都记录它。
- `ParseMeaning` 的请求子句由等价改为从令牌到 `havedict = 0` 的 `needDict` 阶段的蕴含：返回 `Z_NEED_DICT` 之后，一次 `next_out` 为 NULL 的调用被拒绝并返回 `Z_STREAM_ERROR`，令牌变为假而解码器仍在等待（`tests/verification/regressions/inflate-refused-dictionary-request.lean`）。所有使用处都只用蕴含方向。属内部修正；是正确的 C 行为，不是发现。

对象大小上限：`StreamReachable` 在每次 inflate 调用之前和每次调用者编辑之后假设 LP64 的 `PTRDIFF_MAX` 上限，`StreamSequenceSafety` 在每次调用之前假设该上限（`408c1f04`）。

##### inflate 第 1 批：格式含义的解码侧

一次调用内 deflate 流的块体：块头、固定表与动态表的安装、码长表、慢速符号解码、存储块复制、整个
`inflate_fast` 调用、从输出与窗口的匹配复制，以及 `inf_leave` 处的窗口更新。文件为
`inflate.c.meaning-<topic>`。每个引理覆盖 8 到 15 的所有窗口宽度和所有封装，不固定配置。陈述测试：
`tests/goals/inflate-meaning-body`（真实解码器在块体模式下的状态字段与解析位置对照：按下述修正后，
3,200 个会话约 56,000 个状态无子句被违反）。

与 inflate 负责人商定的接口修正（2026-11-10）。每一项都使 `meaning_step` 为假或无法证明；证据来自真实解码器或反例状态。

- P1（`0696a247`）：zlib 对某些动态块头只在读完整一部分后才拒绝，因此 `dynamicBits` 去掉可补全前提（`tests/goals/inflate-meaning/late-rejection.c`：三个单次调用会话以 `Z_OK` 停在 `LENLENS` 或 `CODELENS`）。
- P2（`0696a247`）：动态块头的 `BodyMatches` 增加 `DynamicMatches`（计数、码长码及其表、已读码长）。
- P3（`0696a247`）：没有窗口时 `WindowMeaning` 要求历史为空。
- P4（`0696a247`）：增加 `storedPad`，因为 `STORED` 在等待 `LEN` 之前先丢弃填充位；真实解码器：raw -15，块头结束于第 32805 位时，一次调用停在 `STORED` 且已消费 32808 位（回归测试 `tests/verification/regressions/inflate-stored-pad.lean`）。
- P5（`0696a247`）：`TableMeaning` 包含 `StableQuery`，在保留位少于 15 时拒绝无效码需要它。
- P6（`d9fa89d1`）：存储块不保留位，因此 `COPY` 跟随输入。
- P7（`69b25ebe`）：每个等待位置都限定保留位数，使块边界处少于 8 位成为归纳性质；真实解码器：1,800 个会话约 32,000 个块体状态中数值上界无违反。
- P8（`03c98f14`）：块体阶段中 `out - left` 等于本次调用的输出，`MATCH` 依赖于此。
- P9（`03c98f14`）：`partialCopy` 携带记号的距离（`0 < dist ≤ |dict ++ out|`，`dist ≤ 32768`）。
- P11：`BodyMatches` 在 `.storedHeader` 处保留少于 32 位。`STORED` 的补码检查会读到 32 位以上的位，没有这个上界 `stored_step` 为假：raw -15，输入 `01 01 00 FE FF 01`（一个合法的单字节最终存储块）全部读入，`STORED` 中保留 45 位，检查进入 `BAD`。zlib 在 `TYPEDO` 之后保留少于 8 位，在 `STORED` 中等待之后少于 32 位。
- P12（`123722bb`）：`PendingParsed` 在 `.copy` 处接受一个尚未写出任何字节、没有历史界的完整匹配。`MATCH` 在检查距离之前就因没有输出空间而离开，因此过远的距离可以停在那里，而调用返回 `Z_OK`；真实解码器：raw -15，输入 `03 02`、没有输出空间时停在 `MATCH`，返回 `Z_OK`，offset 为 1，窗口为空，下一次调用报告 `invalid distance too far back`（`tests/goals/inflate-meaning-body/far-match.c`，回归测试 `tests/verification/regressions/inflate-unchecked-match.lean`）。
- P13（`f88873e0`）：`.none` 与 `.distance` 处的保留位上界只排除去掉最后一个字节后的保留位中的有效符号（不超过 285、不超过 29）。`TableMeaning` 没有说明保留符号的表项消耗多少位（`fixedDistLens` 中的 30 和 31，`fixedLitLens` 中的 286 和 287），因此在因缺少输入而离开的查找处，对任意符号的上界无法证明；保留符号会导向 `BAD`。
- P14：`DynamicMatches` 的 `CODELENS` 子句另含 `Trace` 的逆向：从零个码长开始对头部位的每个解析都经过已存的码长。仅有 `Trace` 不能确定头部各项在何处结束，因此 `codelens_step` 在重复错误处为假。反例状态：`HLIT = 0`、`HDIST = 3`（261 个码长）；码长码使符号 2、16、17、18 长度为 2（`00`、`01`、`10`、`11`）；`A = [2,2,2] ++ 0^253 ++ [2]` 由各项 `R` 读出；头部位为 `R ++ 01`（16 的编码，其附加位未读）；已存码长 `A ++ [2,2]`。`Trace` 成立（唯一补全是两个字面量 2，而 `R ++ 01 00 00` 也给出 `A ++ 2^4`）。源 `R ++ 01 10 ...` 有效（16 带附加值 1 给出 `A ++ 2^4`，字面量/长度码完整且含块结束，距离码完整），但解码器把 `10` 读作 17 并进入 `BAD`。
- P15：`TableMeaning` 另含 `PrefixQuery`（适配的查询从其补零后的已消耗位选出同一表项）与 `QueryCompatible`（快速叶标志）。在 `BAD` 处，`inflate_fast` 只丢弃被拒记号的位，然后退还未用的整字节，因此已读输入可能止于查表看过的位之内；`Inv` 与 `StableQuery` 不确定被拒表项需要多少位。反例：一个固定块，其字面量/长度表对 286 和 287 的编码读到 `{op 64, bits 6}`，仍满足 `Inv`、`StableQuery` 与 `QueryCompatible`，快速调用读到 `110001` 为止，而 284 的编码（`11000100`）可有效地接续它。作为一张更小的、经内核检查的表保留：它满足 `Inv` 与 `StableQuery` 但不满足 `PrefixQuery`（`tests/verification/regressions/inflate-prefix-query.lean`）。构造函数建立该性质（`constructor_establishes_prefix_query`，后续构造保持它：`prefix_query_of_prefix`），固定表也满足（`lenfix_prefix`、`distfix_prefix`）。
- 共用块（目标变更）。快速解码器的 `Env` 曾要求输入与输出位于不同的块（`hsep : ib ≠ ob`）。这过窄：输入与输出可以是同一块中互不重叠的范围，这是有定义的 C（[复现](../tests/regression/inflate-shared-block/README.md)）。`Env.hsep` 现为 `ib ≠ ob ∨ (ib = ob ∧ 输入范围 [i0, i0 + avail_in) 与输出范围 [o0, o0 + avail_out) 不相交)`。窗口块仍不同于输出块。循环中输出数组 `A` 任意的片段现在还假设 `Env.InputFrame A i`：块共用时，`A` 从游标 `i` 到输入末尾保留原输入。类型改变的已登记目标：所有基于 `Env` 的目标都容许共用块（`step_safe`、`fast_safe`、`actual_body_preserves_origin`、`actual_body_refines_token`、`actual_fast_preserves_origin`、`actual_distance_block_preserves_origin`、`actual_distance_refines_lz77`、`distance_lookup_matches_format`、`length_lookup_matches_format`、`actual_body_retains_selected_length`、`actual_copy_match_refines_lz77` 以及各 `Origin` 目标）。`StepPre`（因而 `step_safe`、各 `actual_body_*` 目标与 `actual_body_retains_selected_length`）新增字段 `inputFrame`；`actual_pull_preserves_origin`、`actual_rollback_preserves_origin`、`actual_distance_block_preserves_origin` 与 `actual_distance_refines_lz77` 新增前提 `InputFrame`。块不同时新前提空真，因此每个新类型都蕴含旧类型。整次调用的目标 `fast_safe` 与 `actual_fast_preserves_origin` 不带新前提：循环由分离性消去 `InputFrame`，因为解码器只在输出范围内写入（`Env.inputFrame_of_frame`、`Env.InputFrame.write`）。

块体模式的子句由 `tests/goals/inflate-meaning-body` 在真实解码器上检查（3,200 个会话约 56,000 个状态，无违反）。

| 引理 | 含义 | 状态 | 小时 |
| --- | --- | --- | ---: |
| `meaning_interface_body` | P1 到 P4、`DynamicMatches` 以及 `TableMeaning` 中的后缀稳定性（`inflate.c.meaning`，`0696a247`）。 | checked | 0 |
| `LoopMatches`（`meaning-loop`、`meaning-write`、`meaning-frame`） | 一次调用内模式步之间的关系：寄存器、本次调用已消费输入、保留位、阶段、调用基点以来的输出、调用前输出的窗口与校验值。与第 2 批共用。已与第 2 批商定；含输出写入与框架引理。 | checked | 0 |
| `lenfix_inv`、`distfix_inv`、`lenfix_stable`、`distfix_stable`（`meaning-fixed-tables`） | 静态固定表满足 `DecodeTableInvariant.Inv`，码长为固定码长，包括短查询，查询对后续输入稳定、只读其已消耗的位（`lenfix_prefix`、`distfix_prefix`），且叶标志相容。 | checked | 0 |
| `lookup_meaning`（`meaning-lookup`、`meaning-length`、`meaning-distance`） | 带补充输入的慢速 `lookup1`/`lookup2` 作用于满足 `Inv` 的表：选中的叶子是保留位的符号（可用位少于 15 也成立），或输入没有有效符号。已并入各步引理（`fitted_leaf_meaning`、`lookupLoop_fail`、`lookup1_len_fail`、`lookup2_len_fail`）。 | checked | 0 |
| `codes_lookup_meaning`（`meaning-codelens-items`） | 码长表（`CodeLengthMeaning`）的同一性质，包括空码长码（`cl_iter`）。 | checked | 0 |
| `table_step`（`meaning-dynamic-steps`） | `TABLE`：等待、计数拒绝（`BAD`，无有效续写），或以 `LoopMatches` 进入 `LENLENS`。除流记录外无其他假设。 | checked | 0 |
| `lenlens_step`（`meaning-dynamic-steps`） | `LENLENS`：跨调用读取码长码的码长；拒绝且无法补全，或带 `CodeLengthMeaning`、空码的表项和少于 8 个保留位进入 `CODELENS`。除流记录外的假设：`WellFormed`（数组大小）。 | checked | 0 |
| `codelens_step`（`meaning-dynamic-steps`、`meaning-codelens-items`、`meaning-dynamic-tables`） | `CODELENS`：跨调用读取码长；重复（经解析的逆向得出 `BAD`）；块结束与编码检查（`BAD`：不存在 `DynamicHeader` 补全）；以 `Inv`、`StableQuery`、`PrefixQuery` 与 `QueryCompatible` 安装两张表；因 `Z_TREES` 离开或落入 `LEN_`。除流记录外的假设：`WellFormed`、`CodeLengthInvariant`、已安装表的内容分类。 | checked | 0 |
| `typedo_step`、`type_step`（`meaning-block`） | 最后一块之前的 `TYPE`、`TYPEDO`：存储块、固定块（用 `lenfix_inv`）、动态块、类型 3（`BAD`，格式中没有类型 3 的块体）。静态表来自 `LibraryGlobals`。 | checked | 0 |
| `stored_step`（`meaning-block`、`meaning-copy`） | `STORED`、`COPY_`、`COPY`：填充位、长度检查与跨调用的字节复制。除 `LoopMatches`、流记录与窗口界之外没有其他前提；保留位上界来自 `BodyMatches`（P11）。 | checked | 0 |
| `len_slow_step`（`meaning-length`） | `LEN_`、慢速 `LEN`：字面量、块结束（保留位少于 8）、长度、无效码（`len_slow_step`、`len__step`，接入 `lenext_step`）。`match_step` 之外的前提：快速分支条件的否定与 `DataTablesSafe`。 | checked | 0 |
| `distance_steps`（`meaning-distance`） | `LENEXT`、`DIST`、`DISTEXT`：额外位、距离符号、无效距离（`lenext_step`、`dist_step`、`distext_step`，接入 `match_step`）。`match_step` 之外的前提：`DataTablesSafe` 与 back 计数器上界（`DataPendingInvariant`）。 | checked | 0 |
| `lit_step`（`meaning-lit`） | `LIT`：写出待写字面量。 | checked | 0 |
| `match_step`（`meaning-match`） | `MATCH`：从输出和窗口复制、重叠、距离过远。 | checked | 0 |
| `fast_call_meaning`（`meaning-fast-token`、`meaning-fast-loop`、`meaning-fast`、`inffast.c.body-token-reject`） | 从 `LEN` 进入的整个 `inflate_fast` 调用，标准步骤形状：块内更多记号或块结束给出 `LoopMatches`；被拒记号给出 `BAD` 与 `LoopDoomed`（P15：记号在其自身的位上被拒，`actual_body_rejects_prefix`；对已存窗口过远的距离，在完整窗口下对整个历史也过远，`Token.Rejected.rebase`）。输入与输出可以是 `DispatchBuffers` 容许的任何调用方字节视图，也包括同一块中互不重叠的范围（`inflate_fast_entry`，见上面的共用块目标变更）。窗口块不同于输出块由调用方输出范围得出（`callerRange_slow_output`），而非前提。`match_step` 之外的假设：`Good`、`DataTablesSafe`、`DataPendingInvariant`、`DispatchBuffers`、`ByteObjectsFit`。 | checked | 0 |
| `leave_window_meaning`（`meaning-leave-window`） | `inf_leave` 处的 `updatewindow` 给出调用后输出的 `WindowMeaning`，包括首次分配窗口；分配失败时状态不变，旧的 `WindowMeaning` 保持。假设：`Good`、默认分配器、输出字节、输出缓冲区不是窗口块。 | checked | 0 |
| 清理 | 已删除 33 个 `inflate.c.fast*` 模块：没有已登记定理、公开目标、含义模块或其他模块导入它们（早期的语义切片及建于其上的视图框架）。其余 `inflate.c.fast*` 模块由含义证明的快速路径导入。 | 已检查 | 0 |
| **第 1 批剩余** | | | **0** |

供第 3 批使用：ConsumesWithinStream 的界。

| 名称 | 含义 | 状态 | 小时 |
| --- | --- | --- | --- |
| `HeldWithin`（`heldWithin`，`meaning-held-within`） | 处于语法阶段的解码器状态，不持有超出与其位可比较的有效流末尾的位；没有阶段位于完整流之后。即第 3 批的陈述加一个前提 `(consumed ++ held).length % 8 = 0`，在使用处成立。没有其他前提。 | checked | 0 |
| 批次 1 步骤引理中的 `LeaveShort`、`LoopRefuted`（`meaning-leave-short`） | 主体步骤每次因缺少输入（`have = 0`）离开时，所持有的位不足以构成其模式等待的字段（`LeaveShort`：少于 `NEEDBITS` 的位数，`COPY` 仍有剩余字节，在已安装表的任一含义下都没有完整的有效符号或码长项）。每次拒绝（`BAD`）时，已读输入不与任何满窗口有效流可比较（`LoopRefuted`，强于 `LoopDoomed`：有效流也不在已读位之内结束）。步骤：`TYPE`/`TYPEDO`、`STORED`、`COPY_`/`COPY`、`TABLE`、`LENLENS`、`CODELENS`、`LEN_`/`LEN`、`LENEXT`、`DIST`、`DISTEXT`、`MATCH`、`inflate_fast`。两者都先在真实解码器上检验（`tests/goals/inflate-meaning-body`：约 75,000 次缺输入离开，约 490 次损坏源上的数据错误，无违反）。`LoopBad`（批次 2）仍带 `LoopDoomed`（`LoopRefuted.doomed`）。 | checked | 0 |
| `StopShort` | 恰好消耗整个有效流的调用不返回 `Z_OK` 或 `Z_BUF_ERROR`（raw：除非输出空间不足，或 flush 为 `Z_BLOCK`/`Z_TREES`）。单次调用部分已检查：缺少字段（`LeaveShort`）的循环趟次没有读完整个有效流（`LoopMatches.starved_not_end`，`meaning-stop-short`）。剩余：整次调用的组合（`loop_meaning`，批次 3），以及因空间不足或 `Z_BLOCK`/`Z_TREES` 的停止（`BlockedLeave`、`wrapParsed_due`）。 | 不在计划内 | — |
| `FailWithin` | 停在 `BAD` 或 `MEM` 的调用，没有读过此前输入所开始的有效流的末尾。单次调用部分已检查：拒绝排除每个可比较的有效流（`LoopRefuted.not_comparable`，`meaning-stop-short`）；每个循环趟次中已读输入都是每个可比较有效流的开头（`LoopMatches.within`，`meaning-held-within`，用于 `MEM` 离开）。剩余：整次调用的组合（`loop_meaning`，批次 3）。 | 不在计划内 | — |

##### inflate，第 2 批：格式含义的流侧

包装头、字典请求与安装、尾部、结束、把模式步组装成一次调用以及把调用组装成历史，以及 `meaning_init`、`meaning_rebuffer`、`meaning_dictionary`、`meaning_accepted`、`meaning_prefix`。文件为 `inflate.c.meaning-<topic>` 与 `ZlibF/Math/inflate-meaning-*`。每个引理覆盖 raw、zlib、gzip 与自动检测，以及每个被接受的 windowBits（含 0）。协议轨迹中不会挂接头记录（`inflateGetHeader` 不是轨迹步骤），所以不会发生头捕获；头模式在 `head = NULL` 下证明。陈述测试：`tests/goals/inflate-meaning`（真实解码器的状态字段对照解析位置；6000 个会话中没有事实被违反）。

接口修正已与 inflate 负责人商定并在 `dev` 上（`bd0831d3`）：头阶段接纳首次调用前的 raw 数据；`ConfigMatches` 把解码器配置与轨迹联系起来；`needDict` 接纳任意 `DICTID`；块边界处持有少于 8 位（由第 1 批证明）；`MEM` 状态保留 `meaning_accepted` 与 `meaning_prefix` 的结论；`WrapMatches` 记录流侧的阶段字段（`inflate.c.meaning-stream`）。

| 引理 | 含义 | 状态 | 小时 |
| --- | --- | --- | ---: |
| `ConfigMatches`、`WrapMatches` | 配置字段，以及头、`needDict`、尾部与结束阶段的逐阶段字段（`bd0831d3`）。 | defined | 0 |
| `LoopMatches` | 第 1 批的行；第 2 批提供了草案并基于它组装。 | checked | 0 |
| `wrap_header_grammar`（`Math/inflate-meaning-wrap`、`meaning-wrap-steps`） | zlib 与 gzip 头的字节步保持可补全的头前缀；解码器等待处不是完整的头；补全到主体或 `needDict`；`HEAD`、`FLAGS`、`HCRC` 的每种拒绝都没有补全。 | checked | 0 |
| `wrap_trailer_grammar`（`meaning-wrap-steps`、`meaning-accept`） | 主体结束到尾部再到完成；尾部不匹配没有补全。 | checked | 0 |
| `meaning_init`（`inflate.c.meaning-init`） | 每个被接受的 windowBits 下 `inflateInit2_` 给出无输入的头阶段。 | checked | 0 |
| `meaning_rebuffer`（`meaning-rebuffer`） | 调用方换缓冲区保持状态、窗口与表；每个阶段的帧引理。 | checked | 0 |
| `head_step` | `HEAD`：raw 进入 `TYPEDO`，zlib 头（宽度 0 时由头设定宽度），gzip 魔数，每种拒绝。 | 不在计划内 | — |
| `dictid_step`、`dict_step`（`meaning-dictid`） | `DICTID` 保存标识并请求字典（`dictid_step`，已检查；`NeedDictExit`）；`DICT` 再次请求或进入主体（未完成；需要 P16，即 `needDict` 条款中的 `last = total = 0`，已向第 1 批提出）。 | 不在计划内 | — |
| `gzip_fixed_steps` | `FLAGS`、`TIME`、`OS`、`EXLEN`，含头 CRC 累加器。 | 不在计划内 | — |
| `gzip_field_steps` | `EXTRA`、`NAME`、`COMMENT`：跨调用的字节序列，对输入字节做 CRC。 | 不在计划内 | — |
| `hcrc_step` | `HCRC`：头 CRC 检查并进入主体。 | 不在计划内 | — |
| 共用循环引理（`meaning-bits`、`meaning-stuck`、`meaning-outcome`、`meaning-fields`） | `LoopMatches.needbits`；`LoopDoomed.of_stuck`；`LoopBad`、`TripOutcome`、`bad_trip`；持有位作为小端字节。 | checked | 0 |
| `trailer_steps`（`meaning-trailer`、`meaning-check`） | `DONE` 与 gzip `LENGTH`（已检查）；zlib 与 gzip 的 `CHECK` 用本次调用输出更新 Adler-32 或 CRC-32，随后进入长度字段或结束（`check_step`，已检查）；raw `CHECK` 需要 P10（raw 数据在 `CHECK` 时处于结束阶段，已向第 1 批提议）。 | 不在计划内 | — |
| `leave_meaning`（第 3 批，`meaning-leave`） | `inf_leave`：用本次调用输出更新计数与校验值；窗口更新用第 1 批的引理；`Z_MEM_ERROR`。带 `LoopMatches` 的循环出口由 `leave_meaning` 给出（`LeaveMeaning`），`BAD` 出口由 `leave_meaning_bad` 给出（`LeaveBad`），二者基于 `inflate_leave_values` 与 `checkMeaning_leave`。 | checked | 0 |
| `loop_meaning`（第 3 批，`meaning-run`） | 一次调用的模式循环以 `LoopMatches` 进入，以 `LoopExit` 结束：带 `LoopMatches` 的离开、`Z_STREAM_END`、带 `LoopBad` 的 `Z_DATA_ERROR`，或字典请求。前提：`TripMeaning`（第 1、2 批逐模式的步）与 `SideKept`（各步所需的安全事实，每一趟都保持）。 | checked | 0 |
| `meaning_step` 组装（第 3 批） | 入口、拒绝、运行与离开给出调用后的 `ParseMeaning`，含请求令牌。 | 不在计划内 | — |
| `meaning_dictionary`（`meaning-dictionary`） | `inflateSetDictionary`：拒绝、标识不匹配、`Z_MEM_ERROR`、raw 安装、zlib 在 `DICT` 中安装。 | checked | 0 |
| `deflate_prefix_order`（`meaning-prefix-order`、`meaning-accept`） | 有效流前缀上的解析位置位于它的解析上（输出前缀、精确结束），完成的解析就是规格解析，配置的 zlib 窗口与头声明的窗口解码相同，阶段的头就是流的头。 | checked | 0 |
| `meaning_accepted`（`meaning-format`） | 完成的单字典阶段消费的是被接受的流。 | checked | 0 |
| `meaning_prefix`（`meaning-format`） | 前缀、无数据错误、精确结束，`Z_MEM_ERROR` 之后亦然。 | checked | 0 |
| 清理 | 推广或删除默认配置下的头、字典与包装模块。 | 不在计划内 | — |
| **第 2 批剩余** | | | **0** |

第 2 批，为 `inflate_call_gzip` 准备的 gzip 头模式。已在 `dev` 上检查：`inflate_dispatch_gzip_header_rank`（`inflate.c.gzip-header-dispatch`），与 inflate 负责人的接口陈述完全一致。从 `FLAGS` .. `HCRC` 出发的一次分派，对任意允许 gzip 的包装、有无挂接的头记录，都无故障地运行，并保持表示不变式、调用方数据包、头记录与足迹。有两个前提比 zlib.h 更窄（`docs/deviations.md`）：头记录的 `extra` 缓冲区与未读输入分离；在 `EXTRA` 中头记录的 `extra_len` 不小于剩余长度。两者都来自 EXTRA 的 `zmemcpy` 在真实 C 上的未定义行为（`tests/regression/inflate-gzip-extra`）。`Goal.inflate` 是否把它们作为调用方定义域条款保留，由负责人决定。name 与 comment 缓冲区可以与输入重叠。

骨架条款`flags 字保持不变或是 16 位字`（skeleton/inflate 5d6f00e8）按原陈述为假：解码器在 `FLAGS` 中等待时，`inflatePrime` 可以在位缓冲区中留下 32 位，真实 C 随后写入 `flags = 65544`（`tests/regression/inflate-gzip-flags-prime`）。已证明的形式加上了入口位缓冲区的条件。`InflatePhase.flags` 对所有历史作出同样的 16 位断言；如何更正由负责人决定。

| 引理 | 含义 | 状态 | 小时 |
| --- | --- | --- | ---: |
| `HeaderFoot`（`inflate.c.gzip-header-frame`） | 相对入口堆的逐点足迹；给出 `BufferFrame` 与 `LiveChange`。 | checked | 0 |
| `GzInv`（`inflate.c.gzip-header-state`） | 步骤不变式：状态、流与头记录写入，`hbuf` 与区域存储，`NEEDBITS`，输入消耗。 | checked | 0 |
| `gz_FLAGS` .. `gz_HCRC`（`inflate.c.gzip-header-modes`） | 每个模式运行到头模式中的离开、`TYPE` 或 `BAD`；`NAME`/`COMMENT` 字节循环；`CRC2`、`CRC4`；`EXTRA` 的复制。 | checked | 0 |
| `inflate_dispatch_gzip_header_rank`（`inflate.c.gzip-header-dispatch`） | 接口定理。 | checked | 0 |
| `inflate_dispatch_gzip_header_flags_leave_word`（`inflate.c.gzip-header-dispatch`） | 离开时没有剩余输入；flags 字保持不变，或在入口位缓冲区为 0、8 或 16 位时是 16 位字。 | checked | 0 |
| **gzip 头模式** | | | **0** |

#### deflate

骨架位于分支 `skeleton/deflate`，文件为 `ZlibF/Proof/deflate.c.universal.lean`。它可以通过类型检查：`Goal.deflateInit2_`、`Goal.deflate` 和 `Goal.deflate_sequence` 在该分支上由下列未证引理证明。状态 open 表示该引理还没有证明，checked 表示它已在 `dev` 上证明。估计值是专注工作的小时数，误差约为数值的一半，包括共享构建主机上的构建时间。

单一不变量 `DInv` 在每个可达状态下成立，适用于每个 level、`memLevel`、`windowBits`、策略、调优值和头部：`DGood`、默认分配器、窗口、块、惰性匹配、位和待输出状态的形状，散列状态（精确的散列链；level 0 下经过一次存储滑动后，是 `slide_hash` 将修复的链；有前瞻时的滚动散列），以及当前块的已记录符号及其叶频率（`SymbolLedger`）、已清零的块代价（`BlockClear`），且待输出字节位于这些符号之下。`DInv` 与共享的陈述部件（`StrategyEntry`、`CallFrame`、`WindowSide`、`Inserted`）在 `dev` 上的 `ZlibF/Proof/deflate.c.universal-invariant.lean` 中。标量字段由 `tests/goals/deflate/invariant.c` 在真实 C 的随机历史上检查（是证据，不是证明）。其他模块使用它的接口（`DInv.dgood`、`DInv.unique`、`DInv.owned`、`DInv.rebuffer`），不使用其字段。单一账目 `Ledger` 把一个数据段与流联系起来：头部和完整的块解码为输入的前缀，已记录的符号表示接下来的部分（`Trace`），窗口保存其余部分。

范围（owner，2026-11-11）：deflate 只证明安全性。功能性的一半（账目、`completes`、`bound_before_output`、`Goal.deflate_sequence` 的功能条款）不计划；它在 `dev` 上的定义（`deflate.c.universal-ledger-defs`）和骨架上的陈述保持原样。序列目标是 `Goal.deflate_sequence_safety`（`StreamSequenceSafety .deflate`，即 `Goal.deflate_sequence` 的第一个合取项），与原目标并列陈述，不削弱原目标。

三个组合还需要什么（2026-11-11）。`reachable_inv`：`init2_inv`、`DInv.rebuffer`、`copy_inv`（已检查）和 `operation_step`，以及 batch C 的 `HeaderInv` 引理。一旦以下各项成为定理，`operation_step` 即为 `operation_step_of`（已检查，batch 1）：带 `CallClauses` 的 `deflate_call`（inflate batch 2）、`step_setDictionary` 和 `step_params`（batch B）、`step_resetKeep`（inflate batch 1，在 `DInv` 散列链改为位置形式之后；该修正的陈述已写在共享说明中，并与 batch B 的策略返工一起落地）、这四个操作的 `HeaderInv` 引理，以及“`deflateGetDictionary` 的缓冲区是调用者字节块”的历史前提（inflate batch 1）。`deflate_proof`：`reachable_inv`、`DInv.unique`（已检查）和 `deflate_call`。`Goal.deflate_sequence_safety`：`reachable_inv`、`operation_step`、`end_from_inv`（已检查）。共同前提 `TinyOverlay`（`memLevel` 1 和 2 的动态块空间）自 09f19d3f 起是定理（`tinyOverlay`，`deflate.c.engine.overlay-header-ref`），因此这条路径上不再有前提。

deflate 安全性目标尚未完成的工作（2026-11-12）。调用之间的不变量是 `DInv ∧ HeaderInv ∧ CallFacts`；对 `deflateResetKeep` 的直接调用不在定义域内（`docs/deviations.md`），其单次调用的安全性已证明（9b449103）。估计为专注小时。

| 未完成项 | 负责人 | 小时 |
| --- | --- | ---: |
| `deflate_call` 的组装：在 `TinyOverlay` 之下已检查（`deflate_call_of`、`deflate_calls_of`、`deflate_call_header`、`deflate.c.universal-call-assemble`） | inflate batch 2 | 0 |
| 策略导出 M5–M9、M13、M14、M16、M17 和 M19（`deflate_call_of` 的 `StrategyGaps`） | batch B | 10 |
| `step_params`：消去 `deflateCall`、`DeflateHeaderFact`（`SlideRepair` 已去除：`SlidChains` 取 `chainTop` 已落地） | inflate batch 1、batch C | 2 |
| `deflate` 的 `HeaderInv` 引理（头部阶段；`deflateParams`、`deflateSetDictionary`：已检查） | batch C | 8 |
| `deflate` 保持 `CallFacts`（`deflateCalls`：`deflate_calls_of`，在 `TinyOverlay` 之下已检查；其余已检查：`setDictionary_callfacts`、`params_callfacts`） | inflate batch 2 | 0 |
| 消去 `SequenceFacts`（`deflate.c.universal-sequence-safety`）并完成 `Goal.deflate_sequence_safety`。在 `TinyOverlay` 与 `FinishProgress` 之下每个字段都是定理：`sequence_facts_of`（`deflate.c.universal-call-header-fact`；`deflateHeader` 来自 `deflate_call_header`，批次 C）。已完成（09f19d3f）：`deflate_sequence_safety : Goal.deflate_sequence_safety` 和 `deflate_safety : Goal.deflate`，不带假设（`public-deflate-goals`，由 `deflate_sequence_safety_two` / `deflate_safety_two` 与 `tinyOverlayAt_128`、`tinyOverlayAt_256` 得到）。验收登记待办（`tests/audit/pending-deflate-safety.txt`，C 节）。 | inflate batch 1 | 0 |
| `TinyOverlay`：`memLevel` 1 和 2 的动态块空间（各策略引理和 `deflate_call` 的前提）。已检查，不带假设（09f19d3f）：`tinyOverlayAt_256`、`tinyOverlayAt_128`、`tinyOverlay`（`deflate.c.engine.overlay-header-ref`），来自 `header_ref_bound_256 : HeaderRefBound 245` 和 `header_ref_bound_128w : HeaderRefBound128W 29`（见 `dynamic_overlay_small` 行） | inflate batch 1 | 0 |
| `TinyOverlayAt` 的传递（inflate batch 2）：已在 `dev` 上分四片检查。`Keys.lit`（a0bdc974）；`FlushSafeAt L`、`Head.safe`，各策略引理取对应其自身 `lit_bufsize` 的实例（836987e5）；分派、缺口和调用引理以及 `deflate_call_full` 取 `OverlayAt d.lit_bufsize.toNat`（e88a305d）；`lit_cases`、`tinyOverlay_of_two` 和 `public-deflate-safety-two`：由 `TinyOverlayAt 128 ∧ TinyOverlayAt 256` 得到 `Goal.deflate`、`Goal.deflate_sequence_safety` 和四个 `compress*` 目标（4ebf31c7）。`TinyOverlay` 不变，等于 `∀ L < 512, TinyOverlayAt L`（`tinyOverlay_iff`）。不带假设的 `compress*`（4d70859a）：`compress2_z_safety`、`compress_z_safety`、`compress2_safety`、`compress_safety`，类型恰为目标类型（`public-compress-safe-mid`），基于 `DeflateReachMid`（`memLevel ≥ 3` 的 `deflateInit2_`，之后是重新设置缓冲区和 `deflate` 调用；`init2_lit`，`KeepRel` 保持 `lit_bufsize`）；`compress*` 的证明对可达性是泛型的（`CompressReach`）。另有 `goalDeflate_mid`：沿这些历史的 `Goal.deflate` 结论。`Goal.deflate` 和 `Goal.deflate_sequence_safety` 恰由 `TinyOverlayAt 128` 和 `TinyOverlayAt 256` 完成（`deflate_safety_two`、`deflate_sequence_safety_two`；公理已检查）；完成它们的提交写在 `tests/audit/pending-deflate-safety.txt` 的 C 节中。适用于所有操作的 `memLevel ≥ 3` 形式暂时搁置（监督者，2026-11-12），由 batch 1 组装这两个大小 | inflate batch 2 | 0 |
| **合计（不含未定的研究项）** | | **45** |

直接调用 `deflateResetKeep` 被排除的证据（是证据，不是证明）：inflate batch 1 的真实 C 检查器（不在仓库中；固定版本的 zlib，ASan 与 UBSan，分配块填入随机字节）在随机历史的每次调用之后检查 `dev` 上精确的 `Hashing`（`chainTop` 处的 `Chains`、`SlidChains`、滚动散列）。历史包含除直接 `deflateResetKeep` 之外的所有流操作（各种 flush 值的 `deflate`、`deflateParams`、`deflateSetDictionary`、`deflateReset`、`deflatePrime`、`deflateCopy`、`deflateTune`）。它在 461 万个状态上发现 0 次失败。操作中加入直接 `deflateResetKeep` 后，它会发现失败（300 个历史中 656 次）。检查器的运行是关于 C 的证据，不证明模型的任何性质。

| 引理 | 含义 | 状态 | 小时 |
| --- | --- | --- | ---: |
| `DInv.dgood`、`DInv.defAlloc`、`DInv.unique`、`DInv.recorded`、`DInv.bi_valid_le` | 接口：不变量给出 `DGood`、分配器、符号账目和位数上界，并确定状态（`deflate.c.universal-invariant`）。 | checked | 0 |
| `DInv.owned` | 调用历史拥有的块就是状态的五个块。 | checked | 0 |
| `DInv.rebuffer` | 调用者重新设置缓冲区后不变量仍成立。 | checked | 0 |
| `init2_version`、`init2_null` | 对每个参数的版本、流大小和 `NULL` 拒绝（`deflate.c.init.general`）。 | checked | 0 |
| `init2_main` | 每组有符号参数：拒绝、五种分配结果及其清理、成功时的 `DeflateInitial`（`deflate.c.init.general-main`）。 | checked | 0 |
| `init2_inv` | 成功的 `deflateInit2_` 建立 `DInv`（`deflate.c.universal-init`）。 | checked | 0 |
| `deflateInit2_proof` | 类型为 `Goal.deflateInit2_` 的定理（`public-deflate-init2`）。 | checked | 0 |
| `fill_window_inv` | `fill_window`：读取输入并计算校验和、滑动窗口和散列表、插入字符串、高水位边距；之后匹配器有空间，或没有输入。 | checked | 0 |
| `longest_match_inserted` | 对每个调优值都不出故障且终止；返回前瞻范围内的真实匹配。 | checked | 0 |
| `flush_block_spec` | 在非零 level、无待输出字节、输出缓冲区非 `NULL` 时的 `FLUSH_BLOCK_ONLY`：存储、固定或动态块，`send_all_trees`，在共享缓冲区内的 `compress_block`（F9），`flush_pending`，以及之后的 `DInv`。已在 `dev` 上检查：`memLevel` 3 到 9 不带前提（`flush_block_spec_mid`，`trees.c.universal-overlay-mid`；5 到 9 为 `flush_block_spec_large`），所有 `memLevel` 在 `TinyOverlay` 前提下（`flush_block_spec_of_tiny`）；一般形式以覆盖空间 `DynamicOverlay` 为前提（`flush_block_spec_of_overlay`）。`last` 是 `Bool`（0 或 1，与每个调用点一致）。在策略内部使用的显式前提形式是 `flush_block_only_safe` 和 `flush_block_dinv`；它们还给出输出总量、保持不变的输入总量以及输出的 `BufferFrame`，B 批的 `FlushSafe` 只由 `TinyOverlay` 推出（`flushSafeFrame_of_tiny`）。`TinyOverlay` 是定理（`tinyOverlay`，09f19d3f），因此 `flush_block_spec_of_tiny tinyOverlay` 对每个 `memLevel` 成立。 | checked for every `memLevel` | 0 |
| `dynamic_overlay_small` | 小 `memLevel` 时动态块的 F9：树描述和符号编码的每个前缀都留在下一个未读符号之前（`DynamicOverlay`）。`memLevel` 5 到 9 已检查（`dynamic_overlay_large`），3 到 4 已检查（`dynamic_overlay_mid`，`trees.c.universal-overlay-mid`：树的权重低于 F(16)+F(15) = 1597，因此从不截断码长，从而限制每个码的超额）。`memLevel` 1 和 2 尚未完成（`TinyOverlay`；`smallOverlay_of_tiny`，`flushSafe_of_tiny`）。在那里按码计的超额上界（388 和 856 位）加上任何可证明的树描述上界都超过预算；证明需要位长树的最优代价上界和更紧的超额上界。`tests/goals/overlay` 没有找到违反（最小间隔 58 和 161 字节）。`TinyOverlay` 在块开始处带 `BlockClear` 前提，使 `opt_len` 和 `static_len` 等于编码长度（`dynamic_opt_len`、`dynamic_static_len`，已检查）。路线：由动态选择得 `H + bitExcess ≤ 5 + G`，其中增益 `G = Σ (s_i − min(d_i, 24))`（`choice_gain`，已检查），因此 `G + 30 ≤ 8 * lit_bufsize` 给出空间（`dynamic_overlay_of_gain`，已检查，`deflate.c.engine.overlay-gain`）。用实际频率的超额上界已对 `lit_bufsize ≤ 1024` 检查：至多 `excessFibActual (lit_bufsize + 2)`，每个长度码或距离码取其频率在 Fibonacci 界下允许的最大长度（`excess_fib_actual`，`deflate.c.engine.overlay-fib-actual`）。`TinyOverlay` 由两个未证明的假设推出，以树描述上界 `Hb` 为参数（`tiny_overlay_of`，已检查，`deflate.c.engine.overlay-tiny`）：`HeaderFibBound Hb`（树描述至多 `Hb`，针对带 zlib 修复的 7 位位长树）和 `LinkC Hb`（若 `G + 30 > 8 * lit_bufsize`，则 `Hb` 加实际频率下的超额再加 25 不超过 `8 * lit_bufsize`）。路线决定（2026-11-12，`tests/goals/overlay-adversarial`）：经消毒器检查的定向构造块中没有发现覆盖；最坏顺序下的最小空间在 `memLevel` 1 为 266 位（树描述 645，超额 88），在 `memLevel` 2 为 1023 位。按普通 Fibonacci 界的 `HeaderFibBound` 不成立：zlib 对位长树的 7 位修复比 Huffman 多花（第一次搜索为 57 位，频率 24 的符号得到长度 7；在权重 ≤ 316 的任意直方图上为 136 位），因此树描述上界的形式是 `cost_zlib ≤ Σ f·κ + Δ`，其中 `κ` 是固定的完备参考码，`Δ` 是修复超额（待证明；见下面的引理表）。于是 `memLevel` 2 不需要 `LinkC`，也不需要动态选择：码长直方图上的线性规划（Kraft、Fibonacci 频率界、符号数和零游程数、按出现计的超额）用一个参考码把树描述加超额限制在 1863（预算 2023），所以 `Δ ≤ 146` 曾经足够（`certificate/header_lp.py`）；下面批次 3 更紧的规划需要 `Δ ≤ 132`。`memLevel` 1 仍未完成：带动态选择的同一规划给出 1020（预算 999），对长度 1 的码分支后为 1013（富匹配分支）；需要更深的分支或更强的 Huffman 事实。按不同码的个数分情形没有帮助：选择一侧在 70 个码时失败，树描述一侧需要同样的位长树分析。引理表（2026-11-12）。证书使用 `(dynamicHeaderBits ready mb).length ≤ 71 + Δ + Σ_k blScanCount ready k · (κ0 k + blExtraBits k)`，其中 κ0 = [2,7,7,5,5,4,4,4,4,3,4,4,7,7,7,7,7,3,7]（完备）；批次 3 的证书留给 `Δ ≤ 171`（目标 `HeaderRefBound Δ`）。批次 1，树描述上界（`lit_bufsize` 256 时的 `HeaderRefBound Δ`，Δ ≤ 171，以及 128 时的对应形式，Δ ≤ 110，分别用于 `TinyOverlayAt 256` 和 `TinyOverlayAt 128`）：H1，`build_tree` 构造的位长树（7 位修复之前）的代价不超过任何 Kraft 和 ≤ 1 的参考码：在堆树上已检查（`PShape.depth_cost_le_kraft`，`deflate.c.engine.overlay-reference`；无堆部分 `ZlibF.Math.HuffmanReference`）；H1-link 与 H2a，对每个 `max_length ≤ 15` 已检查，特别是 7 位树：`build_tree` 返回堆树、它的权重和按秩的代价上界 `Σ_r w·len ≤ Σ_r w·δ + repairExtra`（`δ` 为真实深度；`repairExtra` 是各修复步加长的秩的权重之和）（`ws_build_tree_rank_initialized`、`BTRankOrigins`、`trees.c.build.rank-cost`；无堆部分 `HuffmanAbstract.repair_cost_le`，`ZlibF.Math.HuffmanRepairCost`），再加上 H1，在树的叶子上，对每个 Kraft 和 ≤ 1 的参考码 `ℓ` 有 `Σ w·len ≤ Σ w·ℓ + repairExtra`（`BTRankOrigins.cost_le_kraft`，`trees.c.build.rank-reference`）；H2b，常数上界，已检查：在截断深度上按秩的 Fibonacci 上限（`rank_cap`，`ZlibF.Math.HuffmanRepairCap`），加上对截断直方图的生成式情形分析（叶子至多 13 个时 164 个，至多 15 个时 535 个；`ZlibF/Math/RepairCap13*`、`RepairCap15*`，生成器 `tests/goals/overlay-adversarial/certificate/repair_caps.py`，测试 `regenerate-caps.sh`）：对权重 `W ≤ 316` 的树，叶子至多 13 个时 `repairExtra ≤ 29 + W/2`，至多 15 个时 `≤ 245`（`BTRankOrigins.cost_le_kraft_cap13`、`_cap15`，`trees.c.build.rank-cap`）；因此在 128 时 `Σ w·len ≤ Σ w·ℓ + 29 + W/2`，在批次 3 的 `71 + W/2` 之内；在 256 时为 `+ 245`，在 memLevel 2 证书改用区域行和选择行后的 642 之内（在当前的 171 之内则不成立）；位长树的权重最多约 316（真实 C 上一个 `memLevel` 1 的动态块为 274），所以先前由 `W ≤ 130` 得到的 `Δ ≤ 72` 是错的；两种大小的 H3，4–8 小时，包括使用符号少于两个的树中的虚叶子。测试结果（真实 `trees.c`，对抗性位长直方图）：在 256 时，位长符号 12 到 15 不出现时找到的最大 Δ 为 55，使用全部 19 个符号时为 136；在 128 时为 14（批次 3 找到 47）；在真实块上为 13（`memLevel` 2）和 4（`memLevel` 1）。批次 3：`lit_bufsize` 128 的 R1、R2、R4、R5、R6（见本行它的部分）。批次 3，已检查：扫描计数和证书重放。在 `lit_bufsize = 256` 时每个准备好的块满足 `71 + refHeaderCost + bitExcess ≤ 1852`（`ref_header_excess_256`，`deflate.c.engine.overlay-mem2`；与堆无关的证书 `DeflateOverlayCertificate.certificate`，由 `tests/goals/overlay-adversarial/certificate/overlay_cert.py` 生成；逐条目扫描界 `scan_cost_le`；强制叶子仅在下标 ≤ 2 以及 Kraft 等式来自 `build_tree`，`trees.c.build.dummy`），因此覆盖空间只依赖一个未证明的假设 `HeaderRefBound Δ`，`Δ ≤ 171`（`dynamic_overlay_256`）。`refHeaderCost` 是扫描所得位长符号在参考码 `κ0` 下的代价。`memLevel` 1，已检查（批次 3）：在 `lit_bufsize = 128` 时，由 `HeaderRefBound128 Δ`（`Δ ≤ 132`）得到 `H + bitExcess ≤ 999`（`header_excess_128`、`dynamic_overlay_128`，`deflate.c.engine.overlay-mem1`），用到区域扫描（`scan_cost_region`）、逐码的选择行（`choice_row`）、强制叶子的两叶事实（`trees.c.build.two-leaves`）以及生成的证书 `DeflateOverlayCertificate128`（三种情形，`overlay_cert128.py`）。memLevel 2 加上区域扫描和选择行后（`DeflateOverlayCertificate256`，`dynamic_overlay_256c`，`deflate.c.engine.overlay-mem2c`）只需 `Δ ≤ 640`。因此 `TinyOverlay` 由两个树描述上界推出（`tiny_overlay_of_headers`，`deflate.c.engine.overlay-tiny-headers`）：`HeaderRefBound Δ₂`（`Δ₂ ≤ 640`）和 `HeaderRefBound128 Δ₁`（`Δ₁ ≤ 132`），κ1 = [2,8,8,6,5,4,3,4,4,3 | 7,3,3]。或者，若 memLevel 1 的修复超额随位长符号个数 `W` 增长，则由 `HeaderRefBound128W α`（`α ≤ 60`，树描述至多为 `71 + α + W/2 + refHeaderCost128`）和 `HeaderRefBound Δ₂` 推出（`tiny_overlay_of_headers_w`，证书 `DeflateOverlayCertificate128W`，`deflate.c.engine.overlay-mem1w`）。小块的码长至多为 9（128）和 11（256），见 `prepared_lengths_128`/`_256`。H3 已检查（09f19d3f，batch 1）：`BTRankLeaves`（`trees.c.build.rank-leaves`）在 `BTRankOrigins` 之上加入实际 `build_tree` 的堆叶子、返回的码长、其 Kraft 和与两叶事实；`BTRankLeaves.cost_le_15` / `cost_le_13` 在允许的符号集合上用参考码界定扫描频率在 7 位码长下的代价（至多 15 个符号时 +245，至多 13 个时 +29 + W/2），根权重等于叶子之和（`SibTree.root_weight`，`ZlibF.Math.HuffmanRootWeight`）；含强制叶子的树只有两个长度为 1 的叶子，不需要修复项。符号 12..15（256）或 10..15（128）不出现（`scanFreq_absent`、`prepared_lengths_*`），且 `W ≤ 316`（`blScanCount_mass_le`）：`header_ref_bound_256 : HeaderRefBound 245`、`header_ref_bound_128w : HeaderRefBound128W 29`（`deflate.c.engine.overlay-header-ref`），从而得到 `tinyOverlayAt_256`、`tinyOverlayAt_128`、`tinyOverlay`。 | 对每个 `memLevel` 已检查（09f19d3f） | 0 |
| `stored_spec` | `deflate_stored`：直接复制、窗口保留、缓冲的存储块；之后 `DInv`、调用者缓冲区和流记账成立（`deflate.c.universal-stored-tail`）。 | checked | 0 |
| `fast_spec`、`slow_spec` | `deflate_fast`，以及带惰性匹配的 `deflate_slow`，含流记账（`deflate.c.universal-strategy-specs`、`deflate.c.universal-slow`）。与 `rle_spec`、`huff_spec` 一样，以 C 批的 `TinyOverlay` 为唯一前提检查通过。 | checked；`TinyOverlay` 是定理（`tinyOverlay`，09f19d3f） | 0 |
| `rle_spec`、`huff_spec` | `deflate_rle` 和 `deflate_huff`，含流记账（`deflate.c.universal-strategy-specs`）。以 C 批的 `TinyOverlay` 为唯一前提检查通过（`dynamic_overlay_small` 中 `memLevel` 1、2 的未决情况）。 | checked；`TinyOverlay` 是定理（`tinyOverlay`，09f19d3f） | 0 |
| `call_frame` | 一次 `deflate` 调用保持 level、`w_bits`、`hash_bits` 和 `gzhead`，只在有输出时改变 `wrap`；在 `INIT_STATE` 或 `GZIP_STATE` 的 zlib 或 gzip 流上，未被拒绝的调用至少交付一个字节（供 `bound_before_output` 使用）。 | open | 4 |
| `deflate_header_trailer` | 一次 `deflate` 调用的组成部分，以针对翻译的配套引理形式给出，每个都对所有参数保持 `DGood`、`TreesInvAt` 与调用方缓冲区：入口刷新（`deflate.c.universal-call-entry`）；串成 `header_phase` 的头部各阶段（`deflate.c.universal-call-headerphase`），适用于每个入口状态，`HeaderEntry` 由 `ActiveHeader` 推出（`fresh_header_entry`、`resumed_header_entry`）；刷新标记（`marker_tail`）；尾部（`trailer_phase`）。每个部分还给出供 `deflate_call` 使用的堆框架：`StageFrame`（`deflate.c.universal-call-stageframe`：计数、总量、输出的 `BufferFrame`、堆形状，只有流根、状态记录、`pending_buf` 和输出块改变；`StageFrame.call_facts`），刷新标记用 `MarkerFrame`（`CLEAR_HASH` 之后 `head` 块可以改变），记录形状 `HeaderShape`，`HeaderInv d → HeaderInv d'`，以及提前返回 `Z_OK` 时 `last_flush = -1`。提升到 `DInv` 属于 `deflate_call`（`DInv.lift_empty`，2 号负责人）。 | checked | 0 |
| `deflate_call` | 一次 `deflate` 调用（进出均为 `DInv ∧ HeaderInv ∧ CallFacts`）：拒绝、分派到各策略、各部分的组装、`Goal.deflate` 的每个条款（包括 `Z_FINISH` 进展条款），以及所拥有的块保持不变。`deflate_call_full`（`deflate.c.universal-call-assemble`）组合了 `KeepRel` 框架（`-call-keep-*`）、入口阶段（`-call-entry-all`）、提前返回（`-call-early`）、由调用前不变量得到的头部步骤（`-call-headerstep`）、策略、标记和尾部的收尾部分（`-call-tail`、`-call-tailstep`），以及两种入口情形（`cont_empty`、`cont_pending`）。推论：`deflate_call_of : DeflateCallFact`、`deflate_calls_of : DeflateCallsFact`、`deflate_call_header`（调用之后的 `HeaderInv`）。唯一假设：`TinyOverlay`（batch C）。 | checked given `TinyOverlay` | 0 |
| `operation_step` | 其他每个流操作在其帧条件下保持不变量：`deflateParams`（内部的 `deflate(Z_BLOCK)`、滑动或清空）、`deflateSetDictionary`、`deflatePrime`、各种重置、`deflateSetHeader`、`deflateTune`、查询和上界。负责人：`deflateSetDictionary` 和 `deflateParams` 为 inflate 1 批（接自 B 批；`deflate.c.universal-ops-dictionary`、`-params` 为 B 批所写，`-dictionary-slid`、`-params-general`）；`deflatePrime`、各种重置和分派为 1 批（`-prime`、`-reset`、`-dispatch`）；其余为 deflate 负责人（`deflate.c.universal-ops`）。已作为 `operation_step_of` 检查（`deflate.c.universal-ops-dispatch`），即带以下假设的分情况组合：`deflate_call` 加上调用保持状态的五个所属块这一条款（骨架陈述缺少它；分配账需要它）、`step_setDictionary` 和 `step_params`（后者读取 `CallFacts`），头部事实 `HeaderInv` 与调用之间的事实 `CallFacts`。`deflateGetDictionary` 的缓冲区可以是任意可写的调用者范围：字节块，或另一个 deflate 状态记录的 `depth` 数组（`step_getDictionary`，`deflate.c.universal-ops-caller-view`，框架论证）。 | checked given hypotheses | 0 (dispatch) |
| `step_params` | `deflateParams` 在每种情况下保持不变量（`deflate.c.universal-ops-params-general`；拒绝和无需冲刷的修改为 B 批所证，`-params`）：首次 `deflate` 调用之前的修改；先 `deflate(Z_BLOCK)`，再做冲刷检查（`Z_STREAM_ERROR`、`Z_BUF_ERROR` 时为该调用的堆）或修改；以及 level 0 的修复（一次待处理滑动用 `slide_hash`，更多用 `CLEAR_HASH`）。配套引理 `params_header`、`params_callfacts` 和 `params_body`。负责人：inflate 1 批。假设：与 `operation_step_of` 相同的 `deflate_call`（配套引理还需 `deflate` 的头部阶段或其 `CallFacts`），以及入口状态的 `CallFacts d`（首次 `deflate` 调用之前的 P1 和 P1b；P2、P3、P6 来自 `Shape`）。有一次待处理滑动时，`SlidChains` 在 `chainTop` 处成立（`DInv`），因此 `slide_hash` 之后的修复是同余（`slide_repair`）。 | checked given hypotheses | 0 |
| `step_setDictionary` | `deflateSetDictionary` 在每种情况下保持不变量（`deflate.c.universal-ops-dictionary-slid`；`matches = 0` 时的主体为 B 批的 `setdict_body`）。头部配套引理 `setDictionary_header`（即 `SequenceFacts.setDictionaryHeader` 的陈述）和 `setDictionary_body`。负责人：inflate 1 批。level 0 且有待处理存储滑动（`matches` 为 1 或 2，B 批的 Finding 1）的情况为 `slid_body`：通过表视图运行主体（`setdict_body_v`，`deflate.c.universal-ops-dictionary-view`；`fill_window_input_v`，`deflate.c.universal-window-view`；`deflate.c.engine.view-chains`），一次滑动用滑动视图，两次滑动不需要链事实。插入的位置在滑动视图中为 `str - w_size` 或 `NIL`，永远不会被跟随（`chains_insert_slid`）。视图使用当前 `SlidChains` 的插入前沿 `strstart - insert`；若 `SlidChains` 改用 `chainTop`（Finding 2），结束时的前沿须随之调整。无前提。 | checked | 0 |
| `resetKeep_single` | 从 `DInv` 直接调用一次 `deflateResetKeep`（不在序列定义域内，这是 deflate 负责人设定的偏差）：无故障，返回 `Z_OK`，写入恰为流记录和状态记录（`rkZ`、`rkPost`）；窗口、`prev`、`head`、`pending_buf` 不变，无分配；拒绝情况为 `resetKeep_refuse`（`deflate.c.universal-ops-resetkeep`）。负责人：inflate 1 批。 | checked | 0 |
| `step_reset` | `deflateReset` 在其帧条件下保持不变量（`deflate.c.universal-ops-reset`）。`deflateResetKeep` 部分 `step_resetKeep` 受阻：`deflateResetKeep` 之后 `DInv.Hashing` 不成立（已报告）。该调用保留 `strstart`、`insert` 和散列表，但令 `lookahead = 0`，于是位于 `strstart - 1` 和 `strstart - 2` 的链头高于 `chainTop`。 | checked（`deflateReset`）；blocked（`deflateResetKeep`） | 2 |
| `step_prime` | `deflatePrime` 在尚未开始的流上保持不变量：待输出字节的前移和位循环（`deflate.c.universal-ops-prime`）。它使用 `DInv` 之外的头部事实 `HeaderInv`（头部写出前没有已记录的符号）。 | checked | 0 |
| `copy_inv` | `deflateCopy` 使目标满足不变量（`deflate.c.universal-ops-copy`）：成功路径（`copy_cut`；失败路径返回 `Z_STREAM_ERROR` 或 `Z_MEM_ERROR`）、新块、复制到 `high_water` 的窗口、`prev` 的部分复制（`chains_copy`；先在真实 C 上测试：21005 次复制中没有一个被跟随的链槽位于未复制部分）。 | checked | 0 |
| `operation_header` | 头部事实 `HeaderInv`（头部状态下没有已记录的符号；从 `EXTRA_STATE` 到 `HCRC_STATE` 附有 gzip 记录）在每个流操作之后成立。已在 `dev` 上检查（`deflate.c.universal-header-inv`）：`init2_header`、`tune_header`、`setHeader_header`、`reset_header`、`prime_header`。未完成：`deflateSetDictionary`（需要 B 批 `setdict_body` 给出状态字段）、`deflateParams`，以及 `deflate` 本身（头部阶段）。已作为 `operation_header_of` 检查（`deflate.c.universal-ops-header`），即对每个操作分情况，带以下假设：`deflate`、`deflateParams`、`deflateSetDictionary` 的头部引理，以及前提 `CallFacts`（`params_header` 读取它）。对 `deflateResetKeep` 的直接调用不是流操作。 | checked given hypotheses | 0 (case split) |
| `operation_callfacts` | 调用之间的事实 `CallFacts` 在每个流操作之后成立。已检查（`deflate.c.universal-ops-callfacts`，inflate 1 批）：`reset_callfacts`、`prime_callfacts`、`tune_callfacts`、`setHeader_callfacts`、各查询（状态不变）、`copy_callfacts`（`-ops-copy`）；初始化时由 `init2_inv` 给出。`setDictionary_callfacts`（`-ops-dictionary-slid`）、`params_callfacts`（`-ops-params-general`，在 `SlideRepair` 之下）。已作为 `operation_callfacts_of` 检查，带 `deflate` 的假设。 | checked given hypotheses | 2 |
| `copy_header` | `deflateCopy` 复制状态记录，因此副本中 `HeaderInv` 成立（`deflate.c.universal-ops-copy`，骨架陈述）。 | checked | 0 |
| `copy_failure` | 某次分配失败的 `deflateCopy`（状态记录失败，或四个缓冲区请求的任意子集失败，它们都在空指针检查之前执行）返回 `Z_MEM_ERROR`，释放它分配的每个块，清除 `dest->state`，并保持源与其他活跃块不变（`deflate.c.copy-failure`）。 | checked | 0 |
| `copy_success` | 所有分配都成功时，`deflateCopy` 返回 `Z_OK`：目标满足 `DGood`，其状态为 `copiedDeflate`，窗口、`head`、`prev` 的已复制部分、待发字节和符号都被复制，账目恰好增加五个新块（`deflate.c.copy-success`，来自 `copy_tail_run`）。 | checked | 0 |
| `deflate_copy_public`、`deflate_copy_safety`（`public-deflate-copy`） | 类型为 `Goal.deflateCopy` 与 `Goal.deflateCopy_safety` 的定理：空参数被拒绝；从可达源出发，由 `copy_failure` 或 `copy_success` 得出。陈述先在真实 C 上测试（`tests/goals/deflate-copy`：144000 种组合，五次分配的每个失败子集，无违例）。`Goal.deflateCopy_safety` 还包含 zlib.h 对不一致源的拒绝（`deflateCopy_refused`）。已登记，带五个结构性公开变异（`tests/proof-mutants/public-streams.tsv`），每个都被内核重放拒绝。 | checked | 0 |
| `inflate_refusal`、`deflate_refusal`（`public-stream-refusal`） | 类型为 `Goal.inflate_refusal` 与 `Goal.deflate_refusal` 的定理：`NULL` 或不一致的流（state 为 `NULL`、`zalloc` 或 `zfree` 为 `NULL`，或检查拒绝的存活状态）被 `inflate`、`inflateEnd`、`inflateReset`、`inflateReset2`、`inflateGetDictionary`、`inflateSetDictionary`、`inflateCopy`、`deflate`、`deflateSetDictionary`、`deflateParams`、`deflateGetDictionary` 与 `deflateCopy` 以 `Z_STREAM_ERROR` 拒绝，且不做任何改变（`inflate` 创建并释放其局部数组；复制会清除 `dest->state`）。陈述先在真实 C 上测试（`tests/goals/stream-refusal`：192 次调用，无违例）。已登记；拒绝变异在 `tests/proof-mutants/stream-refusal.tsv` 中。 | checked | 0 |
| `reachable_inv` | 对 `StreamReachable` 归纳：每个可达状态都满足 `DInv`、`HeaderInv` 和 `CallFacts`（`reachable_inv_of`，`deflate.c.universal-sequence-safety`）。 | checked in skeleton | 0 |
| `deflate_proof` | 类型为 `Goal.deflate` 的定理。已检查为 `deflate_proof_of (facts : SequenceFacts) : Goal.deflate`（`deflate.c.universal-deflate-proof`）：`reachable_inv_of`、`DInv.unique`、字段 `deflateCall`。一旦 `SequenceFacts` 的字段都成为定理，它就是 `Goal.deflate`。`CallFacts.finishBits`（M18）已检查。 | checked given hypotheses | 0 |
| **小计 `Goal.deflateInit2_` 与 `Goal.deflate`** | | | **150** |
| `end_from_inv` | 由不变量得到 `deflateEnd`（复用 `deflate_end_public`）。`deflate.c.universal-end`。 | checked | 0 |
| `Ledger` | 账目的最终设计：头部、块前缀、当前块（符号或存储的窗口字节）、惰性字面量、窗口内容、已结束的流。 | 不计划（范围：安全性） | 0 |
| `ledger_init`、`ledger_rebuffer` | 初始化建立账目；重新设置缓冲区保持它。 | 不计划（范围：安全性） | 0 |
| `ledger_dictionary` | 数据之前的预置字典：窗口与 `DICTID`。 | 不计划（范围：安全性） | 0 |
| `ledger_flush_pending` | 待输出刷新把待输出字节交给调用者；账目的含义不变。 | 不计划（范围：安全性） | 0 |
| `ledger_header` | 头部阶段：带 `DICTID` 的 zlib 头部或 gzip 头部，可被中断；结束于尚无块的数据阶段。 | 不计划（范围：安全性） | 0 |
| `ledger_fill_window` | `fill_window`：读入的字节并入已接受输入和前瞻；滑动保持窗口与数据的对应和块起点。 | 不计划（范围：安全性） | 0 |
| `ledger_block_fixed` | 固定块（`FLUSH_BLOCK_ONLY`）解码为当前块的符号，非最终块或最终块。 | 不计划（范围：安全性） | 0 |
| `ledger_block_dynamic` | 动态块解码为当前块的符号（树描述与编码）。 | 不计划（范围：安全性） | 0 |
| `ledger_block_stored` | 来自窗口的存储块解码为该块的窗口字节。 | 不计划（范围：安全性） | 0 |
| `ledger_fast` | `deflate_fast`：记录的符号表示其覆盖的输入，跨越填充和块刷新。 | 不计划（范围：安全性） | 0 |
| `ledger_slow` | `deflate_slow`，含惰性字面量。 | 不计划（范围：安全性） | 0 |
| `ledger_rle` | `deflate_rle`。 | 不计划（范围：安全性） | 0 |
| `ledger_huff` | `deflate_huff`。 | 不计划（范围：安全性） | 0 |
| `ledger_stored` | `deflate_stored`：缓冲的存储块和直接复制到调用者。 | 不计划（范围：安全性） | 0 |
| `ledger_align` | `Z_PARTIAL_FLUSH`：`_tr_align` 追加一个空固定块。 | 不计划（范围：安全性） | 0 |
| `ledger_empty_stored` | `Z_SYNC_FLUSH`/`Z_FULL_FLUSH`：一个空存储块；完全刷新后清空散列。 | 不计划（范围：安全性） | 0 |
| `ledger_trailer` | 尾部由校验和与计数补全数据流。 | 不计划（范围：安全性） | 0 |
| `ledger_step` | 沿 `deflate_phases` 组装以上各引理，含拒绝和 `Z_BUF_ERROR` 返回。 | 不计划（范围：安全性） | 0 |
| `trace_ledger` | 对 `DeflateDataTrace` 归纳。 | 不计划（范围：安全性） | 0 |
| `ledger_finished` | 已结束的数据段解码为其输入（`DecodesFor`）。 | 不计划（范围：安全性） | 0 |
| `ledger_flush` | 完成的同步或完全刷新：输入已消耗、`FlushedFor`、完全刷新后可以重新开始。 | 不计划（范围：安全性） | 0 |
| `ledger_adler` | `adler` 是已接受输入的校验和。 | 不计划（范围：安全性） | 0 |
| `bound_before_output` | 输出之前，`deflateBound` 和 `deflateBound_z` 返回模型上界。已检查部分：每次返回的 `deflate` 调用都保持每个状态记录的 `level`、`w_bits`、`hash_bits`、`gzhead`、`strm`、`|wrap|` 和有效状态（`par_deflate`，`deflate.c.universal-params-deflate`）。尚未完成：`deflateSetDictionary` 的同一框架（及其对 `strstart` 的影响），以及在新的 zlib 或 gzip 流上被接受的调用会产生输出这一事实（已请批次 D 提供）。 | 不计划（范围：安全性） | 0 |
| `completes` | `DeflateCompletes`：每种策略和块选择在最坏情况下的膨胀都不超过上界，多次 `Z_FINISH` 调用时也是如此。 | 不计划（范围：安全性） | 0 |
| `deflate_sequence_proof` | 类型为 `Goal.deflate_sequence` 的定理。 | 不计划（范围：安全性） | 0 |
| `deflate_sequence_safety_proof` | 类型为 `Goal.deflate_sequence_safety`（`StreamSequenceSafety .deflate`）的定理，由 `reachable_inv` 和 `operation_step` 得到。 | checked in skeleton | 0 |
| **小计 `Goal.deflate_sequence_safety`** | | | **0** |
| `compress*` | `Goal.compress*_safety`（`CompressorSafety`，即 `CompressorContract` 的安全性一半）：已在 `public-compress-safe*` 中证明（`compress2_z_safety_of`、`compress2_safety_of`、`compress_z_safety_of`、`compress_safety_of`），前提是两个显式假设 `Goal.deflate` 和 `DeflateLoopFacts`；`deflateInit_` 和 `deflateEnd` 经由其已证引理进入。终止：度量（未读源字节加未填空间）低于循环燃料，并在每次 `Z_OK` 调用后下降：`Z_NO_FLUSH` 时依据 `DeflateLoopFacts`（该调用有输入），否则依据 `Goal.deflate` 的 `Z_FINISH` 进展条款。`Goal.deflate` 和 `DeflateLoopFacts` 一经证明，每个定理一行即可完成。仅在 `TinyOverlay` 之下：`compress2_z_safety_tiny`、`compress2_safety_tiny`、`compress_z_safety_tiny`、`compress_safety_tiny`（`public-compress-safe-call`，已检查）。`compress*_safety_of_tiny` 的两个调用事实是 `deflate_call_full` 的条款：`CallProgress`（`call_progress_of`：处于 `FINISH_STATE` 之前、有输入和输出空间且被接受的调用会改变 `avail_in` 或 `avail_out`）和 `CallKeepsGzhead`（`call_keeps_gzhead_of`：`KeepRel.gz`，该调用的每次状态写入都保持 `gzhead`）。`compress` 的 `memLevel` 为 8，`TinyOverlay` 在那里从不适用，但 deflate 链把它作为全局假设。 | checked（有条件） | 0 |
| `DeflateLoopFacts`（deflate 负责人） | `Goal.deflate` 未陈述的关于一次 `deflate` 调用的四个事实：有输入和空间的 `Z_NO_FLUSH` 调用有进展；第一次 `Z_FINISH` 之后的新输入返回 `Z_BUF_ERROR` 或写出至少一个字节；每次调用都保持 gzip 头指针和所拥有的块（`public-compress-safe-init`）。已在 `public-compress-loop-facts`（`deflate_loop_facts_of`）中由骨架陈述 `reachable_inv`、`deflate_call`（`CallClauses`）、`call_frame` 以及 `FinishedNewInput`（第一次 `Z_FINISH` 之后的新输入）推出；后者已在 `public-compress-finished` 中针对翻译证明（`finished_new_input`，依据入口阶段引理和 `flush_pending` 的框架）；`deflate_loop_facts` 只需三条骨架陈述。 | checked（有条件） | 0 |
| **合计** | | | **150** |

第 C 批，为 `call_frame` 与 `deflate_header_trailer` 准备的 gzip 头阶段。`Goal.deflate` 曾允许 gzip 头的 name 或 comment 与本次调用写入的字节重叠：输出范围，或流的 `pending_buf`。在真实 C 上，一次刷新或一个头字节会覆盖字符串的 NUL，name 循环越过缓冲区读取（`tests/regression/deflate-gzip-name-output`，两种布局都在 sanitizer 下复现）。zlib.h 没有说明这两种布局是否允许。目标现在通过 `ActiveHeader` 的合取项 `DeflateHeaderApart` 排除二者（`docs/deviations.md`）：写头期间，输入、输出、extra 字段、name 与 comment 两两为分离的字节范围，头区域位于流自身的存储之外。

可交给其他负责人的独立批次。每个批次只依赖其他批次在 `skeleton/deflate` 上的引理陈述，而不依赖其证明，并且放在各自的文件中。不变量 `DInv` 及其接口属于批次 A；对 `DInv` 的改动要通知其他批次。

| 批次 | 引理 | 文件 | 小时 |
| --- | --- | --- | ---: |
| A. 初始化与调用历史（操作：`deflateSetDictionary`、`deflateParams` 由 batch B 负责人负责；`deflatePrime`、重置、`copy_inv` 和 `operation_step` 的分情况组合由 inflate batch 1 负责人负责） | `init2_inv`、`DInv.owned`、`DInv.rebuffer`、`operation_step`、`copy_inv` | `deflate.c.init.general`、`deflate.c.universal-ops` | 67 |
| B. 窗口与策略 | `fill_window_inv`、`longest_match_inserted`、`stored_spec`、`fast_spec`、`slow_spec`、`rle_spec`、`huff_spec` | `deflate.c.universal-window`、`deflate.c.universal-strategies` | 0 |
| C. 块输出与上界 | `flush_block_spec`、`bound_before_output`、`completes`、`call_frame`、`end_from_inv`、`deflate_header_trailer` | `trees.c.universal-block`、`deflate.c.universal-bound` | 156 |
| D. 调用与账目 | `deflate_call`、`Ledger`、`ledger_init`、`ledger_rebuffer`、`ledger_dictionary`、`ledger_step` 及其 14 个部分（`ledger_header` … `ledger_trailer`）、`ledger_finished`、`ledger_flush`、`ledger_adler` | `deflate.c.universal-call`、`deflate.c.universal-ledger` | 227 |

`compress*`（12 小时）在 A 到 D 都检查通过后进行。

批次 B 或 C 负责人的接口。从分支 `skeleton/deflate` 的文件 `ZlibF/Proof/deflate.c.universal.lean` 开始。

- **陈述。** B：第 4 节，`stored_spec` 到 `huff_spec`（`fill_window_inv` 和 `longest_match_inserted` 已检查）。C：第 4 节的 `flush_block_spec`；第 7 节的 `bound_before_output` 和 `completes`（其陈述是 `ZlibF/Spec/Public/Sequences.lean` 中的 `DeflateCompletes`）。
- **引理可以假设什么。** 不变量 `DInv` 和 `StrategyEntry`（在 `dev` 上，`deflate.c.universal-invariant`）、引理中写明的其他前提，以及 `dev` 上已检查的模块：`deflate.c.engine.chains`、`lmbody`、`macros`、`trees.c.*` 各模块和 `ZlibF/Math/Deflate*`。B 可以使用骨架中 `flush_block_spec` 的陈述；骨架中的其他内容都不是前提。
- **修改 `DInv`。** `DInv` 属于批次 A。如果证明需要 `DInv` 没有携带的事实，把它写成该引理的前提并告知 A；由 A 把它加入 `DInv` 并证明每个操作都保持它。不要直接修改 `DInv` 或其他批次的陈述。
- **文件。** 证明放在该批次自己在 `dev` 上的文件中（见上表）；之后骨架用已检查的定理替换其 `sorry`。

需要注意的耦合：B 和 C 的陈述只涉及安全性。批次 D 还需要它们的功能内容（B：已记录符号的含义；C：输出的块解码为其符号）。D 会在 B 或 C 进行到那里之前，把这些配套引理写在安全引理旁边；证明某段执行的负责人最适合同时证明其配套引理。`completes` 需要每个块的输出大小（C）以及每种策略在多次 `Z_FINISH` 调用中的行为（B），因此是最不独立的引理；应在 `flush_block_spec` 和策略引理之后再开始。

现有证明族与骨架的对照：

| 证明族 | 决定 |
| --- | --- |
| `deflate.c.engine.chains`、`lmbody`、`macros` 以及滑动与插入引理 | 已经是参数化的（窗口 2^9 到 2^15，任意散列参数）。适用于 `fill_window_inv` 和 `longest_match_inserted`。保留。 |
| `deflate.c.engine.*` 中的默认、common 和 generic-foreign 调用历史（`DefaultDataTrace`、`Common*DataTrace`、`EngineStart`） | 绑定于窗口 15、`memLevel` 8、策略 0 或 level 6，无法服务于通用引理。待这些引理检查通过后删除，但已登记定理需要的文件除外（约 60 个已登记的引擎定理）。 |
| `deflate.c.init.*` | 固定的缓冲区大小。默认证明是 `init2_main` 的模板；推广它。保留 `deflateInit_proof` 需要的默认模块。 |
| `trees.c.*` | 对块及其描述符参数化（`gen_codes`、`build_tree`、`scan_tree`、`build_bl_tree`、`send_tree`、`send_code` 已检查）。适用于 `flush_block_spec`；剩下 `send_all_trees`、`compress_block` 和 F9。保留。 |
| `ZlibF/Math/Deflate*`、`Huffman*` | 与堆无关：符号及其含义、块前缀、重叠与预算上界、Huffman 深度上界。适用于账目和 F9。保留。 |

#### gz

gzip 文件接口的安全（第 5 项结论，所有者 2026-11-12 的决定）：在一个句柄的每条调用历史上，没有未定义行为、没有内存错误、不泄漏内存块或描述符，并且一定终止。骨架在分支 `skeleton/gz` 的提交 `7d896179` 上，文件为 `ZlibF/Proof/gz.skeleton-model.lean`、`gz.skeleton.lean`、`gz.skeleton-read.lean` 和 `gz.skeleton-write.lean`。它能通过类型检查：`Goal.gz_sequence_safety` 在其中由下列未完成引理证明。该目标涵盖每一种打开（`gzopen`、`gzopen64`、`gzdopen`）、`GzOperation` 的每个公开调用、每次关闭、句柄之外的调用者修改，以及两次调用之间文件系统世界的变化。`GzInv`（`GzCommon`、`GzReadInv`、`GzWriteInv`）是打开句柄的表示不变式；就安全而言，`GzHistory` 取代 `GzReachable`。

会改变骨架的待定输入：

- 操作系统调用的预言机（M1–M5、M7：`read`、`write`、`lseek`、`close`、`open` 可以返回其契约允许的任何结果）是对 `Fs` 的一项拟议修改，设计正在审查中。在它落地之前，目标只覆盖确定性的普通文件世界，`ReadsFinite`（读取类调用终止部分的 M7 前提）为 `True`。
- 本地补丁 0004 及以后（发现 F-1 和 W7：`gz_read` 与 `gz_write` 中 `x.pos` 溢出；R-3：`gz_reset` 不写 `x.next`；R-4：`x.next` 留在调用者的缓冲区中）在分支 `worker/gz-patches` 上，与 0002（R-1）和 0003（R-2）并列。注明“依赖补丁”的引理对当前翻译不成立；它们在补丁落地、骨架变基之后证明。

| 引理 | 含义 | 状态 | 小时 | 负责人 |
| --- | --- | --- | ---: | --- |
| `GzOracle.fsReadO_contract` .. `fsOpenO_fresh`、`regular_instance_*`（10 个）、预言机修改以及 16 个 gz 证明的移植 | M1–M5 和 M7 对每个预言机取值都成立；现在的 `Fs` 是默认实例。 | 未完成（设计审查中） | 18–24 | batch 1 |
| `GzInv.caller` | 句柄之外的调用者修改保持 `GzInv`（编解码器的 rebuffer）。 | 未完成 | 3 | batch 1 |
| `GzInv.gz_error` | `gz_error` 保持 `GzInv`；旧消息被释放，产生新消息或 `Z_MEM_ERROR`。已检查（`gzlib.c.error-inv`、`gzlib.c.error-inv-premises`）：`GzInv.gz_error_full` 覆盖每条路径（包括预言机拒绝和 `2^63` 字节处的拒绝；对消息长度没有 `INT_MAX` 限制），并有不抢占事实 `GzInv.gz_error_own`；`gzwrite.c.init`、`gzread.c.getc-ungetc` 和 `gzread.c.skip-gets` 的前提 `GzErrorSpec` 与 `GzErrorOwn` 在那里得到证明。 | 已检查 | 0 | deflate 负责人 |
| `GzInv.gz_reset` | `gz_reset` 保持 `GzInv`，并清空输出、位置和 skip（R-3 补丁）。 | 未完成 | 2 | batch 1 |
| `GzInv.put_scalars` | 保持各条款的标量字段写入保持 `GzInv`。 | 未完成 | 4 | batch 1 |
| 其他接口引理（窗口、编解码器步骤） | 按负责人的需要。 | 未完成 | 2 | batch 1 |
| `gzopen_safe` | `gzopen` 返回；NULL 不留下任何东西；句柄满足 `GzInv`，且只有它的描述符是新的。 | 未完成 | 6 | batch 1 |
| `gzdopen_safe` | 同上，不打开也不关闭任何描述符。 | 未完成 | 2 | batch 1 |
| `gzclose_dispatch_inv` | `gzclose` 按模式即 `gzclose_r` 或 `gzclose_w`。 | 未完成 | 1 | batch 1 |
| `gzseek64_step` | 在 `GzInv` 上定位是安全的（补丁 0002，以及 R-3、R-4、F-1 补丁）。已在 `2380e023` 检查（`gz.inv-seek`），连同 `gzseek_step`，对预言机的每个世界成立；回归 `gz-seek-pos-have` 表明需要 `GzReadInv.posHave`。 | 已检查 | 0 | batch 1 |
| `gztell64_step`、`gztell_step` | 查询位置是安全的；什么都不变。 | 未完成 | 2 | batch 1 |
| `gzbuffer_step`、`gzerror_step`、`gzclearerr_step`、`gzoffset64_step`、`gzoffset_step`、`gzrewind_step` | 已登记的查询在 `GzInv` 上重新陈述。 | 未完成 | 6 | batch 1 |
| 在补丁 0002–0004+ 上变基，审查陈述 | | 未完成 | 4 | batch 1 |
| `history_inv`、`operation_safe`、`close_safe`、`gz_sequence_safety`、`gzclose_step`、`gzseek_step`、`gzeof_step`、`gzopen64_safe` | 组装。 | 已检查（骨架） | 0 | batch 1 |
| `gz_load_safe` | `read` 循环（M1）：`-1` 或 `0`，`have ≤ len`，只写缓冲区。已检查为 `gz_load_safe`（`gz.read-load-error`）：`fsRead_contract`（M1，对预言机的每个取值）、`gz_load_paths`（`gz.read-store`：循环和返回 `0` 的收尾路径）以及 `gz_load_error_tail`（经由 `gz_error_upToOutput`（`gzlib.c.error-inv-rec`）的 `gz_error(Z_ERRNO, strerror)` 报告）。发现的前提：`size ≠ 0`（读取停滞会置 `again`），缓冲区是数据缓冲块或不属于句柄，以及 `eof ≠ 0 → avail_in = 0`（停滞保留 `eof`；`GzReadInv.againEof`）。 | 已检查 | 0 | 读取侧（deflate 负责人） |
| `gz_avail_safe` | 重新填充 `in`；保持输入窗口。已检查（`gz.read-avail`）：压缩复制（`copy_loop`、`copy_run`；对每个调用者都是死代码，但仍然证明）、在待处理输入之后的 `gz_load_safe`，以及新的窗口（`GzInv.set_input`）；记录只在标志、错误、消息和窗口上改变（`AvailRec`）。前提：读取句柄（`s.mode = GZ_READ`）。为此 `gz_load_safe` 现在也陈述调用后的记录。 | 已检查 | 0 | 读取侧（deflate owner） |
| `gz_look_safe` | 延迟分配的缓冲区与 `inflateInit2`，失败时的账目，COPY 复制。已检查（`gz.read-look`）：`gz_look_safe : GzLookSpec` 覆盖每条路径（`in`/`out` 的分配和 `inflateInit2_` 及其每种失败、重置分支、`gz_avail`、魔数检查、gzip 分支、透明 COPY）。后置条件 `GzInvOut`（COPY 的输出可越过 `GZ_OFF_MAX`）；前提 `how = LOOK`。 | 已检查 | 0 | 读取侧（deflate owner） |
| `gz_decomp_safe` | inflate 历史中的 inflate 步骤；`x.next` 在输出窗口内。已作为 `gz_decomp_safe_of (head : InflateHeadUsesInput) : GzDecompSpec`（`gz.read-decomp`）检查：在嵌入流上调用 `gz_avail` 和 `inflate` 的循环（`inflate_public`；记录只在其流上改变，流消息保持为 NULL 或字面量，由 inflate 整次运行框架的新 `Keeps` 条款 `gz` 与 `msgs` 给出），在 `ReadsFinite` 下终止，错误分支经由 `gz_error`。未完成的前提 `InflateHeadUsesInput`：从模式 `HEAD`、`bits = 0`、`last = 0` 且有输入时的一次 `inflate` 调用会消耗输入（需要一个说明输入计数从不回升的框架）。 | 已检查（基于一个前提） | 3 | 读取侧（deflate owner） |
| `gz_fetch_safe` | 分派函数；在 M7 下终止。陈述 `GzFetchSafe`（`gz.read-fetch-specs`）：后置条件 `GzInvOut`（输出可越过 `GZ_OFF_MAX`，直到调用者丢弃它），在 `ReadsFinite`（预算小于 `2^61`）下终止，前提 `err ≠ Z_STREAM_END` 与 `how = COPY → avail_in = 0`（将成为不变量条款）。已作为 `gz_fetch_safe_of`（`gz.read-fetch`）从 `GzLookSpec` 和 `GzDecompSpec` 检查；二者证明后即闭合。 | 已检查（基于被调用者前提） | 1 | 读取侧（deflate owner） |
| `gz_skip_have_safe` | 消耗缓冲中的 skip 字节（`gzread.c.skip-have`，09fe8c0f；以及 `GzInv.put_consume`）。 | 已检查 | 0 | 读取侧（batch 3） |
| `gz_skip_safe` | skip 循环；在 M7 下终止。已检查为 `gz_skip_safe_of`（6c974c42），前提是 `gz_fetch_safe`、两个请求的 `gz_fetch` 事实（进展、保持 size）和 `gz_error` 的不占用事实；这些证明后即完成。 | 已检查（基于被调用者前提） | 1 | 读取侧（batch 3） |
| `gz_read_safe` | 三条路径，调用者区域，重置 `x.next`（R-4），`x.pos`（F-1）。 | 未完成 | 12 | 读取侧（deflate owner） |
| `gzread_step`、`gzfread_step` | 包装函数。 | 未完成 | 4 | 读取侧（deflate owner） |
| `gzgetc_step` | 读取一个字节的 `gz_read` 包装函数（`gzgetc__step` 已在骨架中检查）。按现在的 `GzInv` 不成立（有缓冲字节时的 skip 请求）；不变式由 batch 1 决定。 | 未完成 | 2 | 读取侧（batch 3） |
| `gzungetc_step` | 在 `out` 内回退。已检查为 `gzungetc_step_of`（b7e5cc07），前提是加了两项请求的 `gz_look_safe`、`gz_skip_safe_of'` 和 `gz_error`。 | 已检查（基于被调用者前提） | 1 | 读取侧（batch 3） |
| `gzgets_step` | 有界的 `memchr`、复制、NUL。 | 未完成 | 6 | 读取侧（batch 3） |
| `gzdirect_step` | 一次 `gz_look` 和 `gz_skip_have`（R-3、R-4）。 | 未完成 | 3 | 读取侧（batch 3） |
| `gzclose_r_step` | `inflateEnd`、释放、释放描述符。已作为 `gzclose_r_step_safe`（`gz.read-close`）检查：对每个世界不出错；结果为 `Z_OK`、`Z_BUF_ERROR` 或 `Z_ERRNO`；句柄拥有的每个块都被释放且其余不变（`Frame`、精确的 `LiveChange`）；即使 `close` 返回 -1 描述符也被关闭，其他描述符不变。`GzCloseSafe`/`GzReleased` 暂时在本地写出（`Close.Released`），直到骨架模型进入 dev。 | 已检查 | 0 | 读取侧（deflate owner） |
| `gz_init_safe` | W2 到 W3、W5、W6；失败时的账目。 | 未完成 | 6 | batch C |
| `gz_comp_safe` | 写循环（M2）、deflate 循环（`deflate_quiet`）、重置。 | 未完成 | 16 | batch C |
| `gz_zero_safe`、`gz_write_safe`、`gz_vacate_safe` | 保持 W4；`x.pos`（W7 补丁）。 | 未完成 | 18 | batch C |
| `gzwrite_step`、`gzfwrite_step`、`gzputc_step`、`gzputs_step` | 包装函数。 | 未完成 | 8 | batch C |
| `gzvprintf_step` | `vsnprintf`（M6）、哨兵、停滞路径（`gzprintf_step` 已在骨架中检查）。 | 未完成 | 9 | batch C |
| `gzflush_step`、`gzsetparams_step` | `gz_zero` 和 `gz_comp`；`deflateParams` 步骤。 | 未完成 | 7 | batch C |
| `gzclose_w_step` | 结束、`deflateEnd`、释放、释放描述符（也包括 O-1）。 | 未完成 | 8 | batch C |
| `deflate_quiet` | 没有输入的 `deflate`：从至少 8 字节空间开始并填满输出的调用降低 `Φ`；结束时仍有空间的调用留下 `Quiet`；从 `Quiet` 出发不产生输出；重新设置缓冲区保持两者。已在 dev 上证明为 `Zlib.Deflate.Universal.Quiet.deflate_quiet_holds`（`dde03ce6`），即骨架的 `DeflateQuiet` 展开写出，没有假设；`skeleton/gz` 包含该提交后，`deflate_quiet := deflate_quiet_holds`。组成部分：`quiet_silent`、`stateOf_rebuffer`、`phiD_lt`、`strat_quiet`、`marker_quiet`、`header_quiet`、`trailer_quiet`、`tail_quiet`、`call_quiet_of`（文件 `deflate.c.quiet-*`）。 | 已检查 | 0 | batch 3 |
| 合并 `deflate.c.quiet-*` 中重述的副本 | 清理工作，不在关键路径上：把重述的阶段与循环证明作为原引理的更强结论并回 batch 2 和 batch B 的文件。 | 未完成 | 4 | 以后 |
| **剩余总计** | batch 1 61–67；读取侧 73（deflate owner 60，batch 3 13）；写入侧 72 | | **206–212** | |


### zlib.h 函数的无故障覆盖

zlib.h 文档化的每个函数占一行。每行给出表明该调用不会出错的已检查定理，以及所走的路线：它自己的目标、序列目标（该调用是一个 `StreamOperation`）、`StreamSequenceSafety` 的 End 子句，或 open。这是 `dev` 在 `10bd366a`（2026-11-13）的快照。“已登记”指列入 `tests/audit/theorems.txt`，即验收候选，尚未验收。定理或目标变化时，需重新核对对应行。

每条流路线或工具函数路线共有的模型级前提，不在每行重复：默认分配器（`DefaultOrNull`/`DefAlloc`/`zfree = zcfree`；已声明的目标限制）、堆良构性（`Fresh`、`Uniq`、`LibraryGlobals`），以及对 inflate、工具函数和 inflateBack 而言的 `ByteObjectsFit`（`docs/deviations.md` 中的平台行）。

缩写：
- **SeqI** = `Goal.inflate_sequence_safety`：`Zlib.Inflate.Proofs.inflate_sequence_safety_public`（`public-inflate-sequence-safety.lean`，已登记）。
- **SeqD** = `Goal.deflate_sequence_safety`：`Zlib.Deflate.Universal.deflate_sequence_safety`（`public-deflate-goals.lean`，已登记）。
- 两者都只覆盖 `p = some r` 且 `StreamReachable r`（以及 `StreamArguments`）的情形。两者都不覆盖 NULL 流或不一致的流（zalloc/zfree 为 NULL、state 为 NULL，或检查拒绝的 state）。zlib.h 把这些情形文档化为 `Z_STREAM_ERROR` 拒绝，`docs/spec/safety.md` 的 A1 把文档化的空指针拒绝保留在范围内。“refusal”一列说明是否有定理覆盖该情形。

#### 流：deflate

| 函数 | 路线 | 定理（Lean 名称，文件） | 已登记？ | 定义域缺口或备注 |
| --- | --- | --- | --- | --- |
| deflateInit_（宏 deflateInit） | 自身目标 | `ZlibF.Spec.Public.Proofs.DeflateInit.deflateInit_proof`，`public-deflate-init.lean` | 是 | 完整：错误版本（`VersionValue`，NULL 或可读的首字节）、错误的 `stream_size`（任意 `p`）、NULL strm、每个 level、分配失败。 |
| deflateInit2_（宏 deflateInit2） | 自身目标 | `ZlibF.Spec.Public.Proofs.DeflateInit2.deflateInit2_proof`，`public-deflate-init2.lean` | 是 | 完整，同 deflateInit_，另加每个 method/windowBits/memLevel/strategy。`Goal.deflate_initialisation_domain`（非空性）没有定理。 |
| deflate | 自身目标 + SeqD | `Zlib.Deflate.Universal.deflate_safety`，`public-deflate-goals.lean` | 是 | 可达 + `DGood` + `StreamBuffers` + `ActiveHeader`（分离行）。Refusal：`Goal.deflate_refusal`（checked）覆盖 NULL 与不一致的流。 |
| deflateEnd | 自身目标 + SeqD 的 End 子句 | `ZlibF.Spec.Public.DeflateEndProof.deflate_end_public`，`public-deflate-end.lean`；SeqD 的第 3 子句 | 是 | 自身目标需要 `DGood`。Refusal：`Zlib.Deflate.Proofs.deflateEnd_reject`（`deflate.c.life.end.lean`，已登记）覆盖 NULL、zalloc/zfree 为 NULL、state 为 NULL，以及被拒绝的活动 state。因此已覆盖：从未初始化（模型指针为 NULL）、NULL、state 为 NULL，以及复制失败之后。它不是类型为目标的定理。 |
| deflateSetDictionary | SeqD | SeqD | 是 | 自身的 `Goal.deflateSetDictionary`：无定理。Refusal：`Goal.deflate_refusal`（checked）覆盖 NULL 与不一致的流。 |
| deflateGetDictionary | 自身目标 + SeqD | `ZlibF.Spec.Public.DeflateDictionaryProof.deflate_getdict_public`，`public-deflate-getdict.lean` | 是 | 自身目标需要 `DGood`，且目标缓冲区与窗口分离。Refusal：`Zlib.Deflate.Proofs.deflateGetDictionary_reject`（`deflate.c.life.getdict.lean`）已检查，但**未登记**。 |
| deflateCopy | 自身目标 | `Zlib.Deflate.Universal.deflate_copy_public` / `deflate_copy_safety`，`public-deflate-copy.lean` | 是 | 不是 `StreamOperation`；`StreamReachable.deflateCopy` 只为 SeqD 的第 1 子句提供输入。缺口：`source ≠ dest`（偏差行）。不一致的源由 `Goal.deflate_refusal`（checked）覆盖。 |
| deflateReset | 自身目标 + SeqD | `ZlibF.Spec.Public.DeflateResetProof.deflate_reset_public`，`public-deflate-reset.lean` | 是 | Refusal：`Zlib.Deflate.Proofs.deflateReset_reject`（已登记）。 |
| deflateParams | SeqD | SeqD | 是 | 自身的 `Goal.deflateParams`：无定理。Refusal：`Goal.deflate_refusal`（checked）覆盖 NULL 与不一致的流。 |
| deflateTune | 自身目标 + SeqD | `ZlibF.Spec.Public.DeflateQueryProof.tune_public`，`public-deflate-small-queries.lean` | 是 | 完整（`CheckedDeflate` 包含各 refusal）。 |
| deflateBound | SeqD | SeqD | 是 | 自身的 `Goal.deflateBound`：无定理。SeqD 需要 `ActiveHeader ∧ DeflateHeaderLive`。Refusal：`deflateBound_nostate`（已登记）。 |
| deflateBound_z | SeqD | SeqD | 是 | 同 deflateBound（`deflateBound_z_nostate`，已登记）。 |
| deflatePending | 自身目标 + SeqD | `ZlibF.Spec.Public.DeflateQueryProof.pending_public` | 是 | 完整。 |
| deflateUsed | 自身目标 + SeqD | `ZlibF.Spec.Public.DeflateQueryProof.used_public` | 是 | 完整。 |
| deflatePrime | SeqD | SeqD | 是 | 自身的 `Goal.deflatePrime`：无定理。SeqD 需要 `DeflateNotStarted`，这是 zlib.h 自己的次序规则。Refusal：`deflatePrime_refused`（已登记）。 |
| deflateSetHeader | 自身目标 + SeqD | `ZlibF.Spec.Public.DeflateQueryProof.header_public` | 是 | 完整。SeqD 需要 `DeflateNotStarted`（zlib.h 的次序）。 |

#### 流：inflate

| 函数 | 路线 | 定理（Lean 名称，文件） | 已登记？ | 定义域缺口或备注 |
| --- | --- | --- | --- | --- |
| inflateInit_（宏 inflateInit） | 自身目标 | `ZlibF.Spec.Public.Proofs.InflateInit.init15_public`，`public-inflate-init.lean` | 是 | 完整：错误版本或大小、NULL strm、分配失败。 |
| inflateInit2_（宏 inflateInit2） | 自身目标 | `ZlibF.Spec.Public.Proofs.InflateInit.inflate_init2_public`，`public-inflate-init2.lean` | 是 | 完整，每个 `windowBits`。 |
| inflate | 自身目标 + SeqI | `Zlib.Inflate.Proofs.inflate_public`，`public-inflate.lean` | 是 | 可达 + `Good` + `ByteObjectsFit` + `StreamBuffers` + `ActiveHeader`。Refusal：`Goal.inflate_refusal`（checked）覆盖 NULL 与不一致的流。 |
| inflateEnd | 自身目标 + SeqI 的 End 子句 | `ZlibF.Spec.Public.InflateEndProof.inflate_end_public`，`public-inflate-end.lean`；SeqI 的第 3 子句 | 是 | 自身目标需要 `Good`。Refusal：`Goal.inflate_refusal`（checked）覆盖 NULL 与不一致的流。 |
| inflateSetDictionary | 自身目标 + SeqI | `ZlibF.Spec.Public.Proofs.inflateSetDictionary_public`，`public-inflate-setdict.lean` | 是 | 自身目标需要 `Good`、`zalloc = zcalloc`，以及与窗口分离的字典（偏差行）。Refusal：`Goal.inflate_refusal`（checked）覆盖 NULL 与不一致的流。 |
| inflateGetDictionary | 自身目标 + SeqI | `ZlibF.Spec.Public.InflateDictionaryProof.inflate_getdict_public` | 是 | 自身目标需要 `Good`，且目标缓冲区与窗口分离。Refusal：`Goal.inflate_refusal`（checked）覆盖 NULL 与不一致的流。 |
| inflateSync | SeqI | SeqI | 是 | 自身的 `Goal.inflateSync`：无定理。Refusal：`inflateSync_check`（已登记）。 |
| inflateCopy | 自身目标 | `Zlib.Inflate.Proofs.inflate_copy_public`，`public-inflate-copy.lean` | 是 | 不是 `StreamOperation`。缺口：`source ≠ dest`（偏差行）。不一致的源由 `Goal.inflate_refusal`（checked）覆盖。 |
| inflateReset | 自身目标 + SeqI | `ZlibF.Spec.Public.InflateResetProof.reset_public` | 是 | 自身目标需要 `InflateView`。Refusal：`Goal.inflate_refusal`（checked）覆盖 NULL 与不一致的流。 |
| inflateReset2 | 自身目标 + SeqI | `ZlibF.Spec.Public.InflateReset2Proof.reset2_public` | 是 | 每个 `windowBits`。Refusal：`Goal.inflate_refusal`（checked）覆盖 NULL 与不一致的流。 |
| inflatePrime | 自身目标 + SeqI | `ZlibF.Spec.Public.InflatePrimeProof.prime_public` | 是 | 完整（`CheckedInflate`）。接受分支需要 `s.bits ≤ 39`，这是不变量的一个事实。 |
| inflateMark | 自身目标 + SeqI | `ZlibF.Spec.Public.InflateMarkProof.mark_public` | 是 | 完整。 |
| inflateGetHeader | 自身目标 + SeqI | `ZlibF.Spec.Public.InflateHeaderProof.getheader_public` | 是 | 在 `InflateView` 上完整。支持 gzip 的流需要 `head ≠ NULL`：C 会解引用它，而 zlib.h 不提供 NULL。SeqI 还需要 `p ≠ none`。Refusal：`inflateGetHeader_check`（已登记）。 |

#### 回调解码器

| 函数 | 路线 | 定理（Lean 名称，文件） | 已登记？ | 定义域缺口或备注 |
| --- | --- | --- | --- | --- |
| inflateBackInit_（宏 inflateBackInit） | 自身目标 | `ZlibF.Spec.Public.InflateBackInitProof.back_init_public`，`public-infback-init.lean` | 是 | 完整：错误版本或大小、NULL strm、NULL 窗口、错误的 `windowBits`、分配失败。成功分支需要一个可写的 `2^wb` 字节窗口（zlib.h 自己的规则）。 |
| inflateBack | 序列（`Goal.inflate_back_sequence_safety`） | **无无条件定理**。只有 `inflate_back_sequence_safety_of (fast : FastOk)`，`infback.c.safety-reach.lean` | 否 | **open**：`LEN_fast_p` 和 `fast_alias` 未完成（progress.md，约 15 小时）。自身的 `Goal.inflateBack`（功能性）不在计划内。NULL strm 和 state 为 NULL 已覆盖（`inflateBack_nullstream`、`inflateBack_nostate`，已登记）。该目标还有收窄：`inputBound < 2^48`，窗口是堆字节块的一个切片，每个输入块都位于堆字节块内（偏差行）。 |
| inflateBackEnd | 自身目标 | `ZlibF.Spec.Public.InflateBackEndProof.back_end_public`，`public-infback-end.lean` | 是 | 完整：NULL、state 为 NULL 或 zfree 为 NULL，以及 `BackValid`。inflateBack 序列目标的第 4 子句也只在条件定理内部得到证明。 |

#### 校验和

| 函数 | 路线 | 定理 | 已登记？ | 定义域缺口或备注 |
| --- | --- | --- | --- | --- |
| adler32 | 自身目标 | `ZlibF.Spec.Public.AdlerUpdateProof.adler_public`，`public-adler-update.lean` | 是 | **更窄**：NULL `buf` 只在 `len = 0` 时允许（`AdlerBufferBytes`，偏差行）。`len = 1` 时 C 会读 `buf[0]`，这是真实的错误（上游 PR #1364 已关闭，并宣布了 zlib.h 的限制）。`len ≥ 2` 的 NULL 在 C 中安全，但未证明。 |
| adler32_z | 自身目标 | `...AdlerUpdateProof.adler_z_public` | 是 | 同 adler32。 |
| adler32_combine / _combine64 | 自身目标 | `...AdlerCombineProof.combine_public` / `combine64_public` | 是 | 完整。 |
| crc32 / crc32_z | 自身目标 | `ZlibF.Spec.Public.Proofs.crc32` / `crc32_z`，`public-crc-updates.lean` | 是 | 完整（`BufferBytes` 包含任意长度的 NULL）。`CrcGlobals` 是模型静态数据的前提。 |
| crc32_combine / _combine64 | 自身目标 | `...CrcCombineProof.combine` / `combine64` | 是 | 完整。 |
| crc32_combine_gen / _gen64 | 自身目标 | `...CrcCombineProof.gen` / `gen64` | 是 | 完整。 |
| crc32_combine_op | 自身目标 | `...CrcCombineProof.op` | 是 | `op` 必须来自 `crc32_combine_gen`（与 zlib.h 一致）。 |
| get_crc_table | 自身目标 | `ZlibF.Spec.Public.Proofs.get_crc_table` | 是 | zlib.h 中未文档化（不是必需的）。 |

#### 工具函数

| 函数 | 路线 | 定理 | 已登记？ | 定义域缺口或备注 |
| --- | --- | --- | --- | --- |
| compress / compress_z / compress2 / compress2_z | 安全目标 `Goal.compress*_safety` | `ZlibF.Spec.Public.Proofs.Compress.compress_safety`、`compress_z_safety`、`compress2_safety`、`compress2_z_safety`，`public-compress-safe-mid.lean` | 是 | 源与目标缓冲区分离（偏差行）。长度单元建模为 `Option` 标量，所以长度单元与数据别名在模型之外（偏差行）。每个 level。功能性的 `Goal.compress*`（不在计划内）没有定理。 |
| uncompress / uncompress_z / uncompress2 / uncompress2_z | 安全目标 `Goal.uncompress*_safe` | `ZlibF.Spec.Public.Proofs.Uncompress.uncompress_safe` 等，`public-uncompress-safe.lean` | 是 | `UtilitySeparation`：数据单元与长度单元两两分离（偏差行）。功能性的 `Goal.uncompress*`（不在计划内）没有定理。 |
| compressBound / compressBound_z | 自身目标 | `ZlibF.Spec.Public.Proofs.compressBound` / `compressBound_z` | 是 | 完整。 |
| zlibVersion | 自身目标 | `ZlibF.Spec.Public.Proofs.zlibVersion` | 是 | 完整。 |
| zlibCompileFlags | 自身目标 | `ZlibF.Spec.Public.Proofs.zlibCompileFlags` | 是 | 完整。 |
| zError | 自身目标 | `ZlibF.Spec.Public.Proofs.zError` | 是 | 未文档化（不是必需的）。 |

#### Gzip 文件接口

**`dev` 上没有 gz 安全目标。** `Goal.gz_sequence_safety` 只作为定义存在于分支 `skeleton/gz` 的一个证明文件中（`gz.skeleton-model.lean`）。它既不在 `goals.txt` 中，也不在 `public-api.json` 的 `safety_goals` 中。`Goal.gz_sequence`（功能性）不在计划内，也没有定理。下面已登记的自身目标定理是针对 `GzValid`、`GzReachable` 或活动 `gzstates` 条目的功能性契约，其中一些还针对 `RegularOs fs`（确定性的常规文件世界，不是每个 OS 调用预言世界）。

| 函数 | 路线 | 定理 | 已登记？ | 定义域缺口或备注 |
| --- | --- | --- | --- | --- |
| gzopen, gzopen64 | 打开 | 无（`gzopen_null`、`gzopen*_alloc_failure` 已登记） | 仅部分 | 路径打开分支为 open。 |
| gzdopen | 自身目标 | `Zlib.Gzlib.Proofs.gzdopen_complete`，`gzlib.c.dopen-complete.lean` | 是 | 每个 `fd`。mode 为 NULL 或 C 字符串。未对每个预言世界证明。 |
| gzbuffer | 自身目标 | `ZlibF.Spec.Public.Proofs.gzbuffer_public` | 是 | NULL 和任意活动句柄。 |
| gzeof | 自身目标 | `ZlibF.Spec.Public.Proofs.gzeof_public` | 是 | NULL 和任意活动句柄。 |
| gzerror | 自身目标 | `ZlibF.Spec.Public.GzErrorProof.gzerror` | 是 | 需要 `GzValid`。该不变量尚未对每个历史推导（只有 gzdopen 建立它）。 |
| gzclearerr | 自身目标 | `ZlibF.Spec.Public.Proofs.gzclearerr` | 是 | 需要 `GzValid`（同上说明）。 |
| gzoffset, gzoffset64 | 自身目标 | `ZlibF.Spec.Public.OffsetProof.gzoffset_public_goal` / `gzoffset64_public_goal` | 是 | 需要 `GzReachable`、`GzValid` 和 `RegularOs fs`（偏差行“Gz file data”）。 |
| gzrewind | 自身目标 | `ZlibF.Spec.Public.GzRewindProof.rewind_public` | 是 | 需要 `GzReachable`、`GzValid` 和 `RegularOs fs`。 |
| gzseek, gzseek64 | open | 片段：`gzseek64_safe`（需要 `GzGood`、`PosInv` 等）已登记；`gzseek64_step` 已检查（`gz.inv-seek`） | 仅部分 | |
| gztell, gztell64 | open | `gztell64_spec` 已登记，但需要 `PosInv`，没有历史定理推导它 | 仅部分 | |
| gzclose | open | `gzclose_null`、`gzclose_dispatch` 已登记 | 仅部分 | |
| gzclose_r | open | `gzclose_r_step_safe`（`gz.read-close.lean`，针对 `GzInv`），已检查，未登记 | 否 | `GzInv` 未从历史推导。 |
| gzclose_w | open | 无 | 否 | |
| gzread, gzfread, gzgetc, gzgetc_, gzungetc, gzgets, gzdirect | open | 公开层面无（内部的 `gz_look_safe`、`gz_fetch_safe_of`、`gzungetc_step_of` 已检查） | 否 | `gzgetc` 宏的内联路径（读取 `have`、`next`、`pos`）尚未翻译。它需要句柄不变量（**待确认**）。 |
| gzwrite, gzfwrite, gzputc, gzputs, gzprintf, gzflush, gzsetparams | open | 公开层面无 | 否 | |

#### 误计与未完成项

对完整文档化定义域没有已检查无故障定理的已文档化函数：

1. **inflateBack**：open。只有 `inflate_back_sequence_safety_of (FastOk)`；`LEN_fast_p` 和 `fast_alias` 未完成。progress.md 也把该目标行列为“Not proved”。
2. **deflateCopy**：已登记。假设 `source ≠ dest`（偏差行）。
3. **inflateEnd**：已关闭。NULL、state 为 NULL、`End` 之后、初始化失败之后，以及复制失败的目标由 `Goal.inflate_refusal`（checked）覆盖。
4. **inflateCopy**：已关闭。不一致的源由 `Goal.inflate_refusal`（checked）覆盖。
5. **NULL 或不一致流的 refusal**：已关闭。`Goal.inflate_refusal` 与 `Goal.deflate_refusal`（checked）覆盖 `inflate`、`deflate`、`inflateEnd`、`inflateReset`、`inflateReset2`、`inflateGetDictionary`、`inflateSetDictionary`、`inflateCopy`、`deflateSetDictionary`、`deflateParams`、`deflateGetDictionary` 与 `deflateCopy`。这些目标与 `deflateGetDictionary_reject` 已登记。
6. **deflateParams、deflateSetDictionary、deflatePrime、deflateBound、deflateBound_z、inflateSync**：没有自身目标定理。可达流上的无故障只经由 SeqI 或 SeqD 得到。这对计划内的安全性已足够，但逐调用的自身目标仍为 open。
7. **adler32、adler32_z**：定义域比 zlib.h 更窄（NULL 只在 `len = 0` 时允许）。`len = 1` 是真实的 C 错误（偏差行）。`len ≥ 2` 的 NULL 安全但未证明。
8. **除 gzdopen、gzbuffer、gzeof、gzerror、gzclearerr、gzoffset(64)、gzrewind 之外的每个 gz 函数**：open（gzopen、gzopen64、gzclose、gzclose_r、gzclose_w、gzread、gzfread、gzgetc、gzgetc_、gzungetc、gzgets、gzdirect、gzwrite、gzfwrite、gzputc、gzputs、gzprintf、gzflush、gzsetparams、gzseek、gzseek64、gztell、gztell64）。已登记的 gz 定理依赖 `GzValid` 或 `GzReachable`（gzoffset 和 gzrewind 还依赖 `RegularOs`），而不是每个历史和每个预言世界。dev 上没有登记 gz 安全目标（`gz_sequence_safety` 只在 `skeleton/gz` 上）。
9. 相关，但不是函数：`Goal.deflate_initialisation_domain`（非空性）没有定理。

### 按顺序的下一步工作

第 9 至 12 行是计划内工作，见[范围](#scope)。先做第 11 行，然后是第 9 行和第 12 行。第 1 至 5 行和第 13 行属于 gzip 文件接口：它们的安全在计划内（第 5 项），按 [gz 骨架](#gz) 进行，而不按本表；它们的功能契约不在计划内。第 6 至 8 行和第 10 行只在某个 sequence 目标需要时才做。

按顺序排列。“前提”是必须先证明的内容，绝不是假设的契约。“负责 PR”是承载该工作的拉取请求（如已存在）。

| # | 目标 | 前提 | 负责 PR |
| ---: | --- | --- | --- |
| 1 | `gzopen`、`gzopen64`、`gz_initialisation_domain` | 陈述已修正（见 [gzip 打开路径长度](#gzip-open-path-length)）。接下来是 `gz_open` 的路径打开（`fd = -1`）分支：`fsOpen` 的结果以及追加/读取定位，复用 `gzdopen` 的组合 | — |
| 2 | `gztell`、`gztell64` | 从每个允许的 gz 调用历史（打开、读、写、定位、回退）推出 `PosInv` | — |
| 3 | `gzclose_r` | 读端缓冲区在调用历史上的归属，然后是已初始化读端上的 `inflateEnd` | — |
| 4 | `gzseek`、`gzseek64` | 第 2 项的 `PosInv` 和缓冲区不变式；透明路径与缓冲路径 | — |
| 5 | `gzread`、`gzfread`、`gzgetc`、`gzgetc_`、`gzgets`、`gzungetc`、`gzdirect`、`gzwrite`、`gzfwrite`、`gzputc`、`gzputs`、`gzprintf`、`gzvprintf`、`gzflush`、`gzsetparams` 的透明路径 | 延迟初始化与缓冲区不变式；压缩路径等待第 12–13 项 | — |
| 6 | `deflatePrime` | 在 `DGood` 下的待输出字节压缩与位插入 | — |
| 7 | `deflateBound`、`deflateBound_z` | 执行公式与饱和上界的对应，包括头部字符串 | — |
| 8 | `deflateSetDictionary` | 在 `DGood` 下的窗口填充、散列插入与输入恢复 | — |
| 9 | `deflateInit2_`、`deflate_initialisation_domain` | 参数规范化、五次分配、清理，以及对每组参数建立 `DGood` | — |
| 10 | `inflateCopy`、`deflateCopy` | 分配失败、缓冲区复制、指针重定位、独立归属 | — |
| 11 | `inflate` → `inflate_sequence` → `inflateSync`、`uncompress*`、`inflateBack`、`inflate_back_sequence` | 由实际 `inflate_table` 得到的表含义；覆盖所有模式的单一调度循环不变式 | — |
| 12 | `deflate` → `deflate_sequence` → `deflateParams`、`compress*` | `fill_window` 与滑动；以级别、`memLevel`、`windowBits` 为参数的单一策略循环不变式；块输出 | — |
| 13 | 压缩 gz 路径、`gzclose_w`、`gzclose`、`gz_sequence` | 第 11 和 12 项 | — |

当陈述修正会改变需要证明的内容时，先做修正。尚未解决：依赖 `detectLag = 8` 的 `Api.Goal.inflate_rejects_invalid`（已检查的反例表明该常数有误；[API 模型](design/api-model.md)）。下文的 gzip 打开路径长度问题已修正。`inflateInit2_` 与 `Api.Goal.gz_seek_read` 已修正并通过检查，等待登记。

早先的叙述性检查点（关于 inflate、deflate、树、CRC、差分框架和集成的分领域说明）保存在[进度检查点](history/progress-checkpoints.zh.md)中，属于历史记录，其中的数字不是当前数字。

### 公开 API 的证明准备情况

**灰色表示尚未证明，不表示无法推进。可以立即开展独立工作。** 被调用函数呈绿色，并不意味着调用者自身的前置条件、循环、返回结果和内存效果已经建立。一个能直接调用的 API，仍可能存在错误的契约或已确认的源码缺陷；只有这类证据才足以给目标加上阻碍边框。不能只凭图中缺少箭头判断证明准备情况。

[证据索引](progress.md)区分证明引用、C 调用和规格引用。下面列出需要组合的证明义务，这些义务与精确目标的连接尚未完成。它们不会引入新的公开调用假设，也不会赋予目标任何已检查的输入覆盖范围。

##### deflate，批次 B：位置形式的散列链（已停止，2026-11-12）

这项工作原想用位置形式的散列链不变式取消对直接调用 `deflateResetKeep` 的排除（`docs/deviations.md`）。按所有者的决定已停止：在这样的历史上，真实 C 会读到窗口之外（`docs/findings/deflate-copy-pending-prev`）：`deflateResetKeep` 和 `deflate(Z_BLOCK)` 留下两个等待插入的链头，`deflateCopy` 只复制前沿以下的 `prev`，副本上的一次 `Z_RLE` 或 `Z_HUFFMAN_ONLY` 刷新以 `insert = 0` 结束，于是 `longest_match` 之后会沿一个未初始化的槽前进。因此任何允许直接调用 `deflateResetKeep` 的不变式都不可能成立。`DInv` 保持精确形式，排除保持不变。不打 zlib 补丁：这个缺陷不妨碍已证明定义域内的证明。

保留在 `dev` 上的部分（切片 1，cc359062，已检查）：`PosChains`/`ReachS` 及其插入、滑动和 `longest_match` 的遍历（`deflate.c.engine.pos-chains`），只讲安全的 `longest_match_safe`（不需要字节一致；以 `chain_length` 终止，`deflate.c.engine.lm-safe`、`-lm-pos`），`insert_string_pos` 以及 `fill_window` 在位置形式散列链上的待插入循环（`-insert-pos`、`-fill-insert-pos`）。安全路径上没有用到它们。分支 `worker/poschains`（不变式、`fill_window`、刷新和重新设置缓冲区已切换；策略未切换）由 deflate 负责人关闭，不合入；位置形式的推广现在由 batch B 负责（2026-11-12），分片落地并保持 `dev` 可构建，精确散列链作为推论。`worker/slid-chaintop` 已关闭：其内容已在 `dev` 上（`SlidChains` 取 `chainTop`）。第一个位置形式分支按计划也无法完成的第二个原因：对 `deflate_huff` 和 `deflate_rle` 末尾的 `insert = 0`，位置形式的不变式给不出这一步，而精确不变式从它的前沿 `chainTop` 得到这一步。

随这一发现一起检查的结论：在已证明的定义域内，没有链头在等待插入（`DInv.heads_inserted`、`DInv.slid_heads_inserted`，`deflate.c.universal-heads`）。

#### 打开、查询与关闭操作的前提

证明打开文件不需要先完成整个引擎。主要工作在公共辅助函数 `gz_open`：模式解析循环、真实分配、字符串复制、文件描述符效果，以及初始化不变量。位置查询尚缺的基础，是覆盖所有允许调用序列的位置不变量。关闭操作尚缺的基础，是覆盖这些调用序列的所有权事实，其中也包括分配失败。

目前本地执行证明已覆盖：

- [打开入口](../ZlibF/Proof/gzlib.c.open.lean)：NULL 参数、负文件描述符和第一次分配失败。结论给出未改变的文件系统和精确堆状态，也包括分配尝试计数器。
- [读模式关闭](../ZlibF/Proof/gzread.c.close.lean)：NULL、模式不匹配，以及在 `GzGood` 条件下完整的未缓冲执行。范围包含文件描述符错误，释放消息、路径和句柄，以及无关分配保持不变的框架性质。
- [位预置入口](../ZlibF/Proof/deflate.c.prime.lean)：在压紧待输出字节之前，拒绝流状态和非法位数的分支。

这些是具有明确内部范围的结果，并不是完整公开目标的证明。特别是，仍须从允许的公开调用序列推出 `GzGood`。不能凭一个分支的结果，就把灰色公开节点改成绿色。

#### inflateBack

回调解码器的安全（所有者 2026-11-12 的要求）：`Goal.inflate_back_sequence_safety`（`ZlibF/Spec/Public/Sequences.lean`），与未改动的 `Goal.inflate_back_sequence` 并列陈述。回调就是目标中的 `CallbackProtocol`：任意会返回的调用者代码，只修改自己的块和必须保持的窗口切片，交出位于窗口之外的可读输入，并提供有限的总输入（`inputBound`）。目标另加 `inputBound < 2^48`（循环额度；`docs/deviations.md`）。陈述测试：`tests/goals/infback-callbacks`（ASan/UBSan，30000 个用例，无报告）。骨架：分支 `skeleton/inflate-back`，`ZlibF/Proof/infback.c.safety-skeleton.lean`（类型检查通过；引理证明待完成）。早先的内部约定 `CbContract` 比协议窄，因此回调引理在 `PInv` 上重新陈述，其位代数可复用。
问题（不在计划内的功能目标）：`Goal.inflateBack` 对 `inputBound` 没有上限，因此输入超过循环额度的协议在模型中使它为假。
所需不变量：`inflate_fast` 假定入口处 `state->bits < 8`。`inflate.c` 在快速路径前检查它（上游 e7bb978）；`infback.c` 不检查，因此证明要说明每轮以 `TYPE`、`TABLE` 或 `LEN` 开始时持有的位少于 8（`BitsShort` 行）。若持有 8 位或更多，`inflate_fast` 可能把 `next` 退回到 `in` 给出的数据块之前。证据：`tests/goals/infback-callbacks/bits8.sh`（60000 个用例，未触发陷阱）。
目标修正（46ce3a0a、200f80e1）：历史为 `BackSafeReachable`。窗口是一个堆字节块的切片；在每次调用所在的堆上以及每个回调步骤之后，每个字节对象都小于 `2^63` 字节（`BackPlatform`）；每个输入块都位于一个堆字节块中（`BackFirstChunk`、`BackPlatform`）；两次调用之间的调用者修改保持存活块的只读标志。偏差行："回调解码器窗口"、"回调解码器输入块"、平台行与"回调"。候选推广（现在不做）：让两个解码器 `inflate` 与 `inflateBack` 一起接受位于任意字节引用的输入块（调用者结构体字段、静态数据）；两者都依赖 `inflate_fast`，其入口要求原始字节块。
组合（6f9575e7）：`inflate_back_sequence_safety_of` 由 `FastOk`（不变量上 `case LEN` 的快速路径）证明目标；剩余的是 `LEN_fast_p` 与 `fast_alias`。

| 引理 | 含义 | 状态 | 小时 |
| --- | --- | --- | ---: |
| `PInv` 框架 | 调用者协议上的循环不变量：`CallbackFrame` 与存活集合在回调调用和库写入之间可组合；状态或寄存器写入保持 `PInv` | 已检查（dd5f9e1e） | 0 |
| `PULL_p` | `PULL()`：只在当前块为空时调用 `in`；由协议的 `inStep` 得到数据块和日志项；返回 0 时为 `Z_BUF_ERROR` | 已检查（dd5f9e1e） | 0 |
| `PULLBYTE_p`、`NEEDBITS_p` | 向 `hold` 读入一个字节，以及 `k ≤ 32` 的 `NEEDBITS(k)`（`inflate.c.main.macros` 的位代数） | 已检查（52ae3999） | 0 |
| `ROOM_p` | `ROOM()`：对满窗口调用 `out`（`outStep`），`whave = wsize`，从窗口开头重新写；拒绝时为 `Z_BUF_ERROR` | 已检查（7971d171） | 0 |
| `TYPE_p` | `case TYPE`：最后块标志与块类型，最后一块之后进入 `DONE` | 已检查（472c8a15） | 0 |
| `STORED_p` | `case STORED`：长度检查以及经 `PULL` 和 `ROOM` 的复制；数据块可与窗口同属一个块 | 已检查（eec477cd） | 0 |
| `TABLE_p` | `case TABLE`：头部、码长码、解码出的码长、三次 `inflate_table` 调用，表已安装（`TablesOk`，含解码不变量与查询稳定性），以及转入 `LEN` | 已检查（650c8931） | 0 |
| `BitsShort` | 每轮以 `TYPE`、`TABLE`、`LEN` 开始时持有的位少于 8（`Round` 中的 `Short`）：带读入见证的查表、由 `StableQuery` 与 `PrefixQuery` 得到的 `consumed_gt`、依据 `CodeLengthContents` 的 `TABLE` 码长解码 | 已检查（57c7fabd、9e93b576） | 0 |
| `fast_alias` | 输出位于窗口块内的 `inflate_fast`（`wnext = 0`）：`Goal.fast_safe` 的 `Env.hwin` 要求窗口块与输出块不同；计划：在 `wnext = 0` 时允许输出块，经 `Src.out`（`cpyG`）复制，精确内容引理保留不同块的情形 | 待完成 | 12 |
| `LEN_slow_p` | 不走快速路径的 `case LEN`：字面量、块结束、带距离检查并经 `ROOM` 复制的长度/距离对、无效码 | 已检查（06e4a17d） | 0 |
| `LEN_fast_p` | 走快速路径的 `case LEN`：`RESTORE`、`fast_alias`、`LOAD` | 待完成 | 3 |
| `dispatch_p` | 调度的一轮：`PInv` 可达的每种模式；度量下降，或调用以三种结果之一离开；在 `LEN_fast_p` 之前快速路径是前提 `LenFast` | 已检查（650c8931） | 0 |
| `loop_p` | 调度循环在额度内结束（由 `inputBound < 2^48` 得 `backMeasure < 2^64`） | 已检查（650c8931） | 0 |
| `back_call` | 一次调用：入口、`loop_p`、出口（把最后的部分窗口交给 `out`，写 `next_in`、`avail_in`）：`back_call_partial`（返回的调用，任意输入）与 `back_call_total`（输入少于 `2^48`） | 已检查（3a2a8753、f91f401d） | 0 |
| `back_null`、`back_end` | 空流；可达历史上的 `inflateBackEnd`（`back_end_public`） | 已检查（6f9575e7） | 0 |
| `back_reach_valid` | 每个可达历史都在调用者窗口上留下有效状态（初始化、换缓冲区、使用无度量循环规则的 `back_call_partial`） | 已检查（6f9575e7） | 0 |
| **合计** | | | **15** |

#### 每个未完成公开目标的下一步

“开始”表示无需等待完整引擎定理就能开展的工作。“组合”列出完整收束目标所需的前提；其他独立分支仍可推进。表中任何一行都不授予已检查状态，也不把被调用函数的规格当作假设。

<!-- proof-readiness:start -->
| 公开目标 | 图中所示证明工作 | 下一步与缺少的前提 |
| --- | --- | --- |
| `gzopen`, `gzopen64`, `gz_initialisation_domain` | 开始：打开与清理 | <a id="readiness-gzopen"></a> **陈述已修正：**见 [gzip 打开路径长度](#gzip-open-path-length)。**开始：**`gz_open` 的路径打开分支（`fsOpen` 结果、追加与读取定位），复用已登记的 `gzdopen` 模式循环、分配与 `OpenState` 组合。上文的入口与失败分支已经过本地检查。 |
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
<!-- proof-readiness:end -->

近期顺序是：先推进独立的入口、清理和算术路径，再建立公共的打开、位置和所有权不变量，最后完成整函数组合。回调压缩块可以并行推进。如果某个前提尚不清楚，应在这里记录精确问题；不能凭空制造依赖，也不能把经过的时间当作存在阻碍的证据。

### 规格审查

#### Gzip 定位模式

已修正。原先的 `GzSeek` 允许成功的定位返回另一种模式的句柄，因此抽象目标 `gz_seek_read` 不成立。现在该关系保持模式不变。该目标已有[本地检查的证明](../ZlibF/Proof/Api/GzSeekRead.lean)，原反例已改为[回归检查](../tests/verification/regressions/gz-seek-mode.lean)。登记和指定提交上的 CI 尚未完成。这是模型问题，不是 zlib 问题。

#### Inflate 初始化清理

已修正。窗口参数非法时，原 `inflateInit2_` 目标要求状态表在结构上完全不变，但分配后再释放会使该表变长。现在该分支逐项比较每个对象表（`SameObjectsUpToTableShape`）；没有任何 C 操作能观察到表的长度。该目标已有[本地检查的证明](../ZlibF/Proof/public-inflate-init2.lean)，原反例已改为[回归检查](../tests/verification/regressions/inflate-init2-table-shape.lean)。登记和指定提交上的 CI 尚未完成。这是契约问题，不是 zlib 问题。

#### 解压工具函数的清理

已修正。`UncompressCounted` 和 `UncompressSingle` 用 `SameObjects` 比较调用后的堆，它要求对象表相等，包括表的物理长度。`uncompress2_z` 在检查参数之前分配一个局部 `z_stream` 和一个 8 字节局部块，并在每条路径上释放二者；释放后的表项作为空项留在表中。因此连空参数拒绝路径也使四个解压目标不成立。现在它们逐项比较对象表（`SameObjectsUpToTableShape`，移到 `Spec/Public/Memory.lean`），与 `inflateInit2_` 的契约相同。反例保留为[回归](../tests/verification/regressions/uncompress-table-shape.lean)。这是契约问题，不是 zlib 问题。`CompressorContract` 曾有相同的模式（`compress2_z` 也释放一个局部 `z_stream`）。

这四个契约还缺少堆的表示条件 `Uniq`（`nextBlk` 以下每个块标识只对应一个对象）。[可信基础](trusted-base.md)要求每个初始堆满足它，每个公开流历史也已假设它（`InitDomain`、`StreamReachable`）。现在它是前提。它不缩小 C 的定义域：每个 C 状态都有这样的表示。

压缩函数的契约也已修正。`CompressorContract` 和 `CompressorSafety` 有这两个缺陷。`compress2_z` 在参数检查之后的每条路径上都释放局部 `z_stream`，它留下的空表项使目标不成立，即使 `deflateInit` 在分配之前就拒绝了压缩级别（公开调用者见证上的级别 10：[回归](../tests/verification/regressions/compress-table-shape.lean)）。现在它们用 `SameObjectsUpToTableShape`。它们也缺少 `Uniq`，而 `deflateInit` 的契约和 `deflate` 流历史（`StreamReachable.deflateInit`）都假设它；现在它是前提。`CompressorSafety` 的陈述测试：`tests/goals/compress-safety`（ASan、UBSan、泄漏计数、分配失败、无效级别；9000 次运行无违反）。

独立审查已经修正的共享关系 `Uncompress2`。延迟距离处理和精确释放的修正，都有独立反例和经过检查的回归证明；实现精化仍未完成。原先在内存失败时要求输出为空的条款，以及在缓冲区错误时要求扩展输出的条款，已依据现有成对反例移除。在把较早的抽象 gz 和字典模型当作完整操作精化之前，还须完成它们；具体公开目标不会假设被调用函数的契约成立。

#### Gzip 打开路径长度

已于 2026-11-13 修正。`gz_open` 用 `malloc(len + 1)` 和 `snprintf(state->path, len + 1, "%s", path)` 复制调用者路径。分两部分：

- `snprintf` 超过 `INT_MAX`：模型 `snprintf` 在此返回 -1，与 glibc 相同（[可信基础](trusted-base.zh.md)，格式化）。不出错，陈述不变。
- `malloc` 超过 `PTRDIFF_MAX`：运行时分配器现在拒绝 `2^63` 字节及以上的请求，与 glibc 2.43 相同（[可信基础](trusted-base.zh.md)，分配大小）。于是长度为 `2^63 − 1` 字节的路径使 `gzopen` 在没有预言失败、也没有调用 `open` 的情况下返回 NULL。`OpenContract` 原来的第二条款接受该路径，并要求模式无效、预言失败或 `open` 失败三者之一，因此它对修正后的模型为假。经过检查的反例是该[回归](../tests/verification/regressions/gzopen-path-ptrdiff.lean)（`old_open_clause_false`）。`Goal.gz_initialisation_domain` 对同一路径也为假：它在 `NoAllocationFailure h` 下承诺返回句柄。复核：运行时修改（`6db5fca9`）、陈述更正（`b35b5523`）和字符串字面量 "position overflow"（`110d11cf`）已对照设计说明进行第二次阅读，没有异议。未完成：`malloc <n>` 差分测试行的 C 端尚未运行。

修正在单独的提交中。`OpenContract`（`Goal.gzopen`、`Goal.gzopen64`）第二条款：原前提为 `Fresh h → Uniq h → LibraryGlobals h → FileSystem fs → CString h path name → CString h mode flags`；新前提在 `FileSystem fs` 之后加入 `ZlibF.PlatformMemory.ByteObjectsFit h`。`Goal.gz_initialisation_domain` 第一条款：原前提为 `... FileSystem fs → NoAllocationFailure h → CString h path name → ...`；新前提在 `NoAllocationFailure h` 之后加入 `ByteObjectsFit h`。有了它，路径及其 NUL 位于同一个小于 `2^63` 字节的对象中，因此复制不会因大小被拒绝，`len + 1` 也不会回绕。见证条款和 `Goal.gzdopen`（19 字节路径）不变。这三个目标都尚未证明或登记。该前提就是已接受的平台范围（[偏差](deviations.zh.md)，“平台字节对象范围”一行）。

#### 带本地修复的 gzip 库发现

2026-11-12 的库报告，在所有者决定 F-1 和 W7 是否作为已确认的发现移入 `README.md` 之前记录在这里。每一项都有本地补丁，经所有者于 2026-11-12 批准，尚未提交上游（[补丁](../patches/README.md)）。

- F-1，[gzread 位置溢出](findings/gzread-pos-overflow/README.md)：在 Linux 的 `/dev/zero` 上透明 `gzseek` 到 `INT64_MAX` 之后，`gzread` 使有符号的 `x.pos` 溢出。在 x86_64 Linux 上由 UBSan 确认。补丁 0004。
- W7，[gzwrite 位置溢出](findings/gzwrite-pos-overflow/README.md)：`/dev/null` 上的透明写入者定位到 `INT64_MAX - 10` 后，`gzwrite` 使 `x.pos` 溢出（在 `INT64_MAX` 处的 `gzputc` 也是）。在 x86_64 Linux 上用真实设备由 UBSan 确认。补丁 0004。
- [gz look COPY 越过上限](findings/gz-position-copy-overflow.md)：`gz_look` 的 COPY 分支缓冲了全部待处理输入而没有空间上限，因此在一个 gzip 成员、尾随数据和 `gzclearerr` 之后、接近 `GZ_OFF_MAX` 的读取者返回时 `x.pos + x.have` 越过该上限。已在模型中确认（`gz.position-copy-overflow-regression`）并通过阅读 C 确认；实际上无法复现（约 2^63 个解码字节）。补丁 0004，于 2026-11-13 扩展。随之的陈述变化：`GzLookSpec` 的 COPY 析取项现为 `how = COPY ∧ avail_in = 0 ∧ (x.have ≠ 0 ∨ x.pos = GZ_OFF_MAX) ∧ x.pos + x.have ≤ GZ_OFF_MAX`（原为 `how = COPY ∧ x.have ≠ 0`）；`gz_fetch` 的 `BodyPost` 允许循环在 `avail_in = 0` 的 COPY 中继续，其度量把 COPY 记为 0。
- R-3，[x.next 从未写入](findings/gz-reset-next-uninitialised/README.md)：`gzopen` 之后立即调用的 `gzseek` 和 `gzdirect` 把从未写入的 `x.next` 前进零。按 C 标准的字面规定未定义；没有 sanitizer 报告。补丁 0005。
- R-4，[直接读取之后 x.next 悬空](findings/gz-next-dangling-after-direct-read/README.md)：大块 `gzread` 读入调用者随后释放的缓冲区之后，`gzseek` 和 `gzdirect` 在已释放的缓冲区内把 `x.next` 前进零。按 C 标准的字面规定未定义；没有 sanitizer 报告。补丁 0005。

`gzread.c`、`gzwrite.c` 和 `gzlib.c` 的翻译跟上了两个补丁。只有 0005 有差分测试行（直接读入已释放的缓冲区，然后 `gzdirect` 和 `gzseek`）；0004 需要设备，文件模型无法表达。`tests/audit/theorems.txt` 仍列出已不存在的 `seekTail_dangling_ub` 和 `gzseek64_dangling_next_ub`；删除它们需由人来做。

#### OS 调用预言下的 Gzip 偏移与回绕

在 `caad9db4` 中经所有者授权修正；证据记录于此。OS 调用预言允许 `lseek` 返回 `[0, 2^63 - 1]` 中的任意值而不移动描述符（M3），某些 Linux 设备即如此。三个已登记目标陈述了 `lseek` 之后的描述符位置：

- `Goal.gzoffset64` 与 `Goal.gzoffset`（`OffsetContract`，`Spec/Public/GzControl.lean`）。旧陈述：对每个可达且满足 `GzValid` 的句柄、每个满足 `FileSystem fs` 的世界，调用返回，堆不变，世界只有 `errno` 改变（`{ fs' with errno := fs.errno } = fs`），结果为描述符位置减去读取者已缓冲的输入（描述符无效时为 -1）。新陈述：相同，但增加前提 `RegularOs fs`，且世界只有 `errno` 与调用计数改变（`{ fs' with errno := fs.errno, nos := fs.nos } = fs`）。
- `Goal.gzrewind`。旧陈述：对每个可达且满足 `GzValid` 的句柄，调用返回 -1 且堆不变，或返回 0、状态被重置且描述符位于保存的起点；写入者或严重错误返回 -1 且世界不变。新陈述：相同，但增加前提 `RegularOs fs`。

原因。每次预言调用都使调用计数 `nos` 前进，因此偏移契约旧的世界子句对每个句柄都为假（由 `fsLseek` 的定义）。预言的 `lseek` 返回与描述符无关的值，因此结果值子句只在之后每次调用都是普通调用时成立：`RegularOs fs`（`Spec/Public/GzState.lean`）。经检查的反例：[回归](../tests/verification/regressions/gz-offset-regular-world.lean)。在一个 `FileSystem` 接受、其 `lseek` 返回 77 而不移动的世界中，`gzdopen(3, "r")` 记录起点 77；随后 `gzoffset64` 与 `gzoffset` 返回 77 而描述符位于 0，`gzrewind` 返回 0 而描述符仍位于 0。三条旧陈述为假，去掉 `RegularOs` 的修正后偏移契约也为假。这是模型变更，不是 zlib 问题。

这三个目标现在是普通文件实例上的功能契约。它们在每个世界（每个预言）上的安全属于分支 `skeleton/gz` 上的 `Goal.gz_sequence_safety`。其调用分派（`gz.skeleton.lean` 中的 `operation_safe`）经由 `gzoffset64_step`、`gzoffset_step` 和 `gzrewind_step` 把 `gzoffset64`、`gzoffset` 与 `gzrewind` 作为下一次调用。每个都是对每个 `fs` 的 `GzCallSafe`，无 `RegularOs`，也无读取额度：不出错，有结果，打开的描述符保持，`GzInv` 保持，只改变句柄自己的块。这三个步骤引理在骨架上尚未完成，`gzrewind_step` 还依赖 R-3 的本地补丁。在它们被检查之前，这些调用在非普通世界上的安全尚未证明。它们不能直接复用已登记的证明，因为那些证明现在假设 `RegularOs`。

### 翻译审查

审查所选构建采用的 C 语言版本和实现扩展。尤其需要确认可达的“空指针加零”和“空指针减空指针”操作是否具有定义。当前模型允许其中一些操作，而 `Ptr.diff` 的源码注释错误地把空指针相减归于 C23。[对照表](spec/safety.md#null-pointers-and-pointer-differences)记录了实际定义和语言依据。这次文档修改不会改变运行时，也不能证明存在可达的上游缺陷。

在已修正压缩器自动存储的基础上，继续逐语句审查。压缩器的窗口滑动现在按源码顺序检查有符号减法。[内部状态回归](../tests/regression/deflate-slide/README.md)比较三个有定义的边界情形，并在 C 和 Lean 中都拒绝一个人为构造的溢出。恢复不受检查的减法，只会改变溢出情形的观察结果。这里没有声称该人为状态实际可达；仍须从合法调用序列推出有符号运算的边界。

树合并中针对所选深度的源码级重新读取已经恢复，并有[六例回归](../tests/regression/trees-depth-read/README.md)和必需的结构检查；该检查会拒绝先前缓存表达式的写法。仍须证明内部深度读取之前的初始化时序。审查标量与指针的别名，以及压缩器指针相减时空指针减空指针的特殊情况；该项审查未完成。

### 观察记录

**`write` 返回 0 时 `gz_comp` 会空转。** 在 `gz_comp` 的两个写循环中（`gzwrite.c`：透明写循环 `while (strm->avail_in)` 和写出循环 `while (strm->next_out > state->x.next)`），对非空缓冲区返回 0 的 `write` 不推进任何东西，也不算错误，所以循环重复同一调用。如果系统一直返回 0，C 永远不返回。这是对代码的阅读；没有运行过永远返回 0 的 `write`。目前不知道 Linux 会对普通文件、管道或套接字的非零计数返回 0（其他文件类型尚未核实），所以 gz 安全证明假设它不会发生（可信基础，“gz 操作系统事实”）。gz 安全研究的故障注入测试平台检查了另一面：当 `write` 对 10% 的非空调用返回 0 时（40 条历史，ASan 和 UBSan），每条历史都结束，没有报告也没有泄漏，因为每个循环最终都会得到正数结果。这是库的行为，不是安全发现；只有在已知某个平台会返回 0 时才值得向上游说明。范围：`gzwrite`、`gzfwrite`、`gzputc`、`gzputs`、`gzprintf`、`gzflush`、`gzsetparams`、`gzclose_w`。

### 边界情况复核

对照当前固定版本，复查 gzip 额外长度算术、部分读取后的恢复、负位置定位、参数变更丢失、结束失败后的恢复，以及 EOF 之后的向前定位。带条件的定位故障引理，不能证明状态可达；须从实际调用序列建立有符号位置与借用指针条件。

`inflateBack` 边界情况针对回调 API 的复核尚未完成；还需要该接口自身的复现，普通 inflate 的内存检查示例不足以完成这一步。在声称完整 gzip 所有权，或任意有限回调都会终止之前，还须审查外部字符串分配器和固定循环执行额度。怀疑存在缺陷，不等于可以把某种公开调用情形排除在外。

[发现记录](findings.md)保存证据和置信度；当前补丁见 [patches/README.md](../patches/README.md)。没有应用一揽子未定义行为补丁。

[架构指南](design/architecture.md#design-decisions)记录设计决策 D1–D6。[安全规格](spec/safety.md#uninitialised-memory)定义新分配内存的证明义务。

