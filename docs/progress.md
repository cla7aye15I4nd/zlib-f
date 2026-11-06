# Proof target graph

<!-- proof-link-revision: f24d2e048ce952887adf94dffcab0e3b5da9e2e9 -->

[Documentation](README.md) · [Current work and group graph](overview.md)

This generated diagram contains **all 134 registered targets**.
Each node is one target from `tests/audit/goals.txt`. Colours report the freshly built
local environment, not final acceptance. A checked theorem must have exactly the target
as its type and use only allowed axioms. Source-only candidates never count as checked.
The numbers count targets, not proof difficulty or percentage of effort.

## Status key

| Status | Targets | Meaning |
| --- | ---: | --- |
| <a id="status-registered"></a>Registered proof | 18 | 🟩 Exact checked proof listed in the theorem registry. |
| <a id="status-local"></a>Locally checked | 61 | 🟦 Exact checked proof, not yet registered. |
| <a id="status-open"></a>Not proved | 53 | ⬜ No exact checked proof or documented blocker. Source drafts do not count. |
| <a id="status-blocked"></a>Blocked | 2 | 🟥 Not proved; a documented obstacle needs resolution. Click for its reason and next step. |

Registered proofs still need the full audit and CI for final acceptance.
Disallowed axiom dependencies stop generation with an error; they are not a progress state.

Solid arrows point from a called public entry to its caller, including calls through
translated helpers. Dotted arrows record actual proof or target-definition references.
These are observed references, not assumed callee contracts or a complete proof plan.
Missing arrows do not establish mathematical independence. Cycles are preserved.
Even when every displayed prerequisite is checked, a caller must establish callee
preconditions, compose heap effects and prove its own branches and loops. Gray is not
a restriction on when work can start; internal lemmas may already exist.

## Blockers

| Blocked targets | Reason and next step |
| --- | --- |
| [gz_seek_read](./progress.md#target-zlibf-spec-api-goal-gz-seek-read) | [Gzip seek mode](./overview.md#gzip-seek-mode) |
| [inflateInit2_](./progress.md#target-zlibf-spec-public-goal-inflateinit2) | [Inflate initialization cleanup](./overview.md#inflate-initialization-cleanup) |

Red marks an explicit blocker recorded in overview, not elapsed time or proof difficulty.
Other targets are not marked red merely because they call a blocked function.

**Why can an isolated node be unfinished?** Only links between registered targets are
drawn. Runtime, helper and mathematical dependencies outside that set are hidden.
Future proof dependencies may also be unknown. No arrows means no displayed link,
not that a proof exists or is easy. Green requires a checked, registered exact proof.
Arrows do not prescribe when work can start. Internal dependencies and model issues
may be hidden; see the [representation limits](trusted-base.md).

## Clickable index

Diagram links open a fixed GitHub snapshot, `f24d2e0`.
A target opens its reference entry or specification. Red targets open their blocker;
groups open their index or specification folder. These links survive merges and branch deletion.
Some Markdown viewers disable diagram links; use the ordinary tables in that case.
Table links remain document-relative and follow the branch being viewed on GitHub.
Local previews open the corresponding local documents.

| Group | Targets |
| --- | ---: |
| [Library queries](./progress.md#group-queries) | 6 |
| [Checksums](./progress.md#group-checksums) | 13 |
| [Byte-address model](./progress.md#group-addresses) | 9 |
| [Inflate streams](./progress.md#group-inflate) | 18 |
| [Deflate streams](./progress.md#group-deflate) | 17 |
| [Callback decoding](./progress.md#group-back) | 3 |
| [Gzip files](./progress.md#group-gzip) | 32 |
| [Whole-buffer operations](./progress.md#group-buffers) | 8 |
| [Format and API models](./progress.md#group-models) | 20 |
| [Lifecycles and call sequences](./progress.md#group-lifecycle) | 8 |

## All targets

```mermaid
flowchart LR
  subgraph queries["Library queries"]
    n19["compressBound"]:::local
    n20["compressBound_z"]:::local
    n21["zlibVersion"]:::local
    n22["zlibCompileFlags"]:::local
    n23["zError"]:::local
    n30["get_crc_table"]:::local
  end
  subgraph checksums["Checksums"]
    n24["adler32"]:::local
    n25["adler32_z"]:::local
    n26["adler32_combine"]:::local
    n27["adler32_combine64"]:::local
    n28["crc32"]:::registered
    n29["crc32_z"]:::registered
    n31["crc32_combine_gen"]:::local
    n32["crc32_combine_gen64"]:::local
    n33["crc32_combine_op"]:::local
    n34["crc32_combine"]:::local
    n35["crc32_combine64"]:::local
    n132["crc32_z_all_byte_views"]:::registered
    n133["crc32_all_byte_views"]:::registered
  end
  subgraph addresses["Byte-address model"]
    n123["address_read_is_pure"]:::registered
    n124["raw_block_unchanged"]:::registered
    n125["every_layout_is_representable"]:::registered
    n126["every_existing_heap_accepts_layout"]:::registered
    n127["mask_refines_base_plus_offset"]:::registered
    n128["pointer_advance_preserves_low_bits"]:::registered
    n129["first_aligned_offset"]:::registered
    n130["byte_stores_preserve_bases"]:::registered
    n131["byte_modifies_preserve_bases"]:::registered
  end
  subgraph inflate["Inflate streams"]
    n39["inflateCopy"]:::open
    n73["inflateInit2_<br/>Blocked"]:::blocked
    n74["inflateInit_"]:::local
    n77["inflateResetKeep"]:::local
    n78["inflateReset"]:::local
    n79["inflateReset2"]:::local
    n80["inflateEnd"]:::local
    n81["inflateGetDictionary"]:::local
    n82["inflateGetHeader"]:::local
    n87["inflateSetDictionary"]:::local
    n89["inflateSyncPoint"]:::local
    n90["inflateMark"]:::local
    n91["inflateCodesUsed"]:::registered
    n92["inflateUndermine"]:::local
    n93["inflateValidate"]:::local
    n94["inflatePrime"]:::local
    n99["inflate"]:::open
    n105["inflateSync"]:::open
  end
  subgraph deflate["Deflate streams"]
    n40["deflateCopy"]:::open
    n75["deflateInit2_"]:::open
    n76["deflateInit_"]:::open
    n83["deflateGetDictionary"]:::local
    n84["deflateEnd"]:::local
    n85["deflateResetKeep"]:::local
    n86["deflateReset"]:::local
    n88["deflateSetDictionary"]:::open
    n95["deflatePending"]:::local
    n96["deflateUsed"]:::local
    n97["deflateTune"]:::local
    n98["deflateSetHeader"]:::local
    n100["deflate"]:::open
    n101["deflateBound_z"]:::open
    n102["deflateBound"]:::open
    n103["deflatePrime"]:::open
    n104["deflateParams"]:::open
  end
  subgraph back["Callback decoding"]
    n36["inflateBackInit_"]:::local
    n37["inflateBack"]:::open
    n38["inflateBackEnd"]:::local
  end
  subgraph gzip["Gzip files"]
    n41["gzclose_r"]:::open
    n42["gzclose_w"]:::open
    n43["gzclose"]:::open
    n44["gzbuffer"]:::local
    n45["gzeof"]:::local
    n46["gztell64"]:::open
    n47["gztell"]:::open
    n48["gzoffset64"]:::local
    n49["gzoffset"]:::local
    n50["gzerror"]:::local
    n51["gzclearerr"]:::registered
    n52["gzrewind"]:::local
    n53["gzseek64"]:::open
    n54["gzseek"]:::open
    n55["gzopen"]:::open
    n56["gzopen64"]:::open
    n57["gzdopen"]:::open
    n58["gzread"]:::open
    n59["gzfread"]:::open
    n60["gzgetc"]:::open
    n61["gzgetc_"]:::open
    n62["gzungetc"]:::open
    n63["gzgets"]:::open
    n64["gzdirect"]:::open
    n65["gzwrite"]:::open
    n66["gzfwrite"]:::open
    n67["gzputc"]:::open
    n68["gzputs"]:::open
    n69["gzvprintf"]:::open
    n70["gzprintf"]:::open
    n71["gzflush"]:::open
    n72["gzsetparams"]:::open
  end
  subgraph buffers["Whole-buffer operations"]
    n106["compress2_z"]:::open
    n107["compress2"]:::open
    n108["compress_z"]:::open
    n109["compress"]:::open
    n110["uncompress2_z"]:::open
    n111["uncompress2"]:::open
    n112["uncompress_z"]:::open
    n113["uncompress"]:::open
  end
  subgraph models["Format and API models"]
    n0["format_deterministic"]:::registered
    n1["format_prefix_free"]:::registered
    n2["inflate_decodes"]:::local
    n3["inflate_completes"]:::local
    n4["inflate_rejects_invalid"]:::open
    n5["deflate_valid"]:::local
    n6["deflate_completes"]:::local
    n7["deflate_full_flush_resync"]:::local
    n8["roundtrip"]:::local
    n9["roundtrip_completes"]:::local
    n10["dict_roundtrip"]:::local
    n11["header_roundtrip"]:::local
    n12["deflate_bound_adequate"]:::local
    n13["compress_bound_adequate"]:::local
    n14["compress_roundtrip"]:::local
    n15["gz_roundtrip"]:::local
    n16["gz_seek_read<br/>Blocked"]:::blocked
    n17["compress_bound_value"]:::local
    n18["compress2_z_first_alloc_failure"]:::local
    n122["inflate_deferred_distance"]:::registered
  end
  subgraph lifecycle["Lifecycles and call sequences"]
    n114["inflate_sequence"]:::open
    n115["deflate_sequence"]:::open
    n116["inflate_back_sequence"]:::open
    n117["gz_sequence"]:::open
    n118["inflate_initialisation_domain"]:::local
    n119["deflate_initialisation_domain"]:::open
    n120["inflate_back_initialisation_domain"]:::local
    n121["gz_initialisation_domain"]:::open
  end
  n24 --> n100
  n24 --> n85
  n24 --> n88
  n24 --> n99
  n24 --> n87
  n25 --> n24
  n107 --> n109
  n106 -.-> n18
  n106 --> n107
  n106 --> n108
  n19 -.-> n17
  n20 -.-> n17
  n20 --> n19
  n28 -.-> n133
  n28 --> n100
  n28 --> n85
  n28 --> n88
  n28 --> n99
  n35 --> n34
  n32 --> n35
  n32 --> n31
  n33 --> n35
  n29 -.-> n132
  n29 --> n28
  n29 --> n100
  n100 --> n106
  n100 --> n104
  n100 --> n42
  n100 --> n71
  n100 --> n66
  n100 --> n67
  n100 --> n68
  n100 --> n72
  n100 --> n69
  n100 --> n65
  n101 --> n102
  n84 --> n106
  n84 --> n75
  n84 --> n42
  n75 --> n76
  n75 -.-> n119
  n75 --> n42
  n75 --> n71
  n75 --> n66
  n75 --> n67
  n75 --> n68
  n75 --> n72
  n75 --> n69
  n75 --> n65
  n76 --> n106
  n104 --> n72
  n86 --> n75
  n86 --> n42
  n86 --> n71
  n86 --> n66
  n86 --> n67
  n86 --> n68
  n86 --> n72
  n86 --> n69
  n86 --> n65
  n85 --> n86
  n43 -.-> n117
  n41 --> n43
  n42 --> n43
  n71 -.-> n117
  n59 -.-> n117
  n66 -.-> n117
  n60 -.-> n117
  n60 --> n61
  n63 -.-> n117
  n48 --> n49
  n55 -.-> n121
  n58 -.-> n117
  n52 --> n53
  n53 --> n54
  n46 --> n47
  n69 --> n70
  n65 -.-> n117
  n99 --> n59
  n99 --> n60
  n99 --> n63
  n99 --> n58
  n99 --> n62
  n99 --> n110
  n37 -.-> n116
  n38 -.-> n116
  n36 -.-> n120
  n80 --> n41
  n80 --> n110
  n73 --> n64
  n73 --> n59
  n73 --> n60
  n73 --> n63
  n73 --> n58
  n73 --> n62
  n73 --> n74
  n73 -.-> n118
  n74 --> n110
  n78 --> n64
  n78 --> n59
  n78 --> n60
  n78 --> n63
  n78 --> n58
  n78 --> n62
  n78 --> n79
  n78 --> n105
  n79 --> n73
  n77 --> n78
  n111 --> n113
  n110 --> n111
  n110 --> n112
  n23 --> n100
  n23 --> n75
  n21 --> n106
  click n0 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-api-goal-format-deterministic" "Open target and proof references" _blank
  click n1 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-api-goal-format-prefix-free" "Open target and proof references" _blank
  click n2 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-api-goal-inflate-decodes" "Open target and proof references" _blank
  click n3 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-api-goal-inflate-completes" "Open target and proof references" _blank
  click n4 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-api-goal-inflate-rejects-invalid" "Open target and proof references" _blank
  click n5 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-api-goal-deflate-valid" "Open target and proof references" _blank
  click n6 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-api-goal-deflate-completes" "Open target and proof references" _blank
  click n7 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-api-goal-deflate-full-flush-resync" "Open target and proof references" _blank
  click n8 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-api-goal-roundtrip" "Open target and proof references" _blank
  click n9 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-api-goal-roundtrip-completes" "Open target and proof references" _blank
  click n10 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-api-goal-dict-roundtrip" "Open target and proof references" _blank
  click n11 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-api-goal-header-roundtrip" "Open target and proof references" _blank
  click n12 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-api-goal-deflate-bound-adequate" "Open target and proof references" _blank
  click n13 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-api-goal-compress-bound-adequate" "Open target and proof references" _blank
  click n14 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-api-goal-compress-roundtrip" "Open target and proof references" _blank
  click n15 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-api-goal-gz-roundtrip" "Open target and proof references" _blank
  click n16 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/overview.md#gzip-seek-mode" "Open blocker reason and next step" _blank
  click n17 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-api-goal-compress-bound-value" "Open target and proof references" _blank
  click n18 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-api-goal-compress2-z-first-alloc-failure" "Open target and proof references" _blank
  click n19 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-compressbound" "Open target and proof references" _blank
  click n20 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-compressbound-z" "Open target and proof references" _blank
  click n21 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-zlibversion" "Open target and proof references" _blank
  click n22 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-zlibcompileflags" "Open target and proof references" _blank
  click n23 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-zerror" "Open target and proof references" _blank
  click n24 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-adler32" "Open target and proof references" _blank
  click n25 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-adler32-z" "Open target and proof references" _blank
  click n26 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-adler32-combine" "Open target and proof references" _blank
  click n27 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-adler32-combine64" "Open target and proof references" _blank
  click n28 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-crc32" "Open target and proof references" _blank
  click n29 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-crc32-z" "Open target and proof references" _blank
  click n30 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-get-crc-table" "Open target and proof references" _blank
  click n31 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-crc32-combine-gen" "Open target and proof references" _blank
  click n32 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-crc32-combine-gen64" "Open target and proof references" _blank
  click n33 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-crc32-combine-op" "Open target and proof references" _blank
  click n34 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-crc32-combine" "Open target and proof references" _blank
  click n35 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-crc32-combine64" "Open target and proof references" _blank
  click n36 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-inflatebackinit" "Open target and proof references" _blank
  click n37 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-inflateback" "Open target and proof references" _blank
  click n38 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-inflatebackend" "Open target and proof references" _blank
  click n39 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-inflatecopy" "Open target and proof references" _blank
  click n40 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-deflatecopy" "Open target and proof references" _blank
  click n41 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-gzclose-r" "Open target and proof references" _blank
  click n42 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-gzclose-w" "Open target and proof references" _blank
  click n43 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-gzclose" "Open target and proof references" _blank
  click n44 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-gzbuffer" "Open target and proof references" _blank
  click n45 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-gzeof" "Open target and proof references" _blank
  click n46 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-gztell64" "Open target and proof references" _blank
  click n47 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-gztell" "Open target and proof references" _blank
  click n48 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-gzoffset64" "Open target and proof references" _blank
  click n49 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-gzoffset" "Open target and proof references" _blank
  click n50 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-gzerror" "Open target and proof references" _blank
  click n51 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-gzclearerr" "Open target and proof references" _blank
  click n52 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-gzrewind" "Open target and proof references" _blank
  click n53 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-gzseek64" "Open target and proof references" _blank
  click n54 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-gzseek" "Open target and proof references" _blank
  click n55 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-gzopen" "Open target and proof references" _blank
  click n56 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-gzopen64" "Open target and proof references" _blank
  click n57 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-gzdopen" "Open target and proof references" _blank
  click n58 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-gzread" "Open target and proof references" _blank
  click n59 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-gzfread" "Open target and proof references" _blank
  click n60 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-gzgetc" "Open target and proof references" _blank
  click n61 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-gzgetc" "Open target and proof references" _blank
  click n62 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-gzungetc" "Open target and proof references" _blank
  click n63 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-gzgets" "Open target and proof references" _blank
  click n64 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-gzdirect" "Open target and proof references" _blank
  click n65 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-gzwrite" "Open target and proof references" _blank
  click n66 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-gzfwrite" "Open target and proof references" _blank
  click n67 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-gzputc" "Open target and proof references" _blank
  click n68 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-gzputs" "Open target and proof references" _blank
  click n69 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-gzvprintf" "Open target and proof references" _blank
  click n70 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-gzprintf" "Open target and proof references" _blank
  click n71 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-gzflush" "Open target and proof references" _blank
  click n72 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-gzsetparams" "Open target and proof references" _blank
  click n73 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/overview.md#inflate-initialization-cleanup" "Open blocker reason and next step" _blank
  click n74 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-inflateinit" "Open target and proof references" _blank
  click n75 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-deflateinit2" "Open target and proof references" _blank
  click n76 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-deflateinit" "Open target and proof references" _blank
  click n77 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-inflateresetkeep" "Open target and proof references" _blank
  click n78 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-inflatereset" "Open target and proof references" _blank
  click n79 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-inflatereset2" "Open target and proof references" _blank
  click n80 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-inflateend" "Open target and proof references" _blank
  click n81 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-inflategetdictionary" "Open target and proof references" _blank
  click n82 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-inflategetheader" "Open target and proof references" _blank
  click n83 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-deflategetdictionary" "Open target and proof references" _blank
  click n84 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-deflateend" "Open target and proof references" _blank
  click n85 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-deflateresetkeep" "Open target and proof references" _blank
  click n86 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-deflatereset" "Open target and proof references" _blank
  click n87 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-inflatesetdictionary" "Open target and proof references" _blank
  click n88 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-deflatesetdictionary" "Open target and proof references" _blank
  click n89 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-inflatesyncpoint" "Open target and proof references" _blank
  click n90 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-inflatemark" "Open target and proof references" _blank
  click n91 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-inflatecodesused" "Open target and proof references" _blank
  click n92 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-inflateundermine" "Open target and proof references" _blank
  click n93 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-inflatevalidate" "Open target and proof references" _blank
  click n94 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-inflateprime" "Open target and proof references" _blank
  click n95 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-deflatepending" "Open target and proof references" _blank
  click n96 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-deflateused" "Open target and proof references" _blank
  click n97 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-deflatetune" "Open target and proof references" _blank
  click n98 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-deflatesetheader" "Open target and proof references" _blank
  click n99 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-inflate" "Open target and proof references" _blank
  click n100 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-deflate" "Open target and proof references" _blank
  click n101 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-deflatebound-z" "Open target and proof references" _blank
  click n102 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-deflatebound" "Open target and proof references" _blank
  click n103 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-deflateprime" "Open target and proof references" _blank
  click n104 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-deflateparams" "Open target and proof references" _blank
  click n105 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-inflatesync" "Open target and proof references" _blank
  click n106 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-compress2-z" "Open target and proof references" _blank
  click n107 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-compress2" "Open target and proof references" _blank
  click n108 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-compress-z" "Open target and proof references" _blank
  click n109 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-compress" "Open target and proof references" _blank
  click n110 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-uncompress2-z" "Open target and proof references" _blank
  click n111 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-uncompress2" "Open target and proof references" _blank
  click n112 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-uncompress-z" "Open target and proof references" _blank
  click n113 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-uncompress" "Open target and proof references" _blank
  click n114 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-inflate-sequence" "Open target and proof references" _blank
  click n115 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-deflate-sequence" "Open target and proof references" _blank
  click n116 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-inflate-back-sequence" "Open target and proof references" _blank
  click n117 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-gz-sequence" "Open target and proof references" _blank
  click n118 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-inflate-initialisation-domain" "Open target and proof references" _blank
  click n119 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-deflate-initialisation-domain" "Open target and proof references" _blank
  click n120 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-inflate-back-initialisation-domain" "Open target and proof references" _blank
  click n121 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-public-goal-gz-initialisation-domain" "Open target and proof references" _blank
  click n122 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlibf-spec-api-goal-inflate-deferred-distance" "Open target and proof references" _blank
  click n123 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-c-byteaddress-spec-goal-address-read-is-pure" "Open target and proof references" _blank
  click n124 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-c-byteaddress-spec-goal-raw-block-unchanged" "Open target and proof references" _blank
  click n125 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-c-byteaddress-spec-goal-every-layout-is-representable" "Open target and proof references" _blank
  click n126 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-c-byteaddress-spec-goal-every-existing-heap-accepts-layout" "Open target and proof references" _blank
  click n127 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-c-byteaddress-spec-goal-mask-refines-base-plus-offset" "Open target and proof references" _blank
  click n128 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-c-byteaddress-spec-goal-pointer-advance-preserves-low-bits" "Open target and proof references" _blank
  click n129 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-c-byteaddress-spec-goal-first-aligned-offset" "Open target and proof references" _blank
  click n130 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-c-byteaddress-spec-goal-byte-stores-preserve-bases" "Open target and proof references" _blank
  click n131 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-c-byteaddress-spec-goal-byte-modifies-preserve-bases" "Open target and proof references" _blank
  click n132 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlib-crc32-spec-byteviews-goal-crc32-z-all-byte-views" "Open target and proof references" _blank
  click n133 href "https://github.com/cla7aye15I4nd/zlib-f/blob/f24d2e048ce952887adf94dffcab0e3b5da9e2e9/docs/progress.md#target-zlib-crc32-spec-byteviews-goal-crc32-all-byte-views" "Open target and proof references" _blank
  classDef registered fill:#dcfce7,color:#166534,stroke:#166534
  classDef local fill:#dbeafe,color:#1e40af,stroke:#1e40af
  classDef open fill:#e5e7eb,color:#374151,stroke:#374151
  classDef blocked fill:#fee2e2,color:#991b1b,stroke:#991b1b
```

## Proof references

The links below let a reader check the evidence behind each coloured node.
A source-only candidate is not a completed proof. An open target may still have useful
internal lemmas; they do not automatically prove the public target.


<a id="group-queries"></a>

### Library queries

| Target statement | State | Contract | Proof evidence |
| --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-compressbound"></a>[compressBound](../ZlibF/Spec/Public/Queries.lean#L35) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/utility.md#compressbound) | [ZlibF.Spec.Public.Proofs.compressBound](../ZlibF/Proof/public-compress-bound.lean#L49) |
| <a id="target-zlibf-spec-public-goal-compressbound-z"></a>[compressBound_z](../ZlibF/Spec/Public/Queries.lean#L40) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/utility.md#compressbound_z) | [ZlibF.Spec.Public.Proofs.compressBound_z](../ZlibF/Proof/public-compress-bound.lean#L46) |
| <a id="target-zlibf-spec-public-goal-zlibversion"></a>[zlibVersion](../ZlibF/Spec/Public/Queries.lean#L46) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/utility.md#zlibversion) | [ZlibF.Spec.Public.Proofs.zlibVersion](../ZlibF/Proof/public-zlib-version.lean#L8) |
| <a id="target-zlibf-spec-public-goal-zlibcompileflags"></a>[zlibCompileFlags](../ZlibF/Spec/Public/Queries.lean#L53) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/utility.md#zlibcompileflags) | [ZlibF.Spec.Public.Proofs.zlibCompileFlags](../ZlibF/Proof/public-zlib-compile-flags.lean#L6) |
| <a id="target-zlibf-spec-public-goal-zerror"></a>[zError](../ZlibF/Spec/Public/Queries.lean#L59) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/utility.md#zerror) | [ZlibF.Spec.Public.Proofs.zError](../ZlibF/Proof/public-zerror.lean#L37) |
| <a id="target-zlibf-spec-public-goal-get-crc-table"></a>[get_crc_table](../ZlibF/Spec/Public/Checksums.lean#L126) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/checksums.md#get_crc_table) | [ZlibF.Spec.Public.Proofs.get_crc_table](../ZlibF/Proof/public-get-crc-table.lean#L13) |

<a id="group-checksums"></a>

### Checksums

| Target statement | State | Contract | Proof evidence |
| --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-adler32"></a>[adler32](../ZlibF/Spec/Public/Checksums.lean#L66) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/checksums.md#adler32) | [ZlibF.Spec.Public.AdlerUpdateProof.adler_public](../ZlibF/Proof/public-adler-update.lean#L46) |
| <a id="target-zlibf-spec-public-goal-adler32-z"></a>[adler32_z](../ZlibF/Spec/Public/Checksums.lean#L61) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/checksums.md#adler32_z) | [ZlibF.Spec.Public.AdlerUpdateProof.adler_z_public](../ZlibF/Proof/public-adler-update.lean#L36) |
| <a id="target-zlibf-spec-public-goal-adler32-combine"></a>[adler32_combine](../ZlibF/Spec/Public/Checksums.lean#L86) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/checksums.md#adler32_combine) | [ZlibF.Spec.Public.AdlerCombineProof.combine_public](../ZlibF/Proof/public-adler-combine.lean#L118) |
| <a id="target-zlibf-spec-public-goal-adler32-combine64"></a>[adler32_combine64](../ZlibF/Spec/Public/Checksums.lean#L90) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/checksums.md#adler32_combine64) | [ZlibF.Spec.Public.AdlerCombineProof.combine64_public](../ZlibF/Proof/public-adler-combine.lean#L121) |
| <a id="target-zlibf-spec-public-goal-crc32"></a>[crc32](../ZlibF/Spec/Public/Checksums.lean#L117) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/checksums.md#crc32) | [ZlibF.Spec.Public.Proofs.crc32](../ZlibF/Proof/public-crc-updates.lean#L28) |
| <a id="target-zlibf-spec-public-goal-crc32-z"></a>[crc32_z](../ZlibF/Spec/Public/Checksums.lean#L109) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/checksums.md#crc32_z) | [ZlibF.Spec.Public.Proofs.crc32_z](../ZlibF/Proof/public-crc-updates.lean#L18) |
| <a id="target-zlibf-spec-public-goal-crc32-combine-gen"></a>[crc32_combine_gen](../ZlibF/Spec/Public/Checksums.lean#L140) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/checksums.md#crc32_combine_gen) | [ZlibF.Spec.Public.CrcCombineProof.gen](../ZlibF/Proof/public-crc-combine.lean#L70) |
| <a id="target-zlibf-spec-public-goal-crc32-combine-gen64"></a>[crc32_combine_gen64](../ZlibF/Spec/Public/Checksums.lean#L143) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/checksums.md#crc32_combine_gen64) | [ZlibF.Spec.Public.CrcCombineProof.gen64](../ZlibF/Proof/public-crc-combine.lean#L74) |
| <a id="target-zlibf-spec-public-goal-crc32-combine-op"></a>[crc32_combine_op](../ZlibF/Spec/Public/Checksums.lean#L150) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/checksums.md#crc32_combine_op) | [ZlibF.Spec.Public.CrcCombineProof.op](../ZlibF/Proof/public-crc-combine.lean#L78) |
| <a id="target-zlibf-spec-public-goal-crc32-combine"></a>[crc32_combine](../ZlibF/Spec/Public/Checksums.lean#L162) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/checksums.md#crc32_combine) | [ZlibF.Spec.Public.CrcCombineProof.combine](../ZlibF/Proof/public-crc-combine.lean#L82) |
| <a id="target-zlibf-spec-public-goal-crc32-combine64"></a>[crc32_combine64](../ZlibF/Spec/Public/Checksums.lean#L165) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/checksums.md#crc32_combine64) | [ZlibF.Spec.Public.CrcCombineProof.combine64](../ZlibF/Proof/public-crc-combine.lean#L86) |
| <a id="target-zlib-crc32-spec-byteviews-goal-crc32-z-all-byte-views"></a>[crc32_z_all_byte_views](../ZlibF/Spec/Crc32ByteViews.lean#L17) | [Registered proof](./progress.md#status-registered) | See target statement | [Zlib.Crc32.Proofs.crc32_z_all_byte_views](../ZlibF/Proof/crc32.c.views.lean#L567) |
| <a id="target-zlib-crc32-spec-byteviews-goal-crc32-all-byte-views"></a>[crc32_all_byte_views](../ZlibF/Spec/Crc32ByteViews.lean#L28) | [Registered proof](./progress.md#status-registered) | See target statement | [Zlib.Crc32.Proofs.crc32_all_byte_views](../ZlibF/Proof/crc32.c.views.lean#L573) |

<a id="group-addresses"></a>

### Byte-address model

| Target statement | State | Contract | Proof evidence |
| --- | --- | --- | --- |
| <a id="target-c-byteaddress-spec-goal-address-read-is-pure"></a>[address_read_is_pure](../ZlibF/Spec/ByteAddress.lean#L39) | [Registered proof](./progress.md#status-registered) | See target statement | [C.ByteAddress.Proofs.address_read_is_pure](../ZlibF/Proof/ByteAddress.lean#L28) |
| <a id="target-c-byteaddress-spec-goal-raw-block-unchanged"></a>[raw_block_unchanged](../ZlibF/Spec/ByteAddress.lean#L43) | [Registered proof](./progress.md#status-registered) | See target statement | [C.ByteAddress.Proofs.raw_block_unchanged](../ZlibF/Proof/ByteAddress.lean#L33) |
| <a id="target-c-byteaddress-spec-goal-every-layout-is-representable"></a>[every_layout_is_representable](../ZlibF/Spec/ByteAddress.lean#L50) | [Registered proof](./progress.md#status-registered) | See target statement | [C.ByteAddress.Proofs.every_layout_is_representable](../ZlibF/Proof/ByteAddress.lean#L39) |
| <a id="target-c-byteaddress-spec-goal-every-existing-heap-accepts-layout"></a>[every_existing_heap_accepts_layout](../ZlibF/Spec/ByteAddress.lean#L57) | [Registered proof](./progress.md#status-registered) | See target statement | [C.ByteAddress.Proofs.every_existing_heap_accepts_layout](../ZlibF/Proof/ByteAddress.lean#L94) |
| <a id="target-c-byteaddress-spec-goal-mask-refines-base-plus-offset"></a>[mask_refines_base_plus_offset](../ZlibF/Spec/ByteAddress.lean#L65) | [Registered proof](./progress.md#status-registered) | See target statement | [C.ByteAddress.Proofs.mask_refines_base_plus_offset](../ZlibF/Proof/ByteAddress.lean#L54) |
| <a id="target-c-byteaddress-spec-goal-pointer-advance-preserves-low-bits"></a>[pointer_advance_preserves_low_bits](../ZlibF/Spec/ByteAddress.lean#L70) | [Registered proof](./progress.md#status-registered) | See target statement | [C.ByteAddress.Proofs.pointer_advance_preserves_low_bits](../ZlibF/Proof/ByteAddress.lean#L60) |
| <a id="target-c-byteaddress-spec-goal-first-aligned-offset"></a>[first_aligned_offset](../ZlibF/Spec/ByteAddress.lean#L77) | [Registered proof](./progress.md#status-registered) | See target statement | [C.ByteAddress.Proofs.first_aligned_offset](../ZlibF/Proof/ByteAddress.lean#L67) |
| <a id="target-c-byteaddress-spec-goal-byte-stores-preserve-bases"></a>[byte_stores_preserve_bases](../ZlibF/Spec/ByteAddress.lean#L83) | [Registered proof](./progress.md#status-registered) | See target statement | [C.ByteAddress.Proofs.byte_stores_preserve_bases](../ZlibF/Proof/ByteAddress.lean#L81) |
| <a id="target-c-byteaddress-spec-goal-byte-modifies-preserve-bases"></a>[byte_modifies_preserve_bases](../ZlibF/Spec/ByteAddress.lean#L87) | [Registered proof](./progress.md#status-registered) | See target statement | [C.ByteAddress.Proofs.byte_modifies_preserve_bases](../ZlibF/Proof/ByteAddress.lean#L88) |

<a id="group-inflate"></a>

### Inflate streams

| Target statement | State | Contract | Proof evidence |
| --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-inflatecopy"></a>[inflateCopy](../ZlibF/Spec/Public/Copy.lean#L27) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/inflate-stream.md#inflatecopy) | — |
| <a id="target-zlibf-spec-public-goal-inflateinit2"></a>[inflateInit2_](../ZlibF/Spec/Public/Initialisation.lean#L90) | [Blocked](./progress.md#status-blocked) | [Contract](../docs/api/inflate-stream.md#inflateinit2_) | [Blocker: Inflate initialization cleanup](./overview.md#inflate-initialization-cleanup) |
| <a id="target-zlibf-spec-public-goal-inflateinit"></a>[inflateInit_](../ZlibF/Spec/Public/Initialisation.lean#L95) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/inflate-stream.md#inflateinit_) | [ZlibF.Spec.Public.Proofs.InflateInit.init15_public](../ZlibF/Proof/public-inflate-init.lean#L81) |
| <a id="target-zlibf-spec-public-goal-inflateresetkeep"></a>[inflateResetKeep](../ZlibF/Spec/Public/Lifecycle.lean#L20) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/inflate-stream.md#inflateresetkeep) | [ZlibF.Spec.Public.InflateResetKeepProof.resetkeep_public](../ZlibF/Proof/public-inflate-reset-keep.lean#L8) |
| <a id="target-zlibf-spec-public-goal-inflatereset"></a>[inflateReset](../ZlibF/Spec/Public/Lifecycle.lean#L32) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/inflate-stream.md#inflatereset) | [ZlibF.Spec.Public.InflateResetProof.reset_public](../ZlibF/Proof/public-inflate-reset.lean#L14) |
| <a id="target-zlibf-spec-public-goal-inflatereset2"></a>[inflateReset2](../ZlibF/Spec/Public/Lifecycle.lean#L43) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/inflate-stream.md#inflatereset2) | [ZlibF.Spec.Public.InflateReset2Proof.reset2_public](../ZlibF/Proof/public-inflate-reset2.lean#L59) |
| <a id="target-zlibf-spec-public-goal-inflateend"></a>[inflateEnd](../ZlibF/Spec/Public/Lifecycle.lean#L60) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/inflate-stream.md#inflateend) | [ZlibF.Spec.Public.InflateEndProof.inflate_end_public](../ZlibF/Proof/public-inflate-end.lean#L53) |
| <a id="target-zlibf-spec-public-goal-inflategetdictionary"></a>[inflateGetDictionary](../ZlibF/Spec/Public/Lifecycle.lean#L77) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/inflate-stream.md#inflategetdictionary) | [ZlibF.Spec.Public.InflateDictionaryProof.inflate_getdict_public](../ZlibF/Proof/public-inflate-getdict.lean#L8) |
| <a id="target-zlibf-spec-public-goal-inflategetheader"></a>[inflateGetHeader](../ZlibF/Spec/Public/Lifecycle.lean#L87) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/inflate-stream.md#inflategetheader) | [ZlibF.Spec.Public.InflateHeaderProof.getheader_public](../ZlibF/Proof/public-inflate-header.lean#L32) |
| <a id="target-zlibf-spec-public-goal-inflatesetdictionary"></a>[inflateSetDictionary](../ZlibF/Spec/Public/Lifecycle.lean#L153) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/inflate-stream.md#inflatesetdictionary) | [ZlibF.Spec.Public.Proofs.inflateSetDictionary_public](../ZlibF/Proof/public-inflate-setdict.lean#L92) |
| <a id="target-zlibf-spec-public-goal-inflatesyncpoint"></a>[inflateSyncPoint](../ZlibF/Spec/Public/StreamQueries.lean#L53) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/inflate-stream.md#inflatesyncpoint) | [ZlibF.Spec.Public.InflateQueryProof.syncpoint_public](../ZlibF/Proof/public-inflate-small-queries.lean#L44) |
| <a id="target-zlibf-spec-public-goal-inflatemark"></a>[inflateMark](../ZlibF/Spec/Public/StreamQueries.lean#L62) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/inflate-stream.md#inflatemark) | [ZlibF.Spec.Public.InflateMarkProof.mark_public](../ZlibF/Proof/public-inflate-mark.lean#L71) |
| <a id="target-zlibf-spec-public-goal-inflatecodesused"></a>[inflateCodesUsed](../ZlibF/Spec/Public/StreamQueries.lean#L73) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/inflate-stream.md#inflatecodesused) | [ZlibF.Spec.Public.Proofs.inflate_codes_used](../ZlibF/Proof/Api/QueryLayout.lean#L71) |
| <a id="target-zlibf-spec-public-goal-inflateundermine"></a>[inflateUndermine](../ZlibF/Spec/Public/StreamQueries.lean#L81) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/inflate-stream.md#inflateundermine) | [ZlibF.Spec.Public.InflateQueryProof.undermine_public](../ZlibF/Proof/public-inflate-small-queries.lean#L60) |
| <a id="target-zlibf-spec-public-goal-inflatevalidate"></a>[inflateValidate](../ZlibF/Spec/Public/StreamQueries.lean#L89) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/inflate-stream.md#inflatevalidate) | [ZlibF.Spec.Public.InflateQueryProof.validate_public](../ZlibF/Proof/public-inflate-small-queries.lean#L75) |
| <a id="target-zlibf-spec-public-goal-inflateprime"></a>[inflatePrime](../ZlibF/Spec/Public/StreamQueries.lean#L100) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/inflate-stream.md#inflateprime) | [ZlibF.Spec.Public.InflatePrimeProof.prime_public](../ZlibF/Proof/public-inflate-prime.lean#L115) |
| <a id="target-zlibf-spec-public-goal-inflate"></a>[inflate](../ZlibF/Spec/Public/Streams.lean#L24) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/inflate-stream.md#inflate) | — |
| <a id="target-zlibf-spec-public-goal-inflatesync"></a>[inflateSync](../ZlibF/Spec/Public/Streams.lean#L160) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/inflate-stream.md#inflatesync) | — |

<a id="group-deflate"></a>

### Deflate streams

| Target statement | State | Contract | Proof evidence |
| --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-deflatecopy"></a>[deflateCopy](../ZlibF/Spec/Public/Copy.lean#L67) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/deflate-stream.md#deflatecopy) | — |
| <a id="target-zlibf-spec-public-goal-deflateinit2"></a>[deflateInit2_](../ZlibF/Spec/Public/Initialisation.lean#L138) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/deflate-stream.md#deflateinit2_) | — |
| <a id="target-zlibf-spec-public-goal-deflateinit"></a>[deflateInit_](../ZlibF/Spec/Public/Initialisation.lean#L145) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/deflate-stream.md#deflateinit_) | — |
| <a id="target-zlibf-spec-public-goal-deflategetdictionary"></a>[deflateGetDictionary](../ZlibF/Spec/Public/Lifecycle.lean#L105) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/deflate-stream.md#deflategetdictionary) | [ZlibF.Spec.Public.DeflateDictionaryProof.deflate_getdict_public](../ZlibF/Proof/public-deflate-getdict.lean#L8) |
| <a id="target-zlibf-spec-public-goal-deflateend"></a>[deflateEnd](../ZlibF/Spec/Public/Lifecycle.lean#L115) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/deflate-stream.md#deflateend) | [ZlibF.Spec.Public.DeflateEndProof.deflate_end_public](../ZlibF/Proof/public-deflate-end.lean#L8) |
| <a id="target-zlibf-spec-public-goal-deflateresetkeep"></a>[deflateResetKeep](../ZlibF/Spec/Public/Lifecycle.lean#L146) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/deflate-stream.md#deflateresetkeep) | [ZlibF.Spec.Public.DeflateResetKeepProof.deflate_resetkeep_public](../ZlibF/Proof/public-deflate-reset-keep.lean#L17) |
| <a id="target-zlibf-spec-public-goal-deflatereset"></a>[deflateReset](../ZlibF/Spec/Public/Lifecycle.lean#L149) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/deflate-stream.md#deflatereset) | [ZlibF.Spec.Public.DeflateResetProof.deflate_reset_public](../ZlibF/Proof/public-deflate-reset.lean#L50) |
| <a id="target-zlibf-spec-public-goal-deflatesetdictionary"></a>[deflateSetDictionary](../ZlibF/Spec/Public/Lifecycle.lean#L175) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/deflate-stream.md#deflatesetdictionary) | — |
| <a id="target-zlibf-spec-public-goal-deflatepending"></a>[deflatePending](../ZlibF/Spec/Public/StreamQueries.lean#L113) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/deflate-stream.md#deflatepending) | [ZlibF.Spec.Public.DeflateQueryProof.pending_public](../ZlibF/Proof/public-deflate-small-queries.lean#L145) |
| <a id="target-zlibf-spec-public-goal-deflateused"></a>[deflateUsed](../ZlibF/Spec/Public/StreamQueries.lean#L124) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/deflate-stream.md#deflateused) | [ZlibF.Spec.Public.DeflateQueryProof.used_public](../ZlibF/Proof/public-deflate-small-queries.lean#L48) |
| <a id="target-zlibf-spec-public-goal-deflatetune"></a>[deflateTune](../ZlibF/Spec/Public/StreamQueries.lean#L132) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/deflate-stream.md#deflatetune) | [ZlibF.Spec.Public.DeflateQueryProof.tune_public](../ZlibF/Proof/public-deflate-small-queries.lean#L61) |
| <a id="target-zlibf-spec-public-goal-deflatesetheader"></a>[deflateSetHeader](../ZlibF/Spec/Public/StreamQueries.lean#L145) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/deflate-stream.md#deflatesetheader) | [ZlibF.Spec.Public.DeflateQueryProof.header_public](../ZlibF/Proof/public-deflate-small-queries.lean#L74) |
| <a id="target-zlibf-spec-public-goal-deflate"></a>[deflate](../ZlibF/Spec/Public/Streams.lean#L51) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/deflate-stream.md#deflate) | — |
| <a id="target-zlibf-spec-public-goal-deflatebound-z"></a>[deflateBound_z](../ZlibF/Spec/Public/Streams.lean#L105) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/deflate-stream.md#deflatebound_z) | — |
| <a id="target-zlibf-spec-public-goal-deflatebound"></a>[deflateBound](../ZlibF/Spec/Public/Streams.lean#L109) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/deflate-stream.md#deflatebound) | — |
| <a id="target-zlibf-spec-public-goal-deflateprime"></a>[deflatePrime](../ZlibF/Spec/Public/Streams.lean#L119) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/deflate-stream.md#deflateprime) | — |
| <a id="target-zlibf-spec-public-goal-deflateparams"></a>[deflateParams](../ZlibF/Spec/Public/Streams.lean#L137) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/deflate-stream.md#deflateparams) | — |

<a id="group-back"></a>

### Callback decoding

| Target statement | State | Contract | Proof evidence |
| --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-inflatebackinit"></a>[inflateBackInit_](../ZlibF/Spec/Public/Back.lean#L22) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/inflate-back.md#inflatebackinit_) | [ZlibF.Spec.Public.InflateBackInitProof.back_init_public](../ZlibF/Proof/public-infback-init.lean#L133) |
| <a id="target-zlibf-spec-public-goal-inflateback"></a>[inflateBack](../ZlibF/Spec/Public/Back.lean#L115) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/inflate-back.md#inflateback) | — |
| <a id="target-zlibf-spec-public-goal-inflatebackend"></a>[inflateBackEnd](../ZlibF/Spec/Public/Back.lean#L142) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/inflate-back.md#inflatebackend) | [ZlibF.Spec.Public.InflateBackEndProof.back_end_public](../ZlibF/Proof/public-infback-end.lean#L18) |

<a id="group-gzip"></a>

### Gzip files

| Target statement | State | Contract | Proof evidence |
| --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-gzclose-r"></a>[gzclose_r](../ZlibF/Spec/Public/GzClose.lean#L35) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/gz-file.md#gzclose_r) | — |
| <a id="target-zlibf-spec-public-goal-gzclose-w"></a>[gzclose_w](../ZlibF/Spec/Public/GzClose.lean#L40) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/gz-file.md#gzclose_w) | — |
| <a id="target-zlibf-spec-public-goal-gzclose"></a>[gzclose](../ZlibF/Spec/Public/GzClose.lean#L44) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/gz-file.md#gzclose) | — |
| <a id="target-zlibf-spec-public-goal-gzbuffer"></a>[gzbuffer](../ZlibF/Spec/Public/GzControl.lean#L12) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/gz-file.md#gzbuffer) | [ZlibF.Spec.Public.Proofs.gzbuffer_public](../ZlibF/Proof/public-gzbuffer.lean#L49) |
| <a id="target-zlibf-spec-public-goal-gzeof"></a>[gzeof](../ZlibF/Spec/Public/GzControl.lean#L22) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/gz-file.md#gzeof) | [ZlibF.Spec.Public.Proofs.gzeof_public](../ZlibF/Proof/public-gzeof.lean#L18) |
| <a id="target-zlibf-spec-public-goal-gztell64"></a>[gztell64](../ZlibF/Spec/Public/GzControl.lean#L36) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/gz-file.md#gztell64) | — |
| <a id="target-zlibf-spec-public-goal-gztell"></a>[gztell](../ZlibF/Spec/Public/GzControl.lean#L39) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/gz-file.md#gztell) | — |
| <a id="target-zlibf-spec-public-goal-gzoffset64"></a>[gzoffset64](../ZlibF/Spec/Public/GzControl.lean#L53) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/gz-file.md#gzoffset64) | [ZlibF.Spec.Public.OffsetProof.gzoffset64_public_goal](../ZlibF/Proof/public-gz-offset.lean#L197) |
| <a id="target-zlibf-spec-public-goal-gzoffset"></a>[gzoffset](../ZlibF/Spec/Public/GzControl.lean#L56) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/gz-file.md#gzoffset) | [ZlibF.Spec.Public.OffsetProof.gzoffset_public_goal](../ZlibF/Proof/public-gz-offset.lean#L207) |
| <a id="target-zlibf-spec-public-goal-gzerror"></a>[gzerror](../ZlibF/Spec/Public/GzControl.lean#L63) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/gz-file.md#gzerror) | [ZlibF.Spec.Public.GzErrorProof.gzerror](../ZlibF/Proof/public-gz-error.lean#L197) |
| <a id="target-zlibf-spec-public-goal-gzclearerr"></a>[gzclearerr](../ZlibF/Spec/Public/GzControl.lean#L74) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/gz-file.md#gzclearerr) | [ZlibF.Spec.Public.Proofs.gzclearerr](../ZlibF/Proof/gzlib.c.public-clearerr.lean#L28) |
| <a id="target-zlibf-spec-public-goal-gzrewind"></a>[gzrewind](../ZlibF/Spec/Public/GzControl.lean#L91) | [Locally checked](./progress.md#status-local) | [Contract](../docs/api/gz-file.md#gzrewind) | [ZlibF.Spec.Public.GzRewindProof.rewind_public](../ZlibF/Proof/public-gz-rewind.lean#L65) |
| <a id="target-zlibf-spec-public-goal-gzseek64"></a>[gzseek64](../ZlibF/Spec/Public/GzControl.lean#L116) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/gz-file.md#gzseek64) | — |
| <a id="target-zlibf-spec-public-goal-gzseek"></a>[gzseek](../ZlibF/Spec/Public/GzControl.lean#L119) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/gz-file.md#gzseek) | — |
| <a id="target-zlibf-spec-public-goal-gzopen"></a>[gzopen](../ZlibF/Spec/Public/GzOpen.lean#L61) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/gz-file.md#gzopen) | — |
| <a id="target-zlibf-spec-public-goal-gzopen64"></a>[gzopen64](../ZlibF/Spec/Public/GzOpen.lean#L65) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/gz-file.md#gzopen64) | — |
| <a id="target-zlibf-spec-public-goal-gzdopen"></a>[gzdopen](../ZlibF/Spec/Public/GzOpen.lean#L70) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/gz-file.md#gzdopen) | — |
| <a id="target-zlibf-spec-public-goal-gzread"></a>[gzread](../ZlibF/Spec/Public/GzRead.lean#L22) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/gz-file.md#gzread) | — |
| <a id="target-zlibf-spec-public-goal-gzfread"></a>[gzfread](../ZlibF/Spec/Public/GzRead.lean#L37) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/gz-file.md#gzfread) | — |
| <a id="target-zlibf-spec-public-goal-gzgetc"></a>[gzgetc](../ZlibF/Spec/Public/GzRead.lean#L58) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/gz-file.md#gzgetc) | — |
| <a id="target-zlibf-spec-public-goal-gzgetc"></a>[gzgetc_](../ZlibF/Spec/Public/GzRead.lean#L61) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/gz-file.md#gzgetc_) | — |
| <a id="target-zlibf-spec-public-goal-gzungetc"></a>[gzungetc](../ZlibF/Spec/Public/GzRead.lean#L66) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/gz-file.md#gzungetc) | — |
| <a id="target-zlibf-spec-public-goal-gzgets"></a>[gzgets](../ZlibF/Spec/Public/GzRead.lean#L80) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/gz-file.md#gzgets) | — |
| <a id="target-zlibf-spec-public-goal-gzdirect"></a>[gzdirect](../ZlibF/Spec/Public/GzRead.lean#L103) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/gz-file.md#gzdirect) | — |
| <a id="target-zlibf-spec-public-goal-gzwrite"></a>[gzwrite](../ZlibF/Spec/Public/GzWrite.lean#L28) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/gz-file.md#gzwrite) | — |
| <a id="target-zlibf-spec-public-goal-gzfwrite"></a>[gzfwrite](../ZlibF/Spec/Public/GzWrite.lean#L43) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/gz-file.md#gzfwrite) | — |
| <a id="target-zlibf-spec-public-goal-gzputc"></a>[gzputc](../ZlibF/Spec/Public/GzWrite.lean#L59) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/gz-file.md#gzputc) | — |
| <a id="target-zlibf-spec-public-goal-gzputs"></a>[gzputs](../ZlibF/Spec/Public/GzWrite.lean#L71) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/gz-file.md#gzputs) | — |
| <a id="target-zlibf-spec-public-goal-gzvprintf"></a>[gzvprintf](../ZlibF/Spec/Public/GzWrite.lean#L102) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/gz-file.md#gzvprintf) | — |
| <a id="target-zlibf-spec-public-goal-gzprintf"></a>[gzprintf](../ZlibF/Spec/Public/GzWrite.lean#L106) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/gz-file.md#gzprintf) | — |
| <a id="target-zlibf-spec-public-goal-gzflush"></a>[gzflush](../ZlibF/Spec/Public/GzWrite.lean#L111) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/gz-file.md#gzflush) | — |
| <a id="target-zlibf-spec-public-goal-gzsetparams"></a>[gzsetparams](../ZlibF/Spec/Public/GzWrite.lean#L128) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/gz-file.md#gzsetparams) | — |

<a id="group-buffers"></a>

### Whole-buffer operations

| Target statement | State | Contract | Proof evidence |
| --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-compress2-z"></a>[compress2_z](../ZlibF/Spec/Public/Utilities.lean#L40) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/utility.md#compress2_z) | — |
| <a id="target-zlibf-spec-public-goal-compress2"></a>[compress2](../ZlibF/Spec/Public/Utilities.lean#L45) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/utility.md#compress2) | — |
| <a id="target-zlibf-spec-public-goal-compress-z"></a>[compress_z](../ZlibF/Spec/Public/Utilities.lean#L52) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/utility.md#compress_z) | — |
| <a id="target-zlibf-spec-public-goal-compress"></a>[compress](../ZlibF/Spec/Public/Utilities.lean#L57) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/utility.md#compress) | — |
| <a id="target-zlibf-spec-public-goal-uncompress2-z"></a>[uncompress2_z](../ZlibF/Spec/Public/Utilities.lean#L103) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/utility.md#uncompress2_z) | — |
| <a id="target-zlibf-spec-public-goal-uncompress2"></a>[uncompress2](../ZlibF/Spec/Public/Utilities.lean#L107) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/utility.md#uncompress2) | — |
| <a id="target-zlibf-spec-public-goal-uncompress-z"></a>[uncompress_z](../ZlibF/Spec/Public/Utilities.lean#L132) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/utility.md#uncompress_z) | — |
| <a id="target-zlibf-spec-public-goal-uncompress"></a>[uncompress](../ZlibF/Spec/Public/Utilities.lean#L136) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/utility.md#uncompress) | — |

<a id="group-models"></a>

### Format and API models

| Target statement | State | Contract | Proof evidence |
| --- | --- | --- | --- |
| <a id="target-zlibf-spec-api-goal-format-deterministic"></a>[format_deterministic](../ZlibF/Spec/Api/Goals.lean#L42) | [Registered proof](./progress.md#status-registered) | See target statement | [ZlibF.Spec.Api.Proofs.format_deterministic](../ZlibF/Proof/Format/Api.lean#L51) |
| <a id="target-zlibf-spec-api-goal-format-prefix-free"></a>[format_prefix_free](../ZlibF/Spec/Api/Goals.lean#L47) | [Registered proof](./progress.md#status-registered) | See target statement | [ZlibF.Spec.Api.Proofs.format_prefix_free](../ZlibF/Proof/Format/Api.lean#L56) |
| <a id="target-zlibf-spec-api-goal-inflate-decodes"></a>[inflate_decodes](../ZlibF/Spec/Api/Goals.lean#L58) | [Locally checked](./progress.md#status-local) | See target statement | [ZlibF.Spec.Api.Proofs.inflate_decodes](../ZlibF/Proof/Api/Inflate.lean#L346) |
| <a id="target-zlibf-spec-api-goal-inflate-completes"></a>[inflate_completes](../ZlibF/Spec/Api/Goals.lean#L69) | [Locally checked](./progress.md#status-local) | See target statement | [ZlibF.Spec.Api.Proofs.inflate_completes](../ZlibF/Proof/Api/Inflate.lean#L353) |
| <a id="target-zlibf-spec-api-goal-inflate-rejects-invalid"></a>[inflate_rejects_invalid](../ZlibF/Spec/Api/Goals.lean#L84) | [Not proved](./progress.md#status-open) | See target statement | — |
| <a id="target-zlibf-spec-api-goal-deflate-valid"></a>[deflate_valid](../ZlibF/Spec/Api/Goals.lean#L99) | [Locally checked](./progress.md#status-local) | See target statement | [ZlibF.Spec.Api.Proofs.deflate_valid](../ZlibF/Proof/Api/Deflate.lean#L181) |
| <a id="target-zlibf-spec-api-goal-deflate-completes"></a>[deflate_completes](../ZlibF/Spec/Api/Goals.lean#L106) | [Locally checked](./progress.md#status-local) | See target statement | [ZlibF.Spec.Api.Proofs.deflate_completes](../ZlibF/Proof/Api/DeflateBounds.lean#L164) |
| <a id="target-zlibf-spec-api-goal-deflate-full-flush-resync"></a>[deflate_full_flush_resync](../ZlibF/Spec/Api/Goals.lean#L116) | [Locally checked](./progress.md#status-local) | See target statement | [ZlibF.Spec.Api.Proofs.deflate_full_flush_resync](../ZlibF/Proof/Api/DeflateFlush.lean#L169) |
| <a id="target-zlibf-spec-api-goal-roundtrip"></a>[roundtrip](../ZlibF/Spec/Api/Goals.lean#L134) | [Locally checked](./progress.md#status-local) | See target statement | [ZlibF.Spec.Api.Proofs.roundtrip](../ZlibF/Proof/Api/GzipRoundtrip.lean#L177) |
| <a id="target-zlibf-spec-api-goal-roundtrip-completes"></a>[roundtrip_completes](../ZlibF/Spec/Api/Goals.lean#L143) | [Locally checked](./progress.md#status-local) | See target statement | [ZlibF.Spec.Api.Proofs.roundtrip_completes](../ZlibF/Proof/Api/GzipRoundtrip.lean#L186) |
| <a id="target-zlibf-spec-api-goal-dict-roundtrip"></a>[dict_roundtrip](../ZlibF/Spec/Api/Goals.lean#L162) | [Locally checked](./progress.md#status-local) | See target statement | [ZlibF.Spec.Api.Proofs.dict_roundtrip](../ZlibF/Proof/Api/DictionaryRoundtrip.lean#L121) |
| <a id="target-zlibf-spec-api-goal-header-roundtrip"></a>[header_roundtrip](../ZlibF/Spec/Api/Goals.lean#L180) | [Locally checked](./progress.md#status-local) | See target statement | [ZlibF.Spec.Api.Proofs.header_roundtrip](../ZlibF/Proof/Api/HeaderRoundtrip.lean#L89) |
| <a id="target-zlibf-spec-api-goal-deflate-bound-adequate"></a>[deflate_bound_adequate](../ZlibF/Spec/Api/Goals.lean#L189) | [Locally checked](./progress.md#status-local) | See target statement | [ZlibF.Spec.Api.Proofs.deflate_bound_adequate](../ZlibF/Proof/Api/DeflateBounds.lean#L103) |
| <a id="target-zlibf-spec-api-goal-compress-bound-adequate"></a>[compress_bound_adequate](../ZlibF/Spec/Api/Goals.lean#L196) | [Locally checked](./progress.md#status-local) | See target statement | [ZlibF.Spec.Api.Proofs.compress_bound_adequate](../ZlibF/Proof/Api/Compress.lean#L8) |
| <a id="target-zlibf-spec-api-goal-compress-roundtrip"></a>[compress_roundtrip](../ZlibF/Spec/Api/Goals.lean#L203) | [Locally checked](./progress.md#status-local) | See target statement | [ZlibF.Spec.Api.Proofs.compress_roundtrip](../ZlibF/Proof/Api/CompressRoundtrip.lean#L32) |
| <a id="target-zlibf-spec-api-goal-gz-roundtrip"></a>[gz_roundtrip](../ZlibF/Spec/Api/Goals.lean#L214) | [Locally checked](./progress.md#status-local) | See target statement | [ZlibF.Spec.Api.Proofs.gz_roundtrip](../ZlibF/Proof/Api/GzRoundtrip.lean#L15) |
| <a id="target-zlibf-spec-api-goal-gz-seek-read"></a>[gz_seek_read](../ZlibF/Spec/Api/Goals.lean#L221) | [Blocked](./progress.md#status-blocked) | See target statement | [Blocker: Gzip seek mode](./overview.md#gzip-seek-mode) |
| <a id="target-zlibf-spec-api-goal-compress-bound-value"></a>[compress_bound_value](../ZlibF/Spec/Api/Concrete.lean#L57) | [Locally checked](./progress.md#status-local) | See target statement | [ZlibF.Spec.Api.Proofs.compress_bound_value](../ZlibF/Proof/Api/Concrete.lean#L57) |
| <a id="target-zlibf-spec-api-goal-compress2-z-first-alloc-failure"></a>[compress2_z_first_alloc_failure](../ZlibF/Spec/Api/Concrete.lean#L67) | [Locally checked](./progress.md#status-local) | See target statement | [ZlibF.Spec.Api.Proofs.compress2_z_first_alloc_failure](../ZlibF/Proof/Api/CompressFailure.lean#L29) |
| <a id="target-zlibf-spec-api-goal-inflate-deferred-distance"></a>[inflate_deferred_distance](../ZlibF/Spec/Api/Inflate.lean#L267) | [Registered proof](./progress.md#status-registered) | See target statement | [ZlibF.Spec.Api.Proofs.inflate_deferred_distance](../ZlibF/Proof/Api/InflateCausality.lean#L244) |

<a id="group-lifecycle"></a>

### Lifecycles and call sequences

| Target statement | State | Contract | Proof evidence |
| --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-inflate-sequence"></a>[inflate_sequence](../ZlibF/Spec/Public/Sequences.lean#L158) | [Not proved](./progress.md#status-open) | See target statement | — |
| <a id="target-zlibf-spec-public-goal-deflate-sequence"></a>[deflate_sequence](../ZlibF/Spec/Public/Sequences.lean#L172) | [Not proved](./progress.md#status-open) | See target statement | — |
| <a id="target-zlibf-spec-public-goal-inflate-back-sequence"></a>[inflate_back_sequence](../ZlibF/Spec/Public/Sequences.lean#L199) | [Not proved](./progress.md#status-open) | See target statement | — |
| <a id="target-zlibf-spec-public-goal-gz-sequence"></a>[gz_sequence](../ZlibF/Spec/Public/Sequences.lean#L211) | [Not proved](./progress.md#status-open) | See target statement | — |
| <a id="target-zlibf-spec-public-goal-inflate-initialisation-domain"></a>[inflate_initialisation_domain](../ZlibF/Spec/Public/Domains.lean#L24) | [Locally checked](./progress.md#status-local) | See target statement | [ZlibF.Spec.Public.Proofs.InflateInit.inflate_initialisation_domain_public](../ZlibF/Proof/public-inflate-init.lean#L259) |
| <a id="target-zlibf-spec-public-goal-deflate-initialisation-domain"></a>[deflate_initialisation_domain](../ZlibF/Spec/Public/Domains.lean#L37) | [Not proved](./progress.md#status-open) | See target statement | — |
| <a id="target-zlibf-spec-public-goal-inflate-back-initialisation-domain"></a>[inflate_back_initialisation_domain](../ZlibF/Spec/Public/Domains.lean#L53) | [Locally checked](./progress.md#status-local) | See target statement | [ZlibF.Spec.Public.InflateBackInitProof.back_init_domain_public](../ZlibF/Proof/public-infback-init.lean#L226) |
| <a id="target-zlibf-spec-public-goal-gz-initialisation-domain"></a>[gz_initialisation_domain](../ZlibF/Spec/Public/Domains.lean#L77) | [Not proved](./progress.md#status-open) | See target statement | — |

## Refresh

Run `python3 scripts/proof-progress.py` from the repository root after proof or registry
updates. It rechecks source hashes, builds the root without downloading cached artifacts,
and inspects exact compiled theorem types. It updates this page
and only the marked graph section at the top of overview. `--check` detects stale views.
It never changes a registry, target, proof, lock or verification gate.
Use the [acceptance checks](checking/README.md) for acceptance evidence.
Current work and remaining tasks are maintained only in [overview](overview.md).

Input fingerprint: `a96576bbae930a79a7c7d610152a3275de2640526bdd92f892fddea2e74059eb`.
