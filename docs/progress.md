# Public API proof target graph

<!-- proof-link-revision: 211d239ee21162caefbf651aa597f0f595d1c374 -->

[Documentation](README.md) · [Current work and group graph](overview.md) · [Supporting proofs](supporting-proofs.md)

This generated view contains **103 public API targets**.
The scope is the public API manifest: function contracts, call sequences and initialization domains. Internal obligations and abstract models have a separate supporting page.
Each target is from `tests/audit/goals.txt`. Colours report the freshly built
local environment, not final acceptance. A checked theorem must have exactly the target
as its type and use only allowed axioms. Source-only candidates never count as checked.
The numbers count targets, not proof difficulty or percentage of effort.

## Status key

| Status | Targets | Meaning |
| --- | ---: | --- |
| <a id="status-registered"></a>Registered proof | 50 | 🟩 Exact checked proof listed in the theorem registry. |
| <a id="status-local"></a>Locally checked | 0 | 🟦 Exact checked proof, not yet registered. |
| <a id="status-open"></a>Not proved | 52 | ⬜ No exact checked proof or documented blocker. Source drafts do not count. |
| <a id="status-blocked"></a>Blocked | 1 | 🟥 Not proved; a documented obstacle needs resolution. Click for its reason and next step. |

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
| [inflateInit2_](./progress.md#target-zlibf-spec-public-goal-inflateinit2) | [Inflate initialization cleanup](./overview.md#inflate-initialization-cleanup) |

Red marks an explicit blocker recorded in overview, not elapsed time or proof difficulty.
Other targets are not marked red merely because they call a blocked function.

**Why can an isolated node be unfinished?** The public graph omits supporting goals.
The supporting module graph records source references, not a complete proof plan.
No arrows means no displayed link, not that a proof exists or is easy.
Green requires a checked, registered exact proof. See the
[supporting proofs](supporting-proofs.md) and [representation limits](trusted-base.md).

## Clickable index

Diagram links open a fixed GitHub snapshot, `211d239`.
A target opens its specification. Red targets open their blocker;
groups open their specification file or folder. These links survive merges and branch deletion.
Some Markdown viewers disable diagram links; use the ordinary tables in that case.
Table links remain document-relative and follow the branch being viewed on GitHub.
Local previews open the corresponding local documents.

| Group | Targets |
| --- | ---: |
| [Library queries](./progress.md#group-queries) | 6 |
| [Checksums](./progress.md#group-checksums) | 11 |
| [Inflate streams](./progress.md#group-inflate) | 18 |
| [Deflate streams](./progress.md#group-deflate) | 17 |
| [Callback decoding](./progress.md#group-back) | 3 |
| [Gzip files](./progress.md#group-gzip) | 32 |
| [Whole-buffer operations](./progress.md#group-buffers) | 8 |
| [Lifecycles and call sequences](./progress.md#group-lifecycle) | 8 |

## Public API targets



```mermaid
flowchart LR
  subgraph queries["Library queries"]
    n0["compressBound"]:::registered
    n1["compressBound_z"]:::registered
    n2["zlibVersion"]:::registered
    n3["zlibCompileFlags"]:::registered
    n4["zError"]:::registered
    n11["get_crc_table"]:::registered
  end
  subgraph checksums["Checksums"]
    n5["adler32"]:::registered
    n6["adler32_z"]:::registered
    n7["adler32_combine"]:::registered
    n8["adler32_combine64"]:::registered
    n9["crc32"]:::registered
    n10["crc32_z"]:::registered
    n12["crc32_combine_gen"]:::registered
    n13["crc32_combine_gen64"]:::registered
    n14["crc32_combine_op"]:::registered
    n15["crc32_combine"]:::registered
    n16["crc32_combine64"]:::registered
  end
  subgraph inflate["Inflate streams"]
    n20["inflateCopy"]:::open
    n54["inflateInit2_<br/>Blocked"]:::blocked
    n55["inflateInit_"]:::registered
    n58["inflateResetKeep"]:::registered
    n59["inflateReset"]:::registered
    n60["inflateReset2"]:::registered
    n61["inflateEnd"]:::registered
    n62["inflateGetDictionary"]:::registered
    n63["inflateGetHeader"]:::registered
    n68["inflateSetDictionary"]:::registered
    n70["inflateSyncPoint"]:::registered
    n71["inflateMark"]:::registered
    n72["inflateCodesUsed"]:::registered
    n73["inflateUndermine"]:::registered
    n74["inflateValidate"]:::registered
    n75["inflatePrime"]:::registered
    n80["inflate"]:::open
    n86["inflateSync"]:::open
  end
  subgraph deflate["Deflate streams"]
    n21["deflateCopy"]:::open
    n56["deflateInit2_"]:::open
    n57["deflateInit_"]:::open
    n64["deflateGetDictionary"]:::registered
    n65["deflateEnd"]:::registered
    n66["deflateResetKeep"]:::registered
    n67["deflateReset"]:::registered
    n69["deflateSetDictionary"]:::open
    n76["deflatePending"]:::registered
    n77["deflateUsed"]:::registered
    n78["deflateTune"]:::registered
    n79["deflateSetHeader"]:::registered
    n81["deflate"]:::open
    n82["deflateBound_z"]:::open
    n83["deflateBound"]:::open
    n84["deflatePrime"]:::open
    n85["deflateParams"]:::open
  end
  subgraph back["Callback decoding"]
    n17["inflateBackInit_"]:::registered
    n18["inflateBack"]:::open
    n19["inflateBackEnd"]:::registered
  end
  subgraph gzip["Gzip files"]
    n22["gzclose_r"]:::open
    n23["gzclose_w"]:::open
    n24["gzclose"]:::open
    n25["gzbuffer"]:::registered
    n26["gzeof"]:::registered
    n27["gztell64"]:::open
    n28["gztell"]:::open
    n29["gzoffset64"]:::registered
    n30["gzoffset"]:::registered
    n31["gzerror"]:::registered
    n32["gzclearerr"]:::registered
    n33["gzrewind"]:::registered
    n34["gzseek64"]:::open
    n35["gzseek"]:::open
    n36["gzopen"]:::open
    n37["gzopen64"]:::open
    n38["gzdopen"]:::open
    n39["gzread"]:::open
    n40["gzfread"]:::open
    n41["gzgetc"]:::open
    n42["gzgetc_"]:::open
    n43["gzungetc"]:::open
    n44["gzgets"]:::open
    n45["gzdirect"]:::open
    n46["gzwrite"]:::open
    n47["gzfwrite"]:::open
    n48["gzputc"]:::open
    n49["gzputs"]:::open
    n50["gzvprintf"]:::open
    n51["gzprintf"]:::open
    n52["gzflush"]:::open
    n53["gzsetparams"]:::open
  end
  subgraph buffers["Whole-buffer operations"]
    n87["compress2_z"]:::open
    n88["compress2"]:::open
    n89["compress_z"]:::open
    n90["compress"]:::open
    n91["uncompress2_z"]:::open
    n92["uncompress2"]:::open
    n93["uncompress_z"]:::open
    n94["uncompress"]:::open
  end
  subgraph lifecycle["Lifecycles and call sequences"]
    n95["inflate_sequence"]:::open
    n96["deflate_sequence"]:::open
    n97["inflate_back_sequence"]:::open
    n98["gz_sequence"]:::open
    n99["inflate_initialisation_domain"]:::registered
    n100["deflate_initialisation_domain"]:::open
    n101["inflate_back_initialisation_domain"]:::registered
    n102["gz_initialisation_domain"]:::open
  end
  n5 --> n81
  n5 --> n66
  n5 --> n69
  n5 --> n80
  n5 --> n68
  n6 --> n5
  n88 --> n90
  n87 --> n88
  n87 --> n89
  n1 --> n0
  n9 --> n81
  n9 --> n66
  n9 --> n69
  n9 --> n80
  n16 --> n15
  n13 --> n16
  n13 --> n12
  n14 --> n16
  n10 --> n9
  n10 --> n81
  n81 --> n87
  n81 --> n85
  n81 --> n23
  n81 --> n52
  n81 --> n47
  n81 --> n48
  n81 --> n49
  n81 --> n53
  n81 --> n50
  n81 --> n46
  n82 --> n83
  n65 --> n87
  n65 --> n56
  n65 --> n23
  n56 --> n57
  n56 -.-> n100
  n56 --> n23
  n56 --> n52
  n56 --> n47
  n56 --> n48
  n56 --> n49
  n56 --> n53
  n56 --> n50
  n56 --> n46
  n57 --> n87
  n85 --> n53
  n67 --> n56
  n67 --> n23
  n67 --> n52
  n67 --> n47
  n67 --> n48
  n67 --> n49
  n67 --> n53
  n67 --> n50
  n67 --> n46
  n66 --> n67
  n24 -.-> n98
  n22 --> n24
  n23 --> n24
  n52 -.-> n98
  n40 -.-> n98
  n47 -.-> n98
  n41 -.-> n98
  n41 --> n42
  n44 -.-> n98
  n29 --> n30
  n36 -.-> n102
  n39 -.-> n98
  n33 --> n34
  n34 --> n35
  n27 --> n28
  n50 --> n51
  n46 -.-> n98
  n80 --> n40
  n80 --> n41
  n80 --> n44
  n80 --> n39
  n80 --> n43
  n80 --> n91
  n18 -.-> n97
  n19 -.-> n97
  n17 -.-> n101
  n61 --> n22
  n61 --> n91
  n54 --> n45
  n54 --> n40
  n54 --> n41
  n54 --> n44
  n54 --> n39
  n54 --> n43
  n54 --> n55
  n54 -.-> n99
  n55 --> n91
  n59 --> n45
  n59 --> n40
  n59 --> n41
  n59 --> n44
  n59 --> n39
  n59 --> n43
  n59 --> n60
  n59 --> n86
  n60 --> n54
  n58 --> n59
  n92 --> n94
  n91 --> n92
  n91 --> n93
  n4 --> n81
  n4 --> n56
  n2 --> n87
  click n0 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Queries.lean#L35" "Open target specification" _blank
  click n1 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Queries.lean#L40" "Open target specification" _blank
  click n2 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Queries.lean#L46" "Open target specification" _blank
  click n3 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Queries.lean#L53" "Open target specification" _blank
  click n4 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Queries.lean#L59" "Open target specification" _blank
  click n5 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Checksums.lean#L66" "Open target specification" _blank
  click n6 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Checksums.lean#L61" "Open target specification" _blank
  click n7 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Checksums.lean#L86" "Open target specification" _blank
  click n8 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Checksums.lean#L90" "Open target specification" _blank
  click n9 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Checksums.lean#L117" "Open target specification" _blank
  click n10 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Checksums.lean#L109" "Open target specification" _blank
  click n11 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Checksums.lean#L126" "Open target specification" _blank
  click n12 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Checksums.lean#L140" "Open target specification" _blank
  click n13 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Checksums.lean#L143" "Open target specification" _blank
  click n14 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Checksums.lean#L150" "Open target specification" _blank
  click n15 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Checksums.lean#L162" "Open target specification" _blank
  click n16 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Checksums.lean#L165" "Open target specification" _blank
  click n17 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Back.lean#L22" "Open target specification" _blank
  click n18 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Back.lean#L115" "Open target specification" _blank
  click n19 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Back.lean#L142" "Open target specification" _blank
  click n20 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Copy.lean#L27" "Open target specification" _blank
  click n21 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Copy.lean#L67" "Open target specification" _blank
  click n22 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/GzClose.lean#L35" "Open target specification" _blank
  click n23 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/GzClose.lean#L40" "Open target specification" _blank
  click n24 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/GzClose.lean#L44" "Open target specification" _blank
  click n25 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/GzControl.lean#L12" "Open target specification" _blank
  click n26 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/GzControl.lean#L22" "Open target specification" _blank
  click n27 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/GzControl.lean#L36" "Open target specification" _blank
  click n28 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/GzControl.lean#L39" "Open target specification" _blank
  click n29 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/GzControl.lean#L53" "Open target specification" _blank
  click n30 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/GzControl.lean#L56" "Open target specification" _blank
  click n31 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/GzControl.lean#L63" "Open target specification" _blank
  click n32 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/GzControl.lean#L74" "Open target specification" _blank
  click n33 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/GzControl.lean#L91" "Open target specification" _blank
  click n34 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/GzControl.lean#L116" "Open target specification" _blank
  click n35 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/GzControl.lean#L119" "Open target specification" _blank
  click n36 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/GzOpen.lean#L61" "Open target specification" _blank
  click n37 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/GzOpen.lean#L65" "Open target specification" _blank
  click n38 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/GzOpen.lean#L70" "Open target specification" _blank
  click n39 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/GzRead.lean#L22" "Open target specification" _blank
  click n40 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/GzRead.lean#L37" "Open target specification" _blank
  click n41 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/GzRead.lean#L58" "Open target specification" _blank
  click n42 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/GzRead.lean#L61" "Open target specification" _blank
  click n43 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/GzRead.lean#L66" "Open target specification" _blank
  click n44 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/GzRead.lean#L80" "Open target specification" _blank
  click n45 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/GzRead.lean#L103" "Open target specification" _blank
  click n46 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/GzWrite.lean#L28" "Open target specification" _blank
  click n47 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/GzWrite.lean#L43" "Open target specification" _blank
  click n48 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/GzWrite.lean#L59" "Open target specification" _blank
  click n49 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/GzWrite.lean#L71" "Open target specification" _blank
  click n50 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/GzWrite.lean#L102" "Open target specification" _blank
  click n51 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/GzWrite.lean#L106" "Open target specification" _blank
  click n52 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/GzWrite.lean#L111" "Open target specification" _blank
  click n53 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/GzWrite.lean#L128" "Open target specification" _blank
  click n54 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/docs/overview.md#inflate-initialization-cleanup" "Open blocker reason and next step" _blank
  click n55 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Initialisation.lean#L95" "Open target specification" _blank
  click n56 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Initialisation.lean#L138" "Open target specification" _blank
  click n57 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Initialisation.lean#L145" "Open target specification" _blank
  click n58 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Lifecycle.lean#L20" "Open target specification" _blank
  click n59 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Lifecycle.lean#L32" "Open target specification" _blank
  click n60 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Lifecycle.lean#L43" "Open target specification" _blank
  click n61 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Lifecycle.lean#L60" "Open target specification" _blank
  click n62 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Lifecycle.lean#L77" "Open target specification" _blank
  click n63 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Lifecycle.lean#L87" "Open target specification" _blank
  click n64 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Lifecycle.lean#L105" "Open target specification" _blank
  click n65 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Lifecycle.lean#L115" "Open target specification" _blank
  click n66 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Lifecycle.lean#L146" "Open target specification" _blank
  click n67 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Lifecycle.lean#L149" "Open target specification" _blank
  click n68 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Lifecycle.lean#L153" "Open target specification" _blank
  click n69 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Lifecycle.lean#L175" "Open target specification" _blank
  click n70 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/StreamQueries.lean#L53" "Open target specification" _blank
  click n71 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/StreamQueries.lean#L62" "Open target specification" _blank
  click n72 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/StreamQueries.lean#L73" "Open target specification" _blank
  click n73 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/StreamQueries.lean#L81" "Open target specification" _blank
  click n74 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/StreamQueries.lean#L89" "Open target specification" _blank
  click n75 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/StreamQueries.lean#L100" "Open target specification" _blank
  click n76 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/StreamQueries.lean#L113" "Open target specification" _blank
  click n77 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/StreamQueries.lean#L124" "Open target specification" _blank
  click n78 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/StreamQueries.lean#L132" "Open target specification" _blank
  click n79 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/StreamQueries.lean#L145" "Open target specification" _blank
  click n80 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Streams.lean#L24" "Open target specification" _blank
  click n81 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Streams.lean#L51" "Open target specification" _blank
  click n82 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Streams.lean#L105" "Open target specification" _blank
  click n83 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Streams.lean#L109" "Open target specification" _blank
  click n84 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Streams.lean#L119" "Open target specification" _blank
  click n85 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Streams.lean#L137" "Open target specification" _blank
  click n86 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Streams.lean#L160" "Open target specification" _blank
  click n87 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Utilities.lean#L40" "Open target specification" _blank
  click n88 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Utilities.lean#L45" "Open target specification" _blank
  click n89 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Utilities.lean#L52" "Open target specification" _blank
  click n90 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Utilities.lean#L57" "Open target specification" _blank
  click n91 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Utilities.lean#L103" "Open target specification" _blank
  click n92 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Utilities.lean#L107" "Open target specification" _blank
  click n93 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Utilities.lean#L132" "Open target specification" _blank
  click n94 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Utilities.lean#L136" "Open target specification" _blank
  click n95 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Sequences.lean#L158" "Open target specification" _blank
  click n96 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Sequences.lean#L172" "Open target specification" _blank
  click n97 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Sequences.lean#L199" "Open target specification" _blank
  click n98 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Sequences.lean#L211" "Open target specification" _blank
  click n99 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Domains.lean#L24" "Open target specification" _blank
  click n100 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Domains.lean#L37" "Open target specification" _blank
  click n101 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Domains.lean#L53" "Open target specification" _blank
  click n102 href "https://github.com/cla7aye15I4nd/zlib-f/blob/211d239ee21162caefbf651aa597f0f595d1c374/ZlibF/Spec/Public/Domains.lean#L77" "Open target specification" _blank
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
| <a id="target-zlibf-spec-public-goal-compressbound"></a>[compressBound](../ZlibF/Spec/Public/Queries.lean#L35) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/utility.md#compressbound) | [ZlibF.Spec.Public.Proofs.compressBound](../ZlibF/Proof/public-compress-bound.lean#L49) |
| <a id="target-zlibf-spec-public-goal-compressbound-z"></a>[compressBound_z](../ZlibF/Spec/Public/Queries.lean#L40) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/utility.md#compressbound_z) | [ZlibF.Spec.Public.Proofs.compressBound_z](../ZlibF/Proof/public-compress-bound.lean#L46) |
| <a id="target-zlibf-spec-public-goal-zlibversion"></a>[zlibVersion](../ZlibF/Spec/Public/Queries.lean#L46) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/utility.md#zlibversion) | [ZlibF.Spec.Public.Proofs.zlibVersion](../ZlibF/Proof/public-zlib-version.lean#L8) |
| <a id="target-zlibf-spec-public-goal-zlibcompileflags"></a>[zlibCompileFlags](../ZlibF/Spec/Public/Queries.lean#L53) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/utility.md#zlibcompileflags) | [ZlibF.Spec.Public.Proofs.zlibCompileFlags](../ZlibF/Proof/public-zlib-compile-flags.lean#L6) |
| <a id="target-zlibf-spec-public-goal-zerror"></a>[zError](../ZlibF/Spec/Public/Queries.lean#L59) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/utility.md#zerror) | [ZlibF.Spec.Public.Proofs.zError](../ZlibF/Proof/public-zerror.lean#L37) |
| <a id="target-zlibf-spec-public-goal-get-crc-table"></a>[get_crc_table](../ZlibF/Spec/Public/Checksums.lean#L126) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/checksums.md#get_crc_table) | [ZlibF.Spec.Public.Proofs.get_crc_table](../ZlibF/Proof/public-get-crc-table.lean#L13) |

<a id="group-checksums"></a>

### Checksums

| Target statement | State | Contract | Proof evidence |
| --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-adler32"></a>[adler32](../ZlibF/Spec/Public/Checksums.lean#L66) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/checksums.md#adler32) | [ZlibF.Spec.Public.AdlerUpdateProof.adler_public](../ZlibF/Proof/public-adler-update.lean#L46) |
| <a id="target-zlibf-spec-public-goal-adler32-z"></a>[adler32_z](../ZlibF/Spec/Public/Checksums.lean#L61) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/checksums.md#adler32_z) | [ZlibF.Spec.Public.AdlerUpdateProof.adler_z_public](../ZlibF/Proof/public-adler-update.lean#L36) |
| <a id="target-zlibf-spec-public-goal-adler32-combine"></a>[adler32_combine](../ZlibF/Spec/Public/Checksums.lean#L86) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/checksums.md#adler32_combine) | [ZlibF.Spec.Public.AdlerCombineProof.combine_public](../ZlibF/Proof/public-adler-combine.lean#L118) |
| <a id="target-zlibf-spec-public-goal-adler32-combine64"></a>[adler32_combine64](../ZlibF/Spec/Public/Checksums.lean#L90) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/checksums.md#adler32_combine64) | [ZlibF.Spec.Public.AdlerCombineProof.combine64_public](../ZlibF/Proof/public-adler-combine.lean#L121) |
| <a id="target-zlibf-spec-public-goal-crc32"></a>[crc32](../ZlibF/Spec/Public/Checksums.lean#L117) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/checksums.md#crc32) | [ZlibF.Spec.Public.Proofs.crc32](../ZlibF/Proof/public-crc-updates.lean#L28) |
| <a id="target-zlibf-spec-public-goal-crc32-z"></a>[crc32_z](../ZlibF/Spec/Public/Checksums.lean#L109) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/checksums.md#crc32_z) | [ZlibF.Spec.Public.Proofs.crc32_z](../ZlibF/Proof/public-crc-updates.lean#L18) |
| <a id="target-zlibf-spec-public-goal-crc32-combine-gen"></a>[crc32_combine_gen](../ZlibF/Spec/Public/Checksums.lean#L140) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/checksums.md#crc32_combine_gen) | [ZlibF.Spec.Public.CrcCombineProof.gen](../ZlibF/Proof/public-crc-combine.lean#L76) |
| <a id="target-zlibf-spec-public-goal-crc32-combine-gen64"></a>[crc32_combine_gen64](../ZlibF/Spec/Public/Checksums.lean#L143) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/checksums.md#crc32_combine_gen64) | [ZlibF.Spec.Public.CrcCombineProof.gen64](../ZlibF/Proof/public-crc-combine.lean#L82) |
| <a id="target-zlibf-spec-public-goal-crc32-combine-op"></a>[crc32_combine_op](../ZlibF/Spec/Public/Checksums.lean#L150) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/checksums.md#crc32_combine_op) | [ZlibF.Spec.Public.CrcCombineProof.op](../ZlibF/Proof/public-crc-combine.lean#L88) |
| <a id="target-zlibf-spec-public-goal-crc32-combine"></a>[crc32_combine](../ZlibF/Spec/Public/Checksums.lean#L162) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/checksums.md#crc32_combine) | [ZlibF.Spec.Public.CrcCombineProof.combine](../ZlibF/Proof/public-crc-combine.lean#L94) |
| <a id="target-zlibf-spec-public-goal-crc32-combine64"></a>[crc32_combine64](../ZlibF/Spec/Public/Checksums.lean#L165) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/checksums.md#crc32_combine64) | [ZlibF.Spec.Public.CrcCombineProof.combine64](../ZlibF/Proof/public-crc-combine.lean#L100) |

<a id="group-inflate"></a>

### Inflate streams

| Target statement | State | Contract | Proof evidence |
| --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-inflatecopy"></a>[inflateCopy](../ZlibF/Spec/Public/Copy.lean#L27) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/inflate-stream.md#inflatecopy) | — |
| <a id="target-zlibf-spec-public-goal-inflateinit2"></a>[inflateInit2_](../ZlibF/Spec/Public/Initialisation.lean#L90) | [Blocked](./progress.md#status-blocked) | [Contract](../docs/api/inflate-stream.md#inflateinit2_) | [Blocker: Inflate initialization cleanup](./overview.md#inflate-initialization-cleanup) |
| <a id="target-zlibf-spec-public-goal-inflateinit"></a>[inflateInit_](../ZlibF/Spec/Public/Initialisation.lean#L95) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/inflate-stream.md#inflateinit_) | [ZlibF.Spec.Public.Proofs.InflateInit.init15_public](../ZlibF/Proof/public-inflate-init.lean#L83) |
| <a id="target-zlibf-spec-public-goal-inflateresetkeep"></a>[inflateResetKeep](../ZlibF/Spec/Public/Lifecycle.lean#L20) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/inflate-stream.md#inflateresetkeep) | [ZlibF.Spec.Public.InflateResetKeepProof.resetkeep_public](../ZlibF/Proof/public-inflate-reset-keep.lean#L8) |
| <a id="target-zlibf-spec-public-goal-inflatereset"></a>[inflateReset](../ZlibF/Spec/Public/Lifecycle.lean#L32) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/inflate-stream.md#inflatereset) | [ZlibF.Spec.Public.InflateResetProof.reset_public](../ZlibF/Proof/public-inflate-reset.lean#L16) |
| <a id="target-zlibf-spec-public-goal-inflatereset2"></a>[inflateReset2](../ZlibF/Spec/Public/Lifecycle.lean#L43) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/inflate-stream.md#inflatereset2) | [ZlibF.Spec.Public.InflateReset2Proof.reset2_public](../ZlibF/Proof/public-inflate-reset2.lean#L61) |
| <a id="target-zlibf-spec-public-goal-inflateend"></a>[inflateEnd](../ZlibF/Spec/Public/Lifecycle.lean#L60) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/inflate-stream.md#inflateend) | [ZlibF.Spec.Public.InflateEndProof.inflate_end_public](../ZlibF/Proof/public-inflate-end.lean#L55) |
| <a id="target-zlibf-spec-public-goal-inflategetdictionary"></a>[inflateGetDictionary](../ZlibF/Spec/Public/Lifecycle.lean#L77) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/inflate-stream.md#inflategetdictionary) | [ZlibF.Spec.Public.InflateDictionaryProof.inflate_getdict_public](../ZlibF/Proof/public-inflate-getdict.lean#L10) |
| <a id="target-zlibf-spec-public-goal-inflategetheader"></a>[inflateGetHeader](../ZlibF/Spec/Public/Lifecycle.lean#L87) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/inflate-stream.md#inflategetheader) | [ZlibF.Spec.Public.InflateHeaderProof.getheader_public](../ZlibF/Proof/public-inflate-header.lean#L34) |
| <a id="target-zlibf-spec-public-goal-inflatesetdictionary"></a>[inflateSetDictionary](../ZlibF/Spec/Public/Lifecycle.lean#L153) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/inflate-stream.md#inflatesetdictionary) | [ZlibF.Spec.Public.Proofs.inflateSetDictionary_public](../ZlibF/Proof/public-inflate-setdict.lean#L92) |
| <a id="target-zlibf-spec-public-goal-inflatesyncpoint"></a>[inflateSyncPoint](../ZlibF/Spec/Public/StreamQueries.lean#L53) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/inflate-stream.md#inflatesyncpoint) | [ZlibF.Spec.Public.InflateQueryProof.syncpoint_public](../ZlibF/Proof/public-inflate-small-queries.lean#L44) |
| <a id="target-zlibf-spec-public-goal-inflatemark"></a>[inflateMark](../ZlibF/Spec/Public/StreamQueries.lean#L62) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/inflate-stream.md#inflatemark) | [ZlibF.Spec.Public.InflateMarkProof.mark_public](../ZlibF/Proof/public-inflate-mark.lean#L71) |
| <a id="target-zlibf-spec-public-goal-inflatecodesused"></a>[inflateCodesUsed](../ZlibF/Spec/Public/StreamQueries.lean#L73) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/inflate-stream.md#inflatecodesused) | [ZlibF.Spec.Public.Proofs.inflate_codes_used](../ZlibF/Proof/Api/QueryLayout.lean#L71) |
| <a id="target-zlibf-spec-public-goal-inflateundermine"></a>[inflateUndermine](../ZlibF/Spec/Public/StreamQueries.lean#L81) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/inflate-stream.md#inflateundermine) | [ZlibF.Spec.Public.InflateQueryProof.undermine_public](../ZlibF/Proof/public-inflate-small-queries.lean#L60) |
| <a id="target-zlibf-spec-public-goal-inflatevalidate"></a>[inflateValidate](../ZlibF/Spec/Public/StreamQueries.lean#L89) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/inflate-stream.md#inflatevalidate) | [ZlibF.Spec.Public.InflateQueryProof.validate_public](../ZlibF/Proof/public-inflate-small-queries.lean#L75) |
| <a id="target-zlibf-spec-public-goal-inflateprime"></a>[inflatePrime](../ZlibF/Spec/Public/StreamQueries.lean#L100) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/inflate-stream.md#inflateprime) | [ZlibF.Spec.Public.InflatePrimeProof.prime_public](../ZlibF/Proof/public-inflate-prime.lean#L117) |
| <a id="target-zlibf-spec-public-goal-inflate"></a>[inflate](../ZlibF/Spec/Public/Streams.lean#L24) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/inflate-stream.md#inflate) | — |
| <a id="target-zlibf-spec-public-goal-inflatesync"></a>[inflateSync](../ZlibF/Spec/Public/Streams.lean#L160) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/inflate-stream.md#inflatesync) | — |

<a id="group-deflate"></a>

### Deflate streams

| Target statement | State | Contract | Proof evidence |
| --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-deflatecopy"></a>[deflateCopy](../ZlibF/Spec/Public/Copy.lean#L67) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/deflate-stream.md#deflatecopy) | — |
| <a id="target-zlibf-spec-public-goal-deflateinit2"></a>[deflateInit2_](../ZlibF/Spec/Public/Initialisation.lean#L138) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/deflate-stream.md#deflateinit2_) | — |
| <a id="target-zlibf-spec-public-goal-deflateinit"></a>[deflateInit_](../ZlibF/Spec/Public/Initialisation.lean#L145) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/deflate-stream.md#deflateinit_) | — |
| <a id="target-zlibf-spec-public-goal-deflategetdictionary"></a>[deflateGetDictionary](../ZlibF/Spec/Public/Lifecycle.lean#L105) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/deflate-stream.md#deflategetdictionary) | [ZlibF.Spec.Public.DeflateDictionaryProof.deflate_getdict_public](../ZlibF/Proof/public-deflate-getdict.lean#L10) |
| <a id="target-zlibf-spec-public-goal-deflateend"></a>[deflateEnd](../ZlibF/Spec/Public/Lifecycle.lean#L115) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/deflate-stream.md#deflateend) | [ZlibF.Spec.Public.DeflateEndProof.deflate_end_public](../ZlibF/Proof/public-deflate-end.lean#L10) |
| <a id="target-zlibf-spec-public-goal-deflateresetkeep"></a>[deflateResetKeep](../ZlibF/Spec/Public/Lifecycle.lean#L146) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/deflate-stream.md#deflateresetkeep) | [ZlibF.Spec.Public.DeflateResetKeepProof.deflate_resetkeep_public](../ZlibF/Proof/public-deflate-reset-keep.lean#L19) |
| <a id="target-zlibf-spec-public-goal-deflatereset"></a>[deflateReset](../ZlibF/Spec/Public/Lifecycle.lean#L149) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/deflate-stream.md#deflatereset) | [ZlibF.Spec.Public.DeflateResetProof.deflate_reset_public](../ZlibF/Proof/public-deflate-reset.lean#L52) |
| <a id="target-zlibf-spec-public-goal-deflatesetdictionary"></a>[deflateSetDictionary](../ZlibF/Spec/Public/Lifecycle.lean#L175) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/deflate-stream.md#deflatesetdictionary) | — |
| <a id="target-zlibf-spec-public-goal-deflatepending"></a>[deflatePending](../ZlibF/Spec/Public/StreamQueries.lean#L113) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/deflate-stream.md#deflatepending) | [ZlibF.Spec.Public.DeflateQueryProof.pending_public](../ZlibF/Proof/public-deflate-small-queries.lean#L145) |
| <a id="target-zlibf-spec-public-goal-deflateused"></a>[deflateUsed](../ZlibF/Spec/Public/StreamQueries.lean#L124) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/deflate-stream.md#deflateused) | [ZlibF.Spec.Public.DeflateQueryProof.used_public](../ZlibF/Proof/public-deflate-small-queries.lean#L48) |
| <a id="target-zlibf-spec-public-goal-deflatetune"></a>[deflateTune](../ZlibF/Spec/Public/StreamQueries.lean#L132) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/deflate-stream.md#deflatetune) | [ZlibF.Spec.Public.DeflateQueryProof.tune_public](../ZlibF/Proof/public-deflate-small-queries.lean#L61) |
| <a id="target-zlibf-spec-public-goal-deflatesetheader"></a>[deflateSetHeader](../ZlibF/Spec/Public/StreamQueries.lean#L145) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/deflate-stream.md#deflatesetheader) | [ZlibF.Spec.Public.DeflateQueryProof.header_public](../ZlibF/Proof/public-deflate-small-queries.lean#L74) |
| <a id="target-zlibf-spec-public-goal-deflate"></a>[deflate](../ZlibF/Spec/Public/Streams.lean#L51) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/deflate-stream.md#deflate) | — |
| <a id="target-zlibf-spec-public-goal-deflatebound-z"></a>[deflateBound_z](../ZlibF/Spec/Public/Streams.lean#L105) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/deflate-stream.md#deflatebound_z) | — |
| <a id="target-zlibf-spec-public-goal-deflatebound"></a>[deflateBound](../ZlibF/Spec/Public/Streams.lean#L109) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/deflate-stream.md#deflatebound) | — |
| <a id="target-zlibf-spec-public-goal-deflateprime"></a>[deflatePrime](../ZlibF/Spec/Public/Streams.lean#L119) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/deflate-stream.md#deflateprime) | — |
| <a id="target-zlibf-spec-public-goal-deflateparams"></a>[deflateParams](../ZlibF/Spec/Public/Streams.lean#L137) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/deflate-stream.md#deflateparams) | — |

<a id="group-back"></a>

### Callback decoding

| Target statement | State | Contract | Proof evidence |
| --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-inflatebackinit"></a>[inflateBackInit_](../ZlibF/Spec/Public/Back.lean#L22) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/inflate-back.md#inflatebackinit_) | [ZlibF.Spec.Public.InflateBackInitProof.back_init_public](../ZlibF/Proof/public-infback-init.lean#L135) |
| <a id="target-zlibf-spec-public-goal-inflateback"></a>[inflateBack](../ZlibF/Spec/Public/Back.lean#L115) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/inflate-back.md#inflateback) | — |
| <a id="target-zlibf-spec-public-goal-inflatebackend"></a>[inflateBackEnd](../ZlibF/Spec/Public/Back.lean#L142) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/inflate-back.md#inflatebackend) | [ZlibF.Spec.Public.InflateBackEndProof.back_end_public](../ZlibF/Proof/public-infback-end.lean#L20) |

<a id="group-gzip"></a>

### Gzip files

| Target statement | State | Contract | Proof evidence |
| --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-gzclose-r"></a>[gzclose_r](../ZlibF/Spec/Public/GzClose.lean#L35) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/gz-file.md#gzclose_r) | — |
| <a id="target-zlibf-spec-public-goal-gzclose-w"></a>[gzclose_w](../ZlibF/Spec/Public/GzClose.lean#L40) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/gz-file.md#gzclose_w) | — |
| <a id="target-zlibf-spec-public-goal-gzclose"></a>[gzclose](../ZlibF/Spec/Public/GzClose.lean#L44) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/gz-file.md#gzclose) | — |
| <a id="target-zlibf-spec-public-goal-gzbuffer"></a>[gzbuffer](../ZlibF/Spec/Public/GzControl.lean#L12) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/gz-file.md#gzbuffer) | [ZlibF.Spec.Public.Proofs.gzbuffer_public](../ZlibF/Proof/public-gzbuffer.lean#L49) |
| <a id="target-zlibf-spec-public-goal-gzeof"></a>[gzeof](../ZlibF/Spec/Public/GzControl.lean#L22) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/gz-file.md#gzeof) | [ZlibF.Spec.Public.Proofs.gzeof_public](../ZlibF/Proof/public-gzeof.lean#L18) |
| <a id="target-zlibf-spec-public-goal-gztell64"></a>[gztell64](../ZlibF/Spec/Public/GzControl.lean#L36) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/gz-file.md#gztell64) | — |
| <a id="target-zlibf-spec-public-goal-gztell"></a>[gztell](../ZlibF/Spec/Public/GzControl.lean#L39) | [Not proved](./progress.md#status-open) | [Contract](../docs/api/gz-file.md#gztell) | — |
| <a id="target-zlibf-spec-public-goal-gzoffset64"></a>[gzoffset64](../ZlibF/Spec/Public/GzControl.lean#L53) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/gz-file.md#gzoffset64) | [ZlibF.Spec.Public.OffsetProof.gzoffset64_public_goal](../ZlibF/Proof/public-gz-offset.lean#L199) |
| <a id="target-zlibf-spec-public-goal-gzoffset"></a>[gzoffset](../ZlibF/Spec/Public/GzControl.lean#L56) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/gz-file.md#gzoffset) | [ZlibF.Spec.Public.OffsetProof.gzoffset_public_goal](../ZlibF/Proof/public-gz-offset.lean#L211) |
| <a id="target-zlibf-spec-public-goal-gzerror"></a>[gzerror](../ZlibF/Spec/Public/GzControl.lean#L63) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/gz-file.md#gzerror) | [ZlibF.Spec.Public.GzErrorProof.gzerror](../ZlibF/Proof/public-gz-error.lean#L197) |
| <a id="target-zlibf-spec-public-goal-gzclearerr"></a>[gzclearerr](../ZlibF/Spec/Public/GzControl.lean#L74) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/gz-file.md#gzclearerr) | [ZlibF.Spec.Public.Proofs.gzclearerr](../ZlibF/Proof/gzlib.c.public-clearerr.lean#L28) |
| <a id="target-zlibf-spec-public-goal-gzrewind"></a>[gzrewind](../ZlibF/Spec/Public/GzControl.lean#L91) | [Registered proof](./progress.md#status-registered) | [Contract](../docs/api/gz-file.md#gzrewind) | [ZlibF.Spec.Public.GzRewindProof.rewind_public](../ZlibF/Proof/public-gz-rewind.lean#L67) |
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

<a id="group-lifecycle"></a>

### Lifecycles and call sequences

| Target statement | State | Contract | Proof evidence |
| --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-inflate-sequence"></a>[inflate_sequence](../ZlibF/Spec/Public/Sequences.lean#L158) | [Not proved](./progress.md#status-open) | See target statement | — |
| <a id="target-zlibf-spec-public-goal-deflate-sequence"></a>[deflate_sequence](../ZlibF/Spec/Public/Sequences.lean#L172) | [Not proved](./progress.md#status-open) | See target statement | — |
| <a id="target-zlibf-spec-public-goal-inflate-back-sequence"></a>[inflate_back_sequence](../ZlibF/Spec/Public/Sequences.lean#L199) | [Not proved](./progress.md#status-open) | See target statement | — |
| <a id="target-zlibf-spec-public-goal-gz-sequence"></a>[gz_sequence](../ZlibF/Spec/Public/Sequences.lean#L211) | [Not proved](./progress.md#status-open) | See target statement | — |
| <a id="target-zlibf-spec-public-goal-inflate-initialisation-domain"></a>[inflate_initialisation_domain](../ZlibF/Spec/Public/Domains.lean#L24) | [Registered proof](./progress.md#status-registered) | See target statement | [ZlibF.Spec.Public.Proofs.InflateInit.inflate_initialisation_domain_public](../ZlibF/Proof/public-inflate-init.lean#L263) |
| <a id="target-zlibf-spec-public-goal-deflate-initialisation-domain"></a>[deflate_initialisation_domain](../ZlibF/Spec/Public/Domains.lean#L37) | [Not proved](./progress.md#status-open) | See target statement | — |
| <a id="target-zlibf-spec-public-goal-inflate-back-initialisation-domain"></a>[inflate_back_initialisation_domain](../ZlibF/Spec/Public/Domains.lean#L53) | [Registered proof](./progress.md#status-registered) | See target statement | [ZlibF.Spec.Public.InflateBackInitProof.back_init_domain_public](../ZlibF/Proof/public-infback-init.lean#L230) |
| <a id="target-zlibf-spec-public-goal-gz-initialisation-domain"></a>[gz_initialisation_domain](../ZlibF/Spec/Public/Domains.lean#L77) | [Not proved](./progress.md#status-open) | See target statement | — |

## Refresh

Run `python3 scripts/proof-progress.py` from the repository root after proof or registry
updates. It rechecks source hashes, builds the root without downloading cached artifacts,
and inspects exact compiled theorem types. It updates both target pages and only the
marked graph section at the top of overview. `--check` detects stale views.
It never changes a registry, target, proof, lock or verification gate.
Use the [acceptance checks](checking/README.md) for acceptance evidence.
Current work and remaining tasks are maintained only in [overview](overview.md).

Input fingerprint: `a0029a79e786ba18dc9ddc5cb45254a4bb78f30c8b46387dd70cc846e6a721a6`.
