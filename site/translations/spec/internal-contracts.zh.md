<!-- source-sha256: 38ef25fff47809857f8a227bddefaeffdec8e1fcfc970dc43d6f2c9dd977e63a -->

# 内部调用处的证明义务

这些是默认构建辅助函数的文档契约。它们解释调用者必须建立什么，以及辅助函数执行证明必须给出什么。
各条目列出实际调用点需要建立的事实。辅助函数的执行定理必须逐项证明这些事实；调用者只能使用这样的定理，不能把表格中的结论当作假设。
执行证明见[证明指南](../proof/README.md)，状态见[进度](../progress.md)。

内部前置条件可以强于公开入口的前置条件。实际调用者必须从初始化建立的不变量和当前执行状态推导它，
不能将其变成公开调用的隐藏限制。尤其是，较小内存级别、任意新分配整数内容和文档错误情况，
仍然是对应公开调用者的证明义务。

## 条目结构与共同要求

每个稳定的 `I-*` 标识符命名一项义务。“前置条件”描述辅助函数定义域，“后置条件”描述结果，“允许的影响”限定读写范围。中间事实必须在所命名的阶段成立，早于 C 将相同字段复用于其他用途。

每个条目也要求共同的内存事实：被引用存储存活、表示正确且访问有界；
写入目标可写；`memcpy` 范围互不重叠；指针字段使用前已被写入。
每个辅助函数证明都必须建立终止性、无故障，以及其作用之外存储的帧性质。
这些义务针对其翻译后函数体，包括调用更底层、已有证明的辅助函数。

```mermaid
flowchart TD
    IT["inflate_table：构造有界表"] --> IF["inflate_fast：使用表和历史"]
    UW["updatewindow：维护历史环"] --> IF
    HC["哈希更新：维护可达链"] --> LM["longest_match：有界搜索"]
    HC --> FW["fill_window：滑动与补充"]
    FW --> LM
    BT["build_tree → gen_bitlen → gen_codes"] --> CB["compress_block：发出符号"]
    CB --> PB["待输出字节与缓冲位"]
    PB --> FP["flush_pending：复制到调用者"]
```

箭头表示证明依赖和所维护数据，不是穷尽的 C 调用图。

## 构造解码表：`inflate_table`

用途：把每个符号的编码长度变成可直接查找符号的解码表。`type` 选择码长、字面量／长度或距离这三种字母表；`codes` 是符号个数，`lens` 保存各符号的码长，单位为比特。`bits` 记录一次根表查询查看多少位；`table` 是写入表项的位置，`work` 是排序时使用的临时数组。这里数组容量按表项数计，不按字节数计。
`inflate_table(type, lens, codes, &table, &bits, work)`；`base` 是入口时的 `*table`。

| 类别／ID | 契约 |
| --- | --- |
| 前置条件 `I-it-pre-lens` | `lens[0..codes)` 可读，长度处于 `0..15`。对于 `CODES`，长度至多为 7，请求的 `*bits` 至少为 7。 |
| 前置条件 `I-it-pre-codes` | `type` 是 `CODES`、`LENS` 或 `DISTS`；`codes` 分别至多为 19、288 或 32。 |
| 前置条件 `I-it-pre-work` | `work[0..codes)` 是可写临时区，与其他参数互不重叠。 |
| 前置条件 `I-it-pre-table` | `table`／`bits` 是可写单元；对于 `CODES`／`LENS`／`DISTS`，`base` 分别容纳 128／852／592 项，并与其他参数互不重叠。 |
| 后置条件 `I-it-ret` | 成功返回 0，无效长度返回 -1，`LENS`／`DISTS` 容量不足拒绝返回 1。空码集合以无效表项成功构造。 |
| 允许的影响 `I-it-writes` | 只修改临时区、指针／位宽单元及容量内表项。成功构造 `[base, base + used)`；错误可能留下部分写入。 |
| 后置条件 `I-it-advance` | 成功时，`*table = base + used`，`*bits` 是实际根表位宽。 |
| 后置条件 `I-it-complete` | 成功时写入全部已构造项，包括允许的单符号码对应的一个无效项，或空码集合对应的两个无效项。 |
| 后置条件 `I-it-links` | 每个成功构造的根表链接及其完整子表都位于 `[base, base + used)`。 |
| 后置条件 `I-it-canonical` | 成功时按照[规范赋码](format/README.md)解码，并为保留符号设置无效标记。 |
| 后置条件 `I-it-term` | 调用在所述定义域内结束。 |

## 留足余量进行解码：`inflate_fast`

用途：在调用者已留足输入／输出余量时批量解码，直到空间不足、块结束或数据无效。`avail_in`、`avail_out` 分别计剩余输入和输出字节；`start` 是外层调用最初的输出容量。`hold` 保存已读入、尚未消费的比特，`bits` 计这些比特的数量。保存历史的窗口容量为 `wsize` 字节，其中 `whave` 字节有效，`wnext` 是下一处写入下标。

| 类别／ID | 契约 |
| --- | --- |
| 前置条件 `I-if-pre-room` | 模式为 `LEN`；`avail_in ≥ 6`、`avail_out ≥ 258`、`start ≥ avail_out`。`next_out - (start - avail_out)` 是外层 `inflate` 调用此前输出的起点，位于同一对象且可读。输入／输出互不重叠。 |
| 前置条件 `I-if-pre-bits` | `bits < 8`；`hold` 恰好包含这些缓冲的低位，其他位均未置位。 |
| 前置条件 `I-if-pre-tables` | `lencode`／`distcode` 及根表位宽满足成功建表的表项／链接规则，包括固定表。 |
| 前置条件 `I-if-pre-window` | `whave ≤ wsize`；`wsize = 0` 蕴含 `whave = wnext = 0`；否则 `wnext < wsize`，且 `window` 容纳 `wsize` 字节。有效历史有 `whave` 字节；`sane` 已设置。 |
| 允许的影响 `I-if-reads` | 字节读取使用入口输入、外层调用此前输出或有效窗口历史；表读取保持在解码表内。 |
| 允许的影响 `I-if-writes` | 只写入入口输出、流的游标／计数／`msg`，以及状态的 `hold`／`bits`／`mode`；不分配内存。 |
| 后置条件 `I-if-post` | 游标／计数记录已消费输入与输出。未使用的完整输入字节被退回；`bits < 8`。模式为 `LEN`、`TYPE` 或 `BAD`；`BAD` 可能已消费无效符号的一部分。 |
| 后置条件 `I-if-dist` | 若距离超过外层 `inflate` 调用已产生字节数加 `whave`，则在复制该匹配前设置 `BAD`。 |

## 保持解码器历史：`updatewindow`

用途：将新产生的输出或字典字节追加到历史，以便之后执行向后引用。`end` 指向这一段的末尾，`copy` 是其字节数，所以段的范围是 `[end - copy, end)`，不包含 `end`。配置指数 `wbits` 对应 `2^wbits` 字节窗口；`whave` 记录有效历史长度，`wnext` 标记环形写入结束处。

| 类别／ID | 契约 |
| --- | --- |
| 前置条件 `I-uw-pre` | `[end - copy, end)` 可读且与目标窗口互不重叠。`wbits` 位于配置允许的 inflate 范围。已有窗口具有 `2^wbits` 个可写字节。环尚未使用（`wsize = 0`），或满足 `wsize = 2^wbits`、`whave ≤ wsize`、`wnext < wsize` 和 `whave < wsize → wnext = whave`。 |
| 允许的影响 `I-uw-alloc` | 仅在窗口不存在时分配。分配失败返回 1，否则返回 0。只写窗口存储／字段和分配器状态；失败保持已有历史。 |
| 后置条件 `I-uw-inv` | 返回 0 时，`wsize = 2^wbits`、`whave ≤ wsize`、`wnext < wsize` 且 `whave < wsize → wnext = whave`。 |
| 后置条件 `I-uw-content` | 成功时保留旧历史与输入拼接后的后缀，至多 `wsize` 字节；`whave` 记录其长度，环形顺序在 `wnext` 处结束。 |

## 补充与滑动：`fill_window`、`slide_hash`、`read_buf`

用途：补充尚未处理的输入，并维护它与已处理历史的位置关系。`w_size` 是配置的窗口尺度，连续字节数组的容量 `window_size` 通常为其两倍。`strstart` 是下一个处理字节的数组下标，`lookahead` 是从这里起已读入、尚未处理的字节数；`MIN_LOOKAHEAD` 是通常希望备好的 262 字节。`insert` 记录仍待建立哈希索引的位置数量。滑动时这些数组下标改变，但所指的输入字节不变。

| 类别／ID | 契约 |
| --- | --- |
| 前置条件 `I-fw-pre` | `fill_window` 满足 `lookahead < MIN_LOOKAHEAD`、`window_size = 2*w_size`、`strstart + lookahead ≤ window_size` 及 `insert ≤ strstart`。窗口、哈希大小／掩码、高水位、搜索设置和位置范围满足配置的 deflate 状态，包括 `I-hc-inv`。输入具有可读的 `avail_in` 视图。 |
| 后置条件 `I-fw-post-room` | `fill_window` 返回后满足 `strstart ≤ window_size - MIN_LOOKAHEAD`。 |
| 后置条件 `I-fw-post-lookahead` | 返回后满足 `lookahead ≥ MIN_LOOKAHEAD` 或 `avail_in = 0`。新读入字节按顺序扩展当前前瞻输入。 |
| 允许的影响 `I-fw-slide` | 滑动将上半窗口的存活字节下移 `w_size`，用 C 算术调整位置／`insert`，并调用 `slide_hash`。其他写入包括输入／校验和核算、哈希及高水位填充。 |
| 前置／后置条件 `I-sh-total` | `slide_hash` 要求正的 `hash_size` 和 `w_size`，以及可写的 `head[0..hash_size)`／`prev[0..w_size)`。每项在 `m ≥ w_size` 时变为 `m - w_size`，否则变为 `NIL`；并设置 `slid = 1`。不可达的 `prev` 值不必初始化。 |
| 前置／后置条件 `I-rb-copy` | `read_buf` 要求可写入 `n = min(avail_in, size)` 字节的目标，并与输入互不重叠。它返回 `n`、复制该前缀、推进 `next_in`、减少 `avail_in`、增加 `total_in`，并为当前包装更新 Adler-32／CRC-32。`n = 0` 时不改变任何内容。 |

## 搜索有效哈希链：`longest_match`

用途：沿同一三字节哈希桶的候选链寻找重复，并限制比较工作量。`cur_match` 是当前候选的数组下标；`strstart` 是当前输入位置，两者之差是回退距离。`MAX_DIST = w_size - 262` 是本实现允许搜索的最远距离，`MAX_MATCH = 258` 是一个匹配最多复制的字节数；`prev_length` 是候选必须改进的已有长度。`head` 保存桶头，`prev` 把候选链接到更早位置，`NIL` 表示链结束。

| 类别／ID | 契约 |
| --- | --- |
| 前置／后置条件 `I-hc-inv` | `INSERT_STRING`、`slide_hash`、`CLEAR_HASH`、`fill_window` 和 `deflateSetDictionary` 保持：链头指向已插入位置，可达 `prev[p mod w_size]` 槽已写入 `NIL` 或更小的同哈希位置。位置与当前窗口／前瞻输入一致。 |
| 前置条件 `I-lm-pre` | `cur_match` 是当前字符串哈希的非零链头，`cur_match < strstart`，且距离至多为 `MAX_DIST`。`I-hc-inv` 成立；`strstart ≤ window_size - MIN_LOOKAHEAD`、`1 ≤ prev_length ≤ MAX_MATCH`，配置的搜索设置在可能的缩减后仍给出正链预算。 |
| 允许的影响 `I-lm-reads` | 读取窗口直到且包括 `strstart + MAX_MATCH`，可能越过前瞻输入，并读取已写入的可达 `prev` 槽。只修改 `match_start`；填充字节不能用来论证无效匹配。 |
| 后置条件 `I-lm-ret` | 返回至多 `min(MAX_MATCH, lookahead)`。找到更优结果时设置有效的 `match_start`；否则可以保留 `prev_length`，再以 lookahead 为上限，但不提供新的 `match_start` 保证。 |
| 后置条件 `I-lm-term` | 在链预算内结束；遍历的非零位置严格递减。不保证全局最优匹配。 |

## 构造并发出 Huffman 树：`trees.c`

用途：根据符号出现频次构造满足长度限制的 Huffman 码，再把符号写成压缩块。描述符选择字面量／长度树、距离树或码长树。`bl_count[l]` 记录码长为 l 比特的符号个数，`max_length` 是该类树允许的最大码长。输出阶段的 `sym_next` 以字节计，符号记录每个占三字节；`pending` 以已产生、尚未交付的压缩字节计。

| 类别／ID | 契约 |
| --- | --- |
| 前置条件 `I-bt-pre` | `build_tree` 接收对应 286／30／19 个字面量-长度／距离／位长度叶子的描述符、已设置的频次，以及容纳内部节点／堆／深度的空间。补足叶子后的频次总和适合对应字段。 |
| 允许的影响 `I-bt-heap` | 堆索引小于 573；节点保持在各自树内。写入描述符最大值、节点、堆／深度、位数统计和成本。 |
| 中间事实 `I-bt-forest` | 在长度／编码覆盖父节点／频次字段前，节点在正频次符号上形成满二叉树，并通过强制叶子补足两个。父节点频次等于子节点频次之和。 |
| 前置／后置条件 `I-gb-len` | 给定该树、有序堆和描述符，`gen_bitlen` 写入活跃叶子长度，位于 `1..max_length`（15 或 7），并满足 Kraft 和为 1，同时写入计数和成本。 |
| 后置条件 `I-gb-count` | `bl_count[l]` 统计长度为 `l` 的活跃叶子；`bl_count[0] = 0`。 |
| 前置／后置条件 `I-gc-code` | `gen_codes` 要求直到 `max_code` 的长度处于 `0..15`，且完整码计数匹配。它只写正长度的编码字段：按符号顺序排列的位反转规范码字。 |
| 前置条件／允许的影响 `I-cb-reads` | `compress_block` 要求 `sym_buf[0..sym_next)` 中有完整三字节符号、有效的字面量／匹配范围、具有可用编码的匹配树，以及待输出／位缓冲空间。它按顺序读取符号，发出对应编码／额外位，最后发出 `END_BLOCK`。 |
| 后置条件 `I-cb-pending` | 在符号 `k`（从 0 开始）之后，`pending < lit_bufsize + 3*(k+1)`。发出过程也必须始终保持未读符号。该上界必须证明，不能从调用者处假设。 |
| 前置／后置条件 `I-tf-choice` | `_tr_flush_block` 要求有效块符号／频次、处于 `0..1` 的 `last`、待输出容量；若选择直接存储块，还要求 `stored_len ≤ 65535` 和可读的 `buf[0..stored_len)`。若 `buf != NULL` 且 `stored_len + 4 ≤ opt_lenb` 则选择直接存储块；否则在 `static_lenb = opt_lenb` 时选择固定编码块，其余选择动态编码块。`opt_lenb` 是取整后的两种压缩大小中的较小者，但 `Z_FIXED` 会优先选择固定编码块。它重置块核算，若 `last` 成立则对齐位。 |

默认[重叠存储上界](../proof/trees.md)必须覆盖每个公开内存级别，不能成为隐藏的调用者限制。

## 排出待输出内容：`flush_pending` 与位写入函数

用途：先把已经凑齐的缓冲位转成字节，再把待输出字节交给调用者。`bi_buf` 是暂存码字的位寄存器，`bi_valid` 是其中有效位数；`pending_buf` 是内部字节数组，`pending_out` 指向下一段待交付字节，`pending` 是其字节数。`avail_out` 则是调用者本轮仍提供的可写字节数，两者不能混同。

| 类别／ID | 契约 |
| --- | --- |
| 前置／后置条件 `I-fp-inv` | `pending_out` 位于待输出分配内，且 `pending_out + pending ≤ pending_buf + pending_buf_size`。写入函数还要求实际写入偏移处有空间；仅有该区间条件并不足够。 |
| 前置／后置条件 `I-fp-copy` | `flush_pending` 要求可写的 `avail_out` 输出，与待输出存储互不重叠，并要求有效位缓冲状态为 `_tr_flush_bits` 留出空间。它先排出完整的缓冲字节，再复制 `n = min(pending, avail_out)`，推进两个游标、增加 `total_out`，并从两个计数中减去 `n`。非零复制清空待输出内容后，`pending_out = pending_buf`。只修改待输出／位字段、流的输出字段和已复制输出字节。 |
| 前置／后置条件 `I-pb-room` | `put_byte` 和 `put_short` 要求各自待输出偏移处有一／两个可写字节。`send_bits` 要求 `1 ≤ length ≤ 16`、数值适合该长度、有效的 `bi_valid`／`bi_buf`，并为可能的双字节写入留出空间。它们追加字节／位而不检查容量。调用者必须建立空间条件；`I-cb-pending` 必须保护重叠区内的未读符号。 |

[翻译规则](../design/translation.md)解释这些义务引用的操作。
[API 模型](../design/api-model.md)解释字节历史与具体堆效果的区别。

[设计指南](../design/README.md) · [文档首页](../README.md)
