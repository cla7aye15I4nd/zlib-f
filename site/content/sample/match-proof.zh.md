前两篇已经沿字节走过[补充输入和窗口滑动](/sample/window.html)，再走过[候选搜索与延迟决策](/sample/match-search.html)。可观察的承诺很直接：策略用一个匹配替换输入时，这个匹配展开后必须恢复被替换的字节。更快的排除方式、更小的搜索预算可以改变选中的表示，但不能破坏这条承诺。

证明沿实现中的同一组交接展开：先保留正确的字节与位置，再说明被追踪的链有什么含义，随后建立搜索返回值的保证，最后把策略提交的符号连接到输入前缀。这些义务互相联系；其中一个交接的定理，不会自动提供其余部分。

## 移动表示中的字节 {#representation}

窗口形状关系是 `strstart + lookahead ≤ 2W`。它能解释补充输入为什么放得下，却没有说明复制了什么内容。功能关系还必须把每个保留窗口位置连接到逻辑流位置。如果窗口所代表的输入流基准为 L，那么保留数组位置 i 的字节，就应等于逻辑输入中 L+i 的字节。

滑动 W 之后，新基准是 L+W，新数组位置 i 保存旧位置 i+W 的字节。两个表达式指向同一个逻辑位置：

```text
(L + W) + i = L + (i + W)
```

窗口例子把它具体化了：滑动 512 后，当前位置 800 和候选 700 分别变成 288 和 188，字节身份与距离 100 一起保持。如果只证明计数器都减去 512，就会遗漏必需的内容相等关系。

分配区间论证是另一件事。滑动把 `[W, strstart+lookahead)` 复制到起点，目标长度为 `strstart+lookahead-W`。在把源码无符号减法解释成数学减法之前，必须先建立边界；`memcpy` 的源、目标也必须有效且不重叠。自然数定理 [slide_copy](/reference/source/ZlibF/Proof/deflate.c.engine.window.html#L52)在 `W ≥ 512`、窗口形状界与滑动条件下建立相应区间算术。它是数值引理，单独并不执行整个 `fill_window`。

读取操作随后要把调用者字节连接到实际窗口数组，并更新输入游标。[read_buf_ok](/reference/source/ZlibF/Proof/deflate.c.engine.readbuf.html#L99)描述有明确范围的翻译后复制及其记账；其中的缓冲区与流前提需要由调用点建立。保护尾部的初始化写入必须留在分配内，同时不扩大逻辑输入。滑动后有符号的 `block_start` 也必须允许为负；要求它处处非负，会悄悄删掉真实执行路径。

## 有意义的链接与槽位复用 {#hash}

源码分配后并不初始化每一个 `prev` 槽位，而是清空头表，再随着位置插入写入前驱槽位。若要求所有槽位都保存合法链接，描述的就是另一套初始化策略。真正有用的命题，应当针对搜索实际可达的槽位。

[HashChains](/reference/source/ZlibF/Proof/deflate.c.engine.chains.html#L29)记录了这个想法：一个非零可达位置 p，在其槽位仍然属于它时，必须是有意义的已插入位置。对应三字节串的哈希等于选定桶号，`p & (W-1)` 中记录的前驱严格小于 p。参数 `top` 限制正在描述的插入代际；条件 `top ≤ p+W` 识别尚未被一个窗口之后的位置复用的链接槽位。

插入改变两个单元：前驱槽位接收旧桶头，桶头接收新位置。证明把新可达结点分成新位置本身和旧链已经可达的结点，还要说明新槽位写入不会破坏一个仍在保留范围内的前驱。[chains_insert](/reference/source/ZlibF/Proof/deflate.c.engine.chains.html#L76)为数学表函数证明结构保持；[INSERT_STRING_ok](/reference/source/ZlibF/Proof/deflate.c.engine.macros.html#L177)则在堆、参数和区间前提下给出实际翻译后的读取与存储。连接这两部分，结构命题才能进入程序证明。

滑动是另一次表示变换：每个保留位置减去 W，而减去 W 不改变它对 W 取模的槽位；窗口内容同时移动相同偏移。[chains_slide](/reference/source/ZlibF/Proof/deflate.c.engine.chains.html#L138)把链关系传递到这些变换之后，[slide_hash_ok](/reference/source/ZlibF/Proof/deflate.c.engine.slide.html#L166)描述表更新的实际执行。未使用的垃圾槽位也可能被变换；它们之所以无害，是因为论证从未把它们当作有意义的链链接。

跳过第三个字节的比较，也需要内容事实，不能只凭对冲突的直觉。[hkey_third](/reference/source/ZlibF/Proof/deflate.c.engine.hash.html#L139)从键相等、前两个字节相等以及明示的哈希参数，推出第三个字节相等。这正是便宜探测通过后所需要的事实。

## 搜索含义与终止 {#search}

搜索不变量让当前候选始终位于已经说明的链上，让缓存的末端字节等于它们代表的窗口字节，并把最佳长度限制在允许范围内。循环体可以排除候选而不改变最佳结果；一旦改进结果，不变量就要增加一个见证：更早的位置、允许的距离，以及被声明区间内每个字节的相等关系。

展开后的比较会连接到一个更简单的数学扫描。[firstMis_spec](/reference/source/ZlibF/Proof/deflate.c.engine.match.html#L50)刻画第一个不相等位置，或最大边界 258。[内层循环结果](/reference/source/ZlibF/Proof/deflate.c.engine.lminner.html#L36)再把八次短路比较组成的条件连接到这次扫描。内存余量说明所有实际到达的读取都位于数组内；字节相等关系说明返回值确实是匹配。它们各自支撑不同的结论。

有明确范围的 [longest_match_ok](/reference/source/ZlibF/Proof/deflate.c.engine.lmmain.html#L212)在 `LMEnv` 下给出执行结果。这个环境提供实际窗口和前驱数组、512 到 32768 之间的二次幂 W、掩码、覆盖比较范围的空间、合法的较早初始候选，以及链的语义事实。定理返回 `min(best, lookahead)`，只改变 `match_start`，并区分两种情况：

- 没有超过 `prev_length`：保留旧 `match_start`。
- 得到改进：`match_start` 见证字节相等、位置在前、距离合法且长度至多 258。

第一种情况并不是针对当前位置的新匹配见证。策略决定保留前一个匹配时，必须使用上一状态的对应关系。这个定理也不承诺在所有窗口位置中达到最大长度；搜索预算与 nice 阈值正是为了免除这种要求。

终止可以使用当前链结点的位置：每个继续访问的前驱都严格更小，而表示中的位置能够放进运行时循环预算。[lm_loop_ok](/reference/source/ZlibF/Proof/deflate.c.engine.lmmain.html#L77)把 `cur_match.toNat` 用作递减度量，并不依赖“无符号链计数器绝不会从零回绕”这一假设。这对从配置默认值扩展到更宽的 [deflateTune 契约](/reference/functions/deflateTune.html)尤其重要。每条允许调参及调用历史究竟怎样建立所需链关系，仍然属于调用者组合义务。

## 从决策到符号序列 {#symbols}

最后一步重新把搜索接回数据流。在普通策略边界，需要区分已经提交的逻辑前缀、可能暂缓的字节，以及尚未处理的输入。延迟匹配可以推进 `strstart`，同时把一个字节留作延期工作；它并没有因此把这个字节发射出去。若只把 `strstart` 当作已提交输出字节个数，关系就会写错。

对 `XABCDEFGQ`，发射字面量 X，让已提交展开增加一个字节；接受保存的七字节匹配，再让它增加 `ABCDEFG`。匹配长度可以大于距离：独立展开语义逐字节从不断增长的逻辑历史读取。相应窗口字节相等时，对复制长度作归纳，就能说明每个新字节都是所需的下一个输入字节。距离为 d 时，第 j 步读取的逻辑源位置为 `S+j-d`。若 `j < d`，来源属于较早历史；否则，它就是第 `j-d` 步产生的字节，其含义已由归纳得到。这也覆盖读到本次匹配刚生成内容的情况。

策略在 tally 之前还必须建立精确的长度和距离界。字面量是一个字节；匹配长度为 3 到 258，所以保存的长度偏移为 0 到 255。其正距离不超过格式界 32768；选定搜索路径建立的是更强的实现界 `W-262`。tally 增加一条三字节记录，并更新对应频率。[tallyCalls_preserves](/reference/source/ZlibF/Proof/trees.c.tally-support.html#L46)在足够符号空间下，给出实际合法 tally 调用的有范围组合。它自己的命题明确没有建立翻译后策略的输入历史，也没有建立发射块的含义。

这里就是接往[Huffman 构造](/sample/huffman-tree.html)、[块选择](/sample/blocks.html)和[输出保持](/sample/proof.html)的边界。完整论证必须让**同一组**选定符号穿过记录、树构造和发射，并保持其含义及未读存储。分别对互不相关的符号列表证明性质，再把它们当作压缩器的真实决策，是无法完成这个连接的。

引用结果未覆盖的初始化、策略循环、补充输入、刷新与公开历史连接，仍需证明确认（**to confirm**）。[实现论证](/reference/docs/proof/deflate.html)解释它们怎样组合，[当前进度](/reference/docs/progress.html)记录接受范围与剩余工作；公开 [deflate 目标](/reference/functions/deflate.html#formal-target)则保留自己的明示定义域。
