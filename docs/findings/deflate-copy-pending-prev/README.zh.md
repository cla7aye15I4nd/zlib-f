<!-- source-sha256: f3e94c5dd92ee199f4dab2811e33bbc2d1cc32f5e2790e8c5bdc8ffe8c17417c -->
# deflateResetKeep 之后的 deflateCopy：longest_match 沿一个未初始化的 prev 槽前进

状态：已在固定的、未修改的 C 上于 x86_64 Linux 确认：AddressSanitizer 报告窗口之外的读取，使用默认分配器时 valgrind 报告使用了未初始化的 `prev` 槽（[报告](../../../tests/regression/deflate-copy-pending-prev/report.txt)）；在 arm64 macOS 上得到相同的 AddressSanitizer 报告。这是内存错误：`longest_match` 读到窗口之外。它需要直接调用 `deflateResetKeep`，而 `zlib.h` 把该函数声明在 `/* undocumented functions (not part of the zlib API) */` 之下：这不是已文档化 API 的缺陷，而是一个导出但未文档化的函数使之可达的内存错误。未向上游报告。

一份面向维护者的报告草稿见 [deflate-copy-pending-prev-report.md](../deflate-copy-pending-prev-report.md)（写给项目所有者的草稿；没有向上游发送任何内容）。

机制，按固定版本的源码：

1. `deflateResetKeep` 保留窗口和散列，丢弃前瞻。位置 `strstart - 2` 和 `strstart - 1` 仍是链头（见 [deflate-resetkeep-stale-hash](../deflate-resetkeep-stale-hash/README.md)）。
2. 随后的 `deflate(Z_BLOCK)` 设置 `insert = 2`：这两个位置此时等待插入。
3. `deflateCopy` 只复制 `strstart - insert` 以下的 `prev`（`deflate.c:1383`）。副本中这两个链头的 `prev` 槽是新分配的、未初始化的内存。
4. 在副本上，`deflateParams(Z_RLE)` 和一次无输入的 `deflate(Z_SYNC_FLUSH)` 以 `deflate_rle` 结束，它设置 `insert = 0`（`deflate.c:2177`）。`fill_window` 只在 `insert` 非零时重新插入等待的位置，所以这两个槽保持未初始化。
5. 在 `deflateParams(Z_DEFAULT_STRATEGY)` 之后，以 `strstart - 2` 处三个字节开头的输入使 `deflate_slow` 以相同的键插入 `strstart`，并对旧链头调用 `longest_match`。循环把未初始化的 `prev` 槽读作下一个候选，并比较该位置的窗口字节。

`repro.c`（与 [tests/regression/deflate-copy-pending-prev](../../../tests/regression/deflate-copy-pending-prev/README.md) 中的驱动程序相同）用 16 位值 1030 填充新内存，因此候选恰好落在 1024 字节窗口（`windowBits` 9）之后，AddressSanitizer 报告这次读取（`deflate.c:1511`）。内存内容不同时，候选就是该槽中的任意值：最大 65535，远在小窗口之外。使用默认分配器（`repro plain`）时，valgrind 报告 `longest_match` 循环判断中的未初始化值（`deflate.c:1555`）。

没有第 1 步时，没有链头等待插入：这是 deflate 不变式 `DInv` 的定理（`DInv.heads_inserted`，以及在 level 0 有一次待处理滑动时的 `DInv.slid_heads_inserted`，`ZlibF/Proof/deflate.c.universal-heads.lean`）：每个非零的 `head` 项都小于 `strstart - insert`。`DInv` 在 deflate 流定义域的每个历史之后都成立，而该定义域中没有直接调用 `deflateResetKeep`（`reachable_inv`，在 `Goal.deflate_sequence_safety` 的假设下）。有两次或更多待处理滑动时（level 0），不变式对散列表不作任何断言，`deflateParams` 在非零 level 运行之前清空它们。Inflate 批次 1 的真实 C 检查器在 460 万个状态上与之一致（这是证据，不是证明）。

没有第 3 步时，这些槽保存着插入这些位置时写入的值。没有第 4 步时，`fill_window` 会在任何 `longest_match` 之前插入这两个位置，从而重写它们的槽。

版本。两个成因都是上游的近期修改。自提交 8404590（"Copy only the initialized deflate state in deflateCopy"，2026-01-10）起，`deflateCopy` 只复制前沿以下的 `prev`，首次发布于 1.3.2；1.3.1 复制全部 `w_size` 项。自提交 1e4178b（"Fix deflateResetKeep() when used in the middle of a stream"，2026-11-02）起，`deflateResetKeep` 丢弃前瞻，首次发布于 1.4。用这个驱动程序（AddressSanitizer，arm64 macOS），报告出现在 1.4 和固定的 `develop` 上，不出现在 1.3.1 和 1.3.2 上：在那两个版本中，`deflateResetKeep` 之后的 `deflate(Z_BLOCK)` 仍会压缩保留的前瞻，不会留下等待插入的链头。

对证明的影响：不能取消 deflate 流定义域对直接调用 `deflateResetKeep` 的排除（`docs/deviations.md`）：取消后，`deflate` 可能读到窗口之外。允许 `deflateResetKeep` 的位置形式散列链不变式在第 4 步之后不成立。
