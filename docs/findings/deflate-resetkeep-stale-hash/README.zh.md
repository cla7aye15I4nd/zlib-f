<!-- source-sha256: 0c33f0dd3010f18bc9d35230dbd3d4ab3acdba2ffac59abb19f50be7a3572299 -->
# deflateResetKeep：过期的散列项可能产生错误的匹配

状态：已在固定版本的 C 上复现；`deflateResetKeep` 的预期用法在 `zlib.h` 中没有文档（列在未文档化函数中），所以这是否算 zlib 缺陷，**待与上游确认**。这是数据错误，不是内存错误。

`deflateResetKeep` 保留窗口和散列（"Keep the window and the hash, but drop what was left unfinished"）：`strstart` 不变，`lookahead` 变为 0。散列中仍有位置 `strstart - 2` 和 `strstart - 1`，它们的键由延伸进被丢弃前瞻的三个字节算出。下一次 `deflate` 从 `strstart` 起写入新输入。`longest_match` 不比较候选的第三个字节（依赖散列键相等），因此一个过期候选可能在第三个字节错误时被接受。

复现：`repro.c` 不刷新地压缩数据 A，调用 `deflateResetKeep`，把数据 B 压缩到结束，再以保留的窗口 `window[0 .. strstart)` 作为字典解码第二个流。前 41 个完成的历史中有 3 个解码结果与 B 不同（种子 13、35、40）。在 `s->lookahead = 0;` 之后加入 `CLEAR_HASH(s)` 后，200000 个中没有一个不同。

对证明的影响：`deflateResetKeep` 之后 `DInv` 的散列链条款不成立（`docs/progress.md`，deflate）。安全性不依赖散列键（`longest_match` 只读取 `strstart` 以下的窗口字节）。
