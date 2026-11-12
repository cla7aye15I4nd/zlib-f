<!-- source-sha256: aa4d42c7e23e371f99910f821e2639f1898e719f8e487ea3d0075d828a3f34e5 -->
# 报告：`deflateResetKeep` 与 `deflateCopy` 之后 `longest_match` 的越界读取

写给 zlib 维护者的草稿，供项目所有者使用。未发送，仅作记录保留。

对本项目而言，`deflateResetKeep` 是 `deflateReset` 的内部步骤：zlib.h 声明它不属于 zlib API，因此已证明的 deflate 定义域排除对它的直接调用，此发现不再计划进一步的工作。

## 摘要

在 zlib `develop` 的提交 `757f0527`（`ZLIB_VERSION "1.3.2.1-motley"`）上，一串使用有效缓冲区的导出函数调用会使 `longest_match` 读到窗口之外。根本原因是读取了由 `deflateCopy` 生成的流中一个未初始化的 `prev` 项。AddressSanitizer 在 `deflate.c:1511` 报告 `heap-buffer-overflow READ of size 1`。

这个序列需要直接调用 `deflateResetKeep`。`zlib.h` 把该函数声明在 `/* undocumented functions (not part of the zlib API) */` 之下：它是导出函数，但不属于 zlib API。所以这不是已文档化 API 的缺陷，而是一个导出但未文档化的函数使之可达的内存错误，并且它随两处近期修改出现（见受影响的版本）。在已文档化的 API 内我们没有找到这样的序列；对我们已证明的定义域，我们证明不存在这样的序列（见与证明的关系）。

已在 x86_64 Linux（GCC 14）上用 AddressSanitizer 和 valgrind 确认，也在 arm64 macOS 上确认。受影响的是 zlib 1.4 和 `develop`，不包括 1.3.1 和 1.3.2。

## 受影响的代码

- `deflateResetKeep`（`deflate.c:644`）保留窗口和散列，并设置 `lookahead = 0`（"Keep the window and the hash, but drop what was left unfinished"）。
- `deflateCopy`（`deflate.c:1383`）只复制 `strstart - insert` 以下的 `prev`：

  ```c
  zmemcpy(ds->prev, ss->prev,
          (ss->slid || ss->strstart - ss->insert > ds->w_size ? ds->w_size :
              ss->strstart - ss->insert) * sizeof(Pos));
  ```

- `deflate_rle`（`deflate.c:2177`）和 `deflate_huff` 以 `s->insert = 0` 结束。

## 受影响的版本

两个成因都是近期修改，这个序列需要两者同时存在：

- 自提交 8404590（"Copy only the initialized deflate state in deflateCopy"，2026-01-10）起，`deflateCopy` 只复制前沿以下的 `prev`，首次发布于 1.3.2。1.3.1 复制全部 `w_size` 项。
- 自提交 1e4178b（"Fix deflateResetKeep() when used in the middle of a stream"，2026-11-02）起，`deflateResetKeep` 丢弃前瞻，首次发布于 1.4。在此之前，`deflateResetKeep` 之后的 `deflate(Z_BLOCK)` 会压缩保留的前瞻，不留下等待插入的链头。

复现在 1.4 和 `develop`（757f0527）上报告这次读取，在 1.3.1 和 1.3.2 上没有报告（AddressSanitizer，arm64 macOS，同一个驱动程序）。

## 机制

1. 一个流不刷新地压缩一些输入。位置 `strstart - 2` 和 `strstart - 1` 已插入散列，是链头。
2. `deflateResetKeep` 丢弃前瞻，保留散列。这两个位置仍是链头。
3. 无输入的 `deflate(Z_BLOCK)` 设置 `insert = 2`。这两个位置此时算作等待插入，尽管散列中已经有它们。
4. `deflateCopy` 只复制 `strstart - insert` 以下的 `prev`。在副本中，这两个链头的 `prev` 项从未被写入。
5. 在副本上，`deflateParams(Z_RLE)` 和无输入的 `deflate(Z_SYNC_FLUSH)` 运行 `deflate_rle`，它设置 `insert = 0`。`fill_window` 只在 `insert` 非零时重新插入等待的位置，所以这两个项保持未写入。
6. 在副本上，先 `deflateParams(Z_DEFAULT_STRATEGY)`，再给出以 `strstart - 2` 处三个字节开头的输入。`deflate_slow` 以相同的键插入 `strstart`，并对旧链头调用 `longest_match`。链遍历把未写入的 `prev` 项读作下一个候选，并比较该位置的窗口字节。

候选就是该项中的任意值，最大 65535。窗口较小时（`windowBits` 9，1024 字节），大多数取值都在窗口分配之外。

## 复现

本目录中的 [`deflate-copy-pending-prev/repro.c`](deflate-copy-pending-prev/repro.c)；带运行脚本的相同驱动程序在 [`tests/regression/deflate-copy-pending-prev`](../../tests/regression/deflate-copy-pending-prev/README.md)。它包含 `deflate.h`，只为读取第 6 步所需的 `strstart` 和三个窗口字节，以及打印状态。它安装一个用 16 位值 1030 填充新内存的分配器，使候选可确定；带参数 `plain` 时使用默认分配器。

用 `-fsanitize=address,undefined -g -O1` 构建固定版本的源码并运行：

```
==ERROR: AddressSanitizer: heap-buffer-overflow ... READ of size 1
    #0 longest_match deflate.c:1511
    #1 deflate_slow deflate.c:2029
    #2 deflate deflate.c:1239
... is located 7 bytes after 1026-byte region ... allocated by ... deflateCopy deflate.c:1361
```

观察结果：

| 变体 | 平台 | 结果 |
| --- | --- | --- |
| 原样的 `repro.c`，ASan 和 UBSan | x86_64 Linux，GCC 14 | `deflate.c:1511` 处 1 字节的 heap-buffer-overflow 读取，位于 `deflateCopy`（`deflate.c:1361`）分配的 1026 字节窗口块之后 7 字节 |
| `repro plain`（默认分配器），无 sanitizer，valgrind `--track-origins=yes` | x86_64 Linux，GCC 14 | `longest_match` 中 "Conditional jump or move depends on uninitialised value(s)"（`deflate.c:1555`，对下一个候选的循环判断），调用者为 `deflate_slow`（`deflate.c:2029`）；该值来自 `deflateCopy` 的 `prev` 分配（`deflate.c:1362`） |
| 原样的 `repro.c` | arm64 macOS，Apple clang 21 | `deflate.c:1511` 处 heap-buffer-overflow |
| 默认分配器 | arm64 macOS，Apple clang 21 | 相同的报告 |
| 把 `deflateCopy` 改为复制 `prev` 的全部 `w_size` 项 | arm64 macOS，Apple clang 21 | 无报告；`deflate` 返回 `Z_STREAM_END` |
| zlib 1.3.1、1.3.2 | arm64 macOS，Apple clang 21 | 无报告 |
| zlib 1.4 | arm64 macOS，Apple clang 21 | `deflate.c:1511` 处 heap-buffer-overflow |

Linux 输出见 [`report.txt`](../../tests/regression/deflate-copy-pending-prev/report.txt)。没有运行 MemorySanitizer；valgrind 报告了未初始化读取。不使用 sanitizer 时，这次读取可能落在已映射的内存中，什么也不显示。

## 影响

- 先读取未初始化的内存，再在距窗口起点最多 65535 的偏移处读取最多 258 字节。未观察到写入。
- 压缩输出可能依赖读到的字节。
- 它要求调用者直接调用 `deflateResetKeep`，然后 `deflateCopy`，再在副本上更改策略。只控制被压缩数据的攻击者无法触发它。

## 可能的修复

每一项都只是建议。只试过第一项，且只在上面这一个复现上试过。

1. 在 `deflateCopy` 中复制 `prev` 的全部 `w_size` 项。
2. 在 `deflateResetKeep` 中清空散列（`CLEAR_HASH`），使没有链头指向将被再次插入的位置。这也消除了 `deflate-resetkeep-stale-hash` 中过期散列造成的数据错误。
3. 不改代码：`zlib.h` 已声明 `deflateResetKeep` 不属于 zlib API。在那里注明它不得与 `deflateCopy` 一起使用，或不再导出它，会让这一点更明确。

## 与证明的关系

deflate 安全定理把直接调用 `deflateResetKeep` 排除在流定义域之外（`docs/deviations.md`）。这不是比 `zlib.h` 更窄的限制，因为 `zlib.h` 声明该函数不属于 zlib API；这份报告也是不能取消这一排除的原因之一。

对于没有这一调用的历史，没有链头等待插入，因此 `deflateCopy` 对 `prev` 的部分复制覆盖了链遍历能到达的每一项。这是一个定理：`DInv.heads_inserted`（以及 level 0 有一次待处理滑动时的 `DInv.slid_heads_inserted`，`ZlibF/Proof/deflate.c.universal-heads.lean`）断言，在满足 deflate 不变式 `DInv` 的每个状态中，每个非零的 `head` 项都小于 `strstart - insert`。`DInv` 在流定义域的每个历史之后都成立（`reachable_inv`，在 `Goal.deflate_sequence_safety` 的假设下）。本项目的真实 C 检查器在 460 万个采样状态上与之一致（这是证据，不是证明）。
