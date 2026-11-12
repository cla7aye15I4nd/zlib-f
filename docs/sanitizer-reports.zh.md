<!-- source-sha256: 950d56694ed49eb060233d30e2e7ffec404bcf42f32ca746114ac0651475d16c -->
# Sanitizer 报告

本页列出所有保留的复现：在这些复现中，sanitizer 报告真实 C 代码有未定义行为或内存错误。每个复现都有一个目录，内含运行脚本、C 驱动程序，以及 `report.txt` 中的原始 sanitizer 输出。

## 这些是什么

主表各行都是调用者一侧的内存布局和调用顺序。调用 zlib 的程序必须有意构造它们：把头部缓冲区指向自己的输入或输出，在 zlib 写头部时修改头部记录，在 zlib.h 允许的时间点之后调用函数，或者为长度单元传入 `NULL`。它们不是攻击者能控制的输入。任何压缩字节流都到达不了这些情形。

每一行都在已证明的定义域之外：某个公开目标的一个具名前提排除了它。若 zlib.h 对该布局没有说明，该前提列在[偏离记录](deviations.md)中。

这些行都没有报告给上游。唯一报告给上游的复现是下一节中的库缺陷，上游已经修复。

## 已证明定义域之外的调用者布局

判定来自固定版本源码加本仓库补丁，在本项目的目标平台 x86_64 Linux 上用 AddressSanitizer 和 UndefinedBehaviorSanitizer 构建。源码行号以固定版本源码为准。此前在 arm64 macOS 上的运行给出相同判定，唯一差异记在 `迟到的 deflatePrime` 一行。

| 名称 | 调用者布局或调用序列 | Sanitizer 判定 | 由谁排除 | 复现 | zlib.h |
| --- | --- | --- | --- | --- | --- |
| inflate extra 重叠 | gzip `inflate`；`head->extra` 指向输入缓冲区，并与正在读取的 extra 字段重叠 | `memcpy-param-overlap`，`inflate.c:626` | `InflateHeaderProgress`（extra 缓冲区与未读输入分离），`ActiveHeader` 的合取项：`Goal.inflate` 和 `Goal.inflate_sequence` 的前提 | [inflate-gzip-extra](../tests/regression/inflate-gzip-extra/README.md)，`overlap.c`，[报告](../tests/regression/inflate-gzip-extra/report.txt) | 未说明 |
| inflate extra 缩短 | `extra_max` 为 `2^32 - 1`；第一次 `inflate` 停在 extra 字段内；调用者把 `head->extra_len` 设为 0；再调用 `inflate` | `heap-buffer-overflow`，4 字节写，`inflate.c:626` | `InflateHeaderProgress`（在 `EXTRA` 中 `extra_len` 不小于 `state->length`）：`Goal.inflate` 和 `Goal.inflate_sequence` 的前提 | [inflate-gzip-extra](../tests/regression/inflate-gzip-extra/README.md)，`shrink.c`，[报告](../tests/regression/inflate-gzip-extra/report.txt) | 未说明 |
| deflate 名称在输出中 | gzip `deflate`，`memLevel` 1；`head->name` 就是调用者的输出缓冲区 | `heap-buffer-overflow`，1 字节读，`deflate.c:1177` | `DeflateHeaderApart`（名称与输出范围分离），`ActiveHeader` 的合取项：`Goal.deflate` 和 `Goal.deflate_sequence` 的前提 | [deflate-gzip-name-output](../tests/regression/deflate-gzip-name-output/README.md)，`output.c`，[报告](../tests/regression/deflate-gzip-name-output/report.txt) | 未说明 |
| deflate 名称在待发缓冲区中 | gzip `deflate`；`head->name` 指向流自己的 `pending_buf` | `heap-buffer-overflow`，1 字节读，`deflate.c:1177` | `DeflateHeaderApart`（名称在流拥有的存储之外）：`Goal.deflate` 和 `Goal.deflate_sequence` 的前提 | [deflate-gzip-name-output](../tests/regression/deflate-gzip-name-output/README.md)，`pending.c`，[报告](../tests/regression/deflate-gzip-name-output/report.txt) | 未说明 |
| 迟到的 deflatePrime | raw，`memLevel` 1；`deflate(Z_NO_FLUSH)` 记录符号；调用 200 次 `deflatePrime(16)`；`deflate(Z_FINISH)` | UBSan：下标 767 超出 `_dist_code[512]`，`trees.c:930`。在 arm64 macOS 上 UBSan 随后还报告有符号左移溢出，`trees.c:937`；在 x86_64 Linux 上没有，因为越界读到的字节不同 | `DeflateNotStarted`，`StreamArguments` 对 `deflatePrime` 的要求：该历史不属于 `StreamReachable`，因而在 `Goal.deflate` 和 `Goal.deflate_sequence` 之外 | [deflate-history-domain](../tests/regression/deflate-history-domain/README.md)，`prime.c`，[报告](../tests/regression/deflate-history-domain/report.txt) | 已排除：`deflatePrime` "must be used before the first deflate() call" |
| 迟到的 deflateSetHeader(NULL) | gzip，`memLevel` 1，2000 字节 extra 字段；第一次 `deflate` 停在其中；`deflateSetHeader(strm, NULL)`；再调用 `deflate` | UBSan：通过空指针访问成员，`deflate.c:1137`；随后 ASan 报告读操作 `SEGV`，`deflate.c:1137` | `DeflateNotStarted`，`StreamArguments` 对 `deflateSetHeader` 的要求：在 `Goal.deflate` 和 `Goal.deflate_sequence` 之外 | [deflate-history-domain](../tests/regression/deflate-history-domain/README.md)，`header.c 1`，[报告](../tests/regression/deflate-history-domain/report.txt) | 已排除：`deflateSetHeader` "may be called ... before the first call of deflate()" |
| deflate extra 缩短 | 开头相同；调用者把 `extra_len` 设为 10，小于已写出的 500 字节；再调用 `deflate` | `heap-buffer-overflow`，512 字节读，`deflate.c:1142` | `DeflateHeaderProgress`（字段仍覆盖 `gzindex`），`ActiveHeader` 的合取项：`Goal.deflate` 和 `Goal.deflate_sequence` 的前提 | [deflate-history-domain](../tests/regression/deflate-history-domain/README.md)，`header.c 2`，[报告](../tests/regression/deflate-history-domain/report.txt) | 未说明写头部期间能否修改 |
| deflate extra 清空 | gzip，`memLevel` 1，1500 字节 extra 字段，3 字节名称；第一次 `deflate` 停在 extra 字段内；调用者把 `extra` 设为 `NULL`；再调用 `deflate` | `heap-buffer-overflow`，1 字节读，`deflate.c:1177`，位于名称之后 496 字节 | `DeflateHeaderProgress`（字段为 `NULL` 时 `gzindex` 为 0）：`Goal.deflate` 和 `Goal.deflate_sequence` 的前提 | [deflate-history-domain](../tests/regression/deflate-history-domain/README.md)，`clear.c`，[报告](../tests/regression/deflate-history-domain/report.txt) | 未说明写头部期间能否修改 |
| compress 空长度 | `compress2(dest, NULL, source, 1, 6)` 和 `compress(dest, NULL, source, 1)` | UBSan：加载类型为 `uLongf` 的空指针，`compress.c:70` | 长度单元非空的 `CompressorContract`（`capacity ≠ none`）：`Goal.compress2` 和 `Goal.compress` 的前提 | [compress-allocation](../tests/regression/compress-allocation/README.md)，`ubwitness.c`，[报告](../tests/regression/compress-allocation/report.txt) | 把 `destLen` 描述为入口时的缓冲区大小；没有提到 `NULL` |

对 `compress 空长度`，`report.txt` 只包含 `run.sh` 的见证步骤。该脚本其余部分是 Lean 对比，没有 sanitizer 报告。

## 库缺陷，上游已修复

| 名称 | 调用序列 | Sanitizer 判定 | 状态 | 复现 |
| --- | --- | --- | --- | --- |
| inflateCopy 固定表 | 默认 `inflateInit`；`inflate` 停在固定块内；`inflateCopy` | `invalid-pointer-pair`，`inflate.c:1383`，比较静态 `lenfix` 与 inflate 状态 | 文档允许的用法之内的 zlib 缺陷。上游已修复（[PR #1369](https://github.com/madler/zlib/pull/1369)）；验证所用源码以临时补丁应用该修复 | [inflate-copy-fixed](findings/inflate-copy-fixed/README.md)，[报告](findings/inflate-copy-fixed/report.txt) |

这个复现有意构建未打补丁的固定版本源码。

## 干净的运行，保留为布局有定义的证据

这些运行使用相同的 sanitizer，没有任何报告。它们说明某种布局是有定义的 C，因此证明必须覆盖它。

- [inflate-shared-block](../tests/regression/inflate-shared-block/README.md)：输入范围和输出范围位于同一个堆块，两种先后顺序都测。属于 `StreamBuffers` 之内。
- [inflate-gzip-flags-prime](../tests/regression/inflate-gzip-flags-prime/README.md)：在 gzip 流处于 `FLAGS` 时调用 `inflatePrime`，flags 字变为 65544。这是有定义的，尽管 zlib.h 说 `inflatePrime` "should only be used with raw inflate"。

## 未列入

- [deflate-slide](../tests/regression/deflate-slide/README.md)：UBSan 在一个人为构造的内部状态中报告有符号溢出，没有证据表明任何调用序列能到达该状态。它检验的是翻译的溢出故障，不是调用者布局。
- sanitizer 构建必须保持安静的差分回归：`inflate-copy`、`inflate-deferred-distance`、`inflate-prime`、`trees-depth-read`、`crc-byte-views`。
- [deflate-resetkeep-stale-hash](findings/deflate-resetkeep-stale-hash/README.md) 中的数据错误，没有 sanitizer 报告它。

## 添加复现

新的 sanitizer 复现放在 `tests/regression/<name>/` 下，包含 `run.sh`、`report.txt`，并在本页加一行。`report.txt` 保存原始输出，进程号已替换，路径改为相对于仓库或 zlib 根目录。
