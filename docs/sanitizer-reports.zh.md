<!-- source-sha256: a62580dc8b01341fd1897f2945979f6f8debceea4f069326f2d083a61ca819e4 -->
# Sanitizer 报告

本页列出所有保留的复现：在这些复现中，sanitizer 报告真实 C 代码有未定义行为或内存错误。每个复现都有一个目录，内含运行脚本、C 驱动程序，以及 `report.txt` 中的原始 sanitizer 输出。

## 这些是什么

主表各行都是调用者一侧的内存布局和调用顺序。调用 zlib 的程序必须有意构造它们：把头部缓冲区指向自己的输入或输出，在 zlib 写头部时修改头部记录，在 zlib.h 允许的时间点之后调用函数，或者为长度单元传入 `NULL`。它们不是攻击者能控制的输入。任何压缩字节流都到达不了这些情形。

每一行都在已证明的定义域之外：某个公开目标的一个具名前提排除了它。若 zlib.h 对该布局没有说明，该前提列在[偏离记录](deviations.md)中。

这些行都没有报告给上游。库缺陷在“库缺陷”一节：上游已修复其中一个；两个的修复已提交上游，维护者尚未确认；另外两个有本地的候选修复，尚未提交。

## 已证明定义域之外的调用者布局

判定来自固定版本源码加本仓库补丁，在本项目的目标平台 x86_64 Linux 上用 AddressSanitizer 和 UndefinedBehaviorSanitizer 构建。源码行号以固定版本源码为准。此前在 arm64 macOS 上的运行给出相同判定，唯一差异记在 `迟到的 deflatePrime` 一行。

| 名称 | 调用者布局或调用序列 | Sanitizer 判定 | 由谁排除 | 复现 | zlib.h |
| --- | --- | --- | --- | --- | --- |
| inflate extra 重叠 | gzip `inflate`；`head->extra` 指向输入缓冲区，并与正在读取的 extra 字段重叠 | `memcpy-param-overlap`，`inflate.c:626` | `InflateHeaderProgress`（extra 缓冲区与未读输入分离），`ActiveHeader` 的合取项：`Goal.inflate` 和 `Goal.inflate_sequence` 的前提 | [inflate-gzip-extra](../tests/regression/inflate-gzip-extra/README.md)，`overlap.c`，[报告](../tests/regression/inflate-gzip-extra/report.txt) | 未说明 |
| inflate extra 缩短 | `extra_max` 为 `2^32 - 1`；第一次 `inflate` 停在 extra 字段内；调用者把 `head->extra_len` 设为 0；再调用 `inflate` | `heap-buffer-overflow`，4 字节写，`inflate.c:626` | `InflateHeaderProgress`（在 `EXTRA` 中 `extra_len` 不小于 `state->length`）：`Goal.inflate` 和 `Goal.inflate_sequence` 的前提 | [inflate-gzip-extra](../tests/regression/inflate-gzip-extra/README.md)，`shrink.c`，[报告](../tests/regression/inflate-gzip-extra/report.txt) | 未说明 |
| deflate 名称在输出中 | gzip `deflate`，`memLevel` 1；`head->name` 就是调用者的输出缓冲区 | `heap-buffer-overflow`，1 字节读，`deflate.c:1177` | `DeflateHeaderApart`（名称与输出范围分离），`ActiveHeader` 的合取项：`Goal.deflate` 和 `Goal.deflate_sequence` 的前提 | [deflate-gzip-name-output](../tests/regression/deflate-gzip-name-output/README.md)，`output.c`，[报告](../tests/regression/deflate-gzip-name-output/report.txt) | 未说明 |
| deflate 名称在待发缓冲区中 | gzip `deflate`；`head->name` 指向流自己的 `pending_buf` | `heap-buffer-overflow`，1 字节读，`deflate.c:1177` | `DeflateHeaderApart`（名称在流拥有的存储之外）：`Goal.deflate` 和 `Goal.deflate_sequence` 的前提 | [deflate-gzip-name-output](../tests/regression/deflate-gzip-name-output/README.md)，`pending.c`，[报告](../tests/regression/deflate-gzip-name-output/report.txt) | 未说明 |
| 迟到的 deflatePrime | raw，`memLevel` 1；`deflate(Z_NO_FLUSH)` 记录符号；调用 200 次 `deflatePrime(16)`；`deflate(Z_FINISH)` | UBSan：下标 767 超出 `_dist_code[512]`，`trees.c:930`。在 arm64 macOS 上 UBSan 随后还报告有符号左移溢出，`trees.c:937`；在 x86_64 Linux 上没有，因为越界读到的字节不同 | `DeflateNotStarted`，`StreamArguments` 对 `deflatePrime` 的要求：该历史不属于 `StreamReachable`，因而在 `Goal.deflate` 和 `Goal.deflate_sequence` 之外 | [deflate-history-domain](../tests/regression/deflate-history-domain/README.md)，`prime.c`，[报告](../tests/regression/deflate-history-domain/report.txt) | 已排除：`deflatePrime` `must be used before the first deflate() call` |
| 迟到的 deflateSetHeader(NULL) | gzip，`memLevel` 1，2000 字节 extra 字段；第一次 `deflate` 停在其中；`deflateSetHeader(strm, NULL)`；再调用 `deflate` | UBSan：通过空指针访问成员，`deflate.c:1137`；随后 ASan 报告读操作 `SEGV`，`deflate.c:1137` | `DeflateNotStarted`，`StreamArguments` 对 `deflateSetHeader` 的要求：在 `Goal.deflate` 和 `Goal.deflate_sequence` 之外 | [deflate-history-domain](../tests/regression/deflate-history-domain/README.md)，`header.c 1`，[报告](../tests/regression/deflate-history-domain/report.txt) | 已排除：`deflateSetHeader` `may be called ... before the first call of deflate()` |
| deflate extra 缩短 | 开头相同；调用者把 `extra_len` 设为 10，小于已写出的 500 字节；再调用 `deflate` | `heap-buffer-overflow`，512 字节读，`deflate.c:1142` | `DeflateHeaderProgress`（字段仍覆盖 `gzindex`），`ActiveHeader` 的合取项：`Goal.deflate` 和 `Goal.deflate_sequence` 的前提 | [deflate-history-domain](../tests/regression/deflate-history-domain/README.md)，`header.c 2`，[报告](../tests/regression/deflate-history-domain/report.txt) | 未说明写头部期间能否修改 |
| deflate extra 清空 | gzip，`memLevel` 1，1500 字节 extra 字段，3 字节名称；第一次 `deflate` 停在 extra 字段内；调用者把 `extra` 设为 `NULL`；再调用 `deflate` | `heap-buffer-overflow`，1 字节读，`deflate.c:1177`，位于名称之后 496 字节 | `DeflateHeaderProgress`（字段为 `NULL` 时 `gzindex` 为 0）：`Goal.deflate` 和 `Goal.deflate_sequence` 的前提 | [deflate-history-domain](../tests/regression/deflate-history-domain/README.md)，`clear.c`，[报告](../tests/regression/deflate-history-domain/report.txt) | 未说明写头部期间能否修改 |
| compress 空长度 | `compress2(dest, NULL, source, 1, 6)` 和 `compress(dest, NULL, source, 1)` | UBSan：加载类型为 `uLongf` 的空指针，`compress.c:70` | 长度单元非空的 `CompressorContract`（`capacity ≠ none`）：`Goal.compress2` 和 `Goal.compress` 的前提 | [compress-allocation](../tests/regression/compress-allocation/README.md)，`ubwitness.c`，[报告](../tests/regression/compress-allocation/report.txt) | 把 `destLen` 描述为入口时的缓冲区大小；没有提到 `NULL` |

对 `compress 空长度`，`report.txt` 只包含 `run.sh` 的见证步骤。该脚本其余部分是 Lean 对比，没有 sanitizer 报告。

## 已证明定义域之外的导出函数调用序列

与上面的行不同，这不是调用者布局：每个缓冲区都有效且彼此分离，每次调用都是导出函数。该序列使用 `deflateResetKeep`，zlib.h 把它列在未文档化函数中，deflate 流定义域排除了它。结论来自固定的、未修改的源码，在 x86_64 Linux 上运行；在 arm64 macOS 上得到相同的 AddressSanitizer 报告。

| 名称 | 调用序列 | Sanitizer 结论 | 排除依据 | 复现 | zlib.h |
| --- | --- | --- | --- | --- | --- |
| deflateResetKeep 之后的 deflateCopy | `windowBits` 9；`deflate(Z_NO_FLUSH)`；`deflateResetKeep`；`deflate(Z_BLOCK)`；`deflateCopy`；在副本上 `deflateParams(Z_RLE)`、无输入的 `deflate(Z_SYNC_FLUSH)`、`deflateParams(Z_DEFAULT_STRATEGY)`，再以 `strstart - 2` 处的字节开头的输入调用 `deflate` | 分配器填充新内存时：ASan `heap-buffer-overflow`，1 字节读，`deflate.c:1511`（`longest_match`）；使用默认分配器时，valgrind：依赖未初始化值的条件跳转，`deflate.c:1555`，该值来自 `deflateCopy` 分配的 `prev` | deflate 调用历史中没有直接的 `deflateResetKeep`（`StreamOperation .deflate`，[偏差](deviations.md)） | [deflate-copy-pending-prev](../tests/regression/deflate-copy-pending-prev/README.md)，`copy.c`，[报告](../tests/regression/deflate-copy-pending-prev/report.txt)；分析见 [findings](findings/deflate-copy-pending-prev/README.md)；[报告草稿](findings/deflate-copy-pending-prev-report.md)，未发送 | 把 `deflateResetKeep` 列在未文档化函数中 |

## 库缺陷

| 名称 | 调用序列 | Sanitizer 判定 | 状态 | 复现 |
| --- | --- | --- | --- | --- |
| inflateCopy 固定表 | 默认 `inflateInit`；`inflate` 停在固定块内；`inflateCopy` | `invalid-pointer-pair`，`inflate.c:1383`，比较静态 `lenfix` 与 inflate 状态 | 文档允许的用法之内的 zlib 缺陷。上游已修复（[PR #1369](https://github.com/madler/zlib/pull/1369)）；验证所用源码以临时补丁应用该修复 | [inflate-copy-fixed](findings/inflate-copy-fixed/README.md)，[报告](findings/inflate-copy-fixed/report.txt) |
| 初始 gzungetc 之后的 gzseek | `gzopen`；在位置 0 调用 `gzungetc`（`x.pos` 变为 -1）；`gzseek(f, 1, SEEK_CUR)`，或在另一个句柄上 `gzseek(f, LONG_MAX, SEEK_SET)`；透明输入和 gzip 输入 | UBSan：有符号整数溢出，`gzlib.c:395`（`SEEK_CUR`）、`gzlib.c:403`（`SEEK_SET`，透明）、`gzlib.c:424`（`SEEK_SET`，gzip） | 文档允许的用法之内的 zlib 缺陷。修复已提交上游（[PR #1361](https://github.com/madler/zlib/pull/1361)），维护者尚未确认；验证所用源码以临时补丁应用该修复 | [gzseek-pushback-overflow](../tests/regression/gzseek-pushback-overflow/README.md)，`seek.c`，[报告](../tests/regression/gzseek-pushback-overflow/report.txt) |
| 部分读取后 gzread 使用过期的 next | 透明 `gzopen`，`gzbuffer(f, 16)`；对 128 字节文件调用 48 次 `gzgetc`；`read()` 返回 1 字节，随后以 `EIO` 失败；`gzread(f, buf, 1)` | `heap-buffer-overflow`，1 字节读，`gzread.c:369`（`gz_read`），在 32 字节输出缓冲区之后 0 字节处 | 文档允许的用法之内的 zlib 缺陷。修复已提交上游（[PR #1363](https://github.com/madler/zlib/pull/1363)），维护者尚未确认；验证所用源码以临时补丁应用该修复 | [gzread-transparent-stale-next](../tests/regression/gzread-transparent-stale-next/README.md)，`stale.c`，[报告](../tests/regression/gzread-transparent-stale-next/report.txt) |
| gzread 位置溢出（F-1） | x86_64 Linux：`gzdopen(open("/dev/zero"), "r")`；`gzread(f, buf, 1)`（透明）；`gzseek(f, INT64_MAX, SEEK_SET)`，因为对设备的 `lseek` 返回 0 而被接受；`gzread(f, buf, 16)`。另一个历史：定位到 `INT64_MAX - 4`，`gzread` 1 字节，四次 `gzgetc()` | UBSan：有符号整数溢出，`gzread.c:414`（`gz_read`，`x.pos += n`）；第二个历史中在调用者里的 `gzgetc()` 宏 | 文档允许的用法之内的 zlib 缺陷。候选修复，尚未提交：本地补丁 0004，所有者于 2026-11-12 批准 | [gzread-pos-overflow](../tests/regression/gzread-pos-overflow/README.md)，`devzero.c`，[报告](../tests/regression/gzread-pos-overflow/report.txt)；[发现](findings/gzread-pos-overflow/README.md) |
| gzwrite 位置溢出（W7） | `gzdopen(open("/dev/null"), "wT")`；`gzbuffer(f, 2^29)`；`gzseek(f, INT64_MAX - 10, SEEK_SET)`；`gzwrite(f, buf, 100)`（填零需要 17 分钟）。另一个历史：定位到 `INT64_MAX`，`gzputc` | UBSan：有符号整数溢出，`gzwrite.c:230`（`gz_write`，`x.pos += copy`）；`gzwrite.c:352`（`gzputc`） | 文档允许的用法之内的 zlib 缺陷。候选修复，尚未提交：本地补丁 0004，所有者于 2026-11-12 批准 | [gzwrite-pos-overflow](../tests/regression/gzwrite-pos-overflow/README.md)，`wpos.c`，[报告](../tests/regression/gzwrite-pos-overflow/report.txt)；[发现](findings/gzwrite-pos-overflow/README.md) |

这些复现有意构建不含修复的源码；gz 运行脚本还会构建含修复的源码，并检查报告已消失。F-1 和 W7 的报告来自 x86_64 Linux（内核 7.0，gcc 15.2）；gzungetc 之后 gzseek 和过期 `x.next` 的报告来自 arm64 macOS（Apple clang 21），它们显示的缺陷与目标平台无关。

## 干净的运行，保留为布局有定义的证据

这些运行使用相同的 sanitizer，没有任何报告。它们说明某种布局是有定义的 C，因此证明必须覆盖它。

- [inflate-shared-block](../tests/regression/inflate-shared-block/README.md)：输入范围和输出范围位于同一个堆块，两种先后顺序都测。属于 `StreamBuffers` 之内。
- [inflate-gzip-flags-prime](../tests/regression/inflate-gzip-flags-prime/README.md)：在 gzip 流处于 `FLAGS` 时调用 `inflatePrime`，flags 字变为 65544。这是有定义的，尽管 zlib.h 说 `inflatePrime` `should only be used with raw inflate`。

## 未列入

- [deflate-slide](../tests/regression/deflate-slide/README.md)：UBSan 在一个人为构造的内部状态中报告有符号溢出，没有证据表明任何调用序列能到达该状态。它检验的是翻译的溢出故障，不是调用者布局。
- sanitizer 构建必须保持安静的差分回归：`inflate-copy`、`inflate-deferred-distance`、`inflate-prime`、`trees-depth-read`、`crc-byte-views`。
- [deflate-resetkeep-stale-hash](findings/deflate-resetkeep-stale-hash/README.md) 中的数据错误，没有 sanitizer 报告它。

## 添加复现

新的 sanitizer 复现放在 `tests/regression/<name>/` 下，包含 `run.sh`、`report.txt`，并在本页加一行。`report.txt` 保存原始输出，进程号已替换，路径改为相对于仓库或 zlib 根目录。
