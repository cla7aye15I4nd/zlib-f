<!-- source-sha256: 2a6724e1a35a1afd071c6b28dbceff66c7a100c0383fd2b213baeb5f12c47cee -->
# gz_reset 从不写入 x.next；gzseek 和 gzdirect 却读取它

状态：按 C 标准的字面规定是未定义的。没有任何 sanitizer 报告它，也没有观察到错误行为。验证对象中由本地补丁
[0005-gz-next-zero-advance.patch](../../../patches/0005-gz-next-zero-advance.patch) 修复；该补丁经所有者于
2026-11-12 批准，尚未提交上游。同一补丁也修复 [gz-next-dangling-after-direct-read](../gz-next-dangling-after-direct-read/README.md)。

源码固定版本：`757f0527154291bcf6bfbd6396ecde6bedd2db95`，加补丁 0001 至 0004。

## 问题

`gz_open` 用 `malloc` 分配 `gz_state` 记录，`gz_reset` 初始化其中除 `x.next` 以外的字段。在读取者上，`x.next` 第一次被写入是在产生输出时（透明模式下的 `gz_look`、`gz_decomp`、`gz_fetch`、`gzungetc`）。有两个函数在此之前就计算它：

- `gzseek64`，不在透明模式时：`n` 是目标中落在输出缓冲区里的部分，缓冲区为空时为 0，而代码照样执行 `state->x.next += n`（`gzlib.c` 中读取时跳过输出缓冲区已有内容的那一段）。
- `gz_skip_have`，由 `gzdirect` 在 `gz_look` 之后调用：对 gzip 文件，`gz_look` 不写 `x.next`，而 `gz_skip_have` 以 `n == 0` 执行 `state->x.next += n`。

读到的值是这块分配的不确定内容。C11 规定，使用可能是陷阱表示的不确定值是未定义的（6.2.6.1p5，J.2）；指针运算只对指向对象或其末尾之后一个位置的指针有定义（6.5.6p8），不确定的指针两者都不是。在 x86_64 上，用通常的编译器，`p + 0` 不改变 `p`，不会出错。

## 调用历史

```
f = gzopen("data.gz", "rb");      /* gzip 文件 */
gzseek(f, 3, SEEK_SET);           /* 对从未写入的字段执行 x.next += 0 */

f = gzopen("data.gz", "rb");
gzdirect(f);                      /* gz_look（gzip），然后 gz_skip_have：x.next += 0 */
```

两者都是文档允许的用法；zlib.h 甚至建议在 `gzopen` 或 `gzdopen` 之后立即调用 `gzdirect`。

## 证据

强度：仅按 C 标准的字面规定。没有 sanitizer 报告它：对任意值做 `p + 0` 既不是越界访问也不是指针溢出，而 MemorySanitizer 不报告只被复制的未初始化值。因此复现把 `gzlib.c` 和 `gzread.c` 中每个 `x.next += n` 都经过一个探针（`probe.h`；计算出的值不变），并打印每次 `n == 0` 的计算。在 AddressSanitizer 下，新分配的内存填充为 `0xbe`：

```
x.next + 0 at gzlib.c:435, x.next = 0xbebebebebebebebe
x.next + 0 at gzread.c:313, x.next = 0xbebebebebebebebe
```

文件：`unset.c`、`probe.h`、`run.sh`、[report.txt](report.txt)（x86_64 Linux，gcc 15.2；arm64 macOS 上结果相同）。`run.sh` 在 ASan 和 UBSan 下分别构建不含和含 0005 的源码；修复前探针看到这两次计算，修复后一次也没有，两个构建都没有 sanitizer 报告。在 Lean 模型中，新分配的指针字段是 NULL，而 `NULL + 0` 能通过，所以模型也看不到它；暴露它的是证明规则“指针字段先写后读”（`docs/spec/safety.md` 第 3 节）。

## 范围

所有读取者：在 `gzopen`/`gzdopen` 之后（以及在 `gzrewind` 之后，那时 `x.next` 保留着以前的值），第一次不在透明模式且输出缓冲区为空的 `gzseek`，或对 gzip 文件的 `gzdirect`。在常见平台上没有可观察的后果。

## zlib.h 的说法

没有说明：公开的 `next` 字段“只能被 gzgetc() 宏使用”，而该宏只在 `have` 不为零时读取它。

## 修复

[0005-gz-next-zero-advance.patch](../../../patches/0005-gz-next-zero-advance.patch)：在 `gzseek64` 和 `gz_skip_have` 中，只有 `n` 不为零时才移动 `x.next`。当 `n` 不为零时，`x.have` 不为零，所以该字段在产生那些输出时已经写入。在 `gz_reset` 中把 `x.next` 初始化为 `NULL` 不行：`NULL + 0` 本身在 C 中就是未定义的，clang 的 `-fsanitize=pointer-overflow` 会报告它。在任何路径上，结果、返回值和状态都不变。

PR 草稿：[upstream-description.md](upstream-description.md)。
