<!-- source-sha256: d92c94049b716713b6544a8a7f78ec56be2972725dfb2aad38a90039d612dd63 -->
# gzwrite：向前定位之后位置发生有符号溢出

状态：在 x86_64 Linux 上用真实的 `/dev/null` 由 UndefinedBehaviorSanitizer 确认。验证对象中由本地补丁
[0004-gz-position-overflow.patch](../../../patches/0004-gz-position-overflow.patch) 修复；该补丁经所有者于
2026-11-12 批准，尚未提交上游。读取一侧的对应问题：[gzread-pos-overflow](../gzread-pos-overflow/README.md)。

源码固定版本：`757f0527154291bcf6bfbd6396ecde6bedd2db95`，加补丁 0001 至 0003。

## 问题

在写入者上，`state->x.pos`（有符号 `z_off64_t`）计数已接收的字节。`gzseek64` 只检查目标能否用 `z_off64_t` 表示；向前定位被记为待处理的跳过量，下一次写入先写出那么多个零（`gz_zero`），把 `x.pos` 移到目标。随后 `gz_write`（`state->x.pos += copy` 和 `+= n`）、`gzputc` 的快速路径（`x.pos++`）和 `gzprintf`（`x.pos += len`）在它上面继续累加，没有上界。

## 调用历史

```
fd = open("/dev/null", O_WRONLY);
f = gzdopen(fd, "wT");                   /* 透明写入者 */
gzbuffer(f, 1 << 29);
gzseek(f, INT64_MAX - 10, SEEK_SET);     /* 待处理的跳过 */
gzwrite(f, buf, 100);                    /* gz_zero 写出 INT64_MAX - 10 个零，
                                            然后 x.pos += 100：有符号溢出 */
```

第二个历史：`gzseek(f, INT64_MAX, SEEK_SET)`，然后 `gzputc(f, 'a')`：在 `gzputc` 的快速路径中溢出。每个调用都在文档允许的用法之内。填零是 2^34 次各 2^29 字节的写入；`/dev/null` 全部接受。

## 证据

UndefinedBehaviorSanitizer，x86_64 Linux（内核 7.0，gcc 15.2），真实的 `/dev/null`，源码加补丁 0001 至 0003，17 分钟：

```
gzwrite.c:230:26: runtime error: signed integer overflow: 9223372036854775797 + 100 cannot be represented in type 'long int'
```

使用一个不经系统调用、替 `/dev/null` 应答的 `write()`（`fastwrite.c`），在 Linux 和 macOS 上大约一分钟得到同样的报告；对 `gzputc`：

```
gzwrite.c:352:25: runtime error: signed integer overflow: 9223372036854775807 + 1 cannot be represented in type 'long int'
```

复现：[tests/regression/gzwrite-pos-overflow](../../../tests/regression/gzwrite-pos-overflow/README.md)（`wpos.c`、`fastwrite.c`、`run.sh`、[报告](../../../tests/regression/gzwrite-pos-overflow/report.txt)）。强度：高（真实的 C、真实的设备、sanitizer 报告），但到达很慢：溢出需要接收端接受大约 2^63 字节。

## 范围

写到接受无界输出的接收端（`/dev/null`、接到丢弃数据的消费者的管道）的透明写入者。对普通文件，写入会早得多地失败（`EFBIG`）。对压缩写入者，这些零要先被压缩，大约 2^63 字节的 CPU 工作，不现实。后果是有符号计数器上的未定义行为；按通常的回绕，`gztell` 变为负数。

## zlib.h 的说法

zlib.h 说，“如果结果位置不能用偏移类型表示”，`gzseek` 返回 -1。对于把位置推过这一界限的写入，它没有说明。

## 修复

[0004-gz-position-overflow.patch](../../../patches/0004-gz-position-overflow.patch) 的写入部分：当 `GZ_OFF_MAX - x.pos < len` 时，`gz_write` 拒绝写入 `len` 个字节；`gzputc` 在 `GZ_OFF_MAX` 处离开其快速路径（随后 `gz_write` 拒绝）；`gzprintf` 拒绝会超过界限的格式化输出。每种情况都设置 `Z_DATA_ERROR` "position overflow"。不超过界限的写入不变。跨越界限的写入被整体拒绝；以前，一旦位置溢出它就是未定义的，只有当 I/O 错误或阻塞在那之前停止了它时才有定义，此时它现在报告 "position overflow" 而不是 I/O 错误。

覆盖读写两侧的 PR 草稿是 [../gzread-pos-overflow/upstream-description.md](../gzread-pos-overflow/upstream-description.md)。
