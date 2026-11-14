<!-- source-sha256: 2f116d2ada5ebe7c724c2e3a249d0468d0f186c99ec7206fd15d34cb8f1f6d7a -->
# 上游 PR 草稿：gz 位置溢出

供所有者提交。一个 PR 覆盖读写两侧（[gzread-pos-overflow](README.md)、[gzwrite-pos-overflow](../gzwrite-pos-overflow/README.md)）；改动是 [0004-gz-position-overflow.patch](../../../patches/0004-gz-position-overflow.patch)。尚未发送任何内容。向上游提交的是英文原文；下面是它的中文译文。

---

**标题：** `gzread/gzwrite: do not let the uncompressed position overflow z_off64_t`（gzread/gzwrite：不让未压缩位置溢出 z_off64_t）

**问题**

`state->x.pos`（有符号 `z_off64_t`）随每个交付或接收的字节增加，没有上界。`gzseek` 只检查它自己的目标能否表示，所以它可以把 `x.pos` 留在 `GZ_OFF_MAX` 或其附近，下一次读或写就会发生有符号整数溢出。

读取一侧，在 Linux 上：对 `/dev/zero` 的 `lseek` 成功但不移动，所以在一次透明 `gzread` 之后，`gzseek(f, INT64_MAX, SEEK_SET)` 走 COPY 路径并设置 `x.pos = INT64_MAX`。下一次 `gzread` 在 `gz_read` 中溢出（`state->x.pos += n`）。如果定位到 `INT64_MAX - 4`，溢出发生在应用程序中的 `gzgetc()` 宏里，因为 `gz_fetch` 填满了整个输出缓冲区，而只有再四个字节的位置能够表示。

写入一侧：`/dev/null` 上的透明写入者，`gzseek(f, INT64_MAX - 10, SEEK_SET)`，然后 `gzwrite(f, buf, 100)`：`gz_zero` 写出直到 `INT64_MAX - 10` 的零，然后复制使 `x.pos` 溢出（`gz_write` 中的 `state->x.pos += copy`）。在 `INT64_MAX` 处的 `gzputc` 在其快速路径中溢出。在 x86_64 Linux 上，填零大约需要 17 分钟。

**复现**

```c
int fd = open("/dev/zero", O_RDONLY);
gzFile f = gzdopen(fd, "r");
char buf[16];
gzread(f, buf, 1);
gzseek(f, INT64_MAX, SEEK_SET);
gzread(f, buf, sizeof buf);   /* gzread.c: signed integer overflow: 9223372036854775807 + 16 */
```

```c
int fd = open("/dev/null", O_WRONLY);
gzFile f = gzdopen(fd, "wT");
char buf[100] = {0};
gzbuffer(f, 1u << 29);
gzseek(f, INT64_MAX - 10, SEEK_SET);
gzwrite(f, buf, sizeof buf);  /* gzwrite.c: signed integer overflow: 9223372036854775797 + 100 */
```

用 `-fsanitize=undefined` 构建，x86_64 Linux，gcc 15.2。

**修复**

读取：辅助函数 `gz_room()` 给出在不超过 `GZ_OFF_MAX` 的前提下还能交付多少字节。`gz_fetch` 最多填入这么多（至少一个，以便仍能检测到文件结束），这保持 `x.pos + x.have <= GZ_OFF_MAX`，从而 `gzgetc()` 宏保持有定义。`gz_read` 和 `gzgets` 最多交付这么多；无法交付的数据被丢弃，并给出 `Z_DATA_ERROR` "position overflow"。写入：`gz_write`、`gzputc`（快速路径）和 `gzprintf` 以 `Z_DATA_ERROR` "position overflow" 拒绝会使 `x.pos` 超过 `GZ_OFF_MAX` 的写入。低于 `GZ_OFF_MAX - 2 * size` 的位置行为与以前完全相同；到达界限时，文件结束像以前一样报告。

**测试**

- `make test`，默认构建以及 `-fsanitize=address,undefined`：通过。
- 上面两个历史以及在 `INT64_MAX` 处的 `gzputc`，修复前后，在 ASan 和 UBSan 下：报告消失；调用返回错误 "position overflow"。
- 不经过 `gz_read` 取缓冲字节的路径（`gzungetc`、`gzgetc()` 宏和函数、`gzdirect`、`gzseek`、`gzgets`），在 `INT64_MAX - 2` 处：修复前 `gzgetc` 函数溢出；修复后没有报告。该改动使每个调用返回时都满足 `x.pos + x.have <= GZ_OFF_MAX`，因此这些路径不需要自己的检查。
- 大约 30 000 个带故障注入（`read`/`write` 失败或变短，`lseek`、`malloc`、`close` 失败）的随机 gz 调用历史，其中一半使用设备式 `lseek`，在 macOS 和 x86_64 Linux（带 LeakSanitizer）上以 ASan 和 UBSan 运行：没有报告，没有泄漏，没有挂起。
