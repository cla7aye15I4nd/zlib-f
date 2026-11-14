<!-- source-sha256: 4241abc7fba109281af6cd255bf46718f14fb4bd79ffef43a0c777980f73126d -->
# gzread：在设备上定位之后位置发生有符号溢出

状态：在 x86_64 Linux 上由 UndefinedBehaviorSanitizer 确认。验证对象中由本地补丁
[0004-gz-position-overflow.patch](../../../patches/0004-gz-position-overflow.patch) 修复；该补丁经所有者于
2026-11-12 批准，尚未提交上游。写入一侧的对应问题：[gzwrite-pos-overflow](../gzwrite-pos-overflow/README.md)。

源码固定版本：`757f0527154291bcf6bfbd6396ecde6bedd2db95`，加补丁 0001 至 0003。

## 问题

`state->x.pos` 是未压缩数据中的位置，类型为有符号的 `z_off64_t`。读取函数把交付的字节数加到它上面，没有任何上界：`gz_read`（`state->x.pos += n`）、`gzgetc`、`gzgets`，以及调用者代码中 zlib.h 的 `gzgetc()` 宏。`gzseek64` 只检查目标能否用 `z_off64_t` 表示，所以它自己就可以把 `x.pos` 设为 `GZ_OFF_MAX`。在透明模式（`how == COPY`）下，它在对描述符做 `lseek` 之后这样做。在 Linux 上，对 `/dev/zero`（以及 `/dev/urandom`、`/dev/null`）的 `lseek` 无论偏移多大都返回 0、不失败，而设备继续提供字节。下一次读取就会让有符号的位置溢出。

## 调用历史

```
fd = open("/dev/zero", O_RDONLY);
f = gzdopen(fd, "r");
gzread(f, buf, 1);                       /* 不是 gzip：透明复制（COPY） */
gzseek(f, INT64_MAX, SEEK_SET);          /* lseek “成功”；x.pos = INT64_MAX */
gzread(f, buf, 16);                      /* x.pos += 16：有符号溢出 */
```

第二个历史定位到 `INT64_MAX - 4`，用 `gzread` 读一个字节，再用 `gzgetc()` 宏读三个；第四次 `gzgetc()` 在宏里、也就是在调用者的代码里溢出，因为 `gz_read` 填满了整个输出缓冲区，超出了可表示的位置。

每个调用都在文档允许的用法之内：zlib.h 允许对任何描述符使用 `gzdopen`，允许定位到偏移类型能表示的任何位置，也允许之后读取。

## 证据

UndefinedBehaviorSanitizer，x86_64 Linux（内核 7.0，gcc 15.2），源码加补丁 0001 至 0003：

```
gzread.c:414:22: runtime error: signed integer overflow: 9223372036854775807 + 16 cannot be represented in type 'long int'
devzero.c:45:17: runtime error: signed integer overflow: 9223372036854775807 + 1 cannot be represented in type 'long int'
```

第二行来自 `gzgetc()` 宏。复现：[tests/regression/gzread-pos-overflow](../../../tests/regression/gzread-pos-overflow/README.md)（`devzero.c`、`run.sh`、[报告](../../../tests/regression/gzread-pos-overflow/report.txt)）。强度：高。真实的 C、真实的设备、sanitizer 报告；故障注入测试框架在模拟设备式 `lseek` 时也得到同样的报告（2 000 个历史中一个）。在 macOS 上不能复现，因为那里对 `/dev/zero` 的 `lseek` 不接受这样的偏移。

## 范围

对 `lseek` 成功却不限制偏移、随后还提供数据的描述符做透明读取：Linux 上的字符设备。对 gzip 流，同样的溢出需要大约 2^63 字节的解压输出，不现实。后果是有符号计数器上的未定义行为；按通常的回绕，`gztell` 变为负数，之后的定位从错误的位置计算。在目前读过的代码中，它不会引起内存错误（**尚待证明确认**）。

## zlib.h 的说法

zlib.h 说，“如果结果位置不能用偏移类型表示”，`gzseek` 返回 -1。对于把位置推过这一界限的读取，以及对于设备，它没有说明。

## 修复

[0004-gz-position-overflow.patch](../../../patches/0004-gz-position-overflow.patch) 的读取部分：辅助函数 `gz_room(state, max)` 返回 `max`，如果再交付 `max` 个字节会使 `x.pos` 超过 `GZ_OFF_MAX`，则返回更少。`gz_fetch` 最多向输出缓冲区填入这么多字节（至少一个，以便仍能发现输入结束），从而 `x.pos + x.have` 永不超过 `GZ_OFF_MAX`，`gzgetc()` 宏保持有定义。`gz_read` 和 `gzgets` 最多交付这么多字节；如果还剩无法交付的数据，就丢弃它并设置 `Z_DATA_ERROR` "position overflow"。在 `GZ_OFF_MAX - 2 * size` 以下没有任何变化。接近界限时交付相同的字节，只是每次填充更少。到达界限时，输入结束仍像以前一样报告；只有原本会使位置溢出的数据变成错误。

补丁保持的不变式是：每次调用返回时 `x.pos + x.have <= GZ_OFF_MAX`。`x.have` 的每个产生者都保持它：`gz_fetch` 最多加载 `GZ_OFF_MAX - x.pos` 个字节；`gz_look` 在透明模式下最多加载 `size` 个字节，而且只在位置 0（紧接 `gz_reset` 之后）；`gz_read` 的直接路径最多交付这么多字节；`gzungetc` 加入一个字节时把 `x.pos` 减一；透明模式下的定位清空缓冲区。`gz_fetch` 在 `GZ_OFF_MAX` 处为发现输入结束而加载的那一个字节，由它在那里仅有的调用者 `gz_read` 和 `gzgets` 在返回前丢弃（`gz_skip` 从不在 `GZ_OFF_MAX` 处取数据，因为 `x.pos + skip` 至多为 `GZ_OFF_MAX`）。因此逐字节取缓冲数据的快速路径（`gzgetc` 函数、`gzgetc()` 宏）以及 `gz_skip_have` 都无需检查。复现的 `fast` 运行在 `INT64_MAX - 2` 处检验了这些路径。

补丁的检查：[upstream-description.md](upstream-description.md) 的 Testing 一节。
