<!--
source: docs/api/checksums.md
source-sha256: add70bc604b8cdb4f5cb5782d32822cf1e297ceee87c3819e7ac7c144c44e832
-->

# 校验和

[API 手册](README.md) · [契约约定](contracts.md) · [缓冲区工具](utility.md)

可以逐个缓冲区计算校验和，也可以合并独立处理的字节序列的校验和，而不重新读取数据。
下文的字节序列 A 和 B 都是普通数据；契约使用这些序列的 Adler-32 或 CRC-32。

| 任务 | 条目 |
| --- | --- |
| 更新 Adler-32 | [尺寸类型长度](#adler32_z)、[32 位长度](#adler32) |
| 合并 Adler-32 | [普通偏移类型](#adler32_combine)、[显式 64 位偏移类型](#adler32_combine64) |
| 更新 CRC-32 | [尺寸类型长度](#crc32_z)、[32 位长度](#crc32) |
| 合并 CRC-32 | [普通偏移类型](#crc32_combine)、[显式 64 位偏移类型](#crc32_combine64) |
| 复用 CRC 合并算子 | [生成](#crc32_combine_gen)、[用 64 位长度生成](#crc32_combine_gen64)、[应用](#crc32_combine_op) |
| 查看字节表 | [get_crc_table](#get_crc_table) |

这些聚焦契约依据固定版本源码及列出的补丁，遵循默认 LP64 Linux 静态构建中的
`adler32.c`、`crc32.c` 和 `zlib.h`。对源码的解读仍 **to confirm**，需要证明确认。
所有校验和条目都不写状态，不分配或释放内存，也不执行 I/O。
特殊的数值结果是普通值，不是错误码。定义域与效果仍然彼此独立，详见[契约约定](contracts.md)。

实用校验和契约使用真实的字节序列 A 和 B。各个校验和独立计算，Adler-32 从 1 开始，
CRC-32 从 0 开始。这些契约有意不对伪造校验和作出功能保证。
[Lean 目标](../../ZlibF/Spec/Public/Checksums.lean)还描述任意种子值和精确的标量结果。
Adler 条目及其 Lean 目标都要求 NULL 初始化查询的长度为零。
参见[范围偏离](../deviations.md)和[公开目标](../checking/goals.md)。

在本构建中，`uLong` 和 `z_size_t` 是无符号 64 位类型；`uInt` 是无符号 32 位类型。
`z_off_t` 和 `z_off64_t` 是有符号 64 位类型。输入校验和值中高于第 31 位的部分被忽略；
返回的校验和值可容纳于 32 位。显式 `*64` 声明取决于头文件的大文件特性宏。

## adler32_z

```c
uLong ZEXPORT adler32_z(uLong adler, const Bytef *buf, z_size_t len);
```

用一段字节更新 Adler-32 校验和，或取得其初始值。

**Domain.** 受限定义域。`buf` 非 NULL 时，效果为**只读**。

**Pre:** `buf` 为 NULL 且 `len == 0`，或者它指向 `len` 个可读字节。
对于校验和后置条件，`adler` 的低 32 位是 A 的 Adler-32。
不要求设置或清理操作。

**Post:** 对任意 `adler`，NULL、零长度查询都返回 1，不读取字节。
否则返回 A 后接 `buf[0..len-1]` 的 Adler-32。
非 NULL 的零长度区间返回传入校验和的低 32 位。

**Effects:** 保持所有内存和所有权不变。只读取给定区间。
零长度区间允许使用尾后一位指针。

NULL 且长度非零不在本契约范围内。伪造种子值仍不属于本实用功能契约：
单字节路径不一定等同于先将种子的两个半部都对 65521 取模。
参见 [Adler 种子说明](../proof/adler32.md)。

## adler32

```c
uLong ZEXPORT adler32(uLong adler, const Bytef *buf, uInt len);
```

用 32 位字节计数更新 Adler-32 校验和。

**Domain.** 受限定义域。`buf` 非 NULL 时，效果为**只读**。

**Pre:** `buf` 为 NULL 且 `len == 0`，或者它指向 `len` 个可读字节。
对于校验和后置条件，`adler` 的低 32 位是 A 的 Adler-32。

**Post:** 精确返回 `adler32_z(adler, buf, len)` 的结果。
NULL、零长度查询返回 1。非 NULL 的空区间保持校验和的低 32 位。

**Effects:** 保持所有内存和所有权不变。只读取给定区间。
零长度区间允许使用尾后一位指针。

长度至多为 `2^32 - 1`。将更大的长度转换为 `uInt` 会在调用前丢弃高位；
对于更大的区间，应使用 `adler32_z` 或分成多次调用。
`adler32_z` 对零长度 NULL 查询及伪造种子值的范围约束也适用于这里。

## adler32_combine

```c
uLong ZEXPORT adler32_combine(uLong adler1, uLong adler2, z_off_t len2);
```

不读取任何一个序列，计算 A 后接 B 的 Adler-32。

**Domain.** 受限定义域。效果为**纯计算**。

**Pre:** 对于拼接结果，`adler1` 和 `adler2` 的低 32 位分别是 A 和 B 的 Adler-32，
`len2` 是 B 的长度。特别地，B 的校验和独立于 A，从 1 开始。
负长度只为下述拒绝结果而纳入范围。

**Post:** 若 `len2 < 0`，返回 `0xFFFFFFFF`。否则返回 A 后接 B 的 Adler-32。
空 B 的校验和为 1，并保持 A 的校验和不变。

**Effects:** 保持所有内存和所有权不变。不读取缓冲区或流状态。

该哨兵值不是有效的 Adler-32。任意标量参数都不会产生内存访问；其精确的非校验和结果
属于更宽的 Lean 契约。若 B 的长度不正确，则不保证拼接结果。

## adler32_combine64

```c
uLong ZEXPORT adler32_combine64(uLong adler1, uLong adler2, z_off64_t len2);
```

使用显式 64 位长度，计算 A 后接 B 的 Adler-32。

**Domain.** 受限定义域。效果为**纯计算**。

**Pre:** 对于拼接结果，`adler1` 和 `adler2` 的低 32 位分别是独立计算的 A、B 的 Adler-32，
`len2` 是 B 的长度。负长度纳入范围以进行拒绝。

**Post:** 负长度返回 `0xFFFFFFFF`。否则返回 A 后接 B 的 Adler-32。
空 B 保持 A 的校验和不变。

**Effects:** 保持所有内存和所有权不变。不读取缓冲区或流状态。

在 LP64 中，它与 `adler32_combine` 的契约及长度范围相同。
显式位宽在其他构建中有意义；本页不覆盖那些构建。

## get_crc_table

```c
const z_crc_t FAR * ZEXPORT get_crc_table(void);
```

返回库的逐字节 CRC 表。

**Domain.** 完整类型定义域；没有参数。效果为**纯计算**，返回指向库内存的指针；
它不读取表项。

**Pre:** 与选定构建一样，库的固定 CRC 表已经存在。
不需要设置调用。

**Post:** 返回非 NULL 指针，指向由 256 个 `z_crc_t` 表项组成的只读数组。
表项 `i` 是从零寄存器开始、对字节 `i` 执行的反射 CRC 寄存器更新，不包含公开校验和的取反步骤。
重复调用返回相同的指针。

**Effects:** 保持所有内存和所有权不变。表仍归库所有，在程序整个生命周期内存在。
调用者可以读取这 256 个表项，但不得通过该指针写入，也不得释放它。

`zlib.h` 将其列在已文档化 API 之外的函数中。它只公开字节表，不公开相邻表或交织表。
这里的 `z_crc_t` 是无符号 32 位类型。动态生成表不在本构建的范围内。

## crc32_z

```c
uLong ZEXPORT crc32_z(uLong crc, const unsigned char FAR *buf, z_size_t len);
```

用一段字节更新 CRC-32 校验和，或取得其初始值。

**Domain.** 受限定义域。`buf` 非 NULL 时，效果为**只读**，并读取库的固定 CRC 表。

**Pre:** `buf` 为 NULL，或者它以任意对齐方式指向 `len` 个可读字节。
对于校验和后置条件，`crc` 的低 32 位是 A 的 CRC-32。选定构建的固定 CRC 表已经存在。

**Post:** 对任意 `crc` 和 `len`，NULL `buf` 都返回 0，不读取缓冲区。
否则返回 A 后接 `buf[0..len-1]` 的 CRC-32。非 NULL 的空区间返回 `crc` 的低 32 位。

**Effects:** 保持所有内存和所有权不变。只读取给定字节区间和库的固定表。
空区间允许使用尾后一位指针。

新的校验和从 0 开始。函数内部执行 CRC 的取反；调用者不得对运行中的值自行取反。
对齐方式不改变契约。字访问模型的限制记录在[安全模型](../safety.md)和[信任基础](../trusted-base.md)中。

## crc32

```c
uLong ZEXPORT crc32(uLong crc, const unsigned char FAR *buf, uInt len);
```

用 32 位字节计数更新 CRC-32 校验和。

**Domain.** 受限定义域。`buf` 非 NULL 时，效果为**只读**，并读取库的固定表。

**Pre:** `buf` 为 NULL，或者它以任意对齐方式指向 `len` 个可读字节。
对于校验和后置条件，`crc` 的低 32 位是 A 的 CRC-32。固定 CRC 表已经存在。

**Post:** 精确返回 `crc32_z(crc, buf, len)` 的结果。
即使长度非零，NULL 也返回 0。非 NULL 的空区间保持传入校验和的低 32 位。
取反操作在内部处理。

**Effects:** 保持所有内存和所有权不变。只读取给定字节区间和库的固定表。
空区间允许使用尾后一位指针。

长度至多为 `2^32 - 1`。将更大的计数转换为 `uInt` 会在调用前截断；
对于更大的区间，应使用 `crc32_z` 或分成多次更新。

## crc32_combine_gen64

```c
uLong ZEXPORT crc32_combine_gen64(z_off64_t len2);
```

生成算子，以便对具有相同 B 长度的序列重复进行 CRC 合并。

**Domain.** 完整类型定义域。效果为**纯计算**，只读取库的固定表。

**Pre:** 无参数限制。选定构建的固定 CRC 表已经存在。
`len2` 可以是任意有符号 64 位值。

**Post:** 负长度返回 0。非负长度返回非零的 32 位算子，适用于 B 长度为 `len2` 时的
`crc32_combine_op`。长度为零时，返回 `0x80000000`。

**Effects:** 保持所有内存和所有权不变。不读取缓冲区或流状态。

该算子只取决于长度。保持它不变，便可对具有该 B 长度的任意 A、B 复用。
它是算子，不是校验和。

## crc32_combine_gen

```c
uLong ZEXPORT crc32_combine_gen(z_off_t len2);
```

用普通偏移类型生成 CRC 合并算子。

**Domain.** 完整类型定义域。效果为**纯计算**，只读取库的固定表。

**Pre:** 无参数限制。选定构建的固定 CRC 表已经存在。
`len2` 可以是任意可表示的有符号值。

**Post:** 返回与 `crc32_combine_gen64(len2)` 相同的算子。
负长度返回 0；零返回 `0x80000000`；正长度返回适用于该 B 长度的非零 32 位算子。

**Effects:** 保持所有内存和所有权不变。不读取缓冲区或流状态。

在 LP64 中，普通长度类型与显式 64 位长度类型的范围相同。

## crc32_combine_op

```c
uLong ZEXPORT crc32_combine_op(uLong crc1, uLong crc2, uLong op);
```

使用此前生成的算子，计算 A 后接 B 的 CRC-32。

**Domain.** 受限定义域。效果为**纯计算**。

**Pre:** 对于拼接结果，`crc1` 和 `crc2` 的低 32 位分别是 A、B 的 CRC-32，
各自从 0 开始。`op` 是针对 B 的长度，由 `crc32_combine_gen` 或
`crc32_combine_gen64` 生成且保持不变的结果。
独立的拒绝情形允许 `op == 0`，此时校验和参数可以任意。

**Post:** 返回 A 后接 B 的 CRC-32。若 `op == 0`，返回 0。
用于空 B 的算子保持 A 的校验和不变。

**Effects:** 保持所有内存和所有权不变。不读取缓冲区或流状态。
该算子可用于 B 长度相同的任意序列对。

对伪造算子，或针对错误 B 长度的算子，没有保证。
特别地，在 LP64 中，若 `op` 非零但低 32 位为零，执行可能不终止；
这不属于生成算子的契约范围。零是拒绝值，不是无歧义的错误码，因为有效 CRC 也可能为零。

## crc32_combine64

```c
uLong ZEXPORT crc32_combine64(uLong crc1, uLong crc2, z_off64_t len2);
```

不读取任何一个序列，计算 A 后接 B 的 CRC-32。

**Domain.** 受限定义域。效果为**纯计算**，只读取库的固定表。

**Pre:** 对于拼接结果，`crc1` 和 `crc2` 的低 32 位分别是独立计算的 A、B 的 CRC-32，
`len2` 是 B 的长度。固定 CRC 表已经存在。负长度纳入范围以进行拒绝，不限制校验和。

**Post:** 负长度返回 0。否则返回 A 后接 B 的 CRC-32。
空 B 的 CRC 为 0，并保持 A 的校验和不变。

**Effects:** 保持所有内存和所有权不变。不读取缓冲区或流状态。
生成的算子满足 `crc32_combine_op` 的输入要求。

在长度为零且校验和任意时，实现返回两者低 32 位的异或。
错误的长度没有拼接保证。零也可能是有效 CRC，因此负长度拒绝没有独立的错误码。

## crc32_combine

```c
uLong ZEXPORT crc32_combine(uLong crc1, uLong crc2, z_off_t len2);
```

用普通偏移类型计算 A 后接 B 的 CRC-32。

**Domain.** 受限定义域。效果为**纯计算**，只读取库的固定表。

**Pre:** 对于拼接结果，`crc1` 和 `crc2` 的低 32 位分别是 A、B 的 CRC-32，
各自从 0 开始；`len2` 是 B 的长度。固定 CRC 表已经存在。
负长度纳入范围以进行拒绝，不限制校验和。

**Post:** 返回与 `crc32_combine64(crc1, crc2, len2)` 相同的结果。
负长度返回 0。真实的空 B 保持 A 的校验和不变。

**Effects:** 保持所有内存和所有权不变。不读取缓冲区或流状态。

在 LP64 中，普通长度类型与显式 64 位长度类型的范围相同。
本页不包括动态生成表、硬件 CRC 钩子和生成表的可执行程序。
参见[构建与模型范围](../deviations.md)。

[返回 API 手册](README.md) · [契约约定](contracts.md)
