# 流式压缩

[API 手册](README.md) · [共享流规则](streams.md) · [流式解压](inflate-stream.md)

输入分批到达、输出空间有限，或需要选择包装、字典、刷新边界时，使用 `z_stream` 压缩器。初始化一次，使用连续的缓冲区调用 `deflate`，即使放弃压缩也要结束流。单个缓冲区的操作见 [compress 和 compress2](utility.md#compress2_z)。

| 任务 | 条目 |
| --- | --- |
| 开始或复用 | [初始化](#deflateinit_)、[配置初始化](#deflateinit2_)、[重置](#deflatereset)、[保留历史的重置](#deflateresetkeep) |
| 提供元数据或历史 | [字典](#deflatesetdictionary)、[读取历史](#deflategetdictionary)、[gzip 头](#deflatesetheader) |
| 压缩与输出大小 | [Deflate](#deflate)、[上界](#deflatebound_z)、[待输出数据](#deflatepending)、[最近刷新位数](#deflateused) |
| 调整或分支 | [参数](#deflateparams)、[调优](#deflatetune)、[位预置](#deflateprime)、[复制](#deflatecopy) |
| 释放存储 | [结束](#deflateend) |

这些聚焦契约遵循固定版本的 `deflate.c`、已应用补丁和 `zlib.h`，采用默认 LP64 Linux 构建。源代码解读仍**待确认（to confirm）**，需要证明。它们不改变范围更广的[已登记公开目标](../../checking/goals.md)。定义域/影响标签见[契约约定](contracts.md)，证明状态和剩余工作见[进度](../../progress.md)。

## 共享约定

在每条所述 Pre 下，都要求执行无运行时故障地终止，并满足所述 Post。调用若保留有效流，就保持其表示不变量。

- **有效流：** 可写的 `z_stream`，其压缩器状态由成功初始化或复制建立，经过合法调用保持，且尚未结束。调用者不改变其内部状态或分配器字段。同一个流的调用按顺序执行。
- **缓冲区：** 输入覆盖 `avail_in` 个可读字节；输出覆盖 `avail_out` 个可写字节。它们彼此不重叠，也不与流或流拥有的状态重叠。非 NULL 标量结果指向可写单元，与其他结果及流内存分离。这些分离条件是聚焦契约的显式假设；见 [safety.md](../safety.md)。
- **分配器：** 使用默认分配/释放函数对，或在初始化前将两个字段都置为 NULL。任意一次分配尝试都可能失败。自定义分配器回调不在本页范围内。
- **帧性质与所有权：** 调用只改变自己的流、其拥有的状态和所述输出区域。调用者输入只读。调用者缓冲区和头部记录仍归调用者所有。只有初始化和复制会分配；只有它们失败时的清理与 `deflateEnd` 会释放内存。其他调用保持流的分配集合。
- **头部生命周期：** 保留的 gzip 头及其可选字段在使用期间保持可读且不变。非 NULL 的 `name` 和 `comment` 以零终止；`extra` 覆盖所述长度。聚焦格式契约使用 `extra_len <= 65535`。
- **检查后的拒绝：** 除初始化和上界查询外，流检查失败会在正常操作之前返回 `Z_STREAM_ERROR`，不发生写入。`deflateCopy` 还会清空非 NULL 目标的状态。这种拒绝不修改查询输出单元。
- **受限定义域（Restricted domain）**指这些显式内存、生命周期和调用顺序条件，加上条目自身的 Pre。它不意味着接受每个可表示的指针或整数。错误概述覆盖可读、可检查的状态，不覆盖任意无效地址。

## deflateInit_

```c
int ZEXPORT deflateInit_(z_streamp strm, int level, const char *version, int stream_size);
```

使用默认 zlib 包装和压缩设置启动压缩器。

**定义域（Domain）：** 受限定义域。**影响（Effect）：** 分配并初始化。

**前置条件（Pre）：** `strm` 可写，且不拥有有效压缩器状态。其分配器字段按上述约定初始化。`level` 为 -1 或 0..9。`version` 的首字节可读且与 `ZLIB_VERSION` 匹配，`stream_size == sizeof(z_stream)`。

**后置条件（Post）：** 满足 `deflateInit2_` 的契约，方法为 `Z_DEFLATED`，窗口为 15，`memLevel` 为 8，策略为 `Z_DEFAULT_STRATEGY`。级别 -1 选择 6。不消费输入，不写入输出。成功返回 `Z_OK`；内存错误返回 `Z_MEM_ERROR` 并完成全部清理。

**聚焦范围之外：** 适用与 `deflateInit2_` 相同的版本和参数拒绝。`deflateInit` 宏提供版本和结构大小。

## deflateInit2_

```c
int ZEXPORT deflateInit2_(z_streamp strm, int level, int method, int windowBits,
                           int memLevel, int strategy, const char *version, int stream_size);
```

选择包装和压缩设置，启动压缩器。

**定义域（Domain）：** 受限定义域。**影响（Effect）：** 分配并初始化。

**前置条件（Pre）：** 满足 `deflateInit_` 的流和版本条件。参数为：`level` 为 -1 或 0..9；`method == Z_DEFLATED`；`memLevel` 为 1..9；`strategy` 为 0..4；zlib 的 `windowBits` 为 8..15，raw 为 -15..-9，gzip 为 25..31。

**后置条件（Post）：** `Z_OK` 建立有效流，拥有五项分配和所选设置。zlib 窗口请求 8 变为 9。总计数为零，`msg` 为 NULL，`data_type` 为 `Z_UNKNOWN`，raw/zlib 的 `adler` 为 1，gzip 的为 0。I/O 指针和可用计数不变；不消费或输出字节。调用者用 `deflateEnd` 释放状态。

`Z_MEM_ERROR` 不保留任何新分配的有效块。如果状态分配失败，`state` 保持入口值。如果后续分配失败，`state` 变为 NULL，`msg` 报告内存不足。状态分配成功后，全部四项缓冲区分配都会被尝试，然后才进行失败清理。

**聚焦范围之外：** 版本首字节为 NULL/不匹配，或结构大小错误时，返回 `Z_VERSION_ERROR`，不改变流。版本兼容且 `strm` 为 NULL 时，返回 `Z_STREAM_ERROR`。其他超出可接受范围的标量参数在分配前返回 `Z_STREAM_ERROR`，此前会清空 `msg`，并按需安装默认分配器字段。安装默认分配器会清空 `opaque`。未改变的公开初始化目标仍要求这些拒绝行为。

## deflateSetDictionary

```c
int ZEXPORT deflateSetDictionary(z_streamp strm, const Bytef *dictionary, uInt dictLength);
```

将预置字节载入压缩历史，不把它们作为输入数据输出。

**定义域（Domain）：** 受限定义域。**影响（Effect）：** 更新历史和字典校验和。

**前置条件（Pre）：** 有效 raw 或 zlib 流，紧接初始化或 `deflateReset`，在第一次 `deflate` 和第一次字典调用之前。`dictionary` 非 NULL，覆盖 `dictLength` 个可读字节，且与窗口分离。

**后置条件（Post）：** 返回 `Z_OK`。历史保留字典的可用后缀，最多一个窗口。zlib 的字典校验和覆盖整个给定字典。原 `next_in` 和 `avail_in` 被恢复；`total_in` 增加 `min(dictLength, window size)`。不交付压缩输出，也不分配。需要字典时，必须向解码器提供相同的预置字典。

**聚焦范围之外：** gzip、NULL 字典、已离开初始状态的 zlib、非零向前查看量，或不在已完成块边界的 raw 输入，均返回 `Z_STREAM_ERROR`，不发生变化。合法边界处的 raw 替换，以及开始前多次调用 zlib 字典设置，仍在公开目标内。重复 zlib 调用会累积 Adler-32，而不是重新开始计算。

## deflateGetDictionary

```c
int ZEXPORT deflateGetDictionary(z_streamp strm, Bytef *dictionary, uInt *dictLength);
```

读取当前压缩历史，包括已接受的向前查看数据。

**定义域（Domain）：** 受限定义域。**影响（Effect）：** 可带输出缓冲区的查询。

**前置条件（Pre）：** 有效流。`dictionary` 为 NULL，或可写一个窗口且与窗口分离；`dictLength` 为 NULL，或有效标量输出单元。

**后置条件（Post）：** 返回 `Z_OK`。设有效状态中的 `n = min(strstart + lookahead, window size)`。非 NULL 的 `dictionary` 按顺序接收该窗口区域的最后 `n` 个字节；非 NULL 的 `dictLength` 接收 `n`。两种结果均可独立省略。流不变。历史不一定包含此前所有已提供输入中的完整一个窗口。

## deflateResetKeep

```c
int ZEXPORT deflateResetKeep(z_streamp strm);
```

重新开始输出和进度计数，同时保留压缩历史。

**定义域（Domain）：** 受限定义域。**影响（Effect）：** 重置，保留历史和分配。

**前置条件（Pre）：** 处于任意阶段的有效流。这是未公开文档化的入口；如果下一个压缩流必须从空历史开始，使用 `deflateReset`。

**后置条件（Post）：** 返回 `Z_OK`。总计数变为零，`msg` 变为 NULL，`data_type` 变为 `Z_UNKNOWN`。待输出数据、尚未完成处理的向前查看数据，以及位/块进度被丢弃；包装输出重新开始，raw/zlib 的 `adler` 变为 1，gzip 的变为 0。自定义 gzip 头指针清空。级别、策略、调优、窗口和哈希历史保留。I/O 指针和可用计数不变。不分配或释放。

后续压缩器调用可以引用重置前的历史。因此，仅进行这种重置不保证所得流可以用空字典解码。

## deflateReset

```c
int ZEXPORT deflateReset(z_streamp strm);
```

复用流，以空历史开始新的压缩。

**定义域（Domain）：** 受限定义域。**影响（Effect）：** 重置，保留分配和配置。

**前置条件（Pre）：** 任意阶段的有效流，包括 `Z_STREAM_END` 之后。

**后置条件（Post）：** 返回 `Z_OK`。完成 `deflateResetKeep` 的计数、包装和待输出数据重置，且历史在逻辑上为空。此前的字典被遗忘；调优恢复为当前级别的默认值。保留 `deflateParams` 最后选择的级别和策略，以及包装、窗口、内存设置。gzip 头被遗忘。I/O 指针和可用计数不变。不分配或释放。已经接受但尚未处理完的输入，以及尚未交付的输出被丢弃。

## deflateSetHeader

```c
int ZEXPORT deflateSetHeader(z_streamp strm, gz_headerp head);
```

选择下一个 gzip 流的头部。

**定义域（Domain）：** 受限定义域。**影响（Effect）：** 保留调用者拥有的头部指针。

**前置条件（Pre）：** 有效 gzip 流，在初始化或重置之后、第一次 `deflate` 之前。`head` 为 NULL 时使用默认值，否则满足共享头部条件。

**后置条件（Post）：** 返回 `Z_OK` 并保留 `head`；此时尚不复制或输出头部字节。后续 `deflate` 写入请求的 text 标志、时间、OS、可选 extra/name/comment，以及可选头部 CRC。压缩设置决定额外标志字节。调用者保持记录和字段有效，直到头部输出完成。两种重置都会清空该指针。不分配，也不转移所有权。

**聚焦范围之外：** 非 gzip 或流检查失败时，返回 `Z_STREAM_ERROR`，不发生变化。gzip 接受较晚的登记，但不会重写已经输出的头部字节；公开指针存储目标包括这一情况。

## deflatePending

```c
int ZEXPORT deflatePending(z_streamp strm, unsigned *pending, int *bits);
```

查询压缩器内部等待输出的数据。

**定义域（Domain）：** 受限定义域。**影响（Effect）：** 可带标量结果的查询。

**前置条件（Pre）：** 有效流；每个结果为 NULL，或有效且独立的输出单元。

**后置条件（Post）：** 返回 `Z_OK`。若请求相应结果，`pending` 接收尚未交付的整字节数，`bits` 接收剩余位数（合法压缩历史下为 0..7）。流及其缓冲区不变。被省略的结果不写入。

若表示出的待输出计数超出 `unsigned`，所请求的字节计数饱和，并返回 `Z_BUF_ERROR`；若请求了位数结果，仍会写入。虽然正常默认构建的缓冲区更小，公开查询目标仍包括这种数值拒绝。

## deflateUsed

```c
int ZEXPORT deflateUsed(z_streamp strm, int *bits);
```

查询最近一次字节边界刷新中，最后一个字节的位使用量。

**定义域（Domain）：** 受限定义域。**影响（Effect）：** 可带标量结果的查询。

**前置条件（Pre）：** 有效流；`bits` 为 NULL，或有效输出单元。

**后置条件（Post）：** 返回 `Z_OK`。若请求结果，存入已保存的位使用计数：字节边界刷新后为 1..8；如果自初始化/重置以来没有发生这种刷新，则为 0。流不变。该保存计数不同于 `deflatePending` 返回的当前待输出位数。

公开目标对每个通过检查的状态返回存储值，不假设任意表示状态都满足正常历史的范围。

## deflatePrime

```c
int ZEXPORT deflatePrime(z_streamp strm, int bits, int value);
```

在 raw 压缩输出前添加调用者提供的位片段。

**定义域（Domain）：** 受限定义域。**影响（Effect）：** 将位追加到待输出数据。

**前置条件（Pre）：** 有效 raw 流，在初始化或 `deflateReset` 后第一次 `deflate` 之前；`bits` 为 0..16，`value` 为任意 `int`。调用者解释后续压缩流时需计入这些前缀位。

**后置条件（Post）：** `Z_OK` 将 `value` 的低 `bits` 位按最低有效位优先的顺序，追加到逻辑待输出位序列。完整字节加入待输出数据，缓冲中剩余少于 8 位。不向 `next_out` 交付字节；不分配。待输出缓冲区空间不足时，`Z_BUF_ERROR` 不插入任何位。发生该拒绝前，可以在所属缓冲区内部紧缩已有待输出字节。

**聚焦范围之外：** 计数不在 0..16 时，在紧缩前返回 `Z_BUF_ERROR`；流检查失败返回 `Z_STREAM_ERROR`。实现不检查包装或首次调用时机。公开目标覆盖这些情况下精确的待输出位影响，但不保证任意插入片段都保持普通流的有效性。

## deflateParams

```c
int ZEXPORT deflateParams(z_streamp strm, int level, int strategy);
```

更改级别和策略，必要时先完成旧块。

**定义域（Domain）：** 受限定义域。**影响（Effect）：** 更新设置；可以消费输入并输出数据。

**前置条件（Pre）：** 有效且尚未开始完成操作的流，流缓冲区和任何正在使用的头部均有效；`level` 为 -1 或 0..9，`strategy` 为 0..4。要选择精确输入边界，持续完成 `deflate(Z_BLOCK)`，直到 `avail_out` 非零，并在此次调用前不提供新输入。

**后置条件（Post）：** `Z_OK` 安装请求的设置（级别 -1 表示 6）。更改级别会恢复该级别的标准调优值。必要的块刷新使用旧设置，可能消费部分输入并交付输出。I/O 指针、可用计数和总计数精确记录这些字节；未消费输入保持可用。

`Z_BUF_ERROR` 表示旧块尚未完成；级别和策略不变，但已发生的压缩推进和输出保留。提供更多输出空间后重试。两种结果都保留有效流及其分配集合。

**聚焦范围之外：** 无效级别/策略返回 `Z_STREAM_ERROR`，不发生变化。必要的块刷新也可能返回 `Z_STREAM_ERROR`，包括已经开始完成操作后的情况。

## deflateTune

```c
int ZEXPORT deflateTune(z_streamp strm, int good_length, int max_lazy, int nice_length, int max_chain);
```

设置供专家使用的四个匹配搜索调优值。

**定义域（Domain）：** 受限定义域（有效流）；覆盖所有 `int` 调优参数。

**影响（Effect）：** 更新调优字段。

**前置条件（Pre）：** 有效流。

**后置条件（Post）：** 返回 `Z_OK`。将 `good_length`、`max_lazy`、`max_chain` 转为无符号后存入，将 `nice_length` 作为有符号值存入。不消费输入、不交付输出、不分配。`deflateParams` 更改级别，或执行 `deflateReset`，会恢复标准调优。仅凭该设置器契约，不能证明所有调优选择下的后续压缩上界或安全性；C 建议 `max_lazy >= 3` 和 `max_chain >= 4`。

## deflateBound_z

```c
z_size_t ZEXPORT deflateBound_z(z_streamp strm, z_size_t sourceLen);
```

根据流当前的配置和包装计算大小上界。

**定义域（Domain）：** 受限定义域（有效流和可读的保留头部）；包括每个 `z_size_t sourceLen`。**影响（Effect）：** 查询。

**前置条件（Pre）：** 有效流，满足共享头部条件。对于下述输出容量保证，应在初始化及任何字典/头部设置后、压缩前调用。保持配置、头部和字典不变；使用标准调优，不插入预置位。

**后置条件（Post）：** 堆不变。数值目标是下述数学值，在 `SIZE_MAX` 处饱和，其中 `n = sourceLen`，`w` 为完整包装大小：

- 窗口 15 且内存级别 8：`n + floor(n/4096) + floor(n/16384) + floor(n/33554432) + 7 + w`。
- 否则，若窗口位数不超过哈希位数且级别非零：`n + floor(n/8) + floor(n/256) + floor(n/512) + 4 + w`。
- 否则：`n + floor(n/32) + floor(n/128) + floor(n/2048) + 7 + w`。

raw 的 `w` 为 0；zlib 为 6，存在预置历史时再加 4；gzip 为 18，再加可选 extra 字段（包括两个长度字节）、以零终止的名称/注释和头部 CRC。

**输出容量：** 与数值公式分开，对于大小可表示且足够的缓冲区，如果输入和输出大小能放入 `avail_in` 和 `avail_out`，向一次 `deflate(Z_FINISH)` 提供全部 `n` 个字节及至少为上界的输出空间，必须返回 `Z_STREAM_END`。在 `Z_FINISH` 前仅使用 `Z_NO_FLUSH` 的干净调用安排具有总输出上界。其他刷新安排可能超出此上界。饱和结果不承诺存在这样大小的可寻址缓冲区。

**聚焦范围之外：** NULL 或可安全检查的无效流，得到上述固定/存储公式中的较大值，再加 18，并进行饱和。没有错误码。公开数值目标仍包括每种可读的 gzip 头部长度，包括聚焦的 16-bit extra 字段范围之外的长度；本页不移除这一义务。

## deflateBound

```c
uLong ZEXPORT deflateBound(z_streamp strm, uLong sourceLen);
```

返回压缩上界的 `uLong` 形式。

**定义域（Domain）：** 与 `deflateBound_z` 相同的受限定义域；包括每个 `uLong sourceLen`。

**影响（Effect）：** 查询。

**前置条件（Pre）：** 适用 `deflateBound_z` 的条件。

**后置条件（Post）：** 如果数值结果能由 `uLong` 表示，则返回该结果，否则返回 `ULONG_MAX`。默认 LP64 目标中两种类型都是 64 位，结果相同。流不变。输出是否足够，仍要求 `deflateBound_z` 单独规定的调用安排和容量条件，不能只由数值相等推出。

## deflate

```c
int ZEXPORT deflate(z_streamp strm, int flush);
```

接受输入，交付有效压缩流的一部分或全部。

**定义域（Domain）：** 受限定义域。**影响（Effect）：** 消费输入、输出数据并更新进度。

**前置条件（Pre）：** 有效流，缓冲区和任何正在使用的头部均有效。`next_out` 非 NULL，`avail_out > 0`；仅输入为零时 `next_in` 可为 NULL。`flush` 为 `Z_NO_FLUSH`、`Z_PARTIAL_FLUSH`、`Z_SYNC_FLUSH`、`Z_FULL_FLUSH`、`Z_FINISH` 或 `Z_BLOCK`。刷新期间输出填满时，以相同刷新请求和更多空间继续。开始完成操作后，不提供新输入，只以 `Z_FINISH` 继续。普通格式有效性要求从初始化/`deflateReset`（或该历史的副本）开始，使用合法字典/头部设置、标准调优，且不进行任意位预置。

**后置条件（Post）：** 接受 `used <= old avail_in` 个字节，交付 `made <= old avail_out` 个字节。指针按相应数量推进，可用计数按相应数量减少，总计数按相应数量增加并遵循无符号回绕。输入不变；已交付前缀以外的输出不变。输出填满时可能仍有输入未消费。不分配或释放。

跨调用交付的字节构成已接受输入的一种有效编码的前缀，使用所选包装、设置和预置字典。完成的输出可解码为该输入。这里规定有效输出，而非唯一的压缩字节序列。头部输出之后，`adler` 用 Adler-32 跟踪 zlib 已接受输入，用 CRC-32 跟踪 gzip 已接受输入；raw 没有输入校验和。

`Z_OK` 表示可能需要继续。`Z_STREAM_END` 只在 `Z_FINISH` 下发生，且所有给定输入及所有压缩输出（包括尾部）都已交付。有效状态仍被拥有，直到 `deflateEnd` 释放，或通过 `deflateReset` 复用。

请求的刷新完全交付后，`Z_BLOCK` 完成一个块但不填充到字节边界；`Z_PARTIAL_FLUSH` 添加空固定块；`Z_SYNC_FLUSH` 使此前全部输入可供解码器解码，并以对齐的空存储块结尾。`Z_FULL_FLUSH` 还重置匹配历史：后续块不引用该次已完成刷新之前的数据。若要在那里重新启动 raw 解码器，需要保留精确边界，并先交付完整刷新标记。`Z_FINISH` 关闭最终块并写入包装尾部。

**错误（Errors）：** `Z_BUF_ERROR` 覆盖输出空间为零、无输入且无更强刷新请求因而无法推进，或最终块处理已开始后又提供输入。它保留有效流；应按需提供空间/输入。`Z_STREAM_ERROR` 覆盖流检查失败、无效刷新（包括 `Z_TREES`）、无效 NULL I/O 组合，或完成操作开始后请求非完成刷新。初始参数拒绝不消费输入、不交付输出。开始完成操作后，因新输入而产生的较晚 `Z_BUF_ERROR`，可能先交付旧的待输出数据；不接受新输入。`msg` 和记录的刷新请求可能改变。未改变的公开目标包括所有有符号刷新值及这些拒绝。

## deflateEnd

```c
int ZEXPORT deflateEnd(z_streamp strm);
```

释放压缩器，丢弃任何未完成工作。

**定义域（Domain）：** 受限定义域。**影响（Effect）：** 释放拥有的状态。

**前置条件（Pre）：** 任意阶段的有效流，默认释放例程保持完整。

**后置条件（Post）：** 对全部五项拥有的分配恰好释放一次，并将 `state` 置为 NULL。调用者输入/输出及头部存储不变，仍归调用者所有。保存的状态为 busy 时返回 `Z_DATA_ERROR`，否则返回 `Z_OK`。两种结果都释放全部资源：`Z_DATA_ERROR` 报告未完成压缩，不表示清理失败。重新初始化前，后续压缩调用均无效。

**聚焦范围之外：** 流检查失败，包括第二次结束，返回 `Z_STREAM_ERROR`，不释放任何内容。返回状态取决于内部压缩阶段，而不只是是否已交付每个产生的字节。

## deflateCopy

```c
int ZEXPORT deflateCopy(z_streamp dest, z_streamp source);
```

创建压缩进度相同、彼此独立的压缩器。

**定义域（Domain）：** 受限定义域。**影响（Effect）：** 分配并复制拥有的状态。

**前置条件（Pre）：** `source` 有效。`dest` 是另一个可写 `z_stream`，不拥有状态，且与源的内存分离。源缓冲区和任何保留的头部满足生命周期要求。

**后置条件（Post）：** `Z_OK` 使 `dest` 获得五项新拥有的分配，包含等价的压缩状态；源不变。复制的流字段包括总计数、分配器字段、I/O 指针和保留的头部指针。内部拥有的指针被重定位到新分配。两个流各自需要 `deflateEnd`，可独立继续。复制的调用者 I/O 指针起初指向相同缓冲区；继续两个流前应分配独立输出空间。头部仍是共享的调用者自有存储。

`Z_MEM_ERROR` 释放每项新分配、清空 `dest->state`，并保持其他目标字段和源不变。没有新的有效状态需要释放。

**聚焦范围之外：** NULL 目标返回 `Z_STREAM_ERROR`；源检查失败还会清空非 NULL 目标的状态。公开目标显式假设两个流不同。这里排除自复制和覆盖已有效目标，不为它们提供无泄漏契约。

[返回 API 手册](README.md) · [契约约定](contracts.md)
