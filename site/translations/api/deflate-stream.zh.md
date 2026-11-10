<!--
source: docs/api/deflate-stream.md
source-sha256: 23ae51a2d7244546657af77bed314e91830caf2dfecd81ab139ebed3290ec0e9
-->

# 流式压缩

[API 手册](README.md) · [流的共同规则](streams.md) · [流式解压](inflate-stream.md)

当输入分批到达、输出空间有限，或者需要选择封装、字典或刷新边界时，可以使用 `z_stream` 压缩器。
初始化一次，用后续缓冲区反复调用 `deflate`，最后结束流，即使中途放弃压缩也要结束。
单个缓冲区的操作见 [compress 和 compress2](utility.md#compress2_z)。

| 任务 | 入口 |
| --- | --- |
| 创建或复用 | [初始化](#deflateinit_)、[带配置初始化](#deflateinit2_)、[重置](#deflatereset)、[保留历史的重置](#deflateresetkeep) |
| 提供元数据或历史 | [字典](#deflatesetdictionary)、[读取历史](#deflategetdictionary)、[gzip 头部](#deflatesetheader) |
| 压缩与确定输出大小 | [Deflate](#deflate)、[上界](#deflatebound_z)、[待交付输出](#deflatepending)、[最后一次刷新的位数](#deflateused) |
| 调整或分支 | [参数](#deflateparams)、[调优](#deflatetune)、[预置位](#deflateprime)、[复制](#deflatecopy) |
| 释放存储 | [结束](#deflateend) |

这些聚焦契约遵循固定版本的 `deflate.c`、已应用的补丁和 `zlib.h`，范围为默认 LP64 Linux 构建。
对源码的解读仍需由证明确认，标记为 **to confirm**。它们不改变范围更广的
[已登记公开目标](../checking/goals.md)。定义域和效果标签见[契约约定](contracts.md)，
证明状态与剩余工作见 [overview](../overview.md)。

## 共同约定

在每项给定的 Pre 下，都要求执行终止、不产生运行时故障，并满足所述 Post。
保留活流的调用必须保持其表示不变量。

- **活流：** 可写的 `z_stream`，其压缩器状态由成功的初始化或复制建立，经合法调用保持，且尚未结束。
  调用者不改动内部状态或分配器字段。同一流上的调用按顺序进行。
- **缓冲区：** 输入覆盖 `avail_in` 个可读字节；输出覆盖 `avail_out` 个可写字节。
  两者互不重叠，也不与流或流拥有的状态重叠。非 NULL 的标量结果指针指向一个可写单元，
  该单元与其他结果及流内存分离。这些分离条件是明确的聚焦假设，见 [safety.md](../safety.md)。
- **分配器：** 使用默认的分配与释放函数对，或者在初始化前将这两个字段都设为 NULL。
  任何一次分配都可能失败。自定义分配器回调不在本页范围内。
- **Frame 与所有权：** 调用只改动其流、流拥有的状态和所述输出区域。调用者输入只读。
  调用者的缓冲区和头部记录仍归调用者所有。只有初始化和复制会分配；只有它们的失败清理
  和 `deflateEnd` 会释放内存。其他调用保持流的分配集合不变。
- **头部生命周期：** 保留的 gzip 头部及其可选字段在使用期间保持可读且不变。
  非 NULL 的 `name` 和 `comment` 含有终止零；`extra` 覆盖其给出的长度。
  聚焦格式契约使用 `extra_len <= 65535`。
- **受检查的拒绝：** 除初始化和上界查询外，流检查失败会在正常操作前返回 `Z_STREAM_ERROR`，
  不发生写入。`deflateCopy` 还会清除非 NULL 目标的状态。查询输出单元在此拒绝路径上不被改动。
- **受限定义域（Restricted domain）** 指这些明确的内存、生命周期和调用顺序条件，以及该入口的 Pre。
  它不表示接受每个可表示的指针或整数。错误概要覆盖可读且受检查的状态，不覆盖任意无效地址。

## deflateInit_

```c
int ZEXPORT deflateInit_(z_streamp strm, int level, const char *version, int stream_size);
```

以默认 zlib 封装和压缩设置创建压缩器。

**Domain:** 受限定义域。**Effect:** 分配并初始化。

**Pre:** `strm` 可写，且不拥有活的压缩器状态。分配器字段已按上述约定初始化。
`level` 为 -1 或 0..9。`version` 的首字节可读且与 `ZLIB_VERSION` 匹配，
并且 `stream_size == sizeof(z_stream)`。

**Post:** 满足 `deflateInit2_` 的契约，其中 method 为 `Z_DEFLATED`、窗口为 15、
`memLevel` 为 8、策略为 `Z_DEFAULT_STRATEGY`。级别 -1 选择 6。
不消耗输入，也不写输出。成功返回 `Z_OK`；失败返回 `Z_MEM_ERROR` 并完成全部清理。

**聚焦范围之外：** 适用与 `deflateInit2_` 相同的版本和参数拒绝行为。
`deflateInit` 宏提供版本和结构体大小。

## deflateInit2_

```c
int ZEXPORT deflateInit2_(z_streamp strm, int level, int method, int windowBits,
                           int memLevel, int strategy, const char *version, int stream_size);
```

以选定的封装和压缩设置创建压缩器。

**Domain:** 受限定义域。**Effect:** 分配并初始化。

**Pre:** 满足 `deflateInit_` 的流和版本条件。参数范围如下：
`level` 为 -1 或 0..9；`method == Z_DEFLATED`；`memLevel` 为 1..9；`strategy` 为 0..4；
zlib 的 `windowBits` 为 8..15，raw 为 -15..-9，gzip 为 25..31。

**Post:** `Z_OK` 建立一个活流，它拥有五项分配并采用选定设置。
zlib 的窗口请求 8 被改为 9。总计数为零，`msg` 为 NULL，`data_type` 为 `Z_UNKNOWN`，
raw/zlib 的 `adler` 为 1，gzip 的为 0。
I/O 指针和可用数量不变；不消耗或发出任何字节。调用者用 `deflateEnd` 释放状态。

`Z_MEM_ERROR` 不留下任何本次新分配的活块。若状态分配失败，`state` 保留入口值。
若后续分配失败，`state` 变为 NULL，`msg` 报告内存不足。
只要状态分配成功，就会先尝试全部四个缓冲区分配，再进行失败清理。

**聚焦范围之外：** NULL 的版本指针、版本首字节不匹配或结构体大小错误，会返回
`Z_VERSION_ERROR`，不改动流。版本兼容而 `strm` 为 NULL 时，返回 `Z_STREAM_ERROR`。
其他标量参数超出接受范围时，在分配前返回 `Z_STREAM_ERROR`；在此之前会清除 `msg`，
并在需要时安装默认分配器字段。安装默认分配器会清除 `opaque`。
未改变的公开初始化目标要求覆盖这些拒绝。

## deflateSetDictionary

```c
int ZEXPORT deflateSetDictionary(z_streamp strm, const Bytef *dictionary, uInt dictLength);
```

将预设字节载入为压缩历史，不把它们作为输入数据输出。

**Domain:** 受限定义域。**Effect:** 更新历史和字典校验值。

**Pre:** 活的 raw 或 zlib 流，紧接初始化或 `deflateReset` 之后，且尚未进行第一次
`deflate` 或字典调用。`dictionary` 非 NULL，覆盖 `dictLength` 个可读字节，并与窗口分离。

**Post:** 返回 `Z_OK`。历史保留字典的一个可用后缀，最多一个窗口。
zlib 的字典校验值覆盖整个给定字典。原来的 `next_in` 和 `avail_in` 被恢复；
`total_in` 增加 `min(dictLength, window size)`。不交付压缩输出，也不分配。
解码器在需要时必须收到同一个预设字典。

**聚焦范围之外：** gzip、NULL 字典、已离开初始状态的 zlib 流、非零 lookahead，
或 raw 输入不处于已完成的块边界时，返回 `Z_STREAM_ERROR`，不发生改动。
合法边界上的 raw 字典替换，以及开始前重复进行的 zlib 字典调用，仍保留在公开目标中。
重复的 zlib 调用会累积 Adler-32，而不是重新开始计算。

## deflateGetDictionary

```c
int ZEXPORT deflateGetDictionary(z_streamp strm, Bytef *dictionary, uInt *dictLength);
```

读取当前压缩历史，包括已经接受的 lookahead。

**Domain:** 受限定义域。**Effect:** 带可选输出缓冲区的查询。

**Pre:** 活流。`dictionary` 为 NULL，或可写一个窗口并与窗口分离；
`dictLength` 为 NULL 或有效的标量输出单元。

**Post:** 返回 `Z_OK`。在活状态中令 `n = min(strstart + lookahead, window size)`。
非 NULL 的 `dictionary` 按顺序接收该窗口区域最后的 `n` 个字节；非 NULL 的 `dictLength`
接收 `n`。两项结果可分别独立省略。流不变。历史不一定包含此前给出的全部输入中的一整窗口。

## deflateResetKeep

```c
int ZEXPORT deflateResetKeep(z_streamp strm);
```

重新开始输出和进度计数，同时保留压缩历史。

**Domain:** 受限定义域。**Effect:** 重置，同时保留历史和分配。

**Pre:** 任意阶段的活流。这是未记入公开文档的入口；若下一条压缩流必须从空历史开始，
应使用 `deflateReset`。

**Post:** 返回 `Z_OK`。总计数变为零，`msg` 变为 NULL，`data_type` 变为 `Z_UNKNOWN`。
丢弃待交付输出、未完成的 lookahead 和位/块进度；重新开始发出封装，
raw/zlib 的 `adler` 变为 1，gzip 的变为 0。自定义 gzip 头部指针被清除。
保留级别、策略、调优、窗口和哈希历史。I/O 指针和可用数量不变。不分配或释放。

后续压缩器调用可以引用重置前的历史。因此，仅进行这次重置，不能保证得到一条可用空字典解码的流。

## deflateReset

```c
int ZEXPORT deflateReset(z_streamp strm);
```

以空历史复用流，开始新的压缩。

**Domain:** 受限定义域。**Effect:** 重置，同时保留分配和配置。

**Pre:** 任意阶段的活流，包括已经返回 `Z_STREAM_END` 的流。

**Post:** 返回 `Z_OK`。执行 `deflateResetKeep` 所述的计数、封装和待交付输出重置，
并使历史在逻辑上为空。忘记先前的字典；调优恢复为当前级别的默认值。
保留 `deflateParams` 最后选定的级别和策略，以及封装、窗口和内存设置。
忘记 gzip 头部。I/O 指针和可用数量不变。不分配或释放。
已经接受但未完成的输入，以及尚未交付的输出，均被丢弃。

## deflateSetHeader

```c
int ZEXPORT deflateSetHeader(z_streamp strm, gz_headerp head);
```

选择下一条 gzip 流的头部。

**Domain:** 受限定义域。**Effect:** 保留一个归调用者所有的头部指针。

**Pre:** 活的 gzip 流，在初始化或重置之后、第一次 `deflate` 之前。
`head` 为 NULL 时采用默认值，否则满足共同的头部条件。

**Post:** 返回 `Z_OK` 并保留 `head`；此时还不复制或输出头部字节。
后续 `deflate` 写出请求的 text 标志、time、OS、可选 extra/name/comment 和可选头部 CRC。
压缩设置决定位于额外标志字节中的内容。调用者保持该记录及其字段存活，直到头部发出完毕。
两种重置都会清除指针。不分配，也不转移所有权。

**聚焦范围之外：** 非 gzip 或流检查失败时返回 `Z_STREAM_ERROR`，不发生改动。
gzip 接受较晚的注册，但不会重写已发出的头部字节；公开的指针存储目标包含这种情况。

## deflatePending

```c
int ZEXPORT deflatePending(z_streamp strm, unsigned *pending, int *bits);
```

报告压缩器内部等待交付的输出。

**Domain:** 受限定义域。**Effect:** 带可选标量结果的查询。

**Pre:** 活流；每个结果指针为 NULL，或指向有效且分离的输出单元。

**Post:** 返回 `Z_OK`。若请求，`pending` 接收尚未交付的整字节数，`bits` 接收剩余位数
（合法压缩历史下为 0..7）。流及其缓冲区不变。省略的结果不被写入。

若表示出的待交付数量超过 `unsigned`，请求的字节数会饱和，返回 `Z_BUF_ERROR`；
请求的位数结果仍然写入。公开查询目标包含此数值拒绝，即使正常默认构建的缓冲区更小。

## deflateUsed

```c
int ZEXPORT deflateUsed(z_streamp strm, int *bits);
```

报告最近一次字节边界刷新中，最后一个字节使用的位数。

**Domain:** 受限定义域。**Effect:** 带可选标量结果的查询。

**Pre:** 活流；`bits` 为 NULL 或有效输出单元。

**Post:** 返回 `Z_OK`。若请求，存入保存的位使用数：一次字节边界刷新后为 1..8；
若初始化/重置以来从未发生过这种刷新，则为 0。流不变。
这个保存的数量不同于 `deflatePending` 返回的当前待交付位数。

公开目标对每个通过检查的状态返回所存值，不假设任意表示状态都满足正常历史的数值范围。

## deflatePrime

```c
int ZEXPORT deflatePrime(z_streamp strm, int bits, int value);
```

在 raw 压缩输出前预置调用者给出的位片段。

**Domain:** 受限定义域。**Effect:** 向待交付输出追加位。

**Pre:** 活的 raw 流，在初始化或 `deflateReset` 后的第一次 `deflate` 之前；
`bits` 为 0..16，`value` 为任意 `int`。调用者在解释后续压缩流时负责计入这些前缀位。

**Post:** `Z_OK` 将 `value` 的低 `bits` 位按最低有效位先行的顺序追加到逻辑待交付位序列。
完整字节加入待交付输出，缓冲的剩余位少于 8。不向 `next_out` 交付字节，也不分配。
待交付缓冲区空间不足时，`Z_BUF_ERROR` 不插入任何位。
在这种拒绝发生前，已有待交付字节可能先在其自有缓冲区内被紧缩。

**聚焦范围之外：** 数量超出 0..16 时，在紧缩前返回 `Z_BUF_ERROR`；
流检查失败返回 `Z_STREAM_ERROR`。实现不检查封装或第一次调用的时机。
公开目标覆盖这些情况下的精确待交付位效果，但不保证任意插入片段都维持普通流的有效性。

## deflateParams

```c
int ZEXPORT deflateParams(z_streamp strm, int level, int strategy);
```

改变级别和策略，在需要时先完成旧块。

**Domain:** 受限定义域。**Effect:** 更新设置；可能消耗输入并发出输出。

**Pre:** 尚未开始结束处理的活流，具有有效流缓冲区和任何仍在使用的头部；
`level` 为 -1 或 0..9，`strategy` 为 0..4。
若要选择精确输入边界，应反复完成 `deflate(Z_BLOCK)`，直到 `avail_out` 非零，
并且在此调用前不提供新输入。

**Post:** `Z_OK` 安装请求的设置（级别 -1 表示 6）。改变级别会恢复该级别的标准调优值。
所需的块刷新使用旧设置，并可能消耗部分输入、交付输出。
I/O 指针、可用数量和总计数精确反映这些字节；未消耗输入仍然可用。

`Z_BUF_ERROR` 表示旧块尚不能完成；级别和策略保持不变，但已经取得的压缩进度和发出的输出保留。
提供更多输出空间后重试。两种结果都保持活流及其分配集合。

**聚焦范围之外：** 无效的级别/策略返回 `Z_STREAM_ERROR`，不发生改动。
所需的块刷新也可能返回 `Z_STREAM_ERROR`，包括结束处理已经开始的情况。

## deflateTune

```c
int ZEXPORT deflateTune(z_streamp strm, int good_length, int max_lazy, int nice_length, int max_chain);
```

设置四个供熟悉实现的使用者调整的匹配搜索值。

**Domain:** 受限定义域（活流）；覆盖所有 `int` 调优参数。

**Effect:** 更新调优字段。

**Pre:** 活流。

**Post:** 返回 `Z_OK`。将 `good_length`、`max_lazy` 和 `max_chain` 转为无符号后存储，
将 `nice_length` 作为有符号值存储。不消耗输入，不交付输出，也不分配。
`deflateParams` 改变级别，或执行 `deflateReset`，都会恢复标准调优。
单独这个设置器的契约不能建立每种调优选择下的后续压缩界或安全性；
C 推荐 `max_lazy >= 3` 和 `max_chain >= 4`。

## deflateBound_z

```c
z_size_t ZEXPORT deflateBound_z(z_streamp strm, z_size_t sourceLen);
```

利用流的当前配置和封装计算大小上界。

**Domain:** 受限定义域（活流及可读的保留头部）；包含每个 `z_size_t sourceLen`。
**Effect:** 查询。

**Pre:** 活流及共同头部条件。要获得下面的输出容量保证，应在初始化和任何字典/头部设置之后、
压缩之前调用。配置、头部和字典保持不变；使用标准调优，且不插入预置位。

**Post:** 堆不变。数值目标是以下数学值，在 `SIZE_MAX` 处饱和，其中 `n = sourceLen`，
`w` 为完整封装大小：

- 窗口为 15 且内存级别为 8：`n + floor(n/4096) + floor(n/16384) + floor(n/33554432) + 7 + w`。
- 否则，若窗口位数不大于哈希位数且级别非零：
  `n + floor(n/8) + floor(n/256) + floor(n/512) + 4 + w`。
- 否则：`n + floor(n/32) + floor(n/128) + floor(n/2048) + 7 + w`。

raw 的 `w` 为 0；zlib 的为 6，存在预设历史时再加 4；gzip 的为 18，再加上可选 extra 字段
（包括两个长度字节）、以零终止的 name/comment 和头部 CRC。

**输出容量：** 这与数值公式是独立的保证。对于可表示且足够的缓冲区，当输入与输出大小能装入
`avail_in` 和 `avail_out` 时，把全部 `n` 个字节交给一次 `deflate(Z_FINISH)`，并提供至少上界大小
的输出空间，必须返回 `Z_STREAM_END`。在 `Z_FINISH` 之前只使用 `Z_NO_FLUSH` 的干净调用安排，
具有总输出上界。其他刷新安排可能超过它。饱和结果不保证存在该大小的可寻址缓冲区。

**聚焦范围之外：** NULL 或可安全检查的无效流，得到上述 fixed/stored 两个公式中的较大值再加 18，
并执行饱和处理。没有错误码。公开数值目标仍然包含每个可读的 gzip 头部长度，
包括超出聚焦的 16 位 extra 字段范围的长度；本页没有移除这项义务。

## deflateBound

```c
uLong ZEXPORT deflateBound(z_streamp strm, uLong sourceLen);
```

返回压缩上界的 `uLong` 形式。

**Domain:** 与 `deflateBound_z` 一样为受限定义域；包含每个 `uLong sourceLen`。

**Effect:** 查询。

**Pre:** 适用 `deflateBound_z` 的条件。

**Post:** 若其数值结果能装入 `uLong`，就返回该结果，否则返回 `ULONG_MAX`。
在默认 LP64 目标上，两种类型都是 64 位，结果一致。流不变。
输出容量足够性需要 `deflateBound_z` 独立给出的调用安排和容量条件，不能仅从数值相等推出。

## deflate

```c
int ZEXPORT deflate(z_streamp strm, int flush);
```

接受输入，并交付有效压缩流的一部分或全部。

**Domain:** 受限定义域。**Effect:** 消耗输入，发出输出，更新进度。

**Pre:** 活流，具有有效缓冲区和任何仍在使用的头部。`next_out` 非 NULL，且 `avail_out > 0`；
`next_in` 只有在输入为零时才可为 NULL。`flush` 为 `Z_NO_FLUSH`、`Z_PARTIAL_FLUSH`、
`Z_SYNC_FLUSH`、`Z_FULL_FLUSH`、`Z_FINISH` 或 `Z_BLOCK`。
刷新过程中若输出填满，应提供更多空间，并继续使用相同的 flush。
结束处理开始后，不提供新输入，只继续使用 `Z_FINISH`。
要获得普通格式有效性，应从初始化/`deflateReset`（或该历史的副本）开始，
采用合法字典/头部设置、标准调优，并且不做任意预置位。

**Post:** 接受 `used <= old avail_in` 个字节，交付 `made <= old avail_out` 个字节。
指针相应前进，可用数量相应减少，总计数相应增加，并按无符号规则回绕。
输入不变；交付前缀之外的输出不变。输出填满时，可能还留有部分输入。不分配或释放。

跨调用交付的字节组成已接受输入的一个有效编码前缀，采用选定的封装、设置和预设字典。
完成后的输出解码得到该输入。这规定的是有效输出，而不是唯一的一串压缩字节。
`adler` 跟踪已接受输入：zlib 用 Adler-32，gzip 在发出头部后用 CRC-32；raw 没有输入校验值。

`Z_OK` 表示可能还需继续。`Z_STREAM_END` 只在 `Z_FINISH` 下发生，且所有给定输入和全部压缩输出
（包括尾部）均已交付。活状态继续归流所有，直到 `deflateEnd` 释放，或由 `deflateReset` 复用。

请求的刷新完全交付后，`Z_BLOCK` 完成一个块而不填充到字节边界；
`Z_PARTIAL_FLUSH` 添加一个空 fixed 块；`Z_SYNC_FLUSH` 使此前全部输入可供解码器取得，
并以一个对齐的空 stored 块结束。`Z_FULL_FLUSH` 还会重置匹配历史：后续块不再引用此次完成刷新之前的数据。
若要从这里重新开始 raw 解码器，必须保留精确边界，并先交付整个刷新标记。
`Z_FINISH` 关闭最终块并写出封装尾部。

**Errors:** `Z_BUF_ERROR` 覆盖以下情况：输出空间为零、没有输入且没有更强刷新请求时无法取得进展，
或最终块处理开始后又提供输入。它保持一个活流；按情况提供空间或输入。
`Z_STREAM_ERROR` 覆盖流检查失败、无效 flush（包括 `Z_TREES`）、无效 NULL I/O 组合，
或结束处理开始后使用非 finish 的 flush。初始参数拒绝不消耗输入或输出。
结束后提供新输入导致的较晚 `Z_BUF_ERROR`，可能先交付旧的待输出数据；不接受新输入。
`msg` 和记忆的 flush 可以改变。未改变的公开目标包含所有有符号 flush 值及这些拒绝。

## deflateEnd

```c
int ZEXPORT deflateEnd(z_streamp strm);
```

释放压缩器，丢弃任何未完成工作。

**Domain:** 受限定义域。**Effect:** 释放拥有的状态。

**Pre:** 任意阶段的活流，默认释放函数仍然完好。

**Post:** 恰好释放一次全部五项自有分配，并把 `state` 设为 NULL。
调用者输入/输出和头部存储不变，仍归调用者所有。
若保存的状态为 busy，返回 `Z_DATA_ERROR`，否则返回 `Z_OK`。
两种结果都会释放全部资源：`Z_DATA_ERROR` 报告的是压缩未完成，不是清理失败。
重新初始化之前，后续压缩调用均不合法。

**聚焦范围之外：** 流检查失败时，包括第二次 end，返回 `Z_STREAM_ERROR`，不释放任何东西。
返回状态取决于内部压缩阶段，而不只是每个已产生字节是否已交付。

## deflateCopy

```c
int ZEXPORT deflateCopy(z_streamp dest, z_streamp source);
```

创建压缩进度相同的独立压缩器。

**Domain:** 受限定义域。**Effect:** 分配并复制自有状态。

**Pre:** `source` 为活流。`dest` 是另一个可写的 `z_stream`，不拥有状态，并与源的内存分离。
源缓冲区及任何保留的头部满足各自的生命周期。

**Post:** `Z_OK` 使 `dest` 获得五项新自有分配，其中包含等价的压缩状态；源不变。
复制的流字段包括总计数、分配器字段、I/O 指针和保留的头部指针。
内部自有指针被重定位到新分配。两个流各自需要 `deflateEnd`，并且能独立继续。
复制后的调用者 I/O 指针最初指向相同缓冲区；同时继续两个流之前，应分别分配输出空间。
头部仍是共享的调用者自有存储。

`Z_MEM_ERROR` 释放每项新分配，清除 `dest->state`，其他目标字段和源不变。
没有新的活状态需要释放。

**聚焦范围之外：** NULL 目标返回 `Z_STREAM_ERROR`；源检查失败也会清除非 NULL 目标的状态。
公开目标明确假设两个流不同。这里排除自复制和覆盖已有活目标，不为它们给出无泄漏契约。

[返回 API 手册](README.md) · [契约约定](contracts.md)
