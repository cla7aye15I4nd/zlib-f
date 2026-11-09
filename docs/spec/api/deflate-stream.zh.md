<!-- source-sha256: b7ad6cd4708c4821c31d8fcb71af9f7cfdc17c1162ca059e4bdacd444ee2a1c5 -->

# 流式压缩

[API 手册](README.md) · [共享流规则](streams.md) · [流式解压](inflate-stream.md)

输入分批到达、输出空间有限，或需要选择封装、字典、刷新边界时，使用 `z_stream` 压缩器。封装是在 DEFLATE 压缩数据之外增加的头部、尾部和完整性信息；raw DEFLATE 则不带这些封装。初始化一次，使用连续的缓冲区调用 `deflate`，即使放弃压缩也要结束流。单个缓冲区的操作见 [compress 和 compress2](utility.md#compress2_z)。

| 任务 | 条目 |
| --- | --- |
| 开始或复用 | [初始化](#deflateinit_)、[配置初始化](#deflateinit2_)、[重置](#deflatereset)、[保留历史的重置](#deflateresetkeep) |
| 提供元数据或历史 | [字典](#deflatesetdictionary)、[读取历史](#deflategetdictionary)、[gzip 头](#deflatesetheader) |
| 压缩与输出大小 | [压缩](#deflate)、[上界](#deflatebound_z)、[待输出数据](#deflatepending)、[最近刷新位数](#deflateused) |
| 调整或分支 | [参数](#deflateparams)、[调优](#deflatetune)、[位预置](#deflateprime)、[复制](#deflatecopy) |
| 释放存储 | [结束](#deflateend) |

这些聚焦契约遵循固定版本的 `deflate.c`、已应用补丁和 `zlib.h`，采用默认 LP64 Linux 构建。它们不改变范围更广的[已登记公开目标](../../checking/goals.md)。定义域/影响标签见[契约约定](contracts.md)，证明状态和剩余工作见[进度](../../progress.md)。

## 共享约定

在每条所述前置条件下，都要求执行无运行时故障地终止，并满足所述后置条件。调用若保留有效流，就保持其表示不变量。

先看一次调用的数据交接。`next_in` 指向本轮尚未读取的输入起点，`avail_in` 是从这里开始可读的字节数；`next_out` 指向本轮下一个可写位置，`avail_out` 是剩余输出容量，也以字节计。一次调用可以只消耗部分输入、只交付部分输出。调用者应读取更新后的指针和计数，接走已交付字节，再为同一个流补充输入或输出空间。

- **有效流：** 可写的 `z_stream`，其压缩器状态由成功初始化或复制建立，经过合法调用保持，且尚未结束。调用者不改变其内部状态或分配器字段。同一个流的调用按顺序执行。
- **缓冲区：** 输入覆盖 `avail_in` 个可读字节；输出覆盖 `avail_out` 个可写字节。它们彼此不重叠，也不与流或流拥有的状态重叠。非 NULL 标量结果指向可写单元，与其他结果及流内存分离。这些分离条件是聚焦契约的显式假设；见 [safety.md](../safety.md)。
- **分配器：** 使用默认分配/释放函数对，或在初始化前将两个字段都置为 NULL。任意一次分配尝试都可能失败。自定义分配器回调不在本页范围内。
- **帧性质与所有权：** 调用只改变自己的流、其拥有的状态和所述输出区域。调用者输入只读。调用者缓冲区和头部记录仍归调用者所有。只有初始化和复制会分配；只有它们失败时的清理与 `deflateEnd` 会释放内存。其他调用保持流的分配集合。
- **头部生命周期：** 保留的 gzip 头及其可选字段在使用期间保持可读且不变。非 NULL 的 `name` 和 `comment` 以零终止；`extra` 覆盖所述长度。聚焦格式契约使用 `extra_len <= 65535`。
- **检查后的拒绝：** 除初始化和上界查询外，流检查失败会在正常操作之前返回 `Z_STREAM_ERROR`，不发生写入。`deflateCopy` 还会清空非 NULL 目标的状态。这种拒绝不修改查询输出单元。
- **受限定义域**指这些显式内存、生命周期和调用顺序条件，加上条目自身的前置条件。它不意味着接受每个可表示的指针或整数。错误概述覆盖可读、可检查的状态，不覆盖任意无效地址。

## deflateInit_

```c
int ZEXPORT deflateInit_(z_streamp strm, int level, const char *version, int stream_size);
```

使用默认 zlib 包装和压缩设置启动压缩器。

### 返回值与后续调用 {#api-deflateinit_-returns}

**返回值类型。** `int` — zlib 状态码

返回值区分压缩器已建立、兼容性拒绝、参数拒绝和分配失败。只有 Z_OK 建立需要结束的有效流。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**压缩器已建立** | 兼容性和级别有效，五项分配均成功；采用 zlib 封装、窗口 15、内存级别 8 和默认策略。 | 可以提供缓冲区并开始压缩；最后用 deflateEnd 释放，即使放弃任务。 |
| `Z_VERSION_ERROR`<br>**兼容性拒绝** | version 为 NULL、版本首字节不匹配，或 stream_size 不等于 sizeof(z_stream)。此检查先于 strm 检查，且不改变流。 | 修正版本和结构大小后再初始化；此结果没有建立待释放的新状态。 |
| `Z_STREAM_ERROR`<br>**流指针为空** | 兼容性检查通过，但 strm 为 NULL。 | 提供符合初始化前提的可写流记录后再初始化。 |
| `Z_STREAM_ERROR`<br>**参数被拒绝** | level 不是 -1 或 0..9。拒绝发生于分配前，但 msg 已清空，并可能安装默认分配器、清空 opaque。 | 修正参数后按初始化前提再调用；没有新分配需要结束。 |
| `Z_MEM_ERROR`<br>**状态分配失败** | 首项状态分配失败；state 保持入口值，没有新分配的块存活。 | 处理内存不足后可按初始化前提重试；无需为此次失败调用 deflateEnd。 |
| `Z_MEM_ERROR`<br>**缓冲分配失败并已清理** | 状态分配成功后，四项缓冲分配全部尝试；任何失败都会释放所有新块，state 变为 NULL，msg 报告内存不足。 | 此调用已完成清理；处理内存不足后可重新初始化。 |

**判读要点。**

- 不消费输入、不写输出。级别 -1 选择 6。

### 调用条件与状态效果 {#api-deflateinit_-contract}

**定义域：** 受限定义域。**影响：** 分配并初始化。

**前置条件：** `strm` 可写，且不拥有有效压缩器状态。其分配器字段按上述约定初始化。`level` 为 -1 或 0..9。`version` 的首字节可读，且与 `ZLIB_VERSION` 的首字节匹配，`stream_size == sizeof(z_stream)`。

<details markdown="1" class="ar-return-exact" data-return-exact="deflateInit_"><summary>完整返回条件与边界</summary>

**后置条件：** 满足 `deflateInit2_` 的契约，方法为 `Z_DEFLATED`，窗口指数为 15（即 `2^15 = 32768` 字节），`memLevel` 为 8，策略为 `Z_DEFAULT_STRATEGY`。级别 -1 选择 6。不消费输入，不写入输出。成功返回 `Z_OK`；内存错误返回 `Z_MEM_ERROR` 并完成全部清理。

**聚焦范围之外：** 适用与 `deflateInit2_` 相同的版本和参数拒绝。`deflateInit` 宏提供版本和结构大小。

</details>

## deflateInit2_

```c
int ZEXPORT deflateInit2_(z_streamp strm, int level, int method, int windowBits,
                           int memLevel, int strategy, const char *version, int stream_size);
```

选择封装和压缩设置，启动压缩器。

这些参数分别决定不同的事情。`level` 在压缩速度与匹配搜索工作量之间作选择；`method` 选择压缩方法，本入口接受 DEFLATE；`memLevel` 控制内部索引和符号缓冲的内存配置；`strategy` 调整采用哪种匹配或编码策略。`windowBits` 同时编码封装选择和窗口尺度。先去掉符号或封装附加值，得到指数 b，再取 `2^b` 字节：15、-15 和 31 都对应 32768 字节，分别选择 zlib、raw 和 gzip。

### 返回值与后续调用 {#api-deflateinit2_-returns}

**返回值类型。** `int` — zlib 状态码

返回值区分压缩器已建立、兼容性拒绝、参数拒绝和分配失败。只有 Z_OK 建立需要结束的有效流。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**压缩器已建立** | 兼容性和参数有效，五项分配均成功；采用所选封装和设置。 | 可以提供缓冲区并开始压缩；最后用 deflateEnd 释放，即使放弃任务。 |
| `Z_VERSION_ERROR`<br>**兼容性拒绝** | version 为 NULL、版本首字节不匹配，或 stream_size 不等于 sizeof(z_stream)。此检查先于 strm 检查，且不改变流。 | 修正版本和结构大小后再初始化；此结果没有建立待释放的新状态。 |
| `Z_STREAM_ERROR`<br>**流指针为空** | 兼容性检查通过，但 strm 为 NULL。 | 提供符合初始化前提的可写流记录后再初始化。 |
| `Z_STREAM_ERROR`<br>**参数被拒绝** | method、level、windowBits、memLevel 或 strategy 不在接受范围。拒绝发生于分配前，但 msg 已清空，并可能安装默认分配器、清空 opaque。 | 修正参数后按初始化前提再调用；没有新分配需要结束。 |
| `Z_MEM_ERROR`<br>**状态分配失败** | 首项状态分配失败；state 保持入口值，没有新分配的块存活。 | 处理内存不足后可按初始化前提重试；无需为此次失败调用 deflateEnd。 |
| `Z_MEM_ERROR`<br>**缓冲分配失败并已清理** | 状态分配成功后，四项缓冲分配全部尝试；任何失败都会释放所有新块，state 变为 NULL，msg 报告内存不足。 | 此调用已完成清理；处理内存不足后可重新初始化。 |

**判读要点。**

- 不消费输入、不写输出。级别 -1 选择 6。

### 调用条件与状态效果 {#api-deflateinit2_-contract}

**定义域：** 受限定义域。**影响：** 分配并初始化。

**前置条件：** 满足 `deflateInit_` 的流和版本条件。参数为：`level` 为 -1 或 0..9；`method == Z_DEFLATED`；`memLevel` 为 1..9；`strategy` 为 0..4；zlib 的 `windowBits` 为 8..15，raw 为 -15..-9，gzip 为 25..31。

<details markdown="1" class="ar-return-exact" data-return-exact="deflateInit2_"><summary>完整返回条件与边界</summary>

**后置条件：** `Z_OK` 建立有效流，拥有五项分配和所选设置。zlib 窗口请求 8 变为 9。总计数为零，`msg` 为 NULL，`data_type` 为 `Z_UNKNOWN`，raw/zlib 的 `adler` 为 1，gzip 的为 0。输入／输出指针和可用计数不变；不消费或输出字节。调用者用 `deflateEnd` 释放状态。

`Z_MEM_ERROR` 不保留任何新分配的有效块。如果状态分配失败，`state` 保持入口值。如果后续分配失败，`state` 变为 NULL，`msg` 报告内存不足。状态分配成功后，全部四项缓冲区分配都会被尝试，然后才进行失败清理。

**聚焦范围之外：** 版本指针为 NULL、首字节不匹配，或结构大小错误时，返回 `Z_VERSION_ERROR`，不改变流。版本兼容且 `strm` 为 NULL 时，返回 `Z_STREAM_ERROR`。其他超出可接受范围的标量参数在分配前返回 `Z_STREAM_ERROR`，此前会清空 `msg`，并按需安装默认分配器字段。安装默认分配器会清空 `opaque`。未改变的公开初始化目标仍要求这些拒绝行为。

</details>

## deflateSetDictionary

```c
int ZEXPORT deflateSetDictionary(z_streamp strm, const Bytef *dictionary, uInt dictLength);
```

将预置字节载入压缩历史，不把它们作为输入数据输出。

`dictLength` 是整个给定字典的字节数，`w_size` 是配置的历史窗口字节数；过长字典只把可用后缀留作历史，但 zlib 的字典标识仍覆盖整个给定字典。

### 返回值与后续调用 {#api-deflatesetdictionary-returns}

**返回值类型。** `int` — zlib 状态码

返回值说明预置历史是否被接受；它不表示字典作为普通输入被压缩输出。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**历史已载入** | 满足字典与流的前提；历史保留最多一个窗口的可用后缀，zlib 校验和覆盖完整字典。 | 随后开始压缩；需要预置字典的解码器须获得相同字典。next_in 和 avail_in 已恢复，不交付输出。 |
| `Z_STREAM_ERROR`<br>**字典条件不满足** | 流检查失败，或使用 gzip、NULL 字典、已离开初始状态的 zlib、非零 lookahead，或 raw 不在已完成块边界；均不改变流。 | 先恢复合法字典调用条件。保留原有有效流的调用可改用合法操作或 deflateEnd。 |

**判读要点。**

- 公开目标还包括合法 raw 边界替换和开始前重复的 zlib 设置；重复 zlib 调用累积 Adler-32。

### 调用条件与状态效果 {#api-deflatesetdictionary-contract}

**定义域：** 受限定义域。**影响：** 更新历史和字典校验和。

**前置条件：** 有效 raw 或 zlib 流，紧接初始化或 `deflateReset`，在第一次 `deflate` 和第一次字典调用之前。`dictionary` 非 NULL，覆盖 `dictLength` 个可读字节，且与窗口分离。

<details markdown="1" class="ar-return-exact" data-return-exact="deflateSetDictionary"><summary>完整返回条件与边界</summary>

**后置条件：** 返回 `Z_OK`。历史保留字典的可用后缀，最多一个窗口。zlib 的字典校验和覆盖整个给定字典。原 `next_in` 和 `avail_in` 被恢复；`total_in` 增加 `min(dictLength, w_size)`。不交付压缩输出，也不分配。需要字典时，必须向解码器提供相同的预置字典。

**聚焦范围之外：** gzip、NULL 字典、已离开初始状态的 zlib、非零预读字节数，或不在已完成块边界的 raw 输入，均返回 `Z_STREAM_ERROR`，不发生变化。合法边界处的 raw 替换，以及开始前多次调用 zlib 字典设置，仍在公开目标内。重复 zlib 调用会累积 Adler-32，而不是重新开始计算。

</details>

## deflateGetDictionary

```c
int ZEXPORT deflateGetDictionary(z_streamp strm, Bytef *dictionary, uInt *dictLength);
```

读取当前压缩历史，包括已接受的预读输入。

这里的“已接受”不等于已经编码。压缩器把一些输入提前读入窗口，等待决定匹配。内部字段 `strstart` 是下一个待处理字节的数组下标，`lookahead` 是其后的预读字节数。下式中的 `w_size` 指配置的历史窗口尺度，以字节计，不是整个物理数组的容量 `window_size`。`n` 表示本次最多复制多少历史字节。

### 返回值与后续调用 {#api-deflategetdictionary-returns}

**返回值类型。** `int` — zlib 状态码

状态码说明查询是否成功；实际历史字节和长度由可选输出参数提供。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**历史查询完成** | 有效流；dictionary 若非 NULL，接收窗口区域最后 n 个字节；dictLength 若非 NULL，接收 n，其中 n = min(strstart + lookahead, window size)。 | 使用所请求的结果；两种输出可独立省略，流不变，可继续合法调用。 |
| `Z_STREAM_ERROR`<br>**流检查未通过** | 流检查失败；正常操作尚未开始，流和结果单元均未写入。 | 先确认有效流及调用前提；不要把这个结果当作已完成操作。 |

**判读要点。**

- 长度以字节计，包括已接受的 lookahead；不保证包含全部历史输入的一个完整窗口。

### 调用条件与状态效果 {#api-deflategetdictionary-contract}

**定义域：** 受限定义域。**影响：** 可带输出缓冲区的查询。

**前置条件：** 有效流。`dictionary` 为 NULL，或可写一个窗口且与窗口分离；`dictLength` 为 NULL，或有效标量输出单元。

<details markdown="1" class="ar-return-exact" data-return-exact="deflateGetDictionary"><summary>完整返回条件与边界</summary>

**后置条件：** 返回 `Z_OK`。设有效状态中的 `n = min(strstart + lookahead, w_size)`。非 NULL 的 `dictionary` 按顺序接收该窗口区域的最后 `n` 个字节；非 NULL 的 `dictLength` 接收 `n`。两种结果均可独立省略。流不变。历史不一定包含此前所有已提供输入中的完整一个窗口。

</details>

## deflateResetKeep

```c
int ZEXPORT deflateResetKeep(z_streamp strm);
```

重新开始输出和进度计数，同时保留压缩历史。

### 返回值与后续调用 {#api-deflateresetkeep-returns}

**返回值类型。** `int` — zlib 状态码

返回值说明输出进度是否已重置；成功仍保留可被后续压缩引用的历史。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**进度已重置，历史保留** | 有效流处于任意阶段。计数、校验和及封装进度重置；待输出数据和未完成的 lookahead 丢弃，gzip 头指针清空。 | 仅在允许引用保留历史的任务中继续；需要空历史时使用 deflateReset。分配仍由流拥有。 |
| `Z_STREAM_ERROR`<br>**流检查未通过** | 流检查失败；正常操作尚未开始，流和结果单元均未写入。 | 先确认有效流及调用前提；不要把这个结果当作已完成操作。 |

**判读要点。**

- 这是未公开文档化的入口。不改变 I/O 指针和可用计数，不分配或释放；保留级别、策略及调优。

### 调用条件与状态效果 {#api-deflateresetkeep-contract}

**定义域：** 受限定义域。**影响：** 重置，保留历史和分配。

**前置条件：** 处于任意阶段的有效流。这是未公开文档化的入口；如果下一个压缩流必须从空历史开始，使用 `deflateReset`。

<details markdown="1" class="ar-return-exact" data-return-exact="deflateResetKeep"><summary>完整返回条件与边界</summary>

**后置条件：** 返回 `Z_OK`。总计数变为零，`msg` 变为 NULL，`data_type` 变为 `Z_UNKNOWN`。待输出数据、尚未完成处理的预读输入，以及位/块进度被丢弃；包装输出重新开始，raw/zlib 的 `adler` 变为 1，gzip 的变为 0。自定义 gzip 头指针清空。级别、策略、调优、窗口和哈希历史保留。输入／输出指针和可用计数不变。不分配或释放。

后续压缩器调用可以引用重置前的历史。因此，仅进行这种重置不保证所得流可以用空字典解码。

</details>

## deflateReset

```c
int ZEXPORT deflateReset(z_streamp strm);
```

复用流，以空历史开始新的压缩。

### 返回值与后续调用 {#api-deflatereset-returns}

**返回值类型。** `int` — zlib 状态码

返回值说明流是否已准备好以空历史复用。成功不释放已有分配。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**已重置为空历史** | 有效流处于任意阶段，包括 Z_STREAM_END 之后。计数、封装及待输出进度重置；历史和字典遗忘，调优恢复为当前级别默认值，gzip 头指针清空。 | 提供新任务的输入和输出；需要时重新登记字典和 gzip 头。最终仍需 deflateEnd。 |
| `Z_STREAM_ERROR`<br>**流检查未通过** | 流检查失败；正常操作尚未开始，流和结果单元均未写入。 | 先确认有效流及调用前提；不要把这个结果当作已完成操作。 |

**判读要点。**

- 未完成输入与未交付输出被丢弃；I/O 指针和可用计数不变，级别、策略、封装和内存配置保留。

### 调用条件与状态效果 {#api-deflatereset-contract}

**定义域：** 受限定义域。**影响：** 重置，保留分配和配置。

**前置条件：** 任意阶段的有效流，包括 `Z_STREAM_END` 之后。

<details markdown="1" class="ar-return-exact" data-return-exact="deflateReset"><summary>完整返回条件与边界</summary>

**后置条件：** 返回 `Z_OK`。完成 `deflateResetKeep` 的计数、包装和待输出数据重置，且历史在逻辑上为空。此前的字典被遗忘；调优恢复为当前级别的默认值。保留 `deflateParams` 最后选择的级别和策略，以及包装、窗口、内存设置。gzip 头被遗忘。输入／输出指针和可用计数不变。不分配或释放。已经接受但尚未处理完的输入，以及尚未交付的输出被丢弃。

</details>

## deflateSetHeader

```c
int ZEXPORT deflateSetHeader(z_streamp strm, gz_headerp head);
```

选择下一个 gzip 流的头部。

### 返回值与后续调用 {#api-deflatesetheader-returns}

**返回值类型。** `int` — zlib 状态码

返回值说明 gzip 头指针是否已登记；成功不表示头部字节已输出。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**头指针已登记** | 有效 gzip 流接受 head；NULL 选择默认头，非 NULL 头仍归调用者所有，尚不复制或输出头部字节。 | 在头部输出完成前保持记录和可选字段有效且不变；继续 deflate。两种重置都会清空指针。 |
| `Z_STREAM_ERROR`<br>**流不接受 gzip 头** | 流检查失败或封装不是 gzip；不发生变化。 | 在有效 gzip 流中按头部调用前提登记；原有效流仍可合法继续或结束。 |

**判读要点。**

- 聚焦用法在第一次 deflate 前登记；较晚登记虽被接受，却不重写已经输出的头部字节。

### 调用条件与状态效果 {#api-deflatesetheader-contract}

**定义域：** 受限定义域。**影响：** 保留调用者拥有的头部指针。

**前置条件：** 有效 gzip 流，在初始化或重置之后、第一次 `deflate` 之前。`head` 为 NULL 时使用默认值，否则满足共享头部条件。

<details markdown="1" class="ar-return-exact" data-return-exact="deflateSetHeader"><summary>完整返回条件与边界</summary>

**后置条件：** 返回 `Z_OK` 并保留 `head`；此时尚不复制或输出头部字节。后续 `deflate` 写入请求的文本标志、时间、操作系统标识，以及可选的扩展字段 `extra`、文件名 `name`、注释 `comment` 和头部 CRC。压缩设置决定额外标志字节。调用者保持记录和字段有效，直到头部输出完成。两种重置都会清空该指针。不分配，也不转移所有权。

**聚焦范围之外：** 非 gzip 或流检查失败时，返回 `Z_STREAM_ERROR`，不发生变化。gzip 接受较晚的登记，但不会重写已经输出的头部字节；公开指针存储目标包括这一情况。

</details>

## deflatePending

```c
int ZEXPORT deflatePending(z_streamp strm, unsigned *pending, int *bits);
```

查询压缩器内部等待输出的数据。

### 返回值与后续调用 {#api-deflatepending-returns}

**返回值类型。** `int` — zlib 状态码

状态码说明查询值能否按请求的类型给出；待输出字节数和位数在输出参数中，不在返回值中。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**查询完成** | 流有效，且 pending 被省略或待输出整字节数可由 unsigned 表示。所请求的 pending 和 bits 接收当前字节数与位数；流和缓冲区不变。 | 使用请求的结果，继续合法流操作；两个输出都可以为 NULL。 |
| `Z_BUF_ERROR`<br>**请求的字节数已饱和** | pending 非 NULL，且内部整字节数超过 unsigned；`*pending` 写为 UINT_MAX。若请求 bits，仍写入位数；流不变。 | 将字节结果视为饱和值，不能视为精确长度；重复相同查询不会恢复精确值。流仍可合法使用。 |
| `Z_STREAM_ERROR`<br>**流检查未通过** | 流检查失败；正常操作尚未开始，流和结果单元均未写入。 | 先确认有效流及调用前提；不要把这个结果当作已完成操作。 |

**判读要点。**

- 正常压缩历史下 bits 为 0..7；这是当前待输出位数，不是 deflateUsed 的最近刷新位数。

### 调用条件与状态效果 {#api-deflatepending-contract}

**定义域：** 受限定义域。**影响：** 可带标量结果的查询。

**前置条件：** 有效流；每个结果为 NULL，或有效且独立的输出单元。

<details markdown="1" class="ar-return-exact" data-return-exact="deflatePending"><summary>完整返回条件与边界</summary>

**后置条件：** 返回 `Z_OK`。若请求相应结果，`pending` 接收尚未交付的整字节数，`bits` 接收剩余位数（合法压缩历史下为 0..7）。流及其缓冲区不变。被省略的结果不写入。

若表示出的待输出计数超出 `unsigned`，所请求的字节计数饱和，并返回 `Z_BUF_ERROR`；若请求了位数结果，仍会写入。虽然正常默认构建的缓冲区更小，公开查询目标仍包括这种数值拒绝。

</details>

## deflateUsed

```c
int ZEXPORT deflateUsed(z_streamp strm, int *bits);
```

查询最近一次字节边界刷新中，最后一个字节的位使用量。

### 返回值与后续调用 {#api-deflateused-returns}

**返回值类型。** `int` — zlib 状态码

返回值是查询状态；最近一次字节边界刷新的位使用量由可选 bits 输出。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**已读取保存的位数** | 有效流；bits 若非 NULL，接收保存值。正常历史下，刷新后为 1..8，自初始化或重置以来未发生该刷新则为 0。 | 使用该保存结果，或以 NULL 省略输出；流不变，可继续合法操作。 |
| `Z_STREAM_ERROR`<br>**流检查未通过** | 流检查失败；正常操作尚未开始，流和结果单元均未写入。 | 先确认有效流及调用前提；不要把这个结果当作已完成操作。 |

**判读要点。**

- 公开目标对每个通过检查的状态返回保存值，不把正常历史范围假设到任意表示状态。该值不同于 deflatePending 的当前待输出位数。

### 调用条件与状态效果 {#api-deflateused-contract}

**定义域：** 受限定义域。**影响：** 可带标量结果的查询。

**前置条件：** 有效流；`bits` 为 NULL，或有效输出单元。

<details markdown="1" class="ar-return-exact" data-return-exact="deflateUsed"><summary>完整返回条件与边界</summary>

**后置条件：** 返回 `Z_OK`。若请求结果，存入已保存的位使用计数：字节边界刷新后为 1..8；如果自初始化/重置以来没有发生这种刷新，则为 0。流不变。该保存计数不同于 `deflatePending` 返回的当前待输出位数。

公开目标对每个通过检查的状态返回存储值，不假设任意表示状态都满足正常历史的范围。

</details>

## deflatePrime

```c
int ZEXPORT deflatePrime(z_streamp strm, int bits, int value);
```

在 raw 压缩输出前添加调用者提供的位片段。

### 返回值与后续调用 {#api-deflateprime-returns}

**返回值类型。** `int` — zlib 状态码

返回值说明位片段是否加入待输出序列。缓冲空间拒绝不会插入片段。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**位片段已加入** | 流检查通过，bits 为 0..16，且待输出空间足够；追加 value 的低 bits 位，最低有效位优先，完整字节进入待输出缓冲。 | 聚焦用法仅在 raw 流首次 deflate 前插入，并在解释输出时计入前缀；没有字节交付至 next_out。 |
| `Z_BUF_ERROR`<br>**位数超范围** | bits 不在 0..16；在待输出字节紧缩之前拒绝，不插入位。 | 修正位数，并满足 priming 的调用前提后再调用。 |
| `Z_BUF_ERROR`<br>**待输出空间不足** | bits 为 0..16，但待输出缓冲没有容纳片段所需的空间；不插入位，但已有待输出字节可能已被紧缩。 | 不要把原样重试当作推进；先按所选位拼接协议合法处理待输出数据，再决定是否重试。 |
| `Z_STREAM_ERROR`<br>**流检查未通过** | 流检查失败；正常操作尚未开始，流和结果单元均未写入。 | 先确认有效流及调用前提；不要把这个结果当作已完成操作。 |

**判读要点。**

- 实现不检查封装或首次调用时机；接受位片段本身不保证任意插入后的普通流格式有效。没有分配。

### 调用条件与状态效果 {#api-deflateprime-contract}

**定义域：** 受限定义域。**影响：** 将位追加到待输出数据。

**前置条件：** 有效 raw 流，在初始化或 `deflateReset` 后第一次 `deflate` 之前；`bits` 为 0..16，`value` 为任意 `int`。调用者解释后续压缩流时需计入这些前缀位。

<details markdown="1" class="ar-return-exact" data-return-exact="deflatePrime"><summary>完整返回条件与边界</summary>

**后置条件：** `Z_OK` 将 `value` 的低 `bits` 位按最低有效位优先的顺序，追加到逻辑待输出位序列。完整字节加入待输出数据，缓冲中剩余少于 8 位。不向 `next_out` 交付字节；不分配。待输出缓冲区空间不足时，`Z_BUF_ERROR` 不插入任何位。发生该拒绝前，可以在所属缓冲区内部紧缩已有待输出字节。

**聚焦范围之外：** 计数不在 0..16 时，在紧缩前返回 `Z_BUF_ERROR`；流检查失败返回 `Z_STREAM_ERROR`。实现不检查包装或首次调用时机。公开目标覆盖这些情况下精确的待输出位影响，但不保证任意插入片段都保持普通流的有效性。

</details>

## deflateParams

```c
int ZEXPORT deflateParams(z_streamp strm, int level, int strategy);
```

更改级别和策略，必要时先完成旧块。

### 返回值与后续调用 {#api-deflateparams-returns}

**返回值类型。** `int` — zlib 状态码

返回值说明新级别和策略是否已安装。为完成旧块，本次调用可能先消费输入并交付输出。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**新设置已安装** | 参数有效，且所需旧块处理已完成；级别 -1 选择 6，更改级别会恢复其标准调优。必要刷新使用旧设置，可产生 I/O 进展。 | 按更新后的指针和计数接走输出、保留未消费输入，并以新设置继续。 |
| `Z_BUF_ERROR`<br>**旧块尚未完成** | 所需旧块尚未处理完；级别和策略保持原值，但已消费输入和已交付输出等压缩进展保留。 | 提供更多输出空间，保留更新后的流与剩余输入，重试 deflateParams；流及分配保留。 |
| `Z_STREAM_ERROR`<br>**设置参数被拒绝** | level 不是 -1 或 0..9，或 strategy 不在 0..4；拒绝时不改变流。 | 修正参数后可在合法流阶段重试；不要假定新设置已经生效。 |
| `Z_STREAM_ERROR`<br>**所需刷新被拒绝** | 参数本身有效，但所需 deflate(Z_BLOCK) 返回 Z_STREAM_ERROR，例如最终处理已开始或缓冲条件不满足；新设置没有安装。 | 先确定原流阶段和缓冲条件。已经开始完成操作时，按 Z_FINISH 协议完成，或合法重置/结束。 |
| `Z_STREAM_ERROR`<br>**流检查未通过** | 流检查失败；正常操作尚未开始，流和结果单元均未写入。 | 先确认有效流及调用前提；不要把这个结果当作已完成操作。 |

**判读要点。**

- 要选择精确输入边界，先完成 deflate(Z_BLOCK) 直到 avail_out 非零，并在参数调用前不提供新输入。

### 调用条件与状态效果 {#api-deflateparams-contract}

**定义域：** 受限定义域。**影响：** 更新设置；可以消费输入并输出数据。

**前置条件：** 有效且尚未开始完成操作的流，流缓冲区和任何正在使用的头部均有效；`level` 为 -1 或 0..9，`strategy` 为 0..4。要选择精确输入边界，持续完成 `deflate(Z_BLOCK)`，直到 `avail_out` 非零，并在此次调用前不提供新输入。

<details markdown="1" class="ar-return-exact" data-return-exact="deflateParams"><summary>完整返回条件与边界</summary>

**后置条件：** `Z_OK` 安装请求的设置（级别 -1 表示 6）。更改级别会恢复该级别的标准调优值。必要的块刷新使用旧设置，可能消费部分输入并交付输出。输入／输出指针、可用计数和总计数精确记录这些字节；未消费输入保持可用。

`Z_BUF_ERROR` 表示旧块尚未完成；级别和策略不变，但已发生的压缩推进和输出保留。提供更多输出空间后重试。两种结果都保留有效流及其分配集合。

**聚焦范围之外：** 无效级别/策略返回 `Z_STREAM_ERROR`，不发生变化。必要的块刷新也可能返回 `Z_STREAM_ERROR`，包括已经开始完成操作后的情况。

</details>

## deflateTune

```c
int ZEXPORT deflateTune(z_streamp strm, int good_length, int max_lazy, int nice_length, int max_chain);
```

设置供专家使用的四个匹配搜索调优值。

这些设置影响寻找重复片段时投入多少工作，不直接指定输出字节。前三个长度参数按输入字节计，最后一个参数按候选个数计：

| 参数 | 控制的选择 |
| --- | --- |
| `good_length` | 已有匹配达到这个长度时，缩短继续搜索的候选链预算。 |
| `max_lazy` | 惰性匹配允许继续尝试下一位置的长度阈值；快速匹配也用它限制短匹配后的逐位置插入。 |
| `nice_length` | 找到达到这个长度的匹配即可提前停止搜索。 |
| `max_chain` | 一次搜索最多检查多少候选。 |

例如增加 `max_chain`，可能让搜索看到更早、更长的匹配，也可能增加比较工作。这不保证每次都压缩得更小；参数仍按下面的 C 存储规则处理。

### 返回值与后续调用 {#api-deflatetune-returns}

**返回值类型。** `int` — zlib 状态码

返回值只说明四个调优字段是否存入，不保证任意取值下后续压缩的性质。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**调优值已存入** | 有效流接受所有 int 参数；good_length、max_lazy 和 max_chain 转为 unsigned，nice_length 按 signed 存储。不消费输入或交付输出。 | 选择适用于后续压缩的调优；deflateReset 或 deflateParams 更改级别会恢复标准值。 |
| `Z_STREAM_ERROR`<br>**流检查未通过** | 流检查失败；正常操作尚未开始，流和结果单元均未写入。 | 先确认有效流及调用前提；不要把这个结果当作已完成操作。 |

**判读要点。**

- C 建议 max_lazy >= 3、max_chain >= 4；设置成功本身不建立所有选择下的后续安全性或压缩上界。

### 调用条件与状态效果 {#api-deflatetune-contract}

**定义域：** 受限定义域（有效流）；覆盖所有 `int` 调优参数。

**影响：** 更新调优字段。

**前置条件：** 有效流。

<details markdown="1" class="ar-return-exact" data-return-exact="deflateTune"><summary>完整返回条件与边界</summary>

**后置条件：** 返回 `Z_OK`。将 `good_length`、`max_lazy`、`max_chain` 转为无符号后存入，将 `nice_length` 作为有符号值存入。不消费输入、不交付输出、不分配。`deflateParams` 更改级别，或执行 `deflateReset`，会恢复标准调优。仅凭该设置器契约，不能证明所有调优选择下的后续压缩上界或安全性；C 建议 `max_lazy >= 3` 和 `max_chain >= 4`。

</details>

## deflateBound_z

```c
z_size_t ZEXPORT deflateBound_z(z_streamp strm, z_size_t sourceLen);
```

根据流当前的配置和封装计算大小上界。

这个查询回答“为整份输入准备多少输出字节才足够”。`sourceLen` 是输入字节数，下面缩写为 `n`；`w` 是头部、尾部及可选字段合计的封装字节数。`floor(x)` 表示向下取整。`SIZE_MAX` 是返回类型 `z_size_t` 能表示的最大值；“饱和”表示数学结果再大也只返回这个最大值，而不回绕成较小数。

### 返回值与后续调用 {#api-deflatebound_z-returns}

**返回值类型。** `z_size_t` — 输出容量上界（字节）

返回值是以字节计的输出容量上界数值，不是 zlib 状态码。结果可能在 SIZE_MAX 处饱和。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `bound`<br>**输出字节数上界** | 有效流按当前窗口、内存级别、压缩级别和完整封装大小选择公式；NULL 或可安全检查的无效流采用固定/存储公式较大者加 18。结果均在 SIZE_MAX 处饱和，堆不变。 | 仅在配置、字典和头部固定，使用标准调优且无预置位的初始化后、压缩前条件下，将它用于所述容量保证；还须满足缓冲可表示及 avail_in/avail_out 容量条件。 |

**判读要点。**

- SIZE_MAX 可是精确值，也可是饱和结果；它不保证存在这么大的可寻址缓冲区。没有错误码。
- 满足容量前提时，一次提供全部输入及至少该上界的输出空间给 deflate(Z_FINISH)，必须得到 Z_STREAM_END；仅 Z_NO_FLUSH 后接 Z_FINISH 的安排具有总输出上界，其他刷新可能超出。

### 调用条件与状态效果 {#api-deflatebound_z-contract}

**定义域：** 受限定义域（有效流和可读的保留头部）；包括每个 `z_size_t sourceLen`。**影响：** 查询。

**前置条件：** 有效流，满足共享头部条件。对于下述输出容量保证，应在初始化及任何字典/头部设置后、压缩前调用。保持配置、头部和字典不变；使用标准调优，不插入预置位。

<details markdown="1" class="ar-return-exact" data-return-exact="deflateBound_z"><summary>完整返回条件与边界</summary>

**后置条件：** 堆不变。数值目标是下述数学值，在 `SIZE_MAX` 处饱和，其中 `n = sourceLen`，`w` 为完整包装大小：

- 窗口 15 且内存级别 8：`n + floor(n/4096) + floor(n/16384) + floor(n/33554432) + 7 + w`。
- 否则，若窗口位数不超过哈希位数且级别非零：`n + floor(n/8) + floor(n/256) + floor(n/512) + 4 + w`。
- 否则：`n + floor(n/32) + floor(n/128) + floor(n/2048) + 7 + w`。

raw 的 `w` 为 0；zlib 为 6，存在预置历史时再加 4；gzip 为 18，再加可选扩展字段 `extra`（包括两个长度字节）、以零终止的名称/注释和头部 CRC。

**输出容量：** 与数值公式分开，对于大小可表示且足够的缓冲区，如果输入和输出大小能放入 `avail_in` 和 `avail_out`，向一次 `deflate(Z_FINISH)` 提供全部 `n` 个字节及至少为上界的输出空间，必须返回 `Z_STREAM_END`。在 `Z_FINISH` 前仅使用 `Z_NO_FLUSH` 的干净调用安排具有总输出上界。其他刷新安排可能超出此上界。饱和结果不承诺存在这样大小的可寻址缓冲区。

**聚焦范围之外：** NULL 或可安全检查的无效流，得到上述固定/存储公式中的较大值，再加 18，并进行饱和。没有错误码。公开数值目标仍包括每种可读的 gzip 头部长度，包括聚焦的 16 位扩展字段范围之外的长度；本页不移除这一义务。

</details>

## deflateBound

```c
uLong ZEXPORT deflateBound(z_streamp strm, uLong sourceLen);
```

返回压缩上界的 `uLong` 形式。

### 返回值与后续调用 {#api-deflatebound-returns}

**返回值类型。** `uLong` — 输出容量上界（字节）

返回 deflateBound_z 上界的 uLong 形式，仍以字节计。ULONG_MAX 是数值上限，不是错误码。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `bound`<br>**uLong 输出字节数上界** | deflateBound_z 的数值可由 uLong 表示时原样返回，否则返回 ULONG_MAX；NULL 或可安全检查的无效流也使用其保守回退公式。流不变。 | 用于容量规划时，遵守 deflateBound_z 的初始化时机、固定设置、调优、无预置位及缓冲和刷新安排条件。 |

**判读要点。**

- ULONG_MAX 可以是精确值，也可以是截至上限的结果；数值相等本身不提供额外容量保证。
- 默认 LP64 下，uLong 和 z_size_t 都为 64 位，两种查询结果一致。

### 调用条件与状态效果 {#api-deflatebound-contract}

**定义域：** 与 `deflateBound_z` 相同的受限定义域；包括每个 `uLong sourceLen`。

**影响：** 查询。

**前置条件：** 适用 `deflateBound_z` 的条件。

<details markdown="1" class="ar-return-exact" data-return-exact="deflateBound"><summary>完整返回条件与边界</summary>

**后置条件：** 如果数值结果能由 `uLong` 表示，则返回该结果，否则返回 `ULONG_MAX`。默认 LP64 目标中两种类型都是 64 位，结果相同。流不变。输出是否足够，仍要求 `deflateBound_z` 单独规定的调用安排和容量条件，不能只由数值相等推出。

</details>

## deflate

```c
int ZEXPORT deflate(z_streamp strm, int flush);
```

接受输入，交付有效压缩流的一部分或全部。

`flush` 描述调用者希望推进到哪里：普通调用交给压缩器选择输出时机，刷新请求建立所选边界，`Z_FINISH` 请求结束整个流。请求不会让有限输出空间变大；空间用完时，仍要取走输出并按下述协议继续。

### 返回值与后续调用 {#api-deflate-returns}

**返回值类型。** `int` — zlib 状态码

返回值区分本次继续、整个压缩流完成，以及拒绝或无法推进。读取更新后的指针和计数，才能知道本轮消费和交付了多少字节。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**尚可能需要继续** | 调用尚未报告完整流结束。可能已消费部分输入或交付头部、数据、刷新标记或尾部；输出填满时仍可能有未消费输入或待输出数据。 | 接走输出并使用更新后的计数；输出填满时补空间，刷新期间保持同一 flush。开始完成操作后不增加输入，只用 Z_FINISH 继续直到 Z_STREAM_END。 |
| `Z_STREAM_END`<br>**完整压缩流已交付** | 仅在 Z_FINISH 下，所有给定输入及全部压缩输出（包括封装尾部）均已交付。 | 保存最终输出；用 deflateEnd 释放，或 deflateReset 开始新流。此返回本身不释放状态。 |
| `Z_BUF_ERROR`<br>**没有输出空间** | 初始检查通过，但 avail_out 为 0；不消费输入、不交付输出，原有效流保留。 | 提供有效非空输出空间后继续；若正在刷新，保持原 flush，最终处理期间只用 Z_FINISH。 |
| `Z_BUF_ERROR`<br>**目前无法推进** | 没有可用输入或待输出数据，且没有比此前更强的刷新请求；当前非 Z_FINISH 调用无法推进。 | 等待新输入，或在应用确实需要时选择更强的合法刷新；不要原样循环。流仍有效。 |
| `Z_BUF_ERROR`<br>**最终处理后又提供输入** | 最终块处理已开始后仍提供新输入；不接受新输入，但拒绝前可能已交付旧待输出数据。有效流保留。 | 接走实际交付的输出，把未接受的新输入留给另一任务；不再向此流提供输入，仅用 Z_FINISH 完成，或合法重置/结束。 |
| `Z_STREAM_ERROR`<br>**流或调用参数被拒绝** | 流检查失败、flush 无效（包括 Z_TREES）、next_out 为 NULL、非零输入配 NULL next_in，或最终处理开始后使用非 Z_FINISH。初始拒绝不消费或交付字节。 | 先确定流仍有效并修正缓冲或 flush；已开始最终处理时只用 Z_FINISH。检查失败不提供可直接重试或结束任意状态的保证。 |

**判读要点。**

- 状态码不是本轮字节计数；I/O 指针、avail_in/avail_out 和 total_in/total_out 记录实际进展。调用不分配或释放。
- 非结束刷新完成后，Z_OK 仍不是流结束；应结合输出空间和所用刷新协议判断该边界是否完成。错误返回仍可能改变 msg 或记住的 flush。

### 调用条件与状态效果 {#api-deflate-contract}

**定义域：** 受限定义域。**影响：** 消费输入、输出数据并更新进度。

**前置条件：** 有效流，缓冲区和任何正在使用的头部均有效。`next_out` 非 NULL，`avail_out > 0`；仅输入为零时 `next_in` 可为 NULL。`flush` 为 `Z_NO_FLUSH`、`Z_PARTIAL_FLUSH`、`Z_SYNC_FLUSH`、`Z_FULL_FLUSH`、`Z_FINISH` 或 `Z_BLOCK`。刷新期间输出填满时，以相同刷新请求和更多空间继续。开始完成操作后，不提供新输入，只以 `Z_FINISH` 继续。普通格式有效性要求从初始化/`deflateReset`（或该历史的副本）开始，使用合法字典/头部设置、标准调优，且不进行任意位预置。

<details markdown="1" class="ar-return-exact" data-return-exact="deflate"><summary>完整返回条件与边界</summary>

**后置条件：** 记本轮消费的输入字节数为 `used`，交付的输出字节数为 `made`；`old avail_in` 和 `old avail_out` 是调用前提供的输入量和输出容量。满足 `used <= old avail_in`、`made <= old avail_out`。指针按相应数量推进，可用计数按相应数量减少，总计数按相应数量增加并遵循无符号回绕。输入不变；已交付前缀以外的输出不变。输出填满时可能仍有输入未消费。不分配或释放。

跨调用交付的字节构成已接受输入的一种有效编码的前缀，使用所选包装、设置和预置字典。完成的输出可解码为该输入。这里规定有效输出，而非唯一的压缩字节序列。头部输出之后，`adler` 用 Adler-32 跟踪 zlib 已接受输入，用 CRC-32 跟踪 gzip 已接受输入；raw 没有输入校验和。

`Z_OK` 表示可能需要继续。`Z_STREAM_END` 只在 `Z_FINISH` 下发生，且所有给定输入及所有压缩输出（包括尾部）都已交付。有效状态仍被拥有，直到 `deflateEnd` 释放，或通过 `deflateReset` 复用。

请求的刷新完全交付后，`Z_BLOCK` 完成一个块但不填充到字节边界；`Z_PARTIAL_FLUSH` 添加空固定块；`Z_SYNC_FLUSH` 使此前全部输入可供解码器解码，并以对齐的空存储块结尾。`Z_FULL_FLUSH` 还重置匹配历史：后续块不引用该次已完成刷新之前的数据。若要在那里重新启动 raw 解码器，需要保留精确边界，并先交付完整刷新标记。`Z_FINISH` 关闭最终块并写入包装尾部。

**错误：** `Z_BUF_ERROR` 覆盖输出空间为零、无输入且无更强刷新请求因而无法推进，或最终块处理已开始后又提供输入。它保留有效流；应按需提供空间/输入。`Z_STREAM_ERROR` 覆盖流检查失败、无效刷新（包括 `Z_TREES`）、无效 NULL 输入／输出组合，或完成操作开始后请求非完成刷新。初始参数拒绝不消费输入、不交付输出。开始完成操作后，因新输入而产生的较晚 `Z_BUF_ERROR`，可能先交付旧的待输出数据；不接受新输入。`msg` 和记录的刷新请求可能改变。未改变的公开目标包括所有有符号刷新值及这些拒绝。

</details>

## deflateEnd

```c
int ZEXPORT deflateEnd(z_streamp strm);
```

释放压缩器，丢弃任何未完成工作。

### 返回值与后续调用 {#api-deflateend-returns}

**返回值类型。** `int` — zlib 状态码

返回值区分释放前的压缩阶段。Z_OK 和 Z_DATA_ERROR 都表示五项流分配已释放，state 已清空。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**状态已释放** | 有效流的保存状态不是 BUSY_STATE；全部流分配已恰好释放一次，state 为 NULL。 | 保留调用者自有的缓冲区和头部；再次压缩前重新初始化。返回值本身不确认所有输出已交付。 |
| `Z_DATA_ERROR`<br>**未完成任务已释放** | 有效流的保存状态为 BUSY_STATE，报告未完成压缩；全部流分配仍已释放，state 为 NULL。 | 不要为清理再次调用 deflateEnd；未完成压缩已经放弃，再次压缩须重新初始化。 |
| `Z_STREAM_ERROR`<br>**结束请求被拒绝** | 流检查失败，包括第二次结束；本次不释放任何内容。 | 不要把该结果当作释放成功；先确定流的实际生命周期，不能据此对任意状态继续压缩或重试释放。 |

**判读要点。**

- 返回状态取决于内部阶段，不只是输出是否全部交付。调用者输入、输出和头部仍归调用者所有，且不被释放。

### 调用条件与状态效果 {#api-deflateend-contract}

**定义域：** 受限定义域。**影响：** 释放拥有的状态。

**前置条件：** 任意阶段的有效流，默认释放例程保持完整。

<details markdown="1" class="ar-return-exact" data-return-exact="deflateEnd"><summary>完整返回条件与边界</summary>

**后置条件：** 对全部五项拥有的分配恰好释放一次，并将 `state` 置为 NULL。调用者输入/输出及头部存储不变，仍归调用者所有。保存的状态为尚未完成普通压缩的 `BUSY_STATE` 时返回 `Z_DATA_ERROR`，否则返回 `Z_OK`。两种结果都释放全部资源：`Z_DATA_ERROR` 报告未完成压缩，不表示清理失败。重新初始化前，后续压缩调用均无效。

**聚焦范围之外：** 流检查失败，包括第二次结束，返回 `Z_STREAM_ERROR`，不释放任何内容。返回状态取决于内部压缩阶段，而不只是是否已交付每个产生的字节。

</details>

## deflateCopy

```c
int ZEXPORT deflateCopy(z_streamp dest, z_streamp source);
```

创建压缩进度相同、彼此独立的压缩器。

### 返回值与后续调用 {#api-deflatecopy-returns}

**返回值类型。** `int` — zlib 状态码

返回值说明目标是否获得独立的压缩状态。失败清理只涉及此次新分配，源流保持不变。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**独立状态已复制** | 源有效且目标满足独立空记录前提；目标获得五项新分配及等价进度，内部指针重定位，源不变。 | 两个流分别需要 deflateEnd；并行推进前给它们独立输出空间。复制的 I/O 指针起初相同，保留的头仍由调用者共享拥有。 |
| `Z_MEM_ERROR`<br>**分配失败并已清理** | 任意新分配失败；所有新块已释放，dest->state 清空，其他目标字段和源不变，没有新的有效目标流。 | 不需要结束失败的目标；处理内存不足后可按复制前提重试，源仍可合法继续或结束。 |
| `Z_STREAM_ERROR`<br>**目标为空** | dest 为 NULL，复制未开始。 | 提供不同于源且不拥有状态的可写目标记录，再按复制前提调用。 |
| `Z_STREAM_ERROR`<br>**源检查未通过** | 非 NULL 目标配源检查失败；dest->state 清空，不进行复制分配。 | 先确定有效源；只对不同且不拥有状态的目标调用，不能据此认为任意原有目标状态已被释放。 |

**判读要点。**

- 契约排除自复制和覆盖已有效目标；这些情况没有无泄漏保证。

### 调用条件与状态效果 {#api-deflatecopy-contract}

**定义域：** 受限定义域。**影响：** 分配并复制拥有的状态。

**前置条件：** `source` 有效。`dest` 是另一个可写 `z_stream`，不拥有状态，且与源的内存分离。源缓冲区和任何保留的头部满足生命周期要求。

<details markdown="1" class="ar-return-exact" data-return-exact="deflateCopy"><summary>完整返回条件与边界</summary>

**后置条件：** `Z_OK` 使 `dest` 获得五项新拥有的分配，包含等价的压缩状态；源不变。复制的流字段包括总计数、分配器字段、输入／输出指针和保留的头部指针。内部拥有的指针被重定位到新分配。两个流各自需要 `deflateEnd`，可独立继续。复制的调用者 输入／输出指针起初指向相同缓冲区；继续两个流前应分配独立输出空间。头部仍是共享的调用者自有存储。

`Z_MEM_ERROR` 释放每项新分配、清空 `dest->state`，并保持其他目标字段和源不变。没有新的有效状态需要释放。

**聚焦范围之外：** NULL 目标返回 `Z_STREAM_ERROR`；源检查失败还会清空非 NULL 目标的状态。公开目标显式假设两个流不同。这里排除自复制和覆盖已有效目标，不为它们提供无泄漏契约。

[返回 API 手册](README.md) · [契约约定](contracts.md)

</details>
