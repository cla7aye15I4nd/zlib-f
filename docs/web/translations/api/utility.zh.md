<!--
source: docs/api/utility.md
source-sha256: d847c0f171b3994c900a7892f1ba76e2d7e49045a634b916ba106fe753f5bada
-->

# 缓冲区工具与库信息

[API 手册](README.md) · [共享流规则](streams.md) · [校验和](checksums.md)

当调用时已经知道完整输入和输出容量，可以使用缓冲区工具。它们在内部管理一个临时流。
若需要增量 I/O、其他封装、字典或显式刷新边界，应使用流接口页面。

| 任务 | 条目 |
| --- | --- |
| 压缩缓冲区 | [选择级别](#compress2_z)、[默认级别](#compress_z)、[确定目标尺寸](#compressbound_z) |
| 解压缓冲区 | [报告已消费输入](#uncompress2_z)、[只返回输出](#uncompress_z) |
| 查看库信息 | [版本](#zlibversion)、[编译标志](#zlibcompileflags)、[错误文本](#zerror) |

这些聚焦契约遵循默认 LP64 Linux 构建中的 `compress.c`、`uncompr.c`、`zutil.c` 和 `zlib.h`。
`_z` 形式使用 `z_size_t`；普通形式使用 `uLong`。这里两者均为 64 位。
对源码的解读仍 **to confirm**，需要证明确认。它们不缩小
[Utilities.lean](../../ZlibF/Spec/Public/Utilities.lean) 与
[Queries.lean](../../ZlibF/Spec/Public/Queries.lean) 中已登记目标的范围。
[Calls.lean](../../ZlibF/Spec/Public/Calls.lean) 固定了翻译后的参数和结果。
定义域及效果标签见[契约约定](contracts.md)，证明状态与剩余工作见[概览](../overview.md)。

缓冲区工具创建并释放一个局部流，使用 zlib 封装和默认设置。

```mermaid
flowchart LR
    B["compressBound"] --> C["compress / compress2"]
    C --> Z["zlib stream"] --> U["uncompress / uncompress2"]
    U --> D["decoded bytes"]
```

### 共同约定

对于缓冲区调用，定义域限制为有效内存：非 NULL 源覆盖给定的可读输入；
非 NULL 目标覆盖给定的可写容量。非 NULL 长度指针指向可读、可写的标量单元。
输入、输出和长度单元彼此分离，包括同时出现的两个长度单元。
调用者在整个调用期间保持这些对象存活，并且不修改它们。
各个条目说明允许的 NULL 情形。其他无效指针不在本范围内。
解压错误处理不要求压缩数据有效。

**共同效果。** 范围内的每次调用都终止且不产生故障。
缓冲区调用保持输入，以及输出和长度单元之外的内存不变，写入量不超过原始容量。
所有内部分配都在返回前释放，包括分配失败路径；不返回局部流或其拥有的分配。
返回指针的查询返回借用的不可变存储。
这些是契约要求，不表示实现证明已经完成。

## compress2_z

```c
int ZEXPORT compress2_z(Bytef *dest, z_size_t *destLen, const Bytef *source,
                        z_size_t sourceLen, int level);
```

按请求的级别，将输入压缩为一个完整的 zlib 流。

**Domain.** 受限定义域。

**Pre.** 满足上述受限缓冲区定义域。`source` 可以在输入为零时为 NULL，
也可以作为需检查并拒绝的情形为 NULL。`destLen` 可以为 NULL，供检查并拒绝。
`dest` 可以为 NULL，供检查并拒绝，包括下述零容量情形。
级别 -1 和 0–9 有效；-1 选择级别 6。

**Post.** `Z_OK` 表示输出是输入的完整 zlib 编码，`*destLen` 为其长度。
`Z_BUF_ERROR` 表示容量已经被该编码的一个前缀填满。
`Z_MEM_ERROR` 表示分配失败，且没有写入输出。

**Effects.** 有状态；适用共同效果。
源为 NULL 且输入非零、`destLen` 为 NULL，或目标为 NULL 且容量非零时，
在任何长度写入之前返回 `Z_STREAM_ERROR`。
否则，在初始化之前将 `*destLen` 清零。
无效级别在任何分配之前返回 `Z_STREAM_ERROR`，长度为零。
之后的返回会保存已写出的字节数。

**Edges.** 目标为 NULL 且容量为零时会进入初始化：若分配失败，则返回 `Z_MEM_ERROR`；
否则返回 `Z_STREAM_ERROR`，长度为零。
非 NULL 目标且容量为零时，在初始化成功后返回 `Z_BUF_ERROR`。
空输入有效。

## compress2

```c
int ZEXPORT compress2(Bytef *dest, uLongf *destLen, const Bytef *source,
                      uLong sourceLen, int level);
```

[compress2_z](#compress2_z) 的 `uLong` 形式。

**Domain.** 受限定义域。

**Pre.** 满足 `compress2_z` 的受限定义域，且 `destLen` 单元必须非 NULL。
封装函数在调用带检查的 `_z` 入口前会读取该单元。

**Post.** 编码及返回码契约与 `compress2_z` 相同。

**Effects.** 有状态；具有相同的缓冲区和清理效果。
封装函数在每次返回时都会回写长度，包括错误返回。
早期参数拒绝保持其原值；无效级别或分配失败会使它变为零。

## compress_z

```c
int ZEXPORT compress_z(Bytef *dest, z_size_t *destLen, const Bytef *source, z_size_t sourceLen);
```

按默认级别压缩（-1，选择级别 6）。

**Domain.** 受限定义域。

**Pre.** 满足 [compress2_z](#compress2_z) 的受限定义域，但没有级别参数。

**Post.** 与默认级别下的 `compress2_z` 相同。

**Effects.** 有状态；长度写入、受检查的 NULL 情形及完整清理均相同。

## compress

```c
int ZEXPORT compress(Bytef *dest, uLongf *destLen, const Bytef *source, uLong sourceLen);
```

使用默认级别的 `uLong` 压缩器。

**Domain.** 受限定义域。

**Pre.** 满足 [compress2](#compress2) 的受限定义域；`destLen` 必须非 NULL。

**Post.** 与级别 -1 下的 `compress2` 相同。

**Effects.** 有状态；长度写入及完整清理与 `compress2` 相同。

## compressBound_z

```c
z_size_t ZEXPORT compressBound_z(z_size_t sourceLen);
```

计算为默认 zlib 压缩缓冲区确定尺寸所用的数值上界。

**Domain.** 完整类型定义域。

**Pre.** 完整类型定义域：所有 64 位 `sourceLen`，包括零和最大值。

**Post.** 对 `n = sourceLen`，返回
`min(2^64 - 1, n + (n >> 12) + (n >> 14) + (n >> 25) + 13)`，
其中求和按数学意义解释。零得到 13；求和溢出则得到最大值。

**Effects.** 纯函数。没有指针访问、分配、状态变化或错误返回。

**Scope.** 本契约规定这个数值。对于使用默认封装、窗口和内存设置的有效压缩调用，
输出容量是否足够是另一项性质。它不为任意 raw 或 gzip 流设置提供上界。

## compressBound

```c
uLong ZEXPORT compressBound(uLong sourceLen);
```

该数值上界的 `uLong` 形式。

**Domain.** 完整类型定义域。

**Pre.** 完整类型定义域：所有 64 位 `sourceLen`。

**Post.** 在本构建中，公式及饱和规则与 [compressBound_z](#compressbound_z) 相同。

**Effects.** 纯函数。没有内存访问或错误返回。输出容量充分性的范围约束也相同。

## uncompress2_z

```c
int ZEXPORT uncompress2_z(Bytef *dest, z_size_t *destLen, const Bytef *source, z_size_t *sourceLen);
```

解码第一个 zlib 流，并同时报告输出大小与输入消费量。

**Domain.** 受限定义域。

**Pre.** 满足上述受限缓冲区定义域。`*sourceLen` 是可用输入量，`*destLen` 是输出容量。
任一长度指针都可以为 NULL，供检查并拒绝。
数据指针只有在对应长度为零，或作为需检查并拒绝的情形时，才允许为 NULL。
畸形、截断、raw、gzip 以及依赖字典的输入，都纳入范围作为错误情形。

**Post.** `Z_OK` 表示一个经过检查的完整 zlib 流已解码为输出。尾随输入未被使用。
`Z_BUF_ERROR` 表示输出已填满容量且仍有输入。
`Z_DATA_ERROR` 覆盖畸形或不完整输入，以及需要预设字典的情形。
`Z_MEM_ERROR` 表示分配失败，并且可能发生在部分输出之后。

**Effects.** 有状态；适用共同效果。
参数检查先于初始化：`sourceLen` 为 NULL、源为 NULL 且非空、`destLen` 为 NULL，
或目标为 NULL 且容量为正时，返回 `Z_STREAM_ERROR`，两个已有长度单元均保持不变。
初始化失败也保持两个长度不变，并且不写输出。
初始化之后，每次返回都会将已消费字节数存入 `*sourceLen`、已产生字节数存入 `*destLen`，
包括之后发生的内存失败。已经写出的输出仍可使用。

**Edges.** 目标为 NULL 且容量为零时，通过一个私有输出指针接受调用；
完整的空流可以成功。空输入在初始化成功后产生数据错误。
精确的最终映射是：`Z_STREAM_END` 映射为 `Z_OK`，`Z_NEED_DICT` 映射为 `Z_DATA_ERROR`，
没有剩余输入时将 `Z_BUF_ERROR` 映射为 `Z_DATA_ERROR`。其他解码器返回码保持不变。

## uncompress2

```c
int ZEXPORT uncompress2(Bytef *dest, uLongf *destLen, const Bytef *source, uLong *sourceLen);
```

带输入消费计数的 `uLong` 解码器。

**Domain.** 受限定义域。

**Pre.** 满足 [uncompress2_z](#uncompress2_z) 的受限定义域，且两个长度单元均非 NULL，
因为封装函数会在 `_z` 检查之前读取它们。

**Post.** 解码、返回码和消费计数与 `uncompress2_z` 相同。

**Effects.** 有状态；输出及清理效果相同。每次返回都会回写两个长度，包括错误返回。
参数拒绝与初始化失败保持它们的值不变。

## uncompress_z

```c
int ZEXPORT uncompress_z(Bytef *dest, z_size_t *destLen, const Bytef *source, z_size_t sourceLen);
```

解码，但不公开已消费输入的计数。

**Domain.** 受限定义域。

**Pre.** 满足 [uncompress2_z](#uncompress2_z) 的受限定义域；`sourceLen` 按值传入。
`destLen` 可以为 NULL，供检查并拒绝。

**Post.** 输出及返回码与 `uncompress2_z` 相同。尾随字节被忽略；
调用者不会获得可用来定位这些字节的消费计数。

**Effects.** 有状态；输出长度写入及完整清理相同。消费计数是局部值。

## uncompress

```c
int ZEXPORT uncompress(Bytef *dest, uLongf *destLen, const Bytef *source, uLong sourceLen);
```

不提供已消费输入计数的 `uLong` 解码器。

**Domain.** 受限定义域。

**Pre.** 满足 [uncompress2](#uncompress2) 的受限缓冲区定义域，且 `destLen` 非 NULL。

**Post.** 输出及返回码与 `uncompress2` 相同；忽略尾随输入。

**Effects.** 有状态；输出长度写入、保留部分输出及完整清理均相同。

## zlibVersion

```c
const char * ZEXPORT zlibVersion(void);
```

返回所链接库的版本字符串。

**Domain.** 完整类型定义域。

**Pre.** 完整类型定义域；不需要参数或调用者状态。

**Post.** 返回非 NULL 指针，指向以 NUL 结尾的 `ZLIB_VERSION`（`1.3.2.1-motley`）。

**Effects.** 只读。结果是借用的不可变静态存储；调用者不得写入或释放它。
没有分配或堆变化。

## zlibCompileFlags

```c
uLong ZEXPORT zlibCompileFlags(void);
```

报告本构建的类型尺寸和编译期选项。

**Domain.** 完整类型定义域。

**Pre.** 完整类型定义域；不需要参数或调用者状态。

**Post.** 在本构建中返回 169（`0xa9`）：`uInt` 为 4 字节；
`uLong`、指针和 `z_off_t` 均为 8 字节。
它们的两位字段分别用 0、1、2、3 表示尺寸 2、4、8 和其他。
选定构建中的其他标志都为零。

**Effects.** 纯标量查询。没有分配、内存写入或错误返回。

## zError

```c
const char * ZEXPORT zError(int err);
```

返回与 zlib 结果码关联的文本。

**Domain.** 完整类型定义域。

**Pre.** 完整类型定义域：所有 `int`，包括最小值与最大值。

**Post.** 返回非 NULL 指针，指向下表中以 NUL 结尾的文本。

| `err` | 文本 |
| --- | --- |
| 2 | `need dictionary` |
| 1 | `stream end` |
| -1 | `file error` |
| -2 | `stream error` |
| -3 | `data error` |
| -4 | `insufficient memory` |
| -5 | `buffer error` |
| -6 | `incompatible version` |
| 0 或其他任意值 | 空字符串 |

**Effects.** 只读。结果是借用的不可变静态存储；不得写入或释放它。
没有分配、堆变化或错误返回。值若超出 -6–2，会在索引运算前被检查，
所以两个标量极值都能安全返回空文本。

[返回 API 手册](README.md) · [契约约定](contracts.md)
