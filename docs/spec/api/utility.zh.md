# 缓冲区工具与库信息

[API 手册](README.md) · [共享流规则](streams.md) · [校验和](checksums.md)

调用时已知完整输入和输出容量，可使用缓冲区工具。它们在内部管理临时流。
需要增量 I/O、其他包装、字典或显式刷新边界时，应使用流式接口页面。

| 任务 | 入口 |
| --- | --- |
| 压缩缓冲区 | [选择级别](#compress2_z)、[默认级别](#compress_z)、[确定目标容量](#compressbound_z) |
| 解压缓冲区 | [报告已消费输入](#uncompress2_z)、[仅报告输出](#uncompress_z) |
| 查询库信息 | [版本](#zlibversion)、[编译标志](#zlibcompileflags)、[错误文本](#zerror) |

这些聚焦契约对应默认 LP64 Linux 构建中的 `compress.c`、`uncompr.c`、`zutil.c` 和
`zlib.h`。`_z` 形式使用 `z_size_t`；普通形式使用 `uLong`。这里两者均为 64 位。
源码解读仍**待确认**，须由证明落实。它们不会缩小
[Utilities.lean](../../../ZlibF/Spec/Public/Utilities.lean) 和
[Queries.lean](../../../ZlibF/Spec/Public/Queries.lean) 中登记的目标。
[Calls.lean](../../../ZlibF/Spec/Public/Calls.lean) 固定翻译后的参数和结果。
定义域和效果标签见[契约约定](contracts.md)；证明状态和剩余工作见[进度](../../progress.md)。
超出聚焦前提只表示本契约不作保证，不自动等于 C 未定义行为（UB），也不保证一定返回错误码。

缓冲区工具使用 zlib 包装和默认设置，创建并释放一个局部流。

```mermaid
flowchart LR
    B["compressBound"] --> C["compress / compress2"]
    C --> Z["zlib 流"] --> U["uncompress / uncompress2"]
    U --> D["解码字节"]
```

### 通用约定

缓冲区调用的定义域限于有效内存：非 NULL 源覆盖指定的可读输入；
非 NULL 目标覆盖指定的可写容量。非 NULL 长度指针指向可读写的标量单元。
输入、输出和长度单元互相分离，包括同时出现的两个长度单元。
调用期间，调用者保持这些对象存活且不修改它们。
各入口分别说明允许的 NULL 情形。其他无效指针不在此范围内。
处理解压错误不要求压缩数据有效。

**通用效果。** 每个范围内调用都终止且不产生故障。
缓冲区调用保持输入以及输出、长度单元以外的内存不变，写入不超过原始容量。
返回前释放所有内部分配，包括分配失败路径；不返回局部流或其拥有的分配。
返回指针的查询交付借用的不可变存储。
这些是契约要求，不表示实现证明已经完成。

## compress2_z

```c
int ZEXPORT compress2_z(Bytef *dest, z_size_t *destLen, const Bytef *source,
                        z_size_t sourceLen, int level);
```

按请求级别，将输入压缩为一个完整 zlib 流。

**定义域。** 受限定义域。

**前置条件。** 上述受限缓冲区定义域。`source` 可在零输入或经检查的拒绝情形中为 NULL。
`destLen` 可在经检查的拒绝情形中为 NULL。`dest` 可在经检查的拒绝情形中为 NULL，
包括下面的零容量情形。有效级别为 -1 和 0–9；-1 选择级别 6。

**后置条件。** `Z_OK` 表示输出是输入的完整 zlib 编码，且 `*destLen` 是其长度。
`Z_BUF_ERROR` 表示容量已由该编码的一个前缀填满。
`Z_MEM_ERROR` 表示分配失败，且没有写入输出。

**效果。** 有状态；适用通用效果。非零输入的 NULL 源、NULL `destLen`，或非零容量的
NULL 目标，会在任何长度写入之前返回 `Z_STREAM_ERROR`。
否则在初始化前清零 `*destLen`。错误级别在任何分配前返回 `Z_STREAM_ERROR`，长度为零。
后续返回会存储已写字节数。

**边缘情形。** NULL 目标配合零容量会进入初始化：若分配失败，返回 `Z_MEM_ERROR`，
否则返回 `Z_STREAM_ERROR`，长度为零。非 NULL 目标配合零容量，在成功初始化后返回
`Z_BUF_ERROR`。空输入有效。

## compress2

```c
int ZEXPORT compress2(Bytef *dest, uLongf *destLen, const Bytef *source,
                      uLong sourceLen, int level);
```

[compress2_z](#compress2_z) 的 `uLong` 形式。

**定义域。** 受限定义域。

**前置条件。** `compress2_z` 的受限定义域，且 `destLen` 单元非 NULL。
包装函数会先读取该单元，再调用带检查的 `_z` 入口。

**后置条件。** 编码和返回码契约与 `compress2_z` 相同。

**效果。** 有状态；缓冲区和清理效果相同。
包装函数在每次返回时写回长度，包括错误返回。
早期参数拒绝保持其原值；无效级别或分配失败使其为零。

## compress_z

```c
int ZEXPORT compress_z(Bytef *dest, z_size_t *destLen, const Bytef *source, z_size_t sourceLen);
```

按默认级别压缩（-1，选择级别 6）。

**定义域。** 受限定义域。

**前置条件。** [compress2_z](#compress2_z) 的受限定义域，不包含级别参数。

**后置条件。** 与默认级别的 `compress2_z` 相同。

**效果。** 有状态；长度写入、经检查的 NULL 情形及完整清理相同。

## compress

```c
int ZEXPORT compress(Bytef *dest, uLongf *destLen, const Bytef *source, uLong sourceLen);
```

默认级别的 `uLong` 压缩入口。

**定义域。** 受限定义域。

**前置条件。** [compress2](#compress2) 的受限定义域；`destLen` 必须非 NULL。

**后置条件。** 与级别 -1 的 `compress2` 相同。

**效果。** 有状态；长度写入和完整清理与 `compress2` 相同。

## compressBound_z

```c
z_size_t ZEXPORT compressBound_z(z_size_t sourceLen);
```

计算为默认 zlib 压缩缓冲区确定容量所用的数值上界。

**定义域。** 完整类型定义域。

**前置条件。** 完整类型定义域：每个 64 位 `sourceLen`，包括零和最大值。

**后置条件。** 对 `n = sourceLen`，返回
`min(2^64 - 1, n + (n >> 12) + (n >> 14) + (n >> 25) + 13)`，其中和按数学整数解释。
零得到 13；和溢出时得到最大值。

**效果。** 纯计算。没有指针访问、分配、状态变化或错误返回。

**范围。** 本契约规定数值。输出容量充分性是另一个性质，针对使用默认包装、
窗口和内存设置的有效压缩调用。它不为任意 raw 或 gzip 流设置给出上界。

## compressBound

```c
uLong ZEXPORT compressBound(uLong sourceLen);
```

数值上界的 `uLong` 形式。

**定义域。** 完整类型定义域。

**前置条件。** 完整类型定义域：每个 64 位 `sourceLen`。

**后置条件。** 此构建下，公式与饱和规则和 [compressBound_z](#compressbound_z) 相同。

**效果。** 纯计算。没有内存访问或错误返回。输出容量充分性的范围也相同。

## uncompress2_z

```c
int ZEXPORT uncompress2_z(Bytef *dest, z_size_t *destLen, const Bytef *source, z_size_t *sourceLen);
```

解码第一个 zlib 流，并报告输出大小和输入消费量。

**定义域。** 受限定义域。

**前置条件。** 上述受限缓冲区定义域。`*sourceLen` 是可用输入量，`*destLen` 是输出容量。
任一长度指针都可在经检查的拒绝情形中为 NULL。
数据指针仅可在对应长度为零，或经检查的拒绝情形中为 NULL。
错误情形包括畸形、截断、raw、gzip 和依赖字典的输入。

**后置条件。** `Z_OK` 表示完整且通过检查的 zlib 流被解码到输出。
尾随输入未使用。`Z_BUF_ERROR` 表示输出已填满容量，且仍有输入。
`Z_DATA_ERROR` 包括畸形或不完整输入，以及需要预置字典的情形。
`Z_MEM_ERROR` 表示分配失败，且可能发生在部分输出之后。

**效果。** 有状态；适用通用效果。参数检查先于初始化：NULL `sourceLen`、
非空输入的 NULL 源、NULL `destLen`，或正容量的 NULL 目标，返回 `Z_STREAM_ERROR`，
并保持两个已有长度单元不变。初始化失败也保持两个长度不变，且不写输出。
初始化后，每次返回都会在 `*sourceLen` 存储已消费字节数，在 `*destLen` 存储已产生
字节数，包括后续内存失败。此前写入的输出仍可用。

**边缘情形。** NULL 目标配合零容量时，使用私有输出指针，因而可以接受；
完整空流可以成功。空输入在成功初始化后是数据错误。
最终精确映射为：`Z_STREAM_END` 到 `Z_OK`，`Z_NEED_DICT` 到 `Z_DATA_ERROR`，
无剩余输入时 `Z_BUF_ERROR` 到 `Z_DATA_ERROR`。其他解码器返回码保留。

## uncompress2

```c
int ZEXPORT uncompress2(Bytef *dest, uLongf *destLen, const Bytef *source, uLong *sourceLen);
```

报告输入消费量的 `uLong` 解码入口。

**定义域。** 受限定义域。

**前置条件。** [uncompress2_z](#uncompress2_z) 的受限定义域，且两个长度单元均非 NULL，
因为包装函数会在 `_z` 检查前读取它们。

**后置条件。** 解码、返回码和已消费计数与 `uncompress2_z` 相同。

**效果。** 有状态；输出和清理效果相同。每次返回都写回两个长度，包括错误返回。
参数拒绝和初始化失败保持其值不变。

## uncompress_z

```c
int ZEXPORT uncompress_z(Bytef *dest, z_size_t *destLen, const Bytef *source, z_size_t sourceLen);
```

解码，但不公开已消费输入计数。

**定义域。** 受限定义域。

**前置条件。** [uncompress2_z](#uncompress2_z) 的受限定义域；`sourceLen` 按值传递。
`destLen` 可在经检查的拒绝情形中为 NULL。

**后置条件。** 输出和返回码与 `uncompress2_z` 相同。
忽略尾随字节；调用者得不到用于定位它们的计数。

**效果。** 有状态；输出长度写入和完整清理相同。已消费计数为局部值。

## uncompress

```c
int ZEXPORT uncompress(Bytef *dest, uLongf *destLen, const Bytef *source, uLong sourceLen);
```

不报告已消费输入计数的 `uLong` 解码入口。

**定义域。** 受限定义域。

**前置条件。** [uncompress2](#uncompress2) 的受限缓冲区定义域，且 `destLen` 非 NULL。

**后置条件。** 输出和返回码与 `uncompress2` 相同；忽略尾随输入。

**效果。** 有状态；输出长度写入、部分输出保留和完整清理相同。

## zlibVersion

```c
const char * ZEXPORT zlibVersion(void);
```

返回已链接库的发布版本字符串。

**定义域。** 完整类型定义域。

**前置条件。** 完整类型定义域；不需要参数或调用者状态。

**后置条件。** 返回非 NULL 指针，指向以 NUL 结尾的 `ZLIB_VERSION`（`1.3.2.1-motley`）。

**效果。** 只读。结果是借用的不可变静态存储；调用者不得写入或释放。
不发生分配或堆变化。

## zlibCompileFlags

```c
uLong ZEXPORT zlibCompileFlags(void);
```

报告构建的类型大小和编译期选项。

**定义域。** 完整类型定义域。

**前置条件。** 完整类型定义域；不需要参数或调用者状态。

**后置条件。** 此构建返回 169（`0xa9`）：`uInt` 为 4 字节；`uLong`、指针和
`z_off_t` 为 8 字节。相应的双位字段将大小 2、4、8 和其他分别编码为 0、1、2 和 3。
所选构建的其他标志为零。

**效果。** 纯标量查询。没有分配、内存写入或错误返回。

## zError

```c
const char * ZEXPORT zError(int err);
```

返回 zlib 结果码对应的文本。

**定义域。** 完整类型定义域。

**前置条件。** 完整类型定义域：每个 `int`，包括最小和最大值。

**后置条件。** 返回非 NULL 指针，指向下列以 NUL 结尾的文本。

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
| 0 或任意其他值 | 空字符串 |

**效果。** 只读。结果是借用的不可变静态存储；不得写入或释放。
没有分配、堆变化或错误返回。索引计算前会检查 -6–2 范围外的值，
因此两个标量极值均安全返回空文本。

[返回 API 手册](README.md) · [契约约定](contracts.md)
