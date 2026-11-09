<!-- source-sha256: 33fcde440928c400dc852d8acc07efa7139001810bb56cd423eeec0335a96b68 -->

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
本页契约不会缩小
[Utilities.lean](../../../ZlibF/Spec/Public/Utilities.lean) 和
[Queries.lean](../../../ZlibF/Spec/Public/Queries.lean) 中登记的目标。
[Calls.lean](../../../ZlibF/Spec/Public/Calls.lean) 固定翻译后的参数和结果。
定义域和效果标签见[契约约定](contracts.md)；证明状态和剩余工作见[进度](../../progress.md)。
超出聚焦前提只表示本契约不作保证，不自动等于 C 未定义行为（UB），也不保证一定返回错误码。

缓冲区工具使用 zlib 包装和默认设置，创建并释放一个局部流。

先看输入／输出长度的约定：`sourceLen` 指定可读输入的字节数；`*destLen` 在调用前是目标数组的可写容量，调用后改为实际写入量。例如目标有 1000 字节容量、最终写入 120 字节，调用前应设置 `*destLen = 1000`，成功返回后读取到 120。这个长度单元自身也是需要保持存活、可读写的调用者存储。`uncompress2_z` 的 `*sourceLen` 同样在调用前给出输入容量，返回后报告已消费量。

查询上界的函数只计算一个数，并不替调用者分配目标数组。

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
这些要求适用于每一条所述返回路径，包括分配失败和部分输出之后的清理。

## compress2_z

```c
int ZEXPORT compress2_z(Bytef *dest, z_size_t *destLen, const Bytef *source,
                        z_size_t sourceLen, int level);
```

按请求级别，将输入压缩为一个完整 zlib 流。

### 返回值与后续调用 {#api-compress2_z-returns}

**返回值类型。** `int` — zlib 状态码；输出长度另行写回

状态码说明整个缓冲区是否已压成完整 zlib 流。字节数在 `*destLen` 中。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**完整压缩完成** | 输出是完整的 zlib 编码；`*destLen` 是写入字节数。 | 使用恰好 `*destLen` 字节作为压缩结果。 |
| `Z_BUF_ERROR`<br>**输出容量耗尽** | 容量由编码前缀填满；非 NULL 目标配合零容量在成功初始化后也返回此码。`*destLen` 报告已写字节数。 | 若从原始输入完整重试，先把 `*destLen` 重新设为目标容量。为完整结果提供更大目标缓冲区，从原输入重新调用；此前缀不是完整流。 |
| `Z_MEM_ERROR`<br>**分配失败且无输出** | 通过早期参数检查且级别有效后，初始化分配失败。没有写入输出；`*destLen` 为零。 | 若从原始输入完整重试，先把 `*destLen` 重新设为目标容量。仅在资源允许时重新发起完整调用；本次没有压缩结果。 |
| `Z_STREAM_ERROR`<br>**早期参数拒绝** | source 为 NULL 且 sourceLen > 0，或 dest 为 NULL 且原始容量 > 0。 destLen == NULL 也在检查中拒绝。 返回前不更改现有长度值。 | 修正已拒绝的参数，再用有效缓冲区重新调用。 |
| `Z_STREAM_ERROR`<br>**无效压缩级别** | 通过早期参数检查后，level 不在 -1 或 0–9 中；分配前将 `*destLen` 置零。 | 选择 -1 或 0–9，并为新调用重新设置输出容量。 |
| `Z_STREAM_ERROR`<br>**零容量 NULL 目标** | 通过早期参数检查且级别有效，dest == NULL 且容量为零，初始化成功；`*destLen` 为零。初始化分配失败则返回 Z_MEM_ERROR。 | 提供有效目标和足够容量，再重新调用。 |

**判读要点。**

- 调用前 `*destLen` 是容量；返回后除早期拒绝外是实际写入量。所有内部分配在每条返回路径上均释放。
- destLen 可为 NULL 以触发经检查的拒绝；非 NULL 长度单元须可读写。
- 输入、目标及长度单元必须互相分离并覆盖所述范围。空输入有效。 -1 选择级别 6。

### 调用条件与状态效果 {#api-compress2_z-contract}

**定义域。** 受限定义域。

**前置条件。** 上述受限缓冲区定义域。`source` 可在零输入或经检查的拒绝情形中为 NULL。
`destLen` 可在经检查的拒绝情形中为 NULL。`dest` 可在经检查的拒绝情形中为 NULL，
包括下面的零容量情形。有效级别为 -1 和 0–9；-1 选择级别 6。

**效果。** 有状态；适用通用效果。非零输入的 NULL 源、NULL `destLen`，或非零容量的
NULL 目标，会在任何长度写入之前返回 `Z_STREAM_ERROR`。
否则在初始化前清零 `*destLen`。错误级别在任何分配前返回 `Z_STREAM_ERROR`，长度为零。
后续返回会存储已写字节数。

<details markdown="1" class="ar-return-exact" data-return-exact="compress2_z"><summary>完整返回条件与边界</summary>

**后置条件。** `Z_OK` 表示输出是输入的完整 zlib 编码，且 `*destLen` 是其长度。
`Z_BUF_ERROR` 表示容量已由该编码的一个前缀填满。
`Z_MEM_ERROR` 表示分配失败，且没有写入输出。

**边缘情形。** NULL 目标配合零容量会进入初始化：若分配失败，返回 `Z_MEM_ERROR`，
否则返回 `Z_STREAM_ERROR`，长度为零。非 NULL 目标配合零容量，在成功初始化后返回
`Z_BUF_ERROR`。空输入有效。

</details>

## compress2

```c
int ZEXPORT compress2(Bytef *dest, uLongf *destLen, const Bytef *source,
                      uLong sourceLen, int level);
```

[compress2_z](#compress2_z) 的 `uLong` 形式。

### 返回值与后续调用 {#api-compress2-returns}

**返回值类型。** `int` — zlib 状态码；输出长度另行写回

状态码说明整个缓冲区是否已压成完整 zlib 流。字节数在 `*destLen` 中。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**完整压缩完成** | 输出是完整的 zlib 编码；`*destLen` 是写入字节数。 | 使用恰好 `*destLen` 字节作为压缩结果。 |
| `Z_BUF_ERROR`<br>**输出容量耗尽** | 容量由编码前缀填满；非 NULL 目标配合零容量在成功初始化后也返回此码。`*destLen` 报告已写字节数。 | 若从原始输入完整重试，先把 `*destLen` 重新设为目标容量。为完整结果提供更大目标缓冲区，从原输入重新调用；此前缀不是完整流。 |
| `Z_MEM_ERROR`<br>**分配失败且无输出** | 通过早期参数检查且级别有效后，初始化分配失败。没有写入输出；`*destLen` 为零。 | 若从原始输入完整重试，先把 `*destLen` 重新设为目标容量。仅在资源允许时重新发起完整调用；本次没有压缩结果。 |
| `Z_STREAM_ERROR`<br>**早期参数拒绝** | source 为 NULL 且 sourceLen > 0，或 dest 为 NULL 且原始容量 > 0。 返回前不更改现有长度值。 | 修正已拒绝的参数，再用有效缓冲区重新调用。 |
| `Z_STREAM_ERROR`<br>**无效压缩级别** | 通过早期参数检查后，level 不在 -1 或 0–9 中；分配前将 `*destLen` 置零。 | 选择 -1 或 0–9，并为新调用重新设置输出容量。 |
| `Z_STREAM_ERROR`<br>**零容量 NULL 目标** | 通过早期参数检查且级别有效，dest == NULL 且容量为零，初始化成功；`*destLen` 为零。初始化分配失败则返回 Z_MEM_ERROR。 | 提供有效目标和足够容量，再重新调用。 |

**判读要点。**

- 调用前 `*destLen` 是容量；返回后除早期拒绝外是实际写入量。所有内部分配在每条返回路径上均释放。
- 普通适配器先读取非 NULL 的 destLen 单元，且每次返回都写回长度；NULL destLen 不在此前提内。
- 输入、目标及长度单元必须互相分离并覆盖所述范围。空输入有效。 -1 选择级别 6。

### 调用条件与状态效果 {#api-compress2-contract}

**定义域。** 受限定义域。

**前置条件。** `compress2_z` 的受限定义域，且 `destLen` 单元非 NULL。
包装函数会先读取该单元，再调用带检查的 `_z` 入口。

**效果。** 有状态；缓冲区和清理效果相同。
包装函数在每次返回时写回长度，包括错误返回。
早期参数拒绝保持其原值；无效级别或分配失败使其为零。

<details markdown="1" class="ar-return-exact" data-return-exact="compress2"><summary>完整返回条件与边界</summary>

**后置条件。** 编码和返回码契约与 `compress2_z` 相同。

</details>

## compress_z

```c
int ZEXPORT compress_z(Bytef *dest, z_size_t *destLen, const Bytef *source, z_size_t sourceLen);
```

按默认级别压缩（-1，选择级别 6）。

### 返回值与后续调用 {#api-compress_z-returns}

**返回值类型。** `int` — zlib 状态码；输出长度另行写回

状态码说明整个缓冲区是否已压成完整 zlib 流。字节数在 `*destLen` 中。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**完整压缩完成** | 输出是完整的 zlib 编码；`*destLen` 是写入字节数。 | 使用恰好 `*destLen` 字节作为压缩结果。 |
| `Z_BUF_ERROR`<br>**输出容量耗尽** | 容量由编码前缀填满；非 NULL 目标配合零容量在成功初始化后也返回此码。`*destLen` 报告已写字节数。 | 若从原始输入完整重试，先把 `*destLen` 重新设为目标容量。为完整结果提供更大目标缓冲区，从原输入重新调用；此前缀不是完整流。 |
| `Z_MEM_ERROR`<br>**分配失败且无输出** | 通过早期参数检查后，初始化分配失败。没有写入输出；`*destLen` 为零。 | 若从原始输入完整重试，先把 `*destLen` 重新设为目标容量。仅在资源允许时重新发起完整调用；本次没有压缩结果。 |
| `Z_STREAM_ERROR`<br>**早期参数拒绝** | source 为 NULL 且 sourceLen > 0，或 dest 为 NULL 且原始容量 > 0。 destLen == NULL 也在检查中拒绝。 返回前不更改现有长度值。 | 修正已拒绝的参数，再用有效缓冲区重新调用。 |
| `Z_STREAM_ERROR`<br>**零容量 NULL 目标** | 通过早期参数检查，dest == NULL 且容量为零，初始化成功；`*destLen` 为零。初始化分配失败则返回 Z_MEM_ERROR。 | 提供有效目标和足够容量，再重新调用。 |

**判读要点。**

- 调用前 `*destLen` 是容量；返回后除早期拒绝外是实际写入量。所有内部分配在每条返回路径上均释放。
- destLen 可为 NULL 以触发经检查的拒绝；非 NULL 长度单元须可读写。
- 输入、目标及长度单元必须互相分离并覆盖所述范围。空输入有效。 使用默认级别 -1，即级别 6。

### 调用条件与状态效果 {#api-compress_z-contract}

**定义域。** 受限定义域。

**前置条件。** [compress2_z](#compress2_z) 的受限定义域，不包含级别参数。

**效果。** 有状态；长度写入、经检查的 NULL 情形及完整清理相同。

<details markdown="1" class="ar-return-exact" data-return-exact="compress_z"><summary>完整返回条件与边界</summary>

**后置条件。** 与默认级别的 `compress2_z` 相同。

</details>

## compress

```c
int ZEXPORT compress(Bytef *dest, uLongf *destLen, const Bytef *source, uLong sourceLen);
```

默认级别的 `uLong` 压缩入口。

### 返回值与后续调用 {#api-compress-returns}

**返回值类型。** `int` — zlib 状态码；输出长度另行写回

状态码说明整个缓冲区是否已压成完整 zlib 流。字节数在 `*destLen` 中。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**完整压缩完成** | 输出是完整的 zlib 编码；`*destLen` 是写入字节数。 | 使用恰好 `*destLen` 字节作为压缩结果。 |
| `Z_BUF_ERROR`<br>**输出容量耗尽** | 容量由编码前缀填满；非 NULL 目标配合零容量在成功初始化后也返回此码。`*destLen` 报告已写字节数。 | 若从原始输入完整重试，先把 `*destLen` 重新设为目标容量。为完整结果提供更大目标缓冲区，从原输入重新调用；此前缀不是完整流。 |
| `Z_MEM_ERROR`<br>**分配失败且无输出** | 通过早期参数检查后，初始化分配失败。没有写入输出；`*destLen` 为零。 | 若从原始输入完整重试，先把 `*destLen` 重新设为目标容量。仅在资源允许时重新发起完整调用；本次没有压缩结果。 |
| `Z_STREAM_ERROR`<br>**早期参数拒绝** | source 为 NULL 且 sourceLen > 0，或 dest 为 NULL 且原始容量 > 0。 返回前不更改现有长度值。 | 修正已拒绝的参数，再用有效缓冲区重新调用。 |
| `Z_STREAM_ERROR`<br>**零容量 NULL 目标** | 通过早期参数检查，dest == NULL 且容量为零，初始化成功；`*destLen` 为零。初始化分配失败则返回 Z_MEM_ERROR。 | 提供有效目标和足够容量，再重新调用。 |

**判读要点。**

- 调用前 `*destLen` 是容量；返回后除早期拒绝外是实际写入量。所有内部分配在每条返回路径上均释放。
- 普通适配器先读取非 NULL 的 destLen 单元，且每次返回都写回长度；NULL destLen 不在此前提内。
- 输入、目标及长度单元必须互相分离并覆盖所述范围。空输入有效。 使用默认级别 -1，即级别 6。

### 调用条件与状态效果 {#api-compress-contract}

**定义域。** 受限定义域。

**前置条件。** [compress2](#compress2) 的受限定义域；`destLen` 必须非 NULL。

**效果。** 有状态；长度写入和完整清理与 `compress2` 相同。

<details markdown="1" class="ar-return-exact" data-return-exact="compress"><summary>完整返回条件与边界</summary>

**后置条件。** 与级别 -1 的 `compress2` 相同。

</details>

## compressBound_z

```c
z_size_t ZEXPORT compressBound_z(z_size_t sourceLen);
```

计算为默认 zlib 压缩缓冲区确定容量所用的数值上界。

### 返回值与后续调用 {#api-compressbound_z-returns}

**返回值类型。** `z_size_t` — 饱和的压缩容量数值

计算默认压缩设置使用的容量数值，不分配缓冲区。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `min(2^64 - 1, n + (n >> 12) + (n >> 14) + (n >> 25) + 13)`<br>**容量数值** | n = sourceLen，可取任意 64 位无符号值；按数学整数求和，再饱和至最大值。n == 0 时返回 13。 | 将数值用于规划有效目标缓冲区容量。 |

**判读要点。**

- 这是数值契约，无错误返回。输出足够大是单独性质，限定默认 zlib 包装、窗口和内存设置；不适用于任意 raw 或 gzip 设置。

### 调用条件与状态效果 {#api-compressbound_z-contract}

**定义域。** 完整类型定义域。

**前置条件。** 完整类型定义域：每个 64 位 `sourceLen`，包括零和最大值。

**效果。** 纯计算。没有指针访问、分配、状态变化或错误返回。

**范围。** 本契约规定数值。输出容量充分性是另一个性质，针对使用默认包装、
窗口和内存设置的有效压缩调用。它不为任意 raw 或 gzip 流设置给出上界。

<details markdown="1" class="ar-return-exact" data-return-exact="compressBound_z"><summary>完整返回条件与边界</summary>

**后置条件。** 对 `n = sourceLen`，返回
`min(2^64 - 1, n + (n >> 12) + (n >> 14) + (n >> 25) + 13)`，其中和按数学整数解释。
零得到 13；和溢出时得到最大值。这里 `n` 是输入字节数；`n >> k` 表示将无符号数右移 k 位，即取 `n / 2^k` 的整数部分。三个额外项和常数 13 计入默认压缩安排的额外空间，最后的 `min` 将数值截在类型最大值。

</details>

## compressBound

```c
uLong ZEXPORT compressBound(uLong sourceLen);
```

数值上界的 `uLong` 形式。

### 返回值与后续调用 {#api-compressbound-returns}

**返回值类型。** `uLong` — 饱和的压缩容量数值

计算默认压缩设置使用的容量数值，不分配缓冲区。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `min(2^64 - 1, n + (n >> 12) + (n >> 14) + (n >> 25) + 13)`<br>**容量数值** | n = sourceLen，可取任意 64 位无符号值；按数学整数求和，再饱和至最大值。n == 0 时返回 13。 | 将数值用于规划有效目标缓冲区容量。 |

**判读要点。**

- 这是数值契约，无错误返回。输出足够大是单独性质，限定默认 zlib 包装、窗口和内存设置；不适用于任意 raw 或 gzip 设置。

### 调用条件与状态效果 {#api-compressbound-contract}

**定义域。** 完整类型定义域。

**前置条件。** 完整类型定义域：每个 64 位 `sourceLen`。

**效果。** 纯计算。没有内存访问或错误返回。输出容量充分性的范围也相同。

<details markdown="1" class="ar-return-exact" data-return-exact="compressBound"><summary>完整返回条件与边界</summary>

**后置条件。** 此构建下，公式与饱和规则和 [compressBound_z](#compressbound_z) 相同。

</details>

## uncompress2_z

```c
int ZEXPORT uncompress2_z(Bytef *dest, z_size_t *destLen, const Bytef *source, z_size_t *sourceLen);
```

解码第一个 zlib 流，并报告输出大小和输入消费量。

### 返回值与后续调用 {#api-uncompress2_z-returns}

**返回值类型。** `int` — zlib 状态码；计数由长度参数报告

状态码说明第一个 zlib 流是否完整解码。长度值报告输出及输入消费量。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**完整解码完成** | 第一个 zlib 流已完整解码且校验通过；`*destLen` 报告已写字节数，`*sourceLen` 报告已消费字节数。尾随输入未使用。 | 使用恰好 `*destLen` 字节的输出。可根据 `*sourceLen` 定位未使用的输入。 |
| `Z_BUF_ERROR`<br>**输出已满且仍有输入** | 输出填满容量且仍有输入；`*destLen` 报告已写字节数，`*sourceLen` 报告已消费字节数。已写输出保持可用。 | 若从原始输入完整重试，先把 `*destLen` 重新设为目标容量，并把 `*sourceLen` 重新设为完整输入长度。若需完整结果，扩大目标容量并从原始输入重新调用；该工具不返回可续用的流。 |
| `Z_DATA_ERROR`<br>**数据、输入完整性或字典错误** | 输入格式错误或不完整，或需要预设字典；raw、gzip 输入也在错误范围内。成功初始化后的空输入亦为数据错误。输出已满但输入耗尽的 Z_BUF_ERROR 也映射为此码。 | 不要把部分输出视为已校验的完整结果；检查格式、输入完整性及字典需求，改用合适的调用。 |
| `Z_MEM_ERROR`<br>**初始化分配失败** | 初始化失败；现有长度值均不变，未写入输出。 | 若从原始输入完整重试，先把 `*destLen` 重新设为目标容量，并把 `*sourceLen` 重新设为完整输入长度。资源允许时可从原输入重新发起完整调用，并重新提供容量。 |
| `Z_MEM_ERROR`<br>**解码期间分配失败** | 成功初始化后分配失败，可能已有部分输出；`*destLen` 报告已写字节数，`*sourceLen` 报告已消费字节数。 | 若从原始输入完整重试，先把 `*destLen` 重新设为目标容量，并把 `*sourceLen` 重新设为完整输入长度。保留需要的已写字节；它们不是已完整校验的结果。新调用须从原输入开始并重新设置容量。 |
| `Z_STREAM_ERROR`<br>**初始化前参数拒绝** | 非空输入的 NULL source，或正容量的 NULL dest，或 NULL destLen 或 NULL sourceLen，会在初始化前被拒绝；现有长度值均不变。 | 修正已拒绝的参数，再重新调用。 |

**判读要点。**

- 成功初始化后，每次返回都写入实际计数，包括后续内存失败；已写输出仍可读取。每条返回路径均释放所有内部分配。
- 长度指针允许 NULL 以触发经检查的拒绝；非 NULL 单元须可读写。
- 输入、目标及长度单元互相分离。NULL 目标配合零容量可使用私有输出指针接受完整空流。内部 Z_STREAM_END 映射为 Z_OK，Z_NEED_DICT 映射为 Z_DATA_ERROR，其他解码码保持不变。

### 调用条件与状态效果 {#api-uncompress2_z-contract}

**定义域。** 受限定义域。

**前置条件。** 上述受限缓冲区定义域。`*sourceLen` 是可用输入量，`*destLen` 是输出容量。
任一长度指针都可在经检查的拒绝情形中为 NULL。
数据指针仅可在对应长度为零，或经检查的拒绝情形中为 NULL。
错误情形包括畸形、截断、raw、gzip 和依赖字典的输入。

**效果。** 有状态；适用通用效果。参数检查先于初始化：NULL `sourceLen`、
非空输入的 NULL 源、NULL `destLen`，或正容量的 NULL 目标，返回 `Z_STREAM_ERROR`，
并保持两个已有长度单元不变。初始化失败也保持两个长度不变，且不写输出。
初始化后，每次返回都会在 `*sourceLen` 存储已消费字节数，在 `*destLen` 存储已产生
字节数，包括后续内存失败。此前写入的输出仍可用。

<details markdown="1" class="ar-return-exact" data-return-exact="uncompress2_z"><summary>完整返回条件与边界</summary>

**后置条件。** `Z_OK` 表示完整且通过检查的 zlib 流被解码到输出。
尾随输入未使用。`Z_BUF_ERROR` 表示输出已填满容量，且仍有输入。
`Z_DATA_ERROR` 包括畸形或不完整输入，以及需要预置字典的情形。
`Z_MEM_ERROR` 表示分配失败，且可能发生在部分输出之后。

**边缘情形。** NULL 目标配合零容量时，使用私有输出指针，因而可以接受；
完整空流可以成功。空输入在成功初始化后是数据错误。
最终精确映射为：`Z_STREAM_END` 到 `Z_OK`，`Z_NEED_DICT` 到 `Z_DATA_ERROR`，
无剩余输入时 `Z_BUF_ERROR` 到 `Z_DATA_ERROR`。其他解码器返回码保留。

</details>

## uncompress2

```c
int ZEXPORT uncompress2(Bytef *dest, uLongf *destLen, const Bytef *source, uLong *sourceLen);
```

报告输入消费量的 `uLong` 解码入口。

### 返回值与后续调用 {#api-uncompress2-returns}

**返回值类型。** `int` — zlib 状态码；计数由长度参数报告

状态码说明第一个 zlib 流是否完整解码。长度值报告输出及输入消费量。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**完整解码完成** | 第一个 zlib 流已完整解码且校验通过；`*destLen` 报告已写字节数，`*sourceLen` 报告已消费字节数。尾随输入未使用。 | 使用恰好 `*destLen` 字节的输出。可根据 `*sourceLen` 定位未使用的输入。 |
| `Z_BUF_ERROR`<br>**输出已满且仍有输入** | 输出填满容量且仍有输入；`*destLen` 报告已写字节数，`*sourceLen` 报告已消费字节数。已写输出保持可用。 | 若从原始输入完整重试，先把 `*destLen` 重新设为目标容量，并把 `*sourceLen` 重新设为完整输入长度。若需完整结果，扩大目标容量并从原始输入重新调用；该工具不返回可续用的流。 |
| `Z_DATA_ERROR`<br>**数据、输入完整性或字典错误** | 输入格式错误或不完整，或需要预设字典；raw、gzip 输入也在错误范围内。成功初始化后的空输入亦为数据错误。输出已满但输入耗尽的 Z_BUF_ERROR 也映射为此码。 | 不要把部分输出视为已校验的完整结果；检查格式、输入完整性及字典需求，改用合适的调用。 |
| `Z_MEM_ERROR`<br>**初始化分配失败** | 初始化失败；现有长度值均不变，未写入输出。 | 若从原始输入完整重试，先把 `*destLen` 重新设为目标容量，并把 `*sourceLen` 重新设为完整输入长度。资源允许时可从原输入重新发起完整调用，并重新提供容量。 |
| `Z_MEM_ERROR`<br>**解码期间分配失败** | 成功初始化后分配失败，可能已有部分输出；`*destLen` 报告已写字节数，`*sourceLen` 报告已消费字节数。 | 若从原始输入完整重试，先把 `*destLen` 重新设为目标容量，并把 `*sourceLen` 重新设为完整输入长度。保留需要的已写字节；它们不是已完整校验的结果。新调用须从原输入开始并重新设置容量。 |
| `Z_STREAM_ERROR`<br>**初始化前参数拒绝** | 非空输入的 NULL source，或正容量的 NULL dest，会在初始化前被拒绝；现有长度值均不变。 | 修正已拒绝的参数，再重新调用。 |

**判读要点。**

- 成功初始化后，每次返回都写入实际计数，包括后续内存失败；已写输出仍可读取。每条返回路径均释放所有内部分配。
- 普通适配器会先读取长度单元：destLen 和 sourceLen 均须非 NULL。两者每次返回都会写回。
- 输入、目标及长度单元互相分离。NULL 目标配合零容量可使用私有输出指针接受完整空流。内部 Z_STREAM_END 映射为 Z_OK，Z_NEED_DICT 映射为 Z_DATA_ERROR，其他解码码保持不变。

### 调用条件与状态效果 {#api-uncompress2-contract}

**定义域。** 受限定义域。

**前置条件。** [uncompress2_z](#uncompress2_z) 的受限定义域，且两个长度单元均非 NULL，
因为包装函数会在 `_z` 检查前读取它们。

**效果。** 有状态；输出和清理效果相同。每次返回都写回两个长度，包括错误返回。
参数拒绝和初始化失败保持其值不变。

<details markdown="1" class="ar-return-exact" data-return-exact="uncompress2"><summary>完整返回条件与边界</summary>

**后置条件。** 解码、返回码和已消费计数与 `uncompress2_z` 相同。

</details>

## uncompress_z

```c
int ZEXPORT uncompress_z(Bytef *dest, z_size_t *destLen, const Bytef *source, z_size_t sourceLen);
```

解码，但不公开已消费输入计数。

### 返回值与后续调用 {#api-uncompress_z-returns}

**返回值类型。** `int` — zlib 状态码；计数由长度参数报告

状态码说明第一个 zlib 流是否完整解码。长度值报告输出，不报告输入消费量。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**完整解码完成** | 第一个 zlib 流已完整解码且校验通过；`*destLen` 报告已写字节数；已消费输入计数不向调用者公开。尾随输入未使用。 | 使用恰好 `*destLen` 字节的输出。此入口没有计数可用来定位尾随输入。 |
| `Z_BUF_ERROR`<br>**输出已满且仍有输入** | 输出填满容量且仍有输入；`*destLen` 报告已写字节数；已消费输入计数不向调用者公开。已写输出保持可用。 | 若从原始输入完整重试，先把 `*destLen` 重新设为目标容量。若需完整结果，扩大目标容量并从原始输入重新调用；该工具不返回可续用的流。 |
| `Z_DATA_ERROR`<br>**数据、输入完整性或字典错误** | 输入格式错误或不完整，或需要预设字典；raw、gzip 输入也在错误范围内。成功初始化后的空输入亦为数据错误。输出已满但输入耗尽的 Z_BUF_ERROR 也映射为此码。 | 不要把部分输出视为已校验的完整结果；检查格式、输入完整性及字典需求，改用合适的调用。 |
| `Z_MEM_ERROR`<br>**初始化分配失败** | 初始化失败；现有长度值均不变，未写入输出。 | 若从原始输入完整重试，先把 `*destLen` 重新设为目标容量。资源允许时可从原输入重新发起完整调用，并重新提供容量。 |
| `Z_MEM_ERROR`<br>**解码期间分配失败** | 成功初始化后分配失败，可能已有部分输出；`*destLen` 报告已写字节数；已消费输入计数不向调用者公开。 | 若从原始输入完整重试，先把 `*destLen` 重新设为目标容量。保留需要的已写字节；它们不是已完整校验的结果。新调用须从原输入开始并重新设置容量。 |
| `Z_STREAM_ERROR`<br>**初始化前参数拒绝** | 非空输入的 NULL source，或正容量的 NULL dest，或 NULL destLen，会在初始化前被拒绝；现有长度值均不变。 | 修正已拒绝的参数，再重新调用。 |

**判读要点。**

- 成功初始化后，每次返回都写入实际计数，包括后续内存失败；已写输出仍可读取。每条返回路径均释放所有内部分配。
- 长度指针允许 NULL 以触发经检查的拒绝；非 NULL 单元须可读写。
- 输入、目标及长度单元互相分离。NULL 目标配合零容量可使用私有输出指针接受完整空流。内部 Z_STREAM_END 映射为 Z_OK，Z_NEED_DICT 映射为 Z_DATA_ERROR，其他解码码保持不变。

### 调用条件与状态效果 {#api-uncompress_z-contract}

**定义域。** 受限定义域。

**前置条件。** [uncompress2_z](#uncompress2_z) 的受限定义域；`sourceLen` 按值传递。
`destLen` 可在经检查的拒绝情形中为 NULL。

**效果。** 有状态；输出长度写入和完整清理相同。已消费计数为局部值。

<details markdown="1" class="ar-return-exact" data-return-exact="uncompress_z"><summary>完整返回条件与边界</summary>

**后置条件。** 输出和返回码与 `uncompress2_z` 相同。
忽略尾随字节；调用者得不到用于定位它们的计数。

</details>

## uncompress

```c
int ZEXPORT uncompress(Bytef *dest, uLongf *destLen, const Bytef *source, uLong sourceLen);
```

不报告已消费输入计数的 `uLong` 解码入口。

### 返回值与后续调用 {#api-uncompress-returns}

**返回值类型。** `int` — zlib 状态码；计数由长度参数报告

状态码说明第一个 zlib 流是否完整解码。长度值报告输出，不报告输入消费量。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `Z_OK`<br>**完整解码完成** | 第一个 zlib 流已完整解码且校验通过；`*destLen` 报告已写字节数；已消费输入计数不向调用者公开。尾随输入未使用。 | 使用恰好 `*destLen` 字节的输出。此入口没有计数可用来定位尾随输入。 |
| `Z_BUF_ERROR`<br>**输出已满且仍有输入** | 输出填满容量且仍有输入；`*destLen` 报告已写字节数；已消费输入计数不向调用者公开。已写输出保持可用。 | 若从原始输入完整重试，先把 `*destLen` 重新设为目标容量。若需完整结果，扩大目标容量并从原始输入重新调用；该工具不返回可续用的流。 |
| `Z_DATA_ERROR`<br>**数据、输入完整性或字典错误** | 输入格式错误或不完整，或需要预设字典；raw、gzip 输入也在错误范围内。成功初始化后的空输入亦为数据错误。输出已满但输入耗尽的 Z_BUF_ERROR 也映射为此码。 | 不要把部分输出视为已校验的完整结果；检查格式、输入完整性及字典需求，改用合适的调用。 |
| `Z_MEM_ERROR`<br>**初始化分配失败** | 初始化失败；现有长度值均不变，未写入输出。 | 若从原始输入完整重试，先把 `*destLen` 重新设为目标容量。资源允许时可从原输入重新发起完整调用，并重新提供容量。 |
| `Z_MEM_ERROR`<br>**解码期间分配失败** | 成功初始化后分配失败，可能已有部分输出；`*destLen` 报告已写字节数；已消费输入计数不向调用者公开。 | 若从原始输入完整重试，先把 `*destLen` 重新设为目标容量。保留需要的已写字节；它们不是已完整校验的结果。新调用须从原输入开始并重新设置容量。 |
| `Z_STREAM_ERROR`<br>**初始化前参数拒绝** | 非空输入的 NULL source，或正容量的 NULL dest，会在初始化前被拒绝；现有长度值均不变。 | 修正已拒绝的参数，再重新调用。 |

**判读要点。**

- 成功初始化后，每次返回都写入实际计数，包括后续内存失败；已写输出仍可读取。每条返回路径均释放所有内部分配。
- 普通适配器会先读取长度单元：destLen 须非 NULL，且每次返回都会写回。
- 输入、目标及长度单元互相分离。NULL 目标配合零容量可使用私有输出指针接受完整空流。内部 Z_STREAM_END 映射为 Z_OK，Z_NEED_DICT 映射为 Z_DATA_ERROR，其他解码码保持不变。

### 调用条件与状态效果 {#api-uncompress-contract}

**定义域。** 受限定义域。

**前置条件。** [uncompress2](#uncompress2) 的受限缓冲区定义域，且 `destLen` 非 NULL。

**效果。** 有状态；输出长度写入、部分输出保留和完整清理相同。

<details markdown="1" class="ar-return-exact" data-return-exact="uncompress"><summary>完整返回条件与边界</summary>

**后置条件。** 输出和返回码与 `uncompress2` 相同；忽略尾随输入。

</details>

## zlibVersion

```c
const char * ZEXPORT zlibVersion(void);
```

返回已链接库的发布版本字符串。

### 返回值与后续调用 {#api-zlibversion-returns}

**返回值类型。** `const char *` — 借用的不可变版本字符串指针

返回实际链接库的版本字符串。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `ZLIB_VERSION`<br>**库版本字符串** | 无参数；返回非 NULL、以 NUL 结尾的 1.3.2.1-motley 字符串。 | 读取此静态字符串；不得写入或释放。 |

### 调用条件与状态效果 {#api-zlibversion-contract}

**定义域。** 完整类型定义域。

**前置条件。** 完整类型定义域；不需要参数或调用者状态。

**效果。** 只读。结果是借用的不可变静态存储；调用者不得写入或释放。
不发生分配或堆变化。

<details markdown="1" class="ar-return-exact" data-return-exact="zlibVersion"><summary>完整返回条件与边界</summary>

**后置条件。** 返回非 NULL 指针，指向以 NUL 结尾的 `ZLIB_VERSION`（`1.3.2.1-motley`）。

</details>

## zlibCompileFlags

```c
uLong ZEXPORT zlibCompileFlags(void);
```

报告构建的类型大小和编译期选项。

### 返回值与后续调用 {#api-zlibcompileflags-returns}

**返回值类型。** `uLong` — 构建信息位字段

返回当前构建的类型大小与编译选项编码。此值不是状态码。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `169 (0xa9)`<br>**当前构建标志** | 本构建的 uInt 为 4 字节，uLong、指针和 z_off_t 为 8 字节；其他标志为零。 | 按位字段读取构建信息；二位大小字段以 0、1、2、3 分别编码 2、4、8、其他字节数。 |

### 调用条件与状态效果 {#api-zlibcompileflags-contract}

**定义域。** 完整类型定义域。

**前置条件。** 完整类型定义域；不需要参数或调用者状态。

**效果。** 纯标量查询。没有分配、内存写入或错误返回。

<details markdown="1" class="ar-return-exact" data-return-exact="zlibCompileFlags"><summary>完整返回条件与边界</summary>

**后置条件。** 此构建返回 169（`0xa9`）：`uInt` 为 4 字节；`uLong`、指针和
`z_off_t` 为 8 字节。相应的双位字段将大小 2、4、8 和其他分别编码为 0、1、2 和 3。
所选构建的其他标志为零。

</details>

## zError

```c
const char * ZEXPORT zError(int err);
```

返回 zlib 结果码对应的文本。

### 返回值与后续调用 {#api-zerror-returns}

**返回值类型。** `const char *` — 借用的不可变错误文本指针

把传入的结果码映射为文本。函数本身总是返回非 NULL 字符串指针。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `"need dictionary"`<br>**需要字典文本** | err == 2。 | 读取借用的静态文本；不得写入或释放。 |
| `"stream end"`<br>**流结束文本** | err == 1。 | 读取借用的静态文本；不得写入或释放。 |
| `"file error"`<br>**文件错误文本** | err == -1。 | 读取借用的静态文本；不得写入或释放。 |
| `"stream error"`<br>**流错误文本** | err == -2。 | 读取借用的静态文本；不得写入或释放。 |
| `"data error"`<br>**数据错误文本** | err == -3。 | 读取借用的静态文本；不得写入或释放。 |
| `"insufficient memory"`<br>**内存不足文本** | err == -4。 | 读取借用的静态文本；不得写入或释放。 |
| `"buffer error"`<br>**缓冲区错误文本** | err == -5。 | 读取借用的静态文本；不得写入或释放。 |
| `"incompatible version"`<br>**版本不兼容文本** | err == -6。 | 读取借用的静态文本；不得写入或释放。 |
| `""`<br>**空文本** | err == 0，或 err 不在 -6–2 范围内，包括 int 的最小值和最大值。 | 按需读取空字符串；这不是 NULL 指针或另一个错误码。 |

**判读要点。**

- 适用于全部 int 值；在索引运算前检查范围。不分配内存或改变堆。

### 调用条件与状态效果 {#api-zerror-contract}

**定义域。** 完整类型定义域。

**前置条件。** 完整类型定义域：每个 `int`，包括最小和最大值。

**效果。** 只读。结果是借用的不可变静态存储；不得写入或释放。
没有分配、堆变化或错误返回。索引计算前会检查 -6–2 范围外的值，
因此两个标量极值均安全返回空文本。

[返回 API 手册](README.md) · [契约约定](contracts.md)

<details markdown="1" class="ar-return-exact" data-return-exact="zError"><summary>完整返回条件与边界</summary>

**后置条件。** 返回非 NULL 指针，指向下列以 NUL 结尾的文本。

| `err` | 返回的原始文本 | 中文含义 |
| --- | --- | --- |
| 2 | `need dictionary` | 需要预置字典 |
| 1 | `stream end` | 流已结束 |
| -1 | `file error` | 文件错误 |
| -2 | `stream error` | 流状态或参数错误 |
| -3 | `data error` | 数据格式或完整性错误 |
| -4 | `insufficient memory` | 内存不足 |
| -5 | `buffer error` | 缓冲区条件不足 |
| -6 | `incompatible version` | 版本不兼容 |
| 0 或任意其他值 | 空字符串 | 无诊断文本 |

</details>
