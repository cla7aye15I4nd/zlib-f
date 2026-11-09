<!-- source-sha256: c8771d0499c6de2c8cba819f5433ba5347c6abdfc262d5f2a4ab13e94236972b -->

# 校验和

[API 手册](README.md) · [契约约定](contracts.md) · [缓冲区工具](utility.md)

逐块计算缓冲区的校验和，或合并独立处理的字节序列的校验和，而不重新读取数据。
下文的字节序列 A 和 B 是普通数据；契约使用这些序列的 Adler-32 或 CRC-32。例如先处理 A，再处理 B，可以把 A 的校验和作为下一次更新的起始值；若 A、B 已在不同位置独立处理，也可以用组合接口得到 A 后接 B 的校验和。

更新函数里的 `buf` 指向这一批输入，`len` 是这一批的字节数，传入的 `adler` 或 `crc` 是继续计算的起始值。组合函数里的 `len2` 则只表示后一段 B 的字节数，不是两段总长度。

| 任务 | 入口 |
| --- | --- |
| 更新 Adler-32 | [大小类型长度](#adler32_z)、[32 位长度](#adler32) |
| 合并 Adler-32 | [普通偏移类型](#adler32_combine)、[显式 64 位偏移类型](#adler32_combine64) |
| 更新 CRC-32 | [大小类型长度](#crc32_z)、[32 位长度](#crc32) |
| 合并 CRC-32 | [普通偏移类型](#crc32_combine)、[显式 64 位偏移类型](#crc32_combine64) |
| 复用 CRC 合并算子 | [生成](#crc32_combine_gen)、[用 64 位长度生成](#crc32_combine_gen64)、[应用](#crc32_combine_op) |
| 查看字节表 | [get_crc_table](#get_crc_table) |

这些聚焦契约对应固定版本源码及登记补丁，在默认 LP64 Linux 静态构建下的
`adler32.c`、`crc32.c` 和 `zlib.h`。
所有校验和入口都不写入状态、不分配或释放内存，也不执行 I/O。
特殊数值结果是普通值，而不是错误码。定义域和效果互相独立，见[契约约定](contracts.md)。
超出聚焦前提只表示本契约不作保证，不自动等于 C 未定义行为（UB），也不保证一定返回错误码。

实用校验和契约使用真实字节序列 A 和 B。各校验和独立计算：Adler-32 从 1 开始，
CRC-32 从 0 开始。这些契约有意不对伪造校验和值作功能保证。
[Lean 目标](../../../ZlibF/Spec/Public/Checksums.lean)还描述任意种子及精确标量结果。
Adler 入口及其 Lean 目标都要求 NULL 初始化查询的长度为零。
见[范围偏差](../../deviations.md)和[公开目标](../../checking/goals.md)。

此构建中，`uLong` 和 `z_size_t` 是无符号 64 位类型；`uInt` 是无符号 32 位类型。
`z_off_t` 和 `z_off64_t` 是有符号 64 位类型。输入校验和值中高于第 31 位的位被忽略；
返回校验和值可用 32 位表示。显式 `*64` 声明取决于头文件的大文件特性宏。

## adler32_z

```c
uLong ZEXPORT adler32_z(uLong adler, const Bytef *buf, z_size_t len);
```

用一段字节更新 Adler-32，或取得初始值。

### 返回值与后续调用 {#api-adler32_z-returns}

**返回值类型。** `uLong` — 32 位校验和值

返回本次更新后的 Adler-32，或新校验和的初始值。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `1`<br>**初始值** | buf == NULL 且 len == 0，任意传入校验和值；不读取字节。 | 以 1 开始处理新序列。 |
| `low32(adler)`<br>**空范围保持原值** | buf 非 NULL 且 len == 0；空范围也允许尾后指针。 | 保留该值，继续下一段更新。 |
| <code>Adler-32(A &#124;&#124; buf)</code><br>**追加后的校验和** | buf 指向 len 个可读字节，len > 0，且 adler 的低 32 位是 A 的 Adler-32。 | 将此值用于后续更新或与预期校验和比较。 |

**判读要点。**

- 返回校验和值可用 32 位表示；传入值高于第 31 位的位被忽略。
- NULL 配合非零长度不在契约范围内；更新的功能保证要求传入真实 A 的校验和。

### 调用条件与状态效果 {#api-adler32_z-contract}

**定义域。** 受限定义域。当 `buf` 非 NULL 时，效果为**只读**。

**前置条件：** `buf` 为 NULL 且 `len == 0`，或它指向 `len` 个可读字节。
要满足校验和后置条件，`adler` 的低 32 位须为 A 的 Adler-32。
不要求任何准备或清理操作。

**效果：** 保持全部内存与所有权。只读取给定范围。
零长度范围允许使用尾后指针。

NULL 配合非零长度不在本契约范围内。伪造种子不属于本实用功能契约：单字节路径
不一定等价于先将种子的两个半部对 65521 取模。见
[Adler 种子说明](../../proof/adler32.md)。

<details markdown="1" class="ar-return-exact" data-return-exact="adler32_z"><summary>完整返回条件与边界</summary>

**后置条件：** NULL、零长度查询对任意 `adler` 都返回 1，不读取字节。
否则返回 A 后接 `buf[0..len-1]` 的 Adler-32。
非 NULL、零长度范围返回传入校验和值的低 32 位。

</details>

## adler32

```c
uLong ZEXPORT adler32(uLong adler, const Bytef *buf, uInt len);
```

用 32 位字节计数更新 Adler-32。

### 返回值与后续调用 {#api-adler32-returns}

**返回值类型。** `uLong` — 32 位校验和值

返回本次更新后的 Adler-32，或新校验和的初始值。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `1`<br>**初始值** | buf == NULL 且 len == 0，任意传入校验和值；不读取字节。 | 以 1 开始处理新序列。 |
| `low32(adler)`<br>**空范围保持原值** | buf 非 NULL 且 len == 0；空范围也允许尾后指针。 | 保留该值，继续下一段更新。 |
| <code>Adler-32(A &#124;&#124; buf)</code><br>**追加后的校验和** | buf 指向 len 个可读字节，len > 0，且 adler 的低 32 位是 A 的 Adler-32。 | 将此值用于后续更新或与预期校验和比较。 |

**判读要点。**

- 返回校验和值可用 32 位表示；传入值高于第 31 位的位被忽略。
- NULL 配合非零长度不在契约范围内；更新的功能保证要求传入真实 A 的校验和。
- len 是 uInt，最多 2^32 - 1 字节；更大的计数须用 _z 形式或多次更新。

### 调用条件与状态效果 {#api-adler32-contract}

**定义域。** 受限定义域。当 `buf` 非 NULL 时，效果为**只读**。

**前置条件：** `buf` 为 NULL 且 `len == 0`，或它指向 `len` 个可读字节。
要满足校验和后置条件，`adler` 的低 32 位须为 A 的 Adler-32。

**效果：** 保持全部内存与所有权。只读取给定范围。
零长度范围允许使用尾后指针。

长度最多为 `2^32 - 1`。把更大长度转换为 `uInt` 会在调用前丢弃高位；
更大范围应使用 `adler32_z` 或分多次调用。
`adler32_z` 关于零长度 NULL 查询和伪造种子的范围同样适用。

<details markdown="1" class="ar-return-exact" data-return-exact="adler32"><summary>完整返回条件与边界</summary>

**后置条件：** 返回值与 `adler32_z(adler, buf, len)` 完全相同。
NULL、零长度查询返回 1。非 NULL 的空范围保持校验和值的低 32 位。

</details>

## adler32_combine

```c
uLong ZEXPORT adler32_combine(uLong adler1, uLong adler2, z_off_t len2);
```

计算 A 后接 B 的 Adler-32，而不读取任一序列。

### 返回值与后续调用 {#api-adler32_combine-returns}

**返回值类型。** `uLong` — 校验和值或长度拒绝值

无需读取 A 或 B，即可得到拼接的 Adler-32；负长度有单独数值结果。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `0xFFFFFFFF`<br>**负长度被拒绝** | len2 < 0；不限制传入校验和值。 | 修正 B 的长度后再组合。 |
| <code>Adler-32(A &#124;&#124; B)</code><br>**拼接校验和** | len2 >= 0 是 B 的长度，两项传入值的低 32 位是分别从 1 开始计算的 A、B 的 Adler-32。 | 将结果作为拼接序列的校验和使用。 |

**判读要点。**

- len2 必须是 B 的字节数；A、B 的校验和须各自独立计算。错误长度没有拼接保证。
- 空 B 的校验和为 1，拼接结果保持 A 的校验和。
- 0xFFFFFFFF 不是有效 Adler-32；本 LP64 构建中，普通与 64 位入口的长度范围相同。

### 调用条件与状态效果 {#api-adler32_combine-contract}

**定义域。** 受限定义域。效果为**纯计算**。

**前置条件：** 要得到拼接结果，`adler1` 和 `adler2` 的低 32 位须分别为 A 和 B 的
Adler-32，且 `len2` 是 B 的长度。特别地，B 的校验和独立于 A，从 1 开始。
负长度仅纳入下述拒绝结果的范围。

**效果：** 保持全部内存与所有权。不读取缓冲区或流状态。

该哨兵值不是有效的 Adler-32。任意标量参数不会导致内存访问；其精确的非校验和结果
由更宽的 Lean 契约描述。若 B 的长度错误，不保证拼接结果。

<details markdown="1" class="ar-return-exact" data-return-exact="adler32_combine"><summary>完整返回条件与边界</summary>

**后置条件：** 若 `len2 < 0`，返回 `0xFFFFFFFF`。否则返回 A 后接 B 的 Adler-32。
空 B 的校验和为 1，合并后 A 的校验和不变。

</details>

## adler32_combine64

```c
uLong ZEXPORT adler32_combine64(uLong adler1, uLong adler2, z_off64_t len2);
```

使用显式 64 位长度计算 A 后接 B 的 Adler-32。

### 返回值与后续调用 {#api-adler32_combine64-returns}

**返回值类型。** `uLong` — 校验和值或长度拒绝值

无需读取 A 或 B，即可得到拼接的 Adler-32；负长度有单独数值结果。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `0xFFFFFFFF`<br>**负长度被拒绝** | len2 < 0；不限制传入校验和值。 | 修正 B 的长度后再组合。 |
| <code>Adler-32(A &#124;&#124; B)</code><br>**拼接校验和** | len2 >= 0 是 B 的长度，两项传入值的低 32 位是分别从 1 开始计算的 A、B 的 Adler-32。 | 将结果作为拼接序列的校验和使用。 |

**判读要点。**

- len2 必须是 B 的字节数；A、B 的校验和须各自独立计算。错误长度没有拼接保证。
- 空 B 的校验和为 1，拼接结果保持 A 的校验和。
- 0xFFFFFFFF 不是有效 Adler-32；本 LP64 构建中，普通与 64 位入口的长度范围相同。

### 调用条件与状态效果 {#api-adler32_combine64-contract}

**定义域。** 受限定义域。效果为**纯计算**。

**前置条件：** 要得到拼接结果，`adler1` 和 `adler2` 的低 32 位须分别为独立计算的
A 和 B 的 Adler-32，且 `len2` 是 B 的长度。负长度纳入拒绝情形。

**效果：** 保持全部内存与所有权。不读取缓冲区或流状态。

在 LP64 下，它与 `adler32_combine` 的契约和长度范围相同。
显式位宽在其他构建中有意义；本页不涵盖那些构建。

<details markdown="1" class="ar-return-exact" data-return-exact="adler32_combine64"><summary>完整返回条件与边界</summary>

**后置条件：** 负长度返回 `0xFFFFFFFF`。否则返回 A 后接 B 的 Adler-32。
空 B 保持 A 的校验和不变。

</details>

## get_crc_table

```c
const z_crc_t FAR * ZEXPORT get_crc_table(void);
```

返回库逐字节计算 CRC 使用的表。

### 返回值与后续调用 {#api-get_crc_table-returns}

**返回值类型。** `const z_crc_t FAR *` — 借用的只读表指针

返回字节 CRC 更新表的地址。此调用不返回状态码。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `table != NULL`<br>**256 项 CRC 表** | 固定 CRC 表存在；每次调用返回同一指针。第 i 项是不包含公开校验和接口的取反步骤、从寄存器零开始的字节 i 反射更新值。 | 可在程序生命周期内读取 256 项；不得写入或释放该表。 |

**判读要点。**

- 此构建的 z_crc_t 为无符号 32 位；指针只公开字节表，不公开相邻表或编织表。

### 调用条件与状态效果 {#api-get_crc_table-contract}

**定义域。** 完整类型定义域；没有参数。效果为**纯计算**，返回指向库内存的指针，
不读取表项。

**前置条件：** 库的固定 CRC 表存在，如所选构建中所示。
不要求准备调用。

**效果：** 保持全部内存与所有权。表仍由库持有，生存期覆盖整个程序。
调用者可读取这 256 项，但不得通过指针写入，也不得释放它。

`zlib.h` 将此入口列于文档化 API 之外的函数中。它只公开字节表，不公开相邻表或
交织表。此处 `z_crc_t` 为无符号 32 位类型。动态建表不属于本构建范围。

<details markdown="1" class="ar-return-exact" data-return-exact="get_crc_table"><summary>完整返回条件与边界</summary>

**后置条件：** 返回非 NULL 指针，指向由 256 个 `z_crc_t` 表项组成的只读数组。
表项 `i` 表示从零寄存器出发处理字节 `i` 的反射 CRC 寄存器更新，
不包含公开校验和接口的取反步骤。重复调用返回相同指针。

</details>

## crc32_z

```c
uLong ZEXPORT crc32_z(uLong crc, const unsigned char FAR *buf, z_size_t len);
```

用一段字节更新 CRC-32，或取得初始值。

### 返回值与后续调用 {#api-crc32_z-returns}

**返回值类型。** `uLong` — 32 位校验和值

返回本次更新后的 CRC-32，或新校验和的初始值。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `0`<br>**初始值** | buf == NULL，任意 len 和传入校验和值；不读取缓冲区。 | 以 0 开始处理新序列。 |
| `low32(crc)`<br>**空范围保持原值** | buf 非 NULL 且 len == 0；空范围也允许尾后指针。 | 保留该值，继续下一段更新。 |
| <code>CRC-32(A &#124;&#124; buf)</code><br>**追加后的校验和** | buf 指向 len 个可读字节，len > 0，且 crc 的低 32 位是 A 的 CRC-32。 | 将此值用于后续更新或与预期校验和比较。 |

**判读要点。**

- 返回校验和值可用 32 位表示；传入值高于第 31 位的位被忽略。
- 取反处理由函数完成；调用者不要对运行中的校验和值取反。固定 CRC 表须存在。

### 调用条件与状态效果 {#api-crc32_z-contract}

**定义域。** 受限定义域。当 `buf` 非 NULL 时为**只读**，并读取库的固定 CRC 表。

**前置条件：** `buf` 为 NULL，或指向任意对齐的 `len` 个可读字节。
要满足校验和后置条件，`crc` 的低 32 位须为 A 的 CRC-32。
所选构建的固定 CRC 表存在。

**效果：** 保持全部内存与所有权。只读取给定字节范围和库的固定表。
空范围允许使用尾后指针。

新校验和从 0 开始。函数内部完成 CRC 的取反步骤；调用者不得对运行值取反。
对齐方式不改变契约。字访问模型的限制记录在
[安全模型](../safety.md)和[可信基](../../trusted-base.md)中。

<details markdown="1" class="ar-return-exact" data-return-exact="crc32_z"><summary>完整返回条件与边界</summary>

**后置条件：** NULL `buf` 对任意 `crc` 和 `len` 都返回 0，不读取缓冲区。
否则返回 A 后接 `buf[0..len-1]` 的 CRC-32。
非 NULL 的空范围返回 `crc` 的低 32 位。

</details>

## crc32

```c
uLong ZEXPORT crc32(uLong crc, const unsigned char FAR *buf, uInt len);
```

用 32 位字节计数更新 CRC-32。

### 返回值与后续调用 {#api-crc32-returns}

**返回值类型。** `uLong` — 32 位校验和值

返回本次更新后的 CRC-32，或新校验和的初始值。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `0`<br>**初始值** | buf == NULL，任意 len 和传入校验和值；不读取缓冲区。 | 以 0 开始处理新序列。 |
| `low32(crc)`<br>**空范围保持原值** | buf 非 NULL 且 len == 0；空范围也允许尾后指针。 | 保留该值，继续下一段更新。 |
| <code>CRC-32(A &#124;&#124; buf)</code><br>**追加后的校验和** | buf 指向 len 个可读字节，len > 0，且 crc 的低 32 位是 A 的 CRC-32。 | 将此值用于后续更新或与预期校验和比较。 |

**判读要点。**

- 返回校验和值可用 32 位表示；传入值高于第 31 位的位被忽略。
- 取反处理由函数完成；调用者不要对运行中的校验和值取反。固定 CRC 表须存在。
- len 是 uInt，最多 2^32 - 1 字节；更大的计数须用 _z 形式或多次更新。

### 调用条件与状态效果 {#api-crc32-contract}

**定义域。** 受限定义域。当 `buf` 非 NULL 时为**只读**，并读取库的固定表。

**前置条件：** `buf` 为 NULL，或指向任意对齐的 `len` 个可读字节。
要满足校验和后置条件，`crc` 的低 32 位须为 A 的 CRC-32。固定 CRC 表存在。

**效果：** 保持全部内存与所有权。只读取给定字节范围和库的固定表。
空范围允许使用尾后指针。

长度最多为 `2^32 - 1`。把更大计数转换为 `uInt` 会在调用前截断；
更大范围应使用 `crc32_z` 或分多次更新。

<details markdown="1" class="ar-return-exact" data-return-exact="crc32"><summary>完整返回条件与边界</summary>

**后置条件：** 返回值与 `crc32_z(crc, buf, len)` 完全相同。
即使长度非零，NULL 也返回 0。非 NULL 的空范围保持传入校验和值的低 32 位。
取反在内部处理。

</details>

## crc32_combine_gen64

```c
uLong ZEXPORT crc32_combine_gen64(z_off64_t len2);
```

生成一个算子，供 B 长度相同的多次 CRC 合并复用。

### 返回值与后续调用 {#api-crc32_combine_gen64-returns}

**返回值类型。** `uLong` — CRC 合并算子

按 B 的字节长度生成可复用的算子。返回值不是校验和。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `0`<br>**负长度被拒绝** | len2 < 0。 | 先修正长度；不要把此值当作有效生成算子。 |
| `0x80000000`<br>**空 B 的算子** | len2 == 0。 | 保持算子不变，用于 B 为空的 crc32_combine_op。 |
| `op != 0`<br>**指定长度的算子** | len2 > 0；返回非零的 32 位算子。 | 保持算子不变，只为 B 长度等于 len2 的各对序列复用。 |

**判读要点。**

- 固定 CRC 表须存在。此 LP64 构建中，两种入口均接受所有有符号 64 位长度。

### 调用条件与状态效果 {#api-crc32_combine_gen64-contract}

**定义域。** 完整类型定义域。效果为**纯计算**，只读取库的固定表。

**前置条件：** 参数不受限制。所选构建的固定 CRC 表存在。
`len2` 可为任意有符号 64 位值。

**效果：** 保持全部内存与所有权。不读取缓冲区或流状态。

算子只取决于长度。保持其值不变，即可用于 B 长度相同的任意 A 和 B。
它描述随长度推进校验和的运算，本身不是任何特定字节序列的校验和值。

<details markdown="1" class="ar-return-exact" data-return-exact="crc32_combine_gen64"><summary>完整返回条件与边界</summary>

**后置条件：** 负长度返回 0。非负长度返回非零 32 位算子，适用于 B 长度为
`len2` 的 `crc32_combine_op`。零长度返回 `0x80000000`。

</details>

## crc32_combine_gen

```c
uLong ZEXPORT crc32_combine_gen(z_off_t len2);
```

使用普通偏移类型生成 CRC 合并算子。

### 返回值与后续调用 {#api-crc32_combine_gen-returns}

**返回值类型。** `uLong` — CRC 合并算子

按 B 的字节长度生成可复用的算子。返回值不是校验和。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `0`<br>**负长度被拒绝** | len2 < 0。 | 先修正长度；不要把此值当作有效生成算子。 |
| `0x80000000`<br>**空 B 的算子** | len2 == 0。 | 保持算子不变，用于 B 为空的 crc32_combine_op。 |
| `op != 0`<br>**指定长度的算子** | len2 > 0；返回非零的 32 位算子。 | 保持算子不变，只为 B 长度等于 len2 的各对序列复用。 |

**判读要点。**

- 固定 CRC 表须存在。此 LP64 构建中，两种入口均接受所有有符号 64 位长度。

### 调用条件与状态效果 {#api-crc32_combine_gen-contract}

**定义域。** 完整类型定义域。效果为**纯计算**，只读取库的固定表。

**前置条件：** 参数不受限制。所选构建的固定 CRC 表存在。
`len2` 可为任意可表示的有符号值。

**效果：** 保持全部内存与所有权。不读取缓冲区或流状态。

LP64 下，普通长度和显式 64 位长度的范围相同。

<details markdown="1" class="ar-return-exact" data-return-exact="crc32_combine_gen"><summary>完整返回条件与边界</summary>

**后置条件：** 返回与 `crc32_combine_gen64(len2)` 相同的算子。
负长度返回 0；零返回 `0x80000000`；正长度返回适用于该 B 长度的非零 32 位算子。

</details>

## crc32_combine_op

```c
uLong ZEXPORT crc32_combine_op(uLong crc1, uLong crc2, uLong op);
```

使用预先生成的算子，计算 A 后接 B 的 CRC-32。

### 返回值与后续调用 {#api-crc32_combine_op-returns}

**返回值类型。** `uLong` — CRC-32 校验和值或算子拒绝值

将先前生成的算子应用于两个独立 CRC。零算子有单独拒绝结果。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `0`<br>**零算子被拒绝** | op == 0；可传任意校验和值。 | 用 B 的真实长度重新生成有效算子。 |
| <code>CRC-32(A &#124;&#124; B)</code><br>**拼接 CRC** | crc1、crc2 的低 32 位是分别从 0 开始计算的 A、B 的 CRC；op 是为 B 的长度生成且未改动的算子。 | 将结果作为拼接 CRC；相同 B 长度可复用此算子。 |

**判读要点。**

- 有效 CRC 也可能为 0，返回值本身不能区分拒绝与有效结果。
- 伪造算子、错误长度的算子不在功能保证内；低 32 位全零的非零 LP64 算子甚至可能不终止。
- B 为空时，使用其 CRC 0 和对应空序列算子，结果保持 A 的 CRC。

### 调用条件与状态效果 {#api-crc32_combine_op-contract}

**定义域。** 受限定义域。效果为**纯计算**。

**前置条件：** 要得到拼接结果，`crc1` 和 `crc2` 的低 32 位须分别为 A 和 B 从 0
独立开始计算的 CRC-32。`op` 是按 B 的长度调用 `crc32_combine_gen` 或
`crc32_combine_gen64` 得到、且未经修改的结果。
独立的拒绝情形允许 `op == 0` 配合任意校验和参数。

**效果：** 保持全部内存与所有权。不读取缓冲区或流状态。
该算子可复用于 B 长度相同的任意序列对。

伪造算子或用于错误 B 长度的算子不受保证。
特别地，若 LP64 `op` 非零、但低 32 位全为零，调用可能不终止；这不在生成算子契约内。
零是拒绝值，不是无歧义的错误码，因为有效 CRC 也可能为零。

<details markdown="1" class="ar-return-exact" data-return-exact="crc32_combine_op"><summary>完整返回条件与边界</summary>

**后置条件：** 返回 A 后接 B 的 CRC-32。若 `op == 0`，返回 0。
用于空 B 的算子保持 A 的校验和不变。

</details>

## crc32_combine64

```c
uLong ZEXPORT crc32_combine64(uLong crc1, uLong crc2, z_off64_t len2);
```

计算 A 后接 B 的 CRC-32，而不读取任一序列。

### 返回值与后续调用 {#api-crc32_combine64-returns}

**返回值类型。** `uLong` — 校验和值或长度拒绝值

无需读取 A 或 B，即可得到拼接的 CRC-32；负长度有单独数值结果。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `0`<br>**负长度被拒绝** | len2 < 0；不限制传入校验和值。 | 修正 B 的长度后再组合。 |
| <code>CRC-32(A &#124;&#124; B)</code><br>**拼接校验和** | len2 >= 0 是 B 的长度，两项传入值的低 32 位是分别从 0 开始计算的 A、B 的 CRC-32。 | 将结果作为拼接序列的校验和使用。 |

**判读要点。**

- len2 必须是 B 的字节数；A、B 的校验和须各自独立计算。错误长度没有拼接保证。
- 空 B 的校验和为 0，拼接结果保持 A 的校验和。
- 0 也可能是有效 CRC，不能仅凭返回 0 判断长度被拒绝。固定 CRC 表须存在。

### 调用条件与状态效果 {#api-crc32_combine64-contract}

**定义域。** 受限定义域。效果为**纯计算**，只读取库的固定表。

**前置条件：** 要得到拼接结果，`crc1` 和 `crc2` 的低 32 位须分别为独立计算的
A 和 B 的 CRC-32，且 `len2` 是 B 的长度。固定 CRC 表存在。
负长度纳入拒绝情形，对校验和不作限制。

**效果：** 保持全部内存与所有权。不读取缓冲区或流状态。
生成的算子满足 `crc32_combine_op` 的输入要求。

若校验和值任意且长度为零，实现返回低 32 位的异或。
错误长度不保证拼接结果。零也是可能的有效 CRC，因此负长度拒绝没有独立错误码。

<details markdown="1" class="ar-return-exact" data-return-exact="crc32_combine64"><summary>完整返回条件与边界</summary>

**后置条件：** 负长度返回 0。否则返回 A 后接 B 的 CRC-32。
空 B 的 CRC 为 0，合并后 A 的校验和不变。

</details>

## crc32_combine

```c
uLong ZEXPORT crc32_combine(uLong crc1, uLong crc2, z_off_t len2);
```

使用普通偏移类型计算 A 后接 B 的 CRC-32。

### 返回值与后续调用 {#api-crc32_combine-returns}

**返回值类型。** `uLong` — 校验和值或长度拒绝值

无需读取 A 或 B，即可得到拼接的 CRC-32；负长度有单独数值结果。

| 返回值 | 含义与出现条件 | 调用者接下来 |
| --- | --- | --- |
| `0`<br>**负长度被拒绝** | len2 < 0；不限制传入校验和值。 | 修正 B 的长度后再组合。 |
| <code>CRC-32(A &#124;&#124; B)</code><br>**拼接校验和** | len2 >= 0 是 B 的长度，两项传入值的低 32 位是分别从 0 开始计算的 A、B 的 CRC-32。 | 将结果作为拼接序列的校验和使用。 |

**判读要点。**

- len2 必须是 B 的字节数；A、B 的校验和须各自独立计算。错误长度没有拼接保证。
- 空 B 的校验和为 0，拼接结果保持 A 的校验和。
- 0 也可能是有效 CRC，不能仅凭返回 0 判断长度被拒绝。固定 CRC 表须存在。

### 调用条件与状态效果 {#api-crc32_combine-contract}

**定义域。** 受限定义域。效果为**纯计算**，只读取库的固定表。

**前置条件：** 要得到拼接结果，`crc1` 和 `crc2` 的低 32 位须分别为 A 和 B 从 0
独立开始计算的 CRC-32，且 `len2` 是 B 的长度。固定 CRC 表存在。
负长度纳入拒绝情形，对校验和不作限制。

**效果：** 保持全部内存与所有权。不读取缓冲区或流状态。

LP64 下，普通长度和显式 64 位长度的范围相同。
本页不包括动态建表、硬件 CRC 钩子或生成表的可执行程序。
见[构建与模型范围](../../deviations.md)。

[返回 API 手册](README.md) · [契约约定](contracts.md)

<details markdown="1" class="ar-return-exact" data-return-exact="crc32_combine"><summary>完整返回条件与边界</summary>

**后置条件：** 返回与 `crc32_combine64(crc1, crc2, len2)` 相同的结果。
负长度返回 0。真实的空 B 保持 A 的校验和不变。

</details>
