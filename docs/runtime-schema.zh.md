# 运行时模式：对象堆上的 zlib 结构体

本页对应的英文模式说明由 `scripts/gen_schema.py` **自动生成**，同时生成
`ZlibF/Runtime/Schema.lean`、`ZlibF/Runtime/Tables.lean` 和 `ZlibF/Runtime/LibcTables.lean`。
不要手工修改生成的英文原文：应修改脚本并重新运行。脚本通过 clang 的 JSON AST 转储，
读取已验证源代码（zlib 提交 `757f0527154291bcf6bfbd6396ecde6bedd2db95`）中的
`zlib.h`、`zutil.h`、`inftrees.h`、`inflate.h`、`deflate.h`、`trees.h`、`gzguts.h` 和 `crc32.h`。
采用默认 x86_64 Linux 构建（`./configure --static`、LP64、`-D_LARGEFILE64_SOURCE=1`）。

## 脚本如何选择表示

| C | Lean | 原因 |
| --- | --- | --- |
| `char`、`short`、`int`、`long` 及其无符号形式 | `Int8`、`Int16`、`Int32`、`Int64`、`UInt8` .. `UInt64` | LP64：`long` 和指针均为 64 位；x86_64 上的普通 `char` 有符号 |
| `enum` 类型 | `UInt32`（若有负枚举值则为 `Int32`）；枚举项成为该类型的常量 `X`，以及 `Int32` 类型的 `X_i` | 对于不含负值的枚举类型对象，gcc 选择 `unsigned int`。枚举常量本身在 C 中的类型是 `int`：与枚举类型对象比较时使用 `X`，与 `int` 一起使用时采用 `X_i` |
| `T *`，其中 `T` 为字节或 `void` | `BPtr = Ptr BRef`：空指针，或数组及偏移 | 字节缓冲区是 `bytes` 表中的一个块；zlib 中的 `void *` 只用于字节缓冲区或不透明数据 |
| `T *`，其中 `T` 为更宽的标量 | `WPtr`、`IPtr`、……（该元素引用类型的 `Ptr`） | 对 `words` 表或结构体内数组采用同样的表示 |
| `T *`，其中 `T` 为数组元素结构体（`ct_data`、`code`） | `CtDataPtr`、`CodePtr` | 指向结构体数组的指针表示为数组和索引，不表示为地址 |
| `S *`，其中 `S` 为单个结构体（`z_stream`、`gz_header`、`deflate_state`、……） | `Option SRef`；`none` 表示空指针 | `SRef` 是表项，或所属对象内部的结构体 |
| `struct internal_state *` | `Option StateRef`（压缩状态或解压状态） | C 中会将 `z_stream.state` 转换为这两种状态指针 |
| 数组字段 `T f[N]` | `Array T` 字段 | 作为结构体一部分的数组随结构体一起复制，与 C 相同；指向它的指针是 `T` 的引用类型的构造器 |
| 结构体字段 `S f` | 嵌套记录 `S` | 采用值语义；`&s->f` 对应 `SRef` 的构造器 `in_<owner>_<f>` |
| 所有成员类型相同的 `union` | 一个字段 | `ct_data` 的两个成员都是 `ush`：它们是相同的位 |
| 函数指针 | `FnPtr`（空指针或名称） | 只对默认分配器建模；调用其他函数会产生故障 |
| 静态表或静态实例 | 堆中 `Statics` 的一个字段，以及引用构造器 `st_<name>` | 只读：通过该引用写入会产生故障；内容由翻译设置 |

## 此模式未建模的内容

* **指向指针的指针，以及标量字段的地址**（调用 `inflate_table` 时的 `&state->lenbits`、`&state->next`）。
  翻译将这类输出参数作为返回结果传递。如果结构体字段的类型为指向指针的指针，脚本会停止。
* **位字段，以及成员类型不同的联合体。** 脚本会停止；这些头文件中没有此类情况。
* **指向调用者数据的不透明（`opaque`）指针**（`z_stream.opaque`、`voidpf`）表示为 `BPtr`；无法表示不属于字节块的调用者对象。
  zlib 从不解引用它。
* **在 `.c` 文件中定义的结构体**（`deflate.c` 中的 `struct config_s`、C 标准库的 `FILE`）。
* **未初始化的指针。** 新记录（`allocK`、`X.garbage`）的指针为空。C 中从未初始化内存读取的指针具有不确定值。
  模型中它是有效的 NULL：解引用会触发空指针解引用故障，但 `p == NULL`、`free(p)` 和复制该指针可以成功。
  因此，若函数在写入某指针字段前读取它，相关定理必须证明先前的写入；运行时不会检查这一点。
  见 `trusted-base.md` 第 2 项。整数可以取任意值；见 `docs/spec/safety.md` 的未初始化内存部分。
* **数组字段的长度。** `Array` 字段可以具有任意长度。`X.WellFormed` 表示每个数组都具有声明的长度，
  `Heap.RecordsWellFormed` 表示堆中的每条记录都满足这一条件；定理将其作为假设
  （`Heap.WellFormed` 还加入静态表的条件）。`X.garbage` 和 `X.zeroed` 都是良构的，
  引理 `Heap.RecordsWellFormed.set_*`、`clear_*` 和 `*.put_*_wf` 证明写入保持良构性。
* **静态表的内容。** `Statics` 保存数组；`Statics.WellFormed` 表示每个数组都具有声明的长度。
  数值由 `trees.c`、`inffixed.h`、`crc32.c` 的翻译确定（各自由读取 C 源码的生成器产生），
  在此之前作为定理的假设。脚本不将这些值与 C 比较。
* **表。** 堆中的表采用 `Tbl`（将 `Array` 看作块编号到元素的函数），使写入原语可以原地更新；
  见 `trusted-base.md` 第 2 项。
* **与枚举项重名的宏。** `COPY` 既是 `inflate.h` 中的枚举项（16195），又是 `gzguts.h` 中的宏（1）。
  枚举项保留名称 `COPY`；宏对应常量 `GZ_COPY`。
* **分配。** 如果下一个块编号已被占用，`allocK` 会产生故障，因此堆必须满足 `Fresh`
  （`Fresh.slotUsed_next`；策略 `fresh_slot` 从 `Fresh h` 解除 `allocK_some` 的假设）。
  直接写入（`stK`）数组长度错误的记录不会产生故障。
* **两类状态之间的转换**在转换时即产生故障；在 C 中，只有访问时才产生故障。

头文件中未声明的静态对象由脚本列出
（`EXTRA_STATIC_ARRAYS`、`EXTRA_STATIC_INSTANCES`）：`lenfix`、`distfix`、`extra_lbits`、`extra_dbits`、`extra_blbits`、`static_l_desc`、`static_d_desc`、`static_bl_desc`。

## 字段


### `z_stream`（Lean `ZStream`，堆表 `streams`）

| 字段 | C 类型 | Lean 类型 | 原因 |
| --- | --- | --- | --- |
| `next_in` | `Bytef *` | `BPtr` | 指向字节块内部：`BPtr`（堆中的块或数组、偏移）；空指针对应一个构造器 |
| `avail_in` | `uInt` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `total_in` | `uLong` | `UInt64` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `next_out` | `Bytef *` | `BPtr` | 指向字节块内部：`BPtr`（堆中的块或数组、偏移）；空指针对应一个构造器 |
| `avail_out` | `uInt` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `total_out` | `uLong` | `UInt64` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `msg` | `char *` | `BPtr` | 指向字节块内部：`BPtr`（堆中的块或数组、偏移）；空指针对应一个构造器 |
| `state` | `struct internal_state *` | `Option StateRef` | 不透明的 `struct internal_state *`：压缩状态或解压状态（`StateRef`）；转换位于 `Tables.lean` |
| `zalloc` | `alloc_func` | `FnPtr` | 函数指针：空指针或函数名称（不对默认分配器以外的分配器建模） |
| `zfree` | `free_func` | `FnPtr` | 函数指针：空指针或函数名称（不对默认分配器以外的分配器建模） |
| `opaque` | `voidpf` | `BPtr` | 指向字节块内部：`BPtr`（堆中的块或数组、偏移）；空指针对应一个构造器 |
| `data_type` | `int` | `Int32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `adler` | `uLong` | `UInt64` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `reserved` | `uLong` | `UInt64` | 标量：LP64（`char` 有符号，`long` 为 64 位） |

引用构造器（`ZStreamRef`）：`tab`, `in_gzstate_strm`。

### `gz_header`（Lean `GzHeader`，堆表 `gzheaders`）

| 字段 | C 类型 | Lean 类型 | 原因 |
| --- | --- | --- | --- |
| `text` | `int` | `Int32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `time` | `uLong` | `UInt64` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `xflags` | `int` | `Int32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `os` | `int` | `Int32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `extra` | `Bytef *` | `BPtr` | 指向字节块内部：`BPtr`（堆中的块或数组、偏移）；空指针对应一个构造器 |
| `extra_len` | `uInt` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `extra_max` | `uInt` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `name` | `Bytef *` | `BPtr` | 指向字节块内部：`BPtr`（堆中的块或数组、偏移）；空指针对应一个构造器 |
| `name_max` | `uInt` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `comment` | `Bytef *` | `BPtr` | 指向字节块内部：`BPtr`（堆中的块或数组、偏移）；空指针对应一个构造器 |
| `comm_max` | `uInt` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `hcrc` | `int` | `Int32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `done` | `int` | `Int32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |

引用构造器（`GzHeaderRef`）：`tab`。

### `deflate_state`（Lean `DeflateState`，堆表 `dstates`）

| 字段 | C 类型 | Lean 类型 | 原因 |
| --- | --- | --- | --- |
| `strm` | `z_streamp` | `Option ZStreamRef` | 指向 `z_stream` 的指针：`ZStreamRef`（表项，或所属对象内部的结构体），`none` 表示空指针 |
| `status` | `int` | `Int32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `pending_buf` | `Bytef *` | `BPtr` | 指向字节块内部：`BPtr`（堆中的块或数组、偏移）；空指针对应一个构造器 |
| `pending_buf_size` | `ulg` | `UInt64` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `pending_out` | `Bytef *` | `BPtr` | 指向字节块内部：`BPtr`（堆中的块或数组、偏移）；空指针对应一个构造器 |
| `pending` | `ulg` | `UInt64` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `wrap` | `int` | `Int32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `gzhead` | `gz_headerp` | `Option GzHeaderRef` | 指向 `gz_header` 的指针：`GzHeaderRef`（表项，或所属对象内部的结构体），`none` 表示空指针 |
| `gzindex` | `ulg` | `UInt64` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `method` | `Byte` | `UInt8` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `last_flush` | `int` | `Int32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `w_size` | `uInt` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `w_bits` | `uInt` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `w_mask` | `uInt` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `window` | `Bytef *` | `BPtr` | 指向字节块内部：`BPtr`（堆中的块或数组、偏移）；空指针对应一个构造器 |
| `window_size` | `ulg` | `UInt64` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `prev` | `Posf *` | `WPtr` | 指向 `UInt16` 数组内部：`WPtr` |
| `head` | `Posf *` | `WPtr` | 指向 `UInt16` 数组内部：`WPtr` |
| `ins_h` | `uInt` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `hash_size` | `uInt` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `hash_bits` | `uInt` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `hash_mask` | `uInt` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `hash_shift` | `uInt` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `block_start` | `long` | `Int64` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `match_length` | `uInt` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `prev_match` | `IPos` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `match_available` | `int` | `Int32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `strstart` | `uInt` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `match_start` | `uInt` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `lookahead` | `uInt` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `prev_length` | `uInt` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `max_chain_length` | `uInt` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `max_lazy_match` | `uInt` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `level` | `int` | `Int32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `strategy` | `int` | `Int32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `good_match` | `uInt` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `nice_match` | `int` | `Int32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `dyn_ltree` | `struct ct_data_s[573]` | `Array CtData` | 结构体内部的结构体数组：记录的 `Array`；指向它的指针是 `CtDataRef` 的构造器 |
| `dyn_dtree` | `struct ct_data_s[61]` | `Array CtData` | 结构体内部的结构体数组：记录的 `Array`；指向它的指针是 `CtDataRef` 的构造器 |
| `bl_tree` | `struct ct_data_s[39]` | `Array CtData` | 结构体内部的结构体数组：记录的 `Array`；指向它的指针是 `CtDataRef` 的构造器 |
| `l_desc` | `struct tree_desc_s` | `TreeDesc` | 结构体内部的结构体：嵌套记录（值语义）；其地址是 `TreeDescRef` 的构造器 `in_dstate_l_desc` |
| `d_desc` | `struct tree_desc_s` | `TreeDesc` | 结构体内部的结构体：嵌套记录（值语义）；其地址是 `TreeDescRef` 的构造器 `in_dstate_d_desc` |
| `bl_desc` | `struct tree_desc_s` | `TreeDesc` | 结构体内部的结构体：嵌套记录（值语义）；其地址是 `TreeDescRef` 的构造器 `in_dstate_bl_desc` |
| `bl_count` | `ush[16]` | `Array UInt16` | 结构体内部的数组：`Array` 字段，随结构体一起复制；指向它的指针是 `WRef` 的构造器 |
| `heap` | `int[573]` | `Array Int32` | 结构体内部的数组：`Array` 字段，随结构体一起复制；指向它的指针是 `IRef` 的构造器 |
| `heap_len` | `int` | `Int32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `heap_max` | `int` | `Int32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `depth` | `uch[573]` | `Array UInt8` | 结构体内部的数组：`Array` 字段，随结构体一起复制；指向它的指针是 `BRef` 的构造器 |
| `sym_buf` | `uchf *` | `BPtr` | 指向字节块内部：`BPtr`（堆中的块或数组、偏移）；空指针对应一个构造器 |
| `lit_bufsize` | `uInt` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `sym_next` | `uInt` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `sym_end` | `uInt` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `opt_len` | `ulg` | `UInt64` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `static_len` | `ulg` | `UInt64` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `matches` | `uInt` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `insert` | `uInt` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `bi_buf` | `ush` | `UInt16` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `bi_valid` | `int` | `Int32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `bi_used` | `int` | `Int32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `high_water` | `ulg` | `UInt64` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `slid` | `int` | `Int32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |

引用构造器（`DeflateStateRef`）：`tab`。

### `inflate_state`（Lean `InflateState`，堆表 `istates`）

| 字段 | C 类型 | Lean 类型 | 原因 |
| --- | --- | --- | --- |
| `strm` | `z_streamp` | `Option ZStreamRef` | 指向 `z_stream` 的指针：`ZStreamRef`（表项，或所属对象内部的结构体），`none` 表示空指针 |
| `mode` | `inflate_mode` | `UInt32` | 枚举：枚举项是此类型的常量（gcc：没有负值时为 `unsigned int`） |
| `last` | `int` | `Int32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `wrap` | `int` | `Int32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `reqwrap` | `int` | `Int32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `havedict` | `int` | `Int32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `flags` | `int` | `Int32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `dmax` | `unsigned int` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `check` | `unsigned long` | `UInt64` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `total` | `unsigned long` | `UInt64` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `head` | `gz_headerp` | `Option GzHeaderRef` | 指向 `gz_header` 的指针：`GzHeaderRef`（表项，或所属对象内部的结构体），`none` 表示空指针 |
| `reqbits` | `unsigned int` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `wbits` | `unsigned int` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `wsize` | `unsigned int` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `whave` | `unsigned int` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `wnext` | `unsigned int` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `window` | `unsigned char *` | `BPtr` | 指向字节块内部：`BPtr`（堆中的块或数组、偏移）；空指针对应一个构造器 |
| `hold` | `unsigned long` | `UInt64` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `bits` | `unsigned int` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `length` | `unsigned int` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `offset` | `unsigned int` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `extra` | `unsigned int` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `lencode` | `const code *` | `CodePtr` | 指向 `code` 数组内部：`CodePtr`（空指针，或数组及索引） |
| `distcode` | `const code *` | `CodePtr` | 指向 `code` 数组内部：`CodePtr`（空指针，或数组及索引） |
| `lenbits` | `unsigned int` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `distbits` | `unsigned int` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `ncode` | `unsigned int` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `nlen` | `unsigned int` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `ndist` | `unsigned int` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `have` | `unsigned int` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `next` | `code *` | `CodePtr` | 指向 `code` 数组内部：`CodePtr`（空指针，或数组及索引） |
| `lens` | `unsigned short[320]` | `Array UInt16` | 结构体内部的数组：`Array` 字段，随结构体一起复制；指向它的指针是 `WRef` 的构造器 |
| `work` | `unsigned short[288]` | `Array UInt16` | 结构体内部的数组：`Array` 字段，随结构体一起复制；指向它的指针是 `WRef` 的构造器 |
| `codes` | `code[1444]` | `Array Code` | 结构体内部的结构体数组：记录的 `Array`；指向它的指针是 `CodeRef` 的构造器 |
| `sane` | `int` | `Int32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `back` | `int` | `Int32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `was` | `unsigned int` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |

引用构造器（`InflateStateRef`）：`tab`。

### `gz_state`（Lean `GzState`，堆表 `gzstates`）

| 字段 | C 类型 | Lean 类型 | 原因 |
| --- | --- | --- | --- |
| `x` | `struct gzFile_s` | `GzFile` | 结构体内部的结构体：嵌套记录（值语义）；其地址是 `GzFileRef` 的构造器 `in_gzstate_x` |
| `mode` | `int` | `Int32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `fd` | `int` | `Int32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `path` | `char *` | `BPtr` | 指向字节块内部：`BPtr`（堆中的块或数组、偏移）；空指针对应一个构造器 |
| `size` | `unsigned int` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `want` | `unsigned int` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `in` | `unsigned char *` | `BPtr` | 指向字节块内部：`BPtr`（堆中的块或数组、偏移）；空指针对应一个构造器 |
| `out` | `unsigned char *` | `BPtr` | 指向字节块内部：`BPtr`（堆中的块或数组、偏移）；空指针对应一个构造器 |
| `direct` | `int` | `Int32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `junk` | `int` | `Int32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `how` | `int` | `Int32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `again` | `int` | `Int32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `start` | `off64_t` | `Int64` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `eof` | `int` | `Int32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `past` | `int` | `Int32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `level` | `int` | `Int32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `strategy` | `int` | `Int32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `reset` | `int` | `Int32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `skip` | `off64_t` | `Int64` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `err` | `int` | `Int32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `msg` | `char *` | `BPtr` | 指向字节块内部：`BPtr`（堆中的块或数组、偏移）；空指针对应一个构造器 |
| `strm` | `z_stream` | `ZStream` | 结构体内部的结构体：嵌套记录（值语义）；其地址是 `ZStreamRef` 的构造器 `in_gzstate_strm` |

引用构造器（`GzStateRef`）：`tab`。

### `gzFile_s`（Lean `GzFile`，仅作为其他结构体的字段）

| 字段 | C 类型 | Lean 类型 | 原因 |
| --- | --- | --- | --- |
| `have` | `unsigned int` | `UInt32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `next` | `unsigned char *` | `BPtr` | 指向字节块内部：`BPtr`（堆中的块或数组、偏移）；空指针对应一个构造器 |
| `pos` | `off64_t` | `Int64` | 标量：LP64（`char` 有符号，`long` 为 64 位） |

引用构造器（`GzFileRef`）：`in_gzstate_x`。

### `tree_desc`（Lean `TreeDesc`，仅作为其他结构体的字段）

| 字段 | C 类型 | Lean 类型 | 原因 |
| --- | --- | --- | --- |
| `dyn_tree` | `ct_data *` | `CtDataPtr` | 指向 `ct_data` 数组内部：`CtDataPtr`（空指针，或数组及索引） |
| `max_code` | `int` | `Int32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `stat_desc` | `const static_tree_desc *` | `Option StaticTreeDescRef` | 指向 `static_tree_desc` 的指针：`StaticTreeDescRef`（表项，或所属对象内部的结构体），`none` 表示空指针 |

引用构造器（`TreeDescRef`）：`in_dstate_l_desc`, `in_dstate_d_desc`, `in_dstate_bl_desc`。

### `static_tree_desc`（Lean `StaticTreeDesc`，仅有静态实例）

| 字段 | C 类型 | Lean 类型 | 原因 |
| --- | --- | --- | --- |
| `static_tree` | `const ct_data *` | `CtDataPtr` | 指向 `ct_data` 数组内部：`CtDataPtr`（空指针，或数组及索引） |
| `extra_bits` | `const intf *` | `IPtr` | 指向 `Int32` 数组内部：`IPtr` |
| `extra_base` | `int` | `Int32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `elems` | `int` | `Int32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `max_length` | `int` | `Int32` | 标量：LP64（`char` 有符号，`long` 为 64 位） |

引用构造器（`StaticTreeDescRef`）：`st_static_l_desc`, `st_static_d_desc`, `st_static_bl_desc`。

### `ct_data`（Lean `CtData`，作为数组元素）

| 字段 | C 类型 | Lean 类型 | 原因 |
| --- | --- | --- | --- |
| `fc` | `union { ush freq; ush code }` | `UInt16` | 成员均为 `UInt16` 类型的联合体：一个字段（成员是相同的位） |
| `dl` | `union { ush dad; ush len }` | `UInt16` | 成员均为 `UInt16` 类型的联合体：一个字段（成员是相同的位） |

### `code`（Lean `Code`，作为数组元素）

| 字段 | C 类型 | Lean 类型 | 原因 |
| --- | --- | --- | --- |
| `op` | `unsigned char` | `UInt8` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `bits` | `unsigned char` | `UInt8` | 标量：LP64（`char` 有符号，`long` 为 64 位） |
| `val` | `unsigned short` | `UInt16` | 标量：LP64（`char` 有符号，`long` 为 64 位） |

### 数组的引用类型

| Lean 类型 | 元素 | 构造器 |
| --- | --- | --- |
| `IRef` / `IPtr` | `Int32` | `dstate_heap`, `st_base_dist`, `st_base_length`, `st_extra_lbits`, `st_extra_dbits`, `st_extra_blbits` |
| `WRef` / `WPtr` | `UInt16` | `blk`（表 `words`）， `dstate_bl_count`, `istate_lens`, `istate_work` |
| `URef` / `UPtr` | `UInt32` | `st_crc_table`, `st_x2n_table` |
| `BRef` / `BPtr` | `UInt8` | `blk`（表 `bytes`）， `dstate_depth`, `st_dist_code`, `st_length_code` |
| `CodeRef` / `CodePtr` | `Code` | `istate_codes`, `st_lenfix`, `st_distfix` |
| `CtDataRef` / `CtDataPtr` | `CtData` | `dstate_dyn_ltree`, `dstate_dyn_dtree`, `dstate_bl_tree`, `st_static_dtree`, `st_static_ltree` |

### 字符串字面量

`strTable`（位于 `Schema.lean`）列出库源代码中的 177 个字符串字面量：已验证源代码顶层目录中的
`*.c` 和 `*.h` 文件，排除注释、合并相邻字面量，并加入空字符串。
它们包括错误消息（`zutil.c`、`inflate.c`、`inffast.c`、`inftrees.c`、`trees.c`、`deflate.c`、`gz*.c`）、
`z_errmsg` 文本、`ZLIB_VERSION`、版权字符串和格式字符串。该集合是封闭的：对表中不存在的文本使用
`strLitRef` 会产生故障。字面量表示为 `BRef.str i`：只读、始终存活、从不释放，且不在堆的任何表中。

```
""
"\n    "
"\n#else /* W == 4 */\n\nlocal const z_crc_t FAR crc_braid_table[][256] = {\n"
"\n#else /* W == 4 */\n\nlocal const z_word_t FAR crc_big_table[] = {\n    "
"\n#endif\n"
"\n#if N == %d\n"
"\n#if W == 8\n\nlocal const z_crc_t FAR crc_braid_table[][256] = {\n"
"\n#ifdef W\n\n#if W == 8\n\nlocal const z_word_t FAR crc_big_table[] = {\n    "
"\nbit length overflow\n"
"\nbl code %2d "
"\nbl counts: "
"\nbl tree: sent %lu"
"\ncd %3d "
"\ncomprlen %lu(%lu) "
"\ndist data: dyn %lu, stat %lu"
"\ndist tree: sent %lu"
"\ndyn trees: dyn %lu, stat %lu"
"\ngen_codes: max_code %d "
"\nlit data: dyn %lu, stat %lu"
"\nlit tree: sent %lu"
"\nlocal const z_crc_t FAR x2n_table[] = {\n    "
"\nn %3d %c l %2d c %4x (%x) "
"\nnode %d(%d), sons %d(%d) %d(%d)"
"\nopt %lu(%lu) stat %lu(%lu) stored %lu lit %u "
"\nstatic const code distfix[%u] = {"
"\n};"
"\n};\n\n"
"    "
"   It is part of the implementation of this library and is"
"   subject to change. Applications should only use zlib.h."
"   {"
" '%c' "
" (last)"
" * Generated automatically by makefixed()."
" */"
" 3_6?"
" deflate 1.3.2.1 Copyright 1995-2026 Jean-loup Gailly and Mark Adler "
" inflate 1.3.2.1 Copyright 1995-2026 Mark Adler "
" l %2d v %4x "
" start %u, match %d, length %d\n"
"%1u%s"
"%2u%s"
"%5u%s"
"%c"
"%s"
"%s\n"
"%s%s%s"
"%s0x%016llx%s"
"%s0x%08lx%s"
"(%02x %02x)"
"+r"
",\n"
", "
"/* WARNING: this file should *not* be used by applications."
"/* crc32.h -- tables for rapid CRC calculation\n * Generated automatically by crc32.c\n */\n\nlocal const z_crc_t FAR crc_table[] = {\n    "
"/* header created automatically with -DGEN_TREES_H */\n\n"
"/* inffixed.h -- table for decoding fixed codes"
"1.3.2.1-motley"
": "
"<fd:%d>"
"C"
"Can't open trees.h"
"Code too clever"
"[FLUSH]"
"\\[%d,%d]"
"_tr_tally: bad match"
"already enough lookahead"
"bad compressed size"
"bad d_code"
"buffer error"
"code %d bits %d->%d\n"
"compressed data error"
"const uch ZLIB_INTERNAL _dist_code[DIST_CODE_LEN] = {\n"
"const uch ZLIB_INTERNAL _length_code[MAX_MATCH-MIN_MATCH+1]= {\n"
"crc32.h"
"crc32b %w0, %w0, %w1"
"crc32x %w0, %w0, %x1"
"ctx=stm"
"data error"
"file error"
"header crc mismatch"
"hidden"
"incompatible version"
"inconsistent bit counts"
"incorrect data check"
"incorrect header check"
"incorrect length check"
"inflate.c too far\n"
"inflate:         distance %u\n"
"inflate:         end of block\n"
"inflate:         length %u\n"
"inflate:         literal '%c'\n"
"inflate:         literal 0x%02x\n"
"inflate:       code lengths ok\n"
"inflate:       codes ok\n"
"inflate:       stored end\n"
"inflate:       stored length %u\n"
"inflate:       table sizes ok\n"
"inflate:     dynamic codes block%s\n"
"inflate:     fixed codes block%s\n"
"inflate:     stored block%s\n"
"inflate:   check matches trailer\n"
"inflate:   dictionary set\n"
"inflate:   length matches trailer\n"
"inflate:   zlib header ok\n"
"inflate: allocated\n"
"inflate: end\n"
"inflate: reset\n"
"insufficient memory"
"internal error: deflate stream corrupt"
"internal error: inflate stream corrupt"
"invalid bit length repeat"
"invalid block type"
"invalid code -- missing end-of-block"
"invalid code lengths set"
"invalid distance code"
"invalid distance too far back"
"invalid distances set"
"invalid length"
"invalid literal/length code"
"invalid literal/lengths set"
"invalid match"
"invalid stored block lengths"
"invalid window size"
"local const ct_data static_dtree[D_CODES] = {\n"
"local const ct_data static_ltree[L_CODES+2] = {\n"
"local const int base_dist[D_CODES] = {\n"
"local const int base_length[LENGTH_CODES] = {\n"
"lost buf"
"match[2]?"
"mbc=60"
"memory"
"more < 2"
"mrs=512"
"need dictionary"
"need lookahead"
"no flush?"
"no future"
"not enough codes"
"not enough room for search"
"out of memory"
"out of room to push characters"
"pendingBuf overflow"
"r"
"request does not fit in a size_t"
"request does not fit in an int"
"requested length does not fit in int"
"rfm=fix"
"scan[2]?"
"stalled write on gzprintf"
"state corrupt"
"static const code lenfix[%u] = {"
"stdio error (consult errno)"
"stream end"
"stream error"
"string length does not fit in int"
"too many codes"
"too many length or distance symbols"
"tr_static_init: 256 + dist != 512"
"tr_static_init: dist != 256"
"tr_static_init: length != 256"
"trees.h"
"unexpected end of file"
"unknown compression method"
"unknown header flags set"
"unknown win32 error (%ld)"
"w"
"wild scan"
"zcfree: ptr not found"
"{%u,%u,%d}"
"{{%2u},{%2u}}%s"
"{{%3u},{%3u}}%s"
"}%s"
"};\n"
"};\n\n#endif\n"
"};\n\n#endif\n\n#endif\n"
"};\n\nlocal const z_word_t FAR crc_braid_big_table[][256] = {\n"
```

### 静态对象

| `Statics` 的字段 | C 对象 | 元素 | 来源 |
| --- | --- | --- | --- |
| `dist_code` | `_dist_code` | 512 x `UInt8` | 头文件 |
| `length_code` | `_length_code` | 256 x `UInt8` | 头文件 |
| `base_dist` | `base_dist` | 30 x `Int32` | 头文件 |
| `base_length` | `base_length` | 29 x `Int32` | 头文件 |
| `crc_table` | `crc_table` | 256 x `UInt32` | 头文件 |
| `static_dtree` | `static_dtree` | 30 x `CtData` | 头文件 |
| `static_ltree` | `static_ltree` | 288 x `CtData` | 头文件 |
| `x2n_table` | `x2n_table` | 32 x `UInt32` | 头文件 |
| `lenfix` | `lenfix` | 512 x `Code` | inffixed.h（由 inftrees.c 包含；原样复制） |
| `distfix` | `distfix` | 32 x `Code` | inffixed.h（由 inftrees.c 包含；原样复制） |
| `extra_lbits` | `extra_lbits` | 29 x `Int32` | trees.c |
| `extra_dbits` | `extra_dbits` | 30 x `Int32` | trees.c |
| `extra_blbits` | `extra_blbits` | 19 x `Int32` | trees.c |
| `static_l_desc` | `static_tree_desc` | `StaticTreeDesc` | trees.c |
| `static_d_desc` | `static_tree_desc` | `StaticTreeDesc` | trees.c |
| `static_bl_desc` | `static_tree_desc` | `StaticTreeDesc` | trees.c |

脚本运行时从 `trees.c` 读取这三个描述符（将结构体声明与脚本的字段列表比较）。
其成员 `(static_tree, extra_bits, extra_base, elems, max_length)` 分别为：

* `static_bl_desc` = (`(const ct_data *)0`, `extra_blbits`, 0, 19, 7)
* `static_d_desc` = (`static_dtree`, `extra_dbits`, 0, 30, 15)
* `static_l_desc` = (`static_ltree`, `extra_lbits`, 257, 286, 15)

`bl_order`（`trees.c` 中的 `local const uch bl_order[BL_CODES]`）不是 `Statics` 的字段：只对它进行索引，
从不取地址，因此 `trees.c` 的翻译将其保存为普通常量。
