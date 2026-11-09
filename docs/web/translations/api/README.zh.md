<!--
source: docs/api/README.md
source-sha256: 68066a63bc54ad3423ebe8848b9089a2d3ba9f55ce7a2d58c34f39d53d665b3d
-->

# zlib API 手册

[文档](../README.md) / API 手册

从这里开始查找 zlib 函数、理解调用者的义务，或了解流的生命周期。
每个条目给出 C 函数签名、用途、**Pre**（前置要求）、**Post**（结果）、
**Effects**（允许的修改），以及影响使用方式的边界情况。

## 选择起点

| 如果你想…… | 阅读 |
| --- | --- |
| 理解契约术语和构建范围 | [怎样阅读契约](contracts.md) |
| 管理缓冲区、所有权、重置和流调用顺序 | [流的共同规则](streams.md) |
| 通过 `z_stream` 增量压缩 | [流式压缩](deflate-stream.md) |
| 通过 `z_stream` 增量解压 | [流式解压](inflate-stream.md) |
| 通过回调提供解压输入并接收输出 | [回调解压](inflate-back.md) |
| 压缩或解压整个缓冲区，或查询库信息 | [缓冲区工具和库信息](utility.md) |
| 计算或合并 Adler-32 和 CRC-32 校验值 | [校验值](checksums.md) |
| 读取、写入、定位或关闭 gzip 文件句柄 | [Gzip 文件](gz-file.md) |

本手册遵循固定版本的源码及列出的补丁，首先针对默认 LP64 Linux 静态构建和默认分配器。
各条目会说明额外限制。Windows 的 `gzopen_w` 条目与该构建分开。
这些是限定范围的文档契约；某些前置条件比公开头文件允许的范围更窄。
不满足所述 Pre 的调用不在该契约范围内，并不自动意味着其 C 行为未定义。
见[范围偏离](../deviations.md)。

从 C 读出的行为仍有待实现证明**确认（to confirm）**。
本手册不报告已经完成的验证，也不改变范围更广的[已登记公开目标](../checking/goals.md)。
[概览](../overview.md)是证明状态和剩余工作的唯一记录。

## 查找函数

下面的索引按用途分组，链接到全部 96 个条目。
函数页面保留 C 名称，包括初始化宏使用的尾随下划线。

### 流式压缩

| 函数 | 简述 |
| --- | --- |
| [deflateInit_](deflate-stream.md#deflateinit_) | 使用默认窗口、内存级别和策略初始化 |
| [deflateInit2_](deflate-stream.md#deflateinit2_) | 使用全部参数初始化 |
| [deflateSetDictionary](deflate-stream.md#deflatesetdictionary) | 预加载字典 |
| [deflateGetDictionary](deflate-stream.md#deflategetdictionary) | 复制出当前字典窗口 |
| [deflateResetKeep](deflate-stream.md#deflateresetkeep) | 重新开始流，但保留窗口和哈希（未公开文档化） |
| [deflateReset](deflate-stream.md#deflatereset) | 重新开始流 |
| [deflateSetHeader](deflate-stream.md#deflatesetheader) | 提供要写出的 gzip 头部 |
| [deflatePending](deflate-stream.md#deflatepending) | 报告待输出的数据 |
| [deflateUsed](deflate-stream.md#deflateused) | 报告上一次 flush 的最后一个字节中已使用的位数 |
| [deflatePrime](deflate-stream.md#deflateprime) | 向输出插入位 |
| [deflateParams](deflate-stream.md#deflateparams) | 修改级别和策略 |
| [deflateTune](deflate-stream.md#deflatetune) | 设置内部匹配搜索的调优值 |
| [deflateBound_z](deflate-stream.md#deflatebound_z) | 压缩大小的上界（size 类型） |
| [deflateBound](deflate-stream.md#deflatebound) | 压缩大小的上界（`uLong`） |
| [deflate](deflate-stream.md#deflate) | 压缩 |
| [deflateEnd](deflate-stream.md#deflateend) | 释放流 |
| [deflateCopy](deflate-stream.md#deflatecopy) | 复制流 |

### 流式解压

| 函数 | 简述 |
| --- | --- |
| [inflateResetKeep](inflate-stream.md#inflateresetkeep) | 重新开始流并保留窗口内容（未公开文档化） |
| [inflateReset](inflate-stream.md#inflatereset) | 重新开始流，丢弃窗口内容 |
| [inflateReset2](inflate-stream.md#inflatereset2) | 使用新窗口大小重新开始流 |
| [inflateInit2_](inflate-stream.md#inflateinit2_) | 使用指定窗口大小初始化 |
| [inflateInit_](inflate-stream.md#inflateinit_) | 使用默认窗口大小初始化 |
| [inflatePrime](inflate-stream.md#inflateprime) | 向输入插入位 |
| [inflate](inflate-stream.md#inflate) | 解压 |
| [inflateEnd](inflate-stream.md#inflateend) | 释放流 |
| [inflateGetDictionary](inflate-stream.md#inflategetdictionary) | 复制出窗口 |
| [inflateSetDictionary](inflate-stream.md#inflatesetdictionary) | 提供字典 |
| [inflateGetHeader](inflate-stream.md#inflategetheader) | 请求获取 gzip 头部 |
| [inflateSync](inflate-stream.md#inflatesync) | 搜索 full flush 点 |
| [inflateSyncPoint](inflate-stream.md#inflatesyncpoint) | 检查是否停在 sync flush 点 |
| [inflateCopy](inflate-stream.md#inflatecopy) | 复制流 |
| [inflateUndermine](inflate-stream.md#inflateundermine) | 请求距离检查选项；默认构建返回 `Z_DATA_ERROR` |
| [inflateValidate](inflate-stream.md#inflatevalidate) | 控制封装完整性检查 |
| [inflateMark](inflate-stream.md#inflatemark) | 报告 `inflate` 在块或编码中的位置 |
| [inflateCodesUsed](inflate-stream.md#inflatecodesused) | 报告当前块使用的编码表条目数（未公开文档化） |

### 回调解压

| 函数 | 简述 |
| --- | --- |
| [inflateBackInit_](inflate-back.md#inflatebackinit_) | 为回调解压初始化 |
| [inflateBack](inflate-back.md#inflateback) | 使用输入和输出回调解压 |
| [inflateBackEnd](inflate-back.md#inflatebackend) | 释放流 |

### 整缓冲区操作和库信息

| 函数 | 简述 |
| --- | --- |
| [compress2_z](utility.md#compress2_z) | 按指定级别压缩缓冲区（size 类型） |
| [compress2](utility.md#compress2) | 按指定级别压缩缓冲区 |
| [compress_z](utility.md#compress_z) | 按默认级别压缩缓冲区（size 类型） |
| [compress](utility.md#compress) | 按默认级别压缩缓冲区 |
| [compressBound_z](utility.md#compressbound_z) | 压缩大小的上界（size 类型） |
| [compressBound](utility.md#compressbound) | 压缩大小的上界 |
| [uncompress2_z](utility.md#uncompress2_z) | 解压缓冲区，报告已使用的输入量（size 类型） |
| [uncompress2](utility.md#uncompress2) | 解压缓冲区，报告已使用的输入量 |
| [uncompress_z](utility.md#uncompress_z) | 解压缓冲区（size 类型） |
| [uncompress](utility.md#uncompress) | 解压缓冲区 |
| [zlibVersion](utility.md#zlibversion) | 库的版本字符串 |
| [zlibCompileFlags](utility.md#zlibcompileflags) | 构建该库时使用的类型大小和选项 |
| [zError](utility.md#zerror) | 返回码对应的文本 |

### 校验值

| 函数 | 简述 |
| --- | --- |
| [adler32_z](checksums.md#adler32_z) | 缓冲区的 Adler-32（size 类型） |
| [adler32](checksums.md#adler32) | 缓冲区的 Adler-32 |
| [adler32_combine](checksums.md#adler32_combine) | 合并两个 Adler-32 值 |
| [adler32_combine64](checksums.md#adler32_combine64) | 合并两个 Adler-32 值（64 位长度） |
| [get_crc_table](checksums.md#get_crc_table) | CRC-32 表 |
| [crc32_z](checksums.md#crc32_z) | 缓冲区的 CRC-32（size 类型） |
| [crc32](checksums.md#crc32) | 缓冲区的 CRC-32 |
| [crc32_combine_gen64](checksums.md#crc32_combine_gen64) | 生成用于合并的算子（64 位长度） |
| [crc32_combine_gen](checksums.md#crc32_combine_gen) | 生成用于合并的算子 |
| [crc32_combine_op](checksums.md#crc32_combine_op) | 使用算子合并 |
| [crc32_combine64](checksums.md#crc32_combine64) | 合并两个 CRC-32 值（64 位长度） |
| [crc32_combine](checksums.md#crc32_combine) | 合并两个 CRC-32 值 |

### Gzip 文件

| 函数 | 简述 |
| --- | --- |
| [gzopen](gz-file.md#gzopen), [gzopen64](gz-file.md#gzopen64), [gzdopen](gz-file.md#gzdopen), [gzopen_w](gz-file.md#gzopen_w) | 打开文件 |
| [gzbuffer](gz-file.md#gzbuffer), [gzsetparams](gz-file.md#gzsetparams) | 缓冲区大小、压缩参数 |
| [gzread](gz-file.md#gzread), [gzfread](gz-file.md#gzfread), [gzgetc](gz-file.md#gzgetc), [gzgetc_](gz-file.md#gzgetc_), [gzungetc](gz-file.md#gzungetc), [gzgets](gz-file.md#gzgets) | 读取 |
| [gzwrite](gz-file.md#gzwrite), [gzfwrite](gz-file.md#gzfwrite), [gzputc](gz-file.md#gzputc), [gzputs](gz-file.md#gzputs), [gzprintf](gz-file.md#gzprintf), [gzvprintf](gz-file.md#gzvprintf), [gzflush](gz-file.md#gzflush) | 写入 |
| [gzrewind](gz-file.md#gzrewind), [gzseek](gz-file.md#gzseek), [gzseek64](gz-file.md#gzseek64), [gztell](gz-file.md#gztell), [gztell64](gz-file.md#gztell64), [gzoffset](gz-file.md#gzoffset), [gzoffset64](gz-file.md#gzoffset64) | 定位 |
| [gzeof](gz-file.md#gzeof), [gzdirect](gz-file.md#gzdirect), [gzerror](gz-file.md#gzerror), [gzclearerr](gz-file.md#gzclearerr) | 状态 |
| [gzclose](gz-file.md#gzclose), [gzclose_r](gz-file.md#gzclose_r), [gzclose_w](gz-file.md#gzclose_w) | 关闭 |

## 构建变体和宏

在 `zlib.h` 声明的函数中，以下内容不会编译进默认 Linux 库：

| 名称 | 原因 |
| --- | --- |
| `gzopen_w` | 仅为 Windows（`_WIN32`）声明；`gzlib.c` 中的定义位于宽字符选项之下 |
| `deflateInit`, `deflateInit2`, `inflateInit`, `inflateInit2`, `inflateBackInit` | 这些是 `zlib.h` 中的宏；它们调用 `deflateInit_`、`deflateInit2_`、`inflateInit_`、`inflateInit2_`、`inflateBackInit_`，并传入头文件自身的版本字符串和 `sizeof(z_stream)` |
| 作为宏的 `gzgetc` | `zlib.h` 还把 `gzgetc` 定义为宏，直接读取缓冲区，并在缓冲区为空时调用 `gzgetc_`；`gzgetc` 函数也同样存在 |

索引包含全部 95 个默认构建条目，以及单独的 Windows 条目 `gzopen_w`。
[内部辅助函数契约](../design/internal-contracts.md)描述库内部使用的例程。
