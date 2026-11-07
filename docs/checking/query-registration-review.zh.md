# 公开查询登记审阅

源码审阅在检查过的快照中未发现类型或定义域阻塞。此次登记不改变目标、翻译或证明主体。

新增的六个证明在提供的编译导出中具有精确目标常量类型、允许的公理和函数文档字符串。查询契约覆盖所有堆；get_crc_table 显式要求已初始化的 CRC 全局状态。两个界限查询覆盖每个 UInt64 输入，断言精确的饱和数值公式，而非输出容量充分性。zError 覆盖每个 Int32；固定版本上游的 ERR_MSG 宏在减法前保护上下两端的越界情形。

二十个变异锚点都在指定函数主体内恰好出现一次。头部／签名和其他声明保持不变。返回空指针的语法经过独立类型检查，未进行构建。下表给出具体允许输入上的行为差异。

| 变异 | 允许输入 | 原版 | 变异版 |
| --- | --- | --- | --- |
| zlibVersion-wrong-string | 任意堆 | 固定版本的非空版本字符串 | 空字符串 |
| zlibVersion-null-pointer | 任意堆 | 只读静态版本指针 | NULL |
| zlibCompileFlags-uint | 任意堆 | 169 | 168 |
| zlibCompileFlags-ulong | 任意堆 | 169 | 165 |
| zlibCompileFlags-pointer | 任意堆 | 169 | 153 |
| zlibCompileFlags-offset | 任意堆 | 169 | 105 |
| zError-lower-bound | err=-6 | 版本不兼容 | 空文本 |
| zError-upper-bound | err=2 | 需要字典 | 空文本 |
| zError-message-index | err=1 | 流结束 | 需要字典 |
| zError-out-of-range-index | err=3 | 空文本 | 需要字典 |
| zError-null-result | err=0 | 只读静态空字符串指针 | NULL |
| get_crc_table-wrong-offset | 具有 CrcGlobals 的堆 | 偏移为零的 CRC 表 | 偏移为一；首个表项不同 |
| get_crc_table-wrong-table | 具有 CrcGlobals 的堆 | CRC 表 | x2n 表；对象、大小及首项不同 |
| get_crc_table-null-pointer | 具有 CrcGlobals 的堆 | CRC 表指针 | NULL |
| compressBound_z-first-shift | sourceLen=2048 | 2061 | 2062 |
| compressBound_z-second-shift | sourceLen=8192 | 8207 | 8208 |
| compressBound_z-third-shift | sourceLen=16777216 | 16782349 | 16782350 |
| compressBound_z-constant | sourceLen=0 | 13 | 12 |
| compressBound_z-overflow-guard | sourceLen=0 | 13 | 18446744073709551615 |
| compressBound-wrapper-result | sourceLen=0 | 13 | 14 |

二十个严格模块变异都从通过的正向基线出发完成检查。六个精确公开证明通过全新内核的基线重放，并拒绝每个所需映射变异。已有的错误清除和代码数量映射也通过其精确重放。

四个补充错误码边界／下标变异仍保留在严格列表中。`zError-lower-bound` 的原证明重放超过内核递归限制，不计为语义拒绝。其余三个边界／下标精确重放未执行。所需映射使用经过独立审阅的返回空指针变异，其严格检查和原证明重放均通过。没有放宽任何拒绝规则。

这些是本地登记检查。它们不证明完整的 C 翻译忠实性，不批准累积的语义锁变化，也不报告 CI 通过。当前验收状态和剩余工作见[进度](../progress.md)。
