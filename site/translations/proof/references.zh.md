<!-- source-sha256: 911099fbe671bb0702a4b991fe59b019167e3286370c6c065025b1a7ee77fc1e -->
# 早期论证与参考来源

主要参考快照为 [zlib-formal 的 `0f1428677ebf5b1614ff77f4702bbb382b2bf3c6`](https://github.com/cla7aye15I4nd/zlib-formal/tree/0f1428677ebf5b1614ff77f4702bbb382b2bf3c6)。参考审查阅读过其源代码和审计文档，没有重新构建快照，也没有在本仓库建立其结果。这里是复用记录；[进度](../progress.md)负责当前工作，[检查指南](../checking/README.md)定义验收。

## 借鉴的思路

阅读这份索引时，先用中间一列找需要的论证，再用左列定位旧来源，最后看右列的适用边界。路径和声明名保持原样，是为了能跳到实际定义；它们不是要求读者预先掌握的算法术语。后面的函数族表也按“可复用内容 → 当前落点”提供检索。

| 参考来源 | 此处的改编 | 边界 |
| --- | --- | --- |
| `Spec/Api/InflateApi.lean`：`Call`, `exec` | `ZlibF/Spec/Public/Calls.lean` 中封闭的公开调用集合与直接分派 | 入口覆盖不证明每个入口或调用序列 |
| `translation_map.py` | 清单检查公开名称、定义文件与手册章节 | 不是完整的预处理后语法比较 |
| `check_imports.py` | 检查传递根导入闭包与缺失源文件 | 模块位于闭包不表示它证明了公开目标 |
| `final_check.sh` | 区分开发检查、规范就绪和最终验收 | 快速构建不等于最终验收 |
| `Spec/crc32.lean`, `Spec/adler32.lean` | 独立的位／寄存器及模和校验规范 | 保留非规范种子与独特的单字节 Adler 行为 |
| `check_axioms.py` | 拒绝空／重复登记表；避免被优化禁用的检查；审查已登记名称之外的声明 | 仅登记不能验证声明定义域或翻译忠实性 |
| `Witness/`, `CONTRACT_AUDIT.md` | 在序列目标旁增加初始化定义域目标与非空泛性要求 | 实际初始化必须建立调用所用的同一个不变量 |

表中路径相对于参考仓库的 `lean/` 目录。下表映射函数族与改变的表示。

## 不能直接迁移的部分

参考堆使用带类型单元和字节块；当前堆使用对象记录与表。堆声明和证明项需要适配。纯算术、位流关系、循环度量和分解，只有比较其定义与定义域之后才能保留含义。

参考序列定理 `Zlib.Api.seq_safe` 将 `ApiContract` 作为假设。其契约审计记录过假前置条件实例与错误策略契约。调用集合与归纳结构有价值，但条件序列定理不能在这里建立安全：每个库内被调用函数需要关于实际翻译的定理，实际初始化必须建立不变量。不相关的见证不能补足这一连接。

参考仓库的 `ub.patch` 政策及启用补丁不同，其构建配置和证明状态不会自动迁移。本仓库验证自己的上游固定版本与已审查补丁，采用自己的公开定义域和验收规则。

```mermaid
flowchart LR
    R[固定参考版本] --> M[提取数学与论证结构]
    M --> T[针对当前源代码与堆重新陈述]
    T --> K[内核检查、审计与变异]
    K --> C[仅接受本仓库的证据]
```

下表用于定位可复用论证族。[组件证明指南](README.md)解释当前论证结构。参考链接与历史测试报告都不属于新的验证运行。

## 复用早期论证

旧堆使用带标签单元和字节块，当前堆使用记录与对象表。纯论证只有在定义和定义域一致后才能迁移。堆级证明需要新的执行、帧性质和所有权论证。早期对被调用函数契约的假设不能替代实际翻译后函数的定理。

## Deflate 引擎来源

| 来源族 | 数学或操作内容 | 当前源代码族 |
| --- | --- | --- |
| `EngineChains` | 滚动哈希在三次更新后遗忘旧值；掩码键界限；键与前两个字节相同时第三字节一致 | `deflate.c.engine.hash` |
| `EngineChains`, `Spec/deflate/Engine` | 环槽算术；链可达性；插入／滑动保持；链位置递减 | `deflate.c.engine.chains` |
| `EngineFillSlide`, `EngineFill` | 滑动阈值、读取数、插入数、`high_water` 和不相交滑动复制范围 | `deflate.c.engine.window` |
| `EngineMatch`, `matchChain_spec`, `innerLoop_spec` | 首个不匹配、每轮八次比较、最大长度 258 与结果限幅 | `deflate.c.engine.match`, `.lminner`, `.lmcond`, `.lmbody`, `.lmmain` |
| `PendingPut`, `DeflatePut`, `Hash`, `LmInit` | 待输出字节顺序、哈希更新、插入存储与清除 | `deflate.c.engine.macros` |
| `EngineSlide` | 每个哈希项变为 `m >= w_size ? m - w_size : 0`；准确帧性质 | `deflate.c.engine.slide` |
| `EngineReadBuf` | 复制 `min(avail_in, size)` 字节，推进入口计数并更新所选校验和 | `deflate.c.engine.readbuf` |
| `PendingFlush` | 刷出树位、复制待输出字节、推进输出计数并重设空 pending 指针 | 待输出字节复制与树位缓冲证明 |

## Deflate 生命周期来源

| 早期来源 | 保留内容 | 当前源代码族 |
| --- | --- | --- |
| `Inv`, `Inv7`, `Heap` | 回指针、缓冲区分离、范围、存储保持与帧性质 | `deflate.c.base` |
| `StateCheckQuick`, `End` | 空指针与无效流拒绝；准确状态检查结果 | 基础检查引理 |
| `TuneQuick`, `HeaderQuick`, `UsedQuick`, `PendingQuick`, `Simple` | 四项调优写入；仅 gzip 的头存储；可选输出写入；待输出计数溢出 | `deflate.c.life.check` |
| `Bound` | 包装长度、`extra_len` 低 16 位、终止字符串与界限算术 | `deflate.c.life.bound`，包括 `boundTail`、`WrapLen` |
| `InitParams`, `Init*` | 参数规范化、二的幂、缓冲区大小与配置表范围 | 支持初始化的算术和基础不变量 |
| `End` | 精确依赖状态的结果、五次释放和流状态指针清除 | `deflate.c.life.end` |
| `LmInit`, `Reset*`, `ResetTr` | 哈希清除、调优表、计数器、包装状态与树重设 | `deflate.c.life.reset` |
| `InitFail*`, `InitOk*`, `InitMem`, `InitFresh` | 每次失败分配及其清理；准确成功状态 | 初始化论证结构 |
| `Prime*`, `PrimeArith` | 移动待输出字节；保持其位值；追加请求的低位 | 位预置算术与执行分解 |
| `Copy*` | 拒绝、失败清理、独立缓冲区与重定向树指针 | 复制论证结构 |
| `DictGet`, `GetDictQuick` | 返回窗口末尾的 `min(strstart + lookahead, w_size)` 字节 | `deflate.c.life.getdict` |

## Inflate 来源

| 早期族 | 内容 | 当前源代码族 |
| --- | --- | --- |
| `natBits`, `bytesBits`，移位与掩码引理 | 低位列表、字节追加、丢弃位和格式位序 | `inflate.c.main.bits` |
| `InflateBits` | `PULLBYTE`, `NEEDBITS`, `BITS`, `DROPBITS`, `BYTEBITS`, `INITBITS`；保持已存位后接未读字节的关系 | `inflate.c.main.macros` |
| `InflateTopLoop`, `InflateLoop` | 递减度量与每个循环退出 | `inflate.c.main.xloop` |
| `SpecStored`, `SpecStoredCopy`, `Copy*` | 存储长度／补码检查与原样复制字节 | `inflate.c.main.stored`, `.stored2` |
| `InflateHead`, `InflateHdr*`, `InflateName` | 头检查、字段长度、可选头写入与 CRC | 模式论证与头部算术 |
| `InflateTable`, `InflateTables`, `InflateCodeLens*` | 动态计数、码长顺序、重复与表安装 | `inflate.c.main.table` 至 `.table6`；见配套记录 |
| `InflateLen*`, `InflateDist*`, `InflateMatch*` | 慢速查找、子表、距离检查与窗口／输出复制 | 符号、查找与复制论证结构 |
| `InflateCheck`, `InflateCheckStep` | 总计、校验和更新与尾部比较 | `inflate.c.main.check0`, `.check` |
| `InflateCases1`, `InflateUpd`, `InflateFixed` | 简单模式、分派、拒绝与固定表选择 | simple/type 模块和固定表定理 |
| `infLeave_ok`, `leaveTail_ok`, `updatewindow_frame` | 寄存器回写、窗口更新、计数器与返回码规则 | 收尾组合论证 |

## 表与尾部来源

| 早期来源 | 可复用论证 | 当前源代码族 |
| --- | --- | --- |
| `InflateTables`（约 1,161 行） | 在读取三比特码长的 `LENLENS` 阶段，`ncode` 是要读的组数，`have` 是已读组数，`available_bits` 是当前可用位数；一次读取 `min(ncode - have, available_bits / 3)` 组；顺序排列、`lensRead`、`lensZero`、`Good3`；读取和补零循环 | `inflate.c.main.table` 至 `.table6` |
| `InflateCheck`, `InflateCheckStep` | 输出总计、校验和更新与字节交换后的 zlib 比较 | `inflate.c.main.check0`, `.check` |
| `InflateBits` | 补充／消费位，不改变所表示流 | 共享 `inflate.c.main.macros` 结果 |

## 回调来源

| 早期族 | 可复用内容 | 当前源代码族 |
| --- | --- | --- |
| 初始化检查与分配 | 版本、大小与参数拒绝；内存失败；成功时准确写入字段 | `infback.c.init` |
| End 与入口退出 | 无效流／状态拒绝；释放状态并清除指针 | `infback.c.end`, `.back` |
| 首次输入耗尽 | `in` 未提供字节、缓冲区错误、恢复输入字段、不调用输出回调 | `infback.c.back` |
| 回调契约与见证 | 自有块集合和局部不变量；具体已初始化示例 | `infback.c.callbacks` |
| 输入宏 | 补充／消费位、回调转移与剩余输入度量 | `infback.c.pull`, `.macros` 及共享 inflate 位引理 |
| 输出空间与窗口写入 | 将满窗口交给 `out`，保持先前输出并扩展输出视图 | `infback.c.room`, `.stored` |
| `TYPE`、固定表与错误模式 | 最终块判断、块类型、固定表字段与错误消息 | `infback.c.inv` 和 `inflate_fixed_ok` |
| 存储块与码长顺序 | 对齐、补码检查、有界分段复制；顺序排列 | `infback.c.pure`, `.stored` |
| 动态表与慢速查找 | 计数、重复、构造调用及规范根／子表一致性 | 需对当前表语义重新陈述的早期论证结构 |
| 分派与离开 | 下降循环度量、最终输出回调、准确结果与输入回写 | 当前循环规则和组合论证 |

## Gzip 来源

| 早期族 | 可复用内容 | 当前源代码族或边界 |
| --- | --- | --- |
| `Basic` | 字段布局与标签 | 由记录访问和流引用替代 |
| `Simple` | 缓冲设置、EOF、tell、错误查询和整数限制 | `gzlib.c.simple` |
| `Error`, `ErrorMsg` | 释放旧消息、存储码、分配并格式化 `path: text`、分配失败 | `gzlib.c.error` 覆盖空消息路径；格式化消息需要准确格式化语义 |
| `Reset`, `Rewind` | 重设字段和错误、拒绝规则、文件定位与按输入修正偏移 | `gzlib.c.error`, `.rewind` |
| `SeekParts`, `SeekRaw`, `SeekFwd`, `SeekBack`, `SeekTail`, `SeekMain`, `SeekCor` | 目标算术与 raw、向前、向后分支 | `gzlib.c.seek` |
| `SeekNeg`, `SeekNegUb`, `SeekFault`, `SeekWitness` | 负位置与有符号溢出路径 | 条件性的准确故障引理，不是公开安全定理 |
| `OpenMode`, `OpenParts`, `OpenRest` | 模式字符折叠与遇到 `+` 时清理 | `parseMode` 和打开论证结构 |
| `OpenPath`, `OpenDesc`, `OpenFinish`, `OpenEff*`, `GzopenEff*`, `Dopen*` | 路径复制、描述符标志、追加／截断效果与失败清理 | 准确格式化、文件效果和所有权必须组合 |
| `Close`, `Dispatch` | 读／写分派和存活块核算 | `gzclose.c`；实际读／写清理属于各自文件 |

## 历史短距离检查

旧记录报告过一次实验，检查快速路径前可能缺少 `whave` 更新的疑点。raw 固定 Huffman 流使用一至三个字面量，随后接长度三、距离一至四的匹配。矩阵包括：至少六个输入字节、258 字节输出空间的快速调用；输入每次只给一字节；以及使用新输出缓冲区的两次调用解码。记录报告路径一致、出现预期的“invalid distance too far back”错误，且运行时检测器没有发现问题。

实验只对这些普通 `inflate` 情形反驳了候选问题，未覆盖长距离、完整或环绕窗口、其他窗口大小或回调解码器。它是历史测试证据，不是内核证明，也不是本次重新执行的验证。

## 证据边界

早期审查记录过 8000 次随机压缩会话，使用运行时检测器与往返比较。变化包括级别、策略、内存级别、包装、最小一字节输出块、刷新模式、参数改变和复制。记录报告这些会话中无不一致或运行时检测器诊断。该运行不包含字典设置、位预置、自定义 gzip 头，也排除了单字节窗口的 stored 路径。

这些观察不证明全部输入的安全、初始化历史、共享存储容量、其他配置或上述 C 假设。聚焦且可复现的证据应与其回归放在一起。验收规则属于[检查指南](../checking/README.md)，[进度](../progress.md)记录当前未解决项与证明验收。

## 历史 gzip 定位观察

早期记录报告：读取五字节到 EOF，再从当前位置向前定位五字节。Seek 返回十，而 tell 仍为五。其解释是向前定位保留 `past`；旧抽象关系却要求目标位置并清除该标志。本次修订未重新执行此实验。该源代码路径的操作细化尚未完成，记录只保留这次历史观察。
