# 流式解码：模式、历史与调用组合

源文件：`zlib/inflate.c`；翻译：`ZlibF/Zlib/inflate.c.lean`。
公开行为见 [API 指南](../spec/api/README.md)，解出的流见[格式指南](../spec/format/README.md)，
窗口更新见[内部契约](../spec/internal-contracts.md)中的 `I-uw-*`。

证明使用[解码表](inftrees.md)、[快速解码](inffast.md)、[Adler-32](adler32.md)、
[CRC-32](crc32.md)与[分配](zutil.md)。本页描述它们必须支持的组合，
并不把整个解码器标为已证明。当前进度统一记录在[进度页](../progress.md)。

## 输入范围与路径组合

[共用输入配置](../spec/input-configurations.md#inflate-inputs)定义严格嵌套的默认、常见及完整流参数范围。
完整且范围明确的声明使用同一套覆盖颜色。精确入口契约保持其原有定义域。
较小的分支引理仍是组合证明的依据，其前提必须明确。

这个解码器由可用输入字节、输出空间及已有缓冲比特选择快速路径。
默认输入配置也需要同时处理快、慢两条路径。分派条件不能成为排除小缓冲区、部分输入或动态 Huffman 块的理由。
表构造、分派与退出必须在实际返回堆之间传递同一不变量与历史。

## 内存与所有权

```mermaid
flowchart LR
    Stream["调用者的 z_stream"] --> State["自有 inflate_state"]
    State --> Window["自有、延迟分配的窗口"]
    State --> Codes["内嵌动态码表"]
    State --> Fixed["只读固定表"]
    State --> Header["调用者的 gz_header 与缓冲区"]
    Stream --> Input["调用者输入视图"]
    Stream --> Output["调用者输出视图"]
```

流拥有其已分配状态及窗口。`lens[320]`、`work[288]` 和 `codes[1444]` 内嵌在状态中。
`lencode` 与 `distcode` 选择静态固定表或 `codes` 的某个区域；`next` 跟踪表构造位置。
`head` 指向调用者拥有的头部存储。不变量必须记录这些替代情形、已初始化范围及获准访问的字节视图。

初始化必须在指针字段读取前建立它们。运行时把新分配指针表示为 null 的约定，
并不能证明这种先写后读的时序事实，见[安全规范](../spec/safety.md#uninitialised-memory)。
不变量也应涵盖错误模式，以保证拒绝或数据错误后仍能安全清理。

## 窗口不变量 W 与 F4

用 **W** 表示环形缓冲区的形状：

1. `wsize = 0` 或 `wsize = 2^wbits`。
2. `window` 为 null，或指向已分配的 `2^wbits` 字节块；`wsize > 0` 蕴含存储非 null。
3. `whave ≤ wsize`；若 `wsize > 0`，则 `wnext < wsize`；否则 `wnext = 0`。
4. 若 `whave < wsize`，则 `wnext = whave`。

初始化建立空窗口。必须逐一检查各个 Reset 变体：重置计数、保留已有存储、改变窗口大小是不同操作。
只有实际释放存储的大小变更路径，才可移除相应所有权声明。

功能正确性还要给 W 加上环中内容：有效的 `whave` 个字节按环顺序对应逻辑历史的适当后缀。
预置字典字节贡献历史，但不成为输出。仅有 W 的形状不能证明向后引用返回正确字节。

### `updatewindow(strm, end, copy)`

`I-uw-pre` 提供可读源区间 `[end-copy, end)`，以及每次 `memcpy` 所需的不重叠事实。
源可以是最近输出，也可以是获准的字典范围。公开调用者必须提供这些事实，不能默默排除合法视图。

若需要分配但分配失败，函数返回 1，且不取得窗口块。
必须证明准确的字段／帧效果，不能由失败码推断整个堆不变。
如果成功分配后 `wsize` 为零，则把它设为 `2^wbits`，并初始化 `wnext = whave = 0`。

对 `copy ≥ wsize`，只保留 `[end-wsize, end)`，写整个窗口，并设 `wnext = 0`、`whave = wsize`。

对 `copy < wsize`，令 `dist = min(wsize-wnext, copy)`。
第一次复制把源前缀写入 `[wnext, wnext+dist)`。
若仍有字节，则 `dist = wsize-wnext`；第二次复制写 `[0, copy-dist)`，此时环已填满。
设置 `wnext = copy-dist`、`whave = wsize`。

若没有剩余字节，则把 `wnext` 增加 dist，并在 `wsize` 处回绕。
若旧环未填满，W.4 给出 `whave = wnext`，同样的加法使 `whave` 增加到不超过 `wsize`；
仍未满时恢复 W.4。若旧环已满，则保持已满。以上建立形状保持论证。
内容论证要在同样的分支中跟踪最新后缀。
还应涵盖零字节复制，以及实际源视图所对应的准确指针形成。

## 模式证明

每个实际模式在共同不变量下有一个执行分支。分组图展示数据流，不能替代源代码中的各模式或出口。

```mermaid
stateDiagram-v2
    state "头部" as Header
    state "字典" as Dictionary
    state "块类型" as Type
    state "存储块" as Stored
    state "编码表" as Tables
    state "符号" as Symbols
    state "尾部校验" as Check
    state "完成" as Done
    state "数据错误" as Bad
    [*] --> Header
    Header --> Dictionary: FDICT
    Header --> Type: 头部完成
    Dictionary --> Type: 字典已接受
    Type --> Stored: 存储块
    Type --> Tables: 动态块
    Type --> Symbols: 固定块
    Tables --> Symbols: 表已安装
    Stored --> Type: 块完成
    Symbols --> Symbols: 字面量或匹配
    Symbols --> Type: 块结束
    Type --> Check: 最后一个块完成
    Check --> Done
    Header --> Bad: 格式错误
    Tables --> Bad: 格式错误
    Symbols --> Bad: 格式错误
    Done --> [*]
    Bad --> [*]
```

| 源代码分组 | 所需执行事实 |
| --- | --- |
| 入口检查 | 无效流／参数返回规定错误，效果恰好在许可范围内。只有契约明确规定时，才可断言整个堆不变。 |
| `PULLBYTE` | `have == 0` 时在读取前离开；否则读取与游标增加消费一个有效字节。 |
| `NEEDBITS`、`BITS`、`DROPBITS` | 为每个实际请求的位数建立界限，并在减法前保证已有足够比特。移入字节时位数必须有效；默认 64 位 `hold` 保留读入比特。 |
| `HEAD` 到 `HCRC` | 验证包装字段；只在调用者提供容量内写 `extra`、`name`、`comment`。无符号减法前为 `length` 与进度计数建立界限。 |
| `DICTID`、`DICT` | 保持需要字典的状态及校验和效果；拒绝字典不能凭空产生已解码输出。 |
| `STORED`、`COPY` | `copy ≤ min(length, have, left)` 同时限制两个视图。为 `memcpy` 提供 API 中有依据的不重叠条件。 |
| `TABLE` | 默认检查给出 `nlen ≤ 286`、`ndist ≤ 30`，因而 `nlen+ndist ≤ 316 < 320`。 |
| `LENLENS` | `have < ncode ≤ 19` 限制 `order[have]`；补零完成提供给码长表的 19 个长度。 |
| `CODELENS` | 码 16 需要先前长度；重复次数检查防止写到 `nlen+ndist` 之外。 |
| 表安装 | 证明 `inflate_table` 的执行、表项含义及总预留量 `852+592 = 1444`，并安装所得表谓词。 |
| `LEN` 到 `DISTEXT` | 根表／子表读取使用已初始化项，恰好消费支撑该码字和附加位的比特。选择快速分支时证明其入口前提。 |
| `MATCH`、`LIT` | 限制输出写入，证明历史／窗口源有效，包括顺序输出内部的重叠。 |
| `CHECK`、`LENGTH` | 按规定宽度，把正确的包装校验和／长度与实际产生字节比较。 |
| `inf_leave` | 写回准确的游标／计数／比特，必要时更新历史，并保持规定的返回行为。 |

补充输入时，若请求 `n ≤ 32`，只有 `bits < n` 才会读入字节；
所以字节移位至多为 31，读入后的位数至多为 39。
其他掩码与丢弃操作需要各自与源代码对应的界限。
不能把每个 `BITS` 用法都当成固定的小常数：动态表宽度及链接项的界限来自表谓词。

外层循环需要考虑模式的度量。有些转换既不消费输入，也不产生输出。
应为进展点或返回点之间的内部转换建立界限，再与有限输入／输出及复制度量组合。
每个模式分别终止，并不能单独建立完整的 fuel 界限。

## 因果关系与跨调用历史

功能正确性必须独立于实现状态确定输出。解出的一个符号需要一段支撑它的源比特前缀。
解码器可能推测性地读到该前缀之后，也可能在离开快速路径前归还完整预读字节。
应把发出的符号与支撑比特关联，不能要求符号含义与所有推测性预读都一致。

早期针对整个预读区间的一致性条件是错误的。修正后的支撑比特前缀关系区分了两者。
同样，固定八字节的数据错误检测延迟存在反例。
没有证明就增大常数，不能建立因果错误定理。这些是规范／模型方面的经验，
并非已确认的上游内存问题。当前反例与验收记录见[进度](../progress.md)。

跨调用应保持累计比特前缀、输出前缀、逻辑历史、包装／校验和状态及字典需求。
应量化所有许可的输入拆分、输出空间拆分及 flush 值。
后续失败可能发生在实际输出之后：延迟窗口分配可在解压已经写出字节后返回 `Z_MEM_ERROR`。
错误契约必须保留这些效果，不能要求输出为空。

预置字典带来已知校验和要求，也可能提供在调用者给出字典前内容未知的历史。
要把这种未知历史与输出字节区分开。raw 字典替换、头部操作、priming 和恢复需要各自精确的 API 效果；
普通数据阶段的细化不会自动涵盖所有此类序列。
负值 priming 也需要一般的比特级连接，不能只依靠有限执行矩阵或模型见证。

## 生命周期与辅助函数

| 函数 | 证明必须组合的内容 |
| --- | --- |
| `inflateInit_`、`inflateInit2_` | 版本／大小及参数拒绝、状态分配、初始化写入、成功不变量与准确的失败清理。 |
| `inflateReset`、`inflateResetKeep`、`inflateReset2` | 各自不同的计数／历史／头部效果、许可的窗口大小变化及对应所有权转换。 |
| `inflateEnd` | 窗口与状态各释放一次，清空流状态，并恢复调用者先前的存活块集合。 |
| `inflatePrime` | 负计数重置与非负比特插入；移位、低位含义和计数上限拒绝。 |
| `inflateSetDictionary`、`inflateGetDictionary` | 文档规定的字典模式、校验和判定，以及按时间顺序的环形复制；历史不等于已产生输出。 |
| `inflateCopy` | 独立状态／窗口分配与失败清理；复制内容，重定位动态 `lencode`、`distcode`、`next`，保留静态指针，并证明未来行为等价。 |
| `inflateSync`、`syncsearch` | 有界扫描、恢复状态变化，以及丢弃输入与重新开始的解码阶段之间的关系。 |
| `inflateGetHeader` | 保存获准的调用者存储，并保持其生命周期／容量要求直到头处理完成。 |
| `inflateMark`、`inflateSyncPoint`、`inflateCodesUsed` | 每个许可模式中的准确数值／查询行为，包括拒绝情形。 |
| `inflateValidate`、`inflateUndermine` | 准确状态更新、支持／不支持的行为及不变量保持。 |

在指针模型下，对动态表与静态表指针做关系比较，需要审阅源代码。
历史上提及的 `inflateCopy` `ub.patch` 不构成补丁授权：选定补丁集只由 `patches/README.md` 定义。

最终序列定理使用 init 结果，以及各函数已证明的保持、帧与所有权效果。
它必须把内部历史、表谓词连接到独立格式关系。
抽象的 `inflate_decodes` 模型定理或局部快速调用定理，都不能独自提供这一实现细化。

## 与 C 的对应检查

### 控制流与位缓冲区

`inflate` 把 C 寄存器保存在 `IL` 中。每个模式是 `ExceptT Ex (StateT IL M)` 中的辅助函数。
switch 的 `break` 返回分派器。`Ex.leave` 携带当前寄存器跳至 `inf_leave`，不回滚先前读写。
`Ex.ret` 是直接的 C 返回。贯穿执行会调用下一个模式体。
分派器每轮从堆读取 `state->mode`。

以下细节可被观察到，必须跨辅助函数边界保持：

- `TYPE` 不写 `mode` 就进入 `TYPEDO`。若读块头时输入耗尽，保存的模式仍是 `TYPE`。
  这会影响 `data_type` 与下次入口。
- `PULLBYTE` 在改变任何内容前检查输入。失败的 `NEEDBITS` 保留此前迭代已经读入的全部字节。
  `DROPBITS` 先改变 `hold` 再从 `bits` 减去位数；`BYTEBITS` 的两个表达式都使用旧位数。
- `BITS(n)` 在与 `(1U << n) - 1` 做掩码前把 `hold` 转为 unsigned int。
  `hold` 本身是 unsigned long。该转换和移位宽度都不能简化。
- `HEAD` 中头部取模表达式在 64 位算术中，将无符号 32 位移位项加到 `hold >> 8`。
  priming 的高位参与该表达式。
- `DICT` 在 `RESTORE` 和输入总数更新后返回 `Z_NEED_DICT`，绕过普通收尾。
  `MEM` 与 `SYNC` 也直接返回。
- `CHECK` 更新输出总数和校验和，再重置局部输出基线。
  收尾使用已改变的基线，避免再次计算同一批字节。
- `inf_leave` 先恢复寄存器，再更新窗口。窗口分配失败在后续总数／校验和更新前返回 `Z_MEM_ERROR`。
  已写输出仍然存在；内存错误不意味着输出为空。

通常的规范化位缓冲区事实是 `bits ≤ 39`、`hold < 2^bits`。
它们是证明义务，并非对任意状态记录都成立的假设。
`inflatePrime` 在位数为负时清空缓冲区，拒绝超过 16 的计数或超过 32 的合计位数，
并先用 signed-long 表达式对 `value` 做掩码，再转为 unsigned long。负值必须遵循这个转换顺序。

`inflateMark` 也需要精确转换：对 `back` 符号扩展，转为 unsigned long，左移 16 位，
转回 signed long，再加无符号条件项。默认平台上超出范围的转换按模进行。
错误结果是 `-65536`。

### 窗口、字典、复制与缓冲区视图

保留历史是按时间顺序的数据，不只是任意存储中的 `whave` 个字节。
对于已分配窗口，`8 ≤ wbits ≤ 15`、`whave ≤ wsize`，且 `wsize > 0` 时 `wnext < wsize`；
未填满窗口满足 `wnext = whave`。完整环的时间顺序从 `wnext` 开始。
匹配证明必须把这个顺序连接到先前输出与字典。

`updatewindow` 分配未初始化字节，然后复制最后一个完整窗口，或绕环边界分成两段的后缀。
只能读取已写入的历史。`inflateGetDictionary` 先返回 `window + wnext` 起的尾部，再返回前缀。
`inflateSetDictionary` 在 `DICT` 验证 Adler 标识，并把字典末尾传给 `updatewindow`；
raw 替换的阶段语义不同于单个预置字典。
`inflateResetKeep` 保留历史；`inflateReset` 恢复请求设置并清空历史，释放大小改变的窗口。

`inflateCopy` 通过源分配器分配；若窗口分配失败，则释放新状态；
源检查或分配失败时清空 `dest->state`。成功时复制两个记录，修复流反向指针，
重定位内部表指针，并只复制 `whave` 个窗口字节。
`next` 始终指向状态的 `codes` 数组；`lencode`／`distcode` 指向该数组或共用固定表。
这些事实必须来自初始化与保持，**待确认（to confirm）**。源、目标记录不得重叠。

现有源代码用 `>=` 和 `<=` 检查 `lencode` 是否位于 `codes` 内。
使用固定表时，它们是不同对象。翻译保留这些比较及其故障，不实现历史建议 `lencode == codes`。
早期笔记记录了在固定块中暂停后复制流所触发的 sanitizer 指针对报告，
以及采用建议修改后的无报告运行。这是历史证据，不是本次文档修订执行的复现，也不是已应用补丁。

字节输入、输出、头部、字典范围必须满足各自实际访问要求。
运行时现在允许 `memcpy` 在同一字节对象内使用不相交区间；早先要求不同块的说法已经过时。
重叠仍会触发故障。要求不同原始块的局部快速解码器引理，并不覆盖全部公开缓冲区视图，
见[偏离与限制](../deviations.md)。

### 初始化、恢复与指针表示

`inflateInit2_` 在设置字段并调用 reset 前将已分配状态清零。
版本检查只读取第一个版本字节及流大小；本构建中流大小为 112。
`inflateReset2` 在取负前拒绝小于 `-15` 的负值，因此 `INT_MIN` 不会到达取负操作。
自定义分配器不在所表示的默认分配器定义域内。

`inflateStateCheck` 保留解引用前的短路检查。把 deflate 状态强转到这里会在对象模型中故障；
布局数值巧合不能证明它是有效 inflate 状态。
初始化家族必须成对使用：`inflateBackInit_` 不能与 `inflateInit2_` 互换，
其结束函数拥有的对象也不同。

`inflateGetHeader` 保存调用者指针，并无条件写 `head->done`。
所以它需要非 null 记录，以及容量符合声明且仍存活的辅助缓冲区。
文档规定的时机关系到 `extra_len - length`。
应保留 `EXTRA` 条件内部的赋值，以及 `NAME`、`COMMENT` 中的后置递增。

`syncsearch` 返回更新后的标量 `have`；`inflateSync` 在源调用边界保存它。
恢复先搜索完整缓冲字节，再搜索调用者输入，并在 reset 后恢复保存的总数和包装事实。
用于恢复及头部 CRC 的局部四字节数组有真实临时字节存储，所有返回路径都会释放。
`inflateGetDictionary` 把可选标量长度输出参数表示为返回值。
这并不建模调用者标量指针的任意别名；公开定义域审阅必须考虑这种表示选择。

## 表与尾部语句边界

`inflate_TABLE_run` 描述计数提取，以及“长度或距离符号过多”的出口。
`inflate_LENLENS_run` 使用 `have <= ncode <= 19` 与 `Good3 lens have`。
`TABLE` 建立计数界限；此前循环迭代建立已写前缀条件。
相关结果 `ll1_run`、`lz_run`、`llTail_run` 展示循环结构。

码长构造器调用使用 `inflate_table_safe` 与 `inflate_table_correct_ret`。
这些结果建立执行安全及返回分类。`u <= 128` 这样的界限和返回根宽度 `lb`，
还不能说明每个表项的含义。

`inflate_CHECK_run` 对校验表使用 `StaticsOK`，对本次调用写出的字节使用 `PutAt`。
当先前校验和不规范化时，单字节 Adler 行为需要自己的关系。
不能为掩盖这个情形而把公开定义域缩到规范化种子。
