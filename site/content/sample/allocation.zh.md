[状态操作章节](/sample/state-operations.html)区分了忘记进度与释放内存。现在沿着这些操作背后的对象继续看。成功初始化获得后续调用持续使用的存储；失败尝试则必须解释失败前获得的每项资源。

这些源码机制仍需由对应执行证明 **to confirm**。首个构建使用默认分配器，分配失败属于范围内。自定义回调、其他布局和接受的平台限制，在[配置参考](/reference/docs/spec/input-configurations.html)与[安全要求](/reference/docs/spec/safety.html)中各有明确范围。

## 压缩器存储 {#compressor}

成功的 [deflateInit2_](/reference/functions/deflateInit2_.html)拥有五项分配：状态记录、窗口、前驱数组 `prev`、哈希头数组 `head` 和 pending 存储。树数组、堆/深度数组及其描述符属于状态记录。调用者的 `z_stream`、I/O 和可选 gzip 元数据仍是借用对象，不是 End 要额外释放的分配。

令 `W = 1 << w_bits`，`B = 1 << (memLevel + 6)`。选定的打包符号布局如下：

| 分配 | 范围 | 默认尺寸 |
| --- | --- | --- |
| 状态 | 一个 `deflate_state` 记录 | 包含控制字段和内嵌树 |
| 窗口 | `2W` 字节 | 窗口位数 15 时为 65536 字节 |
| `prev` | `W` 个位置，每个两字节 | 65536 字节 |
| `head` | `1 << (memLevel + 7)` 个位置 | 内存级别 8 时为 32768 个位置、65536 字节 |
| Pending | `4B` 字节 | `B = 16384` 时为 65536 字节 |

符号从 `pending_buf + B` 开始，并非第六项分配。每个记录占三字节。[共享存储章节](/sample/storage.html)解释何时消费记录会为输出释放空间。`memLevel` 改变哈希和符号容量；压缩级别则改变策略/搜索设置。Zlib 窗口请求 8 会归一化为 9。实际参数接受、归一化和拒绝由完整[初始化契约](/reference/functions/deflateInit2_.html)规定。

分配获得容量，不使所有内容自动有意义。状态记录会显式清零。`lm_init` 清空哈希头并建立计数器，但不初始化每个前驱槽。`high_water` 跟踪已经建立的窗口字节。后续搜索仍需已写位置论证，不能把已分配数组当成全部初始化。

## 一次完整的失败尝试 {#failure}

版本/结构检查兼容后，压缩器初始化先验证参数，再分配。状态分配成功后，它先尝试全部四个缓冲区，**然后才检查合并结果**。较早的缓冲区失败不会停止后面的请求。

考虑这组具体分配 oracle 结果：

| 尝试 | 对象 | 结果 |
| --- | --- | --- |
| 1 | 状态 | 成功 |
| 2 | 窗口 | 成功 |
| 3 | `prev` | 失败 |
| 4 | `head` | 成功 |
| 5 | Pending | 成功 |

失败分支必须释放 pending、head、窗口和状态，跳过 NULL 前驱指针。不能只清理第 3 次尝试之前的分配。源码设置适合清理的状态、记录内存错误消息，调用 [deflateEnd](/reference/functions/deflateEnd.html)，然后返回 `Z_MEM_ERROR`；没有新拥有的活块，流状态指针为 NULL。

如果第 1 次尝试就失败，不会再尝试缓冲区，原 `state` 字段保留。准备默认回调和清除 `msg` 此前可能已经改变流。即使完全清理，也不会恢复分配尝试计数或新对象身份计数。“没有新活分配”与“整个堆不变”是不同结论。

下面更小的双资源模型单独展示生命周期模式。它不是上面精确的五次请求顺序；选择第二次失败，再与成功初始化后 End 比较。

<div class="zl-demo-mount"><zlib-demo kind="ownership"><p>教学初始化器先获得状态，再获得窗口。第二次分配失败时释放状态；成功初始化后保留两者直到 End。真实压缩器先尝试四个缓冲区，再合并检查。</p></zlib-demo></div>

这份账本模式也适用于 [deflateCopy](/reference/functions/deflateCopy.html)，但复制有自己的路径。失败时必须释放目标新获得的每项分配，并保持源不变。不能因为目标尝试失败，就清理源。

## 解码器存储与延迟历史 {#decoder}

[inflateInit2_](/reference/functions/inflateInit2_.html)起初只分配一个 `inflate_state`。码长、工作和解码数组内嵌于该记录。窗口指针从 NULL 开始。静态固定解码表是共享只读对象，不是每个流独立拥有的分配。

解码器把历史窗口分配延迟到需要保留或安装历史的操作。[inflateSetDictionary](/reference/functions/inflateSetDictionary.html)可能需要它；普通解码为后续执行提交近期输出时也可能分配。单次 `Z_FINISH` 完成可能完全不需要窗口。避免不必要分配和历史复制，就是这种延迟设计的实际收益。

它也把失败移到了意外的位置。窗口分配失败前，`inflate` 可能已经消费输入、写入调用者输出。I/O 指针和可用计数可能反映这些效果，而正常的最终总计数/校验更新被跳过。因此，`Z_MEM_ERROR` 不表示输出不变。活解码器仍然可以 End；参见完整 [inflate 契约](/reference/functions/inflate.html)。

解码器初始化的错误顺序不同于压缩器。它先尝试状态分配，再验证窗口参数。因此，如果分配先失败，无效窗口请求也可能得到 `Z_MEM_ERROR`。如果分配成功而请求无效，则释放新状态、将 `state` 置 NULL，再返回 `Z_STREAM_ERROR`。版本/结构拒绝更早发生。这些区别对调用者和精确失败证明都重要。

## 复用与释放 {#release}

[inflateReset](/reference/functions/inflateReset.html)可以保留兼容的物理窗口，同时清空其逻辑历史。不兼容窗口会被释放；reset 自身不分配替代品。[deflateReset](/reference/functions/deflateReset.html)为下一项压缩任务保留五项分配。复用省去重复分配工作，但不代表旧字典内容仍可作为有效历史。

[inflateEnd](/reference/functions/inflateEnd.html)释放可选窗口和状态，清空状态指针；对有效活解码器，即使解码被放弃也返回 `Z_OK`。[deflateEnd](/reference/functions/deflateEnd.html)释放全部五项分配；繁忙且未完成压缩的 `Z_DATA_ERROR` 在释放之后报告，而非代替释放。第二次 End 会因流检查失败而拒绝，不会再次释放。

[inflateBackInit_](/reference/functions/inflateBackInit_.html)提供了有用的所有权对照：其历史窗口由调用者提供。[inflateBackEnd](/reference/functions/inflateBackEnd.html)释放回调解码器的状态，不释放调用者窗口。[所有权证明章节](/sample/ownership-proof.html)把这些实际对象转换为建立、框架条件和精确活块义务。
