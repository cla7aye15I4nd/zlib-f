[流式处理](/sample/stream-state.html)通过更换缓冲区继续同一项任务。Reset 准备另一项任务，Copy 则分出当前任务的一个分支。字典、注入比特和借用头部又会改变后续执行的含义。先看每种操作留下哪些数据，再判断下一份输出能否成为独立的流。

继续沿用示例：解码器 A 已从 `ABABABAB` 交付 `ABAB`，匹配还有四字节待产生。Reset 为消息 B 放弃这些工作；Copy 为两条后续路径保留检查点；约定字典则为新任务提供历史，而非恢复旧任务。这些是保留字节的不同用法。

以下机制依据选定的 C 和聚焦契约解读，仍需通过对应执行证明 **to confirm**。聚焦工作流不缩小更广的公开目标。调用者仍须提供有效存储、可读/可写范围并顺序使用流；C 指针类型本身不建立生命周期。

## 重置与保留历史 {#reset}

假设解码器 A 已交付 `ABAB`。应用保留这些字节。要解码独立消息 B，先调用 [inflateReset](/reference/functions/inflateReset.html)，再提供 B 的缓冲区。Reset 忘记 A 的进度，并使旧历史不能再用于匹配。它不擦除已交付的应用字节，也不移动外部文件位置。原有 I/O 指针和可用计数保持不变，因此重新绑定缓冲区仍是调用者的工作。

三种解码器重置的区别如下：

| 入口 | 进度与历史 | 配置与分配 |
| --- | --- | --- |
| [inflateResetKeep](/reference/functions/inflateResetKeep.html) | 清空总计数、持有比特、已设字典状态和头部登记；保留窗口历史。 | 保留当前封装/窗口设置和分配。不恢复 recovery 改过的封装设置。 |
| [inflateReset](/reference/functions/inflateReset.html) | 重置进度并清空逻辑历史。 | 恢复请求的封装/窗口；保留兼容窗口或释放过时窗口。保持验证设置。 |
| [inflateReset2](/reference/functions/inflateReset2.html) | 放弃进度、历史和头部登记。 | 选择新的可接受封装/窗口请求并启用其验证；释放不兼容窗口。无效值返回 `Z_STREAM_ERROR`，状态不变。 |

三者对可接受的活流重置返回 `Z_OK`。流检查失败返回 `Z_STREAM_ERROR` 且状态不变；悬空的任意指针不在这种干净拒绝的覆盖内。

`inflateReset2` 的聚焦参数域包含每个有符号窗口参数。-15、15、31 和 47 等请求分别选择 raw、zlib、gzip 和自动检测；[inflateInit2_ 契约](/reference/functions/inflateInit2_.html)列出全部可接受值，包括特殊的零窗口请求。Reset 本身从不分配替代窗口。

[deflateReset](/reference/functions/deflateReset.html)保留压缩器的五项分配以及当前级别、策略、封装和内存设置。它放弃 pending 输出、未完成 lookahead、比特进度和匹配历史，并恢复当前级别的默认搜索调优。[deflateResetKeep](/reference/functions/deflateResetKeep.html)与解码器对应入口一样没有公开文档；它保留窗口/哈希历史和调优。两者都重新开始封装输出并忘记自定义 gzip 头部。它们都不证明放弃的工作已经交付。ResetKeep 后的匹配可以引用重置前的历史，因此不保证从空历史解码。

## 字典上下文 {#dictionary}

预置历史为 `AB` 时，载荷可以先执行长度 6、距离 2 的匹配，产生 `ABABAB`。字典提供历史，不属于输出。这是一种可能的格式描述，不是压缩器必定采用的选择。

普通 zlib 交互依次是 [deflateSetDictionary](/reference/functions/deflateSetDictionary.html)、带字典标识的压缩字节、`Z_NEED_DICT`，以及 [inflateSetDictionary](/reference/functions/inflateSetDictionary.html)。标识是整个字典的 Adler-32；保留历史则限于窗口大小的后缀。标识相等不能建立字节相等：正确性仍需恰当的字典上下文。

聚焦压缩工作流在初始化或普通 reset 后、压缩前，安装非 NULL 的可读字典。公开操作还包含 zlib 开始前的重复调用，它们累计 Adler-32，以及合法的 raw 替换。C 对 gzip、非零 lookahead、不合适的 zlib 状态，或尚未处于已完成块边界的 raw 位置返回 `Z_STREAM_ERROR`。它不分配，并恢复临时输入绑定；装入字典可能增加 `total_in`，但不把字典字节交付为消息输出。

解码器的 zlib 安装要求处于等待字典状态。标识不匹配返回 `Z_DATA_ERROR` 且状态不变，可以再试另一份字典。Raw 在调用边界允许安装，不检查标识；gzip 没有预置字典路径。解码器复制字节，不推进 I/O 指针或总计数，且可能分配窗口。分配失败返回 `Z_MEM_ERROR`，进入仍可 End 的内存错误状态。即使长度为零，NULL 字典也会被拒绝；非 NULL 的零长度 raw 字典则被接受。

## 注入比特 {#prime}

[inflatePrime](/reference/functions/inflatePrime.html)把提供的比特放在下一个输入字节之前。零位不改变状态；负计数清空持有比特。计数为 1–16 且总数不超过 32 位时，把值的低位追加到现有比特之上。计数或空间超限返回 `Z_STREAM_ERROR`，状态不变。

[deflatePrime](/reference/functions/deflatePrime.html)将值的 0–16 个低位追加到 pending 输出，不向 `next_out` 交付字节。空间不足返回 `Z_BUF_ERROR` 且不插入比特，但此前可能先在内部压紧已有 pending 字节。超出范围的计数在压紧前被拒绝。普通用法是在初始化/reset 后第一次压缩调用前，为 raw 输出添加比特前缀。

两项入口在流检查失败时都返回 `Z_STREAM_ERROR`，不插入比特。C 并不强制检查这些聚焦工作流的全部 raw 模式或时机前提。落在前提之外不自动等于 UB 或文档规定的干净拒绝。任意插入的片段未必构成普通有效流；操作精确的比特效果与其格式解释仍是不同义务。

## 借用头部 {#headers}

[inflateGetHeader](/reference/functions/inflateGetHeader.html)登记调用者拥有的 gzip 元数据存储，并将 `done` 设为零。记录及可选的 extra/name/comment 目标在解析结束或登记清除前保持有效且可写。容量限制写入；只有空间足够时才写入名称结束符。Gzip 捕获完成时 `done` 为 1，自动检测识别到 zlib 时为 -1。

没有所有权转移。Reset 清除登记，但不释放记录。流检查失败或封装不支持 gzip 时返回 `Z_STREAM_ERROR`；在本可接受的请求中提供 NULL 头部会被 C 解引用，不是干净错误情况。[deflateSetHeader](/reference/functions/deflateSetHeader.html)借用相应的发射元数据直到头部输出完成。较晚登记不能重写已经发射的字节。精确的存储分离限制属于链接中的契约。

## 复制与指针重定位 {#copy}

在 A 的 `ABAB` 检查点，成功复制后两份解码器都能继续产生剩余 `ABAB`。已经交付的前缀仍由应用负责；Copy 不会再次交付它。检查点必须保留持有比特、表、历史和未完成操作，同时能恢复未读输入。单个字节偏移并不足够。在聚焦工作流中，[inflateCopy](/reference/functions/inflateCopy.html)和 [deflateCopy](/reference/functions/deflateCopy.html)要求不同、可写且不拥有活状态的目标；自复制或覆盖活目标不获得这里的无泄漏契约。

成功的解码器副本拥有新状态，以及原来存在时的一份独立窗口。指向源内嵌 `codes` 的动态表指针必须以相同偏移移到副本；静态固定表可以继续共享。构造游标也需重定位。压缩器副本复制五项分配，保留已初始化窗口/哈希/pending/符号内容，并重定位 pending 游标和内嵌树描述符。区分静态和拥有的指针需要有效的来源论证，不只是两个可读的指针值。

两种复制都保持源不变，并要求分别 End。调用者 I/O 指针和保留头部指针也会复制：继续两者之前安排适当输出目标，并维持共享借用元数据的生命周期。分配失败释放本次尝试的新块、清空目标状态，不消耗源检查点。[分配章节](/sample/allocation.html)跟踪这份账本；[所有权证明](/sample/ownership-proof.html)解释精确保持与可达历史主张怎样连接。
