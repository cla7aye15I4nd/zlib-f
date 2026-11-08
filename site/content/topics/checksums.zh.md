## 从恢复字节到校验数据 {#connection}

[解码章节](/sample/decode-copy.html)解决了怎样从压缩主体恢复字节。[封装章节](/sample/wrappers.html#completion)还留着一个步骤：**恢复出字节后，接收者怎样检查它们是否与发送端的数据一致？** 校验和就在这里接入同一条处理流程。

沿用前文的八字节 `ABABABAB`。发送端一边压缩，一边对这八个**原文字节**计算校验值，写进封装尾部；接收端从主体恢复字节后，重新计算，再与尾部比较。若压缩数据在传输中损坏，而解码器仍能解出另一串字节，数值不一致就会报告数据错误。校验通过可以排除许多损坏情形，但不是数据真实性保证。

<figure class="bk-checksum-flow" aria-label="压缩与解压两端的校验流程">
<div><span>发送端</span><p><b>原文字节</b><code>ABABABAB</code></p><i aria-hidden="true">→</i><p><b>压缩主体</b><small>由 deflate 生成</small></p><i aria-hidden="true">＋</i><p><b>尾部校验值</b><code>Adler-32: 093c020d</code><small>同一份原文的摘要</small></p></div>
<div><span>接收端</span><p><b>压缩主体</b><small>由 inflate 解码</small></p><i aria-hidden="true">→</i><p><b>恢复的字节</b><code>ABABABAB</code></p><i aria-hidden="true">→</i><p><b>重新计算并比较</b><code>093c020d = 093c020d</code><small>与收到的尾部字段比较</small></p></div>
<figcaption>图中选用 zlib 封装。gzip 在同一位置使用 CRC-32；裸 DEFLATE 没有这个校验尾部。校验的对象始终是原文，不是压缩主体。</figcaption>
</figure>

因此，“解码器恢复了什么字节”和“校验值属于哪些字节”必须接在一起。算术函数本身不会知道某段缓冲区是否已被解压器计入；外层调用要把刚处理的那一段交给它。[封装中的字节范围](/sample/wrappers.html#checksums)解释这一步，后面的证明章再把它接到实际内存读取。

## 两种校验算法对应两种封装 {#formats}

Adler-32 和 CRC-32 不是压缩流程里先后执行的两步。它们在不同封装中承担同一项任务，可以先读自己需要的那一条。

| 所用格式 | 校验的内容 | 本组章节 |
| --- | --- | --- |
| zlib | 未压缩数据的 Adler-32 | [两个累加器怎样得到校验值](/sample/adler.html) |
| gzip | 未压缩数据的 CRC-32；尾部另存长度 | [移位与异或怎样得到校验值](/sample/crc.html) |
| 裸 DEFLATE | 格式本身不带校验字段 | 回看[主体与封装的区别](/sample/wrappers.html#layout) |

## 分批更新与分块组合 {#combination}

[流式调用](/sample/stream-state.html#history)用五字节输出空间取回八字节：第一次拿到 `ABABA`，第二次拿到 `BAB`。缓冲区换了，原文仍是同一个 `ABABABAB`。校验值也必须跨两次调用继续累积，不能每换一次缓冲区就重新开始。

“组合”处理的是另一种情况：两个工作单元分别算完两段数据，只留下各自的校验值，想得到两段按顺序连接后的校验值。这里合并的是**摘要值**，既不是拼接压缩流，也不是组合两份证明。

| 数据怎样到达 | 手里有什么 | 应做的操作 |
| --- | --- | --- |
| 先拿到 `ABABA`，随后拿到 `BAB` | 第一段的运行中校验值，以及第二段原文字节 | **继续更新**：把第一段结果传给下一次更新 |
| 两段已经独立计算完毕 | 两个校验值，以及第二段的字节长度 3 | **分块组合**：调用对应的 `combine` 接口，无需重读原文 |

两种路径都应得到 `ABABABAB` 的同一个校验值。对 Adler-32，第一段为 `03da0148`，第二段独立计算为 `018d00c6`，连接后为 `093c020d`。下一章会先从逐字节计算得到这些数，再解释为什么第二段长度足以把两个摘要合并。

## 本组的阅读顺序 {#reading-path}

1. **[Adler-32](/sample/adler.html)**：从加法理解摘要、逐批更新和独立分块合并，再看延迟取余怎样减少开销。
2. **[CRC-32](/sample/crc.html)**：同样的任务换成移位与异或，随后展开查表、按字读取和组合算子。它是另一条算法分支，可以直接进入。
3. **[校验和的证明思路](/sample/checksum-proof.html)**：把“得到正确的数”接到“恰好读取对应字节”，并解释优化路径、内存边界和组合长度各自需要什么事实。

只想理解校验在整个 zlib 中的位置，读到这里后可以回到[封装完成与尾部比较](/sample/wrappers.html#completion)。想使用完整接口，可进入[校验和 API](/reference/docs/spec/api/checksums.html)；通过 gzip 文件接口读取数据时，[文件读取路径](/sample/gzip.html#reading)还会把校验错误交给应用处理。
