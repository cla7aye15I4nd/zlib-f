解码路线跟踪了同一份信息的三种形态：[缓冲的源位](/sample/input-bits.html)、[已安装的解码表](/sample/decode-tables.html)，以及 [字面量或匹配输出](/sample/decode-copy.html)。证明必须在实际执行上连接这些形态。只有数组界不能确定符号，正确的抽象符号也不能为无效内存读取提供依据。

继续记住 `AD` 和重叠匹配 `ABABABAB`。这些例子解释局部连接。目标仍然量化覆盖声明的整个定义域，包括分段输入、小输出缓冲区、畸形数据和范围内的失败。它们不是为了让论证容易而新增的限制。

## 未消费输入 {#bit-prefix}

位缓冲章节区分了取入和消费。有效的不变量描述同一条未消费序列：

```text
remainingBits = low_bits(hold, bits) ++ bits(unread_input_bytes)
```

取入一个字节只改变这条序列存放的位置，不改变其值和顺序。丢弃已解码字段则恰好移除它的前缀。源码中的 [`BitInv` 和 `stream`](/reference/source/ZlibF/Proof/inflate.c.main.macros.html#L29) 把局部量连接到实际可读输入范围与归一化的 hold 值。

[`PULLBYTE_succ`](/reference/source/ZlibF/Proof/inflate.c.main.macros.html#L89) 在该不变量和明确移位界下描述一次真实翻译后的取入。[`NEEDBITS_run`](/reference/source/ZlibF/Proof/inflate.c.main.macros.html#L150) 同时包括成功与输入耗尽退出，在统计取入字节的同时保持未消费序列。这些局部命题本身不建立主解码器的所有入口条件。

解码符号依赖支撑它的前缀，不必解释已经缓冲的每个推测性位。对 AD，尽管根查表查看两位，A 只消费第一位。相同区别必须经过快速路径字节回退，并在换用新输入视图恢复执行后继续成立。

## 实际表内容 {#table-content}

构造器的输出必须正是解码器随后读取的那张表。先跟踪实际 `count`、`offs`、有序 `work`、反转编码、重复存储和子表链接，再建立这些已写单元对给定码长的含义。

声明 [`inflate_table_content`](/reference/source/ZlibF/Proof/inftrees.c.content.html#L327) 保留实际执行、返回分类和表内容。[目标定义](/reference/source/ZlibF/Spec/InflateTableContent.html#L32) 把这层连接具体化：返回堆含有该数组，内部环境是执行结果，并与输入码长、类型、位置和根宽度相联系。几何条件不能由调用者直接提供，代替运行构造器。

这仍然不同于完整的解码器接口。[`inflate_table_complete_decoder_safe`](/reference/source/ZlibF/Proof/inftrees.c.content.data.html#L295) 明确要求完整字母表。不能因为构造器能够处理空表或被接受的不完整单符号字母表，就说这个命题也覆盖它们。[`inflate_table_codes_decoder_safe`](/reference/source/ZlibF/Proof/inftrees.c.content.codes.html#L118) 在其构造器前提下处理码长表接口。必须分别阅读每个命题的定义域。

## 查表几何与符号含义 {#lookup}

[`LenTableSafe` 和 `DistTableSafe`](/reference/source/ZlibF/Proof/inffast.c.tableok.html#L63) 描述有界的根区域、有界的单级链接和合适的叶项。它们的码长与额外位界为快速解码器的补充和移位提供依据。仅有 1444 个已分配表项，并不能提供这些事实。

几何是一项要求，与独立编码一致是另一项要求。交换 C、D 的变异可以保留每个索引界，却改变解码输出。生产者到消费者的连接必须在同一堆和返回宽度下，保留精确的 `op`、`bits`、`val`，包括无效与结束标记。

<div class="zl-demo-mount"><zlib-demo kind="table-proof"><p>有界的表仍可能解出错误符号。教学场景把可读单元与有界链接，和符合预期 canonical code 的要求分开。</p></zlib-demo></div>

调用者先建立前提，再使用关于翻译后构造器的定理。不能假设未经证明的被调函数规格，也不能因为某个方便的中间定理定义域较窄，就悄悄排除合法输入。

## 输出与逻辑历史 {#history}

字面量把输出扩展一个字节。对匹配，独立的重复规则从字典加输出历史中逐字节复制。物理来源可以从环尾切到环头，再切到当前输出，正如前面六字节匹配的例子。

所以证明同时携带形状与内容。窗口索引、存活存储和已初始化范围论证访问合法；后缀关系则确定每个单元保存哪一个逻辑历史字节。字典提供历史，但不计作新输出。更换输出缓冲区必须保持逻辑值，不能假装旧的借用内存永远可用。

[`copyMatch_run`](/reference/source/ZlibF/Proof/inffast.c.match.html#L100) 在明确的上下文、距离、长度和空间前提下，记录实际快速复制的成功或距离过远行为。它是内部执行结果，不是整个公开解码器，也不证明初始化与每种历史都会建立这些前提。

## 快路与慢路组合 {#composition}

源码中的 [`inflate_fast_safe`](/reference/source/ZlibF/Proof/inffast.c.final.html#L257) 描述辅助函数的安全、终止、框架条件、归一化和写回目标。[`actual_body_refines_token`](/reference/source/ZlibF/Proof/inffast.c.body-token.html#L685) 把一次实际快速循环体联系到独立 token、块结束或被拒绝的 token。单次循环体精化与整个辅助函数安全命题，提供的是不同结论。

主解码器必须在真实的快速守卫处，建立辅助函数所需的余量、表性质和历史。慢速分派必须为小缓冲区、未完成字段和返回的匹配保持相容关系。`LOAD`、`RESTORE` 连接局部寄存器与边界状态，不表示两种表示在整个函数体中始终相等。无声模式转移也需要秩，因为并非每次分派都会消费输入或写出输出。

## 内存、终止与公开范围 {#scope}

每次访问还需要存活性、读写权限、边界以及正确对象。写入必须保持不相关内存。清理对成功、失败和 End 中的分配进行记账。C 与运行时之间的对应仍有指针、对齐和未初始化内存方面的限制，见 [安全要求](/reference/docs/spec/safety.html) 和 [信任基础](/reference/docs/trusted-base.html)。

终止性必须排除实际模型的 fuel 耗尽。有限复制次数、有界表链接、进展度量和无声转移秩，需要组合进具体预算。定理的内部前提必须来自实际初始化和允许的历史操作，包括被拒绝的调用。

这些是在解释声明与义务，不新增接受结论。[进度](/reference/docs/progress.html) 记录已接受范围和剩余工作；[`inflate`](/reference/functions/inflate.html) 描述需要建立的公开行为。接下来进入 [流状态](/sample/stream-state.html)，继续跟踪跨调用边界的同一论证。另外也可对照 [压缩块输出](/sample/blocks.html)，沿反方向看符号怎样成为比特、待发送字节和已交付输出。
