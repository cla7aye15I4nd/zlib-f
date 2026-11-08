[Adler-32](/sample/adler.html) 和 [CRC-32](/sample/crc.html) 算法已经讲清楚，现在把递推连接到实际的延迟约简、表、字读取和组合辅助函数。

三种结论必须分开：无故障执行、任意种子的精确数值行为，以及某些原始字节的校验和。最后一种额外需要真实的前缀校验和与正确长度。

## 独立递推 {#model}

独立的 [格式定义](/reference/source/ZlibF/Spec/Format/Checksum.html) 用逐字节模更新定义 Adler，用逐字节 XOR 和八个反射位步骤定义 CRC。两个定义都不调用翻译后的校验和函数或它的表。

先在 X 上折叠，再在 Y 上折叠，等于在 `X ++ Y` 上折叠。这建立模型层的增量含义，尚不能说明指针循环访问了相同列表，或展开算术计算了相同步骤。

执行在实际堆上补齐这些事实。读取 `k` 次后，指针位于 `off+k`，寄存器表示请求字节的前 `k` 项。每次迭代同时保持含义与访问权。

## 机器算术 {#arithmetic}

Adler 的数学模数是 65521。机器无符号溢出使用二的幂作为模数。它们不可互换：`2^32 mod 65521 = 225`，因此约简前一次未被发现的 32 位回绕，就可能改变期望结果。

所选 LP64 加法使用 64 位 `unsigned long`。从掩码后的 16 位种子分量开始，经过至多 5552 个步骤，一个方便使用的界为：

```text
a ≤ 65535 + 255j
s ≤ 65535 + j(65535 + 255×5552)
```

当 `j≤5552` 时，它们给出 `a≤1481295`、`s≤8224215375`，均小于 `2^64`。所以加法与自然数算术一致，再由同余关系支持延迟约简。前面 32 位的 NMAX 计算假设分量已约简；这个更宽的界也容纳数值执行论证中的掩码后任意种子。

CRC 的 `UInt32` XOR 和逻辑移位直接实现 GF(2) 寄存器。表必须等于多项式步骤，而不只是条目能放入相应类型。字递推还要跟踪加宽临时值、字节顺序和最终 32 位投影。

## 内存视图 {#memory}

两个更新保留整个堆和所有权。可读性要求 `offset+length≤array.size`，解引用在终点之前发生。空区间可以使用对象的 one-past 指针。

CRC 字对齐取决于地址，不只是数组索引。模型让分配的字节块具有对齐原点，而静态和嵌入数组具有任意且稳定的原点余数。[一般字节视图定理](/reference/source/ZlibF/Proof/crc32.c.views.html#L567) 覆盖这些已表示的视图和余数。它不证明一般的机器 ABI，也不覆盖所有有效类型别名。

在所选的八字节、五通道分支中，初始 47 字节在对齐后至少留下一个 40 字节块。这在执行前减块循环之前非常重要。行索引小于 8，字节索引小于 256，64 位字中的提取移位最多为 56 位。这些事实支持访问；多项式不变量支持表内容和合并的正确性。

[平台前提](/reference/docs/spec/platform.html) 要求每个表示的字节对象小于 `2^63` 字节，不限制流总长度。不能把它悄悄加入定义域更广的校验和命题。一般 C 对齐、转换和别名对应关系仍记在 [可信基础](/reference/docs/trusted-base.html) 中。

## 组合长度 {#composition}

Adler 组合展开两个独立开始的分量和，去掉重复的初始一，核算第一块对新前缀的贡献。错误的第二段长度会产生一个数，却没有连接后的保证。

CRC 的 `T^(8n)` 前进有等价的二进制矩阵和多项式表示。所选源码使用多项式乘法。反复平方论证把 `x2n_table`、长度位迭代和实际 `multmodp` 调用连接到独立的零位递推。

终止性具有真实的定义域条件。`multmodp` 从位 31 开始扫描低 32 位操作数，它需要其中存在一个置位。算子生成结果必须在乘法之前建立这个条件。任意一个非零 64 位整数并不足够。因此，[`crc32_combine_op` 契约](/reference/functions/crc32_combine_op.html) 使用生成的算子，包括零拒绝结果。未经证明的被调函数契约，不能代替执行定理。

## 查询与种子定义域 {#domains}

Adler 的单字节快速路径位于 NULL 检查之前。本项目显式的初始化查询定义域是 NULL 配合零长度；该限制记在 [偏离说明](/reference/docs/deviations.html) 中。CRC 先检查 NULL，对任何提供的长度都返回零。非 NULL 的空 CRC 更新保持传入的低 32 位。

Adler 还要区分正常校验和与伪造种子字。对于 `adler32_z(0xfffffff0,"\0",1)`，掩码后的分量为 65520 和 65535。第二个和是 131055；一次条件减法留下 65534，产生 `0xfffefff0`。若先完整约简起始分量，高分量则会是 13。这个调用内存安全；朴素的任意种子功能命题却是错的。

数值规格 [`adlerValue`](/reference/source/ZlibF/Spec/Public/Checksums.html#L41) 保留这个单字节行为，并在其他长度下规范化起始值。真实增量种子与普通递推一致。入口宽度、非 NULL 空区间、负组合长度和生成算子需要不同的情况划分。

## 精确结果 {#evidence}

当前源码包含 [`adler_z_public` 与 `adler_public`](/reference/source/ZlibF/Proof/public-adler-update.html#L36)：覆盖所有表示中的可读区间和全部种子，显式的零长度 NULL 查询、精确数值结果与不变的堆。[Adler 组合结果](/reference/source/ZlibF/Proof/public-adler-combine.html#L118) 给出标量参数的全执行、负长度拒绝，以及当校验和与第二段长度描述真实序列时的连接结论。

[CRC 更新结果](/reference/source/ZlibF/Proof/public-crc-updates.html#L18) 保留固定全局表前提和完整的已表示字节视图定义域。[CRC 组合结果](/reference/source/ZlibF/Proof/public-crc-combine.html#L76) 覆盖生成器、生成算子的应用和两种组合宽度，并给出精确多项式结果与不变的堆。[`get_crc_table`](/reference/functions/get_crc_table.html) 另外规定静态指针及全部 256 个条目。

这些范围没有建立完整压缩器或解压器的结论：调用者还必须对恰好已接收或已产生的字节计算校验和，并验证相应封装字段。参考文档记录了模型缺口之处，完整定义域的 C 对应关系仍 **to confirm**。[进度](/reference/docs/progress.html#group-checksums) 维护当前登记和接受证据；[组件论证](/reference/docs/proof/README.html) 提供详细推导。
