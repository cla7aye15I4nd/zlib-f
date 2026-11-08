<!-- source-sha256: 5ba7bda65770b84ca6fb8d96d361b468a28b88bd1e1ae50ee008598f0ee9ba6e -->

# 已审阅的递归执行辅助声明

一个递归定义需要说明每次调用为什么离结束更近。例如，自然数从 n 递减到 n−1，列表改为它的尾部。审计列出了六个为全函数逻辑定义生成的执行辅助声明。每个条目是在下列名称后加上 `._unsafe_rec`。

| 逻辑定义 | 递减参数 |
| --- | --- |
| `Zlib.Trees.Math.nextCode` | 自然数的前驱。 |
| `Zlib.Trees.Math.reverseLowBits` | 自然数的前驱。 |
| `Zlib.Trees.Math.scanCount` | 自然数的前驱。 |
| `Zlib.Trees.Math.scanMax` | 自然数的前驱。 |
| `Zlib.Trees.Proofs.Math.blMaxIdx` | 自然数的前驱。 |
| `Zlib.Trees.Proofs.tallyCalls` | 列表的尾部。 |

这些逻辑定义使用自然数递归 `Nat.rec` 或列表递归 `List.rec`，具有经过检查的递归方程。实际生成的类型和分支主体经过独立检查。主体比较只将辅助声明对自身的引用替换为对应的全函数逻辑定义。递归参数也经过直接检查。检查过的环境中，没有安全声明引用这些辅助声明。它们不在已登记定理的逻辑依赖闭包中。

只有这些精确声明被加入现有执行辅助声明列表。其完整导出语法被锁定。这不允许项目源码使用部分定义，也不证明编译器或机器代码正确。当前验收状态仍在[进度](../progress.md)中。
