# 内存、翻译与外部 I/O 语义

本项目证明关于 C 的可执行 Lean 翻译的命题。本节解释翻译表示什么、规范怎样描述它，以及与 C 的哪些联系仍依赖审阅。这里不记录进度；相关记录统一在[进度](../progress.md)中。

先读[架构](architecture.md)，再按问题查阅：

| 问题 | 文档 |
| --- | --- |
| C、运行时、规范与证明怎样组合？ | [架构](architecture.md) |
| 一个 C 语句必须怎样翻译？ | [翻译规则](translation.md) |
| 不涉及堆的 API 关系描述什么？ | [API 模型与具体实现边界](api-model.md) |
| 内部辅助函数的前置条件在哪里定义？ | [内部调用规范](../spec/internal-contracts.md) |
| 外部世界表示哪些文件、格式化和错误行为？ | [外部 I/O](external-io.md) |
| 有哪些记录和指针种类？ | [生成的运行时结构参考](../runtime-schema.md) |

[API 手册](../spec/api/README.md)描述公开调用，[证明指南](../proof/README.md)解释怎样建立它们的性质，[检查指南](../checking/README.md)解释结果怎样验收。判断任何定理的适用范围时，请同时阅读[安全性](../spec/safety.md)、[可信基础](../trusted-base.md)和[表示限制](../deviations.md)。

[文档首页](../README.md)
