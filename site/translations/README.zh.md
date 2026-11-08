<!-- source-sha256: ec48949dc1b19ed0f393cabe3c5fd8a3c7fa920407cbe8f7ec005b5e8bd1dd31 -->
# 文档

从[图解阅读主线](overview.md)开始。网站顶部的语言菜单可在 English 和简体中文之间切换，图内说明也有中文。

需要细节时使用以下参考：

- [规范](spec/README.md)：平台范围、安全性、输入范围、公开 API 契约、内部辅助函数契约与压缩字节的含义。
- [模型](design/README.md)：翻译和内存语义、抽象关系与外部输入输出。
- [实现证明参考](proof/README.md)：共用证明方法，以及图解章节链接到的各个 C 组件的详细论证。
- [检查指南](checking/README.md)：验收规则；早期审阅记录与阅读主线、当前状态分开收纳。
- [进度](progress.md)：全部目标的依赖图、精确证明证据、阻碍与剩余工作。

[可信基础](trusted-base.md)与[偏离记录](deviations.md)说明假设及模型限制。
[源码发现](findings.md)记录报告及其范围。[运行时结构](runtime-schema.md)是字段和类型的对应参考；先在算法章节理解字段负责什么，再用它核对 C 与 Lean 的表示。
[早期论证](proof/references.md)是参考附录，不是另一份规范或状态报告。
