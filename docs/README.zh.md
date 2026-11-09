<!-- source-sha256: 8e3398c1cd43b9a92c999e416634e2366aa09d86138f05b160a2f8acb8b59286 -->
# 文档

[文档网站](https://www.dataisland.org/zlib-f/index.zh.html)是正式阅读入口。这里的文件是网站内容源码。

## 阅读 zlib 文章 {#articles}

1. [基础压缩：LZ77 与 Huffman](articles/foundations.zh.md)。
2. [zlib 的实现与优化](articles/optimizations.zh.md)。
3. [zlib 的功能扩展：流式处理与校验](articles/features.zh.md)。

每篇都有完整的中英文版本。算法系列讲解 zlib 本身；形式化验证使用下面独立的参考资料。

## 参考资料 {#reference}

- [规范](spec/README.md)：平台范围、安全性、输入范围、公开 API 契约、内部辅助函数契约与压缩字节的含义。
- [模型](design/README.md)：翻译、内存语义和外部输入输出。
- [实现论证](proof/README.md)：验证方法，以及各个 C 组件的详细论证。
- [检查指南](checking/README.md)：验收规则和已经审阅的检查。
- [进度](progress.md)：目标依赖关系、证明证据和剩余工作。

[可信基础](trusted-base.md)与[偏离记录](deviations.md)说明模型边界。
[源码发现](findings.md)记录报告及其范围。
[运行时结构](runtime-schema.md)提供字段与类型参考。

## 构建与本地预览 {#local}

文章源码放在 `articles/`。网站构建、交互、样式和测试放在 `web/`。API 契约写在 `spec/api/` 中。英文及相邻的 `.zh.md` 中文各自只维护一份，网页和函数视图由它们生成。
依赖和构建命令见网站指南 `web/README.md`。
