<!-- source-sha256: b3df448a23b326197b1a25a75af6d0261f2509bf0e9fe651dfc78d7accfe95c5 -->
# 文档

[文档网站](https://www.dataisland.org/zlib-f/index.zh.html)是正式阅读入口。这里的文件是网站内容源码。网站从 `dev` 分支构建，因此展示当前的工作。每个页面末尾写明它所构建自的提交和日期。

## 从哪里开始

- [结果与状态](progress.md#scope)：三项核心结论，以及什么在计划内、什么不在。网站的首页和状态页展示同样的事实，数据取自证明记录。
- [术语表](glossary.md)：规格与证明中用到的术语。
- [参与贡献](checking/contributing.md)：编号步骤与命令。

## 阅读 zlib 文章 {#articles}

1. [基础压缩：LZ77 与 Huffman](articles/foundations.zh.md)。
2. [zlib 的实现与优化](articles/optimizations.zh.md)。
3. [zlib 的功能扩展：流式处理与校验](articles/features.zh.md)。

每篇都有完整的中英文版本。算法系列讲解 zlib 本身；形式化验证使用下面独立的参考资料。

## 参考资料 {#reference}

- [规范](spec/README.md)：平台范围、安全性、输入范围、公开 API 契约、内部辅助函数契约与压缩字节的含义。
- [模型](design/README.md)：翻译、内存语义和外部输入输出。
- [实现论证](proof/README.md)：验证方法，以及各个 C 组件的详细论证。
- [检查指南](checking/README.md)：什么算已检查，什么算已验收。
- [证据索引](progress.md)：每个目标的命题、证明与依赖。

[可信基础](trusted-base.md)与[偏离记录](deviations.md)说明模型边界。
[源码发现](findings.md)记录已确认的报告及其范围。
[Sanitizer 报告](sanitizer-reports.md)列出每个 sanitizer 复现以及排除它的前提。
[运行时结构](runtime-schema.md)提供字段与类型参考。

## 构建与本地预览 {#local}

文章源码放在 `articles/`。网站构建、交互、样式和测试放在 `web/`。API 返回值表与完整契约一起写在 `spec/api/` 中。英文及相邻的 `.zh.md` 中文各自只维护一份，网页和函数视图由它们生成。
依赖和构建命令见网站指南 `web/README.md`。
