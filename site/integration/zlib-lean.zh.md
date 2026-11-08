---
date: 2026-11-07
tags: [compression, verification, lean]
title: "zlib × Lean"
description: "沿着数据读算法，沿着实现读证明。"
---

# zlib × Lean

我把 zlib 的算法、接口和验证整理成了一份独立的交互文档。可以从两条路线进入：

- <a href="/zlib-f/algorithms/index.zh.html" data-no-spa>算法与接口</a>：从重复字节开始，经过匹配、编码和压缩块，再看解压与流式调用。完整 API 契约可随时查阅。
- <a href="/zlib-f/verification/index.zh.html" data-no-spa>算法精读与形式化验证</a>：进入具体实现，先展开数据结构、执行过程和优化，再解释证明如何连接这些步骤。

目前的精读从压缩输出开始：同一组符号怎样选择块、写出比特、复用符号存储，最后怎样组织正确性与内存安全的论证。每一章都连接前置背景、下一章和对应的完整参考。

<a href="/zlib-f/index.zh.html" data-no-spa>打开阅读地图 →</a>

正文、交互和参考文档均由 zlib-f 子站承载。博客提供入口。
