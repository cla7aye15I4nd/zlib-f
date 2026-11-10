---
date: 2026-11-07
tags: [compression, verification, lean]
title: "zlib × Lean"
description: "一篇交互文章：先理解 zlib 怎样工作，再理解怎样验证它。"
---

# zlib × Lean

回引用为什么能读取刚刚产生的字节？为什么一个压缩块最终放得下，
输出过程中却仍然可能覆盖未读符号？

我把这些问题整理成了一篇独立的交互文章。第一部分从小例子出发，
解释 zlib 的压缩与解压。第二部分沿用相同的例子，解释规格、不变量，
以及怎样把论证连接到实际执行。
同一个子站还收录完整公开 API 契约、引擎证明指南和相应的 Lean 证明正文。

<a href="/zlib-f/index.zh.html" data-no-spa>阅读 zlib × Lean →</a>

正文和交互都由 zlib-f 项目的独立子站承载。这篇博客只提供入口。
完整 zlib 验证仍在进行中。
