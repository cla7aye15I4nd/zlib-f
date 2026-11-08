---
date: 2026-11-07
tags: [compression, verification, lean]
title: "zlib × Lean"
description: "沿着数据读算法，沿着实现读证明。"
---

# zlib × Lean

我把 zlib 的算法、接口和验证整理成了一份独立的交互文档。

<a href="/zlib-f/algorithms/index.zh.html" data-no-spa>从八个字节开始 →</a>

正文沿匹配、编码、压缩块与解码走完一次往返。讲到窗口、查表或分批调用时，就从那里展开实现章节：先说明任务，再拆开算法、数据结构和优化，接着解释证明需要保持的关系。校验、资源生命周期和不同接口也沿着同一任务接入。

需要查找某个机制时，可以打开<a href="/zlib-f/verification/index.zh.html" data-no-spa>章节目录</a>；各章都有完整 API 契约与源码入口。

<a href="/zlib-f/index.zh.html" data-no-spa>打开阅读地图 →</a>

正文、交互和参考文档均由 zlib-f 子站承载。博客提供入口。
