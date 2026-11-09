---
date: 2026-11-07
tags: [compression, verification, lean]
title: "zlib × Lean"
description: "沿着数据读算法，沿着实现读证明。"
---

# zlib × Lean

这份交互文档沿实际执行顺序讲解 zlib：从一次完整的压缩与还原开始，展开 deflate 的匹配、编码和输出，再展开 inflate 的读位、查表、复制与暂停，最后连接调用协议和资源生命周期。

六章正文各自包含代码、优化和对应的证明图。左侧目录统一定位章节与小节，完整 API 和证明进度放在参考区。全文提供中英文版本。

<a href="/zlib-f/index.zh.html" data-no-spa>阅读正文 →</a>
