<!-- source-sha256: f1f4c742dae02d3047f7a1fbc10c2fac3fdf9574f711abd3f31a550fab5597ca -->
# zlib-f

用 Lean 4 形式化验证 zlib。对 C 源码作忠实翻译，再证明内存安全、终止性、资源所有权和功能正确性。

**项目尚未完成。** 三项结论按顺序被验收时项目完成：`inflate` 对每个输入都安全；`inflate` 产生的字节正是格式所定义的字节；`deflate` 是安全的，且其输出解码后得到原输入。`compress` 与 `uncompress` 作为组合随后完成。目标是默认的 x86_64 Linux 构建。gzip 文件接口、回调解码器和其他构建配置都不在计划内。[状态页](https://www.dataisland.org/zlib-f/status.zh.html)根据证明记录，把每项结论显示为未完成、已检查或已登记。

## 文档

**[阅读文档网站](https://www.dataisland.org/zlib-f/)** · [网站内容源码](docs/README.md)

| 阅读入口 | 内容 |
| --- | --- |
| [证明总览](https://www.dataisland.org/zlib-f/reference/docs/overview.html) | 目标、假设和证明框架。 |
| [结果与状态](https://www.dataisland.org/zlib-f/status.zh.html) | 已确立什么，什么在计划内，什么不在。 |
| [全部目标的依赖图](https://www.dataisland.org/zlib-f/reference/docs/progress.html#proof-progress-graph) | 目标之间的依赖及各自覆盖的输入范围。 |
| [证据索引](https://www.dataisland.org/zlib-f/reference/docs/progress.html) | 每个目标的精确命题、证明和依赖。 |
| [规格](https://www.dataisland.org/zlib-f/reference/docs/spec/README.html) | 需要证明的安全、输入、API、内部函数和格式要求。 |
| [API](https://www.dataisland.org/zlib-f/reference/api.html) | 每个函数的前提和保证。 |
| [数据格式](https://www.dataisland.org/zlib-f/reference/docs/spec/format/README.html) | DEFLATE、zlib 和 gzip 字节的含义。 |
| [设计](https://www.dataisland.org/zlib-f/reference/docs/design/README.html) | 翻译方式与内存模型。 |
| [证明](https://www.dataisland.org/zlib-f/reference/docs/proof/README.html) | 各部分论证的组合方式。 |
| [检查](https://www.dataisland.org/zlib-f/reference/docs/checking/README.html) | 什么算已检查，什么算已验收。 |
| [参与贡献](https://www.dataisland.org/zlib-f/reference/docs/checking/contributing.html) | 运行哪些命令，按什么顺序？ |
| [术语表](https://www.dataisland.org/zlib-f/reference/docs/glossary.html) | 这些术语是什么意思？ |

## 仓库结构

- `zlib/`：固定版本的上游源码；不直接修改，修复补丁放在 `patches/`。
- `ZlibF/Zlib/`：逐条语句翻译的 C 实现。
- `ZlibF/Spec/`：格式模型和具体的验证目标。
- `ZlibF/Proof/` 和 `ZlibF/Math/`：实现证明和不涉及堆的数学推导。
- `ZlibF/Runtime/`：内存、指针、算术和执行语义。
- `tests/`：差分测试、变异测试和证明审计。

## 本地检查

```bash
lake build ZlibF
scripts/check-sorry.sh
```

各项检查的范围和最终验收条件见[检查指南](https://www.dataisland.org/zlib-f/reference/docs/checking/README.html)。差分测试用来检查翻译与 C 的一致性。全称正确性由证明建立。
[源码问题记录](docs/findings.md)列出问题的证据强度和适用范围。

## 源码问题：deflateResetKeep 之后的 deflateCopy

直接调用 `deflateResetKeep` 并调用一次 `deflate(Z_BLOCK)` 之后，有两个链头等待插入；`deflateCopy` 不复制它们的 `prev` 槽，副本上的一次 `Z_RLE` 或 `Z_HUFFMAN_ONLY` 刷新以 `insert = 0` 结束，所以它们不会被重新插入。之后一次默认策略的 `deflate` 会沿一个未初始化的 `prev` 槽前进，`longest_match` 读到窗口之外。[保留的复现](docs/findings/deflate-copy-pending-prev/README.md)在 x86_64 Linux 上诊断固定的、未修改的 C：AddressSanitizer 报告窗口之外的读取，valgrind 报告使用了未初始化的槽。对诊断出的序列，置信度高。它在 zlib 1.4 和固定的 `develop` 上复现，不在 1.3.1 或 1.3.2 上复现（部分复制随 1.3.2 引入，丢弃前瞻随 1.4 引入）。范围：它需要 `deflateResetKeep`，zlib.h 把该函数声明为未文档化、不属于 zlib API，所以这不是已文档化 API 的缺陷；已证明的 deflate 流定义域排除了它（[偏差](docs/deviations.md)）。已写好一份[报告草稿](docs/findings/deflate-copy-pending-prev-report.md)，没有向上游发送任何内容。

## 源码修复

使用默认参数初始化的流如果在固定块中途暂停，`inflateCopy` 会比较静态固定码表与单独分配的状态码数组。保留的[复现材料](docs/findings/inflate-copy-fixed/README.md)诊断了固定版本中未经修改的 C。现在验证的源码通过[临时补丁](patches/README.md)采用了[上游 PR #1369](https://github.com/madler/zlib/pull/1369) 中完全相同的修复；Lean 翻译也使用相同的相等性检查。对于已诊断的 LP64 问题，证据置信度高；公开 `inflateCopy` 的完整证明仍未完成，且在计划内：`inflateCopy` 是 `inflate_sequence` 所涉及的流调用。
