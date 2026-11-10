<!-- source-sha256: 40c64cdcd006c5978d1a5b50645a7619152938dd7dea67bdaf066578f64837ad -->
# zlib-f

用 Lean 4 形式化验证 zlib。对 C 源码作忠实翻译，再证明内存安全、终止性、资源所有权和功能正确性。

**项目尚未完成全库验证。** 首个目标是默认 LP64 Linux 静态构建，使用默认分配器。

## 文档

**[阅读文档网站](https://www.dataisland.org/zlib-f/)** · [网站内容源码](docs/README.md)

| 阅读入口 | 内容 |
| --- | --- |
| [证明总览](https://www.dataisland.org/zlib-f/reference/docs/overview.html) | 目标、假设和证明框架。 |
| [当前进度](https://www.dataisland.org/zlib-f/reference/docs/progress.html) | 已完成的结果和剩余工作。 |
| [全部目标的依赖图](https://www.dataisland.org/zlib-f/reference/docs/progress.html#proof-progress-graph) | 目标之间的依赖及各自覆盖的输入范围。 |
| [证明证据](https://www.dataisland.org/zlib-f/reference/docs/progress.html) | 精确命题、证明正文和各类关系表。 |
| [规格](https://www.dataisland.org/zlib-f/reference/docs/spec/README.html) | 需要证明的安全、输入、API、内部函数和格式要求。 |
| [API](https://www.dataisland.org/zlib-f/reference/api.html) | 每个函数的前提和保证。 |
| [数据格式](https://www.dataisland.org/zlib-f/reference/docs/spec/format/README.html) | DEFLATE、zlib 和 gzip 字节的含义。 |
| [设计](https://www.dataisland.org/zlib-f/reference/docs/design/README.html) | 翻译方式与内存模型。 |
| [证明](https://www.dataisland.org/zlib-f/reference/docs/proof/README.html) | 各部分论证的组合方式。 |
| [检查](https://www.dataisland.org/zlib-f/reference/docs/checking/README.html) | 证明的验收条件。 |
| [贡献指南](docs/checking/contributing.zh.md) | 如何一步步证明、登记并检查一个目标？ |
| [术语表](docs/glossary.zh.md) | `Good`、`DGood`、数据时段、限定范围准入和 `C1`–`C7` 是什么意思？ |

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

## 源码修复

使用默认参数初始化的流如果在固定块中途暂停，`inflateCopy` 会比较静态固定码表与单独分配的状态码数组。保留的[复现材料](docs/findings/inflate-copy-fixed/README.md)诊断了固定版本中未经修改的 C。现在验证的源码通过[临时补丁](patches/README.md)采用了[上游 PR #1369](https://github.com/madler/zlib/pull/1369) 中完全相同的修复；Lean 翻译也使用相同的相等性检查。对于已诊断的 LP64 问题，证据置信度高；公开 `inflateCopy` 的完整证明仍未完成。
