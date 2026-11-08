<!-- source-sha256: 7d456db76892551588ed529bb1d2fa625a87aaa57e6fad0ef6d3288f6e7af649 -->
# zlib-f

用 Lean 4 形式化验证 zlib。对 C 源码作忠实翻译，再证明内存安全、终止性、资源所有权和功能正确性。

**项目尚未完成全库验证。** 首个目标是默认 LP64 Linux 静态构建，使用默认分配器。

## 文档

**[阅读文档网站](https://www.dataisland.org/zlib-f/)** · [浏览 Markdown 文档](docs/README.md)

| 阅读入口 | 内容 |
| --- | --- |
| [证明总览](docs/overview.md) | 目标、假设和证明框架。 |
| [当前进度](docs/progress.md) | 已完成的结果和剩余工作。 |
| [全部目标的依赖图](docs/progress.md#proof-progress-graph) | 目标之间的依赖及各自覆盖的输入范围。 |
| [证明证据](docs/progress.md) | 精确命题、证明正文和各类关系表。 |
| [规格](docs/spec/README.md) | 需要证明的安全、输入、API、内部函数和格式要求。 |
| [API](docs/spec/api/README.md) | 每个函数的前提和保证。 |
| [数据格式](docs/spec/format/README.md) | DEFLATE、zlib 和 gzip 字节的含义。 |
| [设计](docs/design/README.md) | 翻译方式与内存模型。 |
| [证明](docs/proof/README.md) | 各部分论证的组合方式。 |
| [检查](docs/checking/README.md) | 证明的验收条件。 |

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

各项检查的范围和最终验收条件见[检查指南](docs/checking/README.md)。差分测试用来检查翻译与 C 的一致性。全称正确性由证明建立。
[源码问题记录](docs/findings.md)列出问题的证据强度和适用范围。
