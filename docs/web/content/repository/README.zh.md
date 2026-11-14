<!-- source-sha256: 5e9444247b1cd1ec61d0ca87cc784e48f5ae4d17fde34f50bd79dc6138d3f6a1 -->
# zlib-f

用 Lean 4 形式化验证 zlib：对 C 源码作忠实翻译，再证明其安全性、终止性和资源所有权。自 2026-11-11 起功能正确性不在计划内，但计划内的安全证明所依赖的功能性事实除外；已经证明的部分保留。

**项目尚未完成。** 安全结论按以下顺序被验收时项目完成：`inflate` 对每个输入都安全；`deflate` 对每个输入都安全，两者都包括各自的调用序列；然后是其他每个公开函数，包括 gzip 文件接口和回调解码器 `inflateBack`。`compress` 与 `uncompress` 的安全性作为组合随后完成。目标是默认的 x86_64 Linux 构建；其他构建配置不在计划内。[状态页](https://www.dataisland.org/zlib-f/status.zh.html)根据证明记录，把每项结论显示为未完成、已检查或已登记。

## 目标

每个公开函数有两个目标，都在 Lean 命名空间 `ZlibF.Spec.Public.Goal` 中。它的**安全目标**在 `ZlibF/Spec/Safety/` 中，陈述调用返回、没有未定义行为、只写自己的帧、不泄漏。它的**功能目标**在 `ZlibF/Spec/Functional/` 中，陈述结果是什么。`tests/audit/public-api.json` 为每个函数写出两者（`safety_goal`、`functional_goal`）。CI 要求安全目标和非空性目标：每个都必须在 `tests/audit/theorems.txt` 中有一个类型恰好相同的定理，除非 `open_safety` 带负责人列出了它，而该列表只能缩短。已证明的功能目标接受完整审计；未证明的不使任何检查失败。见[拆分说明](docs/design/safety-functional-split.md)。

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
- `ZlibF/Spec/Safety/`：必需的安全目标。`ZlibF/Spec/Functional/`：功能契约、格式模型和 API 模型。`ZlibF/Spec/Public/`：两者共用的定义。
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

## 源码问题：gz 位置溢出

`gzread` 和 `gzwrite` 把搬运的字节数加到有符号 64 位位置 `x.pos` 上，不做上界检查。在位置能到达 2^63 − 1 的透明文件上，这个加法会溢出，是未定义行为。读取：在 `lseek` 成功却不移动的设备上（Linux 上的 `/dev/zero`），`gzseek(INT64_MAX, SEEK_SET)` 被接受，随后的 `gzread` 在 `gz_read`、`gzgetc` 和 `gzgetc()` 宏中溢出（[复现](docs/findings/gzread-pos-overflow/README.md)）。写入：透明写入者在 `/dev/null` 上定位到接近 2^63 之后，`gzwrite` 和 `gzputc` 溢出（[复现](docs/findings/gzwrite-pos-overflow/README.md)）。在 x86_64 Linux 上用固定版本的 C，UndefinedBehaviorSanitizer 报告了两者。对诊断出的序列，置信度高。范围：`lseek` 成功却不移动的设备，或接近 2^63 的透明位置。验证对象包含一个本地修复，[补丁 0004](patches/README.md)，经所有者批准，尚未提交上游：位置保持在 `z_off64_t` 之内，会溢出的调用以 `Z_DATA_ERROR` 失败。

该修复中的一个缺口：`gz_look` 的透明 COPY 分支缓冲至多 `size` 个字节，不受剩余空间的限制。所以在一个带尾部数据的 gzip 成员、`gzclearerr` 和一次接近 2^63 − 1 的读取之后，读取者返回时 `x.pos + x.have` 超过 `GZ_OFF_MAX`，随后 `gzgetc()` 宏使 `x.pos` 溢出（[发现](docs/findings/gz-position-copy-overflow.md)）。已在模型中确认，也已通过阅读 C 确认；实际中无法复现（约 2^63 个解码字节）；没有 sanitizer 确认。对按所写的打过补丁的源码，置信度高。范围：带补丁 0004、在这段历史之后位置距 `GZ_OFF_MAX` 不到 `size` 个字节的读取者。补丁 0004 现在也限制了这个分支。

## 源码修复

使用默认参数初始化的流如果在固定块中途暂停，`inflateCopy` 会比较静态固定码表与单独分配的状态码数组。保留的[复现材料](docs/findings/inflate-copy-fixed/README.md)诊断了固定版本中未经修改的 C。现在验证的源码通过[临时补丁](patches/README.md)采用了[上游 PR #1369](https://github.com/madler/zlib/pull/1369) 中完全相同的修复；Lean 翻译也使用相同的相等性检查。对于已诊断的 LP64 问题，证据置信度高；公开 `inflateCopy` 的完整证明仍未完成，且在计划内：`inflateCopy` 是 `inflate_sequence` 所涉及的流调用。
