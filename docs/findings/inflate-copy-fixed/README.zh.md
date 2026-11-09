<!-- source-sha256: e69c7f313f494c723357b9e7524861ea47de455c6220319ca690eaf21df939fd -->
# 固定块流复制比较了无关的指针

置信度：对诊断出的未修补 C 问题有较高把握。验证所用源码现已包含获接受的上游修复。这并非对所有复制历史的证明。

源代码固定版本：`757f0527154291bcf6bfbd6396ecde6bedd2db95`。
该复现程序编译未修改的解码器源代码。它调用默认的 `inflateInit`，提供一个包含固定块的有效 zlib 流，并提供一个输出字节。`inflate` 在生成 `A` 后返回 OK。随后，它调用 `inflateCopy`，并指定一个不同的已清零的目标。

从仓库根目录运行：
```sh
python3 docs/findings/inflate-copy-fixed/reproduce.py
```
编译器与运行时必须支持地址检测和指针比较 sanitizer。
设置 `CC` 以选择编译器。该脚本要求非零的执行退出码以及特定的指针配对诊断；编译错误或其他失败
不计为复现。

保留的复现在 LP64 构建上成功运行。诊断
定位到 `inflate.c:1383` 处的 `inflateCopy`、静态 `lenfix` 对象，以及
单独分配的 inflate 状态。这是源表达式
`state->lencode >= state->codes`。两个调用者原始字节缓冲区均未超出大小或发生别名。
默认的 LP64 Linux 构建尚未针对此发现重新运行。

旧翻译保留了该表达式，其指针模型拒绝比较这两个不同对象中的指针大小。未声称对 `Goal.inflateCopy` 进行了内核检查的反驳。
一次触发故障的复制本身不足以证明 `StreamReachable` 中存在成功复制后的目标状态。

## 已应用的修复

[上游 PR #1369](https://github.com/madler/zlib/pull/1369) 包含该修复。
维护者确认已于 2026 年 11 月 6 日应用。公开获取的
`develop` 和 `master` 头仍指向
`99623ef7097352da7993ba614161fd6a311e046e`，并保留旧的比较。
[临时补丁](../../../patches/README.md) 与已提交的修复提交 `300fea14353d2e2ca61210aca7c48861ded5788c` 完全一致。

经过验证的 C 和 Lean 翻译现在使用指针相等性来区分
内部表与固定表。内部 `lencode` 被设置为拷贝数组的基址；`distcode` 保留其偏移。指针语义和调用者
域保持不变。上述历史复现有意构建
未打补丁的源。[拷贝回归](../../../tests/regression/inflate-copy/README.md)
则构建打了补丁的源，并将实际成功的拷贝调用
与翻译进行对比。
