<!-- source-sha256: 56db4ba4be73302d35c35f5f624f4913d8ac8f55cfa27bd3184fa59d964dccdc -->
# 补丁

验证对象是固定版本的 `zlib/` 子模块，加上本目录中按文件名顺序应用的所有 `*.patch` 文件。

## 0001-inflate-copy-pointer-equality.patch

`inflateCopy` 不再对静态固定码表与状态内部码数组中的指针做关系比较。保留的[复现材料](../docs/findings/inflate-copy-fixed/README.md)诊断了未打补丁的 C。这一问题阻碍相应的全称安全证明。

补丁与[上游 PR #1369](https://github.com/madler/zlib/pull/1369) 中的提交 `300fea14353d2e2ca61210aca7c48861ded5788c` 完全一致。维护者已于 2026 年 11 月 6 日确认会应用该修复。当前公开可获取的 `develop` 和 `master` 分支头仍为 `99623ef7097352da7993ba614161fd6a311e046e`；其中的 `inflate.c` 仍保留旧的指针比较。因此，在修复提交出现在上游分支之前，继续使用当前固定版本和这一已提交的修复。届时再更新固定版本并删除补丁。

绝不直接修改子模块。只有确认的上游缺陷阻碍证明时才允许打补丁。补丁必须尽可能小、与提交给上游的修复一致，并在本页登记。上游合入修复且固定版本越过该提交后，应删除相应补丁。
