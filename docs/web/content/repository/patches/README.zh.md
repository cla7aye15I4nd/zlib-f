<!-- source-sha256: ab3e02b5f5f0cbdd4ebb9a492438cf299bfaf70efa96e564c3b2ed9a3f959a62 -->
# 补丁

验证对象是固定版本的 `zlib/` 子模块，加上本目录中按文件名顺序应用的所有 `*.patch` 文件。

## 0001-inflate-copy-pointer-equality.patch

`inflateCopy` 不再对静态固定码表与状态内部码数组中的指针做关系比较。保留的[复现材料](../docs/findings/inflate-copy-fixed/README.md)诊断了未打补丁的 C。这一问题阻碍相应的全称安全证明。

补丁与[上游 PR #1369](https://github.com/madler/zlib/pull/1369) 中的提交 `300fea14353d2e2ca61210aca7c48861ded5788c` 完全一致。维护者已于 2026 年 11 月 6 日确认会应用该修复。当前公开可获取的 `develop` 和 `master` 分支头仍为 `99623ef7097352da7993ba614161fd6a311e046e`；其中的 `inflate.c` 仍保留旧的指针比较。因此，在修复提交出现在上游分支之前，继续使用当前固定版本和这一已提交的修复。届时再更新固定版本并删除补丁。

## 0002-gzseek-negative-position-overflow.patch

避免在开头调用 `gzungetc`（它把 `state->x.pos` 设为 -1）之后，`gzseek64` 中的有符号溢出：`SEEK_CUR` 的范围检查在 `pos` 为负时计算 `GZ_OFF_MAX - pos`，而接近 `GZ_OFF_MAX` 的 `SEEK_SET` 目标在 `pos - state->x.pos` 中溢出。UndefinedBehaviorSanitizer 在未打补丁的 C 上报告这两处。这是 [gzip 证明说明](../docs/proof/gzip.md) 中的 R-1，阻碍 `gzseek64` 和 `gzseek` 的安全证明。

补丁是[上游 PR #1361](https://github.com/madler/zlib/pull/1361) 在分支头 `ce2248ee9750` 时 `gzlib.c` 的部分。该 PR 中 `test/example.c` 的部分不属于验证对象。该 PR 尚未合入。

## 0003-gzread-partial-copy-read-error.patch

在透明（`COPY`）模式下，于 `gz_load` 之前设置 `state->x.next = state->out`。如果 `read` 先提供一些字节后失败，`gz_load` 把部分计数留在 `x.have` 并返回 -1，而 `gz_fetch` 在给 `x.next` 赋值之前就返回了。随后读取函数通过过时的 `x.next` 消费这些字节：当先前的输出缓冲区已用完时，这是越界读。这是 [gzip 证明说明](../docs/proof/gzip.md) 中的 R-2，阻碍读取一侧的安全证明。

补丁与[上游 PR #1363](https://github.com/madler/zlib/pull/1363) 在分支头 `37627fd3bb47` 时的改动完全一致。该 PR 尚未合入。

## 0004-gz-position-overflow.patch

本地补丁，尚未提交上游；所有者于 2026-11-12 批准。

使未压缩位置 `state->x.pos` 始终能用 `z_off64_t` 表示。读取：`gz_fetch` 只向输出缓冲区填入位置可表示的字节（至少一个，以便仍能发现输入结束），`gz_read` 和 `gzgets` 不交付超过 `GZ_OFF_MAX` 的字节；超出部分的数据给出 `Z_DATA_ERROR` "position overflow"。写入：`gz_write`、`gzputc` 的快速路径和 `gzprintf` 拒绝会使位置超过 `GZ_OFF_MAX` 的写入，给出同样的错误。发现：[gzread-pos-overflow](../docs/findings/gzread-pos-overflow/README.md)（F-1）和 [gzwrite-pos-overflow](../docs/findings/gzwrite-pos-overflow/README.md)（W7）。证据：在 x86_64 Linux 上用 `/dev/zero` 和真实的 `/dev/null`，UndefinedBehaviorSanitizer 对两者都报告有符号溢出；复现在 `tests/regression/` 下。这阻碍 gz 读写函数的安全证明。PR 草稿在读取一侧的发现中。

## 0005-gz-next-zero-advance.patch

本地补丁，尚未提交上游；所有者于 2026-11-12 批准。

在 `gzseek64` 和 `gz_skip_have` 中，只有当前进量 `n` 不为零时才移动 `state->x.next`。当 `n == 0` 时，该字段可能从未被写入（`gz_reset` 不设置它：R-3），也可能指向调用者在一次直接 `gzread` 之后已释放的缓冲区（R-4）；对这两种值做指针运算在 C 中都是未定义的。任何结果和状态都不变。发现：[gz-reset-next-uninitialised](../docs/findings/gz-reset-next-uninitialised/README.md)（R-3）和 [gz-next-dangling-after-direct-read](../docs/findings/gz-next-dangling-after-direct-read/README.md)（R-4）。证据：按 C 标准的字面规定未定义；没有任何 sanitizer 报告它们。复现中的探针显示了对从未写入的值和悬空值的零前进，以及打补丁后它们消失。没有这个补丁，“指针字段先写后读”的证明规则以及模型对悬空指针运算的故障会阻碍 gz 读取函数的证明。PR 草稿在 R-3 的发现中。

绝不直接修改子模块。只有确认的上游缺陷阻碍证明时才允许打补丁。补丁必须尽可能小、与提交给上游的修复一致，并在本页登记。经所有者批准的补丁可以先于向上游提交而合入；其条目会注明它是本地补丁、等待提交，一旦有上游修复就用上游修复替换它。上游合入修复且固定版本越过该提交后，应删除相应补丁。
