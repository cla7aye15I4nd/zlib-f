<!-- source-sha256: 13b3e8487b6f305ddaad94b36ed7ff2fa17b561079514d2b94fbdc90c3cb079e -->
# 上游 PR 草稿：x.next 前进零

供所有者提交。一个 PR 覆盖 [gz-reset-next-uninitialised](README.md) 和 [gz-next-dangling-after-direct-read](../gz-next-dangling-after-direct-read/README.md)；改动是 [0005-gz-next-zero-advance.patch](../../../patches/0005-gz-next-zero-advance.patch)。尚未发送任何内容。向上游提交的是英文原文；下面是它的中文译文。

---

**标题：** gzseek64, gz_skip_have: do not advance x.next when nothing is skipped（gzseek64、gz_skip_have：没有跳过任何内容时不移动 x.next）

**问题**

`gzseek64`（读取，非透明）和 `gz_skip_have`（由 `gzdirect` 和 `gz_skip` 使用）在 `n` 为 0、即输出缓冲区为空时也执行 `state->x.next += n`。在两个文档允许的历史中，此时 `x.next` 不持有有效指针：

1. 刚对 gzip 文件 `gzopen`/`gzdopen` 之后：`gz_reset` 不设置 `x.next`，而状态来自 `malloc`。`gzseek(f, 3, SEEK_SET)` 或 `gzdirect(f)` 于是对不确定的值做运算。
2. 在一次大到直接解压进调用者缓冲区的 `gzread` 之后，`gz_decomp` 让 `x.next` 指向该缓冲区（`x.have` 为 0）。应用程序释放其缓冲区后，`gzseek` 或（成员结束后的）`gzdirect` 对指向已释放对象的指针做运算。

两者在 C 中都是未定义行为（C11 6.2.4p2、6.2.6.1p5、6.5.6p8），尽管 `p + 0` 在当前编译器上无害，也没有 sanitizer 报告。

**复现**

```c
gzFile f = gzopen("data.gz", "rb");
gzseek(f, 3, SEEK_SET);                /* x.next += 0, x.next never written */
```

```c
gzFile f = gzopen("data.gz", "rb");   /* 100000 bytes compressed */
unsigned char *buf = malloc(100000);
gzread(f, buf, 100000);                /* x.next now points into buf */
free(buf);
gzseek(f, 1, SEEK_CUR);                /* x.next += 0 on a dangling pointer */
```

在 `x.next += n` 上的探针显示：第一种情况 `n == 0` 且 `x.next == 0xbebebebebebebebe`（ASan 的新内存），第二种情况是一个指向已释放缓冲区内部的指针。

**修复**

只有 `n` 不为零时才移动 `x.next`。`n` 不为零时 `x.have` 不为零，所以 `x.next` 指向那些输出。在 `gz_reset` 中设置 `x.next = NULL` 不够：`NULL + 0` 在 C 中同样未定义，而且悬空的情况仍然存在。

**测试**

- `make test`，默认构建以及 `-fsanitize=address,undefined`：通过。
- 探针显示修复前有零前进，修复后没有。
- 大约 30 000 个带故障注入的随机 gz 调用历史，在 macOS 和 x86_64 Linux（带 LeakSanitizer）上以 ASan 和 UBSan 运行：没有报告，没有泄漏，没有挂起。
