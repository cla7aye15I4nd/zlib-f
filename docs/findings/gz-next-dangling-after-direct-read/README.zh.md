<!-- source-sha256: 1b01e0fa16dbe122373cb707eaa5a579f606898e15b3138d1ef3400e07620523 -->
# 直接读取之后 x.next 留在调用者的缓冲区中

状态：按 C 标准的字面规定是未定义的。没有任何 sanitizer 报告它，也没有观察到错误行为。验证对象中由本地补丁
[0005-gz-next-zero-advance.patch](../../../patches/0005-gz-next-zero-advance.patch) 修复；该补丁经所有者于
2026-11-12 批准，尚未提交上游。同一补丁也修复 [gz-reset-next-uninitialised](../gz-reset-next-uninitialised/README.md)。

源码固定版本：`757f0527154291bcf6bfbd6396ecde6bedd2db95`，加补丁 0001 至 0004。

## 问题

对 gzip 文件的大请求，`gz_read` 直接解压到调用者的缓冲区：它把 `strm.next_out` 设为该缓冲区并调用 `gz_decomp`，后者最后执行 `state->x.next = strm->next_out - state->x.have`。随后 `gz_read` 把 `x.have` 设为 0，却让 `x.next` 留在调用者的缓冲区内。调用者可以释放那个缓冲区：`gzread` 返回之后，zlib.h 没有给库任何对它的权利。之后：

- `gzseek64`（非透明，输出缓冲区为空）以 `n == 0` 执行 `state->x.next += n`；
- `gzdirect` 在成员已结束（`how == LOOK`）时调用 `gz_skip_have`，后者做同样的事。

C11 6.2.4p2：指针所指对象的生存期结束时，指针的值变为不确定；6.5.6p8：指针运算需要指向对象的指针。因此这次计算是未定义的。在 x86_64 上，用通常的编译器，`p + 0` 不改变 `p`，该指针也从不被解引用。

## 调用历史

```
f = gzopen("data.gz", "rb");             /* 100000 字节压缩数据 */
buf = malloc(100000);
gzread(f, buf, 100000);                  /* 直接解压：x.next 指向 buf 内 */
free(buf);
gzseek(f, 1, SEEK_CUR);                  /* 对悬空指针执行 x.next += 0 */
                                         /* 或：gzdirect(f) */
```

## 证据

强度：仅按 C 标准的字面规定。没有 sanitizer 报告它：没有访问，`p + 0` 也不溢出。Lean 模型会报告它：在模型中，对指向已释放块的指针做运算是故障。在翻译跟上本补丁之前，定理 `gzseek64_dangling_next_ub` 证明了 `gzseek64` 的翻译会到达它；打补丁后，`gzseek64_dangling_next_ok`（`ZlibF/Proof/gzlib.c.seek.lean`）证明在没有缓冲数据时向前定位不会故障，无论 `x.next` 持有什么。复现使用 [../gz-reset-next-uninitialised/probe.h](../gz-reset-next-uninitialised/probe.h) 中的探针：

```
x.next + 0 at gzread.c:313, x.next = inside the freed caller buffer
x.next + 0 at gzlib.c:435, x.next = inside the freed caller buffer
```

文件：`dangling.c`、`run.sh`、[report.txt](report.txt)（x86_64 Linux，gcc 15.2；arm64 macOS 上结果相同）。修复前探针看到这两次计算，修复后一次也没有，两个构建都没有 sanitizer 报告。

## 范围

读取 gzip 文件、请求长度至少为缓冲区两倍、读入的内存在之后对同一文件调用 `gzseek` 或 `gzdirect` 之前已被释放的读取者。在常见平台上没有可观察的后果。

## zlib.h 的说法

对于 `gzread` 返回之后其缓冲区的生存期，没有说明：调用者可以释放它。

## 修复

与 [gz-reset-next-uninitialised](../gz-reset-next-uninitialised/README.md) 相同：[0005-gz-next-zero-advance.patch](../../../patches/0005-gz-next-zero-advance.patch) 只在 `n` 不为零时移动 `x.next`。`n` 不为零时，输出刚在库自己的缓冲区中产生，`x.next` 指向那里。在任何路径上，结果、返回值和状态都不变。

PR 草稿（两者共用一个 PR）：[../gz-reset-next-uninitialised/upstream-description.md](../gz-reset-next-uninitialised/upstream-description.md)。
