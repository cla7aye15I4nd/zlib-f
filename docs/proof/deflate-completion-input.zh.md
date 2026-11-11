<!-- source-sha256: 69956439b619291ae5298462a6c65371a6413ea65d6d6919f68dc93945cb779c -->
# FINISH 之后出现新输入以及完成目标

> **历史记录。** 本文描述写作当时的流程：锁文件、重新生成的锁、经批准的基线以及对锁差异的审阅。这些机制后来已被移除，现在没有锁文件，见[防作弊](../anti-cheating.md)。下文只应作为那个快照的证据来读。

本文件记录了对已审查的完成调用者协议修正的证据。
它不是 zlib 的缺陷报告，也不是经过内核验证的反例。
当前状态和剩余工作维护在[概览](../overview.md)中。

## 契约与目标

固定的源代码为 `757f0527154291bcf6bfbd6396ecde6bedd2db95`。
其 `zlib.h` 中关于 FINISH 的段落要求，在返回 OK 或 BUF_ERROR 后重试时，
必须提供更多输出空间，但不得提供更多输入数据。

早期的 `Spec/Public/Sequences.lean` 使用实际的 DeflateDataTrace、未完成和仅完成边界标志、DGood、
已接纳的缓冲区、可读的输入切片以及在边界下的足够输出来定义 DeflateCompletes。
它没有排除在 FINISH_STATE 中出现新输入的条件。
该跟踪的 Rebuffer 转换接纳了此类调用者编辑。边界标志
仅记录所有观察到的 flush 参数是否都等于 FINISH。

现有的已翻译执行证明已经暴露了已完成状态下
对新输入的拒绝。实际调用可能在返回 BUF_ERROR 之前发布待处理字节。
这与编码历史定理兼容：
该定理陈述当实际返回 STREAM_END 时的精确编码，
并不断言对每次此类调用都完成。

## 具体的 C 执行

[复现程序](deflate-completion-input.c) 执行默认初始化，
使用空输入和三个输出字节进行 FINISH，然后使用一个新输入字节和 64 个输出字节进行 FINISH。
针对固定的源代码，使用地址和未定义行为 sanitizer编译，程序以零退出并打印：
```text
init=0 first_finish=0 status=666 FINISH_STATE=666 pending=1 observed_output=3 bound=14 next_capacity=64 next_finish=-5 remaining_input=1 total_input=0 total_output=4
```
第一次调用返回 OK，进入 FINISH_STATE，并保留一个待处理字节。
单个输入字节的界限为 14，至多等于前三个输出字节加上新容量 64。第二次调用发布一个待处理字节，
然后返回 BUF_ERROR。它未消耗任何新的输入。
未观察到任何 sanitizer 诊断信息。本次运行是 C 行为的证据，
而非翻译保真度的证明，也不是对目标的正式反证。

要复现，请使用仓库中的
`tests/build-zlib.sh` 将固定版本的源代码构建到一个全新的输出目录中，并使用
`-O1 -g -fsanitize=address,undefined -fno-sanitize-recover=undefined`。
使用相同的标志编译此复现程序，将复制的源代码目录作为其包含目录，并使用其静态 `libz.a`。仅当所述完成状态、界限和拒绝观察成立时，退出状态才为零。

## 审查边界

[必要协议引理](../../ZlibF/Proof/deflate.c.engine.completion-protocol.lean)
已在本地通过内核检查。它源自一个实际的、作用域受限的默认数据
历史，该历史表明：当处于 FINISH_STATE 且存在非空可读输入以及正数原始
输出时，不能返回 STREAM_END。它既不假设执行契约，
也不假设强化后的历史规则。它本身并不确立具体完成历史的所有
前提。

人工审查已授权精确的单行完成前提
`s.status = FINISH_STATE → z.avail_in = 0`，连同相应审计锁的重新生成。此条件现已应用于
DeflateCompletes。它实现了头文件中的重试义务。实际数据
跟踪构造器、被拒绝调用的安全性、翻译和运行时均
未更改。语义锁的差异需要对此授权的目标含义变更进行显式审查；重新生成本身并非批准。

针对先前目标的精确可达 Lean 反例，包括
其所有完成前提，仍**待核实**。编码正确性、
安全执行和输出长度预算是独立的义务。
修正后的完成定理仍需要其实现证明。
