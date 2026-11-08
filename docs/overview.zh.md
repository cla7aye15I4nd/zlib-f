# 理解并证明 zlib

先跟随一次完整任务，再逐层展开需要的机制。每章都把实际操作、例子和由此产生的证明义务放在一起讲。
页面顶部的语言菜单可在同一页切换 **简体中文／English**。

## 目录

- [阅读主线](#reading-path)
- [共用证明规则](#shared-proof-rules)
  - [范围](#scope)
  - [论证](#argument)
  - [证据](#evidence)

## 阅读主线

<a id="1-follow-a-complete-task"></a>
<a id="1-what-zlib-does"></a>
<a id="11-one-library-three-related-formats"></a>
<a id="12-repetition-becomes-a-backward-reference"></a>
<a id="13-meaning-of-compressed-bytes"></a>
<a id="13-symbols-become-bits-and-blocks"></a>
<a id="14-where-these-jobs-live-in-the-library"></a>
<a id="2-how-applications-use-the-apis"></a>
<a id="2-understand-the-encoded-bytes"></a>
<a id="21-one-decoder-two-kinds-of-lifetime"></a>
<a id="22-the-ordinary-inflate-loop"></a>
<a id="23-copies-reuse-and-borrowed-metadata"></a>
<a id="24-compression-has-its-own-completion-protocol"></a>
<a id="3-pause-and-continue-the-same-task"></a>
<a id="33-meaning-of-compressed-bytes"></a>
<a id="4-add-format-headers-and-integrity-checks"></a>
<a id="41-construct-and-interpret-decoding-tables"></a>
<a id="42-join-the-slow-and-fast-paths"></a>
<a id="43-close-the-call-and-its-history"></a>
<a id="5-reuse-branch-and-control-a-task"></a>
<a id="51-window-and-hash-chain-invariants"></a>
<a id="52-trees-symbols-and-shared-output-storage"></a>
<a id="53-publish-blocks-and-compose-calls"></a>
<a id="6-choose-an-application-interface"></a>
<a id="61-construct-and-interpret-decoding-tables"></a>
<a id="62-join-the-slow-and-fast-paths"></a>
<a id="63-close-the-call-and-its-history"></a>
<a id="71-window-and-hash-chain-invariants"></a>
<a id="72-follow-the-actual-implementation"></a>
<a id="72-trees-symbols-and-shared-output-storage"></a>
<a id="73-publish-blocks-and-compose-calls"></a>
<a id="74-locate-the-exact-evidence"></a>
<a id="proving-the-zlib-implementation"></a>

| 章节 | 通过例子理解什么 |
| --- | --- |
| [1. 一次完整任务](guide/round-trip.md) | 原始字节 → 压缩字节 → 还原字节，以及创建、处理和释放。 |
| [2. 重复、编码与数据块](guide/encoding.md) | 历史引用的重叠复制、Huffman 编码和数据块选择。 |
| [3. 流式处理](guide/streaming.md) | 缓冲区耗尽时如何保留位和历史，再准确继续。 |
| [4. 格式与完整性检查](guide/wrappers.md) | 共用的 DEFLATE 主体、包装条件和尾部校验。 |
| [5. 状态操作](guide/state-operations.md) | 用 Reset 开始新任务，用 Copy 保存检查点，以及字典和刷新。 |
| [6. 应用接口](guide/interfaces.md) | 整块缓冲区、回调、gzip 文件与逻辑位置跳转（Seek）。 |

需要精确条件或 C 层面的论证时，再沿章内链接下钻。
[规范](spec/README.md)定义必须满足的行为；[实现证明参考](proof/README.md)按 C 组件给出技术推导。
它们与图解例子回答不同的问题。审阅记录收在“检查与验收”下，不放进入门阅读主线。

## 共用证明规则

<a id="1-what-must-be-proved"></a>
<a id="3-what-must-be-proved-and-why"></a>
<a id="7-how-the-arguments-become-checked-claims"></a>

### 范围

<a id="11-the-implementation-and-configurations"></a>
<a id="12-safety-of-calls-and-lifetimes"></a>
<a id="2-assumptions-and-model-boundaries"></a>
<a id="21-platform-assumptions"></a>
<a id="22-caller-and-external-world-obligations"></a>
<a id="23-what-the-kernel-trusts"></a>
<a id="25-configuration-and-calling-protocol-are-separate"></a>
<a id="31-the-implementation-and-configurations"></a>
<a id="32-safety-of-calls-and-lifetimes"></a>
<a id="4-assumptions-and-model-boundaries"></a>
<a id="41-platform-assumptions"></a>
<a id="42-caller-and-external-world-obligations"></a>
<a id="43-what-the-kernel-trusts"></a>
<a id="71-scope-and-assumptions"></a>

起点是默认 x86_64 Linux 构建与默认输入。更广的嵌套范围统一定义在[输入配置](spec/input-configurations.md)。
例子选择具体运行，不会缩小公开目标的定义域。接受的[平台前提](spec/platform.md)包括：每个被表示的字节对象少于 `2^63` 字节；这不限制整个流的总长度。
[安全规范](spec/safety.md)统一规定 UB、帧性质、终止和资源义务。
[可信基础](trusted-base.md)与[偏离记录](deviations.md)统一记录模型限制。

### 论证

<a id="3-how-the-proof-is-built"></a>
<a id="31-translate-the-actual-c-execution"></a>
<a id="32-establish-an-invariant-by-initialization"></a>
<a id="33-preserve-it-through-calls"></a>
<a id="34-relate-executions-to-byte-meaning"></a>
<a id="4-the-inflate-argument"></a>
<a id="5-how-the-proof-is-built"></a>
<a id="5-the-deflate-argument"></a>
<a id="51-translate-the-actual-c-execution"></a>
<a id="52-establish-an-invariant-by-initialization"></a>
<a id="53-preserve-it-through-calls"></a>
<a id="54-relate-executions-to-byte-meaning"></a>
<a id="6-the-inflate-argument"></a>
<a id="7-the-deflate-argument"></a>
<a id="73-establish-preserve-and-compose"></a>

对象是固定版本的 C 加上已登记补丁，并逐语句翻译。各章对实现的解读都**待确认**，需要证明支持。
初始化必须建立状态不变量与所有权。每次实际调用都要推出辅助函数的前提，并在返回的堆上保持所需性质；End 要交代资源释放。
被调用函数的契约必须是关于该函数的已证明定理。顶层定义域还需要具体见证。

[共用证明方法](proof/method.md)对合法调用历史做归纳，把这些步骤连接起来，并将实际字节与独立格式含义对应。
各章只在相关例子处解释该机制特有的不变量。

### 证据

<a id="6-reading-a-formal-result"></a>
<a id="61-find-its-exact-statement"></a>
<a id="62-follow-its-proof-and-evidence"></a>
<a id="8-reading-a-formal-result"></a>
<a id="81-find-its-exact-statement"></a>
<a id="82-follow-its-proof-and-evidence"></a>

检查精确命题、调用者定义域与返回状态。局部分支引理或无堆模型定理不能独自证明整个公开 API。
早期的 `C1`–`C7` 标签指向 [API 模型目标](../ZlibF/Spec/Api/Goals.lean)；具体执行仍需自己的细化论证。
有限差分运行只能核对例子，不能证明全称命题。[检查指南](checking/README.md)定义指定提交上的验收要求。
只有[进度页](progress.md)记录当前证据、完整目标依赖图与剩余工作。
