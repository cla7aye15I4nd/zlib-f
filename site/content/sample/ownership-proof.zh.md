[分配轨迹](/sample/allocation.html)为压缩器获得了状态、窗口、前驱数组、哈希头和 pending 缓冲区，也跟踪了五项资源尚未全部可用时的一次失败。[状态操作](/sample/state-operations.html)随后复用、分支或释放这些对象。证明必须沿实际翻译调用跟踪同一批对象，不能先假设所有有用事实已经成立。

## 初始对象 {#establishment}

公开初始化命题区分调用者存储和它们建立的状态。[`InitDomain`](/reference/source/ZlibF/Spec/Public/Domains.html)描述新身份、唯一对象表示、库全局对象、可读版本信息，以及分配器字段兼容的可写非活流。它不提供初始化后的库不变量，也不假设被调用函数契约。

[`InflateInitial` 和 `DeflateInitial`](/reference/source/ZlibF/Spec/Public/Initialisation.html)在返回堆上描述成功结果。它们包含具体字段设置、流表示和精确分配账本。Deflate 结果指出五个新拥有的身份；inflate 从一个状态和 NULL 窗口开始。初始化证明必须从实际写入和分配结果导出这些事实。

这也是非空泛性义务。前提不可能成立的保持命题，不能为应用证明有用性质。初始化域目标量化覆盖可接受参数组合和允许的不失败分配，再要求成功的实际执行。固定 `witnessHeap` 还展示调用者域能够成立。一个见证补充全称覆盖，不代替其他窗口尺寸或压缩设置。

## 表示与可达历史 {#representation}

[`Zlib.Inflate.Spec.Good`](/reference/source/ZlibF/Proof/inflate.c.base.html)组合活流、`StInv`、`Uniq` 和 `Fresh`。其窗口条款描述实际分配、容量、有效字节数和环形索引；表指针条款区分内嵌 codes 和静态固定表。固定数组范围很重要：Lean 数组值本身不会强制相应 C 声明的长度。

[`Zlib.Deflate.Spec.DGood`](/reference/source/ZlibF/Proof/deflate.c.base.html)类似地包含活压缩器、存储/尺寸约束、唯一性、新鲜性和树不变量。活状态检查中的非 NULL 分配器字段，不等于单独的 `DefAlloc` 断言；后者指定模型支持的默认分配/释放回调。

这些是具体表示谓词，不是完整的算法历史。形状事实本身不确定窗口的逻辑字节，也不建立表项实现了 canonical code。精化所用关系必须把这些含义连接到同一个返回堆。

[`StreamReachable`](/reference/source/ZlibF/Spec/Public/History.html)记录实际成功初始化、实际返回操作、允许的调用者缓冲区更换和成功复制。执行等式记录调用发生过，不会免费提供其规格。`StreamSequenceSafety` 要求把不变量作为每个允许历史的结论，并要求下一个允许调用返回。它不只是当调用者假设不变量时，有条件地保持它。

## 新对象身份 {#identity}

堆在不同类型表中保存不同对象。字节块和状态记录不能暗中共用一个分配身份。`Uniq` 声明每个块编号至多在其中一张表中有对象。

[`C.Fresh`](/reference/source/ZlibF/Runtime/Schema.html)声明从 `nextBlk` 开始的每个身份都未使用。分配证明必须在计数器推进时保持此条件。`Fresh` 和 `Uniq` 的职责不同：前者保护未来分配，后者保护现有身份的解释。两者单独都不声明某两个流拥有缓冲区具有合适的分离关系；相应表示条款也须建立它。

新整数单元的任意内容仍在范围内。已分配容量不证明前驱或指针字段已经写入。[安全参考](/reference/docs/spec/safety.html)解释模型固定的整数垃圾值和新指针为 NULL 的约定。运行时无法检测遗漏指针写入的地方，建立阶段需要先写后读证据。

## 框架条件与活块账本 {#ledger}

[`Frame`](/reference/source/ZlibF/Spec/Public/Initialisation.html)保护显式改变集合之外的既有分配。它也保持静态对象、分配 oracle 和垃圾函数，同时允许新身份及分配尝试计数器推进。它不是整个堆相等。

独立的 `LiveChange` 定义提供精确账本：

```text
after.live b ↔ (before.live b ∧ ¬ removed b) ∨ created b
```

成功初始化时，`created` 指出新拥有块；初始化失败时，没有新的活块遗留，也不移除旧活块。End 的移除集合恰好是原流拥有集合。失败的五请求轨迹必须解释早先缓冲区请求失败之后发生的成功分配。

调用者输出需要比整个对象的框架条件更细的范围。[`BufferFrame`](/reference/source/ZlibF/Spec/Public/History.html)保持字节数组尺寸，以及授权区域并集之外的字节。它允许已交付前缀或登记头部目标变化，但不授予任意修改同一分配其余部分的权利。

## 重置与复制义务 {#operations}

Reset 中，分配身份不变和逻辑历史改变必须同时成立。[`inflateResetPre` 和 `DeflateResetContract`](/reference/source/ZlibF/Spec/Public/Lifecycle.html)说明哪些计数器、指针和历史字段变化。不兼容的解码器窗口可以从拥有集合消失；普通压缩器重置保留分配并清空字典哈希。要求 `DGood` 的条件性 reset 定理，不能为新分配建立 `DGood`：初始化必须先构造所需状态和树事实。

[`relocateCode`、`copiedDeflate` 和复制目标](/reference/source/ZlibF/Spec/Public/Copy.html)描述相同进度与独立存储。静态编码指针可以共享；指向复制内嵌数组的引用改到新身份。Pending 游标和树描述符需要相应重定位。源流/状态保持不变，失败不留下新拥有的目标块。单独正确的字节复制会漏掉这些指针和所有权义务。

## 反例与范围 {#scope}

[方法记录](/reference/docs/proof/method.html#one-representation-invariant)描述了较早不变量允许 gzip EXTRA 阶段配合 NULL 头部的情况。该条件性执行暴露缺少的状态关系。它不建立允许的公开历史能到达此状态，也不支持排除合法调用者输入。

[契约审查](/reference/docs/checking/contract-review.html#counterexamples-to-the-old-statements)还记录了旧表查询允许 `2^63` 个槽位，而不是实际内嵌范围。对该表示问题的反例要求经过审查的命题修正，不能伪装为证明捷径。改变任何前提之前，先区分证明技术失败、错误规格、翻译不符和真实 C 缺陷。

历史、指针初始化和功能含义的更广组合，仍需通过相应执行证明 **to confirm**。高级操作保留各入口效果和调用序列安全义务；普通格式阶段不自动精化字典替换、预置位和恢复的每种组合。这里的定义和局部结果用于定位证据，不代表完整接受。[完整方法](/reference/docs/proof/method.html)、[流组合](/reference/docs/proof/stream-composition.html)和[当前进展](/reference/docs/progress.html)保留精确义务、范围和具名提交的接受证据。
