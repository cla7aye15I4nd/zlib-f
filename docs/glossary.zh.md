<!-- source-sha256: b6f11daa650f703c8a766f5120804e8a2589d95e7730446096fb98b5479f53e9 -->
# 术语表

文档中常用术语的简短定义。每一条都注明精确定义所在的位置。条目与来源不一致时，以来源为准。

## 目标与状态

| 术语 | 含义 |
| --- | --- |
| 目标（target） | `tests/audit/goals.txt` 中列出的一个固定命题。[进度](progress.zh.md)中的生成区块给出全部目标的当前数量和状态。 |
| Goal | 目标的 Lean 陈述，位于 `ZlibF/Spec/`（例如 `ZlibF.Spec.Public.Goal.inflate`）。Goal 是固定的；证明必须与陈述完全一致。 |
| 已登记证明 | 列入 `tests/audit/theorems.txt`、类型与目标一致且审计通过的定理。报告中称“已证明”还需要四个必需 CI 状态在指名的提交上全部为绿色。 |
| 本地检查 | 在一台机器上构建并审计通过，尚未被 CI 接受。不得报告为已证明。 |
| 受阻（blocked） | 有记录在案的反例或已确认障碍的目标。只有生成器的受阻索引能把目标标为受阻。 |
| 限定范围的结果 | 关于目标定义域受限部分（固定级别、固定历史形状）的定理。它不证明也不缩小公开目标。[偏差](deviations.zh.md)列出这些范围。 |
| 引擎文件 | `ZlibF/Proof/deflate.c.engine.*`（以及类似的 `inflate.c.default-*`）模块之一。多数证明限定范围的默认配置历史，而不是公开目标所需的全称不变式。 |

## 不变式

| 术语 | 含义 |
| --- | --- |
| `Good` | inflate 表示不变式：流记录、状态和窗口存活且归属正确，状态良构（窗口、位计数、内部指针），块编号唯一，分配器的新鲜区域未被使用。定义在 `ZlibF/Proof/inflate.c.base.lean`。 |
| `DGood` | `Good` 的 deflate 对应物：流与状态存活、四个缓冲区、状态字段范围、唯一性、新鲜性以及树不变式。定义在 `ZlibF/Proof/deflate.c.base.lean`。 |
| `GzGood` | `gz_state` 句柄的表示不变式：模式、路径与消息字符串以及可选缓冲区。定义在 `ZlibF/Proof/gzlib.c.base.lean`。 |
| `PosInv` | gz 位置字段的数值不变式，使 `gztell64` 保持在有符号 64 位范围内。定义在 `ZlibF/Proof/gzlib.c.simple.lean`。 |
| `OpenState` | 成功打开 gz 文件后建立的状态。定义在 `ZlibF/Spec/Public/GzOpen.lean`。 |
| `DefAlloc` | 流使用默认的 `zcalloc`/`zcfree` 分配器，这是模型中唯一的分配器。 |
| 全称不变式 | 从每个可达状态出发、经一次调用都保持的不变式，而不只沿某条固定历史成立。尚未证明的公开目标需要这类不变式。 |
| 修改范围（frame） | 一次调用可以改变的堆部分。frame 子句说明其他块全部不变。 |

## 规格术语

| 术语 | 含义 |
| --- | --- |
| `C1`–`C7` | `ZlibF/Spec/Api/Goals.lean` 中抽象 API 模型目标的标签：`C1` 往返，`C2`/`C3` 解码合法流并拒绝非法流，`C4` 字典与头部，`C5` 界限，`C6` 复制，`C7` gz 文件。它们关于模型，而非翻译后的 C。 |
| 普通数据时段（ordinary data epoch） | 只由普通调用组成的流历史部分（不含中途替换原始字典、位预置、头部捕获或恢复）。在其中，序列目标把接受和产生的字节与独立格式联系起来。高级操作保留各自的单次调用与安全目标。见[高级操作边界](checking/contract-review.zh.md)（“高级操作的边界”一节）。 |
| `detectLag` | API 模型中 inflate 报告非法数据最迟时间的界限。取值 8 有反例；见[API 模型](design/api-model.md)。 |
| 定义域见证 | 满足定理前提的具体可达状态，说明前提非空。顶层定理需要它。 |
| `Fault.ub` | 模型中 C 未定义行为的结果。排除它的定理证明该调用没有未定义行为。 |
| 额度（fuel） | 每个翻译循环携带的固定迭代上界。额度耗尽是故障，因此终止性是每条定理的一部分。 |

## 检查术语

| 术语 | 含义 |
| --- | --- |
| 四个必需状态 | `build`、`no-sorry`、`audit` 与 `difftest`。`audit` 汇总 `audit_core`、`audit_selftest` 与 `audit_mutants`；`difftest` 汇总 `diff_core` 与 `diff_harness`。见[检查](checking/README.zh.md)。 |
| 锁文件 | `tests/audit/` 下的生成文件（`statements.lock`、`policy.lock`、`trusted.lock`），记录已审查的陈述类型或受保护文件的哈希。由 `scripts/verification.py regenerate` 重新生成，绝不手工编辑。 |
| 证明变异体 | 对翻译的有意改动（删除检查、差一错误），它必须使该函数的证明失败。见[证明变异](checking/proof-mutants.zh.md)。 |
| 限定范围准入（scoped admission） | 唯一一个经过审查的限定范围证明变异案例（`tests/proofmut/deflate-default-scoped-null-output.py`）。它对照保存在仓库变量中的独立批准基线提交进行检查；该提交的 `policy.lock` 与 `trusted.lock` 必须与候选提交完全相同。 |
| 差分测试 | 在相同输入上运行真实 C 与翻译并比较结果。它是忠实性的证据，不是证明。 |
| `to confirm` | 标记一条仍需证明确认的 C 代码解读。 |
