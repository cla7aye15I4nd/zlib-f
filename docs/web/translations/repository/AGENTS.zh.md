<!-- source-sha256: 78152e01564a024e6016d933b8cc9476c8c9e645e2e8caf78891b20e071fb9f8 -->
# 工作规则

目标是用 Lean 4 内核检查对上游 zlib `develop` 分支忠实翻译的证明。先覆盖默认 x86_64 Linux 构建，再覆盖上游 CI 构建的全部配置。证明范围包括安全性：无未定义行为、无内存错误、无泄漏、保证终止；以及完整功能正确性。工作从 `inflate` 和 `deflate` 开始。先读 `docs/overview.md`，再读 `docs/spec/safety.md`。证明结构放在 `docs/overview.md`，当前状态和剩余工作只放在 `docs/progress.md`。

## 源码

- `zlib/` 是上游子模块，禁止修改。验证对象是 `zlib/` 加上按名称顺序应用的 `patches/*.patch`。
- 只有已复现且阻碍证明的 zlib 缺陷才允许使用补丁。补丁必须最小化，与已提交上游的修复一致，并列在 `patches/README.md`。上游合入修复且固定版本更新后，删除补丁。
- Lean 文件与 C 文件一一对应：`zlib/X.c` 对应 `ZlibF/Zlib/X.c.lean`，`zlib/X.h` 对应 `ZlibF/Zlib/X.h.lean`。每个模块依次放翻译、规格、证明。函数保留 C 名称，文档注释以 C 签名开头。
- 不涉及堆的数学放在 `ZlibF/Math/`。堆、指针、循环和故障等运行时语义放在 `ZlibF/Runtime/*.lean`。

## 翻译

- 逐条语句翻译，禁止重排、合并或简化。
- C 能到达的每一种未定义行为都必须产生 `Fault.ub`。无符号算术回绕，有符号算术接受范围检查。
- 读取未初始化整数时返回任意值，定理必须对所有取值成立。模型把新分配内存中的指针设为 NULL，这比 C 弱。因此证明还必须建立：读取指针字段前已经写入该字段。见 `docs/spec/safety.md` 第 3 节和 `docs/trusted-base.md` 第 2 项。
- 禁止为方便证明而修改翻译。与 C 不一致就是翻译缺陷；修复后还要添加能发现它的差分测试。
- 修改运行时必须经过独立审阅，因为所有证明都依赖运行时。

## 已证明的判定

- 定理必须列在 `tests/audit/theorems.txt`，并通过审计。只允许依赖 `propext`、`Classical.choice` 和 `Quot.sound`。禁止使用 `native_decide`、`bv_decide`、`axiom` 或 `implemented_by`。
- 最终要求是全部 Lean 源码没有 `sorry`。CI 的 `no-sorry` 独立检查这一点，使开发中的提交仍可运行构建、审计和差分测试。`no-sorry` 失败时，禁止把结果报告为最终完成。
- 定理必须明确写出前置条件。如果条件比 `zlib.h` 允许的范围窄，必须在定理注释中说明，并列入 `docs/deviations.md`。禁止悄悄缩小定义域。
- **禁止把被调用函数的契约当成假设。** 被调用函数的规格必须由关于该函数翻译的定理建立。初始化函数必须建立表示不变量，并证明它可以成立。只有顶层定理需要具体见证。
- 每个已证明函数都必须有证明变异测试：删除检查、制造差一错误等翻译变异必须在该函数的证明位置导致检查失败。
- 证明卡住时，必须区分四种可能原因：证明方法、错误规格、翻译缺陷或真实 zlib 缺陷。若怀疑 zlib 缺陷，应构造具体输入，在真实 C 上用 Sanitizer 复现并报告。禁止缩小前置条件来掩盖缺陷。
- 差分测试用于核对翻译一致性；报告时必须与全称证明区分。

## 检查

CI 包括四项作业：`build` 检查全部模块、禁止的构造及补丁能否应用于固定的 `zlib/`，这一项必须始终通过；`no-sorry` 检查最终无占位证明要求；`audit` 检查公理依赖、锁定记录、目标和自检；`difftest` 运行差分测试。没有执行的检查，禁止报告为通过。

## 问题记录

已复现的 zlib 问题记录在 `README.md`：简述问题，链接 `docs/findings/` 下的复现材料，并注明证据强度和适用范围。尚未复现的报告留在 `docs/progress.md`。

## 文档

- 文件名使用小写和连字符，例如 `method.md`；`README.md` 和 `AGENTS.md` 保留惯用名称。
- 使用短句，明确说明已经证明的内容、采用的假设和未完成工作。
- 尚未由证明建立的 C 解读，直接标明相关证明未完成。
- 用 Mermaid 图表达结构和顺序，不要把列表改画成图。
- 不把机器名、地址、用户名、本地路径或工具名写入仓库。

## 协作

- 使用小型、堆叠的拉取请求，每一份都能独立审阅。
- 并行工作按不同 C 文件或函数拆分。运行时、头文件等共享部分由一位审阅者统一处理。
- 提交说明描述改动，不添加工具署名行。

## 仓库代理工作规则

这些规则用于保证绿色构建确实有意义。原因见 [docs/anti-cheating.md](docs/anti-cheating.md)。

- 除非任务明确要求修改对应部分，否则禁止编辑 `tests/audit/`、`.github/`、`scripts/`、`patches/`、`lakefile.toml`、`lean-toolchain`、`docs/spec/`、`docs/README.md`、`docs/design/api-model.md`、`docs/spec/internal-contracts.md`、`docs/checking/goals.md`、`docs/checking/contract-review.md`、`ZlibF/Runtime/` 或 `AGENTS.md`。若任务包含这类改动，必须在拉取请求中说明。
- 禁止手工修改锁文件。必须通过审计重新生成，并解释差异。
- 禁止为使证明通过而修改定理陈述、规格定义或翻译。若陈述错误，应说明错误和原因，并停止该项证明工作。
- 禁止把尚未证明的定理加入 `tests/audit/theorems.txt`，也禁止删除已有定理。
- 禁止使用 `sorry`、`axiom`、`native_decide`、`bv_decide`、`implemented_by`、`extern`、`unsafe`、`partial` 或 `opaque`。审计会拒绝这些构造；遇到阻碍应报告，禁止绕过审计。
- 报告已证明和未证明的内容。只有指明的提交通过全部 CI 后，才能把对应结果报告为完成证明。
