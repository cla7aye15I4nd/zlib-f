<!-- source-sha256: 3c446917abcbd88746b7eca4760b73872f1c3f6ff1d56517630dd01435c0d7d5 -->
# 贡献一个证明

本页给出从一个未完成目标到合并并登记的证明的最短路径。每一步背后的规则见
[`AGENTS.md`](../../AGENTS.md)、[检查](README.zh.md)和[验证政策](../anti-cheating.zh.md)。术语见[术语表](../glossary.zh.md)。

所有命令都在仓库根目录运行。每个命令块注明在哪里检查过：
**本地运行**指在一台单进程内存上限为 6 GiB 的 arm64 macOS 机器上运行过；**CI** 指由指定的 CI 作业运行，未在本地运行。

## 开始之前

```sh
git submodule update --init zlib
lake build ZlibF
```

`lake build ZlibF` 构建所有模块；之后的构建是增量的。有些模块需要超过 6 GiB 内存（例如在内核中计算 CRC 表的
`ZlibF/Proof/crc32.c.lean`）。如果你的机器无法构建它们，就使用 CI 对同一提交的构建结果。
`build` 作业发布名为 `lean-build` 的制品；把其中的输出解压到 `.lake/build` 上，再确认没有需要重新构建的模块（本地运行）：

```sh
gh run download RUN_ID -n lean-build
tar -xzf lean-build.tar.gz .lake/build/lib/lean .lake/build/ir
lake build --no-build ZlibF
```

`RUN_ID` 是同一提交上的一次 `lean` 工作流运行。制品保留两天。

## 1. 选择目标

打开[进度](../progress.zh.md)。其生成区块列出 `tests/audit/goals.txt` 中的每个目标及其状态。
[按顺序的下一步工作](../progress.zh.md#ordered-next-work)表给出每个未完成目标的顺序和前提。
不要开始陈述已有记录在案的反例的目标；修正由所有者先决定。

目标 `ZlibF.Spec.Public.Goal.gztell` 是 `ZlibF/Spec/Public/` 下某个文件中的定义 `Goal.gztell`。用下面的命令查找：

```sh
grep -rn "def Goal.gztell " ZlibF/Spec
```

## 2. 陈述并证明

1. 把证明放在 `ZlibF/Proof/<C 文件>.<主题>.lean`，例如 `ZlibF/Proof/gzlib.c.tell-public.lean`。
   翻译在 `ZlibF/Zlib/`，规格在 `ZlibF/Spec/`，与堆无关的数学在 `ZlibF/Math/`。
2. 陈述一条类型与目标完全相同的定理，例如
   `theorem gztell_public : ZlibF.Spec.Public.Goal.gztell := by …`。
   其文档字符串以 C 签名开头并说明适用范围。
3. 被调用函数的性质要作为关于翻译后被调用函数的定理来证明。不要假设被调用函数的契约。
4. 从 `ZlibF.lean` 或它导入的某个模块导入该模块，使 `lake build ZlibF` 检查它。
5. 检查（本地运行）：

```sh
lake build ZlibF
scripts/check-sorry.sh
```

绝不使用 `sorry`、`axiom`、`native_decide`、`bv_decide`、`implemented_by`、`extern`、`unsafe`、
`partial` 或 `opaque`。证明卡住时，按 [`AGENTS.md`](../../AGENTS.md) 的说明判断原因（证明技术、规格错误、
翻译错误、zlib 缺陷）。绝不为了让证明通过而修改目标、规格或翻译。

## 3. 添加证明变异体

每个已证明的公开入口都需要对其翻译函数体的变异，并且其证明必须拒绝这些变异。

1. 在 `tests/proof-mutants/` 中该入口所属领域的列表（`public-queries.tsv`、`public-checksums.tsv`、
   `public-streams.tsv`）中添加行。每行为 `NAME<TAB>FILE<TAB>OLD<TAB>NEW<TAB>PROOF_MODULES`；
   `OLD` 必须在 `FILE` 中恰好出现一次，`PROOF_MODULES` 是 `ZlibF/Proof/` 下不带 `.lean` 的文件名。
2. 像 `audit_mutants` 一样以严格模式运行你添加的行。运行器在临时副本中工作，绝不改动你的工作区。
   最后一个参数是匹配变异体名称的正则表达式（本地运行）：

```sh
PROOFMUT_STRICT=1 bash tests/audit/proofmut.sh tests/proof-mutants/public-queries.tsv '^zlibVersion-wrong-string$'
```

3. 每个新行都必须报告 `KILLED`，且第一个错误位于你的证明模块中。
4. 在 `tests/audit/public-mutants.json` 中为该目标记录变异体名称。此文件位于 `tests/audit/` 下，因此拉取请求需要所有者审阅。

[证明变异](proof-mutants.zh.md)解释每种判定。

## 4. 添加差分测试

差分测试在相同输入上运行真实 C 与翻译。它是忠实性的证据，不是证明。在 `tests/gen/<name>.py` 中为该函数添加输入，
必要时在 `tests/c/<name>.c` 和 `tests/lean/Driver/<Name>.lean` 中添加分派分支。
[tests/README.md](../../tests/README.md#add-a-c-file-for-example-crc32c) 给出五个步骤。
测试框架以 x86_64 Linux 为目标；在 macOS 上 C 驱动程序无法编译（`adler32_combine64` 未声明）。
请在 Linux 上运行，或依赖 CI 作业 `diff_core`（CI）：

```sh
ONLY=gz ZLIB_SRC=$PWD/zlib bash tests/run.sh
SAN=1 ONLY=gz ZLIB_SRC=$PWD/zlib bash tests/run.sh
```

## 5. 登记定理

只登记你已证明的定理。把它的完整名称逐行加入 `tests/audit/theorems.txt`。登记会修改 `tests/audit/`，
因此拉取请求需要所有者审阅；请在描述中说明。

## 6. 重新生成锁文件

锁文件绝不手工编辑。用审计器重新生成，然后阅读差异：

```sh
python3 scripts/verification.py regenerate
git diff tests/audit/
```

`regenerate` 会构建库、用 `leanchecker` 在全新内核中重放每个声明、运行声明审计，然后才写入锁文件。
全新重放需要超过 6 GiB 内存；它在本地机器上被终止，因此这一步需要更大的机器。

在拉取请求中解释锁文件的每一处变化：每条新登记定理的陈述记录，以及每个被修改的受保护文件的新哈希。
`tests/audit/policy.lock` 或 `tests/audit/trusted.lock` 的任何变化还需要所有者移动已批准的准入基线（见下文 `audit_mutants`）。

## 7. 刷新进度

本地运行（使用 CI 构建时约需 4.5 GiB）：

```sh
python3 scripts/proof-progress.py
python3 scripts/proof-progress.py --check
```

第一条命令重写 `docs/progress.md` 的生成区块。第二条是 CI 运行的检查。保持 `docs/progress.zh.md` 同步：
复制新的链接修订和输入指纹，并把其 `source-sha256` 行更新为 `docs/progress.md` 的 SHA-256。

## 8. 打开拉取请求

保持小规模：每个拉取请求一个目标族。只有当四个必需状态在指名的提交上全部为绿色时，结果才算已证明。

## CI 作业与本地命令

| 必需状态 | CI 作业 | 本地命令 | 是否已在本地检查 |
| --- | --- | --- | --- |
| `build` | `build` | `lake build ZlibF zlibf-audit zlibf-span zlibf-proof-replay` | `ZlibF` 部分：是，使用 CI 构建。该作业还拒绝禁用构造，并检查 `patches/*.patch` 能应用到 `zlib/`。 |
| `no-sorry` | `no-sorry` | `scripts/check-sorry.sh` | 是。 |
| `audit` | `audit_core` | `python3 scripts/verification.py specs`、`tests/verification/` 中的测试，然后 `python3 scripts/proof-progress.py --check` | `--check` 和 `python3 scripts/verification.py coverage`：是。`specs` 运行全新重放：需要超过 6 GiB。 |
| `audit` | `audit_selftest` | `bash tests/audit/selftest.sh` | 否（CI）。每个植入的作弊都必须被拒绝。 |
| `audit` | `audit_mutants` | `python3 scripts/verification.py mutants --baseline COMMIT --scoped-approved-commit COMMIT` | 否（CI）。`COMMIT` 是仓库变量 `ZLIBF_SCOPED_ADMISSION_APPROVED_COMMIT`。只要 `policy.lock` 或 `trusted.lock` 与该提交不同，分片 0 就会失败；只有所有者能移动它。 |
| `difftest` | `diff_core` | `ZLIB_SRC=$PWD/zlib bash tests/run.sh`，再加 `SAN=1` 运行一次 | 否：仅限 Linux。第二次运行用 ASan 和 UBSan 构建 C 侧。 |
| `difftest` | `diff_harness` | `ZLIB_SRC=$PWD/zlib bash tests/selftest.sh` | 否：仅限 Linux。每个测试框架变异都必须被检测到。 |

`python3 scripts/verification.py check` 组合了构建、全新重放、声明审计和锁文件检查。与 `specs` 和 `regenerate` 一样，
它的全新重放需要超过 6 GiB。
