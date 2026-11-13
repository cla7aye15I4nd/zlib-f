<!-- source-sha256: 88adc4d11e045aff6ba799abcd40ff7a60622fca3de44e13f7eb3bb73a6ff098 -->
# 参与贡献

本页列出修改证明、翻译或文档的步骤。所有命令都在仓库根目录运行。规则见 `AGENTS.md`。

标为**站点**的命令在写本页时实际运行过。Lean 与审计命令抄自 CI 工作流 `.github/workflows/lean.yml` 及其调用的脚本，本页写作时没有重新运行。

## 两个层级

- **已检查。** 定理在 `dev` 上，且该提交上快速关卡为绿。
- **已验收。** 定理还在 `tests/audit/theorems.txt` 中，且验收套件在某个具名提交上全部通过。只有已验收的结论才是最终结论。

## 步骤

1. 取得源码，包括上游子模块。

   ```bash
   git clone --recurse-submodules <repository-url>
   git submodule update --init zlib
   ```

2. 从 `dev` 开分支。小步提交并推送到 `dev`，或在快速关卡变绿后把拉取请求合入 `dev`。不需要评审。

3. 构建库。最多四个并行任务，内存上限 16 GB。`crc32.c` 与 `inftrees.c` 的证明各需要 8 到 9 GB。

   ```bash
   lake build ZlibF zlibf-audit zlibf-span zlibf-proof-replay
   ```

4. 检查被禁止的构造和 `sorry`。

   ```bash
   scripts/check-sorry.sh
   grep -rnE '\b(native_decide|bv_decide|implemented_by)\b|^\s*axiom\b' ZlibF.lean ZlibF
   ```

   第一条是关卡。第二条是 `lean.yml` 中 grep 的简写，完整版本还拒绝 `partial`、`unsafe`、`opaque` 和 `extern`。

5. 检查每个补丁都能应用到固定版本的上游源码（抄自 `lean.yml` 的步骤）。

   ```bash
   cp -r zlib /tmp/zlib-verified && rm -rf /tmp/zlib-verified/.git
   for p in patches/*.patch; do (cd /tmp/zlib-verified && git apply "$OLDPWD/$p"); done
   ```

6. 如果改了 `docs/`，构建并检查网站（**站点**）。需要 Python 3.12 或更新版本。

   ```bash
   python3 -m pip install -r docs/web/requirements.txt
   python3 docs/web/build.py
   python3 docs/web/check.py
   node --test docs/web/tests/*.test.mjs
   ```

7. 每个英文文档旁边都有中文副本 `*.zh.md`，其第一行记录英文文件的 `source-sha256`。修改英文文件后，更新中文并写入新哈希。

   ```bash
   shasum -a 256 docs/glossary.md
   ```

   过期的副本不会使构建失败，中文页面会显示英文原文更新的提示。

8. 推送到 `dev`。快速关卡（`build`、`no-sorry`）在每次推送和拉取请求时运行，它是合并的唯一关卡。推送若破坏了它，先修复。

## 到达里程碑时

验收工作按批进行，不是每次改动都做。

1. 把新定理登记到 `tests/audit/theorems.txt`，每行一个完整限定名。
2. 为每个新证明的公共函数添加证明变异体。变异后的翻译必须无法通过检查，且错误出在该函数的证明中。

   ```bash
   bash tests/audit/proofmut.sh tests/audit/proofmut/adler32.tsv
   ```

3. 重新生成进度视图，即 `docs/progress.md` 中 `proof-progress` 标记之间的块。

   ```bash
   python3 scripts/proof-progress.py
   python3 scripts/proof-progress.py --check
   ```

4. 运行验收套件。用手动触发启动 `lean` 工作流，或在本地运行差分测试。

   ```bash
   ZLIB_SRC=$PWD/zlib bash tests/run.sh
   SAN=1 ZLIB_SRC=$PWD/zlib bash tests/run.sh
   ```

5. 报告某结论“已验收”时，写明套件通过的提交。之后 `main` 接收 `dev`。

没有运行过的检查，一律不报告为通过。
