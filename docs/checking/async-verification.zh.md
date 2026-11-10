<!-- source-sha256: e3d09ff02eb5fd6efcc4ebb8e35a381c6cc4415162107f0f67f237e3cb45f0d6 -->

# 异步验证

证明作者提交小批次后可以继续独立工作。另一个进程检查不可变的提交。
队列不改变证明要求，也不授予最终验收。仍须在指定提交上完成所需 CI。

## 启动工作进程

从仓库根目录，在单独的持久进程中运行：

```sh
python3 scripts/verification-queue.py worker --watch-ref HEAD
```

工作进程监视已提交引用，不读取正在编辑的文件。每个新提交进入 `build`
和 `no-sorry` 队列。同一工作进程一次处理一个任务，以限制内存争用。
进程必须持续存活；没有进程管理器时，关闭终端会停止它。
不要对同一个队列目录启动第二个工作进程。

检查证明分支时，用完整引用替换 HEAD。切换分支会改变 HEAD 监视的对象。
默认队列目录为 `.lake/verification-queue`。

## 提交批次

也可以明确提交任务。这些命令记录任务后立即返回，不运行或等待检查：

```sh
python3 scripts/verification-queue.py submit HEAD
python3 scripts/verification-queue.py submit HEAD --stages build no-sorry audit mutants
python3 scripts/verification-queue.py status
```

仓库、提交和阶段集合相同的请求会去重。不同阶段集合产生不同任务。
在可审查的批次边界请求完整审计和变异检查，不要每完成一个引理就请求。
现有审计命令可能自行运行缓存构建；队列不会绕过检查，也不会重新生成锁。

每个任务将已提交源代码克隆到独立目录。zlib 使用该提交记录的精确子模块版本。
未提交源代码和现有构建缓存不会复制。本地缺少子模块对象时，任务失败，
不会尝试网络获取。保留的快照和日志供诊断使用，会占用磁盘。
只有不再需要证据时才清理已完成任务。快照复制对象，不与源仓库共享对象。
在快照创建完成前，源仓库及子模块必须仍然可用。

## 结果与诊断派发

每个完成的任务写入 `jobs/<key>/state.json`、各阶段日志和持久事件
`events/<key>.json`。一个阶段失败后，任务停止后续阶段；工作进程继续处理
其他排队任务。工作进程仍在运行并不表示失败的检查通过。

可以让可执行处理程序接收事件路径：

```sh
python3 scripts/verification-queue.py worker --watch-ref HEAD --on-result ./result-handler
```

随附处理程序为失败结果启动只读诊断会话：

```sh
python3 scripts/verification-queue.py worker --watch-ref HEAD --on-result "$PWD/scripts/verification-agent.py"
```

这要求 PATH 中存在已认证的 `codex` 可执行文件。启动收据只说明派发已开始，
不表示诊断完成。启动或执行失败后，可以显式诊断保存的事件：

```sh
python3 scripts/verification-agent.py --run EVENT_PATH
```

处理程序应检查事件记录的提交、快照和日志，避免修改作者的当前工作区。
队列本身不会启动模型会话；需要单独配置处理程序。
处理程序失败会写入 `notification.json`，不会覆盖验证结果。
重新对已保存事件调用处理程序即可重试失败通知。重试投递的消费者必须按任务键去重。

工作进程中断后，任务可能仍标记为 `running`。确认没有工作进程占用队列后，
显式重新排队：

```sh
python3 scripts/verification-queue.py retry JOB_KEY
```

先前尝试保留在任务的 `history` 目录中。修复环境问题后也可重试失败任务。
证明修复应使用新提交和新任务。重试不会改变候选提交。

审计阶段使用候选快照内的验证脚本。结果只是开发证据，不能替代独立批准的
CI 审计程序、锁审查或最终验收。队列不是不可信代码的沙箱。

## 队列检查

```sh
python3 tests/verification/test_verification_queue.py
python3 tests/verification/test_verification_agent.py
```

测试覆盖提交去重、未提交修改隔离、失败报告、事件投递、历史尝试保留，
以及只读诊断命令和成功结果不触发诊断。测试使用微型本地仓库，
不会执行 Lean 构建或启动真实诊断会话。
