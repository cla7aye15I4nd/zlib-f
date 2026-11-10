# Asynchronous verification

The proof author commits a small proof batch and continues independent work.
A separate process checks that immutable commit. The queue does not change
proof requirements or grant final acceptance. CI on the named commit remains
required.

## Start the worker

Run from the repository root in a separate persistent process:

```sh
python3 scripts/verification-queue.py worker --watch-ref HEAD
```

The worker watches the committed ref, not files being edited. Each new commit
queues `build` and `no-sorry`. One worker processes one job at a time to limit
memory contention. This process runs concurrently with proof writing. It must
remain alive; closing its terminal without a process supervisor stops it.
Do not start a second copy against the same spool.

For a proof branch, use its full ref instead of HEAD. Switching branches changes
what HEAD watches. The default spool is `.lake/verification-queue`.

## Submit a batch

Explicit submission is also supported. This returns after recording the job;
it does not run or wait for any verification:

```sh
python3 scripts/verification-queue.py submit HEAD
python3 scripts/verification-queue.py submit HEAD --stages build no-sorry audit mutants
python3 scripts/verification-queue.py status
```

Requests with the same repository, commit and stage set deduplicate. Different
stage sets are separate jobs. Submit full audit and mutants at a review boundary,
not after each local lemma. The existing audit command may itself run a cached
build; the queue does not bypass its checks. It never regenerates locks.

Each job clones committed source into its own directory. The zlib checkout uses
the commit's exact gitlink. Uncommitted source and existing build caches are not
copied. A missing local submodule object produces a failed job rather than a
network fetch. Jobs retain their snapshots and logs for diagnosis. This consumes
disk space; remove completed job directories only after their evidence is no
longer needed. Snapshots copy objects instead of sharing them with the source repository.
The source repository and its submodule must remain available until snapshot
creation finishes.

## Results and agent dispatch

Every completed job writes `jobs/<key>/state.json`, per-stage logs and a durable
`events/<key>.json`. Failed stages stop the remaining stages for that job. The
worker continues with another queued job. A failed test is a failed result even
though the worker remains operational.

An optional executable receives the event path:

```sh
python3 scripts/verification-queue.py worker --watch-ref HEAD --on-result ./result-handler
```

The included diagnostic handler starts a read-only agent for failed results:

```sh
python3 scripts/verification-queue.py worker --watch-ref HEAD --on-result "$PWD/scripts/verification-agent.py"
```

This requires an authenticated `codex` executable on PATH. A launch receipt means
only that dispatch started, not that the diagnostic agent completed successfully.
After a failed launch or agent run, diagnose a saved event explicitly:

```sh
python3 scripts/verification-agent.py --run EVENT_PATH
```

The handler can notify or dispatch a verification agent. It should use the
recorded commit and snapshot, inspect the logs and avoid changing the proof
writer's current workspace. The queue itself does not wake an agent or invoke a
model. Dispatch requires a separately configured handler. Handler failures are
recorded in `notification.json`; they do not overwrite the test result. Retry a
failed notification by invoking the handler again with the saved event path.
Consumers must deduplicate events by job key if they retry delivery.

An interrupted worker can leave a job marked `running`. Once no worker owns the
spool, requeue that job explicitly:

```sh
python3 scripts/verification-queue.py retry JOB_KEY
```

This preserves the previous attempt under the job's `history` directory. It also
allows retrying a failed job after fixing an environmental problem. A proof fix
should instead be a new commit and a new job. No retry changes the candidate
commit.

The audit stage uses the verification script in the candidate snapshot. These
results are development evidence, not a substitute for an independently approved
CI auditor, lock review or final acceptance. The queue is not a sandbox for
untrusted code.

## Queue checks

```sh
python3 tests/verification/test_verification_queue.py
python3 tests/verification/test_verification_agent.py
```

The tests check commit deduplication, isolation from uncommitted edits, failure
reporting, event delivery and preservation of earlier attempts. They use tiny
local repositories and do not execute Lean builds. The diagnostic tests check
read-only invocation and success handling without starting a real session.
