# New input after FINISH and the completion target

> **Historical record.** It describes the process when it was written: lock files, regenerated locks, an approved baseline and review of lock differences. Those mechanisms were removed later. There are no lock files now; see [anti-cheating](../anti-cheating.md). Read the evidence below as evidence about that snapshot only.

This records evidence for a reviewed completion caller-protocol correction.
It is not a zlib bug report or a kernel-checked counterexample.
Current status and remaining work are maintained in [overview](../overview.md).

## Contract and target

The pinned source is `757f0527154291bcf6bfbd6396ecde6bedd2db95`.
Its `zlib.h` FINISH paragraph requires retries after an OK or BUF_ERROR
return to supply more output space but no more input data.

The earlier `Spec/Public/Sequences.lean` defined DeflateCompletes using actual
DeflateDataTrace, unfinished and finish-only bound flags, DGood, admitted
buffers, a readable input slice and sufficient output under the bound.
It had no condition excluding fresh input in FINISH_STATE.
The trace's Rebuffer transition admits such a caller edit. The bound flag
only records whether all observed flush parameters equal FINISH.

Existing translated execution proofs already expose the finished-state
new-input refusal. The actual call may publish pending bytes before it
returns BUF_ERROR. This is compatible with the encoded-history theorem:
that theorem states exact encoding when STREAM_END is actually returned,
and does not assert completion for every such call.

## Concrete C execution

[The reproduction](deflate-completion-input.c) performs default init,
FINISH with empty input and three output bytes, then FINISH with one fresh
input byte and 64 output bytes. Against the pinned source, compiled with
address and undefined-behaviour sanitizers, the program exits zero and
prints:

```text
init=0 first_finish=0 status=666 FINISH_STATE=666 pending=1 observed_output=3 bound=14 next_capacity=64 next_finish=-5 remaining_input=1 total_input=0 total_output=4
```

The first call returns OK, enters FINISH_STATE and leaves one byte pending.
The bound for one input byte is 14, at most the previous three output bytes
plus the new capacity of 64. The second call publishes one pending byte,
then returns BUF_ERROR. It consumes none of the fresh input.
No sanitizer diagnostic was observed. This run is evidence of C behaviour,
not a proof of translation fidelity or a formal refutation of the target.

To reproduce, build the pinned source with the repository's
`tests/build-zlib.sh` into a fresh output directory, using
`-O1 -g -fsanitize=address,undefined -fno-sanitize-recover=undefined`.
Compile this reproduction with the same flags, the copied source directory
as its include directory, and its static `libz.a`. The exit status is zero
only when the stated finish-state, bound and refusal observations hold.

## Review boundary

The [necessary protocol lemma](../../ZlibF/Proof/deflate.c.engine.completion-protocol.lean)
is locally kernel checked. It derives from an actual scoped default data
history that FINISH_STATE with nonempty readable input and positive raw
output cannot return STREAM_END. It assumes neither an execution contract
nor a strengthened history rule. It does not by itself establish every
premise of a concrete finishing history.

Human review authorized the exact one-line completion premise
`s.status = FINISH_STATE → z.avail_in = 0`, together with regeneration of
the corresponding audit locks. This condition is now applied to
DeflateCompletes. It implements the header's retry obligation. Actual data
trace constructors, refused-call safety, translations and runtime are
unchanged. The semantic lock difference requires explicit review of this
authorized target-meaning change; regeneration itself is not approval.

The exact reachable Lean counterexample to the earlier target, including
all its completion premises, remains **to confirm**. Encoding correctness,
safe execution and the output-length budget are separate obligations.
The corrected completion theorem still needs its implementation proof.
