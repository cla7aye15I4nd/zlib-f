# New input after FINISH and the completion target

This is evidence of a suspected specification-domain error. It is not a
zlib bug report or a kernel-checked counterexample to the current target.
Current status and remaining work are maintained in [overview](../overview.md).

## Contract and target

The pinned source is `757f0527154291bcf6bfbd6396ecde6bedd2db95`.
Its `zlib.h` FINISH paragraph requires retries after an OK or BUF_ERROR
return to supply more output space but no more input data.

`Spec/Public/Sequences.lean` defines DeflateCompletes using actual
DeflateDataTrace, unfinished and finish-only bound flags, DGood, admitted
buffers, a readable input slice and sufficient output under the bound.
It has no condition excluding fresh input in FINISH_STATE.
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
is locally kernel checked. It derives from any actual scoped default data
history that FINISH_STATE with nonempty readable input and positive raw
output cannot return STREAM_END. It assumes neither an execution contract
nor a strengthened history rule. This statement alone does not establish
that a concrete finishing history satisfies every completion premise.

The exact reachable Lean counterexample, including all public completion
premises, remains **to confirm**. No existing statement, translation or
history domain has been changed. A contract correction requires human
review under the repository rules. One candidate direction is an explicit
finishing-input protocol condition, justified against the header; deciding
where to encode that condition is separate from proving the existing
encoding and safety results.
