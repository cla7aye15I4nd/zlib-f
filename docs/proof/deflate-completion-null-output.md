# NULL output and the completion target

The completion proposition before the output-pointer correction is false.
This is a specification-domain error, not a zlib bug. The earlier reviewed
no-new-input condition in FINISH_STATE did not exclude this case.
Current status and remaining work belong in [overview](../overview.md).

## Exact Lean refutation

The [archived Lean reproduction](deflate-completion-null-output.lean.txt)
proves both `¬ DeflateCompletes` and `¬ Goal.deflate_sequence` against
commit `3f816a0cad822cb564f6156b8f16ad2d98def9dc`. Its three imports and the
refuted target agree with the checked publication-budget extension at
`f6376b0f2bbc2184e9ec472197768eb0b1916d12`, where the reproduction was
compiled. Both declarations use only `propext`, `Classical.choice` and
`Quot.sound`. The reproduction constructs a real default-init history;
it assumes no callee execution contract or unreachable private state.

The caller has empty input, NULL output and an output count of 64. Actual
init establishes DGood and retains those public fields. The empty data
trace is unfinished and bound-eligible. StreamBuffers holds because its
CallerRange explicitly admits NULL, including error calls with nonzero
counts. ActiveHeader and the readable empty-input snapshot hold. The
FINISH input condition holds because avail_in is zero. The bound for empty
input is 13, at most 64. Thus every current completion premise holds.
The proved actual public refusal returns STREAM_ERROR, contradicting the
required STREAM_END.

The archived reproduction deliberately names the uncorrected target. It is
historical evidence and will no longer type-check against that target once
a new output-pointer premise is approved. It is not imported as a proof of
an implementation goal. To recheck, copy the text to a temporary Lean file
on the stated revision and compile it with the project environment.

## Pinned C reproduction

[The C reproduction](deflate-completion-null-output.c) performs ordinary
default init and the same empty-input FINISH call. Against pinned source
`757f0527154291bcf6bfbd6396ecde6bedd2db95`, built with address and
undefined-behaviour sanitizers, it exits zero and prints:

```text
init=0 bound=13 capacity=64 finish=-2 total_out=0
```

No sanitizer diagnostic was observed. The return is the source's explicit
NULL-output refusal. This run is evidence of C behaviour, not a proof of
translation fidelity. The Lean refutation supplies the formal model result.

## Minimal proposed correction

Add only `z.next_out ≠ .null` to DeflateCompletes, before the existing
FINISH-input condition. Leave StreamBuffers, all data-trace constructors,
sequence safety, runtime and translations unchanged. Safe error calls with
NULL output remain covered by safety and encoding observations. They do
not belong to a promise of successful completion.

This changes the completion proposition and therefore the meaning of its
conjunct in Goal.deflate_sequence. It requires explicit human authorization
and regenerated, reviewed audit locks. Human review separately authorized this exact additional premise and
regeneration of its audit locks. The premise is applied. The earlier
FINISH-input condition remains. Generated-lock review and the actual
completion proof are still required.

## Entry-refusal audit

The actual deflate entry guards were reviewed together against completion:

| Guard | Existing or proposed justification |
| --- | --- |
| Invalid stream or private state | DGood from the actual admitted history |
| Flush outside its range | The theorem calls the fixed Z_FINISH |
| NULL output | Missing; proposed non-NULL premise |
| NULL input with positive input count | Excluded by the readable Bytes snapshot |
| FINISH_STATE with a different flush | Impossible for the fixed Z_FINISH |
| Zero output capacity | Excluded by the existing positive-capacity premise |
| Duplicate non-FINISH refusal | Explicitly excludes Z_FINISH |
| New input after FINISH_STATE | Excluded by the already-approved input condition |

This is a source-level audit of refusal guards. It does not prove global
output adequacy, every configuration, or the corrected completion target.

## Generated lock comparison

Fresh regeneration passes on the corrected source: full build of 1008
jobs, fresh kernel replay and declaration audit of 27,864 declarations
and 400 listed theorems. Coverage remains 78 of 181 goals. The local
no-placeholder check also passes. These are local checks, not green CI.

Against the reviewed FINISH-input-condition parent `3f816a0`, all 7,991
semantic declaration names remain. Exactly the value fingerprint of
DeflateCompletes changes. Its type remains Prop. Registered theorem types,
registrations and compiler-helper exceptions are byte-identical. The
policy difference covers only Sequences.lean and the regenerated semantic
lock fingerprint. No lock was edited by hand. The direct fingerprint of
Goal.deflate_sequence remains unchanged because it refers to DeflateCompletes;
its completion conjunct intentionally has the new meaning. The reviewed
semantic change must not be described as preserving every target's meaning.

Independent baseline review and checks of the combined integration commit
remain required. No implementation completion theorem is newly proved.
