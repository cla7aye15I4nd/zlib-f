# Safety of `uncompress*`

The goals are `Goal.uncompress2_z_safe`, `Goal.uncompress2_safe`, `Goal.uncompress_z_safe` and
`Goal.uncompress_safe` (`ZlibF/Spec/Public/Utilities.lean`). They are proved with no premise in
`ZlibF/Proof/public-uncompress-safe.lean`.

## What is proved

For every input the functional goals admit:

- the call runs without undefined behaviour and returns (`C.run … = .ok`);
- an argument error returns `Z_STREAM_ERROR` and changes nothing;
- otherwise the call writes at most `capacity` bytes into the output buffer and the length cells,
  and nothing else;
- every allocation is freed on every return path;
- the code is `Z_OK`, `Z_BUF_ERROR`, `Z_DATA_ERROR` or `Z_MEM_ERROR`, and `Z_MEM_ERROR` comes only
  after an allocation failed.

Nothing is said about the bytes written. That is the functional goal, which is not planned.

## Structure

```mermaid
flowchart TD
  init["start_state: inflateInit2_ and the bound stream"] --> loop
  loop["loop_run_safe: do ... while (err == Z_OK)"] --> call
  call["call_phase_safe: one inflate call (inflate_public)"] --> loop
  loop --> epi["epilogue: store the counts, inflateEnd, free the stream and the reserved byte"]
  epi --> z["uncompress2_z_with_safe"]
  z --> w2["counted2_of_z: uncompress2"]
  z --> w1["single_of_counted: uncompress_z, uncompress"]
```

The run is shared with the functional proof. `SafeState` and `SafeFinal` hold everything but the
format fact. The functional proof extends them with `NoOver` (no complete stream at the start of
the source has been read to its end). The wrappers are proved once for every data relation
(`CountedWith`, `SingleWith`). The safety goals use the relation `SafeRel`: the output fits the
capacity, the consumed input fits the source, and the code is documented.

## What the proof uses

- `inflate_public` (`Goal.inflate`) for each call of `inflate`.
- `reachable_invariant_kind` for the decoder of every reachable stream.

No `DecoderFacts` field is used, and no functional fact of `inflate`.

## Termination

The measure is the unread source plus the unfilled room:
`avail_in + len + avail_out + left`. The refills move bytes between the stream fields and the
remaining lengths, so they keep it. Each call that returns `Z_OK` consumes input or writes output
(the progress clause of `Goal.inflate`: `rc = Z_OK → used ≠ 0 ∨ out ≠ []`), so the measure falls.
At the start it is at most `sourceLen + destLen < 2^64`, below the loop fuel. The rule is
`cdoWhile_decreasing`.
