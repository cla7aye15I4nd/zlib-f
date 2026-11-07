# Adler-32: bounded sums and modular refinement

Source: the pinned `zlib/adler32.c`. The corresponding module is
`ZlibF/Zlib/adler32.c.lean`.
The mathematical contract is `F-adler-incremental` in the
[format guide](../spec/format/README.md). The [API guide](../spec/api/README.md) specifies
null buffers, wrappers and combination operations.

This page explains the argument for `adler32_z`. It does not certify a registered
proof. Acceptance and current scope are recorded in [progress](../progress.md).

## What a byte step preserves

Write `B = 65521` and `NMAX = 5552`. Split the input accumulator into
`a = adler & 0xffff` and `s = (adler >> 16) & 0xffff`. The mathematical step for a
byte `b` is

```
α' = (α + b) mod B
σ' = (σ + α') mod B
```

The unreduced machine step is `a' = a + b; s' = s + a'`. If the machine sums have
not wrapped, `a ≡ α (mod B)` and `s ≡ σ (mod B)` imply the same congruences after
the step. Reduction modulo B then recovers the exact mathematical pair.

The proof therefore has two distinct parts: the machine traverses the right
bytes safely, and its sums refine the modular recurrence on the stated
start-value domain.

## Reads and termination

For a non-null buffer into a live byte object, require the whole requested range
`[off, off + len)` to be readable. After consuming `k` bytes, use the invariant
that the cursor is `off + k`, the remaining count is `len₀ - k`, and `k ≤ len₀`.
Each read occurs with `k < len₀`. Each pointer increment ends at or before the
one-past position.

| Branch | Bytes consumed | Measure |
| --- | --- | --- |
| `len == 1` | One byte | No loop |
| `len < 16` | One per byte-loop body | Remaining count before the test |
| Full batch | `347 × 16 = 5552` | Remaining batch count and unrolled-group count |
| Tail | Groups of 16, then single bytes | Remaining count |

A post-decrement test can wrap a local unsigned counter on its final failed
test. The proof must model that test exactly; the wrapped value is not a further
body iteration. The measures must establish the translated fuel bound as well
as mathematical termination.

The one-byte fast path precedes the null-buffer check. Initialization queries
require `buf == NULL` and `len == 0`; they return 1 without reading memory. Other
calls require a readable nonnull range. The function writes no caller memory and
allocates no blocks.

## Why batches do not wrap on the default build

There are at most 5552 byte steps between reductions. After `j` such steps,
starting from 16-bit components, a convenient bound is

```
a ≤ 65535 + 255 j
s ≤ 65535 + j (65535 + 255 × 5552)
```

For `j ≤ 5552`, this gives `a ≤ 1481295` and `s ≤ 8224215375`, below `2^64`.
The default LP64 `unsigned long` additions therefore agree with ordinary natural
arithmetic. This loose bound is specific to the 64-bit argument; another word
width needs a suitable bound for its own branch.

The 16-byte unrolling preserves the byte-step invariant sixteen times. Applying
it to each full batch and tail, then reducing, gives the result packed as
`a | (s << 16)`. The shift and packing also need their machine-width bounds.

## Exact start-value scope

A normal incremental checksum starts with reduced components. The public
function also accepts an integer accumulator, so a correctness statement must
say how noncanonical components are interpreted.

In the short branch, the low component satisfies
`a ≤ 65535 + 15 × 255 = 69360 < 2B`; one conditional subtraction reduces it.
The high component is reduced modulo B. In the one-byte branch both components
receive only one conditional subtraction. Reducing the high component this way
requires the incoming `s < B`, because the new low component is below B and the
sum is then below `2B`.

Thus the straightforward recurrence argument covers arbitrary accumulator words
when `len ≠ 1`, and the one-byte case when the incoming high component is below B.
It must also treat the null-buffer return separately. This is the scope of the
argument, not authorization to narrow a fixed public goal.

The distinction is observable. For `adler32_z(0xFFFFFFF0, "\0", 1)`, the masked
low component is 65520 and the high component is 65535. Their sum after the byte
step is 131055. One subtraction leaves 65534, and the function returns
`0xFFFEFFF0`. Full modular reduction would give a high component of 13. The call
is memory-safe; a specification that reduces every arbitrary start word gives a
different value. Keep that counterexample when reviewing the exact contract.

## Wrappers and combination

`adler32` inherits the byte algorithm after converting its length argument.
The `combine` functions require a separate arithmetic proof: expand the two
running sums for concatenation, include the initial-value correction and show
that the translated reductions compute the formula. Their signed-length
refusals and width conversions belong to their own API contracts. They do not
follow from memory safety of `adler32_z`.

Earlier work supplied a Lean argument for the byte algorithm. Reuse requires
checking its statement, machine widths, selected patch, execution relation and
preconditions against the present module. See [the method](method.md) for
non-vacuity and mutation requirements.
