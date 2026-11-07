# Callback decoding: ownership and finite input

Source: `infback.c`. The caller owns the window and supplies input/output
callbacks. [The API](../api/inflate-back.md) states the public contract;
[overview](../overview.md) records progress. These arguments and source
readings do not certify the complete callback decoder.

## Callback domain and termination

The callback assumptions describe caller-supplied code. They are separate from forbidden
assumptions about library callees. A theorem that calls `inflate_fast` or `inflate_table` still
needs a theorem about that translated function.

| Condition in the migrated arguments | Boundary relative to the API |
| --- | --- |
| Default allocator or a null allocator field that init replaces | Custom allocator implementations are outside this model scope |
| Window represented by a byte block with room for `2^windowBits` bytes from its offset | The caller must supply the valid writable range |
| Callbacks allocate or free no heap blocks | Stronger than the documented lifetime requirement on returned input |
| Input callback alone writes its input blocks | A convenient ownership discipline, not a complete characterisation of every legal callback |
| Callback invariant `R` depends only on its owned blocks | Frames callback effects away from the decoder state |
| `InFinite` bounds input still deliverable | Needed for termination; the API does not promise that a callback eventually ends |

The measure `phi` combines held bits, bytes left and input still deliverable. An indefinitely
productive callback can prevent `inflateBack` from returning without causing C undefined
behaviour. A finite-input theorem must state that premise rather than claim unconditional
termination over every callback allowed by the public interface. All narrower theorem domains
must be explicit and recorded in [deviations](../deviations.md).


## Callback decoder

`inflateBackInit_` allocates a state without zeroing it. It writes only its window settings,
window pointer, history counters and `sane`. Fresh integers are arbitrary and fresh pointer
fields are null in the model. The latter is weaker than C. A proof must show each pointer was
written before it is read; absence of a runtime fault is insufficient. The mode, bit registers,
code lengths and table pointers used by `inflateBack` are initialized along its paths:
**to confirm** by temporal initialization reasoning.

The window is supplied and owned by the caller. `inflateBackEnd` frees only the state.
`ROOM` resets output space and writes `whave` before calling `out`. `PULL` calls `in` only
when the current input is exhausted; a zero result sets `next = NULL` and returns buffer error.
The final partial-window `out` call happens before testing whether `ret == Z_STREAM_END`.
It can therefore occur on an error path, including after an earlier callback refusal.
The final epilogue writes only `next_in` and `avail_in`, not the output registers.

Callbacks run on the shared heap. The implementation's `InCb` receives the current input
pointer and returns `(count, newPointer)`; it does not allocate the older proposal's real
cell for `&next`. A callback that retains that address and later writes through it is outside
this representation. `OutCb` receives the window pointer and length and returns an integer.

Callback obligations are caller premises, not assumed specifications of zlib callees.
They include valid readable input until the next `in` call, preservation of the active window
slice and stream state, and suitable framing of callback effects. Descriptor storage may share
the window allocation outside that slice. Additional restrictions must be explicit in
[deviations](../deviations.md). A concrete initialized example is needed for a top-level claim.

Returning callbacks alone do not imply termination. An input callback can supply infinitely
many empty non-final blocks. A terminating theorem needs a finite input bound or another
stated progress condition. Functional observations must include callback events and failures;
there is no unconditional promise that failed output is delivered exactly once.

## Installed tables and window copies

A table return classification does not establish bounded canonical links.
A fast theorem with separate output and history arrays does not cover output
inside the callback window. The actual caller must establish the installed-table
and copy premises on the returned heap. The historical missing-whave report
remains **to confirm**; ordinary-inflate examples do not settle this API.
