# Input configurations and coverage colours

The build stays fixed: default x86_64 Linux, LP64, static library and default
allocator. The ranges below concern API input parameters. They do not introduce
new formal contracts or change the existing targets.

For each target family, default inputs are contained in common inputs, which
are contained in all supported inputs. The containment is strict for the two
stream engines. A particular entry can ignore or fix some dimensions; its
projected ranges then coincide. Do not invent additional work for that entry.

| Colour | Complete checked coverage required |
| --- | --- |
| Gray | Default inputs have not yet been proved completely. Internal lemmas may exist. |
| Blue | Default inputs are proved; common inputs are not yet proved completely. |
| Yellow | Common inputs are proved; all supported inputs are not yet proved completely. |
| Green | Every input admitted by the exact target statement is covered. |

These are cumulative ranges, not percentages of work. A proof about a few
examples does not cover a configuration. Each range quantifies over the data,
buffers, heap contents, failures and histories specified by its contract.
A red border records an obstacle. Registration and named-commit CI acceptance
are stated separately from coverage.

## Deflate inputs

All three ranges use `method = Z_DEFLATED = 8`.

| Parameter | Default | Common | All supported |
| --- | --- | --- | --- |
| `level` | `-1`, normalized to 6 | `-1` and 0 through 9 | `-1` and 0 through 9 |
| `memLevel` | 8 | 8 | 1 through 9 |
| `windowBits` | 15 | -15, 15, 31 | -15 through -9; 8 through 15; 25 through 31 |
| `strategy` | 0 | 0 | 0 through 4 |
| Wrapper | zlib | raw, zlib, gzip | raw, zlib, gzip |

Every combination in a column is included. Common inputs retain a 32 KiB
window, default memory level and default strategy. The signed window argument
selects raw at -15, zlib at 15 and gzip at 31. In the full range, zlib's 8 is
normalized to 9; raw -8 and gzip 24 are rejected by the pinned source.

The five strategies are default (0), filtered (1), Huffman-only (2), RLE (3)
and fixed-code (4). Memory level changes the hash dimensions and symbol/pending
storage. Small memory levels therefore affect the output-overlap argument.

### Engine and helper ranges

| Declaration family | Relevant range and execution distinction |
| --- | --- |
| Default initialization | `deflateInit_` fixes method, window, memory level and strategy, but leaves level arbitrary. Its exact theorem is independent of the universal Init2 theorem. |
| General initialization | `deflateInit2_` exposes the full parameter tuple. Its default/common instances need their own complete execution contracts before they can be coloured separately. |
| Strategy dispatch | Level 0 selects stored; levels 1 through 3 select fast; levels 4 through 9 select slow. Huffman-only and RLE override the ordinary selection for nonzero levels. |
| Match search | Within one engine, table-selected chain/lazy/nice bounds can potentially be handled parametrically. A proof must establish the actual bounds for every included table row. |
| Refill and sliding | Window and hash dimensions determine array bounds, ring positions and sliding. A fixed-window lemma is not automatically a full-window theorem. |
| Trees and block output | Symbol capacity, pending storage and unread-symbol position are linked to memory level. A tree or single-symbol lemma does not establish the complete overlap bound. |

Those rows partition actual obligations; they do not certify completion.
The [component guide](proof/deflate.md) explains the invariants, and
[overview](overview.md) records current evidence and remaining work.

## Inflate inputs

Inflate has no compression-level, memory-level or strategy argument. Its
input grammar already includes all stored, fixed and dynamic blocks.

| Range | `windowBits` |
| --- | --- |
| Default | 15 |
| Common | -15, 15, 31, 47 |
| All supported | -15 through -8; 0; 8 through 15; 16; 24 through 31; 32; 40 through 47 |

Common inputs select a 32 KiB raw, zlib, gzip or automatically detected stream.
Zero window-bit forms select the size from the header, with the pinned gzip
handling retained. Smaller windows affect distance checking and completeness;
accepting every valid format stream needs the target's window conditions.

### Fast and slow execution

Fast/slow dispatch is a separate partition from these input configurations.
The actual fast call requires at least six available input bytes, at least 258
available output bytes and fewer than eight held bits. A default-configured
stream can take either path as the caller changes buffers. Default coverage
therefore needs both paths and their transitions.

| Declaration family | Required connection |
| --- | --- |
| Initialization and reset | Establish the representation and mode-guarded clauses for the selected window/wrapper. |
| Table construction | Cover stored, fixed and dynamic blocks under default input configuration as well as the wider ranges. |
| Fast decoding | Derive the real fast-call premises from the dispatch state; retain its bit/input/output and memory effects. |
| Slow decoding | Compose literal, length, distance and match steps on the actual returned states. |
| Dispatch and exit | Combine both paths, waiting/error exits, window updates and counter writeback. |

See the [component guide](proof/inflate.md). A checked path lemma remains
conditional on its entry invariant. It cannot grant a complete stream colour.

## Entry inputs

For checksums, queries, buffer utilities, callbacks, gzip files and other
internal targets, read the exact statement's arguments and preconditions.
Stream parameter dimensions apply only where those arguments or the represented
state actually depend on them. A closed exact target proof grants green for
that statement's domain, including its explicit internal premises. It does
not grant the caller's target or remove those premises.

The graph currently discovers exact complete-goal proofs. Default/common
colours are reserved for reviewed scoped contracts with exact checked proofs.
The range table alone never supplies those contracts or raises coverage.
The evidence index keeps registration, local proofs and unproved targets apart.

All applicable error, allocation-failure and cleanup requirements remain.
Full public entry targets also retain their specified invalid-parameter refusals.
Changing a range in prose cannot shrink a public theorem or discharge a goal.
