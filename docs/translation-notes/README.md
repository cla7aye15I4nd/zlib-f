# Translation and source-review notes

These records explain how the selected C source is represented and where its
statement order, integer rules or memory behavior need particular care. They
include source interpretations and finite execution observations. They are not
function contracts or a record of current proof progress.

| Record | Scope |
| --- | --- |
| [Compressor, trees and checksums](deflate-side.md) | `deflate`, Huffman construction and output, CRC, allocation utilities and buffer compression wrappers. |
| [Inflate](inflate-side.md) | Decoder state, tables, fast decoding, callbacks and checksum translation. |
| [Gzip source decisions](gz-side.md) | Configuration, representation and cross-file decisions in the file API. |
| [Gzip file-by-file review](gz-files.md) | Source behavior and fidelity details grouped by gzip implementation file. |

Read [the API manuals](../api/README.md) for caller-visible contracts,
[the design](../design/README.md) for shared representation rules and
[the proof guides](../proof/README.md) for mathematical arguments. A reading of
the C that the proof must establish is marked **to confirm**. Differential tests
are evidence of fidelity, not proof; [checking](../checking/README.md) explains
the acceptance boundary. [Overview](../overview.md) is the single place that
lists remaining work.
