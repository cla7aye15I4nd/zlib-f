# Reviewed recursive execution helpers

The audit lists six generated execution helpers for total logical definitions.
Each entry is the listed name followed by `._unsafe_rec`.

| Logical definition | Decreasing argument |
| --- | --- |
| `Zlib.Trees.Math.nextCode` | Natural-number predecessor. |
| `Zlib.Trees.Math.reverseLowBits` | Natural-number predecessor. |
| `Zlib.Trees.Math.scanCount` | Natural-number predecessor. |
| `Zlib.Trees.Math.scanMax` | Natural-number predecessor. |
| `Zlib.Trees.Proofs.Math.blMaxIdx` | Natural-number predecessor. |
| `Zlib.Trees.Proofs.tallyCalls` | List tail. |

The logical definitions have checked `Nat.rec` or `List.rec` equations.
The actual generated types and branch bodies were checked independently.
The body comparison replaces only the helper's self-reference with its total
logical counterpart. The recursive arguments were also inspected directly.
The inspected environment has no safe declaration that refers to these helpers.
They are absent from the registered theorems' logical dependency closure.

Only these exact declarations are added to the existing execution-helper list.
Their full exported syntax is locked. This does not permit partial definitions
in project source or establish compiler or machine-code correctness.
Current acceptance status remains in [the overview](../overview.md).

## Reviewed Huffman and symbol helpers

The nineteen exact entries were independently reviewed and approved for
registration. They are generated execution helpers of total logical definitions.
Their types match the logical counterparts. After replacing only a helper's
self-reference by that logical definition, all forty-four constructor cases
match by definitional equality. Tree equality checks both tree constructors;
the Huffman witness checks fuel and empty, singleton and longer forests.
No safe declaration in the inspected import closure refers to these helpers.
The complete generated types and bodies are included in the audit export.

| Logical definitions | Decreasing argument |
| --- | --- |
| Tree weight, height, leaves, positive-weight and sibling predicates | Tree children. |
| Derived tree representation and equality | Tree children; equality also matches the other tree. |
| Fibonacci pairs, cumulative counts, rank sums, weighted sums and mass | Natural-number predecessor. |
| Deepest nonzero count, length search and overflow repair iteration | Natural-number predecessor. |
| Minimum extraction, represented symbol bytes and histogram counts | List tail. |
| Deterministic Huffman witness | Fuel predecessor. |

These are exact reviewed additions to the existing compiler-helper list.
They do not permit project source declarations marked partial or unsafe.
The existing declaration checks, axiom restrictions and target questions
remain in force. Registration uses generated locks and requires CI acceptance.
