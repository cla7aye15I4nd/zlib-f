The preceding [tree](/sample/huffman-tree.html) and [length](/sample/huffman-lengths.html) chapters have established the execution story: observed frequencies become queued subtrees; merges produce parent links; lengths are limited; canonical words replace frequencies; a second tree encodes the description. The proof has to connect those phases on their actual returned heaps.

The useful result is more precise than “Huffman coding works.” A symbol that was used must receive a positive, permitted length, its stored word must denote that symbol to an independent decoder, and the description must communicate those same lengths. Storage bounds and output costs must refer to these same arrays.

## The forest behind the queue {#forest}

Start with the scan rather than assuming a well-formed tree. It establishes which alphabet entries are live, zeros unused lengths and records initialized depths. The artificial-leaf loop changes the prepared set and cost counters. A representation must retain that history so an artificial frequency-one entry is not later counted as an extra input symbol.

During merging, interpret the active queue as the roots of a forest. Its subtrees have disjoint leaf identities, and their union is the prepared alphabet. Removing two distinct roots and adding a fresh parent preserves that union. The selected nodes must really come from the old queue; a merely in-bounds integer could name some unrelated internal node.

Two additional facts serve different purposes. Heap order explains why the chosen roots are minimum under the source's frequency/depth comparison. Parent and membership facts explain why a complete tree eventually exists. Bounds on array indices establish neither of those meanings alone. The proof of `pqdownheap` must therefore preserve the node permutation as it restores order, and the merge proof must carry the old forest through every actual store.

The local [`ws_build_tree_complete`](/reference/source/ZlibF/Proof/trees.c.build.complete.html#L160) composes the actual preparation, heap construction, length limiting and code-assignment paths. Its premises concern selected descriptor pointers, array capacities, static tables and related internal storage. It does not assume execution contracts for the helpers it calls. Those helpers have their own execution proofs, applied to the intermediate state produced by the previous step. Public reachability of this internal state and a whole compressor's result are separate connections.

## Retained order and machine bounds {#order}

After `t` merges of `K` leaves, the active heap has `K−t` entries. Two nodes per merge occupy its retained high-end region. This numeric account proves that the regions stay apart and that the next internal-node number fits its selected tree array. Leaf membership and distinctness are needed again when summing lengths: without them, a duplicated retained entry could count one leaf twice and omit another.

The retained order must also establish that a parent is visited before a child in the first length pass. Then reading `Len(parent)` uses the current assigned value, rather than an old `Dad` value that happened to occupy the union. Initialization of the depth cells matters earlier for the same reason. Reusing a field is safe only when the proof follows its changing interpretation.

Frequency sums and subtree depths additionally cross machine-width boundaries. A theorem about natural-number weights cannot silently reuse an unsigned sum if that sum could wrap. Likewise, a byte-sized depth needs a range argument before it can be treated as an unbounded height in a frequency/depth estimate. The [F7 discussion](/reference/docs/proof/trees.html#heap-and-node-bounds-f7) identifies those requirements. They explain why a proof of code validity and a stronger proof of a prefix-cost estimate can need different information about the same constructor.

## Repair as a conserved quantity {#repair}

The key to length repair is the full tree, not a general fact about arbitrary histograms. A full binary tree has leaf Kraft sum one. Consider an internal node at depth `L` with `a` leaves below it. Clamping its leaves to length `L` changes that subtree's contribution from `2^-L` to `a×2^-L`, an excess of `(a−1)×2^-L`. The full subtree has `2a−2` nodes strictly below its root. Each is counted by the source's overflow pass.

Summing these disjoint depth-L subtrees gives

```text
clamped_Kraft = 1 + (overflow / 2) × 2^-L
```

This explains both why overflow is even and why one repair removes two overflow units. Splitting a code at `b<L` preserves Kraft weight; deleting one length-L code removes exactly `2^-L`. The leaf count remains unchanged. In the teaching example, overflow 2 and `L=3` correspond to the excess `1/8`, and one round removes it.

The loop still needs actual safety and termination arguments. While overflow is positive, a shorter nonempty class must exist: otherwise all leaves would have length L and the positive excess would require more than `2^L` leaves, contrary to the descriptor's alphabet capacity. The final length class must have enough entries for its decrement, and the reverse assignment scan must encounter exactly the required leaves. These facts justify the source's searches and subtractions, rather than treating their success as a precondition.

The local length results connect this accounting back to array cells. [`GBDone.symbolic_lengths`](/reference/source/ZlibF/Proof/trees.c.build.format.html#L72) changes from retained-node positions to symbol-indexed lengths and counts. That reindexing relies on the forest's unique leaf identities. The all-alphabet length result also covers entries above `max_code`, whose zero lengths must come from the actual preparation and preservation steps.

## From stored words to decoding {#canonical}

`gen_codes` can perform its arithmetic even if the supplied histogram does not count the actual lengths. An exact execution description of that assignment would then describe the wrong data faithfully. Semantic correctness therefore needs the histogram/length relation from the preceding phase, together with the complete-code property obtained by repair.

Once those are connected, the start-word recurrence and symbol-order assignment agree with the independent format's canonical rule. Reversing exactly the positive length connects the low-bit-first stored integer to the high-bit-first canonical word. The lengths themselves and unrelated fields stay unchanged while code cells are overwritten.

The result has a useful symbol-level form: decoding this used symbol's actual stored bits followed by **any suffix** returns the symbol and that suffix unchanged. [`build_tree_decodable_initialized`](/reference/source/ZlibF/Proof/trees.c.build.format.html#L370) states such an actual constructor result under explicit internal premises: [`TreesRun0`](/reference/source/ZlibF/Proof/trees.c.inv.html#L272) fixes descriptor pointers and bit-buffer facts; [`DeflateState.WellFormed`](/reference/source/ZlibF/Runtime/Schema.html#L1398) fixes the embedded array sizes; static-table facts supply the descriptor data. These premises must hold at the actual constructor call. Merely citing `deflateInit` does not establish them there: the initialization result and preservation along intervening calls must supply that connection. The theorem concerns each constructed tree and its used symbols. It does not say a dynamic block has sent its header, chosen the correct records or completed a public stream.

## Description agreement and output budgets {#description}

The next connection spans `scan_tree`, the small tree and `send_tree`. The scan's frequency for each instruction must count the instructions that emission will actually use. Both executions can be related to one run state containing the previous length, next length, current count and threshold values. The sentinel must force the last run to finish, while never entering the 19-symbol alphabet as a value.

For symbol 16, the previously decoded length must exist and the extra value must denote three through six repeats. For 17 and 18, the extra fields must reconstruct their zero counts. Direct lengths and run expansions together must yield the original length sequence, in order and with the announced total. Code validity for the small tree and exact bit append then connect those instructions to the bytes sent.

The existing [`send_tree_emit`](/reference/source/ZlibF/Proof/trees.c.send-tree.html#L529) links actual emission to its run-based bit sequence. It explicitly requires readable lengths, fitted code data for used instructions and enough total bit room. That room is still a caller obligation. It must not be inferred merely from the fact that the description itself is well formed.

This is the handoff to [shared storage](/sample/storage.html#prefix) and the [output proof](/sample/proof.html#dynamic). A legal tree establishes unambiguous meaning; protecting unread symbols needs a bound on description bits and every emitted data prefix. That stronger estimate must use the actual frequencies, construction choices and repair effects, not just Kraft validity or a final block-size comparison. Full caller and budget connections remain **to confirm** where the component argument marks them. [Project progress](/reference/docs/progress.html) records accepted scope; [block selection](/sample/blocks.html) shows how these costs return to an actual encoding decision.
