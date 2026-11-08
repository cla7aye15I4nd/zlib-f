---
date: 2026-11-07
tags: [compression, verification, lean]
title: "zlib × Lean"
description: "Follow the data through the algorithm, then the implementation through the proof."
---

# zlib × Lean

I put zlib's algorithms, interfaces, and verification into a standalone interactive guide. It has two reading routes:

- <a href="/zlib-f/algorithms/index.html" data-no-spa>Algorithms and interfaces</a>: start with repeated bytes, follow matching, codes, and blocks, then read about decoding and streaming calls. Complete API contracts remain available throughout.
- <a href="/zlib-f/verification/index.html" data-no-spa>Algorithm detail and formal verification</a>: open the implementation, follow its data structures, execution, and optimizations, then understand how the proof connects those steps.

The detailed routes cover windows and matching, Huffman construction, block output, decoding, streaming state, resource lifetime, checksums, and buffer, callback, and gzip-file interfaces. Each topic explains its algorithms and optimizations before using worked executions to develop the proof argument. Chapters link their background, next step, exact contracts, and source.

<a href="/zlib-f/" data-no-spa>Open the reading map →</a>

The article, interactions, and reference documentation live in the zlib-f project site. This blog provides the entrance.
