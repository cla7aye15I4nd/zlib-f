---
date: 2026-11-07
tags: [compression, verification, lean]
title: "zlib × Lean"
description: "Follow the data through the algorithm, then the implementation through the proof."
---

# zlib × Lean

I put zlib's algorithms, interfaces, and verification into a standalone interactive guide.

<a href="/zlib-f/algorithms/index.html" data-no-spa>Start with eight bytes →</a>

Follow matching, coding, blocks, and decoding through one round trip. Each mechanism opens into its implementation chapters: establish the task, unpack the algorithm, data structures, and optimizations, then explain the relations its proof must preserve. Checksums, resource lifetime, and interface choices join the same task where they are needed.

Use the <a href="/zlib-f/verification/index.html" data-no-spa>chapter directory</a> to find a particular mechanism. Chapters also link complete API contracts and source.

<a href="/zlib-f/" data-no-spa>Open the reading map →</a>

The article, interactions, and reference documentation live in the zlib-f project site. This blog provides the entrance.
