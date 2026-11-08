# zlib × Lean

A standalone bilingual reading map, algorithm overview, and documentation site.
Eight detailed routes cover matching, Huffman construction, output, decoding, streaming,
resource lifetime, checksums, and application interfaces. Each route opens its algorithms
and optimizations before developing the proof argument. A separate call map connects the sequence to complete public contracts.
Chapters introduce the task, inputs, outputs, and a concrete example before naming
implementation fields. Short C excerpts connect the example to the pinned source.
Proof chapters begin with the algorithm's promise and possible failure modes.
Interactive scenes are teaching models.
They do not execute the C translation or check Lean proofs.

## Site and blog boundary

The essay is a project site published by this repository's GitHub Pages workflow.
Its intended public base is `/zlib-f/` on the existing website domain.
English uses `index.html`; Chinese uses `index.zh.html`.
All local assets and language links are relative, so the project subpath works.
The language switch preserves the current chapter.

The blog contains only the two short entry posts in `integration/`.
It does not load this site's scripts, styles, or article body.
Do not copy the interactive application into the blog templates.
Do not add a separate custom-domain file for the project site.

## Build and preview

From this directory:

Use Python 3.12 or newer.

```sh
python3 -m pip install -r requirements.txt
python3 build.py
python3 check.py
node --test tests/*.test.mjs
python3 -m http.server --directory dist
```

Markdown and Pygments run at build time. The output is plain HTML, CSS, fonts, and
JavaScript modules. It has no server runtime, package install, or blog dependency.
The existing website's font files are reused to preserve its typography.
Reference diagrams load the vendored Mermaid Tiny renderer only when a diagram enters view.
Its MIT license is retained in `static/vendor/`.

## Edit

- `content/article.en.md` and `content/article.zh.md`: paired prose and stable anchors.
- `build.py`: build entry point.
- `reading.py`: reading map, chapter order, prerequisite and proof links.
- `navigation.py` and `static/navigation.*`: searchable global contents on every reading and reference page.
- `topology.py` and `static/topology.*`: bilingual component purposes and the interactive data-flow map.
- `content/sample/`: paired detailed chapters and the API call map.
- `static/book.css` and `static/book.js`: chapter navigation and reading layout.
- `reference.py`: complete original documents, public function pages, exact targets and source views.
- `syntax.py` and `static/syntax.css`: static syntax colors for examples and Lean source, preserving code text and line links.
- `content/proof-routes.json`: scoped reading routes into actual inflate and deflate proofs.
- `translations/`: reviewed Chinese companions for every reference document, public API category, and repository guide. Each records the English source hash.
- `progress.py`, `progress_graph.py`, and `static/progress.*`: directed component diagrams, selectable target neighborhoods, and searchable evidence from the authoritative progress document. Solid arrows show proof reuse; dashed arrows point from callee to caller.
- `static/base.css` and `static/layout.css`: the reading layout.
- `static/zlib-*.js`: independent interactive scenes and their shared teaching models.
- `static/examples/inflate-chunks.c`: a complete small-buffer decoding program.
- `tests/`: executable checks of those models, not proofs of zlib.

Keep the two reading parts: algorithms and interfaces; algorithm detail and verification.
Within the detailed sequence, establish implementation details before explaining their proof.
Preserve chapter IDs and navigation in both languages. Link the existing project status record
rather than creating another proof-progress inventory.
The reference build reads the existing documentation and public API manifest directly.
It preserves 95 default-build entries plus the separate Windows entry, with one page
per function in each language. Shared conditions and exact Lean targets are shown separately.
Every Chinese reference page requires a reviewed companion under `translations/`.
Missing translations and stale source hashes stop the build. When an English reference changes,
review its complete Chinese companion and update the recorded hash. Native Chinese documents
can supply the starting text; the website companion also supplies reading explanations.
Chinese guide pages select Chinese diagram assets, and reference links retain the selected language.
The source reader includes the actual proof modules, mathematical lemmas, specifications,
runtime, and C translation. Source and import links stay inside the project site.
Working-copy changes are labeled separately from the named base commit. A source snapshot
is not a claim that its proofs passed the acceptance checks.

## Publication

The Pages workflow builds and checks this directory, then publishes
`dist/`. The repository's Pages publishing source must be GitHub Actions.
Pull requests build and check without publishing. Pushes to the default branch
that change this site trigger publication; manual workflow dispatch is also available.

This website task replaces the earlier documentation publishing workflow.
The earlier MkDocs configuration writes to `build/legacy-docs` so that running it
cannot overwrite this site's source directory. It does not change the proof
build, audit, final-verification, or differential-test workflows.

Before linking from the blog, confirm the Pages deployment succeeds at its public URL.
This file describes the deployment configuration, not a completed deployment.

## Reading routes

The root page explains the organization. `algorithms/index` retains the existing algorithm
overview. `verification/index` introduces all eight routes. `routes.py` owns their order, titles,
prerequisites, and per-topic algorithm-to-proof sequence. Detailed pages use `chapters/`;
previously published `sample/` links redirect while preserving their section anchors.
The compression call map remains a side entrance. Each mechanism links to its proof
argument and exact contracts.

The root and detailed-route index show each component's job, inputs, and results before
introducing implementation variables. Solid arrows follow data representations; dashed
links show support from shared mechanisms. This teaching map is not a C call graph.
Readers can explore nodes by pointer, touch, or keyboard, or play the data-flow sequence.
Small screens start with a topic grid and can switch to a pannable topology.
Reduced-motion preferences disable moving paths. A fixed contents control opens all
chapters, their purposes, and API families from every reading or reference page.

The worked block fixes two literals and a length-6, distance-2 match. It is not a claim about
zlib's token selection. Its writer trace retains the selected C's strict 16-bit branch
condition. Interactive Adler and CRC traces connect byte/bit recurrences to batching
and table lookup. Tests decode the five emitted bytes with an independent raw DEFLATE decoder,
and check the bitstring at every intermediate boundary. This is example validation, not
a proof of the implementation.

The window illustration separates a bounded logical suffix from the compressor's physical
array moves. The streaming scene shows the actual selected output capacity, separately
from the collected eight-byte result. Its symbols are a teaching model; the adjacent C
program decodes the complete five-byte raw stream. A five-byte output buffer produces
ABABA with Z_OK, then BAB with Z_STREAM_END. The article inserts its call fragment from
the downloadable source using `<!-- example:inflate-chunks#call -->`.
