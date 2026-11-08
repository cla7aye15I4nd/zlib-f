# zlib × Lean

A standalone bilingual reading map, algorithm overview, and documentation site.
Eight detailed routes cover matching, Huffman construction, output, decoding, streaming,
resource lifetime, checksums, and application interfaces. Each route opens its algorithms
and optimizations before developing the proof argument. A separate call map connects the sequence to complete public contracts.
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

Only Markdown is needed to build. The output is plain HTML, CSS, fonts, and
JavaScript modules. It has no server runtime, package install, or blog dependency.
The existing website's font files are reused to preserve its typography.
Reference diagrams load the vendored Mermaid Tiny renderer only when a diagram enters view.
Its MIT license is retained in `static/vendor/`.

## Edit

- `content/article.en.md` and `content/article.zh.md`: paired prose and stable anchors.
- `build.py`: build entry point.
- `reading.py`: reading map, chapter order, prerequisite and proof links.
- `content/sample/`: paired detailed chapters and the API call map.
- `static/book.css` and `static/book.js`: chapter navigation and reading layout.
- `reference.py`: complete original documents, public function pages, exact targets and source views.
- `content/proof-routes.json`: scoped reading routes into actual inflate and deflate proofs.
- `translations/`: complete Chinese translations of every API category and the core proof guides.
- `static/base.css` and `static/layout.css`: the reading layout.
- `static/zlib-*.js`: independent interactive scenes and their shared teaching models.
- `tests/`: executable checks of those models, not proofs of zlib.

Keep the two reading parts: algorithms and interfaces; algorithm detail and verification.
Within the detailed sequence, establish implementation details before explaining their proof.
Preserve chapter IDs and navigation in both languages. Link the existing project status record
rather than creating another proof-progress inventory.
The reference build reads the existing documentation and public API manifest directly.
It preserves 95 default-build entries plus the separate Windows entry, with one page
per function in each language. Shared conditions and exact Lean targets are shown separately.
The renderer uses the repository's Chinese companion documents when present.
Source hashes distinguish fallback translations from later source changes. Other reference
pages retain the original English, with that language explicitly labeled on the Chinese site.
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

The worked block fixes two literals and a length-6, distance-2 match. It is not a claim about
zlib's token selection. Its writer trace retains the selected C's strict 16-bit branch
condition. Interactive Adler and CRC traces connect byte/bit recurrences to batching
and table lookup. Tests decode the five emitted bytes with an independent raw DEFLATE decoder,
and check the bitstring at every intermediate boundary. This is example validation, not
a proof of the implementation.
