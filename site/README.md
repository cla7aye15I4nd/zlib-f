# zlib × Lean

A bilingual implementation book with six continuous chapters:

1. One complete compression round trip.
2. Deflate input, matching, and strategy selection.
3. Deflate coding, block selection, and output.
4. Inflate bit input and table construction.
5. Inflate copies, suspension, and the fast path.
6. Calling protocols and resource lifetime.

Each chapter explains execution and optimization before its same-page correctness
argument. Local proof diagrams sit beside their derivations. The last chapter joins
those relations in one proof-structure graph. Current acceptance and evidence remain
in the separate progress reference.

One left-hand contents control owns chapter and section navigation. There are no
reading bars, right-hand chapter menus, footer navigation, or topic-portal pages.
Public APIs, exact Lean sources, and complete contracts remain available as reference.
Checksum algorithms and buffer/callback/file details form two substantial appendices.

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

- `content/book/`: the six paired English/Chinese chapters.
- `book.py`: chapter order, section inventory and published URL destinations.
- `reading.py`: chapter/appendix rendering and old-link redirects.
- `navigation.py` and `static/navigation.*`: the single searchable contents panel.
- `content/sample/`: retained appendix material and old section identifiers.
- `content/topics/` and `content/article.*.md`: old identifiers for compatible links.
- `codec_trace.py`, `content/codec-trace.json`, `static/codec-trace.js` and
  `static/examples/codec-trace.c`: reproducible configuration records and their display.
- `static/book.*`: typography and reading behavior.
- `static/select.*` and `static/select-model.mjs`: themed dropdowns and keyboard rules.
- `reference.py`: public contracts, precise targets, original documents and source views.
- `syntax.py` and `static/syntax.css`: code colors with unchanged text and line anchors.
- `translations/`: Chinese reference companions, checked against source hashes.
- `progress.py`, `progress_graph.py` and `static/progress.*`: the separate target graph.

Establish the task and actual control flow before introducing fields and constants.
Explain an optimization's prerequisites, reduced work and preserved relation.
Keep proof completion status in the progress record rather than repeating it in prose.
Source notes may be collapsed; implementation and proof reasoning remain in the chapter.
Keep the two languages complete, with matching anchors and identical code excerpts.

The renderer retains all 96 public API entries per language, including the separate
Windows entry. Missing or stale Chinese reference companions stop the build. The source
reader includes actual translations, specifications, runtime and proof modules.

The configuration fixture records 16 native example runs from the pinned C plus the
registered patch set. It uses a deterministic 192 KiB input and 4096-byte buffers.
Rebuild its C program against that selected source to reproduce the JSON; the program's
`--dump-input` output is independently checked by SHA-256. These runs are example evidence,
not a proof of all inputs or a claim about Linux execution. The proof's platform and
configuration premises are stated in the chapter arguments and exact reference targets.

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

`index` is the first chapter. The other five live under `read/`.
`appendix/checksums` and `appendix/interfaces` retain the additional algorithm and
interface detail. Every former chapter/topic/overview URL redirects to its substantive
replacement, with per-section destinations and language pairing checked during the build.

Animations of selected symbols illustrate local mechanisms. The C configuration panel
shows fixed-source run records. Both remain distinct from Lean execution and proof checking.
