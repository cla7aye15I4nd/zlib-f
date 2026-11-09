# zlib × Lean

Three long bilingual articles explain zlib itself:

1. **A complete codec:** LZ77, Huffman, transmitted coding rules, framing and
   independent reconstruction.
2. **Implementation and optimization:** actual deflate/inflate, search, coding
   choices, storage, tables and copying. This is the central, deepest article.
3. **Added capabilities:** streaming, controls, dictionaries, wrappers, Adler-32,
   CRC-32, combinations and application interfaces.

Formal verification has a separate reading track. The three algorithm articles do
not introduce Lean, theorem inventories or formal invariants. Exact specifications,
proof explanations and the single progress record remain available as reference.
All 96 public API entries per language retain their complete contracts.

## Writing for the reader

Build an explanatory argument: task, technical difficulty, derived mechanism,
worked example, implementation and its tradeoffs. Introduce the purpose and abstract
object before its concrete name, struct, field or constant. A table or source link
does not substitute for an explanation. Apply this rule to every paragraph,
diagram, control label and code excerpt.

The basic codec must be complete before discussing optimization. The receiver's
codebook, token parsing and termination belong to that basic closure. Optional
wrapper identification, streaming and integrity checks add different capabilities.
Explain each new feature before any optimization of that feature. Distinguish a
format rule from a policy for choosing among the format's legal representations.

Start with a concrete repeated passage, introduce the copy instruction and its
meaning, and only then name distance, length and their stored representation.
Streaming records and buffer fields appear when the application needs partial calls.

Every animation answers an introduced question. Keep its current object, controls
and explanation together. Explain the observed result before continuing the text.
Support keyboard operation, reduced motion and a substantive static fallback.
Coding examples must identify their actual format and account for their complete
metadata, payload and ending. The teaching format must never be presented as DEFLATE.

Place citations in the sentences they support. No closing source catalogs,
duplicated navigation, small topic portals or back-and-forth reading ladders.
Keep one searchable contents control on the left. Both languages are complete,
with matching anchors and code. Read each article without opening references during
review: revise any step that requires guessing a new term or filling a logical gap.

## Site and blog boundary

This repository publishes a standalone GitHub Pages project under `/zlib-f/` on the
blog's domain. `index.html` is English; `index.zh.html` is Chinese. Assets and language
links are relative to that project subpath. Do not add a separate CNAME file.

The blog contains only the short bilingual entrance posts in `integration/`.
Keep the application, articles and interaction code in this repository. The gray
palette and existing font files preserve the blog's visual style.

## Sources

The website is the published documentation. Repository Markdown is its authoring
source, rather than a separate reader edition. Edit the English document and its
adjacent `.zh.md` companion once; the builder reads those exact files.


- `../articles/`: three paired articles; `book.py` owns order and old URL targets.
- `reading.py`: article rendering and redirects. `navigation.py` and
  `static/navigation.*` own the one global contents panel.
- `content/reading-aliases.json`: published paths and fragments used for redirects.
- `../spec/api/`: complete API contracts and calling rules.
- `static/minimal-codec.*`, `static/minimal-codec-model.mjs`: the first article's
  complete teaching format, packet-only decoder and editable worked example.
- `static/zlib-*-scene.*`: local mechanism diagrams and controls.
- `static/zlib-playground.*`, `static/zlib-playground-worker.js`,
  `static/examples/codec-playground.c`: actual C round trips for editable UTF-8 or
  hexadecimal inputs, with a 256 KiB bound and actual saved call records.
- `content/codec-playground-provenance.json`: source pin, ordered patches, source
  and header hashes, compiler flags and artifact hashes. Compile the listed files
  after applying those patches to reproduce `static/vendor/zlib-playground.*`.
  Keep the bundled license. The wasm32 example has its own build configuration.
- `codec_trace.py`, `content/codec-trace.json`, `static/examples/codec-trace.c`:
  fixed-source native run records. Insert explained comparisons with a
  `comparison:window`, `comparison:search` or `comparison:storage` HTML comment.
- `reference.py`, `syntax.py`: render canonical content and precise source views.
  Reviewed Chinese companions live beside their English content.
- `content/repository/`: Chinese versions of repository metadata that also appears
  on the site; there is one source per language.
- `progress.py`, `progress_graph.py`, `static/progress.*`: the separate proof inventory.
- `static/diagram-view.mjs`: natural diagram dimensions, scrolling and bounded zoom.

`index`, `read/optimizations` and `read/features` are the main reading routes.
Published chapter, topic and appendix links resolve to a corresponding article or
formal reference. Source files for proofs and accepted status are not edited as part
of article rewriting.

## Build and local preview

Use Python 3.12 or newer, from this directory:

```sh
python3 -m pip install -r requirements.txt
python3 build.py
python3 check.py
node --test tests/*.test.mjs
python3 -m http.server --directory dist
```

The output is static HTML, CSS, fonts, JavaScript and WebAssembly. Interactions have
no server runtime. Mermaid loads on demand using the vendored renderer and license.
The source code views keep their original code and line anchors. Missing or stale
Chinese reference companions stop the build.

## Publication

The Pages workflow builds and checks `dist/`. Pull requests check without publishing;
applicable default-branch pushes publish through GitHub Actions. Complete the local
reading review before publication when the user requests local iteration.
