# zlib × Lean

A standalone, bilingual guide and documentation site. It first explains zlib's algorithms,
then explains the verification argument. Complete public contracts and detailed proof guides
are available alongside the narrative. The eight scenes are teaching models.
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
- `build.py`: standalone page shell and language links.
- `reference.py`: complete original documents, public function pages, exact targets and source views.
- `content/proof-routes.json`: scoped reading routes into actual inflate and deflate proofs.
- `translations/`: complete Chinese translations of every API category and the core proof guides.
- `static/base.css` and `static/layout.css`: the reading layout.
- `static/zlib-*.js`: independent interactive scenes and their shared teaching models.
- `tests/`: executable checks of those models, not proofs of zlib.

Keep exactly two main parts. Preserve corresponding chapter IDs in both languages.
Keep the project overview as the single current proof-status and remaining-work page.
The reference build reads the existing documentation and public API manifest directly.
It preserves 95 default-build entries plus the separate Windows entry, with one page
per function in each language. Shared conditions and exact Lean targets are shown separately.
Source hashes distinguish reviewed translations from later source changes. Other reference
pages retain the original English, with that language explicitly labeled on the Chinese site.
The source reader includes the actual proof modules, mathematical lemmas, specifications,
runtime, and C translation. Source and import links stay inside the project site.
Working-copy changes are labeled separately from the named base commit. A source snapshot
is not a claim that its proofs passed the acceptance checks.

## Publication

The separate Pages workflow builds and checks this directory, then publishes
`dist/`. The repository's Pages publishing source must be GitHub Actions.
Pull requests build and check without publishing. Pushes to the default branch
that change this site trigger publication; manual workflow dispatch is also available.

This website task adds the dedicated Pages workflow. It does not change the proof
build, audit, final-verification, or differential-test workflows.

Before linking from the blog, confirm the Pages deployment succeeds at its public URL.
This file describes the deployment configuration, not a completed deployment.
