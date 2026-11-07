# Bilingual reading site

English Markdown is the canonical document; the adjacent `.zh.md` file is its
Chinese translation. The language selector keeps the corresponding page.
Illustrated chapters own teaching examples. Specifications own exact conditions.
Implementation references own the detailed C arguments. Progress alone owns
current evidence and remaining work. Earlier reviews stay in the review group.

When a page or figure changes:

1. Update and review its English/Chinese pair. Preserve code, contracts and numbers.
2. Run `python website/hooks.py --refresh-sources` with the website dependencies.
3. Review `website/locales/sources.json`, then run `python -m mkdocs build --strict`.

The manifest records the English revisions that the translations were reviewed
against. A missing pair or changed English revision fails the site build. The
pair check also preserves heading structure, code examples, references and SVG
geometry. It cannot judge translation meaning; prose review is still required.
Heading IDs are aligned during the build so shared section links work in both
languages. Normal links and asset names omit the locale suffix.

Search uses build-time Chinese segmentation through jieba and a shared browser
index. Keep the explicit browser search language and disabled i18n search
reconfiguration together; enabling its separate `zh` tokenizer bypasses this
segmentation path. Both language versions retain their distinct page URLs.

`docs/progress.md` is read once. Its Chinese page is generated with
`locales/progress-zh.json`; counts, proof links, nodes and edges are not copied to
a second page. Numeric placeholders reuse the canonical values. Each rule must
still match, and the uncovered prose fingerprint rejects new untranslated text.
When progress wording changes, update the translation rules before refreshing
the source manifest. A coverage-fingerprint change needs the same prose review;
it is not an instruction to accept unlocalized paragraphs.

The build stages files in a temporary directory. It creates the web homepage
from the overview and adds shared website assets there, without generated copies
in the maintained documents. It does not modify Lean or the proof audit.
