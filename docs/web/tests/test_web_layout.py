"""The reference builder must not ingest its own code, output or article copies."""
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
import reference


class ConsolidatedDocumentation(unittest.TestCase):
    def test_reference_inventory_excludes_web_output_and_main_articles(self):
        with tempfile.TemporaryDirectory() as folder:
            root=Path(folder)
            for name in ['docs/overview.md','docs/spec/safety.md',
                         'docs/spec/safety.zh.md','docs/articles/foundations.en.md',
                         'docs/web/README.md','docs/web/dist/reference/copied.md']:
                target=root/name
                target.parent.mkdir(parents=True,exist_ok=True)
                target.write_text('# Document\n')
            with patch.object(reference,'REPO',root):
                self.assertEqual([str(p.relative_to(root)) for p in reference.documents()],
                                 ['docs/overview.md','docs/spec/safety.md'])

    def test_article_links_keep_the_primary_routes_in_both_languages(self):
        routes={'foundations':'read/codec','optimizations':'read/optimizations',
                'features':'read/features'}
        for key,route in routes.items():
            for lang in ['en','zh']:
                source=reference.REPO/'docs/articles'/f'{key}.{lang}.md'
                expected=reference.OUT/(route+('.zh.html' if lang=='zh' else '.html'))
                self.assertEqual(reference.doc_path(source,lang),expected)


if __name__=='__main__':unittest.main()
