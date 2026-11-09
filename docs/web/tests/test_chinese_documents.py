"""Missing or outdated Chinese prose must stop publication."""
from hashlib import sha256
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
import reference


class ChineseDocuments(unittest.TestCase):
    def setUp(self):
        self.directory=tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.repo=Path(self.directory.name)
        self.site=self.repo/'docs/web'
        self.source=self.repo/'docs/example.md'
        self.source.parent.mkdir()
        self.source.write_text('# Example\nAn English document.\n')
        self.target=self.site/'translations/example.zh.md'
        self.target.parent.mkdir(parents=True)
        self.enterContext(patch.object(reference,'REPO',self.repo))
        self.enterContext(patch.object(reference,'SITE',self.site))

    def translate(self):
        self.target.write_text('<!-- source-sha256: '+sha256(self.source.read_bytes()).hexdigest()+' -->\n# 示例\n完整的中文正文。\n')

    def test_missing_translation_is_rejected_even_with_a_native_file(self):
        self.source.with_suffix('.zh.md').write_text('# 旧版中文\n')
        with self.assertRaisesRegex(ValueError,'Missing Chinese'):
            reference.translated(self.source)

    def test_source_change_is_rejected_instead_of_publishing_english(self):
        self.translate()
        self.source.write_text(self.source.read_text()+'New requirements.\n')
        with self.assertRaisesRegex(ValueError,'needs review'):
            reference.translated(self.source)

    def test_missing_source_stamp_is_rejected(self):
        self.target.write_text('# 示例\n没有审阅来源标记。\n')
        with self.assertRaisesRegex(ValueError,'needs review'):
            reference.translated(self.source)

    def test_current_translation_is_used(self):
        self.translate()
        text,available=reference.translated(self.source)
        self.assertTrue(available)
        self.assertIn('完整的中文正文',text)
        self.assertNotIn('An English document',text)

    def test_repository_readme_requires_its_own_translation(self):
        source=self.repo/'README.md'
        source.write_text('# Project\n')
        with self.assertRaisesRegex(ValueError,'repository/README.zh.md'):
            reference.translated(source)

    def test_status_edit_leaves_source_code_untouched(self):
        text='This step is **to confirm**.\n```c\n/* to confirm */\n```\n'
        result=reference.direct_status(text)
        self.assertIn('**unfinished**',result)
        self.assertIn('/* to confirm */',result)


if __name__=='__main__':unittest.main()
