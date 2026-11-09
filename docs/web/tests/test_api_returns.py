"""Canonical return maps preserve source content and reject incomplete guides."""
from html.parser import HTMLParser
from pathlib import Path
import json
import re
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from api_returns import HEADERS, _blocks, enhance_contract, enhance_manual, parse_role, validate_sources
from markdown import Markdown


def source(name='inflate', lang='en', rows=2):
    zh = lang == 'zh'
    title = '返回值与后续调用' if zh else 'Return values and next calls'
    role = '**返回值类型。** `int` — 状态码' if zh else '**Return type.** `int` — status code'
    headers = '| ' + ' | '.join(HEADERS[lang]) + ' |'
    cases = '\n'.join('| `Z_OK`<br>**结果' + str(i) + '** | 条件 `n < 4` | 继续。 |' for i in range(rows))
    return f'''## {name}

```c
int {name}(void);
```

Purpose &amp; setup.

### {title} {{#api-{name.lower()}-returns}}

{role}

Overview with `exact_code`.

{headers}
| --- | --- | --- |
{cases}

- A source note.

### Calling conditions and effects {{#api-{name.lower()}-contract}}

**Domain.** Original domain.

**Pre.** Original precondition.

**Effects.** Original effects.

<details markdown="1" class="ar-return-exact" data-return-exact="{name}"><summary>Complete return conditions</summary>

**Post.** Exact `code` &amp; entities.

Continuation paragraph.

| field | value |
| --- | --- |
| saved | unchanged |

**Errors.** Exact errors.

</details>
'''


def render(text):
    return Markdown(extensions=['fenced_code', 'tables', 'attr_list', 'md_in_html']).convert(text)


class _Content(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=False)
        self.ids = []
        self.details = []

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if 'id' in attrs:
            self.ids.append(attrs['id'])
        if tag == 'details':
            self.details.append(attrs)


class ReturnGuideTests(unittest.TestCase):
    def test_role_is_read_from_both_canonical_languages(self):
        self.assertEqual(parse_role(source()), ('int', 'status code'))
        self.assertEqual(parse_role(source(lang='zh')), ('int', '状态码'))
        for raw in ('', source() + '\n**Return type.** `int` — another role'):
            with self.assertRaises(ValueError):
                parse_role(raw)

    def test_all_source_blocks_and_cells_survive_verbatim_once(self):
        body = render(source())
        enhanced = enhance_contract(body, 'inflate', 'en')
        for block in _blocks(body):
            if block.tag:
                self.assertEqual(enhanced.count(block.raw), 1, block.raw)
        self.assertIn('data-return-guide="inflate"', enhanced)
        self.assertIn('data-return-cases="2"', enhanced)
        self.assertNotIn('ar-return-single', enhanced)
        self.assertIn('&lt; 4', enhanced)
        before, after = _Content(), _Content()
        before.feed(body)
        after.feed(enhanced)
        self.assertEqual(before.ids, after.ids)
        self.assertEqual(before.details, after.details)
        self.assertNotIn('open', after.details[0])
        self.assertLess(enhanced.index('Original precondition'), enhanced.index('<details'))

    def test_root_parser_retains_comments_entities_void_and_multiline_tags(self):
        raw = '<!-- before -->\n<p id="a">A &amp; B<br>more<img src="x"></p>\n<table\n id="t"><tr><td><code>&lt;tag&gt;</code></td></tr></table>\n'
        self.assertEqual(''.join(block.raw for block in _blocks(raw)), raw)
        with self.assertRaises(ValueError):
            _blocks('<p><strong>broken</p>')

    def test_single_value_uses_one_value_card(self):
        enhanced = enhance_contract(render(source(rows=1)), 'inflate', 'en')
        self.assertIn('ar-return-single', enhanced)
        self.assertIn('data-return-cases="1"', enhanced)
        self.assertEqual(enhanced.count('<table>'), 2)  # Guide and exact source table.

    def test_chinese_headers_and_prose_are_preserved(self):
        body = render(source(lang='zh'))
        enhanced = enhance_contract(body, 'inflate', 'zh')
        self.assertIn('返回值与后续调用', enhanced)
        for header in HEADERS['zh']:
            self.assertEqual(enhanced.count(header + '</th>'), 1)
        self.assertIn('状态码', enhanced)
        self.assertNotIn('Next step', enhanced)

    def test_manual_only_wraps_function_return_sections(self):
        body = render('# Manual\n\nShared rules.\n\n## Common conditions\n\nKeep this.\n\n' + source() + '\n' + source('inflateEnd', rows=1))
        enhanced = enhance_manual(body, 'en')
        self.assertEqual(enhanced.count('data-return-guide='), 2)
        self.assertEqual(enhanced.count('Shared rules.'), 1)
        self.assertEqual(enhanced.count('Keep this.'), 1)
        self.assertIn('<h3 id="api-inflate-returns">', enhanced)
        self.assertIn('<h2>inflateEnd</h2>', enhanced)

    def test_missing_duplicate_or_wrong_header_is_rejected(self):
        body = render(source())
        for bad in (body.replace('id="api-inflate-returns"', 'id="other"'),
                    body + '<h3 id="api-inflate-returns">Duplicate</h3>',
                    body.replace('Meaning and conditions', 'Wrong heading'),
                    body.replace('<td>继续。</td>', '')):
            with self.subTest(bad=bad[:80]):
                with self.assertRaises(ValueError):
                    enhance_contract(bad, 'inflate', 'en')

    def test_source_markup_is_not_interpolated_into_generated_attributes(self):
        name = 'odd"><script>alert(1)</script>'
        heading = 'api-' + name.lower() + '-returns'
        from html import escape
        body = render(source()).replace('api-inflate-returns', escape(heading, quote=True))
        enhanced = enhance_contract(body, name, 'en')
        self.assertNotIn('<script>', enhanced)
        self.assertIn('data-return-guide="odd&quot;&gt;&lt;script&gt;', enhanced)
        self.assertIn('&lt;script&gt;alert(1)&lt;/script&gt;()', enhanced)

    def test_source_validation_enforces_all_96_bilingual_entries(self):
        with tempfile.TemporaryDirectory() as temporary:
            repo = Path(temporary)
            (repo / 'tests/audit').mkdir(parents=True)
            (repo / 'docs/spec/api').mkdir(parents=True)
            names = ['fn' + str(index) for index in range(96)]
            manifest = {'apis': [{'function': name, 'manual': 'docs/spec/api/group.md#' + name} for name in names]}
            (repo / 'tests/audit/public-api.json').write_text(json.dumps(manifest))
            for lang in HEADERS:
                suffix = '.zh.md' if lang == 'zh' else '.md'
                (repo / ('docs/spec/api/group' + suffix)).write_text('\n'.join(source(name, lang, rows=1) for name in names))
            self.assertEqual(validate_sources(repo), 96)
            zh = repo / 'docs/spec/api/group.zh.md'
            original = zh.read_text()
            for broken in (original.replace('{#api-fn0-returns}', '{#missing}'),
                           original + '\n' + source('fn0', 'zh'),
                           original.replace('含义与出现条件', '错误表头', 1)):
                zh.write_text(broken)
                with self.assertRaises(ValueError):
                    validate_sources(repo)
            zh.write_text(original)
            manifest['apis'][0]['function'] = names[1]
            (repo / 'tests/audit/public-api.json').write_text(json.dumps(manifest))
            with self.assertRaises(ValueError):
                validate_sources(repo)


    def test_canonical_count_outputs_keep_literal_pointer_stars(self):
        root=Path(__file__).resolve().parents[3]
        for lang in ['en','zh']:
            path=root/'docs/spec/api'/('utility.zh.md' if lang=='zh' else 'utility.md')
            source_text=path.read_text()
            for name in ['uncompress2','uncompress2_z']:
                text=re.split(r'^## '+re.escape(name)+r'\s*$',source_text,flags=re.M)[1].split('\n## ',1)[0]
                blocks=_blocks(render(text))
                table=next(block.raw for block in blocks if block.tag=='table')
                self.assertIn('<code>*destLen</code>',table)
                self.assertIn('<code>*sourceLen</code>',table)



if __name__ == '__main__':
    unittest.main()
