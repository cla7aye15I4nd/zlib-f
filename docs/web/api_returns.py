"""Decorate canonical Markdown return tables without rewriting their content."""
from __future__ import annotations

from dataclasses import dataclass
from html import escape
from html.parser import HTMLParser
import json
from pathlib import Path
import re

SITE = Path(__file__).resolve().parent
REPO = SITE.parents[1]
HEADERS = {
    'en': ('Returned value', 'Meaning and conditions', 'Caller’s next step'),
    'zh': ('返回值', '含义与出现条件', '调用者接下来'),
}
VOID = {'area', 'base', 'br', 'col', 'embed', 'hr', 'img', 'input', 'link', 'meta', 'param', 'source', 'track', 'wbr'}


@dataclass(frozen=True)
class _Block:
    raw: str
    tag: str = ''
    attrs: tuple = ()

    def attr(self, key):
        return dict(self.attrs).get(key)


class _Roots(HTMLParser):
    """Record root boundaries, retaining original HTML through source slicing."""
    def __init__(self, source):
        super().__init__(convert_charrefs=False)
        self.source = source
        self.lines = [0] + [m.end() for m in re.finditer('\n', source)]
        self.stack = []
        self.spans = []
        self.start = 0
        self.root = ''
        self.attrs = ()

    def _position(self):
        line, column = self.getpos()
        return self.lines[line - 1] + column

    def handle_starttag(self, tag, attrs):
        if not self.stack:
            self.start, self.root, self.attrs = self._position(), tag, tuple(attrs)
        if tag in VOID:
            if not self.stack:
                self.spans.append((self.start, self._position() + len(self.get_starttag_text()), tag, self.attrs))
        else:
            self.stack.append(tag)

    def handle_startendtag(self, tag, attrs):
        if not self.stack:
            self.spans.append((self._position(), self._position() + len(self.get_starttag_text()), tag, tuple(attrs)))

    def handle_endtag(self, tag):
        if not self.stack or self.stack[-1] != tag:
            raise ValueError(f'Unbalanced contract HTML at </{tag}>')
        self.stack.pop()
        if not self.stack:
            self.spans.append((self.start, self.source.index('>', self._position()) + 1, self.root, self.attrs))


def _blocks(source):
    parser = _Roots(source)
    parser.feed(source)
    parser.close()
    if parser.stack:
        raise ValueError('Unclosed contract HTML element')
    blocks, end = [], 0
    for start, stop, tag, attrs in parser.spans:
        if start > end:
            blocks.append(_Block(source[end:start]))
        blocks.append(_Block(source[start:stop], tag, attrs))
        end = stop
    if end < len(source):
        blocks.append(_Block(source[end:]))
    return blocks


class _Text(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.parts = []

    def handle_data(self, data):
        self.parts.append(data)


def _text(source):
    parser = _Text()
    parser.feed(source)
    return ''.join(parser.parts).strip()


class _Table(HTMLParser):
    """Inspect canonical rows; nested cell markup remains untouched."""
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.headers = []
        self.rows = []
        self.row = None
        self.header = None
        self.tables = 0

    def handle_starttag(self, tag, attrs):
        if tag == 'table':
            self.tables += 1
        elif tag == 'tr':
            self.row = []
        elif tag in {'td', 'th'}:
            if self.row is None:
                raise ValueError('Return cell outside a table row')
            self.row.append(tag)
            if tag == 'th':
                self.header = []

    def handle_endtag(self, tag):
        if tag == 'th':
            self.headers.append(''.join(self.header).strip())
            self.header = None
        elif tag == 'tr':
            self.rows.append(self.row)
            self.row = None

    def handle_data(self, data):
        if self.header is not None:
            self.header.append(data)


def _table_cases(source, lang):
    parser = _Table()
    parser.feed(source)
    expected = HEADERS[lang]
    # Straight apostrophes and typographic apostrophes have identical meaning.
    normalized = tuple(header.replace("'", '’') for header in parser.headers)
    if parser.tables != 1 or normalized != expected:
        raise ValueError(f'Return table must have exactly these three headers: {expected}')
    if len(parser.rows) < 2 or parser.rows[0] != ['th'] * 3 or any(row != ['td'] * 3 for row in parser.rows[1:]):
        raise ValueError('Return table needs one header row and nonempty three-cell cases')
    return len(parser.rows) - 1


def parse_role(contract_markdown: str) -> tuple[str, str]:
    """Read the source's return type and value-role line for an index badge."""
    pattern = r'^\*\*(?:Return type[.:]?|返回值类型[。.:：]?)\*\*\s*`([^`\n]+)`\s*[—–]\s*(.+?)\s*$'
    matches = re.findall(pattern, contract_markdown, re.M)
    if len(matches) != 1:
        raise ValueError('Expected exactly one canonical return type and role')
    return matches[0]


def enhance_contract(body: str, name: str, lang: str, level: int = 2) -> str:
    """Wrap the canonical return section and its untouched semantic table."""
    if lang not in HEADERS or level not in range(1, 7):
        raise ValueError('Expected en/zh and a heading level from 1 to 6')
    blocks = _blocks(body)
    guide_id = 'api-' + name.lower() + '-returns'
    starts = [i for i, block in enumerate(blocks) if block.attr('id') == guide_id]
    if len(starts) != 1:
        raise ValueError(f'{name}: expected exactly one canonical return heading')
    start = starts[0]
    if not re.fullmatch(r'h[1-6]', blocks[start].tag):
        raise ValueError(f'{name}: return anchor must be a heading')
    heading_level = int(blocks[start].tag[1])
    stop = next((i for i in range(start + 1, len(blocks))
                 if re.fullmatch(r'h[1-6]', blocks[i].tag) and int(blocks[i].tag[1]) <= heading_level), len(blocks))
    tables = [i for i in range(start + 1, stop) if blocks[i].tag == 'table']
    if len(tables) != 1:
        raise ValueError(f'{name}: expected exactly one canonical return table')
    index = tables[0]
    count = _table_cases(blocks[index].raw, lang)
    attr = escape(name, quote=True)
    css = 'ar-return-map' + (' ar-return-single' if count == 1 else '')
    # Source headings, paragraphs, tables, entities and IDs are retained verbatim.
    labels = ';'.join('--ar-col'+str(i)+':'+json.dumps(text,ensure_ascii=False)
                      for i,text in enumerate(HEADERS[lang],1))
    diagram = (f'<div class="{css}" data-return-cases="{count}" style="{escape(labels,quote=True)}">'
               '<div class="ar-return-call"><code>' + escape(name) + '()</code></div>'
               '<div class="ar-return-table">' + blocks[index].raw + '</div></div>')
    guide = (f'<section class="ar-return-guide" data-return-guide="{attr}" aria-labelledby="{escape(guide_id, quote=True)}">'
             + ''.join(block.raw for block in blocks[start:index]) + diagram
             + ''.join(block.raw for block in blocks[index + 1:stop]) + '</section>')
    return ''.join(block.raw for block in blocks[:start]) + guide + ''.join(block.raw for block in blocks[stop:])


def enhance_manual(body: str, lang: str) -> str:
    """Decorate each canonical return heading in an entire API manual."""
    blocks = _blocks(body)
    result, section, name = [], [], None
    def flush():
        raw = ''.join(section)
        if name and any(block.attr('id') == 'api-' + name.lower() + '-returns' for block in _blocks(raw)):
            raw = enhance_contract(raw, name, lang, level=3)
        result.append(raw)
    for block in blocks:
        if block.tag == 'h2':
            flush()
            section = []
            name = _text(block.raw)
            result.append(block.raw)
        else:
            section.append(block.raw)
    flush()
    return ''.join(result)


def validate_sources(repo: Path = REPO) -> int:
    """Reject missing/duplicate guides and malformed bilingual source tables."""
    from markdown import Markdown
    manifest = json.loads((repo / 'tests/audit/public-api.json').read_text())
    names = [entry['function'] for entry in manifest['apis']]
    if len(names) != 96 or len(set(names)) != 96:
        raise ValueError('Public API manifest must contain 96 distinct functions')
    by_path = {}
    for entry in manifest['apis']:
        by_path.setdefault(entry['manual'].split('#')[0], set()).add(entry['function'])
    for relative, expected in by_path.items():
        for lang in HEADERS:
            path = repo / relative
            if lang == 'zh':
                path = path.with_name(path.stem + '.zh.md')
            source = path.read_text()
            sections = list(re.finditer(r'^##\s+(.+?)\s*$', source, re.M))
            counts = {name: 0 for name in expected}
            all_anchors = re.findall(r'\{#api-([\w]+)-returns\}', source)
            if sorted(all_anchors) != sorted(name.lower() for name in expected):
                raise ValueError(f'{path.name}: missing, duplicate or extra canonical return guides')
            for index, match in enumerate(sections):
                name = match[1]
                if name not in expected:
                    continue
                counts[name] += 1
                end = sections[index + 1].start() if index + 1 < len(sections) else len(source)
                contract = source[match.end():end]
                parse_role(contract)
                parser = Markdown(extensions=['fenced_code', 'tables', 'attr_list', 'md_in_html'])
                body = parser.convert(contract)
                enhance_contract(body, name, lang, level=3)
            if any(count != 1 for count in counts.values()):
                raise ValueError(f'{path.name}: missing or duplicate function contracts')
    return len(names)
