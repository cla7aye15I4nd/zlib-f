"""Reject untranslated reader text while retaining exact source and examples."""
from dataclasses import dataclass, field
from html.parser import HTMLParser
import re


# These are names and formats, not English prose. Source identifiers are also
# recognized by their spelling; no directory or page is exempt from the check.
TECHNICAL_NAMES = frozenset('''
API ABI AST ASCII C CRC CRC32 DEFLATE FDICT GZIP Huffman JSON Lean Linux
LP64 NULL RFC UTF UTF8 Windows zlib gzip raw Adler Adler32 Mermaid
'''.lower().split())
ENGLISH_LABELS = frozenset('''
contents|documentation|reference|status|scope|input|output|history|length|
distance|search|reset|play|previous|next|read more|diagram source|source snapshot|
domain|signature|parameters|preconditions|postconditions|returns|effects|ownership|
details|target|targets|dependencies|module|modules|registered|unproved|
initialization|termination|init|end|
library queries|checksums|byte-address model|inflate streams|deflate streams|
target evidence|proof progress graph|proof progress and remaining work|
recorded checkpoint|remaining work|registered proof|locally checked|not proved|
blocked|default inputs|common inputs|all stated inputs|all inputs|clear filters
'''.replace('\n', '').split('|'))
READER_REMINDERS = (
    r'\bto[\s-]+confirm\b',
    r'待确认',
    r'命题存在(?:并)?不代表',
    r'说明与命题不等于已接受证明',
)
STOP_WORDS = frozenset('''
a an the this that these those is are was were be been being and or but
of for to from with without in on at by as into through each every only
not no can cannot must should may when while before after then than its
it they their which all has have had does do will would if so same both
'''.split())
HUMAN_TAGS = frozenset('p h1 h2 h3 h4 h5 h6 th td li summary button label '
                       'legend caption dt dd figcaption option a span text title desc pre'.split())
CONTAINERS = frozenset('body main article section div'.split())
VOID = frozenset('area base br col embed hr img input link meta param source track wbr'.split())
HAN = re.compile(r'[\u3400-\u9fff]')
URL = re.compile(r'https?://\S+|mailto:\S+')
IDENTIFIER = re.compile(
    r'(?<![\w])(?:'
    r'[A-Za-z_][\w.-]*(?:/[\w.-]+)+'  # source paths
    r'|[A-Za-z_][\w-]*(?:\.[A-Za-z_][\w-]*)+'  # namespace/file names
    r'|[A-Za-z][\w]*_[\w]+'  # C names
    r'|[A-Z][a-z]+(?:[A-Z][A-Za-z0-9]*)+'  # Lean declaration names
    r'|[A-Z][A-Z0-9_]*\d[A-Z0-9_]*'
    r')(?![\w])'
)
SOURCE_VIEW = re.compile(
    r'''<pre\b(?=[^>]*\bclass=(["'])rf-source-code\1)[^>]*>.*?</pre\s*>''',
    re.S | re.I,
)


def _issues(text: str, tag: str) -> list[str]:
    lines = [line.strip() for line in text.splitlines() if line.strip()]
    quoted_data = tag == 'pre' and lines and all(
        re.fullmatch(r'"(?:[^"\\]|\\.)*"[,;]?', line) for line in lines
    )
    text = ' '.join(text.split())
    if not text:
        return []
    issues = []
    for pattern in READER_REMINDERS:
        if re.search(pattern, text, re.I):
            issues.append('Reader reminder remains: ' + text[:180])
            break
    # Quoted strings and byte rows in plaintext examples are source data.
    if quoted_data:
        return issues
    readable = IDENTIFIER.sub(' ', URL.sub(' ', text))
    for run in re.split(r'[\u3400-\u9fff]+', readable):
        words = [w.lower() for w in re.findall(r'\b[A-Za-z]+\b', run)]
        human = [w for w in words if len(w) > 1 and w not in TECHNICAL_NAMES]
        if len(human) >= 6 and sum(w in STOP_WORDS for w in human) >= 2:
            issues.append(f'English prose in <{tag}>: ' + text[:180])
            break
    normalized = re.sub(r'\s+', ' ', text.lower()).strip(' .:↗→')
    if not HAN.search(text):
        words = [w.lower() for w in re.findall(r'\b[A-Za-z]+\b', readable)]
        human = [w for w in words if w not in TECHNICAL_NAMES]
        if (normalized in ENGLISH_LABELS
                or re.match(r'^reference\s*/', normalized)
                or re.match(r'^(?:literal\s+[a-z]|match\s*[·:/])', normalized)
                or re.search(r'\b\d+\s+(?:bytes?|bits?)\b', normalized)
                or (tag in {'h1', 'h2', 'h3', 'h4', 'h5', 'h6', 'th', 'button',
                            'label', 'summary', 'caption', 'option', 'title'} and len(human) >= 2)):
            issues.append(f'English label in <{tag}>: ' + text[:180])
    return issues


def _mermaid_issues(source: str) -> list[str]:
    labels = []
    for match in re.finditer(r'\["([^"\n]+)"\]|\[([^\]\n]+)\]|\|([^|\n]+)\||state\s+"([^"]+)"', source):
        label = next(value for value in match.groups() if value is not None)
        labels.extend(_issues(label, 'label'))
    for line in source.splitlines():
        if '-->' in line and ':' in line:
            labels.extend(_issues(line.split(':', 1)[1], 'label'))
    return labels


@dataclass
class _Frame:
    tag: str
    excluded: bool = False
    candidate: bool = False
    diagram: bool = False
    text: list[str] = field(default_factory=list)


class _ChineseHTML(HTMLParser):
    def __init__(self, document: str):
        super().__init__(convert_charrefs=True)
        self.stack: list[_Frame] = []
        self.issues: list[str] = []
        self.feed(document)
        self.close()
        while self.stack:
            self._finish(self.stack.pop())

    def handle_starttag(self, tag, attrs):
        if tag in VOID:
            return
        attrs = dict(attrs)
        classes = attrs.get('class', '').split()
        language = next((c[9:] for c in classes if c.startswith('language-')), '')
        diagram = tag == 'code' and language == 'mermaid'
        excluded = bool(self.stack and self.stack[-1].excluded)
        excluded |= tag in {'script', 'style'} or 'rf-source-code' in classes
        excluded |= tag == 'code' and language not in {'text', 'plaintext', 'mermaid'}
        if tag == 'pre' and self.stack:
            self.stack[-1].text.append(' ')
        candidate = tag in HUMAN_TAGS or tag in CONTAINERS
        if tag in {'span', 'a'}:
            candidate = not any(frame.candidate and frame.tag not in CONTAINERS
                                for frame in self.stack)
        self.stack.append(_Frame(tag, excluded or diagram, candidate, diagram))

    def handle_startendtag(self, tag, attrs):
        if tag not in VOID:
            self.handle_starttag(tag, attrs)
            self.handle_endtag(tag)

    def handle_data(self, data):
        if not self.stack:
            return
        if self.stack[-1].diagram:
            self.stack[-1].text.append(data)
            return
        if self.stack[-1].excluded:
            return
        for frame in reversed(self.stack):
            if frame.candidate:
                frame.text.append(data)
                return

    def _finish(self, frame):
        if frame.diagram:
            self.issues.extend(_mermaid_issues(''.join(frame.text)))
        elif frame.candidate and not frame.excluded:
            self.issues.extend(_issues(''.join(frame.text), frame.tag))
        if self.stack:
            self.stack[-1].text.append(' ')

    def handle_endtag(self, tag):
        index = next((i for i in range(len(self.stack)-1, -1, -1)
                      if self.stack[i].tag == tag), None)
        if index is not None:
            while len(self.stack) > index:
                self._finish(self.stack.pop())


def audit_chinese_html(document: str) -> list[str]:
    """Find actionable untranslated prose/labels, without rewriting source code."""
    # The source reader can contain thousands of highlighted spans. Its exact
    # preformatted source is already excluded by class below, so avoid parsing
    # those spans while retaining every surrounding explanatory element.
    document = SOURCE_VIEW.sub('<pre class="rf-source-code"></pre>', document)
    return list(dict.fromkeys(_ChineseHTML(document).issues))
