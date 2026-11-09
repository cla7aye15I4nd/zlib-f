"""Build-time syntax colors without changing code text or diagram markup."""
from functools import lru_cache
import html
import re

from pygments import highlight
from pygments.formatters import HtmlFormatter
from pygments.lexers import get_lexer_by_name
from pygments.util import ClassNotFound

FORMATTER = HtmlFormatter(nowrap=True, classprefix='tok-')
BLOCK = re.compile(r'(<pre\b[^>]*><code\b[^>]*class=")([^"]*)("[^>]*>)(.*?)(</code></pre>)', re.S)


@lru_cache(maxsize=512)
def color_code(source: str, language: str) -> str:
    """Return balanced token spans, retaining the exact displayed source."""
    language = {'lean': 'lean4', 'shell': 'sh'}.get(language, language)
    try:
        lexer = get_lexer_by_name(language, stripnl=False, ensurenl=False, tabsize=0)
    except ClassNotFound:
        return html.escape(source)
    result = highlight(source, lexer, FORMATTER)
    if not source.endswith('\n') and result.endswith('\n'):
        result = result[:-1]
    if html.unescape(re.sub(r'<[^>]*>', '', result)) != source:
        raise ValueError('Syntax coloring changed the source text: ' + language)
    return result


def color_blocks(document: str) -> str:
    def replace(match):
        classes = match[2].split()
        language = next((name[9:] for name in classes if name.startswith('language-')), '')
        if not language or language in {'text', 'plaintext', 'mermaid'} or 'syntax-highlight' in classes:
            return match[0]
        source = html.unescape(match[4])
        colored = color_code(source, language)
        return match[1] + match[2] + ' syntax-highlight' + match[3] + colored + match[5]
    return BLOCK.sub(replace, document)
