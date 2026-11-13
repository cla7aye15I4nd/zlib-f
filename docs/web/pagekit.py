"""Facts and fragments shared by every page: build stamp, top navigation, description."""
from __future__ import annotations

from pathlib import Path
import html
import os
import re
import subprocess

REPO = Path(__file__).resolve().parents[2]
OUT = Path(__file__).resolve().parent / 'dist'
REPO_URL = 'https://github.com/cla7aye15I4nd/zlib-f'


def _git(*args: str) -> str:
    return subprocess.check_output(['git', *args], cwd=REPO, text=True).strip()


COMMIT = _git('rev-parse', 'HEAD')
DATE = _git('log', '-1', '--format=%cs')
BRANCH = os.environ.get('GITHUB_REF_NAME') or _git('rev-parse', '--abbrev-ref', 'HEAD')


def route_href(route: str, current: Path, lang: str, anchor: str = '') -> str:
    target = OUT / (route + ('.zh.html' if lang == 'zh' else '.html'))
    return os.path.relpath(target, current.parent).replace(os.sep, '/') + ('#' + anchor if anchor else '')


def top_links(current: Path, lang: str) -> str:
    """The one fixed set of top-level entries, on every page."""
    zh = lang == 'zh'
    entries = [
        ('index', 'articles', '文章', 'Articles'),
        ('status', '', '结果与进度', 'Results'),
        ('reference/index', '', '规格', 'Specifications'),
        ('reference/proofs', '', '证明', 'Proofs'),
    ]
    relative = current.relative_to(OUT).as_posix()
    links = []
    for route, anchor, cn, en in entries:
        suffix = '.zh.html' if zh else '.html'
        mark = ' aria-current="page"' if relative == route + suffix and not anchor else ''
        links.append(f'<a href="{route_href(route, current, lang, anchor)}"{mark}>{cn if zh else en}</a>')
    return '<span class="site-links">' + ''.join(links) + '</span>'


def stamp(current: Path, lang: str) -> str:
    zh = lang == 'zh'
    short = COMMIT[:10]
    status = route_href('status', current, lang)
    text = (f'构建自 <a href="{REPO_URL}/commit/{COMMIT}"><code>{short}</code></a>（{html.escape(BRANCH)} 分支），{DATE}。'
            if zh else
            f'Built from <a href="{REPO_URL}/commit/{COMMIT}"><code>{short}</code></a> (branch {html.escape(BRANCH)}), {DATE}.')
    return (f'<footer class="site-stamp">{text} <a href="{status}">'
            f'{"当前状态" if zh else "Current status"}</a></footer>')


def describe(body: str, title: str) -> str:
    """A one-sentence meta description: the first paragraph with text, else the title."""
    for paragraph in re.findall(r'<p\b[^>]*>(.*?)</p>', body, re.S):
        text = html.unescape(re.sub(r'<[^>]+>', '', paragraph))
        text = ' '.join(text.split())
        if len(text) >= 40:
            return text if len(text) <= 180 else text[:177].rsplit(' ', 1)[0] + '…'
    return title
