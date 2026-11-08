"""Check the generated site's local files, language pairing, and chapter anchors."""
from pathlib import Path
from html.parser import HTMLParser
from urllib.parse import urlsplit, unquote
import re
from language import audit_chinese_html

ROOT = Path(__file__).resolve().parent / "dist"


class Page(HTMLParser):
    def __init__(self, path: Path):
        super().__init__()
        self.ids: set[str] = set()
        self.links: list[str] = []
        self.parts = 0
        self.titles = 0
        self.demos = 0
        self.global_toc = 0
        self.map_nodes = []
        self.purpose = 0
        self.uncolored_code = []
        document=path.read_text()
        self.feed(document)
        self.language_issues=audit_chinese_html(document) if path.name.endswith('.zh.html') else []

    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
        if "id" in a:
            assert a["id"] not in self.ids, f"Duplicate id: {a['id']}"
            self.ids.add(a["id"])
        for key in ("href", "src"):
            if a.get(key):
                self.links.append(a[key])
        if tag == "h2":
            self.parts += 1
        if tag == 'h1':
            self.titles += 1
        if tag == "zlib-demo":
            self.demos += 1
        if 'data-global-toc' in a:
            self.global_toc += 1
        if 'data-map-node' in a:
            self.map_nodes.append(a['data-map-node'])
        if 'bk-purpose' in a.get('class', '').split():
            self.purpose += 1
        if tag == 'code':
            classes=a.get('class','').split()
            language=next((c[9:] for c in classes if c.startswith('language-')), '')
            if language in {'c','lean','lean4','sh','bash','python','json','toml'} and 'syntax-highlight' not in classes:
                self.uncolored_code.append(language)
            if language=='mermaid':
                assert 'syntax-highlight' not in classes, 'Diagram source must retain its original markup'


from routes import UNITS, CHAPTER_BY_KEY
routes=['index','algorithms/index','verification/index',*[f'verification/{u["key"]}' for u in UNITS],*[f'chapters/{key}' for key in CHAPTER_BY_KEY],'chapters/interfaces']
pages={}
for route in routes:
    en=Page(ROOT/(route+'.html'));zh=Page(ROOT/(route+'.zh.html'))
    assert en.ids==zh.ids, (route,'Language anchors diverged')
    pages[route+'.html']=en;pages[route+'.zh.html']=zh
assert {'algorithms','verification'}<=pages['index.html'].ids
assert pages['algorithms/index.html'].demos==6, 'Overview must retain its five scenes and the history-window illustration'
assert pages['chapters/bits.html'].demos==1, 'Detailed bit writer is missing'
assert pages['chapters/storage.html'].demos==1, 'Storage comparison is missing'
for route in ['index','verification/index']:
    for suffix in ['.html','.zh.html']:
        assert set(pages[route+suffix].map_nodes)=={u['key'] for u in UNITS}, (route, 'Incomplete mechanism map')
for route in routes:
    if route.startswith('chapters/'):
        assert pages[route+'.html'].purpose==pages[route+'.zh.html'].purpose==1, (route, 'Missing chapter purpose')
for css in (ROOT / "static").glob("*.css"):
    for path in re.findall(r"url\(['\"]?([^)'\"]+)", css.read_text()):
        if ":" not in path:
            assert (css.parent / path).exists(), (css.name, path)
all_pages = {path.resolve(): Page(path) for path in ROOT.rglob('*.html')}
for path, page in all_pages.items():
    assert page.titles == 1, (path, 'Expected one page title', page.titles)
    assert not page.uncolored_code, (path, 'Code block lacks syntax highlighting', page.uncolored_code)
    assert not page.language_issues, (path, 'Chinese reader text needs review', page.language_issues)
    if path.relative_to(ROOT).parts[0] != 'sample':
        assert page.global_toc==1, (path, 'Missing global contents')
        suffix='.zh.html' if path.name.endswith('.zh.html') else '.html'
        targets={((path.parent/urlsplit(href).path).resolve()) for href in page.links if not urlsplit(href).scheme and urlsplit(href).path}
        for chapter in [*CHAPTER_BY_KEY,'interfaces']:
            assert (ROOT/'chapters'/(chapter+suffix)).resolve() in targets, (path, 'Global contents omits chapter', chapter)
    for link in page.links:
        url = urlsplit(link)
        if url.scheme or url.netloc:
            continue
        assert not url.path.startswith('/'), (path.name, 'Link escapes project subpath', link)
        target = (path.parent / unquote(url.path)).resolve() if url.path else path
        assert target.exists(), (path, 'Missing local target', link)
        if url.fragment and target in all_pages:
            assert unquote(url.fragment) in all_pages[target].ids, (path, 'Missing local anchor', link)
    if path.name.endswith('.zh.html'):
        opposite=path.with_name(path.name.removesuffix('.zh.html')+'.html')
        assert opposite in all_pages, (path,'Missing English counterpart')
        assert page.ids==all_pages[opposite].ids, (path,'Reference language anchors diverged',page.ids^all_pages[opposite].ids)
import json
manifest = json.loads((Path(__file__).resolve().parent.parent/'tests/audit/public-api.json').read_text())
for entry in manifest['apis']:
    for suffix in ('.html', '.zh.html'):
        path = ROOT/'reference/functions'/(entry['function']+suffix)
        assert path.exists(), ('Missing contract', entry['function'], suffix)
        if entry.get('goal'):
            assert 'formal-target' in all_pages[path.resolve()].ids, ('Missing formal target', entry['function'])
import subprocess
import sys
subprocess.run([sys.executable,'-m','unittest','discover','-s',str(Path(__file__).resolve().parent/'tests'),'-p','test_*.py'],check=True)
print(f"Static checks passed: {len(all_pages)} pages, Chinese reader text, all API contracts and targets, paired reading routes, local links and assets")
