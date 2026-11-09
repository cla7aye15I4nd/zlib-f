"""Check the generated site's local files, language pairing, and chapter anchors."""
from pathlib import Path
from html.parser import HTMLParser
from urllib.parse import urlsplit, unquote
import re
import json
from language import audit_chinese_html

ROOT = Path(__file__).resolve().parent / "dist"


class Page(HTMLParser):
    def __init__(self, path: Path):
        super().__init__()
        self.ids: set[str] = set()
        self.links: list[str] = []
        self.content_links: list[str] = []
        self.in_content = False
        self.parts = 0
        self.titles = 0
        self.demos = 0
        self.global_toc = 0
        self.map_nodes = []
        self.purpose = 0
        self.redirect = False
        self.obsolete_nav = []
        self.c_blocks = 0
        self.uncolored_code = []
        document=path.read_text()
        self.feed(document)
        for script_id in ["bk-redirect-data","bk-legacy-links"]:
            match=re.search(r'<script[^>]*id="'+script_id+r'"[^>]*>(.*?)</script>',document,re.S)
            if match:self.links.extend(json.loads(match.group(1)).values())
        self.language_issues=audit_chinese_html(document) if path.name.endswith('.zh.html') else []

    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
        if tag == "html" and "data-book-redirect" in a:self.redirect=True
        retired={"bk-navigation","bk-side","rf-nav","rf-sidebar","bk-chapter-pagination","bk-proof-bridge"}
        self.obsolete_nav.extend(retired.intersection(a.get("class","").split()))
        if tag == 'article' and a.get('id') == 'content':
            self.in_content = True
        if "id" in a:
            assert a["id"] not in self.ids, f"Duplicate id: {a['id']}"
            self.ids.add(a["id"])
        for key in ("href", "src"):
            if a.get(key):
                self.links.append(a[key])
                if self.in_content and key == 'href':
                    self.content_links.append(a[key])
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
            if language=='c':self.c_blocks+=1
            if language in {'c','lean','lean4','sh','bash','python','json','toml'} and 'syntax-highlight' not in classes:
                self.uncolored_code.append(language)
            if language=='mermaid':
                assert 'syntax-highlight' not in classes, 'Diagram source must retain its original markup'

    def handle_endtag(self, tag):
        if tag == 'article':
            self.in_content = False


from book import BOOK,APPENDICES
routes=[c['route'] for c in BOOK]+['appendix/'+key for key,_,_ in APPENDICES]
pages={}
for route in routes:
    en=Page(ROOT/(route+'.html'));zh=Page(ROOT/(route+'.zh.html'))
    assert en.ids==zh.ids,(route,'Language anchors diverged')
    pages[route+'.html']=en;pages[route+'.zh.html']=zh
for item in BOOK:
    for suffix in ['.html','.zh.html']:
        page=pages[item['route']+suffix]
        assert {a for a,_,_ in item['anchors']}<=page.ids,(item['route'],'Missing implementation or proof section')
        assert page.c_blocks>0,(item['route'],'Missing actual C excerpt')
        assert not page.obsolete_nav,(item['route'],'Redundant navigation',page.obsolete_nav)
assert len(BOOK)==6,'The main reading path must remain six substantive chapters'
for css in (ROOT / "static").glob("*.css"):
    for path in re.findall(r"url\(['\"]?([^)'\"]+)", css.read_text()):
        if ":" not in path:
            assert (css.parent / path).exists(), (css.name, path)
all_pages = {path.resolve(): Page(path) for path in ROOT.rglob('*.html')}
for path, page in all_pages.items():
    assert page.titles == 1, (path, 'Expected one page title', page.titles)
    assert not page.uncolored_code, (path, 'Code block lacks syntax highlighting', page.uncolored_code)
    assert not page.language_issues, (path, 'Chinese reader text needs review', page.language_issues)
    if not page.redirect:
        assert page.global_toc==1, (path, 'Missing global contents')
        assert any(urlsplit(link).path.endswith('/select.css') for link in page.links), (path, 'Missing shared dropdown styles')
        assert any(urlsplit(link).path.endswith('/select.js') for link in page.links), (path, 'Missing shared dropdown behavior')
        suffix='.zh.html' if path.name.endswith('.zh.html') else '.html'
        targets={((path.parent/urlsplit(href).path).resolve()) for href in page.links if not urlsplit(href).scheme and urlsplit(href).path}
        assert not page.obsolete_nav,(path,'Redundant navigation',page.obsolete_nav)
        for chapter in BOOK:
            assert (ROOT/(chapter['route']+suffix)).resolve() in targets,(path,'Contents omits main chapter',chapter['key'])
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
print(f"Static checks passed: {len(all_pages)} pages, Chinese reader text, all API contracts and targets, six implementation chapters, local links and assets")
