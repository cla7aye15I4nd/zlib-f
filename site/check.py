"""Check the generated site's local files, language pairing, and chapter anchors."""
from pathlib import Path
from html.parser import HTMLParser
from urllib.parse import urlsplit, unquote
import re

ROOT = Path(__file__).resolve().parent / "dist"


class Page(HTMLParser):
    def __init__(self, path: Path):
        super().__init__()
        self.ids: set[str] = set()
        self.links: list[str] = []
        self.parts = 0
        self.titles = 0
        self.demos = 0
        self.feed(path.read_text())

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


pages = {name: Page(ROOT / name) for name in ("index.html", "index.zh.html")}
assert pages["index.html"].ids == pages["index.zh.html"].ids, "Language anchors diverged"
for name, page in pages.items():
    assert page.parts == 2, (name, "Expected exactly two main parts")
    assert page.demos == 8, (name, "Expected eight teaching scenes")
    for link in page.links:
        url = urlsplit(link)
        if url.scheme or url.netloc:
            continue
        assert not url.path.startswith("/"), (name, "Asset would escape the project subpath", link)
        target = (ROOT / unquote(url.path)).resolve() if url.path else ROOT / name
        assert target.is_relative_to(ROOT.resolve()), (name, link)
        assert target.exists(), (name, "Missing local file", link)
        if url.fragment and target.name in pages:
            assert unquote(url.fragment) in pages[target.name].ids, (name, link)
for css in (ROOT / "static").glob("*.css"):
    for path in re.findall(r"url\(['\"]?([^)'\"]+)", css.read_text()):
        if ":" not in path:
            assert (css.parent / path).exists(), (css.name, path)
all_pages = {path.resolve(): Page(path) for path in ROOT.rglob('*.html')}
for path, page in all_pages.items():
    assert page.titles == 1, (path, 'Expected one page title', page.titles)
    for link in page.links:
        url = urlsplit(link)
        if url.scheme or url.netloc:
            continue
        assert not url.path.startswith('/'), (path.name, 'Link escapes project subpath', link)
        target = (path.parent / unquote(url.path)).resolve() if url.path else path
        assert target.exists(), (path, 'Missing local target', link)
        if url.fragment and target in all_pages:
            assert unquote(url.fragment) in all_pages[target].ids, (path, 'Missing local anchor', link)
import json
manifest = json.loads((Path(__file__).resolve().parent.parent/'tests/audit/public-api.json').read_text())
for entry in manifest['apis']:
    for suffix in ('.html', '.zh.html'):
        path = ROOT/'reference/functions'/(entry['function']+suffix)
        assert path.exists(), ('Missing contract', entry['function'], suffix)
        if entry.get('goal'):
            assert 'formal-target' in all_pages[path.resolve()].ids, ('Missing formal target', entry['function'])
print(f"Static checks passed: {len(all_pages)} pages, all API contracts and targets, paired anchors, local links and assets")
