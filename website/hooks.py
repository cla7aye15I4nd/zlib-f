"""Publish the canonical Markdown with repository source links intact."""
import os
from pathlib import Path
import re
from urllib.parse import quote, urlsplit

from mkdocs.structure.files import File

ROOT = Path(__file__).resolve().parents[1]


def on_files(files, config):
    # The web home is the existing proof overview, with no second maintained copy.
    files.remove(files.get_file_from_path('overview.md'))
    files.append(File.generated(config, 'index.md', content=(ROOT / 'docs/overview.md').read_text()))
    for name in ['reading.css', 'diagrams.js']:
        files.append(File.generated(config, 'assets/' + name, content=(ROOT / 'website' / name).read_text()))
    return files


def on_page_markdown(markdown, page, config, files):
    # The browser supplies a persistent heading outline; keep GitHub's manual TOC in source only.
    markdown = re.sub(r'^## Contents\n.*?(?=^## |\Z)', '', markdown, flags=re.M | re.S)
    source = ROOT / 'docs' / page.file.src_uri
    revision = os.environ.get('GITHUB_SHA', 'main')
    repository = config['repo_url'].rstrip('/')

    def link(match):
        target = match[1]
        parsed = urlsplit(target)
        if parsed.scheme or parsed.netloc or not parsed.path:
            return match[0]
        resolved = (source.parent / parsed.path).resolve()
        fragment = '#' + parsed.fragment if parsed.fragment else ''
        if resolved in {ROOT / 'docs/overview.md', ROOT / 'docs/README.md'}:
            target = os.path.relpath(ROOT / 'docs/index.md', source.parent) + fragment
        elif resolved.is_relative_to(ROOT / 'docs'):
            target = os.path.relpath(resolved, source.parent) + fragment
        else:
            relative = resolved.relative_to(ROOT).as_posix()
            target = repository + '/blob/' + revision + '/' + quote(relative, safe='/') + fragment
        return '](' + target + ')'

    return re.sub(r'\]\(([^)]+)\)', link, markdown)
