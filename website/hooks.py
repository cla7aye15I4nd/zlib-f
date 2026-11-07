"""Build two reading languages from canonical documents and shared evidence."""
import hashlib
import json
import os
from collections import Counter
from pathlib import Path
import re
import shutil
import tempfile
import xml.etree.ElementTree as ET
from urllib.parse import quote, urlsplit

from markdown import Markdown
from mkdocs.plugins import event_priority

ROOT = Path(__file__).resolve().parents[1]
STAGING = None


def without_contents(markdown):
    return re.sub(r'^## (?:Contents|目录)(?: \{[^}\n]*\})?\n.*?(?=^## |\Z)',
                  '', markdown, flags=re.M | re.S)


def headings(markdown):
    """Find headings outside fenced examples; their order is part of localization."""
    result = []
    fence = None
    for number, line in enumerate(markdown.splitlines()):
        marker = re.match(r'^\s*(`{3,}|~{3,})', line)
        if marker:
            token = marker[1][0]
            if fence is None:
                fence = token
            elif fence == token:
                fence = None
            continue
        if fence is None:
            match = re.match(r'^(#{1,6}) +(.+)$', line)
            if match:
                result.append((number, len(match[1])))
    return result


def aligned_anchors(english, chinese, path):
    """Keep one fragment vocabulary so every cross-language link remains valid."""
    english, chinese = without_contents(english), without_contents(chinese)
    parser = Markdown(extensions=['toc', 'attr_list', 'pymdownx.superfences'])
    parser.convert(english)

    def flatten(items):
        for item in items:
            yield item
            yield from flatten(item['children'])

    tokens = list(flatten(parser.toc_tokens))
    english_headings, chinese_headings = headings(english), headings(chinese)
    if ([level for _, level in english_headings] !=
            [level for _, level in chinese_headings] or len(tokens) != len(english_headings)):
        raise ValueError(f'English/Chinese section structure differs: {path}')
    lines = chinese.splitlines()
    for (number, _), token in zip(chinese_headings, tokens):
        text = re.sub(r'\s*\{[^{}]*\}\s*$', '', lines[number])
        lines[number] = text + ' {#' + token['id'] + '}'
    return '\n'.join(lines) + '\n'


def localized_progress(source, *, check_coverage=True):
    """Translate labels/prose without maintaining a second graph or status table."""
    rules = json.loads((ROOT / 'website/locales/progress-zh.json').read_text())
    matches = []
    for rule in rules:
        original, translated = rule['source'], rule['translation']
        fields = re.findall(r'\{n\d+\}', original)
        pattern = re.escape(original)
        if fields:
            for field in dict.fromkeys(fields):
                pattern = pattern.replace(re.escape(field), '(?P<' + field[1:-1] + r'>[0-9]+)', 1)
                pattern = pattern.replace(re.escape(field), '(?P=' + field[1:-1] + ')')
        found = list(re.finditer(pattern, source))
        if not found:
            raise ValueError('Stale progress translation: ' + original[:100])
        for match in found:
            result = translated
            for key, value in match.groupdict().items():
                result = result.replace('{' + key + '}', value)
            matches.append((match.start(), match.end(), result))
    # Apply to canonical text once; a paragraph wins over its shorter labels.
    output, residual, end = [], [], 0
    for start, stop, result in sorted(matches, key=lambda m: (m[0], -m[1])):
        if start < end:
            continue
        output.extend([source[end:start], result])
        residual.append(source[end:start])
        end = stop
    output.append(source[end:])
    residual.append(source[end:])
    prose = ''.join(residual)
    prose = re.sub(r'^```[^\n]*\n.*?^```[^\n]*$', '', prose, flags=re.M | re.S)
    prose = re.sub(r'<!--.*?-->|<[^>]+>', '', prose, flags=re.S)
    prose = re.sub(r'!?\[[^\]]*\]\([^)]+\)|`[^`]+`', '', prose)
    terms = re.findall(r"\b[A-Za-z]+(?:[-'][A-Za-z]+)*\b", prose)
    fingerprint = hashlib.sha256('\n'.join(terms).encode()).hexdigest()
    coverage = ROOT / 'website/locales/progress-coverage.json'
    if check_coverage:
        if json.loads(coverage.read_text())['untranslated_terms_sha256'] != fingerprint:
            raise ValueError('New progress prose needs Chinese translation rules')
    else:
        coverage.write_text(json.dumps({'untranslated_terms_sha256': fingerprint}, indent=2) + '\n')
    return ''.join(output)


def verify_sources():
    manifest = ROOT / 'website/locales/sources.json'
    if not manifest.exists():
        raise ValueError('Missing reviewed translation source manifest')
    records = json.loads(manifest.read_text())
    if set(records) != set(translation_sources()):
        raise ValueError('Translation coverage differs from the English source inventory')
    for path, digest in records.items():
        if hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != digest:
            raise ValueError('Chinese translation needs synchronization: ' + path)
        verify_pair(ROOT / path)


def translation_sources():
    return sorted(str(p.relative_to(ROOT)) for p in (ROOT / 'docs').rglob('*')
                  if p.suffix in {'.md', '.svg'} and '.zh.' not in p.name
                  and p.name != 'progress.md')


def verify_pair(source):
    translated = source.with_suffix('.zh' + source.suffix)
    if not translated.is_file():
        raise ValueError('Missing Chinese translation: ' + str(translated.relative_to(ROOT)))
    if source.suffix == '.svg':
        left, right = list(ET.parse(source).iter()), list(ET.parse(translated).iter())
        if len(left) != len(right) or any(a.tag != b.tag or a.attrib != b.attrib
                                        for a, b in zip(left, right)):
            raise ValueError('Localized SVG geometry differs: ' + source.name)
        return
    english, chinese = source.read_text(), translated.read_text()
    # Facts inside code examples must not change during translation.
    fences = lambda s: [(lang, body) for lang, body in re.findall(
        r'^```([^\n]*)\n(.*?)^```[^\n]*$', s, flags=re.M | re.S)
        if lang.strip() != 'mermaid']
    if fences(english) != fences(chinese):
        raise ValueError('Localized code example differs: ' + source.name)
    links = lambda s: Counter(re.findall(r'\]\(([^)]+)\)', s))
    if links(english) - links(chinese):
        raise ValueError('Localized reference was lost: ' + source.name)
    aligned_anchors(english, chinese, source.relative_to(ROOT))


@event_priority(100)
def on_config(config):
    global STAGING
    i18n = config.plugins.get('i18n')
    if STAGING is None or not i18n.building:
        if STAGING is not None:
            STAGING.cleanup()
        verify_sources()
        STAGING = tempfile.TemporaryDirectory(prefix='zlib-reading-')
        staged = Path(STAGING.name)
        shutil.copytree(ROOT / 'docs', staged, dirs_exist_ok=True)
        for language in ['', '.zh']:
            source = staged / ('overview' + language + '.md')
            if source.exists():
                source.rename(staged / ('index' + language + '.md'))
        (staged / 'progress.zh.md').write_text(localized_progress(
            (ROOT / 'docs/progress.md').read_text()))
        for chinese in staged.rglob('*.zh.md'):
            english = chinese.with_name(chinese.name.replace('.zh.md', '.md'))
            if english.exists():
                chinese.write_text(aligned_anchors(english.read_text(), chinese.read_text(),
                                                  chinese.relative_to(staged)))
        (staged / 'assets').mkdir(exist_ok=True)
        for name in ['reading.css', 'diagrams.js']:
            shutil.copyfile(ROOT / 'website' / name, staged / 'assets' / name)
    config.docs_dir = STAGING.name
    return config


def on_page_markdown(markdown, page, config, files):
    markdown = without_contents(markdown)
    normalized = getattr(page.file, 'norm_src_uri', page.file.src_uri)
    source = ROOT / 'docs' / normalized
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


def on_page_context(context, page, config, nav):
    normalized = getattr(page.file, 'norm_src_uri', page.file.src_uri)
    if normalized == 'index.md':
        path = 'overview.zh.md' if page.file.locale == 'zh' else 'overview.md'
    elif normalized == 'progress.md':
        path = 'progress.md'
    else:
        path = page.file.src_uri
    page.edit_url = config.repo_url.rstrip('/') + '/edit/main/docs/' + path
    return context


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description='Record reviewed bilingual source pairs.')
    parser.add_argument('--refresh-sources', action='store_true', required=True)
    parser.parse_args()
    records = {}
    for path in translation_sources():
        verify_pair(ROOT / path)
        records[path] = hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
    localized_progress((ROOT / 'docs/progress.md').read_text(), check_coverage=False)
    (ROOT / 'website/locales/sources.json').write_text(
        json.dumps(records, ensure_ascii=False, indent=2, sort_keys=True) + '\n')
    print(f'Recorded {len(records)} reviewed source pairs; review translation meaning separately.')
