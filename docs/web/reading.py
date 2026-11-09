"""Three bilingual zlib essays, with separate technical references."""
from pathlib import Path
from hashlib import sha256
from urllib.parse import urlsplit
import html
import re

from markdown import Markdown
from reference import OUT, SITE, REPO, doc_path, href, write
from routes import UNITS, CHAPTER_BY_KEY
from navigation import global_contents
from codec_trace import render_trace
from book import BOOK, OLD_BOOK, OVERVIEW, resolve_route, chapter_source


def label(pair, lang):
    return pair[lang == 'en']


def page_path(route, lang):
    return OUT / (route + ('.zh.html' if lang == 'zh' else '.html'))


def link(route, current, lang, anchor=''):
    return href(page_path(route, lang), current) + ('#' + anchor if anchor else '')


def localize(body, current, lang):
    """Resolve author-facing project URLs without escaping the Pages subpath."""
    def replace(match):
        raw = html.unescape(match.group(1))
        url = urlsplit(raw)
        if url.netloc == 'github.com' and '/zlib-f/blob/main/docs/' in url.path:
            source = REPO/'docs'/url.path.split('/zlib-f/blob/main/docs/', 1)[1]
            target = doc_path(source, lang)
        elif raw.startswith('/static/'):
            target=OUT/url.path.lstrip('/')
        elif (raw.startswith('/') or raw.startswith('./reference/')) and url.path.endswith('.html'):
            path = url.path.removeprefix('./').lstrip('/')
            if path.endswith('.zh.html'):
                path = path[:-8] + '.html'
            if path.startswith('reference/docs/'):
                target = doc_path(REPO/(path[len('reference/'): -5]+'.md'), lang)
            else:
                resolved,fragment=resolve_route(path[:-5],url.fragment)
                target=page_path(resolved,lang)
                url=url._replace(fragment=fragment)
        else:
            return match.group(0)
        result = href(target, current)
        if url.query:
            result += '?' + url.query
        if url.fragment:
            result += '#' + url.fragment
        return 'href="' + html.escape(result, quote=True) + '"'
    return re.sub(r'href="([^"]+)"', replace, body)


def markdown(text, current, lang):
    def example(match):
        name,part=match.groups()
        source=(SITE/'static/examples'/(name+'.c')).read_text()
        start='/* BEGIN '+part+' */';end='/* END '+part+' */'
        if source.count(start)!=1 or source.count(end)!=1:
            raise ValueError('Missing example fragment: '+name+'#'+part)
        import textwrap
        code=textwrap.dedent(source.split(start,1)[1].split(end,1)[0]).strip()
        return '\n```c\n'+code+'\n```\n'
    text=re.sub(r'<!-- example:([a-z0-9-]+)#([a-z0-9-]+) -->',example,text)
    parser = Markdown(extensions=['fenced_code', 'tables', 'attr_list', 'toc', 'md_in_html', 'footnotes'])
    return localize(parser.convert(text), current, lang), parser.toc


def shell(title,body,route,lang,*,toc='',number=None):
    current=page_path(route,lang);other=page_path(route,'en' if lang=='zh' else 'zh')
    t=lambda a,b:a if lang=='zh' else b
    asset=lambda name:href(OUT/'static'/name,current)
    names=['book.css','book.js','navigation.css','navigation.js','zlib-essay.js','reference.js','syntax.css']
    styles=['base.css','zlib-essay.css','zlib-search.css','zlib-lookup.css','zlib-overlay.css','zlib-table-proof.css','layout.css','reference.css','book.css','navigation.css','syntax.css']
    styles += [f'zlib-{scene}-scene.css' for scene in ['roundtrip','refill','blockcost','lengths','fastpath','checkpoint']]
    styles += ['zlib-playground.css','minimal-codec.css','deflate-format.css']
    names += styles+['diagram-view.mjs']
    names += ['zlib-playground.js','zlib-playground-model.mjs','zlib-playground-worker.js','minimal-codec.js','minimal-codec-model.mjs','deflate-format.js','deflate-format-model.mjs']
    names += [p.name for p in (SITE/'static').glob('zlib-*-scene.*')]
    names += [p.name for p in (SITE/'static').glob('zlib-*-model.mjs')]
    revision=sha256(b''.join((SITE/'static'/n).read_bytes() for n in sorted(set(names)))).hexdigest()[:12]
    css=''.join(f'<link rel="stylesheet" href="{asset(n)}?v={revision}">' for n in styles)
    scripts=f'<script type="module" src="{asset("zlib-essay.js")}?v={revision}"></script>'+''.join(f'<script defer src="{asset(n)}?v={revision}"></script>' for n in ['reference.js','book.js','navigation.js'])
    eyebrow=f'{number:02} / {len(BOOK):02}' if number else t('参考','REFERENCE')
    return f'''<!doctype html><html lang="{lang}"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>{html.escape(title)} · zlib × Lean</title><link rel="icon" href="{asset('favicon.svg')}" type="image/svg+xml">{css}{scripts}</head><body><a class="zl-skip" href="#content">{t('跳到正文','Skip to content')}</a><main class="zl-page bk-page bk-book"><nav class="article-topbar"><a class="article-brand" href="{link('index',current,lang)}">zlib × Lean</a><div><a data-language href="{href(other,current)}">{t('English','中文')}</a></div></nav><header class="bk-hero bk-hero-chapter"><span class="bk-eyebrow">{eyebrow}</span><h1>{html.escape(title)}</h1></header><article id="content" class="bk-article" data-book-chapter="{number or 'reference'}">{body}</article></main>{global_contents(current,lang,title,toc)}</body></html>'''


def render_chapter(item,lang,number):
    import json
    current=page_path(item['route'],lang)
    source=chapter_source(item['key'],lang)
    for comparison in ['window','search','storage']:
        source=source.replace('<!-- comparison:'+comparison+' -->',render_trace(current,lang,comparison))
    body,toc=markdown(source,current,lang)
    if item['route']=='index':
        old_source=(SITE/'content/book'/f'round-trip.{lang}.md').read_text()
        existing=set(re.findall(r'\bid="([^"]+)"',body))
        redirects={}
        for anchor in set(OVERVIEW)|old_ids(old_source):
            if anchor in existing:continue
            route,fragment=resolve_route('read/round-trip',anchor)
            redirects[anchor]=link(route,current,lang,fragment)
        body+=''.join(f'<span id="{anchor}" hidden></span>' for anchor in sorted(redirects))
        body+='<script type="application/json" id="bk-legacy-links">'+json.dumps(redirects)+'</script>'
    write(current,shell(label(item['title'],lang),body,item['route'],lang,toc=toc,number=number))


def old_ids(source):
    parser=Markdown(extensions=['fenced_code','tables','attr_list','toc'])
    return set(re.findall(r'\bid="([^\"]+)"',parser.convert(source)))


def render_redirect(route,lang,ids=()):
    import json
    current=page_path(route,lang)
    def destination(anchor=''):
        target,fragment=resolve_route(route,anchor)
        return link(target,current,lang,fragment)
    mapping={'':destination()}
    mapping.update({anchor:destination(anchor) for anchor in ids})
    title='章节已合并' if lang=='zh' else 'Chapter merged'
    anchors=''.join(f'<span id="{html.escape(anchor,quote=True)}" hidden></span>' for anchor in sorted(ids))
    script='''const map=JSON.parse(document.getElementById('bk-redirect-data').textContent);const dest=new URL(map[decodeURIComponent(location.hash.slice(1))]||map[''],location.href);for(const [key,value] of new URLSearchParams(location.search))if(!dest.searchParams.has(key))dest.searchParams.append(key,value);location.replace(dest.href);'''
    document=f'<!doctype html><html lang="{lang}" data-book-redirect><head><meta charset="utf-8"><title>{title}</title><link rel="canonical" href="{mapping[""]}"></head><body><h1>{title}</h1><p><a href="{mapping[""]}">{"继续阅读" if lang=="zh" else "Continue reading"} →</a></p>{anchors}<script type="application/json" id="bk-redirect-data">{json.dumps(mapping)}</script><script>{script}</script></body></html>'
    write(current,document)


def build_reading():
    for lang in ('en','zh'):
        for number,item in enumerate(BOOK,1):render_chapter(item,lang,number)
        for key in OLD_BOOK:
            source=(SITE/'content/book'/f'{key}.{lang}.md').read_text()
            ids=old_ids(source)
            if key=='inflate-copy':
                ids.update(old_ids((SITE/'content/book'/f'checksums-section.{lang}.md').read_text()))
            render_redirect('read/'+key,lang,ids)
        for appendix,parts in [('checksums',['adler','crc','checksum-proof']),('interfaces',['buffers','callbacks','gzip','interfaces-proof'])]:
            ids=set(parts)
            for part in parts:
                ids.update(part+'-'+anchor for anchor in old_ids((SITE/'content/sample'/f'{part}.{lang}.md').read_text()))
            render_redirect('appendix/'+appendix,lang,ids)
        article_ids=old_ids((SITE/'content'/f'article.{lang}.md').read_text())
        for route in ['algorithms/index','verification/index']:render_redirect(route,lang,article_ids)
        for unit in UNITS:
            source=SITE/'content/topics'/f'{unit["key"]}.{lang}.md'
            render_redirect('verification/'+unit['key'],lang,old_ids(source.read_text()) if source.exists() else ())
        for key in [*CHAPTER_BY_KEY,'interfaces']:
            ids=old_ids((SITE/'content/sample'/f'{key}.{lang}.md').read_text())
            render_redirect('chapters/'+key,lang,ids)
            if key in ['blocks','bits','storage','proof','interfaces']:render_redirect('sample/'+key,lang,ids)
    print('Built three bilingual zlib essays; public API and formal references remain separate')
