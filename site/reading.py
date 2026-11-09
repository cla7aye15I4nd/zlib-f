"""A reading map and a connected, bilingual chapter sequence."""
from pathlib import Path
from hashlib import sha256
from urllib.parse import urlsplit
import html
import re

from markdown import Markdown
from reference import OUT, SITE, REPO, doc_path, href, write
from routes import UNITS, UNIT_BY_KEY, CHAPTER_BY_KEY, UNIT_FOR_CHAPTER
from navigation import global_contents
from codec_trace import render_trace
from book import BOOK, BY_KEY, APPENDICES, CHECKSUM_PARTS, LEGACY, SUPPLEMENTS, TOPICS, OVERVIEW, resolve_route, chapter_source

TITLES={key:item['title'] for key,item in CHAPTER_BY_KEY.items()}
TITLES['interfaces'] = ('压缩调用与接口地图', 'Compression calls and the API map')


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
    styles += ['zlib-playground.css']
    names += styles+['diagram-view.mjs']
    names += ['zlib-playground.js','zlib-playground-model.mjs','zlib-playground-worker.js']
    names += [p.name for p in (SITE/'static').glob('zlib-*-scene.*')]
    names += [p.name for p in (SITE/'static').glob('zlib-*-model.mjs')]
    revision=sha256(b''.join((SITE/'static'/n).read_bytes() for n in sorted(set(names)))).hexdigest()[:12]
    css=''.join(f'<link rel="stylesheet" href="{asset(n)}?v={revision}">' for n in styles)
    scripts=f'<script type="module" src="{asset("zlib-essay.js")}?v={revision}"></script>'+''.join(f'<script defer src="{asset(n)}?v={revision}"></script>' for n in ['reference.js','book.js','navigation.js'])
    eyebrow=f'{number:02} / 06' if number else t('参考','REFERENCE')
    return f'''<!doctype html><html lang="{lang}"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>{html.escape(title)} · zlib × Lean</title><link rel="icon" href="{asset('favicon.svg')}" type="image/svg+xml">{css}{scripts}</head><body><a class="zl-skip" href="#content">{t('跳到正文','Skip to content')}</a><main class="zl-page bk-page bk-book"><nav class="article-topbar"><a class="article-brand" href="{link('index',current,lang)}">zlib × Lean</a><div><a data-language href="{href(other,current)}">{t('English','中文')}</a></div></nav><header class="bk-hero bk-hero-chapter"><span class="bk-eyebrow">{eyebrow}</span><h1>{html.escape(title)}</h1></header><article id="content" class="bk-article" data-book-chapter="{number or 'reference'}">{body}</article></main>{global_contents(current,lang,title,toc)}</body></html>'''


def render_chapter(item,lang,number):
    current=page_path(item['route'],lang)
    body,toc=markdown(chapter_source(item['key'],lang),current,lang)
    if item['key']=='deflate-matching':
        for anchor,comparison in [('hash','window'),('lazy','search')]:
            marker=f'<h2 id="{anchor}">'
            body=body.replace(marker,render_trace(current,lang,comparison)+marker,1)
    if item['key']=='deflate-output':
        marker='<h2 id="flush">'
        body=body.replace(marker,render_trace(current,lang,'storage')+marker,1)
    if item['key']=='round-trip':
        import json
        redirects={}
        for key in OVERVIEW:
            route,anchor=resolve_route('algorithms/index',key)
            redirects[key]=link(route,current,lang,anchor)
        redirects.update({'algorithms':link('index',current,lang,'task'),'verification':link('read/stream-lifetime',current,lang,'composition'),'algorithm-map':link('index',current,lang,'task')})
        existing=set(re.findall(r'\bid="([^"]+)"',body))
        body+=''.join(f'<span id="{anchor}" hidden></span>' for anchor in redirects if anchor not in existing)
        body+='<script type="application/json" id="bk-legacy-links">'+json.dumps(redirects)+'</script>'
    write(current,shell(label(item['title'],lang),body,item['route'],lang,toc=toc,number=number))


def prefixed(text,key):
    text=re.sub(r'^(#{2,5}) ',lambda m:'#'+m.group(1)+' ',text,flags=re.M)
    text=re.sub(r'\{#([^}]+)\}',lambda m:'{#'+key+'-'+m.group(1)+'}',text)
    text=re.sub(r'href="#([^\"]+)"',lambda m:'href="#'+key+'-'+m.group(1)+'"',text)
    text=re.sub(r'\]\(#([^)]+)\)',lambda m:'](#'+key+'-'+m.group(1)+')',text)
    paragraphs=text.split('\n\n')
    if paragraphs and re.search(r'下一章|接下来进入|The next chapter|Continue to',paragraphs[-1]):paragraphs.pop()
    return '\n\n'.join(paragraphs)


def render_appendix(key,lang):
    current=page_path('appendix/'+key,lang);t=lambda a,b:a if lang=='zh' else b
    titles={c['key']:label(c['title'],lang) for c in CHAPTER_BY_KEY.values()}
    if key=='checksums':
        text=t('zlib 的尾部保存 Adler-32，gzip 的尾部保存 CRC-32。这里从字节更新开始，推导分批处理与独立分块组合，并展开优化与证明。','Zlib trailers carry Adler-32; gzip trailers carry CRC-32. Start with byte updates, derive incremental processing and independent chunk combination, then open the optimizations and proofs.')
        parts=['adler','crc','checksum-proof']
    else:
        text=t('完整缓冲区、自定义读取回调与 gzip 文件，交给应用的是不同的控制方式。以下分别沿真实调用、返回结果与资源归属展开。','Complete buffers, custom input callbacks and gzip files give the application different forms of control. Follow each through actual calls, results and resource ownership.')
        parts=['buffers','callbacks','gzip','interfaces-proof']
    for part in parts:
        text+=f'\n\n## {titles[part]} {{#{part}}}\n\n'+prefixed((SITE/'content/sample'/f'{part}.{lang}.md').read_text(),part)
    body,toc=markdown(text,current,lang)
    title=next(t(cn,en) for k,cn,en in APPENDICES if k==key)
    write(current,shell(title,body,'appendix/'+key,lang,toc=toc))
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
        for key,_,_ in APPENDICES:render_appendix(key,lang)
        checksum_ids=set(CHECKSUM_PARTS)
        for key in CHECKSUM_PARTS:
            checksum_ids.update(key+'-'+anchor for anchor in old_ids((SITE/'content/sample'/f'{key}.{lang}.md').read_text()))
        render_redirect('appendix/checksums',lang,checksum_ids)
        article_ids=old_ids((SITE/'content'/f'article.{lang}.md').read_text())
        for route in ['algorithms/index','verification/index']:render_redirect(route,lang,article_ids)
        for unit in UNITS:
            source=SITE/'content/topics'/f'{unit["key"]}.{lang}.md'
            render_redirect('verification/'+unit['key'],lang,old_ids(source.read_text()) if source.exists() else ())
        for key in [*CHAPTER_BY_KEY,'interfaces']:
            ids=old_ids((SITE/'content/sample'/f'{key}.{lang}.md').read_text())
            render_redirect('chapters/'+key,lang,ids)
            if key in ['blocks','bits','storage','proof','interfaces']:render_redirect('sample/'+key,lang,ids)
        render_redirect('read/round-trip',lang,old_ids((SITE/'content/book'/f'round-trip.{lang}.md').read_text()))
    print('Built six bilingual implementation chapters with checksum algorithms, an interface appendix, and compatible published links')
