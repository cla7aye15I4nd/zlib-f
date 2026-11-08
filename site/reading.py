"""A reading map and a connected, bilingual chapter sequence."""
from pathlib import Path
from hashlib import sha256
from urllib.parse import urlsplit
import html
import re

from markdown import Markdown
from reference import OUT, SITE, REPO, doc_path, href, write

CHAPTERS = [
    ('blocks', ('块选择与符号成本', 'Block selection and symbol costs'),
     ('从同一组符号出发，比较三种块的完整成本。', 'Compare three complete block representations for the same symbols.'),
     ('符号 → 压缩块', 'Symbols → block'), 'blocks'),
    ('bits', ('位输出与字节缓冲', 'Bit output and byte buffering'),
     ('把选中的编码逐步写入 bi_buf，跟踪每个输出字节。', 'Write the chosen codes through bi_buf and follow every emitted byte.'),
     ('编码 → 待发送字节', 'Codes → pending bytes'), 'bit-order'),
    ('storage', ('共享存储与输出前缀', 'Shared storage and output prefixes'),
     ('读符号与写字节共用内存，沿途保持尚未读取的内容。', 'Read symbols and write bytes in one allocation while preserving unread records.'),
     ('读游标 → 写边界', 'Read cursor → write boundary'), 'blocks'),
    ('proof', ('压缩输出的证明思路', 'The output proof argument'),
     ('把符号含义、位串和真实内存连接成同一条论证。', 'Connect symbol meaning, bits, and actual memory in one argument.'),
     ('算法事实 → 实现结论', 'Algorithm facts → implementation result'), 'blocks'),
]
TITLES = {key: title for key, title, *_ in CHAPTERS}
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
                target = page_path(path[:-5], lang)
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
    parser = Markdown(extensions=['fenced_code', 'tables', 'attr_list', 'toc'])
    return localize(parser.convert(text), current, lang), parser.toc


def shell(title, body, route, lang, *, active='', subtitle='', toc='', overview=False):
    current = page_path(route, lang)
    other = page_path(route, 'en' if lang == 'zh' else 'zh')
    t = lambda a, b: a if lang == 'zh' else b
    asset = lambda name: href(OUT/'static'/name, current)
    root = link('index', current, lang)
    algorithm = link('algorithms/index', current, lang)
    verification = link('verification/index', current, lang)
    api = link('reference/api', current, lang)
    revision = sha256(b''.join((SITE/'static'/name).read_bytes() for name in ['book.css', 'book.js'])).hexdigest()[:12]
    side = ''
    if active:
        side = '<aside class="bk-side"><span class="bk-eyebrow">'+t('压缩输出 · 精读路线', 'COMPRESSION OUTPUT')+'</span><ol>'
        for key, heading, *_ in CHAPTERS:
            selected = ' aria-current="page"' if active == key else ''
            side += f'<li><a{selected} href="{link("sample/"+key,current,lang)}">{label(heading,lang)}</a></li>'
        side += '</ol>' + ('<nav aria-label="'+t('本页目录', 'On this page')+'">'+toc+'</nav>' if toc else '')
        side += f'<a class="bk-side-api" href="{link("sample/interfaces",current,lang)}">{t("压缩调用与接口地图", "Calls and API map")} ↗</a></aside>'
    title_markup = 'zlib <span>×</span> Lean' if route == 'index' else html.escape(title)
    hero_class = 'bk-hero-home' if route == 'index' else 'bk-hero-chapter'
    first_active = route.startswith('algorithms/') or active == 'interfaces'
    second_active = route.startswith('verification/') or (active and active != 'interfaces')
    readingbar = f'''<nav class="bk-navigation" aria-label="{t('阅读分部','Reading parts')}">
<a {'aria-current="page"' if first_active else ''} href="{algorithm}"><small>01</small>{t('算法与接口','Algorithms & interfaces')}</a>
<a {'aria-current="page"' if second_active else ''} href="{verification}"><small>02</small>{t('算法精读与验证','Algorithm detail & verification')}</a>
<a class="bk-nav-api" href="{api}">API</a><a href="{root}">{t('阅读地图','Reading map')} ↗</a></nav>'''
    return f'''<!doctype html><html lang="{lang}"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>{html.escape(title) if route == "index" else html.escape(title)+" · zlib × Lean"}</title><meta name="description" content="{html.escape(subtitle,quote=True)}">
<link rel="icon" href="{asset('favicon.svg')}" type="image/svg+xml">
<link rel="stylesheet" href="{asset('base.css')}"><link rel="stylesheet" href="{asset('zlib-essay.css')}"><link rel="stylesheet" href="{asset('zlib-search.css')}"><link rel="stylesheet" href="{asset('zlib-lookup.css')}"><link rel="stylesheet" href="{asset('zlib-overlay.css')}"><link rel="stylesheet" href="{asset('zlib-table-proof.css')}"><link rel="stylesheet" href="{asset('layout.css')}"><link rel="stylesheet" href="{asset('reference.css')}"><link rel="stylesheet" href="{asset('book.css')}?v={revision}">
<script type="module" src="{asset('zlib-essay.js')}?v={revision}"></script><script defer src="{asset('reference.js')}?v={revision}"></script><script defer src="{asset('book.js')}?v={revision}"></script></head>
<body><a class="zl-skip" href="#content">{t('跳到正文','Skip to content')}</a>
<main class="zl-page bk-page{' bk-overview zlib-essay' if overview else ''}">
<nav class="article-topbar"><a class="article-brand" href="{root}">I Have Nothing</a><div><a href="https://www.dataisland.org/blog/">{t('博客','Writing')}</a><a data-language href="{href(other,current)}">{t('English','中文')}</a></div></nav>
<header class="bk-hero {hero_class}"><div class="bk-eyebrow">{t('阅读地图' if route == 'index' else 'ZLIB × LEAN / '+('算法与接口' if first_active else '算法精读与验证'), 'READING MAP' if route == 'index' else 'ZLIB × LEAN / '+('ALGORITHMS & INTERFACES' if first_active else 'ALGORITHM DETAIL & VERIFICATION'))}</div><h1>{title_markup}</h1><p>{subtitle}</p></header>
{readingbar}<div class="bk-layout{' bk-with-side' if side else ''}"><article id="content" class="{'article-body' if overview else 'bk-article'}" {'data-overview="true"' if overview else ''}>{body}</article>{side}</div>
<footer class="zl-footer"><a href="{root}">zlib × Lean</a><a href="{api}">{t('完整 API 契约','Complete API contracts')}</a><a href="{link('reference/proofs',current,lang)}">{t('实现论证与源码','Arguments and source')} ↗</a></footer></main></body></html>'''


def chapter_ladder(current, lang):
    body = '<ol class="bk-ladder">'
    for i, (key, title, desc, transformation, _) in enumerate(CHAPTERS):
        body += f'<li><a href="{link("sample/"+key,current,lang)}"><small>0{i+1}</small><div><span>{label(transformation,lang)}</span><h3>{label(title,lang)}</h3><p>{label(desc,lang)}</p></div><b>↗</b></a></li>'
    return body+'</ol>'


def render_home(lang):
    current = page_path('index',lang)
    t = lambda a,b:a if lang=='zh' else b
    body = f'''<div class="bk-orientation"><p>{t('这份文档有两条阅读路线。第一条沿着字节、符号和调用理解 zlib；第二条进入具体实现，先拆开算法与优化，再解释证明怎样连接起来。','There are two reading routes. The first follows bytes, symbols, and calls through zlib. The second opens the implementation, explains its algorithms and optimizations, then develops the proof argument.')}</p><p>{t('可以先完整读一遍概览，也可以从熟悉的主题进入精读。每一页都给出前置背景、下一步，以及对应的完整契约和实现论证。','Read the overview straight through, or enter a detailed chapter from a familiar topic. Chapters link their background, next step, complete contracts, and implementation arguments.')}</p></div>
<div class="bk-parts"><section id="algorithms"><span class="bk-number">01</span><h2>{t('算法与接口','Algorithms & interfaces')}</h2><p>{t('从重复字节到压缩流，再回到调用者手中的字节。先建立全局认识，再查具体接口。','From repetition to a compressed stream and back to caller-owned bytes. Build the overall picture, then consult exact interfaces.')}</p><a href="{link('algorithms/index',current,lang)}">{t('阅读算法概览','Read the algorithm overview')} →</a><a href="{link('sample/interfaces',current,lang)}">{t('查看调用与接口地图','Explore calls and interfaces')} ↗</a></section>
<section id="verification"><span class="bk-number">02</span><h2>{t('算法精读与形式化验证','Algorithm detail and formal verification')}</h2><p>{t('沿一条实现路径深入：数据怎样布局，优化怎样工作，最后需要证明哪些事实。','Follow an implementation path: how data is laid out, how optimizations work, and which facts the proof must establish.')}</p><a href="{link('verification/index',current,lang)}">{t('进入压缩输出的精读路线','Follow the compression-output route')} →</a><a href="{link('reference/proofs',current,lang)}">{t('查阅其他组件的完整论证','Consult the other component arguments')} ↗</a></section></div>
<section class="bk-sample-intro"><div><span class="bk-eyebrow">{t('沿着同一份数据深入','FOLLOW THE SAME DATA')}</span><h2>{t('从三个符号到五个字节','Three symbols, five bytes')}</h2></div><p>{t('本组精读从 A、B 和一个长度 6、距离 2 的匹配开始。先选择块的表示，再写出比特，接着追踪共用内存的读写，最后把这些算法事实连接成证明。','This detailed route starts with A, B, and a length-6, distance-2 match. Choose the block representation, emit its bits, follow reads and writes in shared memory, then connect those facts into a proof.')}</p></section>
{chapter_ladder(current,lang)}
<section class="bk-connections"><h2>{t('概览与精读的连接','From overview to detailed reading')}</h2><table><thead><tr><th>{t('概览中的主题','Overview topic')}</th><th>{t('深入实现','Implementation detail')}</th><th>{t('对应论证','Proof connection')}</th></tr></thead><tbody>
<tr><td><a href="{link('algorithms/index',current,lang,'blocks')}">{t('块类型与成本','Block types and costs')}</a></td><td><a href="{link('sample/blocks',current,lang)}">{t('符号账目与三种块的成本','Symbol accounting and block costs')}</a></td><td><a href="{link('sample/proof',current,lang)}">{t('符号与格式的含义','Symbol and format meaning')}</a></td></tr>
<tr><td><a href="{link('algorithms/index',current,lang,'bit-order')}">{t('位序与位缓冲','Bit order and buffers')}</a></td><td><a href="{link('sample/bits',current,lang)}">bi_buf / bi_valid / pending</a></td><td><a href="{link('sample/proof',current,lang)}">{t('写入前后的位串关系','The bitstring across a write')}</a></td></tr>
<tr><td><a href="{link('algorithms/index',current,lang,'stream')}">{t('流式调用','Streaming calls')}</a></td><td><a href="{link('sample/storage',current,lang)}">{t('共享存储与输出交付','Shared storage and output delivery')}</a></td><td><a href="{link('sample/proof',current,lang)}">{t('前缀界与跨调用连接','Prefix bounds and call composition')}</a></td></tr></tbody></table></section>
<section class="bk-reference-strip"><h2>{t('完整参考','Complete reference')}</h2><p>{t('接口定义域、返回值和错误路径在函数页完整保留；引擎论证和 Lean 正文可以沿章节继续查阅。','Function pages retain complete domains, results, and error paths. Follow chapter links into component arguments and Lean proof bodies.')}</p><div><a href="{link('reference/api',current,lang)}">{t('全部公开 API','All public APIs')} ↗</a><a href="{link('reference/proofs',current,lang)}">inflate / deflate ↗</a><a href="{link('reference/index',current,lang)}">{t('文档索引','Documentation index')} ↗</a></div></section>'''
    subtitle = t('沿着数据读算法，沿着实现读证明。','Follow the data through the algorithm. Follow the implementation through the proof.')
    output = shell('zlib × Lean',body,'index',lang,subtitle=subtitle)
    # Keep previously published section links useful after the reading-map change.
    ids = ['bytes','layers','search','lazy','huffman-tree','canonical','blocks','bit-order','lookup','stream']
    redirects = {key:link('algorithms/index',current,lang,key) for key in ids}
    for key in ['write-proof','table-proof','overlay','huffman-bound','history-proof','ownership','trust','reading','verifying-zlib']:
        redirects[key]=link('sample/storage' if key=='overlay' else 'verification/index',current,lang)
    redirects['how-zlib-works']=link('algorithms/index',current,lang)
    import json
    output=output.replace('</article>', '<script type="application/json" id="bk-legacy-links">'+json.dumps(redirects)+'</script></article>',1)
    write(current,output)


def render_overview(lang):
    current=page_path('algorithms/index',lang)
    original=(SITE/'content'/f'article.{lang}.md').read_text()
    original=original.split('# ',1)[1].split('\n',1)[1]
    original=original.split('\n# ',1)[0]
    body,toc=markdown(original,current,lang)
    t=lambda a,b:a if lang=='zh' else b
    body=f'<div class="bk-overview-note"><p>{t("这条路线先讲算法的整体形状。需要更细的实现时，从章内链接进入精读；完整函数约定仍可随时查阅。","This route establishes the overall algorithm. Follow the chapter links for detailed implementation reading; complete function contracts remain available throughout.")}</p></div>'+body
    # Add specific bridges at the point where the overview introduces a mechanism.
    for anchor,dest,cn,en in [('blocks','blocks','精读：符号账目与块选择','Detailed reading: symbols and block selection'),('bit-order','bits','精读：16 位输出缓冲与逐字节执行','Detailed reading: the 16-bit writer, step by step'),('stream','interfaces','继续：调用过程与接口地图','Continue: calls and the API map')]:
        marker=re.search(r'<h2 id="'+anchor+r'">.*?</h2>',body)
        if marker:
            bridge=f'<a class="bk-inline-bridge" href="{link("sample/"+dest,current,lang)}">{t(cn,en)} ↗</a>'
            body=body[:marker.end()]+bridge+body[marker.end():]
    body+=f'<div class="bk-next"><span>{t("下一条路线","NEXT ROUTE")}</span><a href="{link("verification/index",current,lang)}">{t("压缩输出的算法精读与证明","Compression output: implementation and proof")} →</a></div>'
    write(current,shell(t('zlib 的算法与接口','Zlib algorithms and interfaces'),body,'algorithms/index',lang,subtitle=t('先理解输入怎样变成压缩流，再理解解压器怎样恢复原文。','First understand how input becomes a compressed stream, then how the decoder recovers it.'),overview=True))


def render_verification(lang):
    current=page_path('verification/index',lang)
    t=lambda a,b:a if lang=='zh' else b
    body=f'''<div class="bk-route-intro"><p>{t('压缩器已经决定用两个字面量 A、B 和一个匹配表示 ABABABAB。接下来的任务是把这三个符号写成合法压缩块，并在输出空间不足时正确暂停。','The compressor has chosen two literals, A and B, and one match to represent ABABABAB. The next task is to encode those symbols as a valid block and pause correctly if output space runs out.')}</p><p>{t('这条路线从这个具体任务出发。前三篇逐步展开算法、数据布局和优化；第四篇使用已经建立的背景解释证明思路。每一步的输出，都是下一步的输入。','This route starts with that concrete task. The first three chapters open the algorithms, layouts, and optimizations. The fourth uses that background to explain the proof. Each step produces the next step’s input.')}</p></div>
<div class="bk-route-legend"><span><i></i>{t('01—03 算法精读','01—03 IMPLEMENTATION DETAIL')}</span><span><i></i>{t('04 证明思路','04 PROOF ARGUMENT')}</span></div>
{chapter_ladder(current,lang)}
<div class="bk-route-foundation"><h2>{t('这条路线的起点','Before this route')}</h2><p>{t('需要先认识字面量、长度与距离，以及 Huffman 编码。概览中的例子已经足够开始；遇到 API 的状态和返回码，可以转入调用地图。','Begin with literals, lengths and distances, and Huffman codes. The overview examples provide the background. For API states and return codes, use the call map.')}</p><a href="{link('algorithms/index',current,lang,'bytes')}">{t('字面量与回引用','Literals and back-references')} ↗</a><a href="{link('algorithms/index',current,lang,'canonical')}">{t('规范 Huffman 编码','Canonical Huffman codes')} ↗</a><a href="{link('sample/interfaces',current,lang)}">{t('压缩调用与接口地图','Compression calls and API map')} ↗</a></div>
<div class="bk-route-foundation"><h2>{t('其他组件的论证','Other component arguments')}</h2><p>{t('这组章节先完整展开压缩输出。解码表、快速解码、窗口和其他接口的现有完整论证仍可直接查阅。','These chapters develop compression output first. Complete existing arguments for decode tables, fast decoding, windows, and other interfaces remain available.')}</p><a href="{link('reference/proofs',current,lang)}">inflate / deflate ↗</a><a href="{link('reference/targets',current,lang)}">{t('精确命题与调用序列','Exact targets and call sequences')} ↗</a></div>'''
    write(current,shell(t('压缩输出的算法与证明','Compression output: algorithms and proof'),body,'verification/index',lang,subtitle=t('先拆开实现，再连接论证。','Open the implementation, then connect the argument.')))


def render_sample(key,lang):
    current=page_path('sample/'+key,lang)
    source=SITE/'content/sample'/f'{key}.{lang}.md'
    body,toc=markdown(source.read_text(),current,lang)
    t=lambda a,b:a if lang=='zh' else b
    if key=='interfaces':
        intro=t('把公开调用、引擎工作和字节交付放在同一张地图中。','Place public calls, engine work, and byte delivery on one map.')
        body=f'<p class="bk-chapter-context">{t("从这里查调用顺序与完整函数约定；沿引擎流程进入算法精读。","Use this page for call order and complete contracts; follow the engine stages into detailed algorithm reading.")}</p>'+body
        body+=f'<div class="bk-next"><span>{t("沿引擎继续","FOLLOW THE ENGINE")}</span><a href="{link("sample/blocks",current,lang)}">{label(TITLES["blocks"],lang)} →</a></div>'
    else:
        index=[c[0] for c in CHAPTERS].index(key)
        _,_,desc,_,overview_anchor=CHAPTERS[index]
        intro=label(desc,lang)
        previous=CHAPTERS[index-1][0] if index else None
        context=f'<div class="bk-chapter-context"><span>{"04 / PROOF" if key=="proof" else "0"+str(index+1)+" / IMPLEMENTATION"}</span>'
        context+=f'<a href="{link("sample/"+previous,current,lang) if previous else link("algorithms/index",current,lang,overview_anchor)}">{t("前置背景：","Background: ")}{label(TITLES[previous],lang) if previous else t("块类型与成本","Block types and costs")} ↗</a></div>'
        body=context+body
        if key!='proof':
            section,cn,en={'blocks':('meaning','把符号记录连接到格式含义','Connect symbol records to format meaning'),
                           'bits':('bitstream','把 pending 与 bi_buf 合成同一条位串','Combine pending and bi_buf into one bitstring'),
                           'storage':('prefix','逐前缀保持尚未读取的记录','Preserve unread records at every prefix')}[key]
            body+=f'<div class="bk-next bk-proof-bridge"><span>{t("这一机制的证明思路","THE PROOF CONNECTION")}</span><a href="{link("sample/proof",current,lang,section)}">{t(cn,en)} ↗</a></div>'
        else:
            for anchor,dest,background,cn,en in [('meaning','blocks','symbols','符号记录与块表示','Symbol records and block forms'),('bitstream','bits','register','十六位暂存寄存器','The 16-bit holding register'),('prefix','storage','boundary','移动的读取边界','The moving read boundary'),('dynamic','blocks','selection','块选择中的总成本','Total cost in block selection'),('composition','interfaces','accounting','输入与输出的交付记账','Input and output accounting')]:
                marker=re.search(r'<h2 id="'+anchor+r'">.*?</h2>',body)
                if marker:
                    bridge=f'<a class="bk-inline-bridge" href="{link("sample/"+dest,current,lang,background)}">{t("算法背景：","Algorithm background: ")}{t(cn,en)} ↗</a>'
                    body=body[:marker.end()]+bridge+body[marker.end():]
        nav='<nav class="bk-chapter-pagination" aria-label="'+t('章节顺序','Chapter order')+'">'
        if previous:
            nav+=f'<a href="{link("sample/"+previous,current,lang)}"><small>{t("上一章","PREVIOUS")}</small>← {label(TITLES[previous],lang)}</a>'
        if index<len(CHAPTERS)-1:
            following=CHAPTERS[index+1][0]
            nav+=f'<a href="{link("sample/"+following,current,lang)}"><small>{t("下一章","NEXT")}</small>{label(TITLES[following],lang)} →</a>'
        else:
            nav+=f'<a href="{link("reference/proofs",current,lang)}"><small>{t("继续查阅","CONTINUE")}</small>{t("完整实现论证与证明正文","Complete arguments and proof bodies")} ↗</a>'
        body+=nav+'</nav>'
    write(current,shell(label(TITLES[key],lang),body,'sample/'+key,lang,active=key,subtitle=intro,toc=toc))


def build_reading():
    for lang in ('en','zh'):
        render_home(lang)
        render_overview(lang)
        render_verification(lang)
        for key in ['blocks','bits','storage','proof','interfaces']:
            render_sample(key,lang)
    print('Built bilingual reading map, overview, route and five connected chapters')
