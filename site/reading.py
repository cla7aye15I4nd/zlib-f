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
from topology import topology, purpose_box

TITLES={key:item['title'] for key,item in CHAPTER_BY_KEY.items()}
TITLES['interfaces'] = ('压缩调用与接口地图', 'Compression calls and the API map')


def label(pair, lang):
    return pair[lang == 'en']


def page_path(route, lang):
    route=route.replace('sample/','chapters/',1) if route.startswith('sample/') else route
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
    revision = sha256(b''.join((SITE/'static'/name).read_bytes() for name in ['book.css', 'book.js','zlib-essay.js','zlib-writer.js','zlib-writer-model.mjs','navigation.css','navigation.js','topology.css','topology.js'])).hexdigest()[:12]
    side = ''
    if active:
        unit=UNIT_FOR_CHAPTER.get(active)
        unit_route=link('verification/'+unit['key'],current,lang) if unit else api
        side_title=label(unit['title'],lang) if unit else t('调用与公开接口','Calls and public APIs')
        side='<aside class="bk-side"><a class="bk-eyebrow" href="'+unit_route+'">'+side_title+' ↗</a>'
        side+='<details class="bk-unit-menu"><summary>'+t('选择主题','Choose a topic')+'</summary><ul>'
        for item in UNITS:
            side+=f'<li><a href="{link("verification/"+item["key"],current,lang)}">{label(item["title"],lang)}</a></li>'
        side+='</ul></details>'+('<ol>' if unit else '')
        for item in (unit['steps'] if unit else []):
            selected=' aria-current="page"' if active==item['key'] else ''
            side+=f'<li><a{selected} href="{link("sample/"+item["key"],current,lang)}">{label(item["title"],lang)}</a></li>'
        side+=('</ol>' if unit else '')+('<nav aria-label="'+t('本页目录','On this page')+'">'+toc+'</nav>' if toc else '')
        side+=f'<a class="bk-side-api" href="{api}">{t("完整 API 契约","Complete API contracts")} ↗</a></aside>'
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
<link rel="stylesheet" href="{asset('base.css')}?v={revision}"><link rel="stylesheet" href="{asset('zlib-essay.css')}?v={revision}"><link rel="stylesheet" href="{asset('zlib-search.css')}?v={revision}"><link rel="stylesheet" href="{asset('zlib-lookup.css')}?v={revision}"><link rel="stylesheet" href="{asset('zlib-overlay.css')}?v={revision}"><link rel="stylesheet" href="{asset('zlib-table-proof.css')}?v={revision}"><link rel="stylesheet" href="{asset('layout.css')}?v={revision}"><link rel="stylesheet" href="{asset('reference.css')}?v={revision}"><link rel="stylesheet" href="{asset('book.css')}?v={revision}">
<link rel="stylesheet" href="{asset('navigation.css')}?v={revision}"><link rel="stylesheet" href="{asset('topology.css')}?v={revision}">
<script type="module" src="{asset('zlib-essay.js')}?v={revision}"></script><script defer src="{asset('reference.js')}?v={revision}"></script><script defer src="{asset('book.js')}?v={revision}"></script><script defer src="{asset('navigation.js')}?v={revision}"></script><script defer src="{asset('topology.js')}?v={revision}"></script></head>
<body><a class="zl-skip" href="#content">{t('跳到正文','Skip to content')}</a>
<main class="zl-page bk-page{' bk-overview zlib-essay' if overview else ''}">
<nav class="article-topbar"><a class="article-brand" href="{root}">I Have Nothing</a><div><a href="https://www.dataisland.org/blog/">{t('博客','Writing')}</a><a data-language href="{href(other,current)}">{t('English','中文')}</a></div></nav>
<header class="bk-hero {hero_class}"><div class="bk-eyebrow">{t('阅读地图' if route == 'index' else 'ZLIB × LEAN / '+('算法与接口' if first_active else '算法精读与验证'), 'READING MAP' if route == 'index' else 'ZLIB × LEAN / '+('ALGORITHMS & INTERFACES' if first_active else 'ALGORITHM DETAIL & VERIFICATION'))}</div><h1>{title_markup}</h1><p>{subtitle}</p></header>
{readingbar}<div class="bk-layout{' bk-with-side' if side else ''}"><article id="content" class="{'article-body' if overview else 'bk-article'}" {'data-overview="true"' if overview else ''}>{body}</article>{side}</div>
<footer class="zl-footer"><a href="{root}">zlib × Lean</a><a href="{api}">{t('完整 API 契约','Complete API contracts')}</a><a href="{link('reference/proofs',current,lang)}">{t('实现论证与源码','Arguments and source')} ↗</a></footer></main>{global_contents(current,lang,title)}</body></html>'''


def chapter_ladder(current, lang, unit=None):
    body = '<ol class="bk-ladder">'
    unit=unit or UNIT_BY_KEY['output']
    for i,item in enumerate(unit['steps']):
        proof=i==len(unit['steps'])-1
        stage=label(('证明思路','PROOF ARGUMENT') if proof else ('算法精读','IMPLEMENTATION DETAIL'),lang)
        body+=f'<li><a href="{link("sample/"+item["key"],current,lang)}"><small>{i+1:02}</small><div><span>{stage}</span><h3>{label(item["title"],lang)}</h3><p>{label(item["description"],lang)}</p></div><b>↗</b></a></li>'
    return body+'</ol>'


def render_home(lang):
    current = page_path('index',lang)
    t = lambda a,b:a if lang=='zh' else b
    body = f'''<div class="bk-orientation"><p>{t('这套文章解释 zlib 怎样压缩和恢复数据，应用怎样使用它，以及这些实现需要证明什么。先用下面的地图认识各个组件，再选择算法概览、实现精读或具体函数的完整约定。','These articles explain how zlib compresses and recovers data, how applications use it, and what the implementation’s proofs must establish. Start with the component map below, then choose the algorithm overview, implementation detail, or a function’s complete contract.')}</p><p>{t('第一部分建立算法与接口的全局认识；第二部分按主题深入，先拆解算法和优化，再连接证明思路。各章都有前置背景和下一步，旁边的全局目录可随时展开。','Part one builds the overall picture of algorithms and interfaces. Part two opens each topic’s algorithms and optimizations before developing its proof argument. Chapters link their background and next step; global contents are always available at the side.')}</p></div>
{topology(current,lang)}
<div class="bk-parts"><section id="algorithms"><span class="bk-number">01</span><h2>{t('算法与接口','Algorithms & interfaces')}</h2><p>{t('从重复字节到压缩流，再回到调用者手中的字节。先建立全局认识，再查具体接口。','From repetition to a compressed stream and back to caller-owned bytes. Build the overall picture, then consult exact interfaces.')}</p><a href="{link('algorithms/index',current,lang)}">{t('阅读算法概览','Read the algorithm overview')} →</a><a href="{link('sample/interfaces',current,lang)}">{t('查看调用与接口地图','Explore calls and interfaces')} ↗</a></section>
<section id="verification"><span class="bk-number">02</span><h2>{t('算法精读与形式化验证','Algorithm detail and formal verification')}</h2><p>{t('沿一条实现路径深入：数据怎样布局，优化怎样工作，最后需要证明哪些事实。','Follow an implementation path: how data is laid out, how optimizations work, and which facts the proof must establish.')}</p><a href="{link('verification/index',current,lang)}">{t('选择一个精读主题','Choose a detailed topic')} →</a><a href="{link('reference/proofs',current,lang)}">{t('查阅其他组件的完整论证','Consult the other component arguments')} ↗</a></section></div>
<section class="bk-sample-intro"><div><span class="bk-eyebrow">{t('沿着同一份数据深入','FOLLOW THE SAME DATA')}</span><h2>{t('从三个符号到五个字节','Three symbols, five bytes')}</h2></div><p>{t('本组精读从 A、B 和一个长度 6、距离 2 的匹配开始。先选择块的表示，再写出比特，接着追踪共用内存的读写，最后把这些算法事实连接成证明。','This detailed route starts with A, B, and a length-6, distance-2 match. Choose the block representation, emit its bits, follow reads and writes in shared memory, then connect those facts into a proof.')}</p></section>
{chapter_ladder(current,lang)}
<section class="bk-all-topics"><h2>{t('全部精读主题','All detailed topics')}</h2>{unit_catalogue(current,lang)}</section>
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
    orientation=[('search','找到重复','Find repetition','决定用哪些字面量和匹配','Choose literals and matches'),('huffman-tree','写成压缩流','Write the compressed stream','编码符号，组织块与字节','Code symbols and organize blocks and bytes'),('lookup','恢复原文','Recover the original','读位、查表、按距离复制','Read bits, look up symbols, copy bytes'),('stream','交给应用','Deliver to the application','用有限缓冲区分批取回结果','Recover batches with bounded buffers')]
    path='<nav class="zl-algorithm-path" aria-label="'+t('本篇阅读顺序','This article’s reading path')+'">'
    for anchor,cn,en,cn_detail,en_detail in orientation:
        path+=f'<a href="#{anchor}"><strong>{t(cn,en)}</strong><span>{t(cn_detail,en_detail)}</span></a>'
    path+='</nav>'
    body=f'<div class="bk-overview-note"><p>{t("本篇沿着一次往返理解 zlib：先把原文字节换成压缩表示，再恢复原文，最后用实际 C 调用把结果分批取回。遇到需要进一步展开的实现，可沿章节链接进入算法精读与对应证明。","Follow one round trip through zlib: represent the original bytes compactly, recover them, then retrieve the result in batches through actual C calls. Follow chapter links when you need a mechanism’s implementation detail and proof argument.")}</p></div>'+path+body
    # Add specific bridges at the point where the overview introduces a mechanism.
    for anchor,dest,cn,en in [('blocks','blocks','精读：符号账目与块选择','Detailed reading: symbols and block selection'),('bit-order','bits','精读：16 位输出缓冲与逐字节执行','Detailed reading: the 16-bit writer, step by step'),('stream','stream-state','精读：暂停状态与调用接续','Detailed reading: suspension and resumed calls'),('search','window','精读：窗口、哈希与匹配搜索','Detailed reading: windows, hashes, and match search'),('huffman-tree','huffman-tree','精读：频率、堆与实际编码树','Detailed reading: frequencies, heaps, and actual coding trees'),('canonical','huffman-lengths','精读：码长修复与规范编号','Detailed reading: length repair and canonical numbering'),('lookup','decode-tables','精读：解码表的实际构造','Detailed reading: actual decode-table construction')]:
        marker=re.search(r'<h2 id="'+anchor+r'">.*?</h2>',body)
        if marker:
            bridge=f'<a class="bk-inline-bridge" href="{link("sample/"+dest,current,lang)}">{t(cn,en)} ↗</a>'
            body=body[:marker.end()]+bridge+body[marker.end():]
    body+=f'<div class="bk-next"><span>{t("下一条路线","NEXT ROUTE")}</span><a href="{link("verification/index",current,lang)}">{t("算法精读与形式化验证","Algorithm detail and formal verification")} →</a></div>'
    write(current,shell(t('zlib 的算法与接口','Zlib algorithms and interfaces'),body,'algorithms/index',lang,subtitle=t('先理解输入怎样变成压缩流，再理解解压器怎样恢复原文。','First understand how input becomes a compressed stream, then how the decoder recovers it.'),overview=True))


def unit_catalogue(current,lang):
    body='<div class="bk-unit-catalogue">'
    t=lambda a,b:a if lang=='zh' else b
    for i,unit in enumerate(UNITS):
        first=unit['steps'][0];last=unit['steps'][-1]
        body+=f'<section><span class="bk-eyebrow">{i+1:02} / {len(unit["steps"])} {t("章","CHAPTERS")}</span><h3><a href="{link("verification/"+unit["key"],current,lang)}">{label(unit["title"],lang)} ↗</a></h3><p>{label(unit["summary"],lang)}</p><div><a href="{link("sample/"+first["key"],current,lang)}">{t("从算法开始","Start with the algorithm")} →</a><a href="{link("sample/"+last["key"],current,lang)}">{t("对应证明思路","The proof argument")} ↗</a></div></section>'
    return body+'</div>'


def render_verification(lang):
    current=page_path('verification/index',lang)
    t=lambda a,b:a if lang=='zh' else b
    body=f'<div class="bk-route-intro"><p>{t("一次压缩任务，从调用者提供的字节开始。窗口与匹配生成符号，编码器把符号写成比特，解码器沿相反方向恢复字节；缓冲区可能在任意一次调用后更换，分配也可能失败。", "A compression task begins with caller-provided bytes. Windows and matching produce symbols; the encoder turns symbols into bits; the decoder recovers bytes. Caller buffers can change between calls, and allocation can fail.")}</p><p>{t("证明沿着这些实际对象前进：先精读一个组件的算法、布局和优化，再说明它需要建立的关系，以及关系怎样交给下一个组件。每个主题的最后一章集中讲证明思路，可以与前面的算法互相跳转。", "The proof follows those actual objects. Read a component’s algorithms, layouts, and optimizations first, then the relations it establishes and passes onward. Each topic ends with a proof chapter, linked back to its algorithm background.")}</p></div>'
    body+=topology(current,lang)
    body+=f'<table class="bk-claims"><thead><tr><th>{t("任务中的对象","Object in the task")}</th><th>{t("论证连接","Proof connection")}</th></tr></thead><tbody>'
    for a,b,c,d in [('输入与符号','Input and symbols','匹配产生的符号展开为已接受的输入。','Chosen symbols expand to the accepted input.'),('编码与解码','Encoding and decoding','实际输出满足独立格式关系，解码产生相同字节。','Actual output satisfies an independent format relation and decodes to the same bytes.'),('调用前后状态','States across calls','每个合法返回留下可接续的状态，精确记录消费与交付。','Every legal return preserves a usable state and exact consumption and delivery.'),('活的内存与资源','Live memory and resources','访问合法、无关对象保持不变，分配与释放精确配对。','Accesses are valid, unrelated objects are preserved, and allocations and frees are accounted for.')]:
        body+=f'<tr><td>{t(a,b)}</td><td>{t(c,d)}</td></tr>'
    body+='</tbody></table>'+unit_catalogue(current,lang)
    body+=f'<div class="bk-route-foundation"><h2>{t("命题、实现与接受范围","Targets, implementation, and acceptance scope")}</h2><p>{t("章节分别标明算法解读、局部已给出的结论和仍需组合的义务。完整命题、调用者前提与 Lean 正文可以继续查阅；项目进度页统一记录接受范围与剩余工作。", "Chapters distinguish source readings, available local results, and remaining composition obligations. Follow links to complete targets, caller premises, and Lean proof bodies. The project progress page records acceptance scope and remaining work.")}</p><a href="{link("reference/targets",current,lang)}">{t("完整目标与调用序列","Complete targets and call sequences")} ↗</a><a href="{link("reference/docs/trusted-base",current,lang)}">{t("翻译与模型边界","Translation and model boundary")} ↗</a><a href="{link("reference/docs/progress",current,lang)}">{t("项目进度","Project progress")} ↗</a></div>'
    write(current,shell(t('算法精读与形式化验证','Algorithm detail and formal verification'),body,'verification/index',lang,subtitle=t('先展开具体实现，再连接每一步的论证。','Open the implementation, then connect the argument at every step.')))


def render_unit(unit,lang):
    current=page_path('verification/'+unit['key'],lang)
    t=lambda a,b:a if lang=='zh' else b
    count=len(unit['steps'])-1
    body=purpose_box(current,unit,lang)+f'<div class="bk-route-intro"><p>{t(f"前 {count} 章先展开算法、数据布局与优化，最后一章连接证明思路。可以按顺序读，也可以从已经熟悉的阶段进入。",f"The first {count} chapters explain algorithms, data layouts, and optimizations. The final chapter connects the proof argument. Read in order or enter from a familiar stage.")}</p></div>'+chapter_ladder(current,lang,unit)
    body+=f'<div class="bk-route-foundation"><h2>{t("前置背景与完整参考","Background and complete reference")}</h2><a href="{link("algorithms/index",current,lang,unit["overview"])}">{t("返回算法概览","Return to the algorithm overview")} ↗</a><a href="{link("reference/api",current,lang)}">{t("完整 API 契约","Complete API contracts")} ↗</a><a href="{link("verification/index",current,lang)}">{t("全部精读主题","All detailed topics")} ↗</a></div>'
    write(current,shell(label(unit['title'],lang),body,'verification/'+unit['key'],lang,subtitle=label(unit['summary'],lang)))


def render_sample(key,lang):
    current=page_path('sample/'+key,lang)
    source=SITE/'content/sample'/f'{key}.{lang}.md'
    body,toc=markdown(source.read_text(),current,lang)
    t=lambda a,b:a if lang=='zh' else b
    if key=='interfaces':
        intro=t('把公开调用、引擎工作和字节交付放在同一张地图中。','Place public calls, engine work, and byte delivery on one map.')
        body=f'<p class="bk-chapter-context">{t("从这里查调用顺序与完整函数约定；沿引擎流程进入算法精读。","Use this page for call order and complete contracts; follow the engine stages into detailed algorithm reading.")}</p>'+purpose_box(current,UNIT_BY_KEY['interfaces'],lang)+body
        body+=f'<div class="bk-next"><span>{t("沿引擎继续","FOLLOW THE ENGINE")}</span><a href="{link("sample/blocks",current,lang)}">{label(TITLES["blocks"],lang)} →</a></div>'
    else:
        unit=UNIT_FOR_CHAPTER[key];steps=unit['steps'];index=[c['key'] for c in steps].index(key)
        intro=label(steps[index]['description'],lang)
        previous=steps[index-1]['key'] if index else None
        is_proof=index==len(steps)-1
        stage=t('证明思路','PROOF') if is_proof else t('算法精读','IMPLEMENTATION')
        context=f'<div class="bk-chapter-context"><span>{index+1:02} / {stage}</span>'
        prerequisites={'huffman':'match-search','output':'huffman-lengths','decoding':'bits','streaming':'decode-copy','lifecycle':'stream-state','checksums':'wrappers','interfaces':'stream-state'}
        dependency=previous or prerequisites.get(unit['key'])
        background=link('sample/'+dependency,current,lang) if dependency else link('algorithms/index',current,lang,unit['overview'])
        name=label(TITLES[dependency],lang) if dependency else t('算法概览','Algorithm overview')
        context+=f'<a href="{background}">{t("前置背景：","Background: ")}{name} ↗</a><a href="{link("verification/"+unit["key"],current,lang)}">{t("本组阅读路线","This topic’s reading route")} ↗</a></div>'
        body=context+purpose_box(current,unit,lang,is_proof)+body
        proof_key=steps[-1]['key']
        if not is_proof:
            section={'blocks':'meaning','bits':'bitstream','storage':'prefix'}.get(key,'')
            body+=f'<div class="bk-next bk-proof-bridge"><span>{t("这一机制的证明思路","THE PROOF CONNECTION")}</span><a href="{link("sample/"+proof_key,current,lang,section)}">{label(TITLES[proof_key],lang)} ↗</a></div>'
        elif key=='proof':
            for anchor,dest,background,cn,en in [('meaning','blocks','symbols','符号记录与块表示','Symbol records and block forms'),('bitstream','bits','register','十六位暂存寄存器','The 16-bit holding register'),('prefix','storage','boundary','移动的读取边界','The moving read boundary'),('dynamic','huffman-lengths','', '频率与实际编码树','Frequencies and the actual coding tree'),('composition','interfaces','accounting','输入与输出的交付记账','Input and output accounting')]:
                marker=re.search(r'<h2 id="'+anchor+r'">.*?</h2>',body)
                if marker:
                    bridge=f'<a class="bk-inline-bridge" href="{link("sample/"+dest,current,lang,background)}">{t("算法背景：","Algorithm background: ")}{t(cn,en)} ↗</a>'
                    body=body[:marker.end()]+bridge+body[marker.end():]
        nav='<nav class="bk-chapter-pagination" aria-label="'+t('章节顺序','Chapter order')+'">'
        if previous:
            nav+=f'<a href="{link("sample/"+previous,current,lang)}"><small>{t("上一章","PREVIOUS")}</small>← {label(TITLES[previous],lang)}</a>'
        if index<len(steps)-1:
            following=steps[index+1]['key']
            nav+=f'<a href="{link("sample/"+following,current,lang)}"><small>{t("下一章","NEXT")}</small>{label(TITLES[following],lang)} →</a>'
        else:
            unit_index=UNITS.index(unit)
            if unit_index<len(UNITS)-1:
                following=UNITS[unit_index+1]
                nav+=f'<a href="{link("verification/"+following["key"],current,lang)}"><small>{t("下一组主题","NEXT TOPIC")}</small>{label(following["title"],lang)} →</a>'
            else:
                nav+=f'<a href="{link("reference/proofs",current,lang)}"><small>{t("继续查阅","CONTINUE")}</small>{t("完整实现论证与证明正文","Complete arguments and proof bodies")} ↗</a>'
        body+=nav+'</nav>'
    write(current,shell(label(TITLES[key],lang),body,'sample/'+key,lang,active=key,subtitle=intro,toc=toc))


def build_reading():
    for lang in ('en','zh'):
        render_home(lang)
        render_overview(lang)
        render_verification(lang)
        for unit in UNITS:
            render_unit(unit,lang)
        for key in [*CHAPTER_BY_KEY,'interfaces']:
            render_sample(key,lang)
        for key in ['blocks','bits','storage','proof','interfaces']:
            old=OUT/'sample'/(key+('.zh.html' if lang=='zh' else '.html'))
            target=link('sample/'+key,old,lang)
            title='章节已迁移' if lang=='zh' else 'Chapter moved'
            write(old,f'<!doctype html><html lang="{lang}"><head><meta charset="utf-8"><title>{title}</title><link rel="canonical" href="{target}"><script>location.replace(new URL({target!r}+location.search+location.hash,location.href))</script></head><body><h1>{title}</h1><a href="{target}">zlib × Lean</a></body></html>')
    print(f'Built bilingual reading map, {len(UNITS)} topic routes, and {len(CHAPTER_BY_KEY)+1} detailed chapters')
