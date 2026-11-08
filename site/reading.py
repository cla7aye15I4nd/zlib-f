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
    revision = sha256(b''.join((SITE/'static'/name).read_bytes() for name in ['book.css', 'book.js','zlib-essay.js','zlib-writer.js','zlib-writer-model.mjs','navigation.css','navigation.js','topology.css','topology.js','syntax.css'])).hexdigest()[:12]
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
    first_active = route.startswith('algorithms/')
    second_active = route == 'verification/index'
    readingbar = f'''<nav class="bk-navigation" aria-label="{t('阅读导航','Reading navigation')}">
<a {'aria-current="page"' if first_active else ''} href="{algorithm}">{t('开始阅读','Start reading')}</a>
<a {'aria-current="page"' if second_active else ''} href="{verification}">{t('章节目录','Chapters')}</a>
<a class="bk-nav-api" href="{api}">API</a><a href="{root}">{t('阅读地图','Reading map')} ↗</a></nav>'''
    return f'''<!doctype html><html lang="{lang}"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>{html.escape(title) if route == "index" else html.escape(title)+" · zlib × Lean"}</title><meta name="description" content="{html.escape(subtitle,quote=True)}">
<link rel="icon" href="{asset('favicon.svg')}" type="image/svg+xml">
<link rel="stylesheet" href="{asset('base.css')}?v={revision}"><link rel="stylesheet" href="{asset('zlib-essay.css')}?v={revision}"><link rel="stylesheet" href="{asset('zlib-search.css')}?v={revision}"><link rel="stylesheet" href="{asset('zlib-lookup.css')}?v={revision}"><link rel="stylesheet" href="{asset('zlib-overlay.css')}?v={revision}"><link rel="stylesheet" href="{asset('zlib-table-proof.css')}?v={revision}"><link rel="stylesheet" href="{asset('layout.css')}?v={revision}"><link rel="stylesheet" href="{asset('reference.css')}?v={revision}"><link rel="stylesheet" href="{asset('book.css')}?v={revision}">
<link rel="stylesheet" href="{asset('navigation.css')}?v={revision}"><link rel="stylesheet" href="{asset('topology.css')}?v={revision}">
<link rel="stylesheet" href="{asset('syntax.css')}?v={revision}">
<script type="module" src="{asset('zlib-essay.js')}?v={revision}"></script><script defer src="{asset('reference.js')}?v={revision}"></script><script defer src="{asset('book.js')}?v={revision}"></script><script defer src="{asset('navigation.js')}?v={revision}"></script><script defer src="{asset('topology.js')}?v={revision}"></script></head>
<body><a class="zl-skip" href="#content">{t('跳到正文','Skip to content')}</a>
<main class="zl-page bk-page{' bk-overview zlib-essay' if overview else ''}">
<nav class="article-topbar"><a class="article-brand" href="{root}">I Have Nothing</a><div><a href="https://www.dataisland.org/blog/">{t('博客','Writing')}</a><a data-language href="{href(other,current)}">{t('English','中文')}</a></div></nav>
<header class="bk-hero {hero_class}"><div class="bk-eyebrow">{t('阅读地图','READING MAP') if route == 'index' else 'ZLIB × LEAN'}</div><h1>{title_markup}</h1><p>{subtitle}</p></header>
{readingbar}<div class="bk-layout{' bk-with-side' if side else ''}"><article id="content" class="{'article-body' if overview else 'bk-article'}" {'data-overview="true"' if overview else ''}>{body}</article>{side}</div>
<footer class="zl-footer"><a href="{root}">zlib × Lean</a><a href="{api}">{t('完整 API 契约','Complete API contracts')}</a><a href="{link('reference/proofs',current,lang)}">{t('实现论证与源码','Arguments and source')} ↗</a></footer></main>{global_contents(current,lang,title)}</body></html>'''


def chapter_ladder(current, lang, unit=None):
    body = '<ol class="bk-ladder">'
    unit=unit or UNIT_BY_KEY['output']
    for i,item in enumerate(unit['steps']):
        proof=i==len(unit['steps'])-1
        stage=label(('证明思路','PROOF ARGUMENT') if proof else ('实现过程','IMPLEMENTATION'),lang)
        body+=f'<li><a href="{link("sample/"+item["key"],current,lang)}"><small>{i+1:02}</small><div><span>{stage}</span><h3>{label(item["title"],lang)}</h3><p>{label(item["description"],lang)}</p></div><b>↗</b></a></li>'
    return body+'</ol>'


def render_home(lang):
    current = page_path('index',lang)
    t = lambda a,b:a if lang=='zh' else b
    body = f'''<div class="bk-orientation"><p>{t('八个字节 ABABABAB，怎样变成压缩流，又怎样被恢复出来？这套文章沿着这次往返展开 zlib 的实现：找到重复、给符号编码、写出字节，再读位、查表和复制。','How do the eight bytes ABABABAB become a compressed stream, then return to their original form? Follow that round trip through zlib: find repetition, code symbols, emit bytes, then read bits, look up symbols, and copy.')}</p><p>{t('正文讲到一个机制时，就会引出它的实现章节。章节先说明要完成的任务，再拆开数据布局、算法与优化；对应的证明接着说明这些步骤需要保持什么关系。随时可以打开旁边的目录，回到同一条数据流。','Each mechanism in the main story opens into its implementation chapters. They establish the task before unpacking data layouts, algorithms, and optimizations. The accompanying proof explains the relations those steps must preserve. Open the contents at any point to find your place in the data flow.')}</p></div>
<section class="bk-start" id="algorithms"><span class="bk-eyebrow">{t('开始阅读','START HERE')}</span><h2>{t('从八个字节开始','Start with eight bytes')}</h2><p>{t('先走完一次压缩与解压。动手调整匹配、编码和输出空间，看到每一步怎样影响下一步；需要知道实际 C 程序怎样做到时，就沿该处的章节继续。','Walk through compression and decoding. Change a match, a code, or the available output space and see how each choice affects the next step. Follow a chapter link where you want to open the actual C implementation.')}</p><a href="{link('algorithms/index',current,lang)}">{t('从字节到压缩流','From bytes to a compressed stream')} →</a></section>
{topology(current,lang)}
<section class="bk-all-topics" id="verification"><h2>{t('沿着数据展开的章节','Chapters along the data flow')}</h2><p>{t('匹配、编码和输出连接成压缩路径；读位、查表和复制连接成解压路径。分批调用、校验、资源管理和接口选择围绕这两条路径展开，不是必须依次经过的流水线。','Matching, coding, and output form the compression path; bit reading, table lookup, and copying form the decoding path. Batched calls, checksums, resource management, and interface choices support those paths rather than forming a mandatory sequence.')}</p>{unit_catalogue(current,lang)}<a href="{link('verification/index',current,lang)}">{t('展开完整章节目录','Open the complete chapter directory')} ↗</a></section>
<section class="bk-reference-strip"><h2>{t('完整参考','Complete reference')}</h2><p>{t('函数页列出公开 API 的参数、返回值和错误路径。各章还连接到引擎论证、精确命题和 Lean 正文。','Function pages give public API parameters, results, and error paths. Chapter links also lead to engine arguments, exact targets, and Lean proof bodies.')}</p><div><a href="{link('reference/api',current,lang)}">{t('全部公开 API','All public APIs')} ↗</a><a href="{link('reference/proofs',current,lang)}">inflate / deflate ↗</a><a href="{link('reference/index',current,lang)}">{t('文档索引','Documentation index')} ↗</a></div></section>'''
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
    body=f'<div class="bk-overview-note"><p>{t("本篇沿着一次往返理解 zlib：先把原文字节换成压缩表示，再恢复原文，最后用实际 C 调用把结果分批取回。每个环节之后都可以展开相应章节，继续读实际实现和它的证明。","Follow one round trip through zlib: represent the original bytes compactly, recover them, then retrieve the result in batches through actual C calls. Expand the continuation after a mechanism to follow its implementation and proof.")}</p></div>'+path+body
    # Expand at the end of a mechanism, after its motivation and example.
    continuations={
        'bytes':('decoding','回引用在解码器中的执行','Executing a back-reference','长度和距离已经能描述原文。解码器还要读出这条指令，在输出空间不足时记住复制进度。','Lengths and distances describe the original bytes. The decoder must read that instruction and retain copying progress when output space runs out.'),
        'layers':('streaming','封装与任务边界','Wrappers and task boundaries','头部说明接下来按什么方式读取；尾部检查恢复出的字节。它们与 DEFLATE 载荷一起构成完整的流状态机。','Headers select how to read the stream; trailers check recovered bytes. Together with the DEFLATE payload, they form the complete stream state machine.'),
        'search':('matching','在有限内存里持续寻找重复','Finding repetition in bounded memory','要得到长度和距离，压缩器必须保存仍可引用的字节，并从中找候选。接下来从保留范围展开到数组搬移、哈希链和逐字节比较。','To produce a length and distance, the compressor retains reusable bytes and finds candidates among them. Follow the retained range into array sliding, hash chains, and byte comparisons.'),
        'huffman-tree':('huffman','从实际频率构造编码','Constructing codes from frequencies','匹配搜索产生符号；编码器统计这些符号，再合并低频节点。构造章节沿频率表、最小堆和树的父节点逐步展开。','Matching produces symbols. The encoder counts them and merges low-frequency nodes. Follow frequency tables, the minimum heap, and parent links in the tree.'),
        'canonical':('huffman','把码长变成双方一致的码字','Turning lengths into agreed codes','树给出码长后，还要满足格式的长度限制，并让解码端重建相同码字。这里连接码长修复、规范编号和可解码性的论证。','Lengths from the tree must meet format limits and let the decoder reconstruct identical codes. Continue through length repair, canonical numbering, and the argument for decodability.'),
        'blocks':('output','从符号成本走到实际输出','From symbol costs to actual output','选块要计算载荷与头部成本。选定表示后，同一份符号记录才会被读出并写成块字段；实现章节追踪这次转换。','Block selection counts payload and header costs. Once the form is chosen, the same records are read and written as block fields. Follow that conversion in the implementation.'),
        'bit-order':('output','把比特交付成字节','Delivering bits as bytes','码字进入位寄存器，完整字节进入待交付区，最后才复制到调用者的缓冲区。这三个位置各自需要空间界和准确的先后顺序。','Codes enter the bit register, complete bytes enter pending storage, and only then are they copied into the caller’s buffer. Each location needs its own capacity bound and ordering argument.'),
        'lookup':('decoding','从压缩字节重新走到原文','From compressed bytes back to the input','查表是解码过程的中间一步。前面要补入位并识别块，后面要解释字面量、长度和距离，再把结果写到输出中。','Table lookup sits inside a larger decoding process. First refill bits and identify the block; then interpret literals, lengths, and distances and write the recovered bytes.'),
        'stream':('streaming','暂停状态与任务接续','Suspension and continuation','一次返回保留未完成的读位、复制和尾部检查。继续章节从同一次小缓冲区解压展开状态字段，再连接校验、资源清理与不同 API 的使用方式。','A return retains unfinished bit reading, copying, and trailer checking. Continue the same small-buffer task into state fields, then checksums, cleanup, and API choices.'),
    }
    def continuation(match):
        section=match.group(0)
        anchor=re.match(r'<h2 id="([^"]+)"',section).group(1)
        if anchor not in continuations:
            return section
        key,cn,en,cn_body,en_body=continuations[anchor]
        unit=UNIT_BY_KEY[key]
        return section+f'<details class="bk-continuation"><summary>{t(cn,en)}</summary><p>{t(cn_body,en_body)}</p><div><a href="{link("verification/"+key,current,lang)}">{label(unit["title"],lang)} →</a><a href="{link("sample/"+unit["steps"][-1]["key"],current,lang)}">{t("对应证明思路","The proof argument")} ↗</a></div></details>'
    body=re.sub(r'<h2 id="[^"]+">[\s\S]*?(?=<h2 |$)',continuation,body)
    body+=f'<div class="bk-next"><span>{t("继续使用这个引擎","USING THE ENGINE")}</span><a href="{link("verification/interfaces",current,lang)}">{t("选择缓冲区、回调或文件接口","Choose buffer, callback, or file interfaces")} →</a></div>'
    write(current,shell(t('从字节到压缩流','From bytes to a compressed stream'),body,'algorithms/index',lang,subtitle=t('从 ABABABAB 出发，沿着压缩与解压展开 zlib。','Start with ABABABAB and follow compression and decoding through zlib.'),overview=True))


def unit_catalogue(current,lang):
    body='<div class="bk-unit-catalogue">'
    t=lambda a,b:a if lang=='zh' else b
    for i,unit in enumerate(UNITS):
        first=unit['steps'][0];last=unit['steps'][-1]
        body+=f'<section><span class="bk-eyebrow">{len(unit["steps"])} {t("章","CHAPTERS")}</span><h3><a href="{link("verification/"+unit["key"],current,lang)}">{label(unit["title"],lang)} ↗</a></h3><p>{label(unit["summary"],lang)}</p><div><a href="{link("verification/"+unit["key"],current,lang)}">{t("展开这一环节","Follow this task")} →</a><a href="{link("sample/"+last["key"],current,lang)}">{t("对应证明思路","The proof argument")} ↗</a></div></section>'
    return body+'</div>'


def render_verification(lang):
    current=page_path('verification/index',lang)
    t=lambda a,b:a if lang=='zh' else b
    body=f'<div class="bk-route-intro"><p>{t("从原文字节出发，压缩器先找到匹配，再编码符号、选择块并写出字节。解压器反过来读位、查表和复制。下面按这些交接组织章节：每组先说明它接收什么、交出什么，再展开实现和对应证明。", "From original bytes, the compressor finds matches, codes symbols, chooses blocks, and writes bytes. The decoder reads bits, looks up symbols, and copies. The chapters below follow these handoffs: each topic establishes what it receives and produces before opening its implementation and proof.")}</p><p>{t("分批调用、校验、状态管理和接口选择服务于同一任务，可以在用到它们时展开。第一次阅读可以跟随正文的章节入口；查具体机制时，直接使用本页或旁边的目录。", "Batched calls, checksums, state management, and API choices support the same task and can be opened where needed. On a first reading, follow the chapter links in the main story; use this directory or the global contents to find a particular mechanism.")}</p></div>'
    body+=topology(current,lang)
    for unit in UNITS:
        body+=f'<section class="bk-directory-topic"><h2><a href="{link("verification/"+unit["key"],current,lang)}">{label(unit["title"],lang)} ↗</a></h2><p>{label(unit["summary"],lang)}</p>'+chapter_ladder(current,lang,unit)+'</section>'
    body+=f'<div class="bk-reference-strip"><h2>{t("接口与证明参考","API and proof reference")}</h2><p>{t("函数页列出完整调用约定；命题和源码页展开形式化陈述与证明正文。", "Function pages give complete calling contracts; target and source pages open the formal statements and proof bodies.")}</p><div><a href="{link("reference/api",current,lang)}">{t("全部公开 API","All public APIs")} ↗</a><a href="{link("reference/targets",current,lang)}">{t("精确命题与调用序列","Exact targets and call sequences")} ↗</a><a href="{link("reference/sources",current,lang)}">{t("Lean 源码与证明正文","Lean source and proof bodies")} ↗</a><a href="{link("reference/docs/progress",current,lang)}">{t("项目进度","Project progress")} ↗</a></div></div>'
    write(current,shell(t('章节目录','Chapter directory'),body,'verification/index',lang,subtitle=t('从字节到符号，从比特到原文；按数据的交接展开实现与证明。','From bytes to symbols and bits back to bytes: implementation and proof at each handoff.')))


def render_unit(unit,lang):
    current=page_path('verification/'+unit['key'],lang)
    t=lambda a,b:a if lang=='zh' else b
    topic=SITE/'content/topics'/f'{unit["key"]}.{lang}.md'
    body,toc=markdown(topic.read_text(),current,lang)
    body+=f'<div class="bk-route-foundation"><h2>{t("前置背景与完整参考","Background and complete reference")}</h2><a href="{link("algorithms/index",current,lang,unit["overview"])}">{t("返回正文中的这一环节","Return to this stage in the main story")} ↗</a><a href="{link("reference/api",current,lang)}">{t("完整 API 契约","Complete API contracts")} ↗</a><a href="{link("verification/index",current,lang)}">{t("全部章节","All chapters")} ↗</a></div>'
    write(current,shell(label(unit['title'],lang),body,'verification/'+unit['key'],lang,subtitle=label(unit['summary'],lang),toc=toc))


def render_sample(key,lang):
    current=page_path('sample/'+key,lang)
    source=SITE/'content/sample'/f'{key}.{lang}.md'
    body,toc=markdown(source.read_text(),current,lang)
    t=lambda a,b:a if lang=='zh' else b
    if key=='interfaces':
        intro=t('把公开调用、引擎工作和字节交付放在同一张地图中。','Place public calls, engine work, and byte delivery on one map.')
        body=f'<p class="bk-chapter-context">{t("从这里查调用顺序与完整函数约定；沿数据流查看各个实现环节。","Use this page for call order and complete contracts; follow the data through the implementation.")}</p>'+purpose_box(current,UNIT_BY_KEY['interfaces'],lang)+body
        body+=f'<div class="bk-next"><span>{t("选择使用方式","CHOOSE A CALLING STYLE")}</span><a href="{link("verification/interfaces",current,lang)}">{label(UNIT_BY_KEY["interfaces"]["title"],lang)} →</a></div>'
    else:
        unit=UNIT_FOR_CHAPTER[key];steps=unit['steps'];index=[c['key'] for c in steps].index(key)
        intro=label(steps[index]['description'],lang)
        previous=steps[index-1]['key'] if index else None
        is_proof=index==len(steps)-1
        stage=t('证明思路','PROOF') if is_proof else t('实现过程','IMPLEMENTATION')
        context=f'<div class="bk-chapter-context"><span>{index+1:02} / {stage}</span>'
        prerequisites={'huffman':'match-search','output':'huffman-lengths','decoding':'bits','streaming':'decode-copy','lifecycle':'stream-state','checksums':'wrappers','interfaces':'stream-state'}
        dependency=('wrappers' if key in {'adler','crc'} else previous or prerequisites.get(unit['key']))
        background=link('sample/'+dependency,current,lang,'checksums' if key in {'adler','crc'} else '') if dependency else link('algorithms/index',current,lang,unit['overview'])
        name=label(TITLES[dependency],lang) if dependency else t('从八个字节开始','Start with eight bytes')
        context+=f'<a href="{background}">{t("相关背景：","Related background: ")}{name} ↗</a><a href="{link("verification/"+unit["key"],current,lang)}">{t("本组阅读路线","This topic’s reading route")} ↗</a></div>'
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
            nav+=f'<a href="{link("sample/"+previous,current,lang)}"><small>{t("相关章节","RELATED CHAPTER") if unit["key"]=="interfaces" or key=="crc" else t("上一章","PREVIOUS")}</small>← {label(TITLES[previous],lang)}</a>'
        if index<len(steps)-1:
            following=steps[index+1]['key']
            nav+=f'<a href="{link("sample/"+following,current,lang)}"><small>{t("另一种封装的算法","ALTERNATIVE WRAPPER ALGORITHM") if key=="adler" else t("另一种使用方式","ANOTHER CALLING STYLE") if unit["key"]=="interfaces" and not following.endswith("proof") else t("下一章","NEXT")}</small>{label(TITLES[following],lang)} →</a>'
        else:
            handoffs={'matching':'huffman','huffman':'output','output':'decoding','decoding':'streaming','streaming':'checksums','lifecycle':'streaming','checksums':'interfaces','interfaces':'lifecycle'}
            following=UNIT_BY_KEY[handoffs[unit['key']]]
            nav+=f'<a href="{link("verification/"+following["key"],current,lang)}"><small>{t("相关环节","RELATED TASK")}</small>{label(following["title"],lang)} →</a>'
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
    print(f'Built bilingual reading map, {len(UNITS)} topic routes, and {len(CHAPTER_BY_KEY)+1} connected chapters')
