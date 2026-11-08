"""Global contents available from every reading and reference page."""
from pathlib import Path
import html
import os

from routes import UNITS, UNIT_FOR_CHAPTER

OUT=Path(__file__).resolve().parent/'dist'
OVERVIEW=[('bytes','字面量与回引用','Literals and back-references'),('layers','库与数据格式','Library and formats'),('search','近期历史与匹配搜索','Recent history and match search'),('lazy','延迟匹配','Lazy matching'),('huffman-tree','Huffman 树','Huffman trees'),('canonical','规范编码','Canonical codes'),('blocks','块类型与成本','Block types and costs'),('bit-order','位序与缓冲','Bit order and buffers'),('lookup','解码表','Decode tables'),('stream','分批解压与输出缓冲区','Decoding in output batches')]
API_GROUPS=[('deflate-stream','压缩流','Compression streams'),('inflate-stream','解压流','Decompression streams'),('inflate-back','回调解码','Callback decoding'),('utility','缓冲区与库信息','Buffers and library information'),('checksums','校验和','Checksums'),('gz-file','gzip 文件','Gzip files')]


def global_contents(current:Path,lang:str,title:str)->str:
    zh=lang=='zh';suffix='.zh.html' if zh else '.html'
    t=lambda a,b:a if zh else b
    def url(route,anchor=''):
        target=OUT/(route+suffix)
        return os.path.relpath(target,current.parent).replace(os.sep,'/')+('#'+anchor if anchor else '')
    relative=current.relative_to(OUT).as_posix()
    chapter=current.name.removesuffix('.zh.html').removesuffix('.html')
    unit=UNIT_FOR_CHAPTER.get(chapter)
    if relative.startswith('verification/'):
        unit=next((u for u in UNITS if u['key']==chapter),None)
    def a(route,cn,en,anchor='',extra=''):
        selected=relative==(route+suffix) and not anchor
        return f'<a href="{url(route,anchor)}"{(" aria-current=\"page\"" if selected else "")} {extra}>{html.escape(t(cn,en))}</a>'
    body=f'''<button type="button" class="bk-global-trigger" data-global-toc aria-controls="book-global-toc" aria-expanded="false" title="{t('打开全局目录','Open global contents')}"><svg viewBox="0 0 20 20" aria-hidden="true"><path d="M3 5h14M3 10h14M3 15h14"/></svg><span>{t('目录','Contents')}</span></button>
<dialog class="bk-global-dialog" id="book-global-toc" aria-labelledby="book-global-title"><div class="bk-global-header"><div><span>ZLIB × LEAN</span><h2 id="book-global-title">{t('全局目录','Global contents')}</h2></div><button type="button" data-toc-close aria-label="{t('关闭目录','Close contents')}">×</button></div>
<div class="bk-global-location"><span>{t('当前位置','READING NOW')}</span>{html.escape(title)}</div>
<label class="bk-global-search">{t('搜索章节','Find a chapter')}<input type="search" data-toc-search placeholder="{t('窗口、Huffman、内存…','Window, Huffman, memory…')}" autocomplete="off"></label>
<nav class="bk-global-tree" aria-label="{t('全书目录','Whole-book contents')}">
<div class="bk-global-map-link">{a('index','阅读地图','Reading map')} {a('index','交互机制图 ↗','Interactive mechanism map ↗','algorithm-map')}</div>
<details class="bk-global-section" data-toc-section {('open' if relative.startswith('algorithms/') else '')}><summary>{t('从八个字节开始','Start with eight bytes')}</summary><ul>'''
    for anchor,cn,en in OVERVIEW:
        body+=f'<li data-toc-entry>{a("algorithms/index",cn,en,anchor)}</li>'
    body+='</ul></details>'
    body+=f'<div class="bk-global-map-link">{a("verification/index","章节目录 ↗","Chapter directory ↗")}</div>'
    for i,item in enumerate(UNITS):
        active=unit is item
        body+=f'<details class="bk-global-section" data-toc-section {("open" if active else "")}><summary><small>{i+1:02}</small>{item["title"][not zh]}</summary><ul>'
        body+=f'<li class="bk-global-route" data-toc-entry>{a("verification/"+item["key"],"这组章节的阅读路线 ↗","This topic’s reading route ↗")}</li>'
        for j,page in enumerate(item['steps']):
            proof=j==len(item['steps'])-1
            keywords=' '.join([item['key'],page['key'],*item['title'],*page['title'],*page['description']])
            body+=f'<li data-toc-entry data-toc-keywords="{html.escape(keywords,quote=True)}"><div>{a("chapters/"+page["key"],*page["title"])}<p>{html.escape(page["description"][not zh])}</p></div>{("<small>"+t("证明","Proof")+"</small>" if proof else "")}</li>'
        body+='</ul></details>'
    body+='<details class="bk-global-section" data-toc-section><summary>'+t('完整论证与源码','Complete arguments and source')+'</summary><ul>'
    for route,cn,en in [('reference/proofs','引擎论证','Engine arguments'),('reference/targets','精确命题与调用序列','Exact targets and call sequences'),('reference/sources','Lean 源码与证明正文','Lean source and proof bodies'),('reference/index','文档索引','Documentation index')]:
        body+=f'<li data-toc-entry>{a(route,cn,en)}</li>'
    body+='</ul></details>'
    body+='<details class="bk-global-section" data-toc-section><summary>'+t('调用与完整 API','Calls and complete APIs')+'</summary><ul>'
    body+=f'<li data-toc-entry>{a("chapters/interfaces","调用顺序与接口地图","Call order and the API map")}</li>'
    body+=f'<li data-toc-entry>{a("reference/api","全部公开 API","All public APIs")}</li>'
    for key,cn,en in API_GROUPS:
        body+=f'<li data-toc-entry><a href="{url("reference/api")}?group={key}">{t(cn,en)}</a></li>'
    body+='</ul></details></nav>'
    body+=f'<p class="bk-global-empty" data-toc-empty hidden>{t("没有匹配章节。函数名可在 API 索引中查找。","No matching chapters. Search function names in the API index.")}</p><footer class="bk-global-footer">{a("reference/api","查找具体函数 ↗","Find a function ↗")}</footer></dialog>'
    return body+f'<noscript><a class="bk-global-trigger" href="{url("verification/index")}">{t("全部章节","All chapters")} ↗</a></noscript>'
