"""The sole navigation surface for the book and its references."""
from pathlib import Path
import html,os,re
from book import BOOK,APPENDICES,chapter_sections
OUT=Path(__file__).resolve().parent/'dist'

def global_contents(current,lang,title,toc=''):
    zh=lang=='zh';suffix='.zh.html' if zh else '.html';t=lambda a,b:a if zh else b
    relative=current.relative_to(OUT).as_posix()
    def url(route,anchor=''):
        return os.path.relpath(OUT/(route+suffix),current.parent).replace(os.sep,'/')+('#'+anchor if anchor else '')
    def a(route,cn,en,anchor=''):
        mark=' aria-current="page"' if relative==route+suffix and not anchor else ''
        return f'<a href="{url(route,anchor)}"{mark}>{html.escape(t(cn,en))}</a>'
    def local_toc():return re.sub(r'<li>','<li data-toc-entry>',toc)
    body=f'''<button type="button" class="bk-global-trigger" data-global-toc aria-controls="book-global-toc" aria-expanded="false" title="{t('打开目录','Open contents')}"><svg viewBox="0 0 20 20" aria-hidden="true"><path d="M3 5h14M3 10h14M3 15h14"/></svg><span>{t('目录','Contents')}</span></button>
<dialog class="bk-global-dialog" id="book-global-toc" aria-labelledby="book-global-title"><div class="bk-global-header"><div><span>ZLIB × LEAN</span><h2 id="book-global-title">{t('目录','Contents')}</h2></div><button type="button" data-toc-close aria-label="{t('关闭目录','Close contents')}">×</button></div>
<div class="bk-global-location"><span>{t('正在阅读','READING NOW')}</span>{html.escape(title)}</div>
<label class="bk-global-search">{t('查找章节或小节','Find a chapter or section')}<input type="search" data-toc-search placeholder="{t('匹配、查表、字典…','Matching, tables, dictionaries…')}" autocomplete="off"></label>
<nav class="bk-global-tree" aria-label="{t('全书目录','Book contents')}">'''
    is_book=False
    for i,item in enumerate(BOOK):
        active=relative==item['route']+suffix;is_book|=active
        body+=f'<details class="bk-global-section" data-toc-section {("open" if active else "")}><summary><small>{i+1:02}</small>{a(item["route"],*item["title"])}</summary>'
        if active and toc:body+=local_toc()
        else:body+='<ul>'+''.join(f'<li data-toc-entry>{a(item["route"],title,title,anchor)}</li>' for anchor,title in chapter_sections(item['key'],lang))+'</ul>'
        body+='</details>'
    if toc and not is_book:body+=f'<details class="bk-global-section" data-toc-section open><summary>{t("本页小节","On this page")}</summary>{local_toc()}</details>'
    body+=f'<details class="bk-global-section" data-toc-section><summary>{t("参考","Reference")}</summary><ul>'
    for key,cn,en in APPENDICES:body+=f'<li data-toc-entry>{a("appendix/"+key,cn,en)}</li>'
    for route,cn,en in [('reference/api','全部公开 API','All public APIs'),('reference/proofs','实现论证','Implementation arguments'),('reference/targets','精确命题','Exact targets'),('reference/sources','Lean 源码','Lean source'),('reference/docs/progress','证明进度','Proof progress'),('reference/index','文档索引','Documentation index')]:body+=f'<li data-toc-entry>{a(route,cn,en)}</li>'
    body+=f'</ul></details></nav><p class="bk-global-empty" data-toc-empty hidden>{t("没有匹配的小节。","No matching sections.")}</p></dialog>'
    fallback=''.join(f'<li>{a(c["route"],*c["title"])}</li>' for c in BOOK)
    return body+f'<noscript><nav class="bk-static-contents" aria-label="{t("章节","Chapters")}"><ol>{fallback}</ol></nav></noscript>'
