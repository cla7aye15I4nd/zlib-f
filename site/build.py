"""Build the standalone bilingual essay. No blog runtime is required."""
from pathlib import Path
import html
import shutil
from markdown import Markdown
from hashlib import sha256
from reference import build_reference, doc_path
import re

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "dist"
OUT.mkdir(exist_ok=True)
shutil.copytree(ROOT / "static", OUT / "static", dirs_exist_ok=True)

for lang in ("en", "zh"):
    zh = lang == "zh"
    source = (ROOT / "content" / f"article.{lang}.md").read_text()
    md = Markdown(extensions=["fenced_code", "tables", "attr_list", "toc"],
                  extension_configs={"toc": {"baselevel": 2, "toc_depth": 3}})
    body = md.convert(source)
    def local_reference(match):
        path=ROOT.parent/'docs'/match.group(1)
        target=doc_path(path,lang)
        relative=target.relative_to(OUT).as_posix()
        return 'href="./'+relative+(('#'+match.group(2)) if match.group(2) else '')+'"'
    body=re.sub(r'href="https://github.com/cla7aye15I4nd/zlib-f/blob/main/docs/([^"#]+\.md)(?:#([^"]+))?"',local_reference,body)
    if not (ROOT.parent/'docs/proof/stream-composition.md').exists():
        body=body.replace('reference/docs/proof/stream-composition.','reference/docs/proof/method.')
    def local_doc_reference(match):
        source=ROOT.parent/'docs'/(match.group(1)+'.md')
        target=doc_path(source,lang).relative_to(OUT).as_posix()
        return 'href="./'+target+(('#'+match.group(2)) if match.group(2) else '')+'"'
    body=re.sub(r'href="\./reference/docs/([^"#]+?)(?:\.zh)?\.html(?:#([^"]+))?"',local_doc_reference,body)
    title = "zlib × Lean"
    description = ("从重复的字节，到可以检查的论证。" if zh else
                   "From repeated bytes to arguments we can check.")
    other = "index.html" if zh else "index.zh.html"
    filename = "index.zh.html" if zh else "index.html"
    t = lambda a, b: a if zh else b
    version = sha256(b''.join(p.read_bytes() for p in sorted((ROOT/'static').glob('*')) if p.is_file())).hexdigest()[:12]
    body = '<div class="zl-reference-door"><span>'+t('导读与完整参考','Guide and complete reference')+'</span><a href="./reference/api'+('.zh' if zh else '')+'.html">'+t('全部 API 契约','All API contracts')+' ↗</a><a href="./reference/proofs'+('.zh' if zh else '')+'.html">'+t('证明细节','Proof details')+' ↗</a></div>'+body
    output = f'''<!doctype html>
<html lang="{lang}">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width,initial-scale=1">
  <meta name="description" content="{html.escape(description)}">
  <meta name="theme-color" content="#eeeeec">
  <title>{title}</title>
  <link rel="alternate" hreflang="en" href="./index.html">
  <link rel="alternate" hreflang="zh" href="./index.zh.html">
  <link rel="icon" href="./static/favicon.svg" type="image/svg+xml">
  <link rel="stylesheet" href="./static/base.css">
  <link rel="stylesheet" href="./static/zlib-essay.css">
  <link rel="stylesheet" href="./static/zlib-search.css">
  <link rel="stylesheet" href="./static/zlib-lookup.css">
  <link rel="stylesheet" href="./static/zlib-overlay.css">
  <link rel="stylesheet" href="./static/zlib-table-proof.css">
  <link rel="stylesheet" href="./static/layout.css?v={version}">
  <link rel="stylesheet" href="./static/reference.css?v={version}">
  <script type="module" src="./static/zlib-essay.js?v={version}"></script>
</head>
<body>
<a class="zl-skip" href="#article">{t('跳到正文','Skip to the essay')}</a>
<main class="zl-page zlib-essay">
  <nav class="article-topbar" aria-label="{t('网站导航','Site navigation')}">
    <a class="article-brand" href="https://www.dataisland.org/blog/">I Have Nothing</a>
    <div><a href="https://www.dataisland.org/blog/">{t('博客','Writing')}</a><span class="zl-nav-separator">/</span><a data-language href="./{other}" hreflang="{t('en','zh')}">{t('English','中文')}</a></div>
  </nav>
  <header class="article-hero">
    <div class="zl-hero-eyebrow">COMPRESSION / FORMAL VERIFICATION</div>
    <h1>zlib <span>×</span> Lean</h1>
    <p>{description}<br>{t('先理解 zlib 怎样工作，再理解怎样验证它。','First understand how zlib works. Then ask how to verify it.')}</p>
    <div class="article-meta"><span>{t('交互导读与参考文档','Interactive guide and reference')}</span><span>{t('算法 · 接口 · 证明细节','Algorithms · contracts · proof details')}</span><span>{t('中文','English')}</span></div>
  </header>
  <nav class="zl-readingbar" aria-label="{t('文章导航','Essay navigation')}">
    <a href="#how-zlib-works" data-part-link="1"><small>01</small> {t('算法与接口','Algorithms & interfaces')}</a>
    <a href="#verifying-zlib" data-part-link="2"><small>02</small> {t('形式化验证','Formal verification')}</a>
    <a class="zl-language" data-language href="./{other}" hreflang="{t('en','zh')}" aria-label="{t('切换到英文，保留当前章节','Switch to Chinese at this chapter')}">{t('EN','中文')}</a>
    <div class="zl-reference-nav"><a href="./reference/api{t('.zh','')}.html">API</a><a href="./reference/proofs{t('.zh','')}.html">{t('证明','Proofs')}</a></div>
    <details class="zl-contents"><summary>{t('目录','Contents')} <span>↗</span></summary><div><p><a href="./reference/api{t('.zh','')}.html">{t('完整 API 契约','Complete API contracts')}</a> · <a href="./reference/proofs{t('.zh','')}.html">{t('证明细节','Proof details')}</a></p>{md.toc}</div></details>
    <div class="zl-progress" aria-hidden="true"><i></i></div>
  </nav>
  <article class="article-body" id="article">{body}</article>
  <footer class="zl-footer"><a href="https://www.dataisland.org/">Dataisland</a><span>zlib × Lean</span><a href="https://github.com/cla7aye15I4nd/zlib-f">{t('源码与证明','Source & proofs')} ↗</a></footer>
</main>
</body>
</html>'''
    (OUT / filename).write_text(output)
(OUT / ".nojekyll").touch()
print("Built dist/index.html and dist/index.zh.html")
build_reference()
