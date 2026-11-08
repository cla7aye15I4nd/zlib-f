"""Render existing documentation and public targets without changing their statements."""
from __future__ import annotations

from pathlib import Path
from hashlib import sha256
from urllib.parse import urlsplit, unquote
import html
import json
import os
import re
import subprocess
import shutil

from markdown import Markdown

SITE = Path(__file__).resolve().parent
REPO = SITE.parent
OUT = SITE / "dist"
COMMIT = subprocess.check_output(['git','rev-parse','HEAD'],cwd=REPO,text=True).strip()
GITHUB = "https://github.com/cla7aye15I4nd/zlib-f/blob/"+COMMIT+"/"
TRACKED = set(subprocess.check_output(['git','ls-files','ZlibF','ZlibF.lean','docs','README.md','AGENTS.md','patches/README.md'],cwd=REPO,text=True).splitlines())
CHANGED = set(subprocess.check_output(['git','ls-files','-m','--others','--exclude-standard','ZlibF','ZlibF.lean','docs','README.md','AGENTS.md','patches/README.md'],cwd=REPO,text=True).splitlines())
GROUPS = {
    "deflate-stream": ("压缩流", "Compression streams"),
    "inflate-stream": ("解压流", "Decompression streams"),
    "inflate-back": ("回调解码", "Callback decoding"),
    "utility": ("缓冲区与库信息", "Buffers and library information"),
    "checksums": ("校验和", "Checksums"),
    "gz-file": ("gzip 文件", "Gzip files"),
}


def href(target: Path, current: Path) -> str:
    return os.path.relpath(target, current.parent).replace(os.sep, "/")


def resolve_doc(source: Path) -> Path:
    if source.name.endswith('.zh.md'):
        source=source.with_name(source.name.removesuffix('.zh.md')+'.md')
    if source.exists():
        return source
    relative=source.relative_to(REPO).as_posix()
    aliases={'docs/design/internal-contracts.md':'docs/spec/internal-contracts.md',
             'docs/safety.md':'docs/spec/safety.md'}
    candidate=aliases.get(relative,relative.replace('docs/api/','docs/spec/api/').replace('docs/format/','docs/spec/format/'))
    target=REPO/candidate
    return target if target.exists() else source


def documents() -> list[Path]:
    return [p for p in sorted((REPO/'docs').rglob('*.md')) if not p.name.endswith('.zh.md')]


def doc_path(source: Path, lang: str) -> Path:
    source=resolve_doc(source)
    # Older source snapshots predate the separate composition guide. Their
    # function-method guide contains the corresponding composition discussion.
    if not source.exists() and source == REPO/'docs/proof/stream-composition.md':
        source=REPO/'docs/proof/method.md'
    stem = source.relative_to(REPO).with_suffix("")
    return OUT / "reference" / (str(stem) + (".zh.html" if lang == "zh" else ".html"))


def md(text: str, *, baselevel: int = 1) -> tuple[str, str, list[dict]]:
    parser = Markdown(extensions=["fenced_code", "tables", "attr_list", "toc"],
                      extension_configs={"toc": {"baselevel": baselevel, "toc_depth": 6}})
    return parser.convert(text), parser.toc, parser.toc_tokens


def flatten(tokens: list[dict]) -> list[dict]:
    return [item for token in tokens for item in [token, *flatten(token.get("children", []))]]


def translated(source: Path) -> tuple[str, bool]:
    if not source.is_relative_to(REPO/'docs'):
        return source.read_text(),False
    native=source.with_name(source.stem+'.zh.md')
    if native.exists():
        return native.read_text(), True
    relative = source.relative_to(REPO / "docs")
    target = SITE / "translations" / relative.parent / (relative.stem + ".zh.md")
    original = source.read_text()
    if not target.exists():
        return original, False
    text = target.read_text()
    stamp = re.search(r"source-sha256:\s*([0-9a-f]{64})", text)
    if not stamp or stamp.group(1) != sha256(source.read_bytes()).hexdigest():
        return original, False
    return text, True


def paired_anchors(original: str, text: str) -> str:
    # Keep the source's heading IDs even when the visible heading is translated.
    # Fenced source is left byte-for-byte intact.
    _, _, tokens = md(original)
    ids = iter(item["id"] for item in flatten(tokens))
    lines = []
    fence = None
    for line in text.splitlines():
        marker = re.match(r"^\s*(`{3,}|~{3,})", line)
        if marker:
            if fence is None:
                fence = marker.group(1)[0]
            elif fence == marker.group(1)[0]:
                fence = None
        if fence is None and re.match(r"^#{1,6}\s+", line):
            key = next(ids, None)
            if key is None:
                raise ValueError("Translation has extra headings")
            line = re.sub(r"\s*\{#[^}]+\}\s*$", "", line) + " {#" + key + "}"
        lines.append(line)
    if next(ids, None) is not None:
        raise ValueError("Translation omits source headings")
    return "\n".join(lines)


def rewrite(body: str, source: Path, current: Path, lang: str) -> str:
    def replace(match):
        attr, raw = match.group(1), html.unescape(match.group(2))
        url = urlsplit(raw)
        if url.scheme or url.netloc or raw.startswith("mailto:"):
            return match.group(0)
        destination = (source.parent / unquote(url.path)).resolve() if url.path else source
        if destination.suffix=='.md' and destination.is_relative_to(REPO):
            destination=resolve_doc(destination)
        extras={REPO/'README.md',REPO/'AGENTS.md',REPO/'patches/README.md'}
        if destination.suffix == ".md" and (destination.is_relative_to(REPO / "docs") or destination in extras) and destination.exists():
            result = href(doc_path(destination, lang), current)
        elif destination.suffix == '.lean' and destination.is_relative_to(REPO) and destination.exists():
            result = href(source_path(destination, lang), current)
        elif destination.is_file() and destination.is_relative_to(REPO/'docs'):
            asset=OUT/'reference/assets'/destination.relative_to(REPO/'docs')
            asset.parent.mkdir(parents=True,exist_ok=True)
            shutil.copyfile(destination,asset)
            result=href(asset,current)
        elif destination.is_relative_to(REPO):
            result = GITHUB + destination.relative_to(REPO).as_posix()
        else:
            return match.group(0)
        if url.fragment:
            fragment=url.fragment
            if destination.suffix == '.lean' and re.fullmatch(r'L\d+-L\d+',fragment):
                fragment=fragment.split('-')[0]
            result += "#" + fragment
        return f'{attr}="{html.escape(result, quote=True)}"'
    return re.sub(r'\b(href|src)="([^"]+)"', replace, body)


def shell(title: str, body: str, current: Path, lang: str, *, toc: str = "", source: str = "",
          other: Path | None = None, intro: str = "", title_id: str = "") -> str:
    zh = lang == "zh"
    t = lambda a, b: a if zh else b
    asset = lambda name: href(OUT / "static" / name, current)
    root = href(OUT / ("index.zh.html" if zh else "index.html"), current)
    home = href(OUT / "reference" / ("index.zh.html" if zh else "index.html"), current)
    api = href(OUT / "reference" / ("api.zh.html" if zh else "api.html"), current)
    proof = href(OUT / "reference" / ("proofs.zh.html" if zh else "proofs.html"), current)
    sources = href(OUT / "reference" / ("sources.zh.html" if zh else "sources.html"), current)
    language = f'<a data-language href="{href(other, current)}" hreflang="{t("en", "zh")}">{t("EN", "中文")}</a>' if other else ""
    source_link=''
    if source:
        path=REPO/source
        digest=sha256(path.read_bytes()).hexdigest()
        source_link=f'<span>{t("此页源文件快照","Source snapshot")} · <code title="SHA-256 {digest}">{digest[:16]}</code></span>'
        if source in TRACKED:
            label=t('GitHub 基准版本','GitHub base version') if source in CHANGED else t('对应提交的原文','Source at the matching commit')
            source_link+=f' · <a href="{GITHUB+source}">{label} ↗</a>'
        if source in CHANGED:
            source_link+=f'<span class="rf-working-copy">{t("含工作区修改；此页快照与基准提交不同。","Includes working-copy changes; this snapshot differs from the base commit.")}</span>'
    reading = href(OUT/("algorithms/index.zh.html" if zh else "algorithms/index.html"),current)
    detailed = href(OUT/("verification/index.zh.html" if zh else "verification/index.html"),current)
    context = ''
    if source and ('deflate' in source or 'trees' in source):
        calls = href(OUT/("sample/interfaces.zh.html" if zh else "sample/interfaces.html"),current)
        output = href(OUT/("sample/blocks.zh.html" if zh else "sample/blocks.html"),current)
        argument = href(OUT/("sample/proof.zh.html" if zh else "sample/proof.html"),current)
        context = f'<div class="rf-reading-context"><span>{t("相关阅读路线","RELATED READING")}</span><a href="{calls}">{t("调用与接口地图","Calls and API map")} ↗</a><a href="{output}">{t("压缩输出的算法精读","Compression output in detail")} ↗</a><a href="{argument}">{t("对应的证明思路","The proof argument")} ↗</a></div>'
    revision = sha256((SITE / "static/reference.js").read_bytes()).hexdigest()[:12]
    return f'''<!doctype html><html lang="{lang}"><head>
<meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>{html.escape(title)} · zlib × Lean</title>
<link rel="icon" href="{asset('favicon.svg')}" type="image/svg+xml">
<link rel="stylesheet" href="{asset('base.css')}"><link rel="stylesheet" href="{asset('reference.css')}"><link rel="stylesheet" href="{asset('book.css')}">
<script defer src="{asset('reference.js')}?v={revision}"></script></head><body>
<a class="zl-skip" href="#content">{t('跳到正文','Skip to content')}</a>
<main class="rf-page"><nav class="article-topbar"><a class="article-brand" href="{root}">zlib × Lean</a><div><a href="https://www.dataisland.org/blog/">{t('博客','Writing')}</a>{language}</div></nav>
<nav class="rf-nav" aria-label="{t('项目导航','Project navigation')}"><a href="{root}">{t('阅读地图','Reading map')}</a><a class="rf-part" href="{reading}">01 {t('算法与接口','Algorithms & interfaces')}</a><a class="rf-part" href="{detailed}">02 {t('算法精读与验证','Algorithm detail & verification')}</a><a href="{api}">API</a><a href="{sources}">Lean</a><a href="{home}">{t('文档索引','Documentation')}</a></nav>
<div class="rf-layout"><article class="rf-body" id="content"><header class="rf-hero"><div class="rf-eyebrow">REFERENCE / ZLIB × LEAN</div><h1{(' id="'+html.escape(title_id,quote=True)+'"') if title_id else ''}>{html.escape(title)}</h1>{intro}<div class="rf-source">{source_link}</div></header>{context}{body}</article>
<aside class="rf-sidebar"><a class="rf-home" href="{home}">{t('文档索引','Documentation index')} ↗</a><nav class="rf-toc">{toc}</nav></aside></div>
<footer class="zl-footer"><a href="{root}">zlib × Lean</a><a href="{href(doc_path(REPO/'docs/overview.md',lang),current)}">{t('当前证明状态','Current proof status')}</a><span>{t('说明与命题不等于已接受证明','A statement is not an accepted proof')}</span></footer></main></body></html>'''


def write(path: Path, content: str) -> None:
    # Old generated documentation contains a few duplicate HTML anchors. Preserve
    # the first destination and disambiguate later IDs in the rendered view only.
    seen = {}
    def unique(match):
        key = match.group(1)
        seen[key] = seen.get(key, 0) + 1
        return f'id="{key}"' if seen[key] == 1 else f'id="{key}--{seen[key]}"'
    content = re.sub(r'\bid="([^"]+)"', unique, content)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content)


def goal_excerpts() -> dict[str, tuple[Path, int, str]]:
    result = {}
    for source in sorted((REPO / "ZlibF/Spec/Public").glob("*.lean")):
        text = source.read_text()
        for match in re.finditer(r"^def Goal\.(\w+)\b", text, re.M):
            start = match.start()
            tail = text[match.end():]
            end_match = re.search(r"\n(?:def |theorem |abbrev |structure |inductive |end\b|/--)", tail)
            end = match.end() + end_match.start() if end_match else len(text)
            previous = text.rfind("/--", 0, start)
            if previous >= 0:
                close = text.find("-/", previous)
                if close < start and not text[close+2:start].strip():
                    start = previous
            result[match.group(1)] = (source, text[:start].count("\n")+1, text[start:end].strip())
    return result


def render_docs() -> None:
    sources=documents()+[REPO/'README.md',REPO/'AGENTS.md',REPO/'patches/README.md']
    for source in sources:
        original = source.read_text()
        for lang in ("en", "zh"):
            text, available = translated(source) if lang == "zh" else (original, True)
            body, toc, tokens = md(paired_anchors(original, text))
            headings = flatten(tokens)
            title = re.sub(r"<[^>]+>", "", headings[0]["name"]) if headings else source.stem
            # The source title is already represented in the page header.
            body = re.sub(r"<h1\b[^>]*>.*?</h1>\s*", "", body, count=1, flags=re.S)
            current = doc_path(source, lang)
            body = rewrite(body, source, current, lang)
            toc = rewrite(toc, source, current, lang)
            if lang == "zh" and not available:
                body = '<p class="rf-language-note">此页保留当前英文原文。API 与核心证明指南另有完整中文对照；代码、公式和命题以原文为准。</p>' + body
            other = doc_path(source, "en" if lang == "zh" else "zh")
            write(current, shell(title, body, current, lang, toc=toc,
                                 source=source.relative_to(REPO).as_posix(), other=other,
                                 title_id=headings[0]['id'] if headings else ''))


def section(text: str, name: str) -> str:
    match = re.search(r"^## " + re.escape(name) + r"\s*$", text, re.M)
    if not match:
        raise ValueError(f"Missing documentary contract: {name}")
    tail = text[match.end():]
    end = re.search(r"\n## ", tail)
    return tail[:end.start()] if end else tail


def common_prefix(text: str, names: list[str]) -> str:
    starts = [m.start() for name in names if (m := re.search(r"^## " + re.escape(name) + r"\s*$", text, re.M))]
    return text[:min(starts)]


def render_api(manifest: dict) -> None:
    excerpts = goal_excerpts()
    all_entries = manifest["apis"]
    for lang in ("en", "zh"):
        zh = lang == "zh"
        t = lambda a, b: a if zh else b
        current = OUT / "reference" / ("api.zh.html" if zh else "api.html")
        other = OUT / "reference" / ("api.html" if zh else "api.zh.html")
        cards = []
        for entry in all_entries:
            name = entry["function"]
            source = REPO / entry["manual"].split("#")[0]
            original = source.read_text()
            text = translated(source)[0] if zh else original
            contract = section(text, name)
            group = source.stem
            index = 0 if zh else 1
            target = OUT / "reference/functions" / (name + (".zh.html" if zh else ".html"))
            opposite = target.with_name(name + (".html" if zh else ".zh.html"))
            without_code = re.sub(r"```[\s\S]*?```", "", contract).strip()
            summary = re.split(r"\n\s*\n", without_code)[0].replace("\n", " ")
            summary = re.sub(r"\[([^\]]+)\]\([^)]+\)", r"\1", summary)
            summary = re.sub(r"[*`]", "", summary)
            keywords = " ".join((name, GROUPS[group][index], re.sub(r"\s+", " ", contract)))
            scope = entry["scope"]
            cards.append(f'<a class="rf-api-row" data-group="{group}" data-scope="{scope}" data-search="{html.escape(keywords,quote=True)}" href="{href(target,current)}"><code>{name}</code><span>{html.escape(summary)}</span><small>{html.escape(GROUPS[group][index])}{" · Windows" if scope != "lp64-linux" else ""}</small><b aria-hidden="true">↗</b></a>')
            body, _, _ = md(contract, baselevel=2)
            body = rewrite(body, source, target, lang)
            labels={'Domain':'定义域','Pre':'前置条件','Post':'返回与保证','Effects':'内存与状态效果','Errors':'错误路径','Edges':'边界情况','Results':'返回码','Accounting':'计数记账','Ownership':'所有权'}
            seen_labels=set()
            def clause(match):
                key=match.group(1)
                identifier=f' id="{key.lower()}"' if key not in seen_labels else ''
                seen_labels.add(key)
                label=f'{labels[key]} <small>{key}</small>' if zh else key
                return f'<strong class="rf-contract-label"{identifier}>{label}</strong>'
            body=re.sub(r'<strong>(Domain|Pre|Post|Effects|Errors|Edges|Results|Accounting|Ownership)[.:]?</strong>',clause,body)
            names = [item["function"] for item in all_entries if item["manual"].split("#")[0] == entry["manual"].split("#")[0]]
            common, _, _ = md(common_prefix(text, names), baselevel=2)
            common = re.sub(r"<h2\b[^>]*>.*?</h2>\s*", "", common, count=1, flags=re.S)
            common = rewrite(common, source, target, lang)
            body = f'<p class="rf-scope-note">{t("本条采用文档明示的定义域。共同前提同样适用；下方另列原始 Lean 目标，不把两者混同。","This entry uses its explicitly documented domain. Shared conditions also apply; the original Lean target is shown separately below.")}</p>' + body
            body += f'<details class="rf-common"><summary>{t("本组共同前提与范围","Shared conditions and scope")}</summary>{common}</details>'
            goal = entry.get("goal")
            if goal:
                short = goal.rsplit(".", 1)[-1]
                if short not in excerpts:
                    raise ValueError(f"Public target not found: {goal}")
                goal_source, line, code = excerpts[short]
                context = source_path(goal_source, lang)
                body += f'<section class="rf-formal" id="formal-target"><h2>{t("形式化目标","Formal target")}</h2><p><code>{html.escape(goal)}</code></p><p>{t("以下逐字摘自当前源码。命题存在不代表该目标已经证明；接受状态统一见 overview。","Verbatim from the current source. A target declaration is not an accepted proof; the overview records acceptance status.")}</p><pre><code class="language-lean">{html.escape(code)}</code></pre><a href="{href(context,target)}#L{line}">{t("完整定义与上下文","Complete definition and context")} ↗</a></section>'
            else:
                body += f'<p class="rf-language-note">{t("此平台专用条目没有默认 LP64 构建目标。","This platform-specific entry has no default LP64 target.")}</p>'
            category = doc_path(source, lang)
            related = ''.join(f'<li><a href="{href(OUT/"reference/functions"/(n+(".zh.html" if zh else ".html")),target)}">{n}</a></li>' for n in names)
            sidebar = f'<h3>{GROUPS[group][index]}</h3><ul>{related}</ul>'
            intro = f'<p>{html.escape(summary)}</p><a class="rf-category" href="{href(category,target)}">{t("完整章节与共同规则","Full chapter and shared rules")} ↗</a>'
            write(target, shell(name, body, target, lang, toc=sidebar,
                                source=entry["manual"].split("#")[0], other=opposite, intro=intro))
        default_count = sum(item["scope"] == "lp64-linux" for item in all_entries)
        controls = f'<div class="rf-search"><label for="api-search">{t("查找函数或约定","Find a function or contract")}</label><input id="api-search" type="search" autocomplete="off" placeholder="{t("函数名、Z_MEM_ERROR、字典、所有权…","Function, Z_MEM_ERROR, dictionary, ownership…")}"><div class="rf-filters"><label>{t("分组","Group")}<select id="api-group" aria-label="{t('分组','Group')}"><option value="">{t("全部分组","All groups")}</option>'+''.join(f'<option value="{key}">{value[0 if zh else 1]}</option>' for key,value in GROUPS.items())+f'</select></label><label>{t("配置","Build")}<select id="api-scope" aria-label="{t('配置','Build')}"><option value="">{t("全部条目","All entries")}</option><option value="lp64-linux">LP64 Linux</option><option value="windows">Windows</option></select></label><output id="api-count" aria-live="polite">{len(all_entries)} {t("个条目","entries")}</output></div></div>'
        banner = f'<p class="rf-scope-note">{default_count} {t("个默认构建入口，另含 Windows gzopen_w。各条完整保留签名、定义域、前置条件、结果、内存效果和错误路径。文档契约与注册目标的范围可能不同，均原样呈现。","default-build entries, plus Windows gzopen_w. Every entry retains its signature, domain, preconditions, results, memory effects, and error paths. Documentary contracts and registered goals may have different scopes; both are preserved.")}</p>'
        body = banner + controls + '<div class="rf-api-list">'+''.join(cards)+'</div><p id="api-empty" hidden>'+t('没有匹配项。试试函数名的一部分。','No matches. Try part of a function name.')+'</p>'
        write(current, shell(t("API 契约", "API contracts"), body, current, lang,
                             other=other, intro=f'<p>{t("完整公开接口索引","The complete public-interface index")}</p>'))


def render_portals() -> None:
    for lang in ("en", "zh"):
        zh = lang == "zh"
        t = lambda a, b: a if zh else b
        suffix = ".zh.html" if zh else ".html"
        current = OUT / "reference" / ("index"+suffix)
        other = current.with_name("index.html" if zh else "index.zh.html")
        def link(file, label):
            return f'<a href="{href(doc_path(REPO/"docs"/file,lang),current)}">{label} ↗</a>'
        body = f'<p class="rf-intro">{t("导读、完整接口契约和证明细节共用同一套文档。原始内容在构建时读入，没有删去长推导或错误路径。","The guide, complete interface contracts, and detailed proofs share one documentation system. Original material is read at build time, preserving long arguments and error paths.")}</p>'
        body += f'<section class="rf-portal-section"><span>01 / ZLIB</span><h2>{t("算法与接口","Algorithms and interfaces")}</h2><a class="rf-portal-primary" href="api{suffix}">{t("全部公开 API 契约","All public API contracts")} ↗</a><div class="rf-link-grid">'+link('api/contracts.md',t('契约术语与定义域','Contract vocabulary and domains'))+link('api/streams.md',t('流、缓冲区与调用顺序','Streams, buffers, and call order'))+link('format/README.md',t('DEFLATE、zlib 与 gzip 格式','DEFLATE, zlib, and gzip formats'))+link('format/model.md',t('格式的 Lean 模型','The Lean format model'))+'</div></section>'
        body += f'<section class="rf-portal-section"><span>02 / VERIFICATION</span><h2>{t("形式化验证","Formal verification")}</h2><a class="rf-portal-primary" href="proofs{suffix}">{t("inflate 与 deflate 的证明路线","Inflate and deflate proof routes")} ↗</a><div class="rf-link-grid">'+link('design/architecture.md',t('翻译与运行时架构','Translation and runtime architecture'))+link('design/internal-contracts.md',t('内部函数义务','Internal helper obligations'))+link('proof/method.md',t('单函数证明方法','Proving one function'))+link('proof/stream-composition.md',t('跨调用组合','Composition across calls'))+link('safety.md',t('安全目标与调用者义务','Safety goals and caller obligations'))+link('trusted-base.md',t('信任边界','Trusted base'))+link('deviations.md',t('范围限制','Scope restrictions'))+link('checking/README.md',t('审计、变异与检查','Audits, mutations, and checks'))+link('overview.md',t('当前状态与全部剩余工作','Current status and remaining work'))+'</div></section>'
        body += f'<details class="rf-common"><summary>{t("原有文档的完整目录","Complete original documentation tree")}</summary><ul>'
        for file in documents():
            body += '<li>'+link(file.relative_to(REPO/'docs').as_posix(),html.escape(file.relative_to(REPO/'docs').as_posix()))+'</li>'
        body += '</ul></details>'
        write(current,shell(t('文档索引','Documentation'),body,current,lang,other=other))
        current=OUT/'reference'/('proofs'+suffix)
        other=current.with_name('proofs.html' if zh else 'proofs.zh.html')
        engine=[('inflate','inflate.md',t('解压引擎','Decompression engine'),t('窗口内容、真实模式、位前缀、查表、退出与跨调用历史。','Window contents, actual modes, supporting bits, lookup, exits, and call histories.')),
                ('deflate','deflate.md',t('压缩引擎','Compression engine'),t('窗口、哈希链、匹配搜索、策略循环、符号账本、块输出与默认封装。','Windows, hash chains, matching, strategy loops, symbol ledgers, block output, and the default wrapper.'))]
        body=f'<p class="rf-scope-note">{t("这里保留完整论证指南，不把它们当作已完成的全库证明。具体命题、前提和接受范围必须分别查看。","These are complete argument guides, not a claim that the whole library is proved. Inspect exact targets, premises, and acceptance scope separately.")}</p><div class="rf-engine-grid">'
        for name,file,label,desc in engine:
            target=doc_path(REPO/'docs/proof'/file,lang)
            fn=OUT/'reference/functions'/(name+suffix)
            body+=f'<section><span>{name}.c</span><h2>{label}</h2><p>{desc}</p><a href="{href(target,current)}">{t("完整证明细节","Full proof details")} →</a><a href="{href(fn,current)}#formal-target">{t("公开契约与精确目标","Public contract and exact target")} →</a></section>'
        body+='</div><div class="rf-link-grid">'
        for file,label in [('inftrees.md',t('解码表构造','Decode-table construction')),('inffast.md',t('快速解码','Fast decoding')),('trees.md',t('树、位输出与共享缓冲区','Trees, bit emission, and shared storage')),('stream-composition.md',t('两个引擎的组合架构','Composition of the two engines')),('method.md',t('证明方法与不变量','Proof method and invariants')),('adler32.md','Adler-32'),('crc32.md','CRC-32'),('zutil.md',t('分配与工具函数','Allocation and utilities'))]:
            body+=link('proof/'+file,label)
        body+='</div>'
        body+=f'<p><a href="targets{suffix}">{t("调用序列与初始化定义域的精确目标","Exact targets for call sequences and initialization domains")} →</a></p>'
        write(current,shell(t('证明细节','Proof details'),body,current,lang,other=other))


def source_path(source: Path, lang: str) -> Path:
    return OUT/'reference/source'/source.relative_to(REPO).with_suffix('.zh.html' if lang=='zh' else '.html')


def render_sources() -> None:
    sources=set((REPO/'ZlibF').rglob('*.lean'))|{REPO/'ZlibF.lean'}
    for document in (REPO/'docs').rglob('*.md'):
        for raw in re.findall(r'\]\(([^)]+\.lean(?:#[^)]*)?)\)',document.read_text()):
            url=urlsplit(raw)
            if not url.scheme and not url.netloc:
                linked=(document.parent/unquote(url.path)).resolve()
                if linked.is_relative_to(REPO) and linked.exists():sources.add(linked)
    sources=sorted(sources)
    catalog=[]
    for source in sources:
        raw=source.read_text()
        relative=source.relative_to(REPO).as_posix()
        group=relative.split('/')[1] if '/' in relative else 'Root'
        symbols=re.findall(r'^(?:(?:private|protected|noncomputable)\s+)?(?:def|theorem|lemma|structure|inductive|abbrev|class)\s+([\w.\']+)',raw,re.M)
        catalog.append((source,group,symbols))
        for lang in ('en','zh'):
            zh=lang=='zh';current=source_path(source,lang)
            other=source_path(source,'en' if zh else 'zh')
            body='<p class="rf-scope-note">'+('当前源码原文。此视图展示命题及其定义上下文，不声明这些目标已经证明。' if zh else 'Current source, verbatim. This view shows targets and their definition context; it does not claim these targets are proved.')+'</p>'
            lines=[]
            for i,line in enumerate(raw.splitlines(),1):
                escaped=html.escape(line)
                imported=re.match(r'^import\s+(ZlibF\S*)\s*$',line)
                if imported:
                    pieces=re.findall(r'«([^»]+)»|([\w\']+)',imported.group(1))
                    dependency=REPO/('/'.join(a or b for a,b in pieces)+'.lean')
                    if dependency.exists():
                        escaped='import <a href="'+href(source_path(dependency,lang),current)+'">'+html.escape(imported.group(1))+'</a>'
                lines.append(f'<span class="rf-source-line" id="L{i}"><a href="#L{i}">{i}</a>{escaped}\n</span>')
            body+='<pre class="rf-source-code"><code>'+''.join(lines)+'</code></pre>'
            write(current,shell(source.name,body,current,lang,other=other,source=relative))
    for lang in ('en','zh'):
        zh=lang=='zh';suffix='.zh.html' if zh else '.html';current=OUT/'reference'/('sources'+suffix)
        other=current.with_name('sources.html' if zh else 'sources.zh.html')
        title='Lean 源码与证明正文' if zh else 'Lean source and proof bodies'
        body='<p class="rf-scope-note">'+('包含实际证明、规格、数学、运行时和翻译。这里展示当前源码，不将文件存在或声明数量当成证明接受状态。' if zh else 'Actual proofs, specifications, mathematics, runtime, and translations. These are current source snapshots; neither file presence nor declaration counts establish acceptance.')+'</p>'
        body+='<div class="rf-search"><label for="api-search">'+('搜索模块或声明名' if zh else 'Search modules or declaration names')+'</label><input id="api-search" type="search" autocomplete="off"><div class="rf-filters"><label>'+('分组' if zh else 'Group')+'<select id="api-group"><option value="">'+('全部模块' if zh else 'All modules')+'</option>'+''.join('<option>'+name+'</option>' for name in ['Proof','Spec','Math','Runtime','Zlib','Root'])+'</select></label><select id="api-scope" hidden><option value=""></option></select><output id="api-count" aria-live="polite"></output></div></div><div class="rf-api-list">'
        for source,group,symbols in catalog:
            relative=source.relative_to(REPO).as_posix()
            keys=' '.join([relative,*symbols])
            body+=f'<a class="rf-api-row rf-source-row" data-group="{group}" data-scope="source" data-search="{html.escape(keys,quote=True)}" href="{href(source_path(source,lang),current)}"><code>{html.escape(source.name)}</code><span>{html.escape(relative)}</span><small>{group}</small><b>↗</b></a>'
        body+='</div><p id="api-empty" hidden>'+('没有匹配模块。' if zh else 'No matching modules.')+'</p>'
        write(current,shell(title,body,current,lang,other=other))


def render_targets(manifest: dict) -> None:
    excerpts=goal_excerpts()
    for lang in ('en','zh'):
        zh=lang=='zh';suffix='.zh.html' if zh else '.html'
        current=OUT/'reference'/('targets'+suffix)
        other=current.with_name('targets.html' if zh else 'targets.zh.html')
        body='<p class="rf-scope-note">'+('单次调用目标之外，以下命题固定合法调用序列与初始化定义域。所有文本逐字取自当前源码；目标的存在不是证明。' if zh else 'Beyond individual calls, these targets fix legal call sequences and initialization domains. Every statement is taken verbatim from the current source. The existence of a target is not a proof.')+'</p>'
        for category in ('sequence_goals','nonvacuity_goals'):
            body+='<h2>'+({'sequence_goals':('调用序列','Call sequences'),'nonvacuity_goals':('初始化定义域','Initialization domains')}[category][0 if zh else 1])+'</h2>'
            for goal in manifest[category]:
                name=goal.rsplit('.',1)[-1]
                source,line,code=excerpts[name]
                body+=f'<section id="{name}"><h3>{name}</h3><pre><code class="language-lean">{html.escape(code)}</code></pre><a href="{href(source_path(source,lang),current)}#L{line}">{"完整上下文" if zh else "Complete context"} ↗</a></section>'
        write(current,shell('精确证明目标' if zh else 'Exact proof targets',body,current,lang,other=other))


def render_proof_routes() -> None:
    routes=json.loads((SITE/'content/proof-routes.json').read_text())
    for lang in ('en','zh'):
        zh=lang=='zh';suffix='.zh.html' if zh else '.html'
        current=OUT/'reference'/('proofs'+suffix)
        text=current.read_text()
        body='<section class="rf-proof-routes"><h2>'+('实际证明的阅读路线' if zh else 'Reading the actual proofs')+'</h2><p>'+('以下链接直接进入本次源码快照中存在的 Lean 声明与证明正文。每项写明声明的小范围与前提，不能把局部引理当成完整公开目标。' if zh else 'These links enter Lean declarations and proof bodies present in this source snapshot. Each item states its narrow result and premises; a local lemma is not the complete public target.')+'</p>'
        for engine in ('inflate','deflate'):
            body+=f'<h3>{engine}</h3><ol class="rf-proof-steps">'
            for route in routes:
                if route['engine']!=engine:continue
                source=REPO/route['path'];name=route['declaration']
                # A curated route may refer to a later development snapshot.
                # Never present a missing declaration as evidence in an older one.
                if not source.exists():continue
                raw=source.read_text()
                found=re.search(r'^(?:(?:private|protected|noncomputable)\s+)?(?:theorem|lemma|def)\s+'+re.escape(name)+r'\b',raw,re.M)
                if not found:continue
                line=raw[:found.start()].count('\n')+1
                body+=f'<li><a href="{href(source_path(source,lang),current)}#L{line}">{html.escape(route["topic"][lang])}</a><p>{html.escape(route["summary"][lang])}</p><small>{html.escape(route["premise"][lang])}</small><code>{html.escape(name)}</code></li>'
            body+='</ol>'
        body+='</section>'
        text=text.replace('</article>',body+'</article>',1)
        write(current,text)


def build_reference() -> None:
    manifest=json.loads((REPO/'tests/audit/public-api.json').read_text())
    render_docs()
    render_sources()
    render_api(manifest)
    render_targets(manifest)
    render_portals()
    render_proof_routes()
    count=len(list((OUT/'reference').rglob('*.html')))
    print(f"Built {count} reference pages; {len(manifest['apis'])} public API entries per language")
