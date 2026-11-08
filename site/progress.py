"""Lay out the recorded target inventory without turning counts into proof claims."""
from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from pathlib import Path
import html
import re

GROUPS = {
    'queries': ('库信息与容量查询', 'Library queries', '读取版本、构建配置或计算容量界。', 'Read version and build information or compute capacity bounds.', 'public'),
    'checksums': ('校验和', 'Checksums', '计算、继续或组合 Adler-32 与 CRC-32。', 'Compute, continue, or combine Adler-32 and CRC-32.', 'public'),
    'inflate': ('解压流', 'Inflate streams', '初始化、推进和管理一个解压任务。', 'Initialize, advance, and manage a decoding task.', 'public'),
    'deflate': ('压缩流', 'Deflate streams', '初始化、推进和管理一个压缩任务。', 'Initialize, advance, and manage a compression task.', 'public'),
    'back': ('回调解码', 'Callback decoding', '由回调提供输入并接收解压输出。', 'Supply input and receive decoded output through callbacks.', 'public'),
    'gzip': ('gzip 文件', 'Gzip files', '连接压缩引擎、文件状态与外部 I/O。', 'Connect compression engines, file state, and external I/O.', 'public'),
    'buffers': ('完整缓冲区', 'Whole-buffer operations', '在一次封装调用中处理完整缓冲区。', 'Process a complete buffer through a convenience call.', 'public'),
    'lifecycle': ('调用序列与初始化', 'Call sequences and initialization', '连接单次调用，描述完整任务及初始化定义域。', 'Compose calls into tasks and describe initialization domains.', 'public'),
    'addresses': ('字节地址模型', 'Byte-address model', '解释对象、字节地址、对齐和偏移的关系。', 'Relate objects, byte addresses, alignment, and offsets.', 'support'),
    'fast': ('快速解码义务', 'Fast decoder obligations', '连接快速路径的读位、查表、复制与字节含义。', 'Connect fast-path bit reads, table lookup, copying, and byte meaning.', 'support'),
    'tables': ('解码表义务', 'Decode-table obligations', '说明构造出的表具有需要的内容与访问边界。', 'Establish the content and access bounds of constructed tables.', 'support'),
    'copy': ('历史复制数学', 'History-copy mathematics', '描述重叠复制以及历史保留的字节含义。', 'Describe overlapping copies and retained-history byte meaning.', 'support'),
    'internal': ('其他内部义务', 'Other internal obligations', '补齐字节视图与符号步骤等局部连接。', 'Connect byte views, token steps, and other local facts.', 'support'),
    'models': ('格式与 API 抽象模型', 'Format and API models', '研究抽象输入输出关系；与实际 C 执行目标分开。', 'Study abstract input/output relations separately from actual C execution.', 'model'),
}
STATUS = {
    'registered': ('已登记证明', 'Registered proof'),
    'local': ('本地证明（未登记）', 'Local proof, not registered'),
    'open': ('未完成', 'Not completed'),
    'blocked': ('存在阻塞', 'Blocked'),
}
COVERAGE = {
    'all': ('覆盖命题全部输入', 'All stated inputs'),
    'common': ('常用输入', 'Common inputs'),
    'default': ('默认输入', 'Default inputs'),
    'unproved': ('尚无完整输入覆盖', 'No complete input coverage'),
}


@dataclass(frozen=True)
class Target:
    node: str
    anchor: str
    name: str
    group: str
    coverage: str
    status: str
    blocked: bool
    original_url: str


@dataclass(frozen=True)
class Progress:
    targets: tuple[Target, ...]
    edges: tuple[tuple[str, str, str], ...]
    drawn_edges: tuple[tuple[str, str, str], ...]
    groups: tuple[str, ...]


def _section(source: str, heading: str) -> str:
    found = re.search(r'^## '+re.escape(heading)+r'\s*\n(.*?)(?=^## |\Z)', source, re.M | re.S)
    if not found:
        raise ValueError('Missing progress section: '+heading)
    return found[1]


def parse_progress(source: str) -> Progress:
    """Fail rather than silently dropping a target, state, or observed connection."""
    marker = re.search(r'<!-- proof-progress:start -->(.*?)<!-- proof-progress:end -->', source, re.S)
    if not marker:
        raise ValueError('Missing generated proof-progress region')
    block = re.search(r'```mermaid\n(.*?)\n```', marker[1], re.S)
    if not block:
        raise ValueError('Missing recorded target graph')
    graph = block[1]
    evidence = {}
    evidence_links = {}
    anchor_counts = Counter()
    evidence_group = None
    for line in marker[1].splitlines():
        group = re.search(r'<a id="group-([^"]+)"></a>', line)
        if group:
            evidence_group = group[1]
        row = re.match(r'^\| <a id="(target-[^"]+)"></a>\[([^\]]+)\]\([^)]+\) \| ([^|]+) \|', line)
        if row:
            anchor, name, state = row.groups()
            raw_anchor = anchor
            anchor_counts[anchor] += 1
            if anchor_counts[anchor] > 1:
                anchor += '--'+str(anchor_counts[anchor])
            evidence_links[(raw_anchor, name)] = anchor
            if 'Registered proof' in state:
                status = 'registered'
            elif 'Locally checked' in state:
                status = 'local'
            elif 'Blocked' in state:
                status = 'blocked'
            elif 'Not proved' in state:
                status = 'open'
            else:
                raise ValueError('Unknown evidence state: '+state)
            evidence[anchor] = (name, evidence_group, status)
    if not evidence:
        raise ValueError('No fixed-target evidence')
    urls = dict(re.findall(r'^  click (n\d+) href "([^"]+)"', graph, re.M))
    obstacles = set(re.findall(r'^  class (n\d+) obstacle$', graph, re.M))
    targets = []
    used = set()
    group_order = []
    group = None
    for line in graph.splitlines():
        heading = re.match(r'  subgraph ([\w-]+)\[', line)
        if heading:
            group = heading[1]
            if group not in GROUPS:
                raise ValueError('Progress group needs a bilingual description: '+group)
            group_order.append(group)
        node = re.match(r'    (n\d+)\["(.*?)"\]:::(\w+)$', line)
        if not node:
            continue
        node_id, label, coverage = node.groups()
        if coverage not in COVERAGE:
            raise ValueError('Unknown input coverage: '+coverage)
        clean = label.replace('<br/>', '').replace('Local exact proof', '').replace('Blocked', '')
        matches = [(key, row) for key, row in evidence.items() if row[1] == group and clean.endswith(row[0])]
        if matches:
            longest = max(len(row[0]) for _, row in matches)
            matches = [(key, row) for key, row in matches if len(row[0]) == longest]
        if len(matches) != 1:
            raise ValueError('Cannot map graph node to unique target: '+node_id+' '+label)
        anchor, (name, _, status) = matches[0]
        if anchor in used or node_id not in urls:
            raise ValueError('Duplicate or unlinked graph target: '+node_id)
        if (node_id in obstacles) != (status == 'blocked'):
            raise ValueError('Graph blocker and evidence disagree: '+node_id)
        if ('Local exact proof' in label) != (status == 'local'):
            raise ValueError('Graph local proof and evidence disagree: '+node_id)
        used.add(anchor)
        targets.append(Target(node_id, anchor, name, group, coverage, status, node_id in obstacles, urls[node_id]))
    if used != set(evidence):
        raise ValueError('Targets omitted from graph: '+str(set(evidence)-used))
    by_node = {target.node: target.anchor for target in targets}
    drawn = []
    for a, arrow, b in re.findall(r'^  (n\d+) (-->|-\.->) (n\d+)$', graph, re.M):
        if a not in by_node or b not in by_node:
            raise ValueError('Graph edge names an unknown target')
        drawn.append((by_node[a], by_node[b], 'proof' if arrow == '-->' else 'call'))
    edges = []
    for heading, kind in [('Observed proof dependencies', 'proof'), ('C function calls', 'call')]:
        body = _section(marker[1], heading)
        rows = re.findall(r'^\| \[([^\]]+)\]\(#([^\)]+)\) \| \[([^\]]+)\]\(#([^\)]+)\) \|', body, re.M)
        for a_name, a_raw, b_name, b_raw in rows:
            try:
                a = evidence_links[(a_raw, a_name)]
                b = evidence_links[(b_raw, b_name)]
            except KeyError as error:
                raise ValueError('Observed dependency names an unknown target') from error
            edges.append((a, b, kind))
    if len(set(edges)) != len(edges):
        raise ValueError('Duplicate observed dependency')
    if not set(drawn) <= set(edges):
        raise ValueError('Drawn edge absent from complete evidence index')
    summary = re.search(r'\*\*(\d+) fixed targets: (\d+) public and (\d+) supporting\.', marker[1])
    if summary:
        actual_public = sum(GROUPS[target.group][4] == 'public' for target in targets)
        if tuple(map(int, summary.groups())) != (len(targets), actual_public, len(targets)-actual_public):
            raise ValueError('Target summary and inventory disagree')
    exact = re.search(r'Exact proofs: (\d+) registered and (\d+) local only\.', marker[1])
    if exact:
        states = Counter(target.status for target in targets)
        if tuple(map(int, exact.groups())) != (states['registered'], states['local']):
            raise ValueError('Proof summary and evidence states disagree')
    return Progress(tuple(targets), tuple(edges), tuple(drawn), tuple(group_order))


def render_progress(original: str, lang: str, current: Path | None = None) -> str:
    """Return HTML for the graph block only; all evidence anchors remain below it."""
    data = parse_progress(original)
    zh = lang == 'zh'
    tr = lambda pair: pair[0 if zh else 1]
    t = lambda a, b: a if zh else b
    e = html.escape
    by_anchor = {target.anchor: target for target in data.targets}
    counts = Counter(target.status for target in data.targets)
    open_count = counts['open'] + counts['blocked']
    body = ['<section class="pg-map" data-progress-map aria-label="'+t('证明目标与依赖','Proof targets and dependencies')+'">']
    body.append('<header class="pg-intro"><p>'+t('选择一个组件，展开其中的目标，查看输入范围、证明状态和依赖关系。','Choose a component, then expand a target to inspect its input range, proof state, and dependencies.')+'</p></header>')
    body.append('<dl class="pg-totals">'+''.join('<div><dt>'+label+'</dt><dd>'+str(count)+'</dd></div>' for label, count in [(t('固定目标','Fixed targets'), len(data.targets)), (t('已登记精确证明','Registered exact proofs'), counts['registered']), (t('本地证明，尚未登记','Local, not registered'), counts['local']), (t('未完成目标','Uncompleted targets'), open_count)])+'</dl>')
    body.append('<p class="pg-reading-note">'+t('未完成目标中有 '+str(counts['blocked'])+' 项记录了阻塞。展开目标后，输入覆盖与证明登记状态分别列出。', str(counts['blocked'])+' uncompleted targets have recorded blockers. Input coverage and registration are listed separately inside each target.')+'</p>')
    lanes = [('public', ('公开接口与调用序列','Public interfaces and call sequences'), ('对应实际调用和完整任务。','Actual calls and whole tasks.')), ('support', ('实现层的局部义务','Implementation obligations'), ('支撑引擎证明的地址、查表与复制事实。','Address, lookup, and copying facts supporting engine proofs.')), ('model', ('抽象模型','Abstract models'), ('描述格式与 API 的数学性质。','Mathematical properties of formats and APIs.'))]
    for lane, title, desc in lanes:
        groups = [g for g in data.groups if GROUPS[g][4] == lane]
        lane_count = sum(target.group in groups for target in data.targets)
        body.append('<section class="pg-lane"><header><h4>'+tr(title)+'</h4><span>'+str(lane_count)+' '+t('项目标','targets')+'</span></header><p>'+tr(desc)+'</p><div class="pg-group-cards">')
        for group in groups:
            info = GROUPS[group]
            members = [target for target in data.targets if target.group == group]
            c = Counter(target.status for target in members)
            body.append('<a class="pg-group-card" href="#pg-group-'+group+'" data-progress-open="'+group+'"><span>'+str(len(members))+' '+t('项目标','targets')+'</span><strong>'+e(info[0 if zh else 1])+'</strong><p>'+e(info[2 if zh else 3])+'</p><small>'+t('登记 '+str(c['registered'])+' · 本地 '+str(c['local'])+' · 未完成 '+str(c['open']+c['blocked']), str(c['registered'])+' registered · '+str(c['local'])+' local · '+str(c['open']+c['blocked'])+' uncompleted')+'</small><b aria-hidden="true">↗</b></a>')
        body.append('</div></section>')
    body.append('<div class="pg-explorer"><header><h4>'+t('逐项查看目标与依赖','Inspect targets and dependencies')+'</h4><p>'+t('先选组件，或按名称和证据状态筛选。每项都保留通往完整证据表和记录源码的链接。','Choose a component, or filter by name and evidence state. Every target links to its full evidence entry and recorded source.')+'</p></header><div class="pg-controls" data-progress-controls hidden><label>'+t('目标名称','Target name')+'<input type="search" data-progress-search placeholder="'+t('例如 inflate、copy、crc32','For example: inflate, copy, crc32')+'"></label><label>'+t('组件','Component')+'<select data-progress-group><option value="">'+t('全部组件','All components')+'</option>'+''.join('<option value="'+g+'">'+e(GROUPS[g][0 if zh else 1])+'</option>' for g in data.groups)+'</select></label><label>'+t('证据状态','Evidence state')+'<select data-progress-status><option value="">'+t('全部状态','All states')+'</option>'+''.join('<option value="'+key+'">'+tr(value)+'</option>' for key, value in STATUS.items())+'</select></label><button type="button" data-progress-reset>'+t('清除筛选','Clear filters')+'</button><output data-progress-count aria-live="polite"></output></div>')
    for group in data.groups:
        members = [target for target in data.targets if target.group == group]
        body.append('<details class="pg-group" id="pg-group-'+group+'" data-progress-group-section="'+group+'"><summary><span>'+e(GROUPS[group][0 if zh else 1])+'</span><small>'+str(len(members))+' '+t('项目标','targets')+'</small></summary><ul class="pg-targets">')
        for target in members:
            body.append('<li data-progress-row data-progress-name="'+e(' '.join([target.name, *GROUPS[target.group][:4], *STATUS[target.status], *COVERAGE[target.coverage]]).lower(), quote=True)+'" data-progress-state="'+target.status+'"><details class="pg-target" id="pg-'+target.node+'"><summary><code>'+e(target.name)+'</code><span class="pg-badge pg-'+target.status+'">'+tr(STATUS[target.status])+'</span></summary><div class="pg-target-body"><dl class="pg-target-facts"><div><dt>'+t('输入覆盖','Input coverage')+'</dt><dd>'+tr(COVERAGE[target.coverage])+'</dd></div><div><dt>'+t('证据状态','Evidence state')+'</dt><dd>'+tr(STATUS[target.status])+'</dd></div></dl><nav class="pg-target-links" aria-label="'+t('目标证据链接','Target evidence links')+'"><a href="#'+target.anchor+'">'+t('完整目标与证据','Full target and evidence')+' ↗</a><a href="'+e(target.original_url, quote=True)+'">'+t('记录的阻塞说明' if target.blocked else '记录的目标源码', 'Recorded blocker' if target.blocked else 'Recorded target source')+' ↗</a></nav><div class="pg-dependencies">')
            connection_count = 0
            for kind, direction, title in [('proof', 'in', ('复用的证明','Proofs reused here')), ('proof', 'out', ('复用此结果的目标','Targets reusing this result')), ('call', 'in', ('实现调用的入口','Entries called by this implementation')), ('call', 'out', ('调用此入口的实现','Implementations calling this entry'))]:
                connected = [a if direction == 'in' else b for a, b, k in data.edges if k == kind and (b if direction == 'in' else a) == target.anchor]
                if not connected:
                    continue
                connection_count += len(connected)
                body.append('<section><h5>'+tr(title)+' <small>'+str(len(connected))+'</small></h5>')
                if connected:
                    body.append('<ul>'+''.join('<li><a href="#pg-'+by_anchor[key].node+'" data-progress-target-link><code>'+e(by_anchor[key].name)+'</code></a></li>' for key in connected)+'</ul>')
                else:
                    body.append('<p>'+t('未记录此类连接。','No recorded connection of this kind.')+'</p>')
                body.append('</section>')
            if not connection_count:
                body.append('<p class="pg-no-connections">'+t('本记录没有与其他固定目标的直接连接。','This record has no direct connection to another fixed target.')+'</p>')
            body.append('</div></div></details></li>')
        body.append('</ul></details>')
    body.append('<p class="pg-empty" data-progress-empty hidden>'+t('没有匹配目标。请清除筛选或使用较短的名称。','No matching target. Clear the filters or use a shorter name.')+'</p><p class="pg-footnote">'+str(sum(k == 'proof' for _, _, k in data.edges))+' '+t('条已观察证明复用关系','observed proof-reuse connections')+' · '+str(sum(k == 'call' for _, _, k in data.edges))+' '+t('条 C 调用关系。包含原图为减少交叉线而省略的直接连接；下方证据索引保留规范引用和其他支持关系。','C-call connections. Direct connections omitted from the old drawing to reduce crossings remain available here. The evidence index below retains specification references and other support relationships.')+'</p></div></section>')
    return ''.join(body)
