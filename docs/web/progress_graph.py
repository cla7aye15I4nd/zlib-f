"""Explicit component layout and complete data for the dependency diagrams."""
from collections import Counter
import html
import json

WIDTH, HEIGHT = 1230, 730
NODE_W, NODE_H = 225, 112
POSITIONS = {
    'tables': (25, 75), 'copy': (25, 225),
    'fast': (340, 75), 'models': (340, 225),
    'back': (655, 75), 'lifecycle': (970, 75), 'addresses': (655, 225),
    'queries': (25, 425), 'internal': (25, 585), 'checksums': (340, 585),
    'deflate': (655, 425), 'inflate': (655, 585),
    'buffers': (970, 425), 'gzip': (970, 585),
}


def graph_data(data, lang, groups, statuses):
    by_anchor={t.anchor:t for t in data.targets}
    index=0 if lang=='zh' else 1
    return {
        'groups':[{ 'id':g, 'label':groups[g][index], 'description':groups[g][index+2]} for g in data.groups],
        'targets':[{ 'id':t.node, 'anchor':t.anchor, 'name':t.name, 'group':t.group,
                     'status':t.status, 'statusLabel':statuses[t.status][index]} for t in data.targets],
        'edges':[{ 'from':by_anchor[a].node, 'to':by_anchor[b].node, 'kind':k} for a,b,k in data.edges],
    }


def render_graph(data, lang, groups, statuses):
    zh=lang=='zh';t=lambda a,b:a if zh else b;e=html.escape
    if set(data.groups)!=set(POSITIONS):
        raise ValueError('Each progress component needs an explicit diagram position')
    payload=graph_data(data,lang,groups,statuses)
    by_anchor={target.anchor:target for target in data.targets}
    aggregated=Counter((by_anchor[a].group,by_anchor[b].group,k) for a,b,k in data.edges if by_anchor[a].group!=by_anchor[b].group)
    internal=Counter(by_anchor[a].group for a,b,k in data.edges if by_anchor[a].group==by_anchor[b].group)
    assert sum(aggregated.values())+sum(internal.values())==len(data.edges)
    body=['<section class="pg-graph" id="pg-dependency-graph" data-dependency-graph aria-label="'+t('依赖关系图','Dependency diagram')+'">']
    body.append('<div class="pg-graph-toolbar" data-graph-toolbar hidden><div class="pg-graph-modes" role="group" aria-label="'+t('图的范围','Diagram scope')+'"><button type="button" data-graph-mode="groups" aria-pressed="true">'+t('组件关系图','Component graph')+'</button><button type="button" data-graph-mode="target" aria-pressed="false">'+t('目标上下游','Target dependencies')+'</button></div><label class="pg-graph-picker">'+t('选择目标','Choose a target')+'<select data-graph-picker>')
    for g in data.groups:
        body.append('<optgroup label="'+e(groups[g][0 if zh else 1],quote=True)+'">')
        for target in data.targets:
            if target.group==g:
                body.append('<option value="'+target.node+'"'+(' selected' if target.name=='inflate' else '')+'>'+e(target.name)+'</option>')
        body.append('</optgroup>')
    body.append('</select></label><div class="pg-graph-zoom" role="group" aria-label="'+t('缩放图形','Diagram zoom')+'"><button type="button" data-graph-zoom="out" aria-label="'+t('缩小','Zoom out')+'">−</button><output data-graph-zoom-level aria-label="'+t('缩放比例','Zoom level')+'">100%</output><button type="button" data-graph-zoom="fit" aria-pressed="true">'+t('适合宽度','Fit width')+'</button><button type="button" data-graph-zoom="reset">'+t('原始大小','Actual size')+'</button><button type="button" data-graph-zoom="in" aria-label="'+t('放大','Zoom in')+'">＋</button></div></div>')
    body.append('<div class="pg-graph-legend"><span><i class="pg-line-proof"></i>'+t('实线：证明依赖（上游 → 下游）','Solid: proof dependency (upstream → downstream)')+'</span><span><i class="pg-line-call"></i>'+t('虚线：被调用函数 → 调用者','Dashed: callee → caller')+'</span></div>')
    body.append('<p class="pg-graph-instruction" data-graph-instruction>'+t('从左向右看依赖。连线数字是跨组件关系条数；节点内列出组件内部关系。点击节点查看具体目标。','Read dependencies from left to right. Edge numbers count connections between components; nodes count internal connections. Select a node to inspect actual targets.')+'</p>')
    body.append('<div class="pg-graph-scroll" data-graph-scroll tabindex="0" aria-label="'+t('依赖图，可横向滚动','Dependency diagram, horizontally scrollable')+'"><div class="pg-graph-size" data-graph-size><div class="pg-graph-canvas" data-graph-canvas style="width:'+str(WIDTH)+'px;height:'+str(HEIGHT)+'px"><div class="pg-component-diagram" data-graph-groups>')
    body.append('<svg class="pg-graph-edges" viewBox="0 0 '+str(WIDTH)+' '+str(HEIGHT)+'" role="img" aria-label="'+t('组件之间的有向依赖连线','Directed dependencies between components')+'"><defs>')
    for kind in ('proof','call'):
        body.append('<marker id="pg-'+kind+'-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto"><path d="M1 1 L9 5 L1 9 Z"/></marker>')
    body.append('</defs>')
    for (a,b,kind),n in aggregated.items():
        ax,ay=POSITIONS[a];bx,by=POSITIONS[b]
        x1,y1=ax+NODE_W,ay+NODE_H/2;x2,y2=bx-5,by+NODE_H/2
        if (a,b)==('queries','buffers'):
            path=f'M{x1},{y1} H{ax+NODE_W+42} V380 H{bx-48} V{y2} H{x2}'
            lx,ly=(ax+NODE_W+bx)/2,370
        else:
            bend=(x1+x2)/2
            path=f'M{x1},{y1} C{bend},{y1} {bend},{y2} {x2},{y2}'
            lx,ly=bend,(y1+y2)/2-9
            if (a,b)==('inflate','buffers'):ly+=26
        title=e(groups[a][0 if zh else 1]+' → '+groups[b][0 if zh else 1]+' · '+str(n)+' '+t('条证明复用' if kind=='proof' else '条 C 调用',('proof-reuse connection' if kind=='proof' else 'C-call connection')+('' if n==1 else 's')))
        body.append('<g class="pg-diagram-edge pg-edge-'+kind+'" data-graph-edge data-kind="'+kind+'" data-edge-count="'+str(n)+'" data-from="'+a+'" data-to="'+b+'"><title>'+title+'</title><path d="'+path+'" marker-end="url(#pg-'+kind+'-arrow)"/><text x="'+str(lx)+'" y="'+str(ly)+'">'+str(n)+'</text></g>')
    body.append('</svg>')
    for x,cn,en in [(25,'基础操作','Basic operations'),(340,'局部机制','Local mechanisms'),(655,'引擎与状态','Engines and state'),(970,'接口与组合','Interfaces and composition')]:
        body.append('<span class="pg-graph-column" style="left:'+str(x)+'px">'+t(cn,en)+'</span>')
    for g in data.groups:
        x,y=POSITIONS[g];count=sum(target.group==g for target in data.targets)
        body.append('<a class="pg-graph-node" data-graph-group="'+g+'" data-internal-count="'+str(internal[g])+'" href="#pg-group-'+g+'" style="left:'+str(x)+'px;top:'+str(y)+'px;width:'+str(NODE_W)+'px;height:'+str(NODE_H)+'px"><strong>'+e(groups[g][0 if zh else 1])+'</strong><small>'+str(count)+' '+t('项目标','targets')+' · '+str(internal[g])+' '+t('条内部关系','internal connection' if internal[g]==1 else 'internal connections')+'</small></a>')
    body.append('</div><div class="pg-focus-diagram" data-graph-focus hidden></div></div></div></div>')
    body.append('<div class="pg-graph-detail" data-graph-detail aria-live="polite"><p>'+t('悬停或聚焦节点可突出相连的路径。目标图中，点击任意相邻目标可继续沿依赖查看。','Hover or focus a node to highlight connected paths. In the target graph, select a neighbor to continue along the dependencies.')+'</p></div>')
    encoded=json.dumps(payload,ensure_ascii=False,separators=(',',':')).replace('<','\\u003c')
    body.append('<script type="application/json" data-progress-graph-data>'+encoded+'</script></section>')
    return ''.join(body)
