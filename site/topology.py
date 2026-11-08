"""Purpose and data-flow map, before implementation vocabulary."""
from pathlib import Path
import html
import os

from routes import UNITS, UNIT_BY_KEY

OUT=Path(__file__).resolve().parent/'dist'
PURPOSES={
 'interfaces':{
  'short':('把应用接到压缩引擎','Connect the application'),
  'job':('应用需要交出输入、接收输出，并处理返回结果。缓冲区、回调和文件接口提供不同的使用方式，底层仍然复用压缩与解压引擎。','An application supplies input, receives output, and handles results. Buffers, callbacks, and file interfaces offer different ways to use the same compression and decoding engines.'),
  'input':('调用请求与应用数据','Requests and application data'),'output':('交付的数据与返回结果','Delivered data and results'),'position':(12,55)},
 'matching':{
  'short':('找到可以复用的重复片段','Find reusable repetitions'),
  'job':('重复片段可以用“回退距离、复制长度”描述。压缩器保留近期历史，寻找可以复用的内容；滑动窗口限制保留的历史范围，哈希链减少需要逐字节比较的候选。','A repeated passage can be described by a backward distance and a copy length. The compressor keeps recent history to find reusable content. A sliding window limits the retained history; hash chains reduce the candidates that need byte comparisons.'),
  'input':('原始输入与近期历史','Input bytes and recent history'),'output':('字面量和长度／距离对','Literals and length/distance pairs'),'position':(36,22)},
 'huffman':{
  'short':('让常见符号少用一些比特','Use fewer bits for frequent symbols'),
  'job':('符号的出现次数不同。给常见符号更短的码字，可以降低编码成本；解码器还必须知道使用了哪套编码，因此也需要描述码长。','Symbols occur at different frequencies. Shorter codes for frequent symbols can reduce the cost. The decoder also needs to know which codes were used, so code lengths must be described.'),
  'input':('符号及其出现次数','Symbols and their frequencies'),'output':('码长、码字与树描述','Lengths, codes, and tree descriptions'),'position':(60,22)},
 'output':{
  'short':('把编码组织成可交付字节','Turn codes into deliverable bytes'),
  'job':('码字长短不一，应用接收的却是整字节。这个组件选择块的表示，把编码接成字节，暂存尚未交付的部分，再随调用者提供空间逐步交付。','Codes have different lengths, while applications receive whole bytes. This component chooses a block representation, packs codes into bytes, and holds undelivered bytes until the caller supplies space.'),
  'input':('符号、码字与输出空间','Symbols, codes, and output space'),'output':('压缩块与待交付字节','Blocks and bytes awaiting delivery'),'position':(84,22)},
 'decoding':{
  'short':('从压缩比特恢复原文字节','Recover bytes from compressed bits'),
  'job':('解压器识别块和编码表，把比特还原成字面量与匹配。字面量直接成为字节；匹配则从历史逐字节复制，重新产生原来的内容。','The decoder reads blocks and code tables and recovers literals and matches. Literals become bytes directly; matches copy from history, one byte at a time, to recover the original content.'),
  'input':('压缩比特与可用历史','Compressed bits and available history'),'output':('恢复出的原文字节','Recovered original bytes'),'position':(84,60)},
 'streaming':{
  'short':('让分批输入和暂停能够接续','Resume across input and output batches'),
  'job':('应用常把大任务拆成多批输入和输出。输入暂时不够，或本轮输出空间用完时，流状态记住处理到哪里；下一次换了缓冲区仍能继续。zlib 与 gzip 的头尾信息也沿同一个任务处理。','Applications often divide a large task into input and output batches. When input or output space runs out, stream state remembers the progress so a later call can continue with new buffers. Zlib and gzip headers and trailers belong to the same task.'),
  'input':('分批输入与有限输出空间','Batched input and finite output space'),'output':('可暂停、可接续的状态','A state that can pause and resume'),'position':(60,82)},
 'checksums':{
  'short':('用校验值帮助发现数据损坏','Help detect damaged data'),
  'job':('zlib 与 gzip 封装记录未压缩数据的校验值。解压时重新计算并比较，帮助发现损坏。Adler 与 CRC 用很小的状态累积这些信息，也能跨缓冲区继续。','Zlib and gzip wrappers store a checksum of the uncompressed data. Recomputing and comparing it during decoding helps detect damage. Adler and CRC accumulate this information in a small state and continue across buffers.'),
  'input':('未压缩的数据','Uncompressed data'),'output':('校验值与比对结果','Checksums and comparison results'),'position':(36,82)},
 'lifecycle':{
  'short':('管理状态、借用与资源释放','Manage state and resource lifetime'),
  'job':('窗口和内部状态需要分配，也可能在中途分配失败。初始化、重置、复制和结束操作共同决定哪些内容可以保留、哪些必须清理。','Windows and internal state need storage, and allocation can fail. Initialization, reset, copy, and end determine what can be retained and what must be cleaned up.'),
  'input':('状态块、窗口和其他资源','State, windows, and other resources'),'output':('合法活状态与精确清理','Usable state and exact cleanup'),'position':(12,82)},
}

EDGES=[
 ('interfaces','matching','M120 470 C120 270 190 220 275 220','data'),
 ('matching','huffman','M445 220 L515 220','data'),
 ('huffman','output','M685 220 L755 220','data'),
 ('output','decoding','M840 300 L840 520','data'),
 ('decoding','interfaces','M755 600 C650 600 620 500 480 500 L205 550','data'),
 ('lifecycle','interfaces','M120 740 L120 630','support'),
 ('checksums','interfaces','M315 750 C280 650 255 580 205 570','support'),
 ('checksums','decoding','M445 820 C620 820 680 700 755 640','support'),
 ('streaming','output','M660 750 C730 640 770 490 790 300','support'),
 ('streaming','decoding','M685 800 C740 770 780 710 805 680','support'),
]


def target(current,route,lang,query=''):
    suffix='.zh.html' if lang=='zh' else '.html'
    return os.path.relpath(OUT/(route+suffix),current.parent).replace(os.sep,'/')+query


def purpose_box(current:Path,unit:dict,lang:str,proof:bool=False)->str:
    item=PURPOSES[unit['key']];i=lang=='en';t=lambda a,b:b if i else a
    route=target(current,'index',lang,'?topic='+unit['key']+'#algorithm-map')
    extra=t('这一章再把这些算法事实接到证明义务上。','This chapter then connects these algorithm facts to their proof obligations.') if proof else ''
    return f'<section class="bk-purpose" aria-label="{t("本章用途","Purpose of this chapter")}"><span>{t("这一环节的任务","THE JOB OF THIS COMPONENT")}</span><p>{item["job"][i]} {extra}</p><a href="{route}">{t("在全局图中定位","Locate this topic on the global map")} ↗</a></section>'


def topology(current:Path,lang:str)->str:
    i=lang=='en';t=lambda a,b:b if i else a
    body=f'''<section class="bk-topology" id="algorithm-map" aria-labelledby="topology-title" data-topology>
<header><div><span class="bk-eyebrow">ZLIB / {t('全局机制图','THE WHOLE SYSTEM')}</span><h2 id="topology-title">{t('压缩与解压的全局地图','The compression and decoding map')}</h2></div><p>{t('先看每个组件负责什么，再进入算法或证明。悬停、聚焦或点选节点，查看它的输入、输出和阅读入口。','See each component’s job before opening its algorithm or proof. Hover, focus, or select a node to explore its inputs, outputs, and reading links.')}</p></header>
<div class="bk-map-controls"><div class="bk-map-view" role="group" aria-label="{t('地图视图','Map view')}"><button type="button" data-map-view="graph" aria-pressed="true">{t('拓扑图','Topology')}</button><button type="button" data-map-view="list" aria-pressed="false">{t('按主题','Topics')}</button></div><button type="button" data-map-play data-play-label="{t('沿数据流播放','Follow the data flow')}" data-stop-label="{t('停止播放','Stop playback')}">{t('沿数据流播放','Follow the data flow')}</button><span data-map-progress aria-live="polite"></span></div>
<div class="bk-map-scroll"><div class="bk-map-canvas"><svg class="bk-map-edges" viewBox="0 0 1000 1000" preserveAspectRatio="none" aria-hidden="true"><defs><marker id="topology-arrow" viewBox="0 0 8 8" refX="7" refY="4" markerWidth="6" markerHeight="6" orient="auto"><path d="M0 0L8 4L0 8Z" fill="currentColor"/></marker></defs>'''
    for n,(source,destination,path,kind) in enumerate(EDGES):
        marker=' marker-end="url(#topology-arrow)"' if kind=='data' else ''
        body+=f'<path id="topology-edge-{n}" class="bk-map-edge bk-map-{kind}" data-from="{source}" data-to="{destination}" d="{path}"{marker}/>'
    body+='</svg>'
    for x,y,cn,en in [(22,16,'原始字节','Input bytes'),(48,16,'符号','Symbols'),(72,16,'编码','Codes'),(91,42,'压缩流','Compressed stream'),(48,47,'恢复的字节','Recovered bytes')]:
        body+=f'<span class="bk-map-label" style="left:{x}%;top:{y}%">{t(cn,en)}</span>'
    for unit in UNITS:
        key=unit['key'];p=PURPOSES[key];x,y=p['position']
        body+=f'<button type="button" class="bk-map-node" data-map-node="{key}" style="--node-x:{x}%;--node-y:{y}%" aria-controls="map-component-detail" aria-pressed="false"><span>{unit["title"][i]}</span><small>{p["short"][i]}</small></button>'
    body+='</div></div>'
    body+=f'<div class="bk-map-legend"><span><i></i>{t("编码块的主要数据流","Main data flow for coded blocks")}</span><span><i></i>{t("共同机制的支持与约束","Support from shared mechanisms")}</span><span>{t("stored 块直接存放原文字节","Stored blocks carry original bytes directly")}</span></div>'
    body+=f'<div class="bk-map-details" id="map-component-detail" data-map-details aria-label="{t("所选组件的作用","Selected component’s purpose")}"></div>'
    for unit in UNITS:
        key=unit['key'];p=PURPOSES[key]
        start=target(current,'chapters/'+unit['steps'][0]['key'],lang)
        proof=target(current,'chapters/'+unit['steps'][-1]['key'],lang)
        overview=target(current,'verification/'+key,lang)
        body+=f'<template data-map-detail="{key}"><div class="bk-map-description"><span>{t("这个组件负责什么","WHAT THIS COMPONENT DOES")}</span><h3>{unit["title"][i]}</h3><p>{p["job"][i]}</p></div><dl><dt>{t("输入","Input")}</dt><dd>{p["input"][i]}</dd><dt>{t("得到的结果","Result")}</dt><dd>{p["output"][i]}</dd></dl><div class="bk-map-reading"><a href="{start}">{t("从算法开始","Start with the algorithm")} →</a><a href="{proof}">{t("对应证明思路","The proof argument")} ↗</a><a href="{overview}">{t("本组章节","This topic’s chapters")} ↗</a></div></template>'
    body+=f'<noscript><p><a href="{target(current,"verification/index",lang)}">{t("查看所有主题与章节","Browse all topics and chapters")} →</a></p></noscript></section>'
    return body
