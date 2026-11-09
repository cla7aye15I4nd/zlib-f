"""One implementation reading path, plus stable destinations for older URLs."""

def chapter(key,zh,en,sections):
    return {'key':key,'route':'index' if key=='round-trip' else 'read/'+key,'title':(zh,en),'anchors':[tuple(s.split('|')) for s in sections.split(';')]}

BOOK=[
 chapter('round-trip','一次完整的压缩与还原','One complete compression round trip','task|输入与结果|Input and result;formats|库与格式|Library and formats;protocol|调用协议|Calling protocol;example|八字节例子|The eight-byte example;configuration|配置|Configuration;correctness|正确性|Correctness'),
 chapter('deflate-matching','deflate：输入与匹配','deflate: input and matching','dispatch|主循环与策略|Main loop and strategies;configuration|级别与策略|Level and strategy;window|窗口布局|Window layout;refill|补充输入|Refilling input;hash|哈希链|Hash chains;search|候选比较与预算|Comparison and budgets;lazy|延迟匹配|Lazy matching;symbols|提交符号|Committing symbols;correctness|正确性|Correctness'),
 chapter('deflate-output','deflate：编码与输出','deflate: coding and output','records|符号记录|Symbol records;frequencies|频率统计|Frequencies;tree|构造编码树|Coding trees;lengths|码长限制|Length limits;canonical|规范编码|Canonical codes;blocks|块形式与成本|Block forms and costs;bits|位写入|Writing bits;pending|字节交付|Delivering bytes;storage|共享存储|Shared storage;flush|刷新与完成|Flush and completion;correctness|正确性|Correctness'),
 chapter('inflate-tables','inflate：读位与查表','inflate: reading bits and tables','entry|进入解码器|Entering the decoder;configuration|封装与窗口配置|Wrapper and window settings;dispatch|状态分派|State dispatch;input|读位与预读|Bit input;block-header|读取块头|Reading block headers;lengths|解读码长|Code lengths;tables|构造解码表|Building tables;lookup|查表与消费位数|Lookup and consumption;errors|错误描述|Invalid descriptions;correctness|正确性|Correctness'),
 chapter('inflate-copy','inflate：复制、暂停与快速路径','inflate: copying, suspension and the fast path','dispatch|执行符号|Executing symbols;literals|写出字面量|Writing literals;copy|重叠复制|Overlapping copies;window|当前输出与保留窗口|Output and retained history;suspension|暂停与接续|Suspension and continuation;fast|快速路径|The fast path;restore|回退、写回与记账|Backtracking and accounting;wrappers|尾部校验与完成|Trailer checks;correctness|正确性|Correctness'),
 chapter('stream-lifetime','调用协议与资源生命周期','Calling protocols and resource lifetime','init|初始化与配置|Initialization and settings;buffers|输入与输出记账|Input and output accounting;flush|刷新请求|Flush requests;dictionary|字典与预置位|Dictionaries and priming;reset|重置|Reset;copy|复制任务|Copying a task;allocation|分配与清理|Allocation and cleanup;callbacks|回调解码|Callback decoding;gzip|gzip 文件接口|Gzip file interfaces;correctness|正确性|Correctness;composition|整体证明结构|The complete proof structure'),
]
BY_KEY={c['key']:c for c in BOOK}
APPENDICES=[('checksums','校验算法','Checksum algorithms'),('interfaces','缓冲区、回调与文件','Buffers, callbacks and files')]
LEGACY={
 'window':('deflate-matching','window',{'array':'window','dimensions':'window','hash':'hash','slots':'hash','slide':'refill'}),
 'match-search':('deflate-matching','search',{'budget':'configuration','lazy':'lazy'}),
 'match-proof':('deflate-matching','correctness',{}),
 'huffman-tree':('deflate-output','tree',{}),
 'huffman-lengths':('deflate-output','lengths',{'canonical':'canonical','description':'canonical'}),
 'huffman-proof':('deflate-output','correctness',{}),
 'blocks':('deflate-output','blocks',{'symbols':'records'}),
 'bits':('deflate-output','bits',{'delivery':'pending'}),
 'storage':('deflate-output','storage',{}),'proof':('deflate-output','correctness',{}),
 'input-bits':('inflate-tables','input',{}),
 'decode-tables':('inflate-tables','tables',{'limits':'errors'}),
 'decode-copy':('inflate-copy','copy',{'dispatch':'dispatch','window':'window','margins':'fast','unrolling':'fast','writeback':'restore'}),
 'decode-proof':('inflate-tables','correctness',{}),
 'stream-state':('inflate-copy','suspension',{'history-window':'window','accounting':'restore'}),
 'wrappers':('inflate-copy','wrappers',{}),'stream-proof':('inflate-copy','correctness',{}),
 'state-operations':('stream-lifetime','reset',{'copy':'copy','dictionary':'dictionary','headers':'dictionary'}),
 'allocation':('stream-lifetime','allocation',{}),'ownership-proof':('stream-lifetime','correctness',{}),
 'interfaces':('stream-lifetime','buffers',{'pipeline':'flush','lifetime':'init'}),
}
SUPPLEMENTS={'adler':'checksums','crc':'checksums','checksum-proof':'checksums','buffers':'interfaces','callbacks':'interfaces','gzip':'interfaces','interfaces-proof':'interfaces'}
TOPICS={'matching':('deflate-matching','dispatch'),'huffman':('deflate-output','frequencies'),'output':('deflate-output','records'),'decoding':('inflate-tables','entry'),'streaming':('inflate-copy','suspension'),'lifecycle':('stream-lifetime','init'),'checksums':('appendix/checksums',''),'interfaces':('appendix/interfaces','')}
OVERVIEW={'bytes':('round-trip','example'),'layers':('round-trip','formats'),'search':('deflate-matching','window'),'lazy':('deflate-matching','lazy'),'huffman-tree':('deflate-output','tree'),'canonical':('deflate-output','canonical'),'blocks':('deflate-output','blocks'),'bit-order':('deflate-output','bits'),'lookup':('inflate-tables','lookup'),'stream':('inflate-copy','suspension')}

def route_for(key):
    return BY_KEY[key]['route'] if key in BY_KEY else key

def resolve_route(route,anchor=''):
    if route=='read/round-trip': return 'index',anchor
    if route in {'algorithms/index','verification/index'}:
        key,section=OVERVIEW.get(anchor,('round-trip','task'))
        return route_for(key),section
    if route.startswith('verification/') and route.split('/')[-1] in TOPICS:
        key,section=TOPICS[route.split('/')[-1]]
        return route_for(key),section
    if route.startswith(('sample/','chapters/')):
        key=route.split('/')[-1]
        if key in SUPPLEMENTS:return 'appendix/'+SUPPLEMENTS[key],key+('-'+anchor if anchor else '')
        if key in LEGACY:
            chapter,section,overrides=LEGACY[key]
            return route_for(chapter),overrides.get(anchor,section)
    return route,anchor

OVERVIEW.update({"write-proof":("inflate-copy","correctness"),"table-proof":("inflate-tables","correctness"),"overlay":("deflate-output","storage"),"huffman-bound":("deflate-output","correctness"),"history-proof":("inflate-copy","correctness"),"ownership":("stream-lifetime","correctness"),"trust":("reference/docs/trusted-base",""),"reading":("stream-lifetime","composition"),"verifying-zlib":("stream-lifetime","composition"),"how-zlib-works":("round-trip","task")})


from functools import lru_cache

@lru_cache(maxsize=12)
def chapter_sections(key,lang):
    import re
    from pathlib import Path
    source=(Path(__file__).resolve().parent/'content/book'/f'{key}.{lang}.md').read_text()
    return [(anchor,title.replace('`','').replace('*','')) for title,anchor in re.findall(r'^## (.*?) \{#([^}]+)\}\s*$',source,re.M)]
