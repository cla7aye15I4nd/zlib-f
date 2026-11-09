"""Three complete zlib essays and destinations for published reading links."""
from functools import lru_cache
from pathlib import Path
import re


def article(key, route, zh, en, sections):
    return {'key':key,'route':route,'title':(zh,en),'anchors':[tuple(s.split('|')) for s in sections.split(';')]}


BOOK=[
    article('foundations','index','基础压缩：LZ77 与 Huffman','A complete codec: LZ77 and Huffman',
            'purpose|无损压缩的任务|The lossless task;lz77|重复片段与复制指令|Repeated passages and copies;huffman|符号频率与编码|Symbol frequencies and codes;codebook|传递编码规则|Transmitting the codebook;packet|完整数据表示|The complete packet;decode|独立还原|Independent decoding;deflate|连接 DEFLATE|Connecting to DEFLATE;roadmap|后续需求|What follows'),
    article('optimizations','read/optimizations','zlib 的实现与优化','Implementing and optimizing zlib',
            'costs|基本方案的成本|Costs of the baseline;window|回引范围与存储|References and storage;refill|搬移与补充输入|Sliding and refilling;hash|候选索引|Candidate indexing;search|搜索与预算|Search and budgets;lazy|延迟匹配|Lazy matching;records|记录与频率|Records and frequencies;huffman|构造编码|Constructing codes;lengths|限制码长|Limiting code lengths;canonical|规范编码|Canonical codes;blocks|块选择|Block selection;bits|位写入|Writing bits;storage|存储复用|Reusing storage;decode-bits|读位与预读|Bit input and lookahead;tables|解码表|Decode tables;lookup|查表|Table lookup;copy|复制|Copying;fast|快速路径|The fast path;configuration|配置与取舍|Settings and tradeoffs'),
    article('features','read/features','zlib 的功能扩展：流式处理与校验','Extending zlib: streams and integrity',
            'needs|应用的新需求|Application requirements;stream|持续的任务|A continuing task;buffers|分批输入输出|Input and output batches;flush|刷新与完成|Flush and completion;dictionary|字典|Dictionaries;reset|重置|Reset;copy|复制任务|Copying a task;wrappers|封装|Wrappers;checksums|内容校验|Checking the content;adler|Adler-32|Adler-32;crc|CRC-32|CRC-32;combine|组合分段结果|Combining chunks;interfaces|应用接口|Application interfaces;errors|错误与资源|Errors and resources;program|实际 C 调用|Actual C calls;playground|运行自己的输入|Run your own input'),
]
BY_KEY={item['key']:item for item in BOOK}
APPENDICES=[]
CHECKSUM_PARTS={'adler','crc','checksum-proof'}
OLD_BOOK=['round-trip','deflate-matching','deflate-output','inflate-tables','inflate-copy','stream-lifetime']

# Main article keys and required section anchors, rather than implementation names.
LEGACY={
 'window':('optimizations','window'), 'match-search':('optimizations','search'),
 'huffman-tree':('optimizations','huffman'), 'huffman-lengths':('optimizations','lengths'),
 'blocks':('optimizations','blocks'), 'bits':('optimizations','bits'),
 'storage':('optimizations','storage'), 'input-bits':('optimizations','decode-bits'),
 'decode-tables':('optimizations','tables'), 'decode-copy':('optimizations','copy'),
 'stream-state':('features','buffers'), 'wrappers':('features','wrappers'),
 'state-operations':('features','reset'), 'allocation':('features','errors'),
 'interfaces':('features','interfaces'), 'adler':('features','adler'),
 'crc':('features','crc'), 'buffers':('features','buffers'),
 'callbacks':('features','interfaces'), 'gzip':('features','interfaces'),
}
PROOF_DESTINATIONS={
 'match-proof':'deflate', 'huffman-proof':'trees', 'proof':'trees',
 'decode-proof':'inftrees', 'stream-proof':'inflate', 'ownership-proof':'zutil',
 'checksum-proof':'adler32', 'interfaces-proof':'buffers',
}
SUPPLEMENTS={key:'interfaces' for key in ['buffers','callbacks','gzip','interfaces-proof']}
TOPICS={
 'matching':('optimizations','hash'), 'huffman':('optimizations','huffman'),
 'output':('optimizations','bits'), 'decoding':('optimizations','tables'),
 'streaming':('features','stream'), 'lifecycle':('features','reset'),
 'checksums':('features','checksums'), 'interfaces':('features','interfaces'),
}
OVERVIEW={
 'bytes':('foundations','lz77'), 'layers':('features','wrappers'),
 'search':('optimizations','search'), 'lazy':('optimizations','lazy'),
 'huffman-tree':('foundations','huffman'), 'canonical':('foundations','codebook'),
 'blocks':('optimizations','blocks'), 'bit-order':('foundations','packet'),
 'lookup':('optimizations','lookup'), 'stream':('features','stream'),
 'overlay':('optimizations','storage'), 'reading':('foundations','roadmap'),
 'how-zlib-works':('foundations','purpose'), 'task':('foundations','purpose'),
 'formats':('features','wrappers'), 'example':('features','program'),
 'protocol':('features','stream'), 'configuration':('optimizations','configuration'),
 'playground':('features','playground'), 'algorithms':('foundations','purpose'),
 'algorithm-map':('foundations','roadmap'),
 'write-proof':('reference/docs/proof/inflate',''),
 'table-proof':('reference/docs/proof/inftrees',''),
 'huffman-bound':('reference/docs/proof/trees',''),
 'history-proof':('reference/docs/proof/inflate',''),
 'ownership':('reference/docs/spec/safety',''),
 'trust':('reference/docs/trusted-base',''),
 'verifying-zlib':('reference/docs/proof/method',''),
 'verification':('reference/docs/proof/method',''),
 'correctness':('reference/docs/proof/method',''),
}


def route_for(key):
    return BY_KEY[key]['route'] if key in BY_KEY else key


def destination(key, section=''):
    return route_for(key),section


def checksum_destination(anchor):
    if anchor.startswith('checksum-proof'):
        return 'reference/docs/proof/adler32',''
    if anchor.startswith('adler'):
        return destination('features','adler')
    if anchor.startswith('crc'):
        return destination('features','crc')
    return destination('features','checksums')


def resolve_route(route,anchor=''):
    if route=='algorithms/index':return destination(*OVERVIEW.get(anchor,('foundations','purpose')))
    if route=='verification/index':return 'reference/docs/proof/method',''
    if route.startswith('verification/') and route.split('/')[-1] in TOPICS:
        return destination(*TOPICS[route.split('/')[-1]])
    if route=='appendix/checksums':return checksum_destination(anchor)
    if route=='appendix/interfaces':
        if 'proof' in anchor:return 'reference/docs/proof/buffers',''
        return destination('features','interfaces')
    if route.startswith(('sample/','chapters/')):
        key=route.split('/')[-1]
        if key in PROOF_DESTINATIONS:return 'reference/docs/proof/'+PROOF_DESTINATIONS[key],''
        if key in LEGACY:
            target,section=LEGACY[key]
            overrides={
              'window':{'hash':'hash','slots':'hash','slide':'refill','refill':'refill'},
              'match-search':{'budget':'search','lazy':'lazy'},
              'huffman-lengths':{'canonical':'canonical','description':'canonical'},
              'blocks':{'symbols':'records'}, 'bits':{'delivery':'bits'},
              'decode-copy':{'margins':'fast','unrolling':'fast'},
              'state-operations':{'copy':'copy','dictionary':'dictionary','headers':'wrappers'},
            }.get(key,{})
            return destination(target,overrides.get(anchor,section))
    if route.startswith('read/'):
        key=route.split('/')[-1]
        if key=='round-trip':return destination(*OVERVIEW.get(anchor,('foundations','purpose')))
        if key in OLD_BOOK:
            if anchor in {'correctness','composition'}:
                proof={'deflate-matching':'deflate','deflate-output':'trees','inflate-tables':'inftrees','inflate-copy':'inflate','stream-lifetime':'method'}[key]
                return 'reference/docs/proof/'+proof,''
            if key=='inflate-copy' and anchor.startswith(('checksums','adler','crc','checksum-proof')):
                return checksum_destination(anchor)
            table={
              'deflate-matching':('optimizations','costs',{'dispatch':'costs','symbols':'records'}),
              'deflate-output':('optimizations','records',{'frequencies':'records','tree':'huffman','pending':'bits'}),
              'inflate-tables':('optimizations','decode-bits',{'entry':'decode-bits','dispatch':'decode-bits','input':'decode-bits','block-header':'tables','lengths':'tables','errors':'tables'}),
              'inflate-copy':('optimizations','copy',{'dispatch':'copy','literals':'copy','window':'copy','suspension':'buffers','restore':'buffers','wrappers':'wrappers'}),
              'stream-lifetime':('features','stream',{'init':'stream','allocation':'errors','callbacks':'interfaces','gzip':'interfaces','recovery':'errors'}),
            }
            target,section,overrides=table[key]
            section=overrides.get(anchor,anchor or section)
            if key=='deflate-output' and section=='flush':target='features'
            if key=='inflate-copy' and section in {'buffers','wrappers'}:target='features'
            allowed={a for a,_,_ in BY_KEY[target]['anchors']}
            return destination(target,section if section in allowed else table[key][1])
    return route,anchor


def chapter_source(key,lang):
    return (Path(__file__).resolve().parents[1]/'articles'/f'{key}.{lang}.md').read_text()


@lru_cache(maxsize=6)
def chapter_sections(key,lang):
    source=chapter_source(key,lang)
    return [(anchor,title.replace('`','').replace('*',''))
            for title,anchor in re.findall(r'^## (.*?) \{#([^}]+)\}\s*$',source,re.M)]
