"""The detailed book: implementation steps followed by their proof argument."""

def chapter(key,zh,en,desc_zh,desc_en):
    return {'key':key,'title':(zh,en),'description':(desc_zh,desc_en)}

UNITS=[
 {'key':'matching','title':('窗口与匹配','Windows and matching'),'overview':'search',
  'summary':('重复片段的长度与距离从哪里来，以及为什么只需保留近期字节。','Where match lengths and distances come from, and why recent history is enough.'),
  'steps':[
   chapter('window','滑动窗口与哈希链','Sliding windows and hash chains','理解保留哪些旧字节，怎样在有限内存里持续寻找重复。','Understand which earlier bytes to keep and how bounded memory supports continuing match search.'),
   chapter('match-search','匹配搜索与延迟决策','Match search and lazy decisions','从已处理字节中找出可引用的片段，权衡比较次数和匹配长度。','Find reusable passages among processed bytes and balance comparison work against match length.'),
   chapter('match-proof','匹配搜索的证明思路','The matching proof argument','说明搬移位置和提前停止搜索后，引用为什么仍能还原输入。','Explain why references still recover the input after positions move or search stops early.') ]},
 {'key':'huffman','title':('Huffman 编码构造','Huffman construction'),'overview':'huffman-tree',
  'summary':('让常见符号占更少比特，并让解码端重建同一套编码。','Use fewer bits for frequent symbols and reconstruct the same codes at the decoder.'),
  'steps':[
   chapter('huffman-tree','频率、堆与编码树','Frequencies, heaps, and coding trees','让常见符号占更少比特，跟踪频率怎样变成一棵编码树。','Give frequent symbols shorter codes and follow frequencies into a coding tree.'),
   chapter('huffman-lengths','码长修复与规范编码','Length repair and canonical codes','让双方只凭码长重建相同编码，并满足格式的长度限制。','Reconstruct the same codes from lengths while meeting the format’s length limits.'),
   chapter('huffman-proof','编码构造的证明思路','The coding-construction proof','连接实际构造出的树、可区分的编码和最终写出的位。','Connect the constructed tree, distinguishable codes, and the bits actually written.') ]},
 {'key':'output','title':('块与压缩输出','Blocks and compression output'),'overview':'blocks',
  'summary':('把选好的符号写成压缩块，并安全交给调用者。','Write selected symbols into compressed blocks and safely deliver their bytes.'),
  'steps':[
   chapter('blocks','块选择与符号成本','Block selection and symbol costs','比较同一份输入的三种块表示，解释何时值得发送新编码。','Compare three block representations and see when sending new codes is worth its cost.'),
   chapter('bits','位输出与字节缓冲','Bit output and byte buffering','把长短不齐的码字接成字节，再交给调用者。','Pack variable-length codes into bytes and deliver them to the caller.'),
   chapter('storage','共享存储与输出前缀','Shared storage and output prefixes','理解共用一块内存时，怎样保护尚未读取的符号。','Understand how shared memory can preserve symbols that have not yet been read.'),
   chapter('proof','压缩输出的证明思路','The output proof argument','说明从符号到输出的每次写入怎样保留正确含义。','Explain how each write preserves meaning from symbols to delivered output.') ]},
 {'key':'decoding','title':('位输入、解码表与复制','Bit input, decode tables, and copying'),'overview':'lookup',
  'summary':('读取压缩字节、识别符号，并恢复出原来的数据。','Read compressed bytes, identify symbols, and recover the original data.'),
  'steps':[
   chapter('input-bits','位输入与预读','Bit input and lookahead','暂存分批到达的字节，只取走当前字段需要的位。','Buffer arriving bytes and consume only the bits needed for the current field.'),
   chapter('decode-tables','解码表的实际构造','Constructing decode tables','把码长描述变成一张能直接查出符号的表。','Turn code lengths into tables that directly identify symbols.'),
   chapter('decode-copy','快速解码与回引用复制','Fast decoding and back-reference copies','把长度和距离恢复成原文，并理解批量解码怎样加速。','Recover bytes from lengths and distances and understand the decoding fast path.'),
   chapter('decode-proof','解码器的证明思路','The decoder proof argument','把读位、查表和复制连接成同一份解码承诺。','Connect bit reading, table lookup, and copying into one decoding promise.') ]},
 {'key':'streaming','title':('流式状态与封装','Streaming state and wrappers'),'overview':'stream',
  'summary':('理解同一任务为什么需要多次调用，以及暂停后怎样继续。','Understand why one task spans calls and how it resumes after a pause.'),
  'steps':[
   chapter('stream-state','暂停状态与调用接续','Suspension and resumed calls','用小输出缓冲区和分批输入，继续同一个解压任务。','Continue one decoding task across small output buffers and input batches.'),
   chapter('wrappers','封装、字典与完整性检查','Wrappers, dictionaries, and integrity','识别压缩数据的头尾、字典请求和完整性信息。','Interpret headers, trailers, dictionary requests, and integrity information.'),
   chapter('stream-proof','跨调用的证明思路','The cross-call proof argument','说明暂停再继续怎样保留已经完成的工作和正确输出。','Explain how pausing and resuming preserve completed work and correct output.') ]},
 {'key':'lifecycle','title':('状态操作与资源生命周期','State operations and resource lifetime'),'overview':'stream',
  'summary':('开始、复用、复制和结束任务，同时处理分配失败。','Start, reuse, copy, and end tasks while handling allocation failure.'),
  'steps':[
   chapter('state-operations','重置、字典与状态复制','Reset, dictionaries, and state copies','选择何时复用任务、开始新任务或复制当前进度。','Choose when to reuse a task, start another, or copy the current progress.'),
   chapter('allocation','初始化、延迟分配与清理','Initialization, lazy allocation, and cleanup','沿申请与释放步骤理解成功、分配失败和资源复用。','Follow allocation and cleanup through success, failure, and resource reuse.'),
   chapter('ownership-proof','生命周期的证明思路','The lifetime proof argument','说明内存访问和最终清理怎样有可靠的资源归属。','Explain the ownership facts that justify memory access and final cleanup.') ]},
 {'key':'checksums','title':('校验和与分块组合','Checksums and chunk combination'),'overview':'layers',
  'summary':('从 zlib 与 gzip 的尾部检查出发，理解分批更新和独立分块校验值的合并。','Follow zlib and gzip trailer checks into incremental updates and the combination of independent chunk checksums.'),
  'steps':[
   chapter('adler','Adler-32 的递推与分块','Adler-32 recurrence and batching','用两个累加值检查字节序列，再理解分批计算与合并。','Check a byte sequence with two running sums, then understand batching and combination.'),
   chapter('crc','CRC-32 的位运算与查表','CRC-32 bits and table lookup','从一位更新理解 CRC，再看查表怎样减少重复工作。','Understand CRC one bit at a time, then see how tables reduce repeated work.'),
   chapter('checksum-proof','校验和的证明思路','The checksum proof argument','说明快速实现为何算出同一个值，并只读取允许的输入。','Explain why optimized implementations compute the same checksum and read only admitted input.') ]},
 {'key':'interfaces','title':('应用接口与外部交互','Application interfaces and external interaction'),'overview':'layers',
  'summary':('为完整缓冲区、回调和 gzip 文件选择合适的调用方式。','Choose suitable calls for whole buffers, callbacks, and gzip files.'),
  'steps':[
   chapter('buffers','缓冲区接口与库信息','Buffer interfaces and library information','在已有完整输入时，用封装调用完成压缩或解压。','Use a convenience call to compress or decode a complete input buffer.'),
   chapter('callbacks','回调解码与控制反转','Callback decoding and inverted control','把读取和交付交给回调，理解调用顺序与缓冲区责任。','Delegate input and output to callbacks and understand ordering and buffer responsibilities.'),
   chapter('gzip','gzip 文件与缓冲 I/O','Gzip files and buffered I/O','通过文件接口使用 gzip，理解格式识别、成员和逻辑位置。','Use gzip file operations and understand detection, members, and logical positions.'),
   chapter('interfaces-proof','应用接口的证明思路','The application-interface proof','说明封装接口怎样继承引擎保证，并约束外部交互。','Explain how interface wrappers inherit engine guarantees and constrain external interaction.') ]},
]
UNIT_BY_KEY={u['key']:u for u in UNITS}
CHAPTER_BY_KEY={c['key']:c for u in UNITS for c in u['steps']}
UNIT_FOR_CHAPTER={c['key']:u for u in UNITS for c in u['steps']}
