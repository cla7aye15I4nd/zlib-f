"""The detailed book: implementation steps followed by their proof argument."""

def chapter(key,zh,en,desc_zh,desc_en):
    return {'key':key,'title':(zh,en),'description':(desc_zh,desc_en)}

UNITS=[
 {'key':'matching','title':('窗口与匹配','Windows and matching'),'overview':'search',
  'summary':('从输入字节到字面量和匹配，跟踪位置、候选链和延迟决策。','From input bytes to literals and matches: positions, candidate chains, and deferred decisions.'),
  'steps':[
   chapter('window','滑动窗口与哈希链','Sliding windows and hash chains','跟踪补充、滑动、位置重定位和滚动哈希。','Follow refills, sliding, position rebasing, and rolling hashes.'),
   chapter('match-search','匹配搜索与延迟决策','Match search and lazy decisions','展开比较、搜索预算、提前终止与符号提交。','Open byte comparisons, search budgets, early exits, and symbol commitment.'),
   chapter('match-proof','匹配搜索的证明思路','The matching proof argument','连接实际窗口、候选位置与符号展开的含义。','Connect the actual window and candidate positions to symbol expansion.') ]},
 {'key':'huffman','title':('Huffman 编码构造','Huffman construction'),'overview':'huffman-tree',
  'summary':('从频率到树、受限码长与树描述，再连接实际构造的含义。','From frequencies to trees, bounded lengths, and tree descriptions, then the meaning of the actual construction.'),
  'steps':[
   chapter('huffman-tree','频率、堆与编码树','Frequencies, heaps, and coding trees','区分队列结构与编码树，逐步跟踪合并和深度。','Separate queue structure from coding trees; follow merging and depth.'),
   chapter('huffman-lengths','码长修复与规范编码','Length repair and canonical codes','展开长度上限、修复、规范编号与重复码长描述。','Explain length limits, repair, canonical numbering, and repeated-length descriptions.'),
   chapter('huffman-proof','编码构造的证明思路','The coding-construction proof','把频率、树形、码长和实际写入的编码连接起来。','Connect frequencies, tree shape, lengths, and the codes actually written.') ]},
 {'key':'output','title':('块与压缩输出','Blocks and compression output'),'overview':'blocks',
  'summary':('从同一组符号到块、位与字节，理解共享存储和逐前缀预算。','Follow the same symbols into blocks, bits, and bytes; understand shared storage and prefix budgets.'),
  'steps':[
   chapter('blocks','块选择与符号成本','Block selection and symbol costs','比较 stored、fixed 与 dynamic 的完整成本。','Compare the complete costs of stored, fixed, and dynamic blocks.'),
   chapter('bits','位输出与字节缓冲','Bit output and byte buffering','逐字段跟踪 bi_buf、bi_valid 与 pending 字节。','Trace bi_buf, bi_valid, and pending bytes field by field.'),
   chapter('storage','共享存储与输出前缀','Shared storage and output prefixes','跟踪同一次分配中的读游标与写入边界。','Follow read cursors and write boundaries in a single allocation.'),
   chapter('proof','压缩输出的证明思路','The output proof argument','连接符号含义、精确位串、前缀预算和交付。','Connect symbol meaning, exact bitstrings, prefix budgets, and delivery.') ]},
 {'key':'decoding','title':('位输入、解码表与复制','Bit input, decode tables, and copying'),'overview':'lookup',
  'summary':('沿解压方向展开实际建表、快慢路径、历史来源与重叠复制。','Follow decoding through actual table construction, fast and slow paths, history sources, and overlapping copies.'),
  'steps':[
   chapter('input-bits','位输入与预读','Bit input and lookahead','区分取入、查看与消费的位，跟踪 hold 和 bits。','Separate fetched, inspected, and consumed bits in hold and bits.'),
   chapter('decode-tables','解码表的实际构造','Constructing decode tables','跟踪计数、稳定排序、根表、子表与表项含义。','Follow counts, stable sorting, root tables, subtables, and entry meanings.'),
   chapter('decode-copy','快速解码与历史复制','Fast decoding and history copies','展开快路径条件、退出恢复和窗口／当前输出的切换。','Open fast-path guards, exit restoration, and window/current-output transitions.'),
   chapter('decode-proof','解码器的证明思路','The decoder proof argument','把表构造、查表、位前缀和真实复制组合起来。','Compose table construction, lookup, supporting bit prefixes, and actual copies.') ]},
 {'key':'streaming','title':('流式状态与封装','Streaming state and wrappers'),'overview':'stream',
  'summary':('在输入和输出边界暂停，把模式、历史、封装与调用顺序接起来。','Pause at input and output boundaries and connect modes, history, wrappers, and call order.'),
  'steps':[
   chapter('stream-state','暂停状态与调用接续','Suspension and resumed calls','跟踪模式、待完成字段和替换后的调用者缓冲区。','Follow modes, pending fields, and replacement caller buffers.'),
   chapter('wrappers','封装、字典与完整性检查','Wrappers, dictionaries, and integrity','展开 raw、zlib、gzip 的头尾、字典与成员边界。','Open raw, zlib, and gzip headers, trailers, dictionaries, and member boundaries.'),
   chapter('stream-proof','跨调用的证明思路','The cross-call proof argument','组合逻辑历史、缓冲区替换、错误返回与封装关系。','Compose logical history, rebuffering, error returns, and wrapper relations.') ]},
 {'key':'lifecycle','title':('状态操作与资源生命周期','State operations and resource lifetime'),'overview':'stream',
  'summary':('理解 reset、copy、字典和分配，再论证状态建立与精确清理。','Understand reset, copy, dictionaries, and allocation, then establish state and exact cleanup.'),
  'steps':[
   chapter('state-operations','重置、字典与状态复制','Reset, dictionaries, and state copies','区分保留、重建和重定位，逐项跟踪状态影响。','Distinguish retention, rebuilding, and relocation in each state operation.'),
   chapter('allocation','初始化、延迟分配与清理','Initialization, lazy allocation, and cleanup','沿真实分配顺序解释失败路径与资源复用。','Follow actual allocation order, failure paths, and resource reuse.'),
   chapter('ownership-proof','生命周期的证明思路','The lifetime proof argument','从合法调用者存储建立不变量，保持 frame 与所有权。','Establish invariants from valid caller storage and preserve frame and ownership.') ]},
 {'key':'checksums','title':('校验和与组合','Checksums and composition'),'overview':'layers',
  'summary':('展开 Adler 与 CRC 的数学递推、批处理优化和序列合并。','Open Adler and CRC recurrences, batching optimizations, and sequence combination.'),
  'steps':[
   chapter('adler','Adler-32 的递推与分块','Adler-32 recurrence and batching','从两个和的更新走到模运算延迟与合并公式。','From the two running sums to delayed modular reduction and combining.'),
   chapter('crc','CRC-32 的位运算与查表','CRC-32 bits and table lookup','从逐位递推走到字节表、字处理和合并算子。','From bit recurrence to byte tables, word processing, and combine operators.'),
   chapter('checksum-proof','校验和的证明思路','The checksum proof argument','连接整数／多项式模型、机器运算、内存读取和公开定义域。','Connect arithmetic and polynomial models to machine operations, memory reads, and public domains.') ]},
 {'key':'interfaces','title':('应用接口与外部交互','Application interfaces and external interaction'),'overview':'layers',
  'summary':('把缓冲区、回调与 gzip 文件放回同一个引擎和外部世界中。','Place whole buffers, callbacks, and gzip files around the engines and their external world.'),
  'steps':[
   chapter('buffers','缓冲区接口与库信息','Buffer interfaces and library information','展开临时流、长度切片、压缩上界与查询接口。','Open temporary streams, length slicing, compression bounds, and queries.'),
   chapter('callbacks','回调解码与控制反转','Callback decoding and inverted control','跟踪输入补充、窗口交付、返回协议与资源边界。','Follow input refill, window delivery, callback returns, and resource boundaries.'),
   chapter('gzip','gzip 文件与缓冲 I/O','Gzip files and buffered I/O','理解透明读取、成员、逻辑 seek、错误和关闭。','Understand transparent reading, members, logical seek, errors, and close.'),
   chapter('interfaces-proof','应用接口的证明思路','The application-interface proof','连接引擎契约、回调协议、文件模型和外部假设。','Connect engine contracts, callback protocols, file models, and external assumptions.') ]},
]
UNIT_BY_KEY={u['key']:u for u in UNITS}
CHAPTER_BY_KEY={c['key']:c for u in UNITS for c in u['steps']}
UNIT_FOR_CHAPTER={c['key']:u for u in UNITS for c in u['steps']}
