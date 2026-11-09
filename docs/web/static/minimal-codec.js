import {MINIMAL_LIMIT,MATCH,END,parseMinimalInput,runMinimal,hexBytes} from './minimal-codec-model.mjs';
let nextId=0;
export function mountMinimalCodec(host) {
  const T=host.t,id=`mc-${++nextId}`;
  let result=null,steps=[],step=0,timer=null;
  const reduced=globalThis.matchMedia?.('(prefers-reduced-motion: reduce)');
  const symbol=s=>s===MATCH?'MATCH (256)':s===END?'END (257)':`${s>=32&&s<127?String.fromCharCode(s)+' · ':''}${s}`;
  const escape=s=>String(s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
  const label=s=>escape(symbol(s));
  host.controls.hidden=true;
  host.controls.style.display='none';
  host.view.innerHTML=`<section class="mc-root" aria-label="${T('完整教学压缩器','Complete teaching codec')}">
  <p>${T('这台教学压缩器先把重复片段换成回退复制，再给指令分配前缀码。它发送码表和载荷，接收端只读取发送的字节。这份自定义教学格式不是 DEFLATE 或 zlib。','This teaching compressor replaces repeated runs with backward copies, then assigns prefix codes to instructions. It sends a codebook and a payload; the receiver reads only those bytes. This custom teaching format is not DEFLATE or zlib.')}</p>
  <p class="mc-help">${T('先选文本或十六进制字节，输入原文，再点“编码并从头查看”。“下一步”依次查看匹配、码表、发送字节和接收端每次写入。滑块可直接回看任一步。','Choose text or hexadecimal bytes, enter the original, then select “Encode and inspect from start”. “Next step” follows matches, codebook, sent bytes and each receiver write. The slider revisits any step.')}</p>
  <fieldset class="mc-modes"><legend>${T('原文怎样表示','How the original is written')}</legend><label><input type="radio" name="${id}-mode" value="text" checked>${T('文本 → UTF-8 字节','Text → UTF-8 bytes')}</label><label><input type="radio" name="${id}-mode" value="hex">${T('十六进制字节','Hexadecimal bytes')}</label></fieldset>
  <label for="${id}-input">${T('原文（最多 512 字节）','Original (at most 512 bytes)')}</label><textarea id="${id}-input" data-input spellcheck="false" aria-describedby="${id}-hint">ABABABAB</textarea><p id="${id}-hint" data-hint class="mc-help"></p>
  <div class="mc-actions"><button type="button" data-run>${T('编码并从头查看','Encode and inspect from start')}</button><button type="button" data-example="repeat">${T('运行 ABABABAB','Run ABABABAB')}</button><button type="button" data-example="skew">${T('运行频率不均的例子','Run unequal frequencies')}</button><button type="button" data-example="binary">${T('运行二进制例子','Run binary example')}</button><button type="button" data-example="empty">${T('运行空输入','Run empty input')}</button></div>
  <div data-results><div class="mc-navigation"><button type="button" data-back>${T('上一步','Back')}</button><button type="button" data-next>${T('下一步','Next step')}</button><button type="button" data-play>${T('播放步骤','Play steps')}</button><label>${T('查看任一步','Inspect any step')}<input type="range" min="0" value="0" step="1" data-range></label><span data-position></span></div>
  <ol class="mc-stages">${[T('原文','Original'),T('重复 → 指令','Runs → instructions'),T('频率 → 码表','Counts → codes'),T('发送字节','Send bytes'),T('接收端读表','Receiver reads book'),T('恢复与核对','Recover and compare')].map((name,i)=>`<li data-stage="${i}">${name}</li>`).join('')}</ol>
  <p data-explain class="mc-explain" aria-live="off"></p>
  <section class="mc-section" data-section="0"><h4>${T('1 · 输入字节','1 · Input bytes')}</h4><div data-original class="mc-cells"></div><p data-input-count class="mc-help"></p></section>
  <section class="mc-section" data-section="1"><h4>${T('2 · 从重复片段得到指令','2 · Repeated runs become instructions')}</h4><div data-tokens class="mc-tokens"></div><p class="mc-help">${T('字面量直接输出一个字节。MATCH 后跟距离与长度；逐字节复制允许读取刚写出的字节。END 不输出字节。这里只对这些指令符号计频，距离与长度另写成定长数。','A literal emits one byte. MATCH carries distance and length; copying one byte at a time may read newly written bytes. END emits nothing. Only these instruction symbols are counted; distance and length use fixed-width numbers.')}</p></section>
  <section class="mc-section" data-section="2"><h4>${T('3 · 频率、合并与规范码表','3 · Frequencies, merges and canonical codes')}</h4><p data-merges class="mc-help"></p><div data-tree class="mc-tree-wrap"></div><div class="mc-table-wrap"><table><thead><tr><th>${T('符号编号','Symbol ID')}</th><th>${T('次数','Count')}</th><th>${T('码长','Length')}</th><th>${T('发送的码字','Code bits')}</th></tr></thead><tbody data-book></tbody></table></div><p class="mc-help">${T('每次合并最轻的两棵树，叶子的深度给出码长。相同权重先选最小符号较小的树。再按（码长、符号编号）排列，从全零开始递增；码长增加时在右边补零。这使接收端仅凭码长就能重建码字。','Merge the two lightest trees repeatedly; leaf depth gives code length. Equal weights choose the tree with the smaller minimum symbol first. Sort by (length, symbol ID), start with all zero bits, then increment; append zeros when length increases. The receiver can therefore reconstruct codes from lengths alone.')}</p></section>
  <section class="mc-section" data-section="3"><h4>${T('4 · 真正发送的完整字节串','4 · The complete bytes actually sent')}</h4><div data-header class="mc-header"></div><p class="mc-help">${T('头部与每个表项都按整字节存放，16 位整数高字节在前。表项按符号编号递增；每项是符号编号 16 位 + 码长 8 位。以下载荷按最高位先读，字段不要求对齐字节。','Header and book entries occupy whole bytes; 16-bit integers put the high byte first. Book entries increase by symbol ID: 16-bit symbol plus 8-bit length. Payload below is read most-significant bit first; fields need not align with bytes.')}</p><div data-fields class="mc-fields"></div><p data-cost class="mc-help"></p><pre data-packet></pre><details><summary>${T('查看全部发送字节','Inspect every sent byte')}</summary><pre data-full-packet></pre></details></section>
  <section class="mc-section" data-section="4"><h4>${T('5 · 接收端只拿到字节串','5 · The receiver gets only the packet')}</h4><p data-receiver></p><div data-receiver-book class="mc-receiver-book"></div><p data-current-bits class="mc-current-bits"></p><div data-output class="mc-cells"></div><p data-output-count class="mc-help"></p><p data-comparison class="mc-check"></p></section>
  </div><p class="mc-scope">${T('此页面执行独立的 JavaScript 教学模型。512 字节上限让朴素的逐位置搜索保持响应。它不执行所选 C 源码。字节预览有界，最后的比较覆盖全部输入。','This page executes a separate JavaScript teaching model. The 512-byte cap keeps naive position-by-position search responsive. It does not execute the selected C sources. Byte previews are bounded; the final comparison covers the entire input.')}</p></section>`;
  const q=s=>host.view.querySelector(s),input=q('[data-input]'),mode=()=>q('.mc-modes input:checked').value;
  function stop(){clearInterval(timer);timer=null;q('[data-play]').textContent=T('播放步骤','Play steps');}
  function validate(){
    try{const bytes=parseMinimalInput(mode(),input.value);q('[data-hint]').textContent=T(`输入是 ${bytes.length} 字节。文本按 UTF-8 编码；十六进制每两位是一字节。`,`Input is ${bytes.length} bytes. Text is UTF-8 encoded; each hexadecimal pair is one byte.`);input.removeAttribute('aria-invalid');q('[data-run]').disabled=false;return bytes;}
    catch(error){input.setAttribute('aria-invalid','true');q('[data-run]').disabled=true;q('[data-hint]').textContent=error.message==='limit'?T('输入超过 512 字节，请缩短。','Input exceeds 512 bytes; shorten it.'):T('十六进制需要完整的两位字节，例如 00 ff 41，可用空白分隔。','Use complete two-digit hexadecimal bytes, such as 00 ff 41, optionally separated by whitespace.');return null;}
  }
  function cells(bytes,source=-1,target=-1){
    let indices=Array.from({length:Math.min(48,bytes.length)},(_,i)=>i);
    for(const n of [source,target])if(n>=0&&n<bytes.length&&!indices.includes(n))indices.push(n);
    indices.sort((a,b)=>a-b);
    return indices.map((i,j)=>`${j&&i!==indices[j-1]+1?'<span class="mc-gap">…</span>':''}<span class="mc-byte ${i===source?'mc-source ':''}${i===target?'mc-target':''}"><b>${bytes[i]>=32&&bytes[i]<127?escape(String.fromCharCode(bytes[i])):'·'}</b><code>${bytes[i].toString(16).padStart(2,'0')}</code><small>${i}</small></span>`).join('')||(T('空字节序列','Empty byte sequence'));
  }
  const tokenText=t=>t.symbol===MATCH?T(`MATCH 距离 ${t.distance}，长度 ${t.length}`,`MATCH distance ${t.distance}, length ${t.length}`):symbol(t.symbol);
  function buildSteps(){
    steps=[{stage:0,kind:'input'}];
    result.tokens.forEach((_,token)=>steps.push({stage:1,kind:'token',token}));
    steps.push({stage:2,kind:'counts'},{stage:2,kind:'book'},{stage:3,kind:'wire'},{stage:4,kind:'read-book'});
    result.decoded.events.forEach(event=>steps.push({stage:5,kind:'decode',event}));
    steps.push({stage:5,kind:'compare'});
  }
  function explanation(s){
    if(s.kind==='input')return T(`原文是 ${result.input.length} 个字节。先找重复片段，还没有发送数据。`,`The original has ${result.input.length} bytes. First find repeated runs; nothing has been sent yet.`);
    if(s.kind==='token'){const t=result.tokens[s.token];return t.symbol===MATCH?T(`位置 ${t.start}：最长重复片段长 ${t.length} 字节，来源距离为 ${t.distance}。用一条 MATCH 替换位置 ${t.start}…${t.end-1}。`,`Position ${t.start}: the longest repeated run has ${t.length} bytes at distance ${t.distance}. One MATCH replaces positions ${t.start}…${t.end-1}.`):t.symbol===END?T('原文已读完；追加 END，让接收端能识别最后一条指令。','The original is exhausted; append END so the receiver can recognize the final instruction.'):T(`位置 ${t.start}：没有至少三字节的匹配，输出字面量 ${symbol(t.symbol)}。`,`Position ${t.start}: no match of at least three bytes; emit literal ${symbol(t.symbol)}.`);}
    if(s.kind==='counts')return T(`共 ${result.tokens.length} 条指令，包含 END；统计 ${result.book.length} 种实际出现的符号。重复片段与频率偏斜是两种机会：LZ77 处理前者，Huffman 给更常见的指令更短的码。`,`There are ${result.tokens.length} instructions including END, with ${result.book.length} distinct symbols. Repeated runs and unequal frequencies offer different opportunities: LZ77 handles runs; Huffman gives common instructions shorter codes.`);
    if(s.kind==='book')return T('合并树确定码长，再规范化码字。发送的是符号编号和码长，不是私有的树，也不是原文。','Tree merging determines lengths, then canonicalization determines bits. Send symbol IDs and lengths, rather than a private tree or the original.');
    if(s.kind==='wire')return T(`把头部、码表与载荷接起来，实际发送 ${result.packet.length} 字节。接收端尚未得到任何原文字节。`,`Join header, codebook and payload: actually send ${result.packet.length} bytes. The receiver has no original bytes yet.`);
    if(s.kind==='read-book')return T(`接收端读出原文长度 ${result.decoded.rawLength} 和 ${result.decoded.book.length} 个码长，独立重建规范码表。然后从字节偏移 ${result.decoded.payloadOffset} 开始读载荷。`,`The receiver reads original length ${result.decoded.rawLength} and ${result.decoded.book.length} code lengths, and independently rebuilds canonical codes. Payload starts at byte offset ${result.decoded.payloadOffset}.`);
    if(s.kind==='compare')return T(`END 与 ${result.padding} 个零补位都已验证，输入和恢复结果的全部 ${result.input.length} 个字节逐一相等。`,`END and ${result.padding} zero padding bits have been validated. All ${result.input.length} input and recovered bytes compare equal.`);
    const e=s.event;
    if(e.kind==='literal')return T(`载荷位 [${e.start}, ${e.end}) 解出字面量 ${symbol(e.symbol)}，写到输出位置 ${e.target}。`,`Payload bits [${e.start}, ${e.end}) decode literal ${symbol(e.symbol)}, written at output position ${e.target}.`);
    if(e.kind==='match')return T(`载荷位 [${e.start}, ${e.symbolEnd}) 是 MATCH；随后各读 16 位得到距离 ${e.distance}、长度 ${e.length}。接下来逐字节复制，不再读符号。`,`Payload bits [${e.start}, ${e.symbolEnd}) mean MATCH; the next two 16-bit numbers give distance ${e.distance}, length ${e.length}. Copy bytes next, without reading another symbol.`);
    if(e.kind==='copy')return T(`输出位置 ${e.target} 从位置 ${e.source} 读取 ${hexBytes([e.value])}，距离仍为 ${e.distance}。本次匹配还剩 ${e.remaining} 字节。虚线是来源，实线是新写入。`,`Output position ${e.target} reads ${hexBytes([e.value])} from position ${e.source}, still at distance ${e.distance}. ${e.remaining} bytes remain in this match. Dashed outline marks source; solid outline marks new write.`);
    return T(`载荷位 [${e.start}, ${e.end}) 解出 END。已输出 ${e.outputLength} 字节；接着检查长度、零补位和数据结尾。`,`Payload bits [${e.start}, ${e.end}) decode END. ${e.outputLength} bytes have been emitted; next validate length, zero padding and packet end.`);
  }
  function render(){
    if(!result)return;
    const s=steps[step],e=s.event,complete=s.kind==='compare',outputLength=complete?result.input.length:e?.outputLength||0;
    q('[data-range]').max=steps.length-1;q('[data-range]').value=step;q('[data-position]').textContent=`${step+1} / ${steps.length}`;q('[data-back]').disabled=step===0;q('[data-next]').disabled=step===steps.length-1;
    for(const node of host.view.querySelectorAll('[data-stage]')){const active=+node.dataset.stage===s.stage;node.classList.toggle('mc-active',active);if(active)node.setAttribute('aria-current','step');else node.removeAttribute('aria-current');}
    for(const node of host.view.querySelectorAll('[data-section]')){const active=+node.dataset.section===Math.min(s.stage,4);node.classList.toggle('mc-current',active);node.hidden=!active&&+node.dataset.section!==0;}
    q('[data-explain]').textContent=explanation(s);host.status.textContent=explanation(s);
    const token=s.kind==='token'?result.tokens[s.token]:null;
    q('[data-original]').innerHTML=cells(result.input,token?.symbol===MATCH?token.start-token.distance:-1,token?.start??-1);
    q('[data-input-count]').textContent=T(`${result.input.length} 字节；位置从 0 计数。最多显示前 48 字节及当前来源和目标。`,`${result.input.length} bytes; positions start at 0. Preview shows the first 48 bytes plus the current source and target.`);
    let indices=Array.from({length:Math.min(32,result.tokens.length)},(_,i)=>i);if(s.token>=32)indices.push(s.token);
    q('[data-tokens]').innerHTML=indices.map(i=>`<button type="button" data-token="${i}" class="${i===s.token?'mc-active':''}" aria-pressed="${i===s.token}"><small>${i}</small> ${escape(tokenText(result.tokens[i]))}</button>`).join('')+(result.tokens.length>32?`<small>${T(`显示前 32 条及当前指令；共 ${result.tokens.length} 条。`,`Showing first 32 and current instruction; ${result.tokens.length} total.`)}</small>`:'');
    const activeSymbol=token?.symbol??e?.symbol;
    q('[data-book]').innerHTML=result.book.map(b=>`<tr class="${b.symbol===activeSymbol?'mc-active':''}"><td>${label(b.symbol)}</td><td>${b.frequency}</td><td>${b.length}</td><td><code>${b.bits}</code></td></tr>`).join('');
    const treeNode=node=>`<div class="mc-tree-node"><span>${node.symbol===undefined?T('权重','Weight')+' '+node.weight:label(node.symbol)+' · '+node.weight}</span>${node.left?`<div class="mc-tree-children">${treeNode(node.left)}${treeNode(node.right)}</div>`:''}</div>`;
    q('[data-tree]').innerHTML=result.book.length<=12?`<div class="mc-tree" aria-label="${T('合并得到的树：每向下一层码长增加一位','Merged tree: each level adds one bit to code length')}">${treeNode(result.tree)}</div>`:`<p class="mc-help">${T('超过 12 个叶子，省略树形预览；完整频率和规范码表列在下方。','More than 12 leaves: tree preview omitted; the complete frequencies and canonical codebook appear below.')}</p>`;
    const visibleMerges=result.merges.slice(0,12).map(m=>`${m.leftWeight} + ${m.rightWeight} → ${m.weight}`).join('; ');
    q('[data-merges]').textContent=result.merges.length?T(`从最小权重开始合并：${visibleMerges}${result.merges.length>12?' …':''}。共 ${result.merges.length} 次合并。`,`Merge smallest weights first: ${visibleMerges}${result.merges.length>12?' …':''}. ${result.merges.length} merges total.`):T('只有 END：约定它的码长为 1，码字为 0。','Only END exists: its agreed length is 1 and its code is 0.');
    q('[data-header]').innerHTML=[[T('原文长度 · 16 位','Original length · 16 bits'),hexBytes(result.metadata.slice(0,2))],[T('表项数 · 16 位','Entry count · 16 bits'),hexBytes(result.metadata.slice(2,4))],[T('符号编号 16 位 + 码长 8 位','Symbol 16 bits + length 8 bits'),hexBytes(result.metadata.slice(4,Math.min(28,result.metadata.length)))+(result.book.length>8?' …':'')]].map(([name,bits])=>`<div><small>${name}</small><code>${bits}</code></div>`).join('');
    let fields=result.fields.slice(0,20);if(e)for(const f of result.fields)if(f.start>=e.start&&f.end<=e.end&&!fields.includes(f))fields.push(f);
    q('[data-fields]').innerHTML=fields.map(f=>{const active=e&&f.start>=e.start&&f.end<=e.end;const name=f.kind==='symbol'?symbol(result.tokens[f.token].symbol):f.kind==='distance'?T('距离 16 位','Distance 16 bits'):f.kind==='length'?T('长度 16 位','Length 16 bits'):T('零补位','Zero padding');return `<div class="mc-field ${active?'mc-active':''}"><small>${escape(name)} · [${f.start},${f.end})</small><code>${f.bits}</code></div>`;}).join('')+(fields.length<result.fields.length?`<small>${T('字段预览已截断；当前解码字段仍会显示。','Field preview truncated; current decoding fields are included.')}</small>`:'');
    q('[data-cost]').textContent=T(`头部 4 + 码表 ${result.book.length*3} + 载荷 ${result.payload.length} = ${result.packet.length} 字节。载荷含 ${result.payloadBits} 有效位及 ${result.padding} 个零补位；原文 ${result.input.length} 字节。小输入可能变大。`,`Header 4 + codebook ${result.book.length*3} + payload ${result.payload.length} = ${result.packet.length} bytes. Payload has ${result.payloadBits} meaningful bits and ${result.padding} zero padding bits; original ${result.input.length} bytes. Small inputs may grow.`);
    q('[data-packet]').textContent=hexBytes(result.packet.slice(0,80))+(result.packet.length>80?' …':'');q('[data-full-packet]').textContent=hexBytes(result.packet);
    q('[data-receiver]').textContent=s.stage<4?T('尚未解释发送字节。','Sent bytes have not been interpreted yet.'):T(`接收端根据发送的 ${result.decoded.book.length} 个表项重建码字。输入参数只有完整数据包。`,`The receiver rebuilt codes from ${result.decoded.book.length} transmitted entries. Its only input is the complete packet.`);
    q('[data-receiver-book]').hidden=s.stage!==4;
    q('[data-receiver-book]').innerHTML=result.decoded.book.map(b=>`<span>${label(b.symbol)} → <code>${b.bits}</code></span>`).join('');
    const receivedBits=Array.from(result.packet.slice(result.decoded.payloadOffset),b=>b.toString(2).padStart(8,'0')).join('');
    q('[data-current-bits]').textContent=e?T(`本条指令的载荷位 [${e.start},${e.end})：${receivedBits.slice(e.start,e.end)}${e.kind==='copy'?'（复制时不再消耗这些位）':''}`,`This instruction’s payload bits [${e.start},${e.end}): ${receivedBits.slice(e.start,e.end)}${e.kind==='copy'?' (copying consumes no further bits)':''}`):'';
    q('[data-output]').innerHTML=cells(result.decoded.output.slice(0,outputLength),e?.kind==='copy'?e.source:-1,e?.target??-1);
    q('[data-output-count]').textContent=T(`已写出 ${outputLength} / ${result.input.length} 字节。解码时只使用已经恢复的历史。`,`Emitted ${outputLength} / ${result.input.length} bytes. Decoding uses only already recovered history.`);
    q('[data-comparison]').textContent=complete?T(`✓ 全部 ${result.input.length} 字节相等；数据包格式与结尾也已通过检查。`,`✓ All ${result.input.length} bytes equal; packet structure and ending also validated.`):T('在 END、长度和补位检查后，才进行完整的逐字节比较。','The full byte comparison follows END, length and padding checks.');
    if(complete)stop();
  }
  function go(value){stop();step=Math.max(0,Math.min(steps.length-1,value));render();}
  function execute(){stop();const bytes=validate();if(!bytes)return;result=runMinimal(bytes);buildSteps();step=0;q('[data-results]').hidden=false;render();}
  function changed(){stop();result=null;q('[data-results]').hidden=true;validate();host.status.textContent=T('原文已更改；点编码按钮重新执行。','Original changed; select Encode to run again.');}
  host.on(input,'input',changed);for(const radio of host.view.querySelectorAll('.mc-modes input'))host.on(radio,'change',changed);
  host.on(q('[data-run]'),'click',execute);
  const examples={repeat:['text','ABABABAB'],skew:['text','AA0AA1AA2AA3AA4AA5AA6AA7AA8AA9'],binary:['hex','00 ff 00 ff 00 ff 00 ff'],empty:['hex','']};
  for(const button of host.view.querySelectorAll('[data-example]'))host.on(button,'click',()=>{const [choice,value]=examples[button.dataset.example];for(const radio of host.view.querySelectorAll('.mc-modes input'))radio.checked=radio.value===choice;input.value=value;execute();});
  host.on(q('[data-back]'),'click',()=>go(step-1));host.on(q('[data-next]'),'click',()=>go(step+1));host.on(q('[data-range]'),'input',()=>go(Number(q('[data-range]').value)));
  host.on(q('[data-tokens]'),'click',event=>{const button=event.target.closest('[data-token]');if(button)go(Number(button.dataset.token)+1);});
  host.on(q('[data-play]'),'click',()=>{if(timer){stop();return;}if(reduced?.matches){go(step===steps.length-1?0:step+1);return;}if(step===steps.length-1)step=0;render();q('[data-play]').textContent=T('暂停','Pause');timer=setInterval(()=>{step++;render();},1800);});
  if(reduced)host.on(reduced,'change',()=>{if(reduced.matches)stop();});host.abort.signal.addEventListener('abort',stop,{once:true});execute();
}
