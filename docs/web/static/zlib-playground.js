import {PLAYGROUND_LIMIT,PLAYGROUND_PREVIEW,PLAYGROUND_KINDS,parsePlaygroundInput,playgroundHex} from './zlib-playground-model.mjs';
let nextPlaygroundId=0;

export function mountPlayground(host) {
  const T=host.t,id=`zpg-${++nextPlaygroundId}`;
  let worker=null,generation=0,result=null,step=0,timer=null,source=new Uint8Array();
  const reduced=globalThis.matchMedia?.('(prefers-reduced-motion: reduce)');
  host.controls.hidden=true;
  host.view.innerHTML=`<section class="zpg-root" aria-label="${T('运行真实压缩与解压','Run actual compression and decoding')}">
    <p class="zpg-intro">${T('换一份原文，再让实际 C 程序完成同样的往返。文本先转换为 UTF-8 字节；十六进制可以直接输入任何字节，包括 00、ff 和空序列。程序使用默认 zlib 封装与压缩级别。','Choose another input and let the actual C program make the same round trip. Text becomes UTF-8 bytes; hexadecimal accepts any bytes, including 00, ff, and an empty sequence. The program uses the default zlib wrapper and compression level.')}</p>
    <fieldset class="zpg-modes"><legend>${T('输入表示方式','Input notation')}</legend><label><input type="radio" name="${id}-mode" value="text" checked>${T('文本 → UTF-8','Text → UTF-8')}</label><label><input type="radio" name="${id}-mode" value="hex">${T('十六进制字节','Hexadecimal bytes')}</label></fieldset>
    <label class="zpg-label" for="${id}-input">${T('交给压缩器的原文','Original input for the compressor')}</label><textarea id="${id}-input" class="zpg-input" data-zpg-input spellcheck="false" aria-describedby="${id}-hint">ABABABAB</textarea>
    <p class="zpg-hint" id="${id}-hint" data-zpg-hint></p>
    <div class="zpg-examples" aria-label="${T('填入示例','Fill an example')}"><button type="button" data-zpg-example="eight">ABABABAB</button><button type="button" data-zpg-example="repeat">${T('1024 字节重复片段','1024 repeated bytes')}</button><button type="button" data-zpg-example="binary">00 ff 00 ff 41 00</button><button type="button" data-zpg-example="empty">${T('空输入','Empty input')}</button></div>
    <div class="zpg-actions"><button type="button" data-zpg-run>${T('运行 C 程序','Run the C program')}</button><button type="button" data-zpg-cancel disabled>${T('取消运行','Cancel run')}</button><span data-zpg-state></span></div>
    <div class="zpg-pipeline">${['input','packed','restored'].map((kind,i)=>`<section class="zpg-buffer"><h4>${[T('1 · 原文字节','1 · Original bytes'),T('2 · 压缩字节','2 · Compressed bytes'),T('3 · 恢复字节','3 · Recovered bytes')][i]}</h4><b class="zpg-size" data-zpg-size="${kind}">—</b><pre data-zpg-bytes="${kind}"></pre><small data-zpg-preview="${kind}"></small></section>`).join('')}</div>
    <p class="zpg-check" data-zpg-check></p>
    <section class="zpg-records" data-zpg-records hidden><h4>${T('查看这次实际运行的调用记录','Inspect this run’s actual call records')}</h4><p class="zpg-hint">${T('运行按钮已经执行了全部 C 调用。下面逐条查看保存的返回值和字节账目；切换步骤不会再次压缩，也不表示实现内部逐条寻找匹配。','Run has already executed all C calls. Inspect their recorded results and byte accounts below. Changing steps does not recompress the input or trace internal match searches.')}</p><div class="zpg-log" data-zpg-log></div><div class="zpg-inspector"><code class="zpg-call" data-zpg-call></code><p class="zpg-explain" data-zpg-explain></p><dl class="zpg-counts" data-zpg-counts><div><dt>${T('可读输入余量 avail_in · 字节','Readable input remaining · avail_in · bytes')}</dt><dd data-zpg-in></dd></div><div><dt>${T('可写目标余量 avail_out · 字节','Writable output room · avail_out · bytes')}</dt><dd data-zpg-out></dd></div><div><dt>${T('本次实际取入 · 字节','Actually consumed · bytes')}</dt><dd data-zpg-used></dd></div><div><dt>${T('本次实际写出 · 字节','Actually produced · bytes')}</dt><dd data-zpg-made></dd></div></dl></div><div class="zpg-step-controls"><button type="button" data-zpg-back>${T('上一步','Back')}</button><button type="button" data-zpg-next>${T('下一条记录','Next record')}</button><button type="button" data-zpg-play>${T('播放记录','Play records')}</button><span data-zpg-position></span></div></section>
    <p class="zpg-scope">${T('输入上限为 256 KiB（262144 字节），以保持页面响应。计算在本页的独立 Worker 中完成，输入不会发给服务器。本页将同一份所选 C 源码编译为 WebAssembly 运行。','Input is limited to 256 KiB (262144 bytes) to keep the page responsive. An isolated Worker on this page performs the computation; input is not sent to a server. This page runs the same selected C sources compiled to WebAssembly.')}</p>
  </section>`;
  const q=selector=>host.view.querySelector(selector),input=q('[data-zpg-input]'),run=q('[data-zpg-run]'),cancel=q('[data-zpg-cancel]');
  const mode=()=>q('input[type="radio"]:checked').value;
  const stop=()=>{clearInterval(timer);timer=null;q('[data-zpg-play]').textContent=T('播放记录','Play records');};
  const terminate=()=>{worker?.terminate();worker=null;cancel.disabled=true;};
  const inputError=error=>error.code==='limit'?T('输入超过 262144 字节，请缩短后再运行。','Input exceeds 262144 bytes. Shorten it before running.'):T('十六进制每字节需要两个数位，可用空格或换行分隔，例如 00 ff 41。','Use two hexadecimal digits per byte, optionally separated by spaces or newlines, for example 00 ff 41.');
  function showBuffer(kind,bytes){
    q(`[data-zpg-size="${kind}"]`).textContent=bytes===null?'—':T(`${bytes.length} 字节`,`${bytes.length} bytes`);
    q(`[data-zpg-bytes="${kind}"]`).textContent=bytes===null?T('尚未查看对应调用','Corresponding call not inspected'):bytes.length?playgroundHex(bytes):T('空字节序列','Empty byte sequence');
    q(`[data-zpg-preview="${kind}"]`).textContent=bytes&&bytes.length>PLAYGROUND_PREVIEW?T(`仅预览前 ${PLAYGROUND_PREVIEW} 字节`,`Previewing the first ${PLAYGROUND_PREVIEW} bytes`):'';
  }
  function resetResult(){
    generation++;terminate();stop();result=null;step=0;q('[data-zpg-records]').hidden=true;q('[data-zpg-check]').textContent='';q('[data-zpg-state]').textContent='';showBuffer('packed',null);showBuffer('restored',null);host.status.textContent=T('输入尚未运行。','This input has not been run.');
  }
  function validate(){
    if(mode()==='hex')input.removeAttribute('maxlength');else input.maxLength=PLAYGROUND_LIMIT;
    try{
      source=parsePlaygroundInput(mode(),input.value);run.disabled=false;input.removeAttribute('aria-invalid');q('[data-zpg-hint]').classList.remove('zpg-error');
      q('[data-zpg-hint]').textContent=mode()==='text'?T(`UTF-8 编码后为 ${source.length} 字节；字节数不一定等于字符数。`,`UTF-8 encoding gives ${source.length} bytes; byte count need not equal character count.`):T(`共 ${source.length} 字节。两个十六进制数位表示一字节，可连续书写或用空白分隔。`,`${source.length} bytes. Two hexadecimal digits represent one byte; join pairs directly or separate them with whitespace.`);
      showBuffer('input',source);return true;
    }catch(error){
      source=null;run.disabled=true;input.setAttribute('aria-invalid','true');q('[data-zpg-hint]').classList.add('zpg-error');q('[data-zpg-hint]').textContent=inputError(error);showBuffer('input',null);return false;
    }
  }
  const rcName=rc=>({0:'Z_OK',1:'Z_STREAM_END',[-2]:'Z_STREAM_ERROR',[-3]:'Z_DATA_ERROR',[-4]:'Z_MEM_ERROR',[-5]:'Z_BUF_ERROR'})[rc]??String(rc);
  function recordName(record){return record.kind===7?T('比较字节','Compare bytes'):PLAYGROUND_KINDS[record.kind];}
  function render(){
    if(!result)return;
    const record=result.records[step],kind=record.kind;
    showBuffer('packed',result.records.slice(0,step+1).some(r=>r.kind===2)?new Uint8Array(result.packed):null);
    showBuffer('restored',result.records.slice(0,step+1).some(r=>r.kind===5)?new Uint8Array(result.restored):null);
    q('[data-zpg-check]').textContent=kind===7?(result.equal?T(`全部 ${result.inputLength} 字节与原文相等。`,`All ${result.inputLength} bytes equal the original.`):T('恢复结果与原文不相等。','The recovered bytes differ from the original.')):T('最后比较恢复长度和全部字节；下方数字序列只是预览。','The final check compares the recovered length and every byte; the byte rows are previews.');
    q('[data-zpg-call]').textContent=kind===7?T('恢复长度相等 && 逐字节相等','Equal restored length && equal bytes'):`${recordName(record)}${kind===2?'(…, Z_FINISH)':kind===5?'(…, Z_NO_FLUSH)':'(…)'} → ${rcName(record.result)}`;
    q('[data-zpg-explain]').textContent={
      1:T('先建立压缩状态。此时还没有交出原文，也没有写出压缩字节。','First initialize compressor state. No original input has been supplied and no compressed bytes have been written.'),
      2:T('交出全部原文，并要求完成压缩。目标区按实际 C 的 compressBound 结果分配，足以容纳这次默认配置的输出。前后余量之差，就是本次实际取入和写出的数量。','Supply all original bytes and request completion. The output allocation uses the actual C compressBound result, sufficient for this default-configured run. The differences in remaining input and output room give the actual byte counts.'),
      3:T('释放压缩器内部状态。压缩结果仍由程序保存，接下来交给另一个解码器。','Release the compressor’s private state. The program retains its compressed result for a separate decoder.'),
      4:T('建立独立的解码状态，使用与压缩器对应的默认 zlib 封装。','Initialize independent decoder state with the matching default zlib wrapper.'),
      5:T('让解码器解释真实压缩结果。目标区比原文多一字节，使空输入也有可写空间，并能发现错误地产生了额外字节。前后余量分别记录实际消费与交付。','Decode the actual compressed result. The destination has one byte more than the original, so empty input still has writable room and unexpected extra output can be detected. Input and output differences record actual consumption and delivery.'),
      6:T('释放解码器内部状态。正常完成并不会自动省掉这次释放；恢复字节仍由程序保存。','Release the decoder’s private state. Successful completion still requires this cleanup; the program retains the recovered bytes.'),
      7:T('C 程序检查恢复长度，再比较全部字节，而非只检查可见预览。运行记录与结果已复制回页面，计算使用的缓冲区已经释放。','The C program checks the recovered length and every byte, not just the visible preview. The run records and results have been copied back to the page, and the computation buffers have been released.'),
    }[kind];
    q('[data-zpg-counts]').hidden=kind!==2&&kind!==5;
    q('[data-zpg-in]').textContent=`${record.inputBefore} → ${record.inputAfter}`;q('[data-zpg-out]').textContent=`${record.outputBefore} → ${record.outputAfter}`;q('[data-zpg-used]').textContent=String(record.inputBefore-record.inputAfter);q('[data-zpg-made]').textContent=String(record.outputBefore-record.outputAfter);
    q('[data-zpg-back]').disabled=step===0;q('[data-zpg-next]').disabled=step===result.records.length-1;q('[data-zpg-position]').textContent=`${step+1} / ${result.records.length}`;
    q('[data-zpg-log]').querySelectorAll('button').forEach((button,i)=>{button.setAttribute('aria-pressed',String(i===step));button.dataset.future=String(i>step);});
    host.status.textContent=T(`C 已完成运行；正在查看第 ${step+1} 条真实记录，共 ${result.records.length} 条。`,`C execution has finished; inspecting actual record ${step+1} of ${result.records.length}.`);
    if(step===result.records.length-1)stop();
  }
  function go(value){stop();if(result){step=Math.max(0,Math.min(result.records.length-1,value));render();}}
  function failure(code){
    terminate();run.disabled=false;const message=code==='input'?T('输入超过本例范围。','Input exceeds this example’s range.'):code==='allocation'?T('没有足够内存完成运行。','Not enough memory to complete the run.'):code==='codec'?T('C 调用没有完成往返，请更换输入后重试。','The C calls did not complete the round trip. Try another input.'):T('无法加载本页的 WebAssembly 程序，请重新运行。','Could not load this page’s WebAssembly program. Run again to retry.');q('[data-zpg-state]').textContent=message;host.status.textContent=message;
  }
  function execute(){
    resetResult();if(!validate())return;
    if(typeof globalThis.Worker!=='function'||typeof WebAssembly!=='object'){failure('runtime');return;}
    const current=generation;cancel.disabled=false;q('[data-zpg-state]').textContent=T('正在加载并运行 C…','Loading and running C…');host.status.textContent=q('[data-zpg-state]').textContent;
    try{
      worker=new Worker(new URL('./zlib-playground-worker.js',import.meta.url),{type:'module'});
      host.on(worker,'message',event=>{
        const data=event.data;if(current!==generation||data.id!==current)return;
        if(data.type==='loading')return;
        if(data.type==='error'){failure(data.code);return;}
        if(data.type!=='result'||!Array.isArray(data.records)||data.records.length!==7||!data.released){failure('runtime');return;}
        terminate();result=data;step=0;q('[data-zpg-state]').textContent=T('运行完成','Run complete');q('[data-zpg-records]').hidden=false;
        q('[data-zpg-log]').innerHTML=data.records.map((record,i)=>`<button type="button" data-zpg-record="${i}">${i+1} · ${recordName(record)}</button>`).join('');
        render();
      });
      host.on(worker,'error',()=>{if(current===generation)failure('runtime');});
      const bytes=source.slice();worker.postMessage({id:current,bytes:bytes.buffer},[bytes.buffer]);
    }catch{failure('runtime');}
  }
  host.on(q('[data-zpg-log]'),'click',event=>{const button=event.target.closest('[data-zpg-record]');if(button)go(Number(button.dataset.zpgRecord));});
  host.on(input,'input',()=>{resetResult();validate();});q('.zpg-modes').querySelectorAll('input').forEach(radio=>host.on(radio,'change',()=>{resetResult();validate();}));
  const examples={eight:['text','ABABABAB'],repeat:['text','ABCD'.repeat(256)],binary:['hex','00 ff 00 ff 41 00'],empty:['hex','']};
  q('.zpg-examples').querySelectorAll('button').forEach(button=>host.on(button,'click',()=>{const [choice,value]=examples[button.dataset.zpgExample];q('.zpg-modes').querySelectorAll('input').forEach(radio=>{radio.checked=radio.value===choice;});input.value=value;resetResult();validate();}));
  host.on(run,'click',execute);host.on(cancel,'click',()=>{resetResult();validate();q('[data-zpg-state]').textContent=T('已取消，可重新运行','Canceled; ready to run again');host.status.textContent=q('[data-zpg-state]').textContent;});
  host.on(q('[data-zpg-back]'),'click',()=>go(step-1));host.on(q('[data-zpg-next]'),'click',()=>go(step+1));host.on(q('[data-zpg-play]'),'click',()=>{if(timer){stop();return;}if(!result)return;if(reduced?.matches){go(step===result.records.length-1?0:step+1);return;}if(step===result.records.length-1)step=0;render();q('[data-zpg-play]').textContent=T('暂停','Pause');timer=setInterval(()=>{step++;render();},1800);});
  if(reduced)host.on(reduced,'change',()=>{if(reduced.matches)stop();});host.abort.signal.addEventListener('abort',()=>{generation++;terminate();stop();},{once:true});validate();showBuffer('packed',null);showBuffer('restored',null);
}
