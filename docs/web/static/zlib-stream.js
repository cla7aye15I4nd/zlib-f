import {streamCall} from './zlib-models.mjs';

export function mountStream(host) {
  const T=host.t;let produced=0,chunks=[],lastStart=0,lastRoom=5;
  host.controls.innerHTML=`<label>${T('下一次提供的输出空间','Output space for the next call')}<select aria-label="${T('下一次提供的输出空间','Output space for the next call')}">${[1,2,3,4,5,6,7,8].map(n=>`<option value="${n}"${n===5?' selected':''}>${T(`${n} 字节`,`${n} bytes`)}</option>`).join('')}</select></label><button type="button" data-call>${T('调用一次，取回一批','Make one call, take one batch')}</button><button type="button" data-reset class="zl-quiet">${T('重置','Reset')}</button>`;
  host.view.innerHTML=`<p class="zl-stream-instructions">${T('已知指令：输出 A → 输出 B → 回退 2 字节，逐字节复制 6 次','Known instructions: emit A → emit B → go back 2 bytes, copy 6 times')}</p><div class="zl-label-row"><span>${T('把各次结果按顺序拼起来','Join the batches in order')}</span><code data-total></code></div><div class="zl-bytes" data-logical>${Array.from({length:8},(_,i)=>`<span class="zl-cell zl-empty"><b>·</b><small>${i}</small></span>`).join('')}</div><p class="zl-stream-note">${T('这八格汇总完整结果，不是本次调用的输出缓冲区。','These eight cells collect the whole result. They are not this call’s output buffer.')}</p><div class="zl-stream-physical"><div><small>${T('本轮开始前，解码器保留的历史','History retained before this call')}</small><div class="zl-stream-history" data-history>∅</div></div><div><small data-buffer-label></small><div class="zl-stream-buffer" data-buffer></div></div></div><div class="zl-registers"><div><small>${T('已执行的调用','Calls made')}</small><b data-calls>0</b></div><div><small>${T('接下来要做的工作','Work to do next')}</small><b data-work></b></div><div><small>${T('复制指令还差几个字节','Copy bytes remaining')}</small><b data-remaining>—</b></div></div><div class="zl-call-log" data-log></div>`;
  const select=host.controls.querySelector('select'),button=host.controls.querySelector('[data-call]');
  const letters=[...host.view.querySelectorAll('[data-logical] .zl-cell')];
  const render=(animate=false)=>{
    host.view.querySelector('[data-total]').textContent=T(`${produced} / 8 字节`,`${produced} / 8 bytes`);
    letters.forEach((node,i)=>{node.classList.toggle('zl-empty',i>=produced);node.querySelector('b').textContent=i<produced?'ABABABAB'[i]:'·';});
    const last=chunks.at(-1)?.bytes||'';
    const buffer=host.view.querySelector('[data-buffer]');
    buffer.style.gridTemplateColumns=`repeat(${lastRoom},1fr)`;
    buffer.replaceChildren(...Array.from({length:lastRoom},(_,i)=>{
      const node=document.createElement('span'),position=lastStart+i;
      node.textContent=last[i]||'·';node.classList.toggle('filled',i<last.length);
      const saved=i<last.length&&position>=2&&position-2<lastStart;
      node.classList.toggle('from-history',saved);
      node.dataset.source=i>=last.length?'empty':saved?'history':position<2?'literal':'current-output';
      if(animate&&i<last.length&&!matchMedia('(prefers-reduced-motion: reduce)').matches)
        node.animate([{opacity:0,transform:'translateY(-8px)'},{opacity:1,transform:'translateY(0)'}],{duration:350,delay:i*70,fill:'backwards'});
      return node;
    }));
    host.view.querySelector('[data-buffer-label]').textContent=chunks.length?T(`第 ${chunks.length} 次的缓冲区：${lastRoom} 格，写入 ${last.length} 字节`,`Call ${chunks.length} buffer: ${lastRoom} positions, ${last.length} bytes written`):T(`准备提供的输出缓冲区：${lastRoom} 格`,`Output buffer ready: ${lastRoom} positions`);
    host.view.querySelector('[data-history]').textContent='ABABABAB'.slice(0,lastStart)||'∅';
    host.view.querySelector('[data-calls]').textContent=chunks.length;
    host.view.querySelector('[data-work]').textContent=produced===8?T('八字节已取回','All eight bytes recovered'):produced===0?T('先输出 A','Emit A first'):produced===1?T('再输出 B','Emit B next'):T('继续复制','Continue copying');
    host.view.querySelector('[data-remaining]').textContent=produced<2?'—':8-produced;
    host.view.querySelector('[data-log]').innerHTML=chunks.map((chunk,i)=>`<div><small>${T(`第 ${i+1} 次`, `CALL ${i+1}`)}</small><code>${chunk.bytes}</code><span>${T(`${chunk.bytes.length} / ${chunk.room} 格已使用`,`${chunk.bytes.length} / ${chunk.room} positions used`)}</span></div>`).join('');
    button.disabled=produced===8;
    host.status.textContent=produced===8?T('把已取回的批次拼接，得到 ABABABAB。真实 C 的完成返回值见下方示例。','Joining the saved batches gives ABABABAB. See the C example for actual completion results.'):
      chunks.length?T('先取走本轮结果，再提供空间继续同一任务。图中省略了压缩比特解析。','Take this batch, then supply space to continue the same task. Compressed-bit parsing is omitted here.'):
      T('点击一次，观察这一批写入多少字节。容量限制本次输出，不改变完整结果。','Make one call and inspect the batch. Capacity limits this call’s output, not the complete result.');
  };
  host.on(button,'click',()=>{lastStart=produced;lastRoom=Number(select.value);const state=streamCall(produced,lastRoom);produced=state.produced;chunks.push({bytes:state.chunk,room:lastRoom});render(true);});
  host.on(select,'change',()=>{if(!chunks.length)lastRoom=Number(select.value);render();});
  host.on(host.controls.querySelector('[data-reset]'),'click',()=>{produced=0;lastStart=0;lastRoom=Number(select.value);chunks=[];render();});
  render();
}
