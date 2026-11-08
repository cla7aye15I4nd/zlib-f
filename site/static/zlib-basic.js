import {canonical, streamCall, ownership} from './zlib-models.mjs';

const tree = entries => {
  const nodes = new Map([['',{x:300,y:22}]]), edges=[];
  const leaves=new Map(entries.filter(e=>e.length).map(e=>[e.code,e.symbol]));
  for(const entry of entries.filter(e=>e.length)) for(let d=1;d<=entry.length;d++) {
    const key=entry.code.slice(0,d); if(nodes.has(key)) continue;
    const parent=nodes.get(key.slice(0,-1));
    const point={x:(parseInt(key,2)+.5)*600/(2**d),y:22+43*d}; nodes.set(key,point);
    edges.push(`<path d="M${parent.x},${parent.y}L${point.x},${point.y}"/><text x="${(parent.x+point.x)/2+8}" y="${(parent.y+point.y)/2-4}">${key.at(-1)}</text>`);
  }
  return `<svg class="zl-tree" viewBox="0 0 600 ${48+43*Math.max(1,...entries.map(e=>e.length))}" aria-hidden="true">${edges.join('')}${[...nodes].map(([key,p])=>`<circle cx="${p.x}" cy="${p.y}" r="${leaves.has(key)?15:4}" class="${leaves.has(key)?'leaf':''}"/>${leaves.has(key)?`<text x="${p.x}" y="${p.y+5}" text-anchor="middle" class="leaf-label">${leaves.get(key)}</text>`:''}`).join('')}</svg>`;
};

export function mountHuffman(host) {
  const T=host.t;
  host.controls.innerHTML=['A','B','C','D'].map((s,i)=>`<label>${s}<select aria-label="${T(s+' 的码长','Code length for '+s)}">${[0,1,2,3,4].map(n=>`<option value="${n}"${n===[1,2,3,3][i]?' selected':''}>${n}</option>`).join('')}</select></label>`).join('')+`<button type="button" data-conflict>${T('把 B 缩短一位','Shorten B by one bit')}</button><button type="button" data-reset class="zl-quiet">${T('恢复示例','Reset')}</button>`;
  host.view.innerHTML=`<div class="zl-label-row"><span>${T('一单位编码空间','One unit of code space')}</span><code data-kraft></code></div><div class="zl-space"><div class="zl-space-segments">${['A','B','C','D'].map(s=>`<div class="zl-space-${s}" data-segment><b>${s}</b><small></small></div>`).join('')}</div><div class="zl-space-limit"><span>1</span></div></div><div class="zl-space-caption"></div><div data-tree></div><div class="zl-code-list">${['A','B','C','D'].map(s=>`<div><span>${s}</span><b>—</b><small></small></div>`).join('')}</div>`;
  const selects=[...host.controls.querySelectorAll('select')],segments=[...host.view.querySelectorAll('[data-segment]')];
  const output=[...host.view.querySelectorAll('.zl-code-list > div')];
  const render=()=>{
    const lengths=selects.map(s=>Number(s.value)),result=canonical(lengths);
    host.view.querySelector('[data-kraft]').textContent=`K = ${result.kraft}`;
    segments.forEach((segment,i)=>{
      const fraction=lengths[i]?2**-lengths[i]:0;
      segment.style.width=`${fraction*80}%`;
      segment.querySelector('small').textContent=fraction?'1/'+2**lengths[i]:'';
      segment.classList.toggle('unused',!fraction);
    });
    host.classList.toggle('zl-error',!result.valid);
    host.view.querySelector('.zl-space-caption').textContent=!result.valid
      ?T('超过边界的空间没有对应叶子；不能分配新的前缀码。','The excess has no available leaves: this assignment cannot form a prefix code.')
      :T('短码占据更多空间。码长 0 表示未使用。','Short codes occupy more space. Length 0 means unused.');
    const treeNode=host.view.querySelector('[data-tree]');
    if(result.valid) {treeNode.innerHTML=tree(result.entries);treeNode.classList.remove('zl-old-tree');}
    else treeNode.classList.add('zl-old-tree');
    output.forEach((node,i)=>{
      node.querySelector('b').textContent=result.valid?(result.entries[i].code||'—'):'—';
      node.querySelector('small').textContent=`${lengths[i]} bit`;
    });
    host.status.textContent=!result.valid?T('K > 1：码长发生冲突。淡化的树保留上一个可分配状态。','K > 1: oversubscribed. The faded tree preserves the last valid assignment.'):
      result.complete?T('K = 1：完整前缀码。试着把 B 从 2 改成 1。','K = 1: a complete prefix code. Try changing B from 2 to 1.'):
      T('K < 1：仍有空缺。数学上可分配不等于真实块会被接受。','K < 1: some space remains. A mathematical assignment is not necessarily an accepted DEFLATE table.');
  };
  selects.forEach(s=>host.on(s,'change',render));
  host.on(host.controls.querySelector('[data-conflict]'),'click',()=>{selects[1].value='1';render();});
  host.on(host.controls.querySelector('[data-reset]'),'click',()=>{selects.forEach((s,i)=>s.value=[1,2,3,3][i]);render();});
  render();
}

export function mountStream(host) {
  const T=host.t;let produced=0,chunks=[],lastStart=0;
  host.controls.innerHTML=`<label>${T('每次输出空间','Output room per call')}<select aria-label="${T('每次输出空间','Output room per call')}">${[1,2,3,4,5,6,7,8].map(n=>`<option value="${n}"${n===5?' selected':''}>${n} bytes</option>`).join('')}</select></label><button type="button" data-call>${T('执行下一次调用','Run next call')}</button><button type="button" data-reset class="zl-quiet">${T('重置','Reset')}</button>`;
  host.view.innerHTML=`<div class="zl-label-row"><span>${T('逻辑输出 · 保持连续','Logical output · one continuous history')}</span><code data-total></code></div><div class="zl-bytes" data-logical>${Array.from({length:8},(_,i)=>`<span class="zl-cell zl-empty"><b>·</b><small>${i}</small></span>`).join('')}</div><div class="zl-stream-physical"><div><small>${T('本次调用之前保存的历史','History saved before this call')}</small><div class="zl-stream-history" data-history>∅</div></div><div><small>${T('本次新提供的输出缓冲区','Fresh output buffer for this call')}</small><div class="zl-stream-buffer" data-buffer>${Array.from({length:8},()=>'<span>·</span>').join('')}</div></div></div><div class="zl-registers"><div><small>${T('暂停状态','Mode at return')}</small><b data-mode>LIT</b></div><div><small>${T('匹配剩余长度','Match remaining')}</small><b data-remaining>6</b></div><div><small>${T('匹配距离','Match distance')}</small><b>2</b></div></div><div class="zl-call-log" data-log></div>`;
  const select=host.controls.querySelector('select'),button=host.controls.querySelector('[data-call]');
  const letters=[...host.view.querySelectorAll('[data-logical] .zl-cell')],buffer=[...host.view.querySelectorAll('[data-buffer] span')];
  const render=(animate=false)=>{
    host.view.querySelector('[data-total]').textContent=`${produced} / 8 bytes`;
    letters.forEach((node,i)=>{node.classList.toggle('zl-empty',i>=produced);node.querySelector('b').textContent=i<produced?'ABABABAB'[i]:'·';});
    const last=chunks.at(-1)||'';
    buffer.forEach((node,i)=>{
      node.textContent=last[i]||'·';node.classList.toggle('filled',i<last.length);
      node.classList.toggle('from-history',lastStart>=2&&i<Math.min(2,last.length));
      if(animate&&i<last.length&&!matchMedia('(prefers-reduced-motion: reduce)').matches)
        node.animate([{opacity:0,transform:'translateY(-8px)'},{opacity:1,transform:'translateY(0)'}],{duration:350,delay:i*70,fill:'backwards'});
    });
    host.view.querySelector('[data-history]').textContent='ABABABAB'.slice(0,lastStart)||'∅';
    host.view.querySelector('[data-mode]').textContent=produced===8?'PAYLOAD_DONE':produced<2?'LIT':'MATCH';
    host.view.querySelector('[data-remaining]').textContent=produced<2?6:8-produced;
    host.view.querySelector('[data-log]').innerHTML=chunks.map((chunk,i)=>`<div><small>CALL ${i+1}</small><code>${chunk}</code></div>`).join('');
    button.disabled=produced===8;
    host.status.textContent=produced===8?T('载荷完成。真实解码还需块结束码和适用的封装尾部。','Payload complete. Real decoding still needs the end-of-block code and any wrapper trailer.'):
      chunks.length>1?T('新缓冲区先从保存的历史读取，随后可读本次新输出。','The new buffer first reads saved history, then can read newly produced output.'):
      chunks.length?T('输出空间耗尽；剩余匹配保存在状态里。','Output room exhausted; the unfinished match remains in state.'):
      T('教学符号流，不模拟真实 inflate 的返回码。','A teaching token stream, not a simulation of real inflate return codes.');
  };
  host.on(button,'click',()=>{lastStart=produced;const state=streamCall(produced,Number(select.value));produced=state.produced;chunks.push(state.chunk);render(true);});
  host.on(host.controls.querySelector('[data-reset]'),'click',()=>{produced=0;lastStart=0;chunks=[];render();});
  render();
}

export function mountOwnership(host) {
  const T=host.t;let step=0;const seen=new Set();
  const english={
    '还没有开始分配。背景中的其他对象始终保持不变。':'No allocation yet. Pre-existing objects remain unchanged.',
    'state 分配失败；没有获得新资源。':'state allocation failed; no new resource was acquired.',
    'state 分配成功，模型开始拥有它。':'state allocated; the stream now owns it.',
    'window 分配失败；state 仍需清理。':'window allocation failed; state still needs cleanup.',
    '失败清理释放 state，返回分配错误。':'Failure cleanup frees state before returning an allocation error.',
    'state 分配成功。':'state allocated.', 'window 分配成功。':'window allocated.',
    '初始化成功；两项资源继续归流所有。':'Initialization succeeds; both resources remain owned by the stream.',
    '调用 end，释放 window。':'end frees window.', 'end 释放 state；生命周期结束。':'end frees state; the lifetime is complete.',
  };
  const text=s=>host.lang==='en'?(english[s]||s):s;
  host.controls.innerHTML=`<label>${T('分配结果','Allocation outcome')}<select aria-label="${T('分配失败点','Allocation failure point')}"><option value="2">${T('第二次失败','Second allocation fails')}</option><option value="1">${T('第一次失败','First allocation fails')}</option><option value="0">${T('成功，然后 end','Success, then end')}</option></select></label><button type="button" data-next>${T('执行下一步','Next step')}</button><button type="button" data-reset class="zl-quiet">${T('重置','Reset')}</button>`;
  host.view.innerHTML=`<div class="zl-owned"><div class="background"><small>${T('调用前已存在','Pre-existing')}</small><b>${T('其他对象','Other objects')}</b><span>${T('始终保持不变','Unchanged throughout')}</span></div>${['state','window'].map(s=>`<div data-resource="${s}"><small>${T('流的资源','Stream resource')}</small><b>${s}</b><span></span></div>`).join('')}</div><div class="zl-call-log"></div>`;
  const select=host.controls.querySelector('select'),button=host.controls.querySelector('[data-next]');
  const render=()=>{
    const state=ownership(Number(select.value),step);
    for(const name of state.live) seen.add(name);
    for(const name of ['state','window']) {
      const node=host.view.querySelector(`[data-resource="${name}"]`),live=state.live.includes(name);
      node.classList.toggle('live',live);node.classList.toggle('released',!live&&seen.has(name));
      node.querySelector('span').textContent=live?T('已分配 · 流拥有','Allocated · stream-owned'):seen.has(name)?T('已释放','Freed'):T('尚未分配','Not allocated');
    }
    host.view.querySelector('.zl-call-log').innerHTML=state.history.map((s,i)=>`<div><small>${i+1}</small><span>${text(s)}</span></div>`).join('');
    button.disabled=state.index===state.total;
    host.status.textContent=text(state.text);
  };
  const reset=()=>{step=0;seen.clear();render();};
  host.on(select,'change',reset);host.on(button,'click',()=>{step++;render();});host.on(host.controls.querySelector('[data-reset]'),'click',reset);render();
}
