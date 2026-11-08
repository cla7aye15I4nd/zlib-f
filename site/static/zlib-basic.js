import {canonical, ownership} from './zlib-models.mjs';

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
      node.querySelector('small').textContent=T(`${lengths[i]} 位`,`${lengths[i]} bit${lengths[i]===1?'':'s'}`);
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
  const chinese={
    'state 分配失败；没有获得新资源。':'状态块分配失败；没有获得新资源。',
    'state 分配成功，模型开始拥有它。':'状态块分配成功，流开始拥有它。',
    'window 分配失败；state 仍需清理。':'历史窗口分配失败；状态块仍需清理。',
    '失败清理释放 state，返回分配错误。':'失败清理释放状态块，返回分配错误。',
    'state 分配成功。':'状态块分配成功。', 'window 分配成功。':'历史窗口分配成功。',
    '调用 end，释放 window。':'调用结束函数，释放历史窗口。',
    'end 释放 state；生命周期结束。':'结束函数释放状态块；生命周期结束。',
  };
  const text=s=>host.lang==='en'?(english[s]||s):(chinese[s]||s);
  host.controls.innerHTML=`<label>${T('分配结果','Allocation outcome')}<select aria-label="${T('分配失败点','Allocation failure point')}"><option value="2">${T('第二次失败','Second allocation fails')}</option><option value="1">${T('第一次失败','First allocation fails')}</option><option value="0">${T('成功，然后结束释放','Success, then end')}</option></select></label><button type="button" data-next>${T('执行下一步','Next step')}</button><button type="button" data-reset class="zl-quiet">${T('重置','Reset')}</button>`;
  host.view.innerHTML=`<div class="zl-owned"><div class="background"><small>${T('调用前已存在','Pre-existing')}</small><b>${T('其他对象','Other objects')}</b><span>${T('始终保持不变','Unchanged throughout')}</span></div>${['state','window'].map(s=>`<div data-resource="${s}"><small>${T('流的资源','Stream resource')}</small><b>${T(s==='state'?'状态块 state':'历史窗口 window',s)}</b><span></span></div>`).join('')}</div><div class="zl-call-log"></div>`;
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
