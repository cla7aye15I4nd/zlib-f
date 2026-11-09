import {refillSnapshots,refillFacts} from './zlib-refill-model.mjs';

// A spatial view of one slide and one read, not a simulation of engine decisions.
export function mountRefill(host) {
  const T=host.t,states=refillSnapshots(),pct=n=>`${n/1024*100}%`;
  let step=0,animation;
  const labels=[T('尾部空间不足','Too little tail space'),T('搬移保留字节','Move retained bytes'),T('装入新输入','Load new input')];
  host.controls.innerHTML=`<button type="button" data-zrf-back>${T('上一步','Back')}</button><button type="button" data-zrf-next></button><button type="button" data-zrf-reset class="zl-quiet">${T('重置','Reset')}</button>`;
  host.view.innerHTML=`<p class="zrf-intro">${T('换地址会改变输入吗？下一批有 300 字节，尾部却只剩 124 字节。跟踪原输入位置 700–707 的八个示例字节：先搬移保留区，再装入新输入。','Does changing an address change the input? The next batch has 300 bytes, but only 124 tail bytes are free. Track eight sample bytes at original positions 700–707 as the retained region moves and new input arrives.')}</p>
    <ol class="zrf-steps" aria-label="${T('搬移与读取步骤','Slide and read steps')}">${labels.map((label,i)=>`<li data-zrf-step="${i}">${i+1}. ${label}</li>`).join('')}</ol>
    <div class="zrf-map" role="img" aria-label="${T('同一个 1024 字节连续数组：上方是搬移前，下方是当前状态。下方文字给出精确区间。','One continuous 1024-byte array: before above, current state below. Exact intervals follow in text.')}">
      <span class="zrf-track-title">${T('搬移前 · 数组下标','Before · array index')}</span><div class="zrf-track" data-zrf-before></div><div class="zrf-axis"><span>0</span><span>512</span><span>1024</span></div>
      <span class="zrf-track-title is-current" data-zrf-title></span><div class="zrf-track is-current" data-zrf-current></div><div class="zrf-axis is-current"><span>0</span><span>512</span><span>1024</span></div>
      <svg class="zrf-connectors" viewBox="0 0 1024 210" preserveAspectRatio="none" aria-hidden="true"><path data-zrf-arrow></path><polygon data-zrf-tip></polygon></svg>
      <div class="zrf-transfer" aria-hidden="true"></div><div class="zrf-fill" aria-hidden="true"></div>
    </div>
    <p class="zrf-map-caption" data-zrf-caption></p>
    <div class="zrf-legend"><span><i class="zrf-old"></i>${T('保留着，但已太远','Retained, too far')}</span><span><i class="zrf-history"></i>${T('距离允许的旧字节','History within distance')}</span><span><i class="zrf-lookahead"></i>${T('原有待处理输入','Existing unread input')}</span><span><i class="zrf-new-input"></i>${T('新装入的输入','Newly loaded input')}</span><span><i class="zrf-free"></i>${T('可写入区域','Room for input')}</span><span><i class="zrf-start-key"></i>${T('当前处理位置','Processing position')}</span></div>
    <dl class="zrf-counts"><div><dt>${T('处理位置 · 数组下标','Processing · array index')}</dt><dd data-zrf-start></dd></div><div><dt>${T('待处理字节数','Unread bytes')}</dt><dd data-zrf-lookahead></dd></div><div><dt>${T('尾部可写字节数','Free tail bytes')}</dt><dd data-zrf-free></dd></div><div><dt>${T('应用程序剩余输入','Application bytes remaining')}</dt><dd data-zrf-available></dd></div></dl>
    <section class="zrf-byte-card"><h4>${T('追踪八个示例字节 01234567：内容不变，数组下标改变','Track eight sample bytes 01234567: same contents, different array indices')}</h4><div class="zrf-byte-row" data-zrf-bytes></div>
      <dl class="zrf-relations"><div><dt>${T('当前处理的原输入位置','Original-input processing position')}</dt><dd data-zrf-logical></dd></div><div><dt>${T('到所跟踪来源的距离','Distance to the tracked source')}</dt><dd data-zrf-distance></dd></div></dl>
    </section>
    <p class="zrf-note">${T('W=512，容量 2W=1024，搜索距离上限 250，搬移阈值 762。每条色带按真实字节比例绘制；小格只放大八个跟踪字节。距离允许不保证索引会访问该来源。可写入区域也可能仍有旧副本。','W=512, capacity 2W=1024, search-distance limit 250, slide threshold 762. Bands use actual byte proportions; only the eight tracked bytes are enlarged. Distance eligibility does not guarantee an index visit. Room for input can still contain stale copies.')}</p>`;
  const q=selector=>host.view.querySelector(selector),next=host.controls.querySelector('[data-zrf-next]'),back=host.controls.querySelector('[data-zrf-back]');
  const band=(kind,start,end)=>`<i class="zrf-region zrf-${kind}" style="left:${pct(start)};width:${pct(end-start)}"></i>`;
  function track(state) {
    const f=refillFacts(state),oldEnd=f.end-state.loaded;
    return band('old',0,f.historyStart)+band('history',f.historyStart,state.strstart)+band('lookahead',state.strstart,oldEnd)+(state.loaded?band('new-input',oldEnd,f.end):'')+band('free',f.end,1024)+`<i class="zrf-marker is-start" style="left:${pct(state.strstart)}"></i><i class="zrf-marker is-byte" style="left:${pct(f.trackedIndex)}"></i>`+(state.phase===0?'<i class="zrf-copy-range" style="left:50%;width:37.890625%"></i>':'');
  }
  function render(animate=false) {
    animation?.cancel();
    const state=states[step],f=refillFacts(state);
    host.view.querySelectorAll('[data-zrf-step]').forEach((node,i)=>{if(i===step)node.setAttribute('aria-current','step');else node.removeAttribute('aria-current');});
    q('[data-zrf-before]').innerHTML=track(states[0]);q('[data-zrf-current]').innerHTML=track(state);
    q('[data-zrf-title]').textContent=T('当前 · ','Current · ')+labels[step];
    const x=f.trackedIndex;
    q('[data-zrf-arrow]').setAttribute('d',`M700 57 C700 98 ${x} 98 ${x} 133`);
    q('[data-zrf-tip]').setAttribute('points',`${x-5},125 ${x},135 ${x+5},125`);
    q('[data-zrf-caption]').textContent=[T('框内 [512,900) 将整体复制到低地址。黑点追踪原输入位置 700，虚线指向处理位置 800。距离允许的来源范围是 [550,800)。','The outlined [512,900) interval will move to low addresses. The dot tracks original position 700; the dashed line marks processing position 800. Distance permits sources in [550,800).'),T('388 字节从 [512,900) 复制到 [0,388)。处理位置 800→288，来源 700→188；距离允许范围变为 [38,288)，仍是原输入的同一段。','Copy 388 bytes from [512,900) to [0,388). Processing 800→288; source 700→188. The allowed range becomes [38,288), the same original-input interval.'),T('新输入接到 [388,688)，原来 100 字节的预读变为 400 字节。处理位置没有前进，追踪字节也没有再次移动。','Append new input at [388,688). The original 100 unread bytes become 400. Processing has not advanced, and tracked bytes have not moved again.')][step];
    q('[data-zrf-start]').textContent=String(state.strstart);q('[data-zrf-lookahead]').textContent=String(state.lookahead);q('[data-zrf-free]').textContent=String(f.free);q('[data-zrf-available]').textContent=String(state.availableInput);
    q('[data-zrf-bytes]').innerHTML=Array.from({length:8},(_,j)=>`<span><b>${String.fromCharCode(state.bytes[x+j].value)}</b><small>${T('下标','index')} ${x+j}</small></span>`).join('');
    q('[data-zrf-logical]').textContent=`${state.base} + ${state.strstart} = ${f.logicalStart}`;q('[data-zrf-distance]').textContent=`${state.strstart} − ${x} = ${f.distance}`;
    next.textContent=[T('搬移 388 字节','Move 388 bytes'),T('装入 300 字节','Load 300 bytes'),T('本例完成','Example complete')][step];next.disabled=step===2;back.disabled=step===0;
    host.status.textContent=[T('待处理输入不足 262 字节，处理位置已达搬移阈值。先腾出空间，尚未读取新输入。','Unread input is below 262 and processing has reached the slide threshold. Make room before reading new input.'),T('字节已换地址，原输入位置仍为 800，来源距离仍为 100。现在尾部有 636 字节可写。','Addresses changed; the original processing position remains 800 and source distance remains 100. There are now 636 free tail bytes.'),T('实际读入 300 字节，预读量达到 400。补充输入不等于已经把它们选定为输出记录。','Read 300 bytes; lookahead reaches 400. Receiving bytes does not commit them as output records.')][step];
    if(animate&&!globalThis.matchMedia?.('(prefers-reduced-motion: reduce)').matches){
      const overlay=q(step===1?'.zrf-transfer':'.zrf-fill');
      if(overlay.animate)animation=overlay.animate(step===1?[{left:'50%',opacity:.85},{left:'0%',opacity:.85},{left:'0%',opacity:0}]:[{transform:'scaleX(0)',opacity:.85},{transform:'scaleX(1)',opacity:.85},{transform:'scaleX(1)',opacity:0}],{duration:700,easing:'ease-in-out'});
      animation?.finished.catch(()=>{});
    }
  }
  host.on(next,'click',()=>{if(step<2){step++;render(true);}});host.on(back,'click',()=>{if(step>0){step--;render();}});host.on(host.controls.querySelector('[data-zrf-reset]'),'click',()=>{step=0;render();});
  host.abort.signal.addEventListener('abort',()=>animation?.cancel(),{once:true});render();
}
