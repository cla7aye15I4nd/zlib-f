export function mountWindow(host) {
  const T=host.t, text='0123ABCDABCDwxyz', positions=[8,8,12,16];
  const steps=[T('定位输入','Locate the input'),T('查看引用','Inspect the reference'),T('处理匹配','Accept the match'),T('继续输入','Continue the input')];
  let phase=0;
  host.controls.innerHTML=`<button type="button" data-window-next></button><button type="button" data-window-reset class="zl-quiet">${T('重置','Reset')}</button>`;
  host.view.innerHTML=`<ol class="zl-window-steps" aria-label="${T('演示步骤','Demonstration steps')}">${steps.map((s,i)=>`<li data-window-step="${i}"><span>${i+1}</span>${s}</li>`).join('')}</ol>
    <p class="zl-window-intro">${T('完整输入如下。蓝色的两组 ABCD 相同；方框只圈住已处理内容中保留的最近 8 字节。','The complete input is below. The two blue ABCD groups are identical. The frame retains only the last 8 processed bytes.')}</p>
    <div class="zl-window-regions"><span data-window-processed></span><span data-window-unprocessed></span></div>
    <div class="zl-window-track"><div class="zl-window-band" aria-hidden="true"></div>${[...text].map((byte,i)=>`<div class="zl-window-byte"><b>${byte}</b><small>${i}</small></div>`).join('')}<i class="zl-window-cursor" aria-hidden="true"><span data-window-cursor></span></i></div>
    <div class="zl-window-reference"><svg viewBox="0 0 800 65" preserveAspectRatio="none" aria-hidden="true"><path class="zl-window-reference-line" d="M400 5 V25 Q400 48 375 48 H225 Q200 48 200 25 V5"/><path class="zl-window-reference-head" d="M192 15 L200 5 L208 15"/></svg><p data-window-reference></p></div>
    <div class="zl-window-legend"><span>${T('蓝色下划线：引用来源','Blue underline: reference source')}</span><span>${T('蓝色底色：重复片段','Blue fill: repeated passage')}</span><span>${T('竖虚线：当前处理位置','Dashed line: current position')}</span></div>
    <dl class="zl-window-facts"><div><dt>${T('已处理的字节数','Bytes processed')}</dt><dd data-window-position></dd></div><div><dt>${T('保留的最近八字节','Retained last eight bytes')}</dt><dd data-window-history></dd></div><div><dt>${T('接下来处理','Remaining input')}</dt><dd data-window-next-input></dd></div></dl>
    <p class="zl-window-note">${T('下方小数字从 0 开始标记输入位置。8 字节仅用于说明保留范围；真实 zlib 的窗口大小与数组布局见下文。','Small numbers label input positions starting at 0. Eight bytes illustrate the retained range; real zlib window sizes and array layout follow below.')}</p>`;
  const next=host.controls.querySelector('[data-window-next]');
  const cells=[...host.view.querySelectorAll('.zl-window-byte')];
  const render=()=>{
    const position=positions[phase], start=position-8;
    host.view.dataset.windowPhase=phase;
    host.view.querySelectorAll('[data-window-step]').forEach((step,i)=>{
      if(i===phase)step.setAttribute('aria-current','step');else step.removeAttribute('aria-current');
    });
    host.view.querySelector('.zl-window-band').style.left=`${start/16*100}%`;
    host.view.querySelector('.zl-window-cursor').style.left=`calc(${position/16*100}% - 1px)`;
    host.view.querySelector('[data-window-cursor]').textContent=T('当前位置','Current position');
    host.view.querySelector('[data-window-processed]').textContent=T('已处理','Processed');
    host.view.querySelector('[data-window-processed]').style.width=`${position/16*100}%`;
    host.view.querySelector('[data-window-unprocessed]').textContent=phase===3?T('输入结束','End of input'):T('尚未处理','Unprocessed');
    cells.forEach((cell,i)=>{
      cell.classList.toggle('is-retained',i>=start&&i<position);
      cell.classList.toggle('is-discarded',i<start);
      cell.classList.toggle('is-candidate',i>=4&&i<8);
      cell.classList.toggle('is-upcoming',i>=8&&i<12);
    });
    host.view.querySelector('[data-window-reference]').textContent=[
      T('先找到两组 ABCD：第一组在历史中，第二组从当前位置开始。','Locate both ABCD groups: the first is in history; the second starts at the current position.'),
      T('从位置 8 回退到位置 4：距离 = 8 − 4 = 4。重复片段 ABCD：长度 = 4。','Go back from position 8 to position 4: distance = 8 − 4 = 4. The repeated passage ABCD has length 4.'),
      T('已处理第二组 ABCD。保留范围右移 4 格，0123 退出。','The second ABCD is processed. The retained range moves right by 4; 0123 leaves it.'),
      T('再处理 wxyz。范围继续右移，第一组 ABCD 也退出。','Process wxyz. The range moves right again; the first ABCD also leaves it.')
    ][phase];
    host.view.querySelector('[data-window-position]').textContent=position;
    host.view.querySelector('[data-window-history]').textContent=text.slice(start,position);
    host.view.querySelector('[data-window-next-input]').textContent=text.slice(position)||T('输入结束','End of input');
    next.textContent=[T('查看距离与长度','Show distance and length'),T('接受这次匹配','Accept this match'),T('再处理 wxyz','Process wxyz'),T('本例完成','Example complete')][phase];
    next.disabled=phase===3;
    host.status.textContent=[
      T('已处理 0123ABCD，接下来是 ABCDwxyz。处理位置在两组 ABCD 之间，此时还没有前进。','0123ABCD is processed; ABCDwxyz comes next. The current position lies between the two ABCD groups and has not advanced yet.'),
      T('压缩器可以用“距离 4、长度 4”描述接下来的 ABCD。解压器按这条引用复制，就能恢复这四个字节。','The compressor can describe the next ABCD with distance 4, length 4. The decoder follows this reference to recover those four bytes.'),
      T('处理位置从 8 变为 12，保留 ABCDABCD。输入增长了 4 字节，保留容量仍是 8 字节。','The position advances from 8 to 12. Retain ABCDABCD: input grows by 4 bytes while retained capacity stays at 8.'),
      T('处理位置从 12 变为 16，保留 ABCDwxyz。输入处理完毕；后续匹配不能再使用已经退出范围的旧字节。','The position advances from 12 to 16. Retain ABCDwxyz. All input is processed; later matches cannot use bytes outside the retained range.')
    ][phase];
  };
  host.on(next,'click',()=>{if(phase<3){phase++;render();}});
  host.on(host.controls.querySelector('[data-window-reset]'),'click',()=>{phase=0;render();});
  render();
}
