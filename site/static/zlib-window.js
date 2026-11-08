export function mountWindow(host) {
  const T=host.t, text='0123ABCDABCDwxyz', positions=[8,12,16];
  let phase=0;
  host.controls.innerHTML=`<button type="button" data-window-next></button><button type="button" data-window-reset class="zl-quiet">${T('重置','Reset')}</button>`;
  host.view.innerHTML=`<p class="zl-window-intro">${T('示意：只保留已处理内容的最近 8 字节','Illustration: retain the last 8 processed bytes')}</p><div class="zl-window-track"><div class="zl-window-band" aria-hidden="true"></div>${[...text].map((byte,i)=>`<div class="zl-window-byte"><b>${byte}</b><small>${i}</small></div>`).join('')}<i class="zl-window-cursor" aria-hidden="true"></i></div><div class="zl-window-legend"><span>${T('框内：保留的历史','Inside the frame: retained history')}</span><span>${T('右侧：尚未处理的输入','To the right: unprocessed input')}</span></div><dl class="zl-window-facts"><div><dt>${T('已处理的字节数','Bytes processed')}</dt><dd data-window-position></dd></div><div><dt>${T('保留的最近八字节','Retained last eight bytes')}</dt><dd data-window-history></dd></div><div><dt>${T('接下来处理','Remaining input')}</dt><dd data-window-next-input></dd></div></dl><p class="zl-window-note">${T('这里的位置属于整条输入流。8 字节仅用于图示；真实 zlib 使用更大的窗口和不同的物理数组布局。','Positions belong to the whole input stream. Eight bytes are only for illustration; real zlib uses a larger window and a different physical array layout.')}</p>`;
  const next=host.controls.querySelector('[data-window-next]');
  const cells=[...host.view.querySelectorAll('.zl-window-byte')];
  const render=()=>{
    const position=positions[phase], start=position-8;
    host.view.querySelector('.zl-window-band').style.left=`${start/16*100}%`;
    host.view.querySelector('.zl-window-cursor').style.left=`calc(${position/16*100}% - 1px)`;
    cells.forEach((cell,i)=>{
      cell.classList.toggle('is-retained',i>=start&&i<position);
      cell.classList.toggle('is-discarded',i<start);
      cell.classList.toggle('is-candidate',phase===0&&i>=4&&i<8);
      cell.classList.toggle('is-upcoming',phase===0&&i>=8&&i<12);
    });
    host.view.querySelector('[data-window-position]').textContent=position;
    host.view.querySelector('[data-window-history]').textContent=text.slice(start,position);
    host.view.querySelector('[data-window-next-input]').textContent=text.slice(position)||T('输入结束','End of input');
    next.textContent=phase===0?T('接受 ABCD 匹配','Accept the ABCD match'):phase===1?T('再处理 wxyz','Process wxyz'):T('本例完成','Example complete');
    next.disabled=phase===2;
    host.status.textContent=[
      T('当前位置是 8。历史中位置 4 的 ABCD 可以替代接下来的 ABCD：距离 4，长度 4。','At position 8, ABCD at position 4 can represent the next ABCD: distance 4, length 4.'),
      T('匹配接受了四字节输入。保留范围前移四格，0123 离开窗口；保留内存仍只有八字节。','The match accepts four input bytes. The range moves four positions; 0123 leaves it. Retained storage is still eight bytes.'),
      T('再处理四个字面量 wxyz。现在保留 ABCDwxyz，更早的 ABCD 也离开范围。','Process the four literals wxyz. Retain ABCDwxyz; the older ABCD also leaves the range.')
    ][phase];
  };
  host.on(next,'click',()=>{phase++;render();});
  host.on(host.controls.querySelector('[data-window-reset]'),'click',()=>{phase=0;render();});
  render();
}
