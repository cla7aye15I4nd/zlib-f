import {copyBack} from './zlib-models.mjs';

export function mountCopy(host) {
  let step = 0, animation;
  const T=host.t;
  host.controls.innerHTML = `<label>${T("历史","History")} <select aria-label="${T("回引用示例","Back-reference example")}"><option value="2">${T("AB · 距离 2","AB · distance 2")}</option><option value="1">${T("A · 距离 1","A · distance 1")}</option></select></label><button type="button" data-next>${T("复制一个字节","Copy one byte")}</button><button type="button" data-play>${T("播放","Play")}</button><button type="button" data-reset class="zl-quiet">${T("重置","Reset")}</button><label class="zl-scrub">${T("时间","Time")} <input type="range" aria-label="${T("复制进度","Copy progress")}" min="0" max="6" value="0"></label>`;
  const select = host.controls.querySelector('select'), range = host.controls.querySelector('input');
  const next = host.controls.querySelector('[data-next]');
  host.view.innerHTML = `<div class="zl-label-row"><span>${T("同一段历史，逐字节长出来","The same history, growing byte by byte")}</span><code data-count></code></div><svg class="zl-copy-stage" viewBox="0 0 640 190" role="img" aria-label="${T("源字节沿弧线进入目标位置","A source byte travels into its destination")}"><defs><marker id="zl-copy-arrow" markerWidth="6" markerHeight="6" refX="5" refY="3" orient="auto"><path d="M0 0L6 3L0 6" fill="#9d462e"/></marker></defs><path data-arc class="zl-copy-arc" marker-end="url(#zl-copy-arrow)"/>${Array.from({length:8},(_,i) => `<g data-cell="${i}"><rect x="${14+i*78}" y="70" width="65" height="65" rx="3"/><text class="zl-copy-letter" x="${46.5+i*78}" y="111" text-anchor="middle">·</text><text class="zl-copy-index" x="${46.5+i*78}" y="154" text-anchor="middle">${i}</text></g>`).join('')}<g class="zl-copy-fly" aria-hidden="true"><rect width="46" height="46" rx="3"/><text x="23" y="31" text-anchor="middle">A</text></g><text data-read-label class="zl-copy-cursor" y="179" text-anchor="middle">${T("读","read")}</text><text data-write-label class="zl-copy-cursor" y="52" text-anchor="middle">${T("写","write")}</text></svg><div class="zl-operation" data-operation></div><div class="zl-copy-identity"><span><i></i>${T("匹配前已有的历史","History before the match")}</span><span><i></i>${T("本次匹配生成的历史","History produced by this match")}</span></div>`;
  const groups = [...host.view.querySelectorAll('[data-cell]')];
  const fly = host.view.querySelector('.zl-copy-fly');
  const render = (moving = false) => {
    const distance = Number(select.value), seed = distance === 2 ? 'AB' : 'A';
    const length = 8-distance, output = copyBack(seed, step, distance);
    range.max = String(length); range.value = String(step);
    next.disabled = step === length;
    const source = moving ? step-1 : Math.min(step, length-1), target = source+distance;
    groups.forEach((g,i) => {
      g.classList.toggle('filled', i < output.length);
      g.classList.toggle('generated', i >= distance && i < output.length);
      g.classList.toggle('source', i === source && (step < length || moving));
      g.classList.toggle('target', i === target && (step < length || moving));
      g.querySelector('.zl-copy-letter').textContent = output[i] || '·';
    });
    const x = i => 46.5+78*i;
    const arc = host.view.querySelector('[data-arc]');
    arc.setAttribute('d', `M${x(source)},65 C${x(source)},4 ${x(target)},4 ${x(target)},65`);
    arc.style.opacity = step === length && !moving ? '0' : '1';
    const read = host.view.querySelector('[data-read-label]'), write = host.view.querySelector('[data-write-label]');
    read.setAttribute('x',x(source)); write.setAttribute('x',x(target));
    read.style.opacity = write.style.opacity = step === length && !moving ? '0' : '1';
    host.view.querySelector('[data-count]').textContent = `${output.length} / 8 bytes`;
    host.view.querySelector('[data-operation]').textContent = step < length || moving
      ? T(`下一步：output[${target}] ← output[${source}] = “${output[source]}”`,`Next: output[${target}] ← output[${source}] = “${output[source]}”`)
      : T(`匹配完成：${output}`,`Match complete: ${output}`);
    host.status.textContent = T(`已复制 ${step} / ${length} 个字节。`,`Copied ${step} / ${length} bytes. `) +
      (step === length ? T('长度大于距离，仍然可以完成匹配。','A match can be longer than its distance.') : source >= distance ? T('接下来读取的字节，也来自本次匹配。','The next source byte was produced by this match.') : T('接下来读取匹配开始前已有的字节。','Next, read a byte that existed before the match.'));
    if (moving && !matchMedia('(prefers-reduced-motion: reduce)').matches) {
      animation?.cancel();
      const from = x(step-1)-23, to = x(distance+step-1)-23;
      fly.querySelector('text').textContent = output[distance+step-1];
      animation = fly.animate([
        {transform:`translate(${from}px,79px)`,opacity:1},
        {transform:`translate(${(from+to)/2}px,8px)`,opacity:1,offset:.5},
        {transform:`translate(${to}px,79px)`,opacity:0},
      ], {duration:560,easing:'cubic-bezier(.25,.65,.35,1)'});
      const animatedStep=step;animation.onfinish=()=>{if(step===animatedStep)render();};
    }
    if (step === length) host.stop();
  };
  host.on(next,'click',() => { step++; render(true); });
  host.on(range,'input',() => { host.stop(); animation?.cancel(); step=Number(range.value); render(); });
  host.on(select,'change',() => { host.stop(); animation?.cancel(); step=0; render(); });
  host.on(host.controls.querySelector('[data-reset]'),'click',() => { host.stop(); animation?.cancel(); step=0; render(); });
  host.on(host.controls.querySelector('[data-play]'),'click',() => {
    if (host.timer) {host.stop(); return;}
    if (step === 8-Number(select.value)) step=0;
    host.querySelector('[data-play]').textContent=T('暂停','Pause');
    host.timer=setInterval(() => {step++;render(true);},850);
  });
  host.abort.signal.addEventListener('abort',() => animation?.cancel(),{once:true});
  render();
}
