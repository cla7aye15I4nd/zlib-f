import {fastAdmission, FIELD_BOUNDS, orderedMatch} from './zlib-fastpath-scene.mjs';

export function mountFastpath(host) {
  const T = host.t;
  host.classList.add('zlfp-scene');
  host.controls.innerHTML = `
    <label>${T('未读输入字节 have', 'Unread input bytes · have')}<select data-fp-input aria-label="${T('未读输入字节数', 'Unread input byte count')}"><option>5</option><option selected>6</option><option>12</option></select></label>
    <label>${T('可写输出位置 left', 'Writable output slots · left')}<select data-fp-output aria-label="${T('可写输出位置数', 'Writable output slot count')}"><option>257</option><option selected>258</option><option>512</option></select></label>
    <label>${T('已保存未消费位 bits', 'Held, unconsumed bits · bits')}<select data-fp-held aria-label="${T('已保存未消费位数', 'Held unconsumed bit count')}"><option selected>0</option><option>1</option><option>7</option><option>8</option></select></label>
    <button type="button" data-fp-step>${T('查看下一项依据', 'Inspect next reason')}</button>
    <button type="button" data-play>${T('播放', 'Play')}</button>
    <button type="button" class="zl-quiet" data-fp-reset>${T('重置', 'Reset')}</button>`;
  host.view.innerHTML = `
    <p class="zlfp-purpose">${T('准备读取下一条指令时，先判断现有空间是否足以覆盖任何一条长度／距离指令。改变容量，观察 C 选择的分支；下方再逐项展开这些余量的用途。', 'Before reading the next instruction, test whether available space covers any one length/distance instruction. Change capacities to inspect the C branch, then inspect why each margin exists.')}</p>
    <div class="zlfp-guard"><code>have &gt;= 6 &amp;&amp; left &gt;= 258 &amp;&amp; bits &lt; 8</code><div data-fp-tests></div><strong data-fp-route aria-live="polite"></strong></div>
    <div class="zlfp-margins">
      <section><h4>${T('输入余量：六个字节位置', 'Input margin: six byte positions')}</h4><ol class="zlfp-cells" data-fp-input-cells></ol><p data-fp-input-note></p></section>
      <section><h4>${T('输出余量：最长匹配的末四格', 'Output margin: last four slots of a maximum match')}</h4><div class="zlfp-output-end"><span>0 … 253</span><ol class="zlfp-cells" data-fp-output-cells></ol></div><p data-fp-output-note></p></section>
    </div>
    <section class="zlfp-budget" data-fp-budget><h4>${T('一条长度／距离指令的字段上界', 'Field bounds for one length/distance instruction')}</h4><div class="zlfp-fields" data-fp-fields></div><p>${T('15 + 5 + 15 + 13 = 48 位。这四项是通用上界，不是某条指令的实际读取记录；补位后留下的位会用于后续字段。', '15 + 5 + 15 + 13 = 48 bits. These are general bounds, not an actual instruction trace. Bits left by a refill are reused for later fields.')}</p></section>
    <div class="zlfp-reason" data-fp-reason></div>
    <section class="zlfp-equivalence"><h4>${T('分组仍须保留逐字节依赖', 'Grouping must preserve byte dependencies')}</h4><p>${T('独立的小例子：已有 AB，长度六、距离二。两行按同一条合法指令比较复制规则，不使用上面的字段上界虚构压缩位。', 'Separate small example: seed AB, length six, distance two. The two rows compare copy rules for that same valid instruction; the field bounds above do not invent compressed bits for it.')}</p><div><span>${T('逐字节规则', 'Byte recurrence')}</span><code data-fp-reference></code></div><div><span>${T('每组三次有序赋值', 'Three ordered stores per group')}</span><code data-fp-grouped></code></div><p class="zlfp-premises">${T('数值守卫只提供容量余量。两条路径还需要相同的正确码表、可用来源历史与可写目标；通过守卫不代表输入有效。普通路径在补位点和复制批次前检查容量，快速路径把整条指令的容量检查移到入口。', 'The numeric guard provides capacity margins only. Both routes still need correct tables, available source history and writable destination memory; passing does not validate the input. The ordinary route checks at input refills and before copy batches; the fast route moves whole-instruction capacity checks to entry.')}</p></section>`;
  const q = selector => host.view.querySelector(selector);
  const input = host.controls.querySelector('[data-fp-input]');
  const output = host.controls.querySelector('[data-fp-output]');
  const held = host.controls.querySelector('[data-fp-held]');
  const play = host.controls.querySelector('[data-play]');
  const names = [T('长度码', 'Length code'), T('长度额外位', 'Length extra bits'), T('距离码', 'Distance code'), T('距离额外位', 'Distance extra bits')];
  const reasons = [
    T('长度码最多占 15 位。查表可以分两级完成；上界约束的是整个码字，并非每级各读 15 位。', 'A length code occupies at most 15 bits. A lookup may use two table levels; the bound covers the whole code, not 15 bits for each level.'),
    T('长度额外位最多 5 位，用来在长度基值上增加偏移。较早补入但未消费的位，仍可用于这个字段。', 'Length extra bits use at most 5 bits to extend the base length. Unconsumed bits from earlier refills remain available to this field.'),
    T('距离码最多占 15 位，先选择距离基值。输入余量不能替代码表含义与表访问边界。', 'A distance code occupies at most 15 bits and selects a distance base. Input capacity cannot replace table meanings or readable table bounds.'),
    T('距离额外位最多 13 位。四个字段合计最多 48 位；实际补位的六字节界还要追踪各处共享的位余额，而不是把各处最大读取量独立相加。', 'Distance extra bits use at most 13 bits. The four bounds total 48 bits; the six-byte refill bound also tracks shared residual bits, rather than adding independent maximum pulls at each site.'),
    T('任意匹配最多产生 258 字节。因此，即使本例只复制六字节，入口仍要求 258 个位置。只有 257 格时走普通路径，并不是数据错误。', 'Any match produces at most 258 bytes. Entry therefore requires 258 slots even though the small example copies only six. With 257 slots the ordinary route continues; that is not a data error.'),
    T('入口保存位必须少于 8 位。这不是另一个输出界，而是退出时退回完整多读字节的条件：这样退回的完整字节都来自本次辅助函数读取。', 'Entry must hold fewer than 8 bits. This is an exit-normalization condition: every whole unused byte returned to input was then fetched within this helper.'),
  ];
  let reason = 0;
  const stop = () => { clearInterval(host.timer); host.timer = null; play.textContent = T('播放', 'Play'); };
  function render() {
    const have = Number(input.value), left = Number(output.value), bits = Number(held.value);
    const admission = fastAdmission(have, left, bits);
    host.dataset.fastpath = admission.fast ? 'fast' : 'ordinary';
    q('[data-fp-tests]').innerHTML = [
      `${have} ≥ 6`, `${left} ≥ 258`, `${bits} < 8`,
    ].map((text, i) => `<span class="${admission.tests[i] ? 'zlfp-pass' : 'zlfp-missing'}">${text} · ${admission.tests[i] ? T('满足', 'met') : T('不满足', 'unmet')}</span>`).join('');
    q('[data-fp-route]').textContent = admission.fast ? T('进入快速辅助函数', 'Enter the fast helper') : T('继续普通路径', 'Continue on the ordinary route');
    q('[data-fp-input-cells]').innerHTML = Array.from({length: 6}, (_, i) => `<li class="${i < have ? 'zlfp-present' : 'zlfp-absent'}"><small>${i}</small><b>${i < have ? T('可读', 'read') : T('缺少', 'missing')}</b></li>`).join('');
    q('[data-fp-output-cells]').innerHTML = Array.from({length: 4}, (_, j) => { const i = j + 254; return `<li class="${i < left ? 'zlfp-present' : 'zlfp-absent'}"><small>${i}</small><b>${i < left ? '·' : '×'}</b></li>`; }).join('');
    q('[data-fp-input-note]').textContent = T('编号为 0 到 5。更多输入仍可用，图中只显示入口要求的六格。', 'Indices 0 through 5. Additional input remains available; only the six required positions are shown.');
    q('[data-fp-output-note]').textContent = T('编号为 0 到 257。第 257 格存在，才足以容纳 258 字节；这里没有执行写入。', 'Indices 0 through 257. Slot 257 is needed for 258 bytes; no writes are executed here.');
    q('[data-fp-fields]').innerHTML = FIELD_BOUNDS.map((field, i) => `<div style="--zlfp-width:${field.bits}" class="${reason === i ? 'zlfp-active' : ''}"><span>${names[i]}</span><b>≤ ${field.bits} ${T('位', 'bits')}</b></div>`).join('');
    q('[data-fp-reason]').textContent = reasons[reason];
    q('[data-fp-budget]')?.classList.toggle('zlfp-active', reason < 4);
    const reference = orderedMatch('AB', 6, 2, 1), grouped = orderedMatch('AB', 6, 2, 3);
    q('[data-fp-reference]').textContent = reference.output;
    q('[data-fp-grouped]').innerHTML = 'AB ' + grouped.batches.map(batch => `<span>${batch.map(store => store.byte).join('')}</span>`).join(' ');
    host.status.textContent = (admission.fast ? T('三项入口条件都满足。', 'All three entry conditions hold. ') : T('入口条件不足，继续普通状态机；这本身不是错误。', 'The guard fails, so the ordinary state machine continues; this alone is not an error. ')) + T(`当前展开第 ${reason + 1} / 6 项依据。`, `Inspecting reason ${reason + 1} of 6.`);
  }
  for (const control of [input, output, held]) host.on(control, 'change', render);
  host.on(host.controls.querySelector('[data-fp-step]'), 'click', () => { stop(); reason = (reason + 1) % reasons.length; render(); });
  host.on(play, 'click', () => {
    if (host.timer) { stop(); return; }
    play.textContent = T('暂停', 'Pause');
    host.timer = setInterval(() => { reason = (reason + 1) % reasons.length; render(); if (reason === reasons.length - 1) stop(); }, 2200);
  });
  host.on(host.controls.querySelector('[data-fp-reset]'), 'click', () => { stop(); input.value = '6'; output.value = '258'; held.value = '0'; reason = 0; render(); });
  host.abort.signal.addEventListener('abort', stop, {once: true});
  render();
}
