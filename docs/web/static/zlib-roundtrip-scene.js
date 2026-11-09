import {ROUNDTRIP_INPUT, ROUNDTRIP_BYTES, ROUNDTRIP_FIELDS, ROUNDTRIP_LAST, roundtripState} from './zlib-roundtrip-scene.mjs';

export function mountRoundtrip(host) {
  const T = host.t;
  let step = 0;
  const reduced = matchMedia('(prefers-reduced-motion: reduce)');
  const names = [T('最后一块 · 固定编码', 'Final block · fixed codes'), T('直接输出 A', 'Emit A'), T('直接输出 B', 'Emit B'),
    T('复制长度 6', 'Copy length 6'), T('回退距离 2', 'Go back distance 2'), T('这一块结束', 'End this block')];
  const text = [
    T('任务开始：这八个字节是要保存、再恢复的原文。', 'Start with the eight original bytes to store and recover.'),
    T('选定表示：直接输出 A、B，再回退 2 字节复制 6 次。收发双方还要知道使用哪种编码、在哪里结束。', 'Choose a representation: emit A and B, then copy six bytes from distance two. Both sides also need the coding choice and the end position.'),
    T('先写块头。按写入顺序，1 表示最后一块，接着的 10 选择固定编码。', 'Write the block header. In writing order, 1 marks the final block and the following 10 selects fixed coding.'),
    T('A 的固定码占 8 位，接在 3 位块头后，跨越第一个字节边界。', 'The eight-bit fixed code for A follows the three header bits, crossing the first byte boundary.'),
    T('B 再占 8 位。存储按字节分组，解释按编码字段分组；两种边界不必重合。', 'B uses another eight bits. Storage groups bits into bytes; interpretation groups them into fields. The boundaries need not coincide.'),
    T('长度 6 的固定码占 7 位。这个长度的编码已经完整，不需要另接补充位。', 'The fixed code for length six uses seven bits. This exact length fits in one code, with no additional bits after it.'),
    T('距离 2 的固定码占 5 位，也不需要另接补充位。匹配现在表示完整。', 'The fixed code for distance two uses five bits, with no additional bits after it. The match is now fully represented.'),
    T('再写 7 位块结束符，补两个零位：38 个有效位装入 5 字节 73 74 82 40 00。', 'Add the seven-bit end symbol and two zero padding bits: 38 meaningful bits occupy five bytes, 73 74 82 40 00.'),
    T('解码器解释块头，再读出 A。已经恢复的第一个字节与原文相同。', 'The decoder interprets the header, then A. Its first recovered byte equals the original.'),
    T('再读出 B。已经恢复 AB，接下来可以从这两个字节复制。', 'Decode B next. The recovered AB now supplies the source for copying.'),
    T('读完长度和距离，开始复制：位置 2 从位置 0 读取 A。位置从零计数。', 'Read length and distance, then copy: position 2 reads A from position 0. Positions count from zero.'),
    T('位置 3 从位置 1 读取 B。虚线圈出来源，实线圈出刚写入的位置。', 'Position 3 reads B from position 1. A dashed border marks the source; a solid border marks the new write.'),
    T('位置 4 读取刚产生的位置 2。若目标只有五格，就在这里暂停：已恢复 ABABA，同一条匹配还剩 3 字节。', 'Position 4 reads the newly produced position 2. A five-position destination pauses here: ABABA is recovered, with three bytes left in this same match.'),
    T('换好输出区，继续同一匹配：位置 5 读取位置 3，产生 B。无需再读一条匹配指令。', 'After replacing the destination, continue the same match: position 5 reads position 3 to produce B. No new match instruction is needed.'),
    T('位置 6 读取位置 4，产生 A，仍然回退 2 字节。', 'Position 6 reads position 4 to produce A, still at distance two.'),
    T('位置 7 读取位置 5，产生 B。八字节已恢复，还要识别块结束符。', 'Position 7 reads position 5 to produce B. All eight bytes are recovered; the end symbol remains to be recognized.'),
    T('识别最终块结束符，裸流完成。输出逐字节等于输入；五格目标区的两批结果是 ABABA 和 BAB。', 'Recognize the final block’s end symbol: the raw stream is complete. Output equals input byte for byte; five-position destinations produce ABABA and BAB.'),
  ];
  const hex = byte => byte.toString(16).toUpperCase().padStart(2, '0');
  host.controls.innerHTML = `<button type="button" data-rt-back>${T('上一步', 'Back')}</button><button type="button" data-rt-next>${T('执行下一步', 'Next step')}</button><button type="button" data-play>${T('播放', 'Play')}</button><button type="button" data-rt-reset class="zl-quiet">${T('从头开始', 'Restart')}</button><label>${T('查看任一步', 'Inspect a step')}<input data-rt-range type="range" min="0" max="16" value="0" step="1" aria-label="${T('表示与恢复步骤', 'Representation and recovery step')}"></label>`;
  host.view.innerHTML = `<div class="zrt-scene" tabindex="0" role="group" aria-label="${T('原文、编码与恢复结果；左右方向键逐步查看', 'Original, encoding and recovered output; left and right arrows change step')}"><div class="zrt-heading"><span data-rt-phase></span><span data-rt-count></span></div>
    <section class="zrt-row"><h4>${T('要保存的原文 · 8 字节', 'Original to store · 8 bytes')}</h4><div class="zrt-cells zrt-original">${[...ROUNDTRIP_INPUT].map((letter,i)=>`<span data-rt-input="${i}"><b>${letter}</b><small>${hex(letter.charCodeAt(0))}</small></span>`).join('')}</div></section>
    <section class="zrt-row"><h4>${T('按约定把指令写成位 · 固定编码', 'Write instructions as bits · fixed codes')}</h4><div class="zrt-fields">${ROUNDTRIP_FIELDS.map((field,i)=>`<button type="button" data-rt-field="${i}" aria-label="${T('查看编码：', 'Inspect code: ')+names[i]}"><span>${names[i]}</span><code>${field.bits.join('')}</code><small>${field.width} ${T('位', 'bits')}</small></button>`).join('')}</div><p class="zrt-help">${T('点一项查看它占用的位。位从左向右按写入／读取顺序排列。', 'Select an item to highlight its bits. Bits run left to right in writing/reading order.')}</p></section>
    <section class="zrt-row"><h4>${T('要发送的编码 · 5 字节', 'Encoding to send · 5 bytes')}</h4><div class="zrt-packed">${ROUNDTRIP_BYTES.map((byte,i)=>`<div data-rt-byte="${i}"><code>${hex(byte)}</code><span class="zrt-bitrow">${Array.from({length:8},(_,bit)=>`<i data-rt-bit="${i*8+bit}">${(byte>>>bit)&1}</i>`).join('')}</span><small>${T('字节', 'byte')} ${i}</small></div>`).join('')}</div><p class="zrt-help">${T('每个字节下方先列最低位。最末两位只补齐字节，不是新指令。', 'The low bit is listed first below each byte. The final two bits only pad the byte; they are not instructions.')}</p></section>
    <section class="zrt-row"><h4>${T('接收端恢复的字节 · 点一格查看写入', 'Bytes recovered by the receiver · select a write')}</h4><div class="zrt-cells zrt-output">${[...ROUNDTRIP_INPUT].map((_,i)=>`<button type="button" data-rt-output="${i}" aria-label="${T('查看输出位置 ', 'Inspect output position ')+i}"><b>·</b><small>${i}</small></button>`).join('')}</div><div class="zrt-ledger"><div><small>${T('目前已恢复', 'Recovered so far')}</small><code data-rt-prefix>∅</code></div><div><small>${T('还要复制', 'Still to copy')}</small><code data-rt-remaining>—</code></div><div><small>${T('与原文核对', 'Compare with original')}</small><span data-rt-check></span></div></div></section><p class="zrt-explanation" data-rt-explanation></p></div>`;
  const q = selector => host.view.querySelector(selector), range = host.controls.querySelector('[data-rt-range]');
  const back = host.controls.querySelector('[data-rt-back]'), next = host.controls.querySelector('[data-rt-next]'), play = host.controls.querySelector('[data-play]');
  const stop = () => {clearInterval(host.timer); host.timer = null; play.textContent = T('播放', 'Play');};
  function render() {
    const s = roundtripState(step);
    range.value = String(step); back.disabled = step === 0; next.disabled = s.complete;
    q('[data-rt-phase]').textContent = step < 2 ? T('选定表示', 'Choose representation') : step < 8 ? T('写成编码', 'Encode') : T('恢复原文', 'Recover original');
    q('[data-rt-count]').textContent = `${step} / 16`; q('[data-rt-explanation]').textContent = text[step];
    for (const node of host.view.querySelectorAll('[data-rt-field]')) {const i = Number(node.dataset.rtField); node.classList.toggle('zrt-active', i === s.field); node.setAttribute('aria-pressed', String(i === s.field));}
    for (const node of host.view.querySelectorAll('[data-rt-bit]')) {
      const bit = Number(node.dataset.rtBit), field = ROUNDTRIP_FIELDS[s.field];
      node.classList.toggle('zrt-written', bit < s.encodedBits || (step >= 7 && bit >= 38));
      node.classList.toggle('zrt-active', !!field && bit >= field.start && bit < field.end);
      node.classList.toggle('zrt-padding', bit >= 38);
    }
    for (const node of host.view.querySelectorAll('[data-rt-byte]')) node.classList.toggle('zrt-ready', step >= 7 || (Number(node.dataset.rtByte)+1)*8 <= s.encodedBits);
    for (const node of host.view.querySelectorAll('[data-rt-output]')) {
      const i = Number(node.dataset.rtOutput); node.querySelector('b').textContent = s.output[i] || '·';
      node.classList.toggle('zrt-done', i < s.output.length); node.classList.toggle('zrt-source', i === s.source);
      node.classList.toggle('zrt-target', i === s.target || (step === 8 && i === 0) || (step === 9 && i === 1));
      node.setAttribute('aria-pressed', String(i === s.output.length-1)); q(`[data-rt-input="${i}"]`).classList.toggle('zrt-verified', i < s.output.length);
    }
    q('[data-rt-prefix]').textContent = s.output || '∅'; q('[data-rt-remaining]').textContent = step < 10 ? '—' : String(s.remaining);
    q('[data-rt-check]').textContent = step < 8 ? T('尚未开始恢复', 'Recovery has not started') : s.complete ? T('8 / 8 字节相等；完成', '8 / 8 bytes equal; complete') : T(`已恢复的 ${s.output.length} 字节都相同`, `All ${s.output.length} recovered bytes match`);
    host.status.textContent = text[step]; if (s.complete) stop();
  }
  const go = value => {stop(); step = Math.max(0, Math.min(ROUNDTRIP_LAST, value)); render();};
  host.on(back, 'click', () => go(step-1)); host.on(next, 'click', () => go(step+1)); host.on(range, 'input', () => go(Number(range.value)));
  host.on(host.controls.querySelector('[data-rt-reset]'), 'click', () => go(0));
  for (const node of host.view.querySelectorAll('[data-rt-field]')) host.on(node, 'click', () => go(Number(node.dataset.rtField)+2));
  for (const node of host.view.querySelectorAll('[data-rt-output]')) host.on(node, 'click', () => go(Number(node.dataset.rtOutput)+8));
  host.on(q('.zrt-scene'), 'keydown', event => {
    if (!['ArrowLeft','ArrowRight','Home','End'].includes(event.key) || event.target.closest('button')) return;
    event.preventDefault(); go(event.key === 'Home' ? 0 : event.key === 'End' ? 16 : step+(event.key === 'ArrowRight' ? 1 : -1));
  });
  host.on(play, 'click', () => {
    if (host.timer) {stop(); return;}
    if (reduced.matches) {go(step === 16 ? 0 : step+1); return;}
    if (step === 16) step = 0; play.textContent = T('暂停', 'Pause'); render();
    host.timer = setInterval(() => {step++; render();}, 2100);
  });
  host.abort.signal.addEventListener('abort', stop, {once:true}); host.on(reduced, 'change', () => {if (reduced.matches) stop();}); render();
}
