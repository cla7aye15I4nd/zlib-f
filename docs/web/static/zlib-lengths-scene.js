import {createLengthsState, stepLengths} from './zlib-lengths-model.mjs';

export function mountLengths(host) {
  const T = host.t;
  host.classList.add('zll-scene');
  host.controls.innerHTML = `
    <p class="zll-control-purpose">${T('选择一组描述及可用格数，观察解码器能否完整写出所要求的码长。格子装的是码长，不是原文字节。', 'Choose description instructions and available slots; inspect whether their requested lengths fit. The slots hold code lengths, not original bytes.')}</p>
    <label class="zll-choice">${T('描述指令与可用格数', 'Instructions and available slots')}
      <select data-lengths-example>
        <option value="valid">${T('五条描述 · 24 格，恰好填满', 'Five descriptions · 24 slots, exact fit')}</option>
        <option value="overrun">${T('同样描述 · 23 格，最后一段放不下', 'Same descriptions · 23 slots, final run does not fit')}</option>
        <option value="previous">${T('第一条就重复前值，但还没有前值', 'Repeat a previous value before any value exists')}</option>
      </select>
    </label>
    <button type="button" data-lengths-step>${T('下一步', 'Step')}</button>
    <button type="button" data-play>${T('播放', 'Play')}</button>
    <button type="button" class="zl-quiet" data-lengths-reset>${T('重置', 'Reset')}</button>`;
  host.view.innerHTML = `
    <p class="zll-purpose">${T('输入是已经解出的码长描述指令；输出是每个符号的码长。重复指令用很少的额外位生成一整段相同数值。', 'Input: decoded length-description instructions. Output: one code length per symbol. A repeat uses a few extra bits to generate a run of equal values.')}</p>
    <section class="zll-instructions" aria-label="${T('描述指令输入', 'Length-description input')}">
      <div class="zll-row-heading"><strong>${T('描述指令', 'Description instructions')}</strong><span data-lengths-read></span></div>
      <ol class="zll-rail" data-lengths-rail></ol>
      <p class="zll-notation">${T('额外值按通常的二进制写法显示，高位在左。这里只计算重复字段，不给指令虚构 Huffman 码。', 'Extra values use ordinary binary notation, high bit on the left. Only repeat fields are counted; no Huffman code is invented for these instructions.')}</p>
    </section>
    <div class="zll-operation" data-lengths-operation></div>
    <section class="zll-output" aria-label="${T('展开后的码长数组', 'Expanded length array')}">
      <div class="zll-row-heading"><strong>${T('每格是一个符号的码长', 'One code length per symbol')}</strong><span data-lengths-written></span></div>
      <ol class="zll-slots" data-lengths-slots></ol>
      <div class="zll-invariant" data-lengths-bound></div>
    </section>`;
  const q = selector => host.view.querySelector(selector);
  const choice = host.controls.querySelector('[data-lengths-example]');
  const step = host.controls.querySelector('[data-lengths-step]');
  const play = host.controls.querySelector('[data-play]');
  let state = createLengthsState();
  const extraWidth = symbol => symbol === 16 ? 2 : symbol === 17 ? 3 : symbol === 18 ? 7 : 0;
  const stop = () => {
    clearInterval(host.timer);
    host.timer = null;
    play.textContent = T('播放', 'Play');
  };
  function render() {
    const {current, cursor, output, capacity, phase, pending, amount, start, error} = state;
    const finished = phase === 'done' || phase === 'error';
    host.dataset.lengthsPhase = phase;
    q('[data-lengths-read]').textContent = T('已读符号 ', 'Symbols read: ') + `${cursor} / ${state.instructions.length}`;
    q('[data-lengths-written]').textContent = T('已写码长 ', 'Lengths written: ') + `${output.length} / ${capacity}`;
    q('[data-lengths-rail]').innerHTML = state.instructions.map((instruction, i) => {
      const width = extraWidth(instruction.symbol);
      const active = i === cursor - 1 && phase !== 'read' && phase !== 'done';
      return `<li class="${i < cursor ? 'zll-read' : ''} ${active ? 'zll-active' : ''}">
        <span class="zll-instruction-index">${i + 1}</span><b>${instruction.symbol}</b>
        <span>${width ? T('额外值 ', 'extra ') + `${instruction.extra} <small>(${instruction.extra.toString(2).padStart(width, '0')}₂ · ${width} ${T('位', 'bits')})</small>` : T('直接码长', 'direct length')}</span>
      </li>`;
    }).join('');
    q('[data-lengths-slots]').innerHTML = Array.from({length: capacity}, (_, i) => {
      const written = i < output.length;
      const inRun = current && i >= start && i < start + amount;
      const fresh = phase === 'write' && i === output.length - 1 && i >= start;
      return `<li class="${written ? 'zll-filled' : ''} ${inRun ? 'zll-run' : ''} ${fresh ? 'zll-fresh' : ''}"><small>${i}</small><b>${written ? output[i] : '·'}</b></li>`;
    }).join('');
    let explanation;
    let operation;
    if (error === 'previous') {
      operation = T('16 → 需要前一个码长 → 拒绝', '16 → needs a previous length → reject');
      explanation = T('还没有写过任何码长，不能读取“前一个”。C 可能已经取入装着额外位的字节，但会在消费这 2 位前报错，也不写数组。图中只统计字段消费量。', 'No previous length exists. C may already have fetched bytes holding the extra bits, but rejects before consuming those two bits and writes no array entry. This scene counts field consumption only.');
    } else if (error === 'overrun') {
      operation = `${start} + ${amount} > ${capacity} → ${T('拒绝整次重复', 'reject the entire repeat')}`;
      explanation = T(`18 的额外值为 2，要求 11 + 2 = 13 个零；只剩 ${capacity - start} 格。检查发生在写入之前，已经写好的 ${start} 个码长不变。`, `Symbol 18 has extra value 2: it requests 11 + 2 = 13 zero lengths, but only ${capacity - start} slots remain. The check precedes every store in this repeat; the ${start} existing lengths stay unchanged.`);
    } else if (error === 'short') {
      operation = T('指令用完，数组尚未填满', 'Instructions ended before the array filled');
      explanation = T('真实解析器会继续等待下一条描述指令；这个固定教学输入没有更多指令。', 'The real parser would need another description instruction; this fixed teaching input contains no more.');
    } else if (phase === 'done') {
      operation = T('5 条指令 → 24 个码长', '5 instructions → 24 code lengths');
      explanation = T('所有格子恰好填满。符号消费与数组位置是不同进度：16、17、18 各消耗一条描述，却分别展开 4、5、13 个码长。接下来才检查这组码长能否构成需要的编码表。', 'Every slot is filled. Instruction consumption and array progress differ: 16, 17 and 18 each consume one description symbol but generate 4, 5 and 13 lengths. Checking whether the resulting lengths form the required code tables comes afterward.');
    } else if (phase === 'read') {
      operation = output.length === 0 ? T('先读一条描述，再决定写几个码长', 'Read one instruction, then determine its expansion') : T('本条展开完毕 → 读取下一条', 'Expansion complete → read the next instruction');
      explanation = T('下排的格子装的是码长，不是解压后的字节。上排每条描述可以对应下排一个或多个格子。', 'The lower slots contain code lengths, not decompressed bytes. One upper instruction can describe one or many lower slots.');
    } else if (phase === 'expand') {
      operation = `${T('已读符号', 'Read symbol')} ${current.symbol} → ${T('检查前值与展开范围', 'check its prerequisite and expansion')}`;
      explanation = current.symbol === 16
        ? T('16 本身不是码长。它要求已有前一个码长，才允许消费 2 位额外值，决定重复 3 到 6 次。补足输入位可以先发生，消费额外字段必须在检查之后。', '16 is not a code length. A previous length must exist before its two-bit extra value is consumed to choose 3 through 6 repetitions. Input refill can happen earlier; extra-field consumption must follow that check.')
        : current.symbol === 17 || current.symbol === 18
          ? T('这条指令表示一段零。读取额外值、算出段长，并确认剩余格子足够，才开始写入。', 'This instruction describes a run of zeroes. Consume its extra value, calculate the run length, and check remaining space before writing.')
          : T('这是普通码长，直接产生一个数值；不需要重复次数的额外位。', 'This is an ordinary code length: it produces one value and needs no repeat-count extra bits.');
    } else {
      const symbol = current.symbol;
      const arithmetic = symbol < 16 ? '1' : `${symbol === 18 ? 11 : 3} + ${current.extra} = ${amount}`;
      operation = `${symbol} → ${T('码长', 'length')} ${state.value} × (${arithmetic})`;
      explanation = T(`整段范围已经通过检查。逐个写入同一码长，还剩 ${pending} 格；前面已展开的内容保持不变。`, `The entire run passed its range check. Write the same length one slot at a time; ${pending} slots remain. Previously expanded lengths remain unchanged.`);
    }
    q('[data-lengths-operation]').textContent = operation;
    q('[data-lengths-bound]').innerHTML = `<span>${T('写入边界', 'Write bound')}: <b>0 ≤ ${output.length} ≤ ${capacity}</b></span><span>${T('已消费重复字段', 'Repeat-field bits consumed')}: <b>${state.extraConsumed}</b></span>`;
    host.status.textContent = explanation;
    step.disabled = finished;
    play.disabled = finished;
    if (finished) stop();
  }
  function advance() { state = stepLengths(state); render(); }
  function reset() { stop(); state = createLengthsState(choice.value); render(); }
  host.on(choice, 'change', reset);
  host.on(step, 'click', () => { stop(); advance(); });
  host.on(host.controls.querySelector('[data-lengths-reset]'), 'click', reset);
  host.on(play, 'click', () => {
    if (host.timer) { stop(); return; }
    play.textContent = T('暂停', 'Pause');
    advance();
    if (state.phase !== 'done' && state.phase !== 'error') host.timer = setInterval(advance, 430);
  });
  host.abort.signal.addEventListener('abort', stop, {once: true});
  render();
}
