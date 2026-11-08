// Independent four-symbol teaching decoder, not zlib execution.
const CODE = { A: '0', B: '10', C: '110', D: '111' };

export function lookupTrace(message = 'AD', lang = 'zh') {
  const T = (zh, en) => lang === 'en' ? en : zh;
  if (!['AD', 'AC', 'AB'].includes(message)) throw new RangeError('Unknown example');
  const stream = [...message].map(symbol => CODE[symbol]).join('');
  const valueAt = consumed => {
    const rest = stream.slice(consumed);
    return rest ? parseInt([...rest].reverse().join(''), 2) : 0;
  };
  let consumed = 0;
  let output = '';
  const events = [{
    consumed, output, root: null, sub: null, peek: [], focus: null,
    action: T('输入已就绪', 'Input ready'),
    text: T(`教学消息 ${message}：缓冲区保留 ${stream.length} 个有效位。点击下一步，先查看低两位。`,
      `Teaching message ${message}: the buffer holds ${stream.length} valid bits. Step forward to inspect the lowest two.`),
  }];
  for (const symbol of message) {
    const root = valueAt(consumed) & 3;
    events.push({
      consumed, output, root, sub: null, peek: [consumed, consumed + 1], focus: 'root',
      action: T(`查看根表：${root.toString(2).padStart(2, '0')}`, `Root lookup: ${root.toString(2).padStart(2, '0')}`),
      text: symbol === 'A'
        ? T('低两位是 10。根表仍然得到 A，因为最低位 0 已经确定这个符号；第二位属于后续输入。',
          'The lowest two bits are 10. The root table still gives A: its lowest bit, 0, already identifies the symbol. The other bit belongs to later input.')
        : CODE[symbol].length === 2
          ? T('低两位是 01，根表直接得到 B，这个码正好需要两位。',
            'The lowest two bits are 01. The root table gives B directly; this code needs exactly two bits.')
          : T('低两位是 11，根表无法直接区分 C 与 D，它给出一个子表链接。',
            'The lowest two bits are 11. They cannot distinguish C from D, so the root entry links to a subtable.'),
    });
    if (CODE[symbol].length <= 2) {
      consumed += CODE[symbol].length;
      output += symbol;
      events.push({
        consumed, output, root, sub: null, peek: [], focus: null,
        action: T(`产生 ${symbol} · 消耗 ${CODE[symbol].length} 位`, `Emit ${symbol} · consume ${CODE[symbol].length} bit${CODE[symbol].length === 1 ? '' : 's'}`),
        text: symbol === 'A'
          ? T('只移走 A 的一位。刚才查看的第二位留下来，继续参与下一个符号的解码。',
            'Only A’s one bit is removed. The other inspected bit stays in the buffer for the next symbol.')
          : T('B 的两位已经移走。教学消息解码完成。',
            'B’s two bits have been removed. The teaching message is complete.'),
      });
    } else {
      consumed += 2;
      events.push({
        consumed, output, root, sub: null, peek: [], focus: 'link',
        action: T('根表链接 · 先消耗 2 位', 'Follow the link · consume 2 bits'),
        text: T('移走根表已经解释的两位，还没有产生新符号。剩下的一位用于子表索引。',
          'Remove the two bits handled by the root table. No new symbol has been emitted yet. The remaining bit indexes the subtable.'),
      });
      const sub = valueAt(consumed) & 1;
      events.push({
        consumed, output, root, sub, peek: [consumed], focus: 'sub',
        action: T(`查看子表：${sub}`, `Subtable lookup: ${sub}`),
        text: T(`子表索引 ${sub} 得到 ${symbol}。这个表项还需要消耗一位。`,
          `Subtable index ${sub} gives ${symbol}. This entry consumes one more bit.`),
      });
      consumed++;
      output += symbol;
      events.push({
        consumed, output, root, sub, peek: [], focus: null,
        action: T(`产生 ${symbol} · 再消耗 1 位`, `Emit ${symbol} · consume 1 more bit`),
        text: T(`${symbol} 共消耗三位：根表两位，加上子表一位。教学消息 ${message} 解码完成。`,
          `${symbol} used three bits in total: two at the root and one in the subtable. Teaching message ${message} is complete.`),
      });
    }
  }
  return { message, stream, events: events.map(event => ({ ...event,
    hold: valueAt(event.consumed), bits: stream.length - event.consumed,
  })) };
}

export function mountLookup(host) {
  const T = (zh, en) => host.lang === 'en' ? en : zh;
  let trace = lookupTrace('AD', host.lang);
  let step = 0;
  host.controls.innerHTML = `
    <label>${T('教学消息', 'Message')} <select aria-label="${T('查表教学消息', 'Lookup teaching message')}"><option>AD</option><option>AC</option><option>AB</option></select></label>
    <button type="button" data-lookup-next>${T('下一步', 'Next step')}</button>
    <button type="button" data-lookup-reset class="zl-quiet">${T('重置', 'Reset')}</button>
    <label class="zl-scrub">${T('解码进度', 'Decoding progress')} <input type="range" min="0" max="6" value="0" aria-label="${T('查表解码进度', 'Lookup decoding progress')}"></label>`;
  host.view.innerHTML = `
    <div class="zl-lu">
      <div class="zl-lu-reading"><span>${T('依次到达的码位', 'Bits in arrival order')}</span><code data-lu-stream></code><small>${T('时间 →', 'time →')}</small></div>
      <div class="zl-lu-timeline" aria-label="${T('原始码位的读取情况', 'Consumption of the original code bits')}"></div>
      <div class="zl-lu-buffer-label"><span>${T('位缓冲', 'Bit buffer')} <code>hold</code> · ${T('高位在左', 'high bit on the left')}</span><span><code data-lu-hold>1110</code> <small data-lu-count>${T('4 位有效', '4 valid bits')}</small></span></div>
      <div class="zl-lu-reservoir" role="img" aria-label="${T('位缓冲', 'Bit buffer')}">
        <div class="zl-lu-bit-layer" aria-hidden="true"></div>
        <div class="zl-lu-peek-band" aria-hidden="true"><span>${T('只查看', 'inspect only')}</span></div>
        <span class="zl-lu-low-label" aria-hidden="true">${T('最低位 / bit 0', 'lowest bit / bit 0')}</span>
      </div>
      <div class="zl-lu-action" aria-hidden="true"><span data-lu-action>${T('输入已就绪', 'Input ready')}</span><i>↓</i></div>
      <div class="zl-lu-tables">
        <table class="zl-lu-root"><caption>${T('根表', 'Root table')} <small>${T('查看低 2 位', 'inspect the lowest 2 bits')}</small></caption><thead><tr><th>${T('索引', 'Index')}</th><th>${T('结果', 'Result')}</th><th>${T('消耗', 'Consume')}</th></tr></thead><tbody>
          <tr data-lu-root="0"><td>00</td><td>A</td><td>${T('1 位', '1 bit')}</td></tr>
          <tr data-lu-root="1"><td>01</td><td>B</td><td>${T('2 位', '2 bits')}</td></tr>
          <tr data-lu-root="2"><td>10</td><td>A</td><td>${T('1 位', '1 bit')}</td></tr>
          <tr data-lu-root="3"><td>11</td><td>${T('子表 →', 'Subtable →')}</td><td>${T('2 位', '2 bits')}</td></tr>
        </tbody></table>
        <div class="zl-lu-link" aria-hidden="true"><span>${T('继续查找', 'follow link')}</span><i>→</i></div>
        <table class="zl-lu-sub"><caption>${T('子表', 'Subtable')} <small>${T('再看 1 位', 'inspect 1 more bit')}</small></caption><thead><tr><th>${T('索引', 'Index')}</th><th>${T('结果', 'Result')}</th><th>${T('消耗', 'Consume')}</th></tr></thead><tbody>
          <tr data-lu-sub="0"><td>0</td><td>C</td><td>${T('1 位', '1 bit')}</td></tr>
          <tr data-lu-sub="1"><td>1</td><td>D</td><td>${T('1 位', '1 bit')}</td></tr>
        </tbody></table>
      </div>
      <div class="zl-lu-output"><span>${T('输出', 'Output')}</span><div data-lu-output></div><small data-lu-step></small></div>
      <p class="zl-mini">${T('固定的四符号教学编码：A=0 · B=10 · C=110 · D=111。这里不是完整 DEFLATE 字节流。', 'Fixed four-symbol teaching code: A=0 · B=10 · C=110 · D=111. This is not a complete DEFLATE byte stream.')}</p>
    </div>`;

  const root = host.view.querySelector('.zl-lu');
  const select = host.controls.querySelector('select');
  const range = host.controls.querySelector('input');
  const next = host.controls.querySelector('[data-lookup-next]');
  const reservoir = root.querySelector('.zl-lu-reservoir');
  const band = root.querySelector('.zl-lu-peek-band');
  const layer = root.querySelector('.zl-lu-bit-layer');
  const timeline = root.querySelector('.zl-lu-timeline');
  const output = root.querySelector('[data-lu-output]');
  let bitNodes = [];
  let timeNodes = [];
  let outputNodes = [];

  const resetNodes = () => {
    root.querySelector('[data-lu-stream]').textContent = [...trace.message].map(s => CODE[s]).join(' | ');
    layer.innerHTML = [...trace.stream].map((bit, i) => `<span class="zl-lu-bit" style="--slot:${i}" data-original="${i}"><b>${bit}</b><small>bit ${i}</small></span>`).join('');
    timeline.innerHTML = [...trace.stream].map((bit,i) => `<span data-original="${i}">${bit}</span>`).join('');
    output.innerHTML = [...trace.message].map(symbol => `<b>${symbol}</b>`).join('');
    bitNodes = [...layer.children];
    timeNodes = [...timeline.children];
    outputNodes = [...output.children];
    range.max = String(trace.events.length - 1);
  };

  const render = () => {
    const state = trace.events[step];
    const holdBits = state.bits ? state.hold.toString(2).padStart(state.bits, '0') : '∅';
    range.value = String(step);
    next.disabled = step === trace.events.length - 1;
    root.dataset.focus = state.focus || 'none';
    root.querySelector('[data-lu-hold]').textContent = holdBits;
    root.querySelector('[data-lu-count]').textContent = T(`${state.bits} 位有效`, `${state.bits} valid bit${state.bits === 1 ? '' : 's'}`);
    root.querySelector('[data-lu-action]').textContent = state.action;
    root.querySelector('[data-lu-step]').textContent = `${step} / ${trace.events.length - 1}`;
    reservoir.setAttribute('aria-label', T(`位缓冲数值 ${holdBits}，${state.bits} 位有效。${state.action}`,
      `Bit buffer value ${holdBits}, ${state.bits} valid bits. ${state.action}`));
    band.classList.toggle('is-active', state.peek.length > 0);
    band.style.setProperty('--peek', String(state.peek.length || 1));
    bitNodes.forEach((node, i) => {
      const consumed = i < state.consumed;
      node.classList.toggle('is-consumed', consumed);
      node.classList.toggle('is-peeked', state.peek.includes(i));
      node.style.setProperty('--shift', String(consumed ? Math.max(0, i) : state.consumed));
      node.querySelector('small').textContent = consumed ? T('已消耗', 'used') : `bit ${i - state.consumed}`;
    });
    timeNodes.forEach((node, i) => {
      node.classList.toggle('is-consumed', i < state.consumed);
      node.classList.toggle('is-peeked', state.peek.includes(i));
    });
    root.querySelectorAll('[data-lu-root]').forEach(row => {
      row.classList.toggle('is-selected', Number(row.dataset.luRoot) === state.root);
      row.classList.toggle('is-looking', Number(row.dataset.luRoot) === state.root && state.focus === 'root');
    });
    root.querySelectorAll('[data-lu-sub]').forEach(row => {
      row.classList.toggle('is-selected', Number(row.dataset.luSub) === state.sub);
      row.classList.toggle('is-looking', Number(row.dataset.luSub) === state.sub && state.focus === 'sub');
    });
    outputNodes.forEach((node, i) => node.classList.toggle('is-produced', i < state.output.length));
    host.status.textContent = state.text;
  };

  host.on(select, 'change', () => { trace = lookupTrace(select.value, host.lang); step = 0; resetNodes(); render(); });
  host.on(range, 'input', () => { step = Number(range.value); render(); });
  host.on(next, 'click', () => { if (step < trace.events.length - 1) step++; render(); });
  host.on(host.controls.querySelector('[data-lookup-reset]'), 'click', () => { step = 0; render(); });
  resetNodes();
  render();
}
