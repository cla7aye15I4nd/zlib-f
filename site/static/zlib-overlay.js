import { overlay, PLANS } from './zlib-models.mjs';

let overlayId = 0;

// This scene compares constructed write schedules. It is not a zlib execution.
export function mountOverlay(host) {
  const T = (zh, en) => host.lang === 'en' ? en : zh;
  const id = `zl-overlay-${++overlayId}`;
  let q = 0;
  const max = PLANS.safe.length;
  const plot = { left: 48, right: 610, top: 24, bottom: 214 };
  const x = step => plot.left + step * (plot.right - plot.left) / max;
  const y = value => plot.bottom - value * (plot.bottom - plot.top) / 32;
  const points = (kind, last = max) => Array.from({length: last + 1}, (_, step) => {
    const state = overlay(kind, step);
    return `${x(step)},${y(state.pending)}`;
  }).join(' ');
  const boundaryPoints = Array.from({length: max + 1}, (_, step) => `${x(step)},${y(8 + step * 3)}`).join(' ');

  host.controls.innerHTML = `
    <label class="zl-scrub" for="${id}-range">${T('已读取符号','Symbols read')}
      <input id="${id}-range" aria-label="${T('对照计划的已读取符号','Symbols read in both schedules')}" type="range" min="0" max="${max}" value="0" aria-describedby="${id}-hint">
    </label>
    <span class="zlo-counter" aria-hidden="true"><b data-q>0</b> / ${max}</span>
    <button type="button" data-next>${T('下一符号','Next symbol')}</button>
    <button type="button" data-reset class="zl-quiet">${T('重置','Reset')}</button>`;
  host.view.classList.add('zlo-view');
  host.view.innerHTML = `
    <div class="zlo-question"><span>${T('同样的容量，不同的写入节奏。','Same capacity. Different write schedules.')}</span><strong>${T('总量都放得下，哪个计划先出问题？','Both fit at the end. Which one fails along the way?')}</strong></div>
    <div class="zlo-chart-wrap">
      <svg class="zlo-chart" viewBox="0 0 650 254" role="img" aria-labelledby="${id}-chart-title ${id}-chart-desc">
        <title id="${id}-chart-title">${T('写入前缀与未读符号边界','Output prefixes and the unread-symbol boundary')}</title>
        <desc id="${id}-chart-desc">${T('横轴为已读取符号数 q，纵轴为字节偏移。两条实线分别表示安全计划和前重计划，虚线为 B 加 3q。','The horizontal axis counts symbols read, q; the vertical axis shows byte offsets. The solid lines show the safe and front-loaded schedules; the dashed line is B plus 3q.')}</desc>
        ${[0,8,16,24,32].map(value => `<line class="zlo-grid" x1="${plot.left}" y1="${y(value)}" x2="${plot.right}" y2="${y(value)}"/><text class="zlo-axis-label" x="${plot.left-10}" y="${y(value)+4}" text-anchor="end">${value}</text>`).join('')}
        <text class="zlo-axis-name" x="${plot.left}" y="12">${T('字节偏移','Byte offset')}</text>
        ${Array.from({length:max+1}, (_, step) => `<text class="zlo-axis-label" x="${x(step)}" y="237" text-anchor="middle">${step}</text>`).join('')}
        <text class="zlo-axis-name" x="630" y="237">q</text>
        <polyline class="zlo-boundary" points="${boundaryPoints}"/>
        <polyline class="zlo-forecast zlo-safe-line" points="${points('safe')}"/>
        <polyline class="zlo-forecast zlo-unsafe-line" points="${points('unsafe')}"/>
        <polyline class="zlo-progress zlo-safe-line" data-safe-line points="${points('safe',0)}"/>
        <polyline class="zlo-progress zlo-unsafe-line" data-unsafe-line points="${points('unsafe',0)}"/>
        <line class="zlo-cursor" data-cursor x1="${x(0)}" x2="${x(0)}" y1="${plot.top}" y2="${plot.bottom}"/>
        <circle class="zlo-current zlo-safe-point" data-safe-point r="4.5" cx="${x(0)}" cy="${y(2)}"/>
        <circle class="zlo-current zlo-unsafe-point" data-unsafe-point r="4.5" cx="${x(0)}" cy="${y(2)}"/>
        <circle class="zlo-boundary-point" data-boundary-point r="3.5" cx="${x(0)}" cy="${y(8)}"/>
        <g class="zlo-first-breach" data-first-breach visibility="hidden">
          <circle cx="${x(1)}" cy="${y(14)}" r="10"/>
          <path d="M${x(1)+8},${y(14)-6} l24,-27 h98"/>
          <text x="${x(1)+36}" y="${y(14)-39}">${T('q = 1 · 首次覆盖','q = 1 · first overwrite')}</text>
        </g>
      </svg>
    </div>
    <div class="zlo-chart-key" aria-label="${T('曲线图例','Chart legend')}"><span><i class="zlo-safe-key"></i>${T('安全计划的待交付字节','Safe pending')}</span><span><i class="zlo-unsafe-key"></i>${T('前重计划的待交付字节','Front-loaded pending')}</span><span><i class="zlo-boundary-key"></i>${T('未读边界 B + 3q','Unread boundary B + 3q')}</span></div>
    <div class="zlo-comparison">
      ${['safe','unsafe'].map(kind => `<section class="zlo-plan zlo-plan-${kind}" data-plan="${kind}" aria-label="${kind === 'safe' ? T('安全教学计划','Safe teaching schedule') : T('前重教学计划','Front-loaded teaching schedule')}">
        <div class="zlo-plan-title"><span>${kind === 'safe' ? 'A' : 'B'}</span><h4>${kind === 'safe' ? T('逐步腾出空间','Make room gradually') : T('一开始就写很多','Write more up front')}</h4><b data-badge>${T('未开始','Not started')}</b></div>
        <p class="zlo-write-label">${T('每个符号对应的写入量','Bytes written for each symbol')}</p>
        <div class="zlo-schedule">${PLANS[kind].map((bytes, index) => `<span data-schedule="${index}">${bytes}</span>`).join('')}<small>${T('字节','bytes')}</small></div>
        <div class="zlo-memory" aria-label="${kind === 'safe' ? T('安全计划的32字节内存','32-byte memory for the safe schedule') : T('前重计划的32字节内存','32-byte memory for the front-loaded schedule')}">${Array.from({length:32}, (_, cell) => `<span class="zlo-memory-cell" data-cell="${cell}"><small>${cell}</small><b></b></span>`).join('')}</div>
        <div class="zlo-counts"><span>${T('待交付字节 pending','pending')} <b data-pending>2</b></span><span>${T('边界','boundary')} <b data-boundary>8</b></span><span>${T('最终','final')} <b data-final></b></span></div>
        <p class="zlo-plan-result" data-result></p>
      </section>`).join('')}
    </div>
    <div class="zlo-memory-key"><span><i class="zlo-output-key"></i>${T('已写输出','Written output')}</span><span><i class="zlo-symbol-key"></i>${T('未读符号','Unread symbols')}</span><span><i class="zlo-damage-key"></i>${T('曾被提前覆盖','Overwritten before reading')}</span></div>
    <p class="zlo-teaching-note" id="${id}-hint">${T('教学尺寸 B = 8，容量 32；两种计划均为人为构造，不是 zlib 漏洞。拖动滑块可回看任意前缀。','Teaching example: B = 8, capacity = 32. Both schedules are constructed examples, not zlib bugs. Scrub to inspect any prefix.')}</p>`;

  const range = host.controls.querySelector('input');
  const next = host.controls.querySelector('[data-next]');
  const counter = host.controls.querySelector('[data-q]');
  const safeLine = host.view.querySelector('[data-safe-line]');
  const unsafeLine = host.view.querySelector('[data-unsafe-line]');
  const cursor = host.view.querySelector('[data-cursor]');
  const safePoint = host.view.querySelector('[data-safe-point]');
  const unsafePoint = host.view.querySelector('[data-unsafe-point]');
  const boundaryPoint = host.view.querySelector('[data-boundary-point]');
  const breach = host.view.querySelector('[data-first-breach]');
  const desc = host.view.querySelector(`#${id}-chart-desc`);
  const panels = ['safe','unsafe'].map(kind => {
    const node = host.view.querySelector(`[data-plan="${kind}"]`);
    return {
      kind, node,
      badge: node.querySelector('[data-badge]'),
      pending: node.querySelector('[data-pending]'),
      boundary: node.querySelector('[data-boundary]'),
      final: node.querySelector('[data-final]'),
      result: node.querySelector('[data-result]'),
      cells: [...node.querySelectorAll('[data-cell]')],
      schedule: [...node.querySelectorAll('[data-schedule]')],
    };
  });

  function position(node, step, value) {
    node.setAttribute('cx', x(step));
    node.setAttribute('cy', y(value));
  }

  function render() {
    const safe = overlay('safe',q);
    const unsafe = overlay('unsafe',q);
    range.value = String(q);
    range.setAttribute('aria-valuetext', T(`已读取 ${q} 个符号，共 ${max} 个`, `${q} of ${max} symbols read`));
    counter.textContent = String(q);
    next.disabled = q === max;
    safeLine.setAttribute('points',points('safe',q));
    unsafeLine.setAttribute('points',points('unsafe',q));
    cursor.setAttribute('x1', x(q));
    cursor.setAttribute('x2', x(q));
    position(safePoint,q,safe.pending);
    position(unsafePoint,q,unsafe.pending);
    position(boundaryPoint,q,safe.unread);
    breach.setAttribute('visibility', q >= 1 ? 'visible' : 'hidden');
    host.classList.toggle('zl-error',q > 0);

    for (const panel of panels) {
      const state = panel.kind === 'safe' ? safe : unsafe;
      const damaged = new Set(state.corrupted);
      panel.node.classList.toggle('zlo-has-damage', damaged.size > 0);
      panel.badge.textContent = damaged.size ? T('已破坏','Damaged') : q === max ? T('完成','Complete') : q ? T('安全前缀','Safe prefix') : T('未开始','Not started');
      panel.pending.textContent = String(state.pending);
      panel.boundary.textContent = q === max ? T('无未读','none unread') : String(state.unread);
      panel.final.textContent = `${state.finalSize} / 32`;
      panel.result.textContent = damaged.size ? T(`q = 1 时首次覆盖；当前前缀累计损坏 ${damaged.size} 个字节。`, `First overwrite at q = 1. This prefix has damaged ${damaged.size} bytes in total.`) : q === max ? T('所有符号已读完，始终没有提前覆盖。','All symbols read, with no premature overwrite.') : T(`下一步先读符号 ${q} 的三字节，再写入 ${PLANS[panel.kind][q]} 字节。`, `Next: read symbol ${q}'s three bytes, then write ${PLANS[panel.kind][q]} bytes.`);
      panel.schedule.forEach((node,index) => {
        node.classList.toggle('zlo-step-done',index < q);
        node.classList.toggle('zlo-step-current',q > 0 && index === q - 1);
      });
      panel.cells.forEach((node,index) => {
        const stateName = damaged.has(index) ? 'damage' : index < state.pending ? 'output' : index >= state.unread && index < state.symbolEnd ? 'symbol' : 'free';
        node.dataset.state = stateName;
        const label = stateName === 'damage' ? '×' : stateName === 'symbol' ? `s${Math.floor((index-8)/3)}` : stateName === 'output' ? '·' : '';
        node.querySelector('b').textContent = label;
        const meanings = { damage:T('曾被提前覆盖','overwritten before reading'), output:T('已写输出','written output'), symbol:T('未读符号','unread symbol'), free:T('当前空闲','currently free') };
        node.title = T(`偏移 ${index}：${meanings[stateName]}`, `Offset ${index}: ${meanings[stateName]}`);
      });
    }
    desc.textContent = T(`已读 ${q} 个符号。安全计划的待交付字节数为 ${safe.pending}，前重计划为 ${unsafe.pending}。${q === max ? '符号全部读取完成。' : '未读边界为 ' + safe.unread + '。'}${q ? '前重计划在 q 等于 1 时已破坏未读符号；后来曲线回到边界下方也不能修复。' : '两种计划都还没有开始符号发射。'}`, `${q} symbols read. Safe pending is ${safe.pending}; front-loaded pending is ${unsafe.pending}. ${q === max ? 'All symbols have been read.' : 'The unread boundary is ' + safe.unread + '.'} ${q ? 'The front-loaded schedule damaged unread symbols at q equals 1. Returning below the boundary later cannot repair that damage.' : 'Neither schedule has started emitting symbols.'}`);
    host.status.textContent = q === 0 ? T('两种计划最终都放得下。向前一步，检查写入是否碰到未读符号。','Both final outputs fit. Step forward to see whether a write reaches unread symbols.') : q === 1 ? T('首次分歧：前重计划写到偏移 14，超过未读起点 11；最终只需 20 字节仍然无济于事。','First divergence: the front-loaded schedule writes up to offset 14, beyond unread offset 11. Its final size of 20 bytes cannot undo that overwrite.') : q === 2 ? T('前重计划又覆盖了偏移 14。图中保留首次破坏点，内存中累计记录已损坏的字节。','The front-loaded schedule also overwrites offset 14. The chart preserves the first breach; memory retains every damaged byte.') : T('“当前写入位置已在边界下方”不等于“此前没有破坏”。红色标记保留已经发生的覆盖。','Being below the boundary now does not mean earlier writes were safe. Rust markers preserve the damage already done.');
  }

  host.on(range,'input', () => { q = Number(range.value); render(); });
  host.on(next,'click', () => { q = Math.min(max,q + 1); render(); });
  host.on(host.controls.querySelector('[data-reset]'),'click', () => { q = 0; render(); });
  render();
}
