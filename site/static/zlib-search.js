import { search } from './zlib-models.mjs';

// A small candidate-chain illustration, not zlib's hash implementation.
// The host supplies persistent controls/view/status nodes and abortable listeners.
export function mountSearch(host) {
  const T = (zh, en) => host.lang === 'en' ? en : zh;
  host.classList.add('zls-demo');
  const fixture = search(2);
  let budget = 1;
  let candidate = 0;
  let compared = 0;
  let visited = 0;
  let best = null;
  let phase = 'ready';

  host.controls.innerHTML = `
    <label class="zls-budget">${T('最多检查', 'Search budget')}
      <input type="range" min="1" max="2" value="1" aria-label="${T('搜索预算', 'Search budget')}">
      <output class="zls-budget-value">${T('1 个候选', '1 candidate')}</output>
    </label>
    <button type="button" data-zls-next>${T('比较下一字节', 'Compare next byte')}</button>
    <button type="button" data-play>${T('连续比较', 'Play comparison')}</button>
    <button type="button" data-zls-reset class="zl-quiet">${T('重置', 'Reset')}</button>`;

  const currentText = fixture.text.slice(fixture.current, fixture.current + 8);
  const byteRow = (kind, text, start) => `<div class="zls-byte-row" data-zls-row="${kind}">
    ${[...text].map((char, i) => `<span class="zls-byte"><b>${char}</b><small>${start + i}</small><i aria-hidden="true"></i></span>`).join('')}
    </div>`;

  host.view.innerHTML = `
    <div class="zls-chain" aria-label="${T('候选链：head 指向位置4，再指向位置0', 'Candidate chain: head points to position 4, then position 0')}">
      <span class="zls-head">head</span><span class="zls-arrow" aria-hidden="true">→</span>
      <div class="zls-chain-nodes">
        ${fixture.candidates.map((item, i) => `<span class="zls-node" data-zls-node="${i}"><small>${T('候选位置', 'Candidate at')}</small><b>${item.position}</b></span>`).join('')}
        <span class="zls-node-link" aria-hidden="true">→</span>
        <i class="zls-chain-cursor" aria-hidden="true">↑</i>
      </div>
      <span class="zls-nil">→ NIL</span>
    </div>
    <div class="zls-comparison">
      <div class="zls-row-label"><span>${T('待处理输入', 'Input to process')}</span><code>${T(`当前位置 ${fixture.current}`, `Current position ${fixture.current}`)}</code></div>
      ${byteRow('current', currentText, fixture.current)}
      <div class="zls-equality" aria-hidden="true">${Array.from({length:8}, () => '<span>·</span>').join('')}</div>
      <div class="zls-row-label"><span>${T('候选字节', 'Candidate bytes')}</span><code class="zls-source-position"></code></div>
      ${byteRow('source', fixture.text.slice(fixture.candidates[0].position, fixture.candidates[0].position + 8), fixture.candidates[0].position)}
    </div>
    <div class="zls-facts">
      <div><small>${T('本候选匹配长度', 'Current match length')}</small><b data-zls-length>0</b></div>
      <div><small>${T('已检查候选', 'Candidates checked')}</small><b data-zls-visited>0 / 1</b></div>
      <div><small>${T('目前最佳', 'Best so far')}</small><b data-zls-best>${T('尚未确定', 'Not yet determined')}</b></div>
    </div>
    <p class="zls-footnote">${T('教学模型 · 用逻辑位置演示候选链，不复现实际哈希函数。位置 0 在此可用，真实 C 中它是 NIL 哨兵。', 'Teaching model · Logical positions illustrate the candidate chain, not the actual hash function. Position 0 is usable here; the real C implementation reserves it for NIL.')}</p>`;

  const range = host.controls.querySelector('input');
  const budgetValue = host.controls.querySelector('.zls-budget-value');
  const nextButton = host.controls.querySelector('[data-zls-next]');
  const playButton = host.controls.querySelector('[data-play]');
  const cursor = host.view.querySelector('.zls-chain-cursor');
  const sourcePosition = host.view.querySelector('.zls-source-position');
  const currentCells = [...host.view.querySelectorAll('[data-zls-row="current"] .zls-byte')];
  const sourceCells = [...host.view.querySelectorAll('[data-zls-row="source"] .zls-byte')];
  const equalities = [...host.view.querySelectorAll('.zls-equality span')];
  const nodes = [...host.view.querySelectorAll('[data-zls-node]')];
  const facts = {
    length: host.view.querySelector('[data-zls-length]'),
    visited: host.view.querySelector('[data-zls-visited]'),
    best: host.view.querySelector('[data-zls-best]'),
  };

  const stop = () => {
    clearInterval(host.timer);
    host.timer = null;
    playButton.textContent = T('连续比较', 'Play comparison');
  };

  const render = (announcement) => {
    const source = fixture.candidates[candidate];
    const sourceText = fixture.text.slice(source.position, source.position + 8);
    const done = phase === 'done';
    const matched = Math.min(compared, source.length);
    budgetValue.textContent = T(`${budget} 个候选`, `${budget} ${budget === 1 ? 'candidate' : 'candidates'}`);
    sourcePosition.textContent = T(`位置 ${source.position} · 距离 ${source.distance}`, `Position ${source.position} · distance ${source.distance}`);
    cursor.style.left = candidate === 0 ? '25%' : '75%';
    nodes.forEach((node, i) => {
      node.classList.toggle('is-current', i === candidate);
      node.classList.toggle('is-visited', i < visited);
      node.classList.toggle('is-unavailable', i >= budget);
      if (i === candidate) node.setAttribute('aria-current', 'step');
      else node.removeAttribute('aria-current');
    });
    currentCells.forEach((cell, i) => {
      const checked = i < compared;
      const same = currentText[i] === sourceText[i];
      const active = !done && phase !== 'candidate-done' && i === compared;
      for (const target of [cell, sourceCells[i]]) {
        target.classList.toggle('is-match', checked && same);
        target.classList.toggle('is-mismatch', checked && !same);
        target.classList.toggle('is-active', active);
      }
      sourceCells[i].querySelector('b').textContent = sourceText[i];
      sourceCells[i].querySelector('small').textContent = String(source.position + i);
      equalities[i].textContent = checked ? (same ? '=' : '≠') : '·';
      equalities[i].classList.toggle('is-mismatch', checked && !same);
    });
    facts.length.textContent = String(matched);
    facts.visited.textContent = `${visited} / ${budget}`;
    facts.best.textContent = best ? T(`${best.length} 字节 · 距离 ${best.distance}`, `${best.length} bytes · back ${best.distance}`) : T('尚未确定', 'Not yet determined');
    nextButton.textContent = phase === 'candidate-done' ? T('检查更早候选', 'Try earlier candidate') : done ? T('本轮完成', 'Search complete') : T('比较下一字节', 'Compare next byte');
    nextButton.disabled = done;
    playButton.disabled = done;
    if (announcement) host.status.textContent = announcement;
  };

  const advance = () => {
    if (phase === 'done') return;
    if (phase === 'candidate-done') {
      candidate++;
      compared = 0;
      phase = 'ready';
      render(T(`沿 prev 链移动到位置 ${fixture.candidates[candidate].position}；从第一个字节重新比较。`, `Follow prev to position ${fixture.candidates[candidate].position}; compare again from the first byte.`));
      return;
    }
    phase = 'comparing';
    const source = fixture.candidates[candidate];
    const index = compared++;
    const sourceChar = fixture.text[source.position + index];
    const targetChar = currentText[index];
    if (sourceChar !== targetChar || compared === currentText.length) {
      visited++;
      const length = sourceChar === targetChar ? compared : compared - 1;
      if (!best || length > best.length) best = {length, distance: source.distance};
      phase = visited >= budget ? 'done' : 'candidate-done';
      stop();
      render(T(
        `位置 ${source.position}：${sourceChar === targetChar ? '比较到输入末尾' : `“${sourceChar}”与“${targetChar}”不同`}，匹配长度 ${length}。${phase === 'done' ? `预算用完，目前最佳长度 ${best.length}。` : '还可以沿链检查一个更早候选。'}`,
        `Position ${source.position}: ${sourceChar === targetChar ? 'reached the end of the input' : `“${sourceChar}” differs from “${targetChar}”`}; match length ${length}. ${phase === 'done' ? `Budget exhausted. Best length: ${best.length}.` : 'One earlier candidate is still within the budget.'}`
      ));
    } else {
      render(T(`第 ${compared} 个字节相同：“${targetChar}”。继续向右比较。`, `Byte ${compared} matches: “${targetChar}”. Continue to the right.`));
    }
  };

  const reset = () => {
    stop(); candidate = 0; compared = 0; visited = 0; best = null; phase = 'ready';
    render(T(`head 定位到最近候选 4；最多检查 ${budget} 个候选。逐字节比较，遇到不同字节时停止。`, `head selects the most recent candidate at position 4. Budget: ${budget} ${budget === 1 ? 'candidate' : 'candidates'}. Compare byte by byte until a mismatch.`));
  };

  host.on(range, 'input', () => { budget = Number(range.value); reset(); });
  host.on(nextButton, 'click', () => { stop(); advance(); });
  host.on(playButton, 'click', () => {
    if (host.timer) { stop(); return; }
    if (phase === 'candidate-done') advance();
    playButton.textContent = T('暂停', 'Pause');
    host.timer = setInterval(advance, 440);
  });
  host.on(host.controls.querySelector('[data-zls-reset]'), 'click', reset);
  reset();
}
