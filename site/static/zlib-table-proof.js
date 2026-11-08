// Teaching table only: this module does not execute the C or Lean translation.
export function mountTableProof(host) {
  const T = (zh, en) => host.lang === 'en' ? en : zh;
  host.classList.add('zl-table-proof');
  host.controls.innerHTML = `
    <button type="button" class="zl-tp-switch" role="switch" aria-checked="false" data-tp-toggle
      aria-label="${T('仅把子表项的符号值从 C 改成 D', 'Change only the subtable symbol value from C to D')}">
      <span class="zl-tp-switch-track" aria-hidden="true"><i></i></span>
      <span>${T('只改一个值：C → D', 'Change one value: C → D')}</span>
    </button>
    <button type="button" class="zl-quiet" data-tp-reset>${T('恢复原表', 'Restore table')}</button>
    <span class="zl-tp-controls-note">${T('索引、链接、码长和初始化状态都不变', 'Indices, links, code lengths and initialization stay unchanged')}</span>`;
  host.view.innerHTML = `
    <div class="zl-tp-input">
      <div><small>${T('固定输入 · 码的读取顺序', 'Fixed input · code bits in reading order')}</small><strong>1<span>→</span>1<span>→</span>0</strong></div>
      <div><small>${T('缓冲区数值 · 高位在左', 'Buffer value · most significant bit on the left')}</small><strong>0 1 1</strong></div>
      <span class="zl-tp-expect"><small>${T('编码规定的结果', 'Expected symbol')}</small><b>C</b></span>
    </div>
    <div class="zl-tp-path">
      <div><table class="zl-tp-root">
        <caption>${T('根表', 'Root table')} <span>${T('索引 3，范围 [0, 4)', 'Index 3, range [0, 4)')}</span></caption>
        <thead><tr><th scope="col">${T('低两位', 'Low two bits')}</th><th scope="col">${T('条目含义', 'Entry meaning')}</th></tr></thead>
        <tbody>
          <tr><td><code>00</code></td><td>A · ${T('消耗 1 位', 'consume 1 bit')}</td></tr>
          <tr><td><code>01</code></td><td>B · ${T('消耗 2 位', 'consume 2 bits')}</td></tr>
          <tr><td><code>10</code></td><td>A · ${T('消耗 1 位', 'consume 1 bit')}</td></tr>
          <tr class="zl-tp-reached"><td><code>11</code></td><td>${T('子表链接 · 先消耗 2 位', 'Subtable link · consume 2 bits first')} <span aria-hidden="true">↘</span></td></tr>
        </tbody>
      </table></div>
      <div><table class="zl-tp-sub">
        <caption>${T('子表', 'Subtable')} <span>${T('索引 0，范围 [0, 2)', 'Index 0, range [0, 2)')}</span></caption>
        <thead><tr><th scope="col">${T('下一位', 'Next bit')}</th><th scope="col">${T('符号值', 'Symbol value')}</th></tr></thead>
        <tbody>
          <tr class="zl-tp-reached zl-tp-editable"><td><code>0</code></td>
            <td><span class="zl-tp-value" data-tp-value role="img" aria-label="${T('实际符号值 C', 'Actual symbol value C')}">
              <span class="zl-tp-original" aria-hidden="true">C</span><span class="zl-tp-altered" aria-hidden="true">D</span>
            </span><span class="zl-tp-unchanged">${T('再消耗 1 位', 'consume 1 more bit')}</span></td>
          </tr>
          <tr><td><code>1</code></td><td>D</td></tr>
        </tbody>
      </table><p class="zl-tp-initialized">${T('两个槽位都已初始化', 'Both entries are initialized')}</p></div>
    </div>
    <div class="zl-tp-evidence" aria-label="${T('两组独立的教学条件', 'Two independent sets of teaching conditions')}">
      <section class="zl-tp-track zl-tp-access" aria-label="${T('本次访问条件', 'Conditions for this access')}">
        <div class="zl-tp-track-heading"><span class="zl-tp-indicator" aria-hidden="true">✓</span><strong>${T('本次访问条件', 'Conditions for this access')}</strong><span class="zl-tp-outcome">${T('仍满足', 'Still satisfied')}</span></div>
        <div class="zl-tp-rail" aria-hidden="true"><i></i><i></i><i></i></div>
        <p>${T('根索引 3 < 4，子表索引 0 < 2；链接有效，读取的槽位已初始化。', 'Root index 3 < 4; subtable index 0 < 2. The link is valid and both accessed entries are initialized.')}</p>
      </section>
      <section class="zl-tp-track zl-tp-meaning" aria-label="${T('与编码含义一致', 'Agreement with the code')}">
        <div class="zl-tp-track-heading"><span class="zl-tp-indicator" data-tp-mark aria-hidden="true">✓</span><strong>${T('与编码含义一致', 'Agreement with the code')}</strong><span class="zl-tp-outcome" data-tp-outcome></span></div>
        <div class="zl-tp-rail" aria-hidden="true"><i></i><i></i><i></i></div>
        <p>${T('110 应当解出 C，当前实际解出 ', '110 should decode to C. The actual result is ')}<b data-tp-result>C</b><span data-tp-comparison></span></p>
      </section>
    </div>
    <p class="zl-tp-footnote">${T('这里只对照两组教学条件，没有运行证明内核。', 'This compares teaching conditions; it does not run a proof kernel.')}</p>`;
  const toggle = host.controls.querySelector('[data-tp-toggle]');
  const reset = host.controls.querySelector('[data-tp-reset]');
  const value = host.view.querySelector('[data-tp-value]');
  const mark = host.view.querySelector('[data-tp-mark]');
  const outcome = host.view.querySelector('[data-tp-outcome]');
  const result = host.view.querySelector('[data-tp-result]');
  const comparison = host.view.querySelector('[data-tp-comparison]');
  let changed = false;
  function update() {
    host.dataset.tableChanged = String(changed);
    toggle.setAttribute('aria-checked', String(changed));
    value.setAttribute('aria-label', T('实际符号值 ', 'Actual symbol value ') + (changed ? 'D' : 'C'));
    mark.textContent = changed ? '×' : '✓';
    outcome.textContent = changed ? T('不一致', 'Does not agree') : T('一致', 'Agrees');
    result.textContent = changed ? 'D' : 'C';
    comparison.textContent = changed ? T('；与编码规定的 C 不同。', ', which differs from the required C.') : T('；二者相同。', ', as required.');
    host.status.textContent = changed
      ? T('只改了实际符号值。访问仍有界且已初始化，但输入 110 被解成 D，与编码含义不一致。', 'Only the symbol value changed. Accesses remain bounded and initialized, but 110 now decodes to D rather than C.')
      : T('原表把 110 解成 C。切换上方开关，观察哪一组条件会随符号值改变。', 'The original table decodes 110 to C. Toggle the value and see which conditions change.');
  }
  host.on(toggle, 'click', () => { changed = !changed; update(); });
  host.on(reset, 'click', () => { changed = false; update(); });
  update();
}
