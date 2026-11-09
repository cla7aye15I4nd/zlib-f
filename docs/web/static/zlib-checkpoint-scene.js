import {checkpointSnapshot, checkpointSteps} from './zlib-checkpoint-model.mjs';

// Each transition is a caller rebinding or one completed public operation.
export function mountCheckpoint(host) {
  const T = host.t;
  let action = 'continue', step = 0, animation;
  const actions = [
    ['continue', T('继续原消息', 'Continue this message')],
    ['reset', T('换一条消息', 'Start another message')],
    ['copy', T('保存两条后续路径', 'Save two continuations')]
  ];
  host.controls.innerHTML = `<div class="zcp-choices" role="group" aria-label="${T('应用接下来要做什么', 'What the application needs next')}">${actions.map(([key, label]) => `<button type="button" data-zcp-action="${key}" aria-pressed="${key === action}">${label}</button>`).join('')}</div><div class="zcp-controls"><button type="button" data-zcp-back>${T('上一步', 'Back')}</button><button type="button" data-zcp-next></button><button type="button" data-zcp-restart class="zl-quiet">${T('重新演示', 'Restart scene')}</button></div>`;
  host.view.innerHTML = `<div class="zcp-scene">
    <p class="zcp-purpose">${T('应用已经拿到 ABAB。要么取回同一消息的其余部分，要么换消息，要么从这里保留两条执行路径。每一步都显示操作返回后的状态。', 'The application has ABAB. It can collect the rest, start another message, or keep two paths from this point. Each step shows the state after an operation returns.')}</p>
    <div class="zcp-heading"><strong data-zcp-title></strong><span data-zcp-count></span></div>
    <section class="zcp-caller"><h4>${T('应用拥有的字节 · 库只借用', 'Application-owned bytes · borrowed by the codec')}</h4>
      <div class="zcp-caller-grid"><div class="zcp-byte-card"><span>${T('已交付的原消息前缀', 'Delivered original prefix')}</span><div class="zcp-bytes" data-zcp-prefix></div><small>${T('Reset 与 End 都不抹掉它', 'Reset and End do not erase it')}</small></div>
      <div class="zcp-byte-card"><span data-zcp-input-title></span><code data-zcp-input></code><small data-zcp-input-note></small></div>
      <div class="zcp-byte-card" data-zcp-outa-card><span>${T('新输出区 A · 四个位置', 'New output A · four positions')}</span><div class="zcp-bytes" data-zcp-outputa></div><small data-zcp-outputa-note></small></div>
      <div class="zcp-byte-card" data-zcp-outb-card><span>${T('新输出区 B · 四个位置', 'New output B · four positions')}</span><div class="zcp-bytes" data-zcp-outputb></div><small data-zcp-outputb-note></small></div></div>
    </section>
    <div class="zcp-borrow-label" data-zcp-borrow></div>
    <div class="zcp-tasks" data-zcp-tasks></div>
    <p class="zcp-argument" data-zcp-explanation></p>
    <p class="zcp-code-help">${T('代码把上面的任务记录叫作 a、b，新输出区叫作 tail_a、tail_b，新消息输入叫作 fresh_cdcd。记录中的 next_in／next_out 选择输入／输出位置，avail_in／avail_out 计数本轮仍可读取／写入的字节。', 'In the code, a and b are the task records above; tail_a and tail_b are new output regions; fresh_cdcd is the new message input. Within a record, next_in/next_out select input/output positions and avail_in/avail_out count the bytes still readable/writable in this call.')}</p>
    <pre class="zcp-call"><code class="language-c syntax-highlight" data-zcp-code></code></pre>
  </div>`;
  const q = selector => host.view.querySelector(selector);
  const next = host.controls.querySelector('[data-zcp-next]');
  const back = host.controls.querySelector('[data-zcp-back]');
  const cells = (text, empty = false) => Array.from({length: 4}, (_, i) => `<b class="${text[i] ? 'zcp-written' : 'zcp-empty'}">${text[i] || (empty ? '·' : '—')}</b>`).join('');
  const names = {
    continue: [T('同一个检查点', 'The same checkpoint'), T('绑定新的输出区', 'Bind another output region'), T('原消息完成', 'The original message completes')],
    reset: [T('同一个检查点', 'The same checkpoint'), T('清除旧任务的执行进度', 'Clear the old task’s progress'), T('绑定一份新的完整编码', 'Bind a new complete encoding'), T('新消息完成', 'The new message completes')],
    copy: [T('同一个检查点', 'The same checkpoint'), T('复制私有状态，借用指针仍相同', 'Copy private state; borrowed pointers still match'), T('分别绑定两个输出区', 'Bind separate output regions'), T('先完成 A', 'Complete A first'), T('结束 A，B 仍能继续', 'End A; B can still continue'), T('再完成 B', 'Complete B next'), T('两份私有存储都已释放', 'Both decoders’ private storage has been released')]
  };
  const nextLabels = {
    continue: [T('绑定输出区 A', 'Bind output A'), T('调用 inflate 继续', 'Call inflate to continue')],
    reset: [T('调用 inflateReset', 'Call inflateReset'), T('绑定新编码和输出区', 'Bind new encoding and output'), T('解码新消息', 'Decode the new message')],
    copy: [T('调用 inflateCopy', 'Call inflateCopy'), T('绑定各自的输出区', 'Bind each output region'), T('调用 inflate(A)', 'Call inflate(A)'), T('调用 inflateEnd(A)', 'Call inflateEnd(A)'), T('调用 inflate(B)', 'Call inflate(B)'), T('调用 inflateEnd(B)', 'Call inflateEnd(B)')]
  };
  const color = code => code.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/\b(?:inflate(?:Reset|Copy|End)?|Z_[A-Z_]+|[0-9]+)\b/g, token => `<span class="${token.startsWith('inflate') ? 'tok-nf' : token.startsWith('Z_') ? 'tok-no' : 'tok-mi'}">${token}</span>`);
  const initial = T('A 保存了未完成匹配，还能产生四字节 ABAB。私有窗口保存已经交付的 ABAB。原输出区已经写满，必须先提供新的可写范围。', 'A keeps an unfinished match that can produce four more bytes, ABAB. Its private window keeps the delivered ABAB. The original destination is full, so continuation first needs another writable range.');
  const explanations = {
    continue: [initial,
      T('应用只改写任务记录中的输出绑定。未完成匹配、已保留窗口和输入位都不变；新输出区仍为空。', 'The application changes only the output binding in its task record. The unfinished match, retained window and held input bit stay intact. The new destination is still empty.'),
      T('一次继续调用写出剩余 ABAB，然后读到结束标记。原消息的累计输出从四变为八。私有状态仍存在，供查询、Reset 或 End 使用。', 'One continuation writes the remaining ABAB and reads the end marker. Total output for the original task rises from four to eight. Private state remains available for queries, Reset or End.')],
    reset: [initial,
      T('普通 Reset 清除匹配、暂存位和有效窗口范围，把累计输出归零。窗口分配可以保留，但旧 ABAB 不再是新消息的有效来源。调用者输入、输出绑定没有被移动。', 'Ordinary Reset clears the unfinished instruction, held bits and valid history, and resets total output. The window allocation can remain, but old ABAB is no longer a valid source for the new message. Caller input and output bindings have not moved.'),
      T('丢弃执行进度后，不能把旧流中间的后缀当成新消息。这里改为完整裸编码 73 76 71 76 01 00，它表示 CDCD，再绑定独立的四字节输出区。', 'After discarding progress, the middle of the old encoding cannot serve as a fresh message. Bind the complete raw encoding 73 76 71 76 01 00, representing CDCD, and a separate four-byte destination.'),
      T('新任务写出 CDCD，累计输出为四。原来交付的 ABAB 仍在应用的旧缓冲区里；它不属于这条新消息。物理窗口被复用，有效历史现在来自 CDCD。', 'The new task delivers CDCD and its total output is four. The old ABAB remains in the application’s earlier buffer; it is not part of this new message. The physical window is reused, with valid history now coming from CDCD.')],
    copy: [initial,
      T('成功 Copy 为 B 取得独立状态和窗口，并保存同一条未完成匹配。调用者指针按值复制：A、B 此时仍指向已经写满的同一输出区。只读输入可以共享，写输出前要各自重新绑定。', 'Successful Copy obtains a distinct state and window for B and preserves the same unfinished match. Caller pointers are copied by value: A and B still point to the same full output region. Read-only input can be shared; independent writes need separate output bindings.'),
      T('应用分别给 A、B 绑定四个可写位置。两份私有匹配仍各剩四字节；重新绑定不会执行解码。', 'The application gives A and B separate four-byte writable ranges. Each private match still has four bytes left. Rebinding performs no decoding.'),
      T('A 先写出剩余 ABAB。B 的私有匹配和窗口没有改变，所以它仍停在相同检查点。', 'A writes the remaining ABAB first. B’s private match and window do not change, so B stays at the checkpoint.'),
      T('End 只释放 A 拥有的状态和窗口。应用的两个输出区以及 B 的私有状态仍存在。B 不能依赖 A 的私有内存，这正是复制时修复内部指针的原因。', 'End releases only A’s state and window. Application output regions and B’s private state remain. B must not depend on A’s private memory; this is why Copy repairs internal pointers.'),
      T('A 已经结束，B 仍能独立写出剩余 ABAB。两条路径各得到八字节原消息：应用保存的共同前缀，加上各自的四字节后缀。', 'After A has ended, B independently writes its remaining ABAB. Each path has the eight-byte original message: the application’s saved prefix plus its own four-byte suffix.'),
      T('再 End B，释放它自己的状态和窗口。应用保存的前缀和两个后缀都保留；释放私有存储不交付或删除调用者字节。', 'End B releases its own state and window. The saved prefix and both suffixes remain with the application. Releasing private storage neither delivers nor deletes caller bytes.')]
  };
  const codes = {
    continue: ['a.avail_out == 0;', 'a.next_out = tail_a;\na.avail_out = 4;', 'inflate(&a, Z_NO_FLUSH);'],
    reset: ['a.avail_out == 0;', 'inflateReset(&a);', 'a.next_in = fresh_cdcd; a.avail_in = 6;\na.next_out = tail_a;    a.avail_out = 4;', 'inflate(&a, Z_NO_FLUSH);'],
    copy: ['a.avail_out == 0;', 'inflateCopy(&b, &a);', 'a.next_out = tail_a; a.avail_out = 4;\nb.next_out = tail_b; b.avail_out = 4;', 'inflate(&a, Z_NO_FLUSH);', 'inflateEnd(&a);', 'inflate(&b, Z_NO_FLUSH);', 'inflateEnd(&b);']
  };
  function stateCard(stream) {
    const id = stream.id, resetBeforeNew = action === 'reset' && step >= 1 && step < 3;
    const live = stream.live;
    const binding = stream.binding === 'prefix' ? T('旧输出末端 · 0 字节可写', 'Old output end · 0 writable bytes') : `${T('输出区', 'Output')} ${id} · ${stream.mode === 'DONE' ? '0' : '4'} ${T('字节可写', 'writable bytes')}`;
    const purpose = stream.mode === 'MATCH' ? T('继续同一条匹配', 'Continue the same match') : stream.mode === 'HEAD' ? T('等待新消息开头', 'Await a new message') : T('编码流已结束', 'The encoded stream has ended');
    const physical = resetBeforeNew ? 'ABAB' : stream.validHistory;
    return `<section class="zcp-task ${live ? '' : 'zcp-ended'}"><div class="zcp-record"><h4>${T('应用的任务记录', 'Application task record')} ${id}</h4><p>${live ? binding : T('状态链接已清空', 'State link cleared')}</p><small>${T('本任务累计输出', 'Task total output')}: <b>${stream.totalOut}</b></small></div>
      <div class="zcp-owner-arrow" aria-hidden="true">${live ? '↓' : '×'}</div>
      <div class="zcp-private"><h4>${live ? T('库拥有的私有对象', 'Private objects owned by the codec') : T('私有对象已释放', 'Private objects released')}</h4>
        <div class="zcp-private-grid"><div class="zcp-object"><strong>${T('状态', 'State')} ${id}</strong><p>${live ? purpose : T('已释放', 'Released')}</p><code>${live ? stream.mode : '—'}</code><small>${live && stream.remaining !== null ? T(`还可复制 ${stream.remaining} 字节`, `${stream.remaining} match bytes remain`) : live ? T('没有待完成匹配', 'No unfinished match') : T('不再访问', 'No further access')}</small><small>${live ? T(`暂存输入位：${stream.heldBits}`, `Held input bits: ${stream.heldBits}`) : ''}</small></div>
        <div class="zcp-object"><strong>${T('窗口', 'Window')} ${id}</strong><p>${live ? T('独立分配的存储', 'Distinct allocated storage') : T('已释放', 'Released')}</p><code class="${resetBeforeNew ? 'zcp-stale' : ''}">${live ? physical || '—' : '—'}</code><small>${live ? T(`有效历史：${stream.validHistory.length} 字节`, `Valid history: ${stream.validHistory.length} bytes`) : T('不再访问', 'No further access')}</small>${resetBeforeNew ? `<small>${T('旧字节仍可存在，但不可回引', 'Old contents can remain, but cannot be referenced')}</small>` : ''}</div></div>
      </div></section>`;
  }
  function render(animate = false) {
    animation?.cancel();
    const state = checkpointSnapshot(action, step);
    host.controls.querySelectorAll('[data-zcp-action]').forEach(node => node.setAttribute('aria-pressed', String(node.dataset.zcpAction === action)));
    q('[data-zcp-title]').textContent = names[action][step];
    q('[data-zcp-count]').textContent = `${step + 1} / ${checkpointSteps[action] + 1}`;
    q('[data-zcp-prefix]').innerHTML = cells(state.prefix);
    q('[data-zcp-outputa]').innerHTML = cells(state.outputA, true);
    q('[data-zcp-outputb]').innerHTML = cells(state.outputB, true);
    q('[data-zcp-outa-card]').classList.toggle('zcp-bound', state.a.binding === 'outputA');
    q('[data-zcp-outb-card]').hidden = action !== 'copy';
    q('[data-zcp-outb-card]').classList.toggle('zcp-bound', state.b?.binding === 'outputB');
    q('[data-zcp-outputa-note]').textContent = state.a.binding === 'outputA' ? T('任务记录 A 指向这个区域', 'Task record A points here') : T('尚未绑定', 'Not bound yet');
    q('[data-zcp-outputb-note]').textContent = state.b?.binding === 'outputB' ? T('任务记录 B 指向这个区域', 'Task record B points here') : T('尚未绑定', 'Not bound yet');
    q('[data-zcp-input-title]').textContent = state.inputKind === 'fresh' ? T('新消息的完整压缩输入', 'Complete compressed input for a new message') : T('原消息的最后一个压缩字节', 'The original message’s last compressed byte');
    q('[data-zcp-input]').textContent = state.inputKind === 'fresh' ? '73 76 71 76 01 00' : '00';
    const pendingReaders = [state.a, state.b].filter(stream => stream?.live && stream.mode === 'MATCH').map(stream => stream.id);
    const stillSaved = pendingReaders.length > 0;
    q('[data-zcp-input-note]').textContent = state.inputKind === 'fresh'
      ? (state.a.input === 'empty' ? T('六字节已全部取入；输入存储仍归应用所有', 'All six bytes were taken; input storage remains application-owned') : T('完整编码表示 CDCD', 'The complete encoding represents CDCD'))
      : stillSaved ? T(`任务 ${pendingReaders.join('、')} 尚未取入此字节，各自还暂存一位`, `Task${pendingReaders.length > 1 ? 's' : ''} ${pendingReaders.join(' and ')} ${pendingReaders.length > 1 ? 'have' : 'has'} not taken this byte; each holds one bit`)
      : state.a.mode === 'HEAD' ? T('旧输入绑定仍在这里；它不是完整的新编码', 'The old input binding stays here; this is not a complete new encoding')
      : T('此字节已取入；应用仍拥有原输入存储', 'This byte has been taken; the application still owns its input storage');
    const allEnded = !state.a.live && (!state.b || !state.b.live);
    const borrows = allEnded ? T('两个状态链接均已清空 ↓ 上方应用字节全部保留', 'Both state links are cleared ↓ all application bytes above remain') : state.copiedAliases ? T('A、B 借用同一旧输出末端 ↓ 重新绑定前不能独立写出', 'A and B borrow the same old output end ↓ rebind before independent writes') : action === 'copy' && step >= 2 ? T('两个记录分别借用输出区 A、B ↓ 只读输入可以共享', 'The records borrow separate outputs A and B ↓ read-only input can be shared') : T('任务记录借用上方字节区域 ↓ 私有状态另行拥有', 'The task record borrows the byte regions above ↓ private state has separate ownership');
    q('[data-zcp-borrow]').textContent = borrows;
    q('[data-zcp-borrow]').classList.toggle('zcp-alias', state.copiedAliases);
    q('[data-zcp-tasks]').innerHTML = stateCard(state.a) + (state.b ? stateCard(state.b) : '');
    q('[data-zcp-explanation]').textContent = explanations[action][step];
    q('[data-zcp-code]').innerHTML = color(codes[action][step]);
    next.textContent = nextLabels[action][step] || T('本条路径完成', 'This path is complete');
    next.disabled = step === checkpointSteps[action]; back.disabled = step === 0;
    host.status.textContent = names[action][step] + T('。 ', '. ') + explanations[action][step];
    if (animate && !globalThis.matchMedia?.('(prefers-reduced-motion: reduce)').matches) {
      const target = q(step === 1 ? '[data-zcp-tasks]' : '[data-zcp-explanation]');
      if (target.animate) animation = target.animate([{opacity: .4, transform: 'translateY(5px)'}, {opacity: 1, transform: 'translateY(0)'}], {duration: 260, easing: 'ease-out'});
    }
  }
  host.controls.querySelectorAll('[data-zcp-action]').forEach(node => host.on(node, 'click', () => {action = node.dataset.zcpAction; step = 0; render();}));
  host.on(next, 'click', () => {if (step < checkpointSteps[action]) {step++; render(true);}});
  host.on(back, 'click', () => {if (step > 0) {step--; render();}});
  host.on(host.controls.querySelector('[data-zcp-restart]'), 'click', () => {step = 0; render();});
  host.abort.signal.addEventListener('abort', () => animation?.cancel(), {once: true});
  render();
}
