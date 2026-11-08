document.querySelectorAll('[data-topology]').forEach(map => {
  const nodes = [...map.querySelectorAll('[data-map-node]')];
  const edges = [...map.querySelectorAll('.bk-map-edge')];
  const details = map.querySelector('[data-map-details]');
  const play = map.querySelector('[data-map-play]');
  const progress = map.querySelector('[data-map-progress]');
  const zh = document.documentElement.lang === 'zh';
  const reducedMotion = matchMedia('(prefers-reduced-motion: reduce)');
  const steps = ['interfaces', 'matching', 'huffman', 'output', 'decoding', 'interfaces'];
  const captions = zh ? ['应用交出原始输入', '重复片段变成字面量与匹配', '为符号构造编码', '把编码写成压缩流', '读取压缩流并恢复字节', '应用接收恢复后的字节'] : ['The application supplies input', 'Repetition becomes literals and matches', 'Build codes for the symbols', 'Write codes into a compressed stream', 'Read the stream and recover bytes', 'The application receives the recovered bytes'];
  let timer = null;
  let phase = 0;
  let selected = '';
  function select(key) {
    if (!nodes.some(node => node.dataset.mapNode === key)) return;
    if (selected !== key) {
      details.replaceChildren(map.querySelector(`[data-map-detail="${key}"]`).content.cloneNode(true));
      selected = key;
    }
    nodes.forEach(node => node.setAttribute('aria-pressed', String(node.dataset.mapNode === key)));
    edges.forEach(edge => {
      const connected = edge.dataset.from === key || edge.dataset.to === key;
      edge.classList.toggle('is-connected', connected);
      edge.classList.toggle('is-muted', !connected);
    });
  }
  function stop() {
    clearTimeout(timer);
    timer = null;
    play.setAttribute('aria-pressed', 'false');
    play.textContent = play.dataset.playLabel;
    edges.forEach(edge => edge.classList.remove('is-travelling'));
    progress.textContent = '';
  }
  function tick() {
    select(steps[phase]);
    progress.textContent = `${phase + 1} / ${steps.length} · ${captions[phase]}`;
    edges.forEach(edge => edge.classList.toggle('is-travelling', !reducedMotion.matches && edge.dataset.from === steps[phase] && edge.dataset.to === steps[phase + 1]));
    timer = setTimeout(() => {
      if (++phase < steps.length) tick();
      else stop();
    }, 3000);
  }
  play.setAttribute('aria-pressed', 'false');
  play.addEventListener('click', () => {
    if (timer) { stop(); return; }
    phase = 0;
    play.setAttribute('aria-pressed', 'true');
    play.textContent = play.dataset.stopLabel;
    tick();
  });
  nodes.forEach(node => {
    const explore = () => { stop(); select(node.dataset.mapNode); };
    node.addEventListener('pointerenter', event => { if (event.pointerType !== 'touch') explore(); });
    node.addEventListener('focus', explore);
    node.addEventListener('click', explore);
  });
  function layout(value) {
    map.dataset.layout = value;
    map.querySelectorAll('[data-map-view]').forEach(button => button.setAttribute('aria-pressed', String(button.dataset.mapView === value)));
  }
  map.querySelectorAll('[data-map-view]').forEach(button => button.addEventListener('click', () => layout(button.dataset.mapView)));
  layout(matchMedia('(max-width: 700px)').matches ? 'list' : 'graph');
  select(new URLSearchParams(location.search).get('topic') || 'interfaces');
  if (!selected) select('interfaces');
  document.querySelectorAll('[data-language]').forEach(link => link.addEventListener('click', () => {
    const target = new URL(link.href);
    target.searchParams.set('topic', selected);
    target.hash = location.hash;
    link.href = target.href;
  }));
  document.addEventListener('visibilitychange', () => { if (document.hidden) stop(); });
});
