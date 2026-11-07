import mermaid from "https://cdn.jsdelivr.net/npm/mermaid@12.2.0/dist/mermaid.esm.min.mjs";

mermaid.initialize({startOnLoad: false, securityLevel: "loose", maxTextSize: 100000, theme: "neutral", flowchart: {useMaxWidth: false}});

const chinese = document.documentElement.lang.startsWith('zh');
const labelText = (english, translated) => chinese ? translated : english;

/* Make the same Mermaid diagrams readable at either overview or node scale. */
(() => {
  function enhance() {
    document.querySelectorAll('.diagram-canvas').forEach(diagram => {
      const svg = diagram.querySelector('svg, img');
      if (!svg || diagram.dataset.reader) return;
      const box = svg.tagName.toLowerCase() === 'svg' ? svg.viewBox.baseVal :
        {width: svg.naturalWidth, height: svg.naturalHeight};
      if (!box.width || !box.height) return;
      diagram.dataset.reader = 'ready';
      const frame = document.createElement('div');
      frame.className = 'diagram-reader';
      const tools = document.createElement('div');
      tools.className = 'diagram-tools';
      tools.setAttribute('role', 'group');
      tools.setAttribute('aria-label', labelText('Diagram zoom', '图形缩放'));
      const viewport = document.createElement('div');
      viewport.className = 'diagram-viewport';
      viewport.tabIndex = 0;
      viewport.setAttribute('aria-label', labelText('Scrollable diagram', '可滚动图形'));
      diagram.before(frame);
      frame.append(tools, viewport);
      viewport.append(diagram);
      const width = box.width, height = box.height;
      const label = document.createElement('output');
      let scale = 1;
      function zoom(value, fit = false) {
        const x = (viewport.scrollLeft + viewport.clientWidth / 2) / scale;
        const y = (viewport.scrollTop + viewport.clientHeight / 2) / scale;
        scale = Math.max(.025, Math.min(2, value));
        svg.style.width = `${width * scale}px`;
        svg.style.height = `${height * scale}px`;
        svg.setAttribute('width', width * scale);
        svg.setAttribute('height', height * scale);
        viewport.scrollLeft = fit ? 0 : x * scale - viewport.clientWidth / 2;
        viewport.scrollTop = fit ? 0 : y * scale - viewport.clientHeight / 2;
        label.textContent = `${Math.round(scale * 100)}%`;
      }
      for (const [text, title, action] of [
        ['−', labelText('Zoom out', '缩小'), () => zoom(scale / 1.35)],
        ['+', labelText('Zoom in', '放大'), () => zoom(scale * 1.35)],
        [labelText('Fit', '适应宽度'), labelText('Fit diagram to width', '使图形适应宽度'), () => zoom(Math.min(1, (viewport.clientWidth - 16) / width), true)],
        ['100%', labelText('Show full-size labels', '显示原始字号'), () => zoom(1, true)]
      ]) {
        const button = document.createElement('button');
        button.type = 'button'; button.textContent = text;
        button.setAttribute('aria-label', title); button.title = title;
        button.addEventListener('click', action); tools.append(button);
      }
      tools.append(label);
      zoom(Math.min(1, (viewport.clientWidth - 16) / width), true);
    });
  }
  let nextId = 0;
  async function render(source) {
    if (source.dataset.rendering) return;
    source.dataset.rendering = 'true';
    try {
      const {svg, bindFunctions} = await mermaid.render(`proof-diagram-${++nextId}`, source.textContent);
      const canvas = document.createElement('div');
      canvas.className = 'diagram-canvas';
      canvas.innerHTML = svg;
      source.replaceWith(canvas);
      bindFunctions?.(canvas);
      enhance();
    } catch (error) {
      source.dataset.error = 'true';
      const note = document.createElement('p');
      note.setAttribute('role', 'alert');
      note.textContent = labelText('Diagram could not be rendered. The source remains available below.', '图形无法渲染，下方仍保留源码。');
      source.before(note);
      console.error(error);
    }
  }
  function scan() {
    document.querySelectorAll('.diagram-source').forEach(render);
    document.querySelectorAll('.md-content img[src$=".svg"]').forEach(img => {
      if (img.closest('.diagram-canvas')) return;
      if (!img.complete) {
        if (!img.dataset.readerWatch) {
          img.dataset.readerWatch = 'true';
          img.addEventListener('load', scan, {once: true});
        }
        return;
      }
      if (!img.naturalWidth) return;
      const canvas = document.createElement('div');
      canvas.className = 'diagram-canvas';
      img.before(canvas);
      canvas.append(img);
    });
    enhance();
  }
  new MutationObserver(scan).observe(document.body, {childList: true, subtree: true});
  scan();
})();
