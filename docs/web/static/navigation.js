(() => {
  const trigger = document.querySelector('[data-global-toc]');
  const dialog = document.getElementById('book-global-toc');
  if (!trigger || !dialog) return;
  const search = dialog.querySelector('[data-toc-search]');
  const entries = [...dialog.querySelectorAll('[data-toc-entry]')];
  const sections = [...dialog.querySelectorAll('[data-toc-section], [data-toc-part]')];
  const initialOpen = new Map(sections.map(section => [section, section.open]));
  trigger.addEventListener('click', () => {
    dialog.showModal();
    trigger.setAttribute('aria-expanded', 'true');
    // Keep the mobile keyboard closed until the reader chooses to search.
    dialog.querySelector('[data-toc-close]').focus({preventScroll: true});
    const active = dialog.querySelector('[aria-current="page"]');
    if (active) active.scrollIntoView({block: 'nearest'});
  });
  dialog.querySelector('[data-toc-close]').addEventListener('click', () => dialog.close());
  dialog.addEventListener('click', event => {
    if (event.target !== dialog) return;
    const r = dialog.getBoundingClientRect();
    if (event.clientX < r.left || event.clientX > r.right || event.clientY < r.top || event.clientY > r.bottom) dialog.close();
  });
  dialog.addEventListener('close', () => trigger.setAttribute('aria-expanded', 'false'));
  dialog.querySelectorAll('a').forEach(a => a.addEventListener('click', () => dialog.close()));
  search.addEventListener('input', () => {
    const query = search.value.trim().toLocaleLowerCase();
    const words = query.split(/\s+/).filter(Boolean);
    for (const entry of entries) {
      const heading = entry.closest('[data-toc-section]')?.querySelector('summary')?.textContent || '';
      const text = (entry.textContent + ' ' + heading + ' ' + (entry.dataset.tocKeywords || '')).toLocaleLowerCase();
      entry.hidden = !words.every(word => text.includes(word));
    }
    // Nested sections first, then their containing reading parts.
    for (const section of [...sections].reverse()) {
      section.hidden = query !== '' && !section.querySelector('[data-toc-entry]:not([hidden])');
      section.open = query ? !section.hidden : initialOpen.get(section);
    }
    dialog.querySelector('[data-toc-empty]').hidden = entries.some(entry => !entry.hidden);
  });
})();
