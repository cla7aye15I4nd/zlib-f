const {menuGeometry, nextEnabled, matchOption} = await import('./select-model.mjs' + new URL(import.meta.url).search);

const controls = new Map();
let serial = 0, opened = null;

function enhance(select) {
  if (controls.has(select) || select.multiple || select.size > 1 || select.hidden) return;
  const id = `theme-select-${++serial}`;
  const optionLabel = option => option.label || option.text || option.textContent || '';
  const groupLabel = group => group.label || group.getAttribute('label') || '';
  const labels = [...select.labels];
  const wrapper = document.createElement('span');
  wrapper.className = 'theme-select';
  const button = document.createElement('button');
  button.type = 'button'; button.className = 'theme-select-trigger'; button.id = id;
  button.setAttribute('role', 'combobox'); button.setAttribute('aria-haspopup', 'listbox');
  button.setAttribute('aria-expanded', 'false'); button.setAttribute('aria-controls', `${id}-menu`);
  button.innerHTML = '<span></span><svg viewBox="0 0 12 8" aria-hidden="true"><path d="M1 1L6 6L11 1"/></svg>';
  if (select.getAttribute('aria-label')) button.setAttribute('aria-label', select.getAttribute('aria-label'));
  else if (select.getAttribute('aria-labelledby')) button.setAttribute('aria-labelledby', select.getAttribute('aria-labelledby'));
  else if (labels.length) {
    const ids = labels.map((label, index) => {
      // A separate text node avoids including the selected value in the field name.
      const name = document.createElement('span'); name.id = `${id}-label-${index}`;
      const text = [...label.childNodes].filter(node => node.nodeType === Node.TEXT_NODE).map(node => node.textContent).join(' ').trim();
      name.textContent = text;
      label.prepend(name);
      for (const node of [...label.childNodes]) if (node.nodeType === Node.TEXT_NODE) node.remove();
      return name.id;
    });
    button.setAttribute('aria-labelledby', ids.join(' '));
  }
  for (const name of ['aria-describedby', 'title']) if (select.hasAttribute(name)) button.setAttribute(name, select.getAttribute(name));
  const menu = document.createElement('div');
  menu.className = 'theme-select-menu'; menu.id = `${id}-menu`; menu.hidden = true;
  menu.setAttribute('role', 'listbox');
  for (const name of ['aria-label', 'aria-labelledby']) if (button.hasAttribute(name)) menu.setAttribute(name, button.getAttribute(name));
  select.before(wrapper); wrapper.append(select, button); document.body.append(menu);
  let active = select.selectedIndex, signature = '', rows = [], options = [], typeahead = '', lastTyped = 0;
  const abort = new AbortController(), on = (node, event, fn) => node.addEventListener(event, fn, {signal: abort.signal});

  function refresh() {
    options = [...select.options].map(option => ({label: optionLabel(option), disabled: option.disabled || !!option.parentElement.disabled}));
    const key = JSON.stringify([...select.options].map(option => [optionLabel(option), option.value, option.disabled, groupLabel(option.parentElement), option.parentElement.disabled]));
    if (key !== signature) {
      signature = key; menu.replaceChildren(); rows = []; let group = null;
      [...select.options].forEach((option, index) => {
        if (option.parentElement.tagName === 'OPTGROUP' && group !== option.parentElement) {
          group = option.parentElement;
          const heading = document.createElement('div'); heading.className = 'theme-select-group'; heading.textContent = groupLabel(group);
          heading.setAttribute('role', 'presentation'); menu.append(heading);
        }
        const row = document.createElement('div'); row.className = 'theme-select-option'; row.id = `${id}-option-${index}`;
        row.setAttribute('role', 'option'); row.dataset.index = index; row.textContent = optionLabel(option);
        row.setAttribute('aria-disabled', String(options[index].disabled)); menu.append(row); rows.push(row);
      });
    }
    const selected = select.options[select.selectedIndex];
    const text = selected ? optionLabel(selected) : '';
    if (button.firstElementChild.textContent !== text) button.firstElementChild.textContent = text;
    button.disabled = select.disabled || !options.length;
    rows.forEach((row, index) => row.setAttribute('aria-selected', String(index === select.selectedIndex)));
    if (select.disabled && opened === control) close();
  }
  function highlight(index) {
    if (index < 0 || index >= options.length || options[index].disabled) return;
    active = index;
    rows.forEach((row, i) => row.classList.toggle('is-active', i === active));
    button.setAttribute('aria-activedescendant', rows[active].id);
    rows[active].scrollIntoView({block: 'nearest'});
  }
  function position() {
    const rect = button.getBoundingClientRect();
    const width = document.documentElement.clientWidth || innerWidth;
    if (!button.isConnected || rect.bottom < 0 || rect.top > innerHeight) return close();
    // Set width before measuring height, since long labels wrap in the menu.
    menu.style.width = `${Math.min(Math.max(rect.width, 180), width - 24)}px`;
    const layout = menuGeometry(rect, width, innerHeight, menu.scrollHeight);
    Object.assign(menu.style, {left: `${layout.left}px`, top: `${layout.top}px`, width: `${layout.width}px`, maxHeight: `${layout.height}px`});
  }
  function open() {
    if (button.disabled) return;
    opened?.close(); refresh(); opened = control;
    menu.hidden = false; button.setAttribute('aria-expanded', 'true'); button.focus({preventScroll: true}); position();
    highlight(select.selectedIndex >= 0 && !options[select.selectedIndex]?.disabled ? select.selectedIndex : nextEnabled(options, -1, 1));
  }
  function close() {
    menu.hidden = true; button.setAttribute('aria-expanded', 'false'); button.removeAttribute('aria-activedescendant');
    if (opened === control) opened = null;
    typeahead = '';
  }
  function choose(index, focus = true) {
    if (!options[index] || options[index].disabled) return;
    const changed = select.selectedIndex !== index;
    select.selectedIndex = index; refresh(); close();
    if (focus) button.focus({preventScroll: true});
    if (changed) {
      select.dispatchEvent(new Event('input', {bubbles: true}));
      select.dispatchEvent(new Event('change', {bubbles: true}));
    }
  }
  const control = {refresh, close, position, wrapper, menu, button, destroy() {
    close(); abort.abort(); menu.remove(); wrapper.remove();
    for (const [key, original] of patched) {if (original) Object.defineProperty(select, key, original); else delete select[key];}
    select.classList.remove('theme-select-native'); controls.delete(select);
  }};
  const patched = [];
  // Reset buttons and graph selection set native values without emitting change.
  for (const key of ['value', 'selectedIndex', 'disabled']) {
    const original = Object.getOwnPropertyDescriptor(select, key);
    const descriptor = original || Object.getOwnPropertyDescriptor(HTMLSelectElement.prototype, key);
    if (descriptor?.get && descriptor?.set && descriptor.configurable !== false) {
      Object.defineProperty(select, key, {configurable: true, get() {return descriptor.get.call(this);}, set(value) {descriptor.set.call(this, value); refresh();}});
      patched.push([key, original]);
    }
  }
  on(button, 'click', () => opened === control ? close() : open());
  on(button, 'keydown', event => {
    const isOpen = opened === control, key = event.key;
    if (key === 'Escape') {if (isOpen) {event.preventDefault(); close();} return;}
    if (key === 'Tab') {if (isOpen) choose(active, false); return;}
    if (['ArrowDown', 'ArrowUp', 'Home', 'End', 'Enter', ' '].includes(key)) {
      event.preventDefault();
      if (!isOpen) {open(); if (key === 'Home' || key === 'End') highlight(nextEnabled(options, key === 'Home' ? -1 : options.length, key === 'Home' ? 1 : -1)); return;}
      if (key === 'Enter' || key === ' ') choose(active);
      else highlight(nextEnabled(options, key === 'Home' ? -1 : key === 'End' ? options.length : active, key === 'ArrowUp' || key === 'End' ? -1 : 1));
    } else if (key.length === 1 && !event.ctrlKey && !event.metaKey && !event.altKey) {
      event.preventDefault(); refresh();
      const now = Date.now(); typeahead = now - lastTyped < 700 ? typeahead + key : key; lastTyped = now;
      const query = [...typeahead].every(letter => letter === key) ? key : typeahead;
      const index = matchOption(options, query, (isOpen ? active : select.selectedIndex) - (query.length > 1 ? 1 : 0));
      if (index >= 0) {if (isOpen) highlight(index); else {const typed = typeahead; choose(index); typeahead = typed;}}
    }
  });
  on(menu, 'pointerdown', event => event.preventDefault());
  on(menu, 'pointermove', event => {const row = event.target.closest('[data-index]'); if (row) highlight(Number(row.dataset.index));});
  on(menu, 'click', event => {const row = event.target.closest('[data-index]'); if (row) choose(Number(row.dataset.index));});
  on(select, 'change', refresh);
  for (const label of labels) on(label, 'click', event => {
    if (event.target === label || event.target.id?.startsWith(`${id}-label-`)) {event.preventDefault(); button.focus();}
  });
  controls.set(select, control); refresh(); select.classList.add('theme-select-native');
}

function scan(node) {
  if (node.nodeType !== Node.ELEMENT_NODE && node !== document) return;
  if (node.matches?.('select')) enhance(node);
  node.querySelectorAll('select').forEach(enhance);
}
scan(document);
new MutationObserver(records => {
  for (const record of records) {
    for (const node of record.addedNodes) scan(node);
    const select = controls.has(record.target) ? record.target : record.target.closest?.('select');
    if (select) controls.get(select)?.refresh();
  }
  for (const [select, control] of controls) if (!select.isConnected) control.destroy();
}).observe(document.body, {subtree: true, childList: true, attributes: true, attributeFilter: ['disabled', 'selected', 'label', 'value']});
document.addEventListener('pointerdown', event => {
  if (opened && !opened.wrapper.contains(event.target) && !opened.menu.contains(event.target)) opened.close();
});
document.addEventListener('focusin', event => {if (opened && event.target !== opened.button) opened.close();});
document.addEventListener('reset', () => queueMicrotask(() => {for (const control of controls.values()) control.refresh();}));
window.addEventListener('resize', () => opened?.position());
window.addEventListener('scroll', () => opened?.position(), {capture: true, passive: true});
window.addEventListener('hashchange', () => {opened?.close(); for (const control of controls.values()) control.refresh();});
