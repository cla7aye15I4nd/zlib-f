// Layout and keyboard rules shared by the themed select and its tests.
export function menuGeometry(rect, viewportWidth, viewportHeight, contentHeight) {
  const margin = Math.min(12, viewportWidth / 4, viewportHeight / 4), gap = 6;
  const width = Math.max(1, Math.min(Math.max(rect.width, 180), viewportWidth - 2 * margin));
  const below = Math.max(0, viewportHeight - rect.bottom - gap - margin);
  const above = Math.max(0, rect.top - gap - margin);
  const upward = below < Math.min(contentHeight, 260) && above > below;
  const height = Math.max(1, Math.min(contentHeight, 360, upward ? above : below));
  return {
    left: Math.max(margin, Math.min(rect.left, viewportWidth - margin - width)),
    top: Math.max(margin, Math.min(upward ? rect.top - gap - height : rect.bottom + gap, viewportHeight - margin - height)),
    width, height, upward,
  };
}

export function nextEnabled(options, current, direction) {
  for (let index = current + direction; index >= 0 && index < options.length; index += direction) {
    if (!options[index].disabled) return index;
  }
  return current;
}

export function matchOption(options, query, start) {
  const normalize = text => text.normalize('NFKD').replace(/\p{M}/gu, '').toLocaleLowerCase();
  const prefix = normalize(query);
  if (!prefix) return -1;
  for (let offset = 1; offset <= options.length; offset++) {
    const index = (start + offset + options.length) % options.length;
    if (!options[index].disabled && normalize(options[index].label).startsWith(prefix)) return index;
  }
  return -1;
}
