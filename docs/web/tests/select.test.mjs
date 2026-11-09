import test from 'node:test';
import assert from 'node:assert/strict';
import {menuGeometry, nextEnabled, matchOption} from '../static/select-model.mjs';

test('menus remain inside narrow viewports, including near every edge', () => {
  for (const width of [280, 320, 390, 768, 1440]) for (const height of [180, 600, 900]) {
    for (const left of [-20, 12, width - 100]) for (const top of [0, height / 2, height - 44]) {
      const rect = {left, top, width: 220, bottom: top + 40};
      const menu = menuGeometry(rect, width, height, 800);
      assert.ok(menu.left >= 0 && menu.left + menu.width <= width);
      assert.ok(menu.top >= 0 && menu.top + menu.height <= height);
      assert.ok(menu.height <= 360);
    }
  }
});

test('menus open upward when the bottom edge leaves insufficient room', () => {
  assert.equal(menuGeometry({left: 20, top: 520, bottom: 560, width: 250}, 390, 600, 400).upward, true);
  assert.equal(menuGeometry({left: 20, top: 30, bottom: 70, width: 250}, 390, 600, 400).upward, false);
});

test('arrow, Home and End movement skip disabled choices and stop at boundaries', () => {
  const options = [{disabled: true}, {disabled: false}, {disabled: true}, {disabled: false}];
  assert.equal(nextEnabled(options, -1, 1), 1);
  assert.equal(nextEnabled(options, options.length, -1), 3);
  assert.equal(nextEnabled(options, 1, 1), 3);
  assert.equal(nextEnabled(options, 3, 1), 3);
  assert.equal(nextEnabled(options, 3, -1), 1);
});

test('typeahead cycles long target lists without selecting a disabled option', () => {
  const options = [{label: 'inflate', disabled: true}, {label: 'inflateCopy'}, {label: 'inflateEnd'}, {label: 'deflate'}];
  assert.equal(matchOption(options, 'INFLATE', -1), 1);
  assert.equal(matchOption(options, 'inflate', 1), 2);
  assert.equal(matchOption(options, 'inflate', 2), 1);
  assert.equal(matchOption(options, 'def', 0), 3);
  assert.equal(matchOption(options, 'missing', 0), -1);
});
