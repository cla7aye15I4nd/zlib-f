import test from 'node:test';
import assert from 'node:assert/strict';
import {lookupTrace} from '../static/zlib-lookup.js';

test('lookahead from the next symbol selects the replicated A slot', () => {
  const trace=lookupTrace('AD','en');
  const states=trace.events;
  assert.equal(states[0].hold,14);
  const firstLookup=states.find(s=>s.focus==='root');
  assert.equal(firstLookup.root,2);
  const afterA=states.find(s=>s.output==='A');
  assert.equal(afterA.consumed,1);
  assert.equal(afterA.hold,7);
});

test('all messages preserve the exact bit accounting in both languages', () => {
  for(const lang of ['en','zh'])for(const message of ['AD','AC','AB']){
    const trace=lookupTrace(message,lang);
    for(const state of trace.events){
      assert.equal(state.bits+state.consumed,trace.stream.length);
      if(lang==='en')assert.equal(/[\u3400-\u9fff]/u.test(state.text+state.action),false);
    }
    assert.equal(trace.events.at(-1).output,message);
    assert.equal(trace.events.at(-1).bits,0);
  }
});
