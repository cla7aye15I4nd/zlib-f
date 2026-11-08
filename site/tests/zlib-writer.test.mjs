import test from 'node:test';
import assert from 'node:assert/strict';
import {inflateRawSync} from 'node:zlib';
import {FIXED_FIELDS,writerTrace} from '../static/zlib-writer-model.mjs';

const byteBits=bytes=>bytes.flatMap(byte=>Array.from({length:8},(_,i)=>(byte>>>i)&1));
test('the worked raw block recovers the stated eight bytes with a real decoder',()=>{
  const last=writerTrace().at(-1);
  assert.equal(last.logical.length,38);
  assert.deepEqual(last.bytes,[0x73,0x74,0x82,0x40,0]);
  assert.equal(inflateRawSync(Buffer.from(last.bytes)).toString(),'ABABABAB');
});
test('every writer boundary represents exactly the bits already supplied',()=>{
  for(const state of writerTrace().slice(0,-1)){
    const held=Array.from({length:state.valid},(_,i)=>(state.buffer>>>i)&1);
    assert.deepEqual([...byteBits(state.bytes),...held],state.logical);
    assert.ok(state.valid<=16);
  }
  const last=writerTrace().at(-1);
  assert.deepEqual(byteBits(last.bytes).slice(0,38),last.logical);
  assert.deepEqual(byteBits(last.bytes).slice(38),[0,0]);
});
test('exactly sixteen held bits remain until a later write or windup',()=>{
  const trace=writerTrace([{name:'first',value:7,width:3},{name:'second',value:8191,width:13},{name:'third',value:1,width:1}]);
  assert.equal(trace[2].valid,16);assert.deepEqual(trace[2].bytes,[]);
  assert.equal(trace[3].valid,1);assert.deepEqual(trace[3].bytes,[255,255]);
  assert.deepEqual(trace.at(-1).bytes,[255,255,1]);
});
test('the fields have the stated six lengths and strict input bounds',()=>{
  assert.deepEqual(FIXED_FIELDS.map(f=>f.width),[3,8,8,7,5,7]);
  assert.throws(()=>writerTrace([{name:'bad',value:2,width:1}]),RangeError);
});
