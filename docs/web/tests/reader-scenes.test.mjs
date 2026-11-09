import test from 'node:test';
import assert from 'node:assert/strict';
import {inflateRawSync} from 'node:zlib';
import {ROUNDTRIP_BYTES,ROUNDTRIP_LAST,roundtripState} from '../static/zlib-roundtrip-scene.mjs';
import {refillSnapshots,refillFacts} from '../static/zlib-refill-model.mjs';
import {createLengthsState,stepLengths} from '../static/zlib-lengths-model.mjs';
import {BLOCK_CASES,blockCandidates} from '../static/zlib-blockcost-model.mjs';
import {fastAdmission,orderedMatch} from '../static/zlib-fastpath-scene.mjs';

test('selected round-trip bytes decode independently; displayed prefixes and pause agree',()=>{
 assert.equal(inflateRawSync(Uint8Array.from(ROUNDTRIP_BYTES)).toString(),'ABABABAB');
 for(let i=0;i<=ROUNDTRIP_LAST;i++){
  const s=roundtripState(i);assert.equal(s.output,'ABABABAB'.slice(0,s.output.length));
  if(s.target>=0){assert.equal(s.target-s.source,2);assert.equal(s.output[s.target],s.output[s.source]);}
 }
 assert.equal(roundtripState(12).output,'ABABA');assert.equal(roundtripState(12).remaining,3);
 assert.equal(roundtripState(15).complete,false);assert.equal(roundtripState(16).complete,true);
});

test('sliding changes addresses without changing retained bytes or reference distance',()=>{
 const [before,slid,loaded]=refillSnapshots();
 assert.equal(slid.copied,388);assert.equal(loaded.loaded,300);
 for(let i=0;i<388;i++)assert.deepEqual(slid.bytes[i],before.bytes[i+512]);
 for(let i=0;i<300;i++)assert.equal(loaded.bytes[388+i].logical,900+i);
 for(const s of [before,slid,loaded]){
  const f=refillFacts(s);assert.equal(s.base+s.strstart,800);assert.equal(f.distance,100);
  assert.equal(s.bytes[f.trackedIndex].logical,700);
 }
 assert.equal(slid.strstart,288);assert.equal(loaded.lookahead,400);assert.equal(loaded.inputCursor,1200);
});

function expand(name){let s=createLengthsState(name);for(let i=0;i<200&&s.phase!=='done'&&s.phase!=='error';i++)s=stepLengths(s);return s;}
test('repeat descriptions expand to the requested cells and reject before an overrun',()=>{
 const valid=expand('valid');assert.equal(valid.phase,'done');
 assert.deepEqual(valid.output,[3,3,3,3,3,0,0,0,0,0,2,...Array(13).fill(0)]);
 const overrun=expand('overrun');assert.equal(overrun.error,'overrun');assert.equal(overrun.output.length,11);
 const missing=expand('previous');assert.equal(missing.error,'previous');assert.equal(missing.extraConsumed,0);assert.equal(missing.output.length,0);
});

test('complete block examples distinguish description overhead, stored eligibility and strategy',()=>{
 const selected=['fixed','fixed','dynamic','stored'];
 for(let i=0;i<4;i++)for(let offset=0;offset<8;offset++){
  const c=blockCandidates(BLOCK_CASES[i],{offset});assert.equal(c.selected,selected[i]);
  for(const row of c.rows)assert.equal((row.total+offset)%8,0);
 }
 assert.equal(blockCandidates(BLOCK_CASES[3],{fixed:true}).selected,'stored');
 assert.equal(blockCandidates(BLOCK_CASES[3],{raw:false}).selected,'fixed');
 assert.equal(blockCandidates(BLOCK_CASES[2],{fixed:true}).selected,'fixed');
});

test('fast admission is a capacity decision; grouped stores preserve self-reading copies',()=>{
 assert.equal(fastAdmission(6,258,7).fast,true);
 for(const args of [[5,258,7],[6,257,7],[6,258,8]])assert.equal(fastAdmission(...args).fast,false);
 for(const seed of ['AB','ABC','AAAA'])for(let d=1;d<=seed.length;d++)for(const n of [0,1,2,6,258]){
  const ordinary=orderedMatch(seed,n,d,1),grouped=orderedMatch(seed,n,d,3);
  assert.equal(grouped.output,ordinary.output);
  for(const write of grouped.batches.flat()){assert.ok(write.source<write.target);assert.equal(write.target-write.source,d);}
 }
});
