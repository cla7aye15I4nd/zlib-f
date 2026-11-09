import test from 'node:test';
import assert from 'node:assert/strict';
import {readFile} from 'node:fs/promises';
import {createHash} from 'node:crypto';
import {inflateSync} from 'node:zlib';
import createCodecModule from '../static/vendor/zlib-playground.js';
import {PLAYGROUND_LIMIT,parsePlaygroundInput,readPlaygroundRecords} from '../static/zlib-playground-model.mjs';

const wasm=await readFile(new URL('../static/vendor/zlib-playground.wasm',import.meta.url));
const module=await createCodecModule({wasmBinary:wasm});
function run(bytes){
 const p=module._malloc(Math.max(1,bytes.length));assert.ok(p);module.HEAPU8.set(bytes,p);
 try{
  assert.equal(module._codec_run(p,bytes.length),0);
  const records=readPlaygroundRecords(module.HEAPU8,module._codec_records(),module._codec_record_count());
  const packed=module.HEAPU8.slice(module._codec_packed(),module._codec_packed()+module._codec_packed_length());
  const restored=module.HEAPU8.slice(module._codec_restored(),module._codec_restored()+module._codec_restored_length());
  assert.equal(module._codec_equal(),1);return {records,packed,restored};
 }finally{module._codec_reset();module._free(p);}
}

test('published C and wasm artifacts match their build record',async()=>{
 const record=JSON.parse(await readFile(new URL('../content/codec-playground-provenance.json',import.meta.url),'utf8'));
 for(const [file,info] of Object.entries(record.artifacts)){
  const data=await readFile(new URL('../static/vendor/'+file,import.meta.url));
  assert.equal(data.length,info.bytes);assert.equal(createHash('sha256').update(data).digest('hex'),info.sha256);
 }
 const source=await readFile(new URL('../'+record.wrapper.path,import.meta.url));
 assert.equal(createHash('sha256').update(source).digest('hex'),record.wrapper.sha256);
 assert.equal(module._codec_stream_size(),record.configuration.browser_stream_size_bytes);
});

test('text and hexadecimal inputs preserve bytes and reject malformed notation',()=>{
 assert.deepEqual(parsePlaygroundInput('text','汉🙂\0'),new Uint8Array(Buffer.from('汉🙂\0')));
 assert.deepEqual(parsePlaygroundInput('hex','00 ff\n41 00'),Uint8Array.of(0,255,65,0));
 assert.equal(parsePlaygroundInput('hex','').length,0);
 for(const value of ['0','gg','00x1'])assert.throws(()=>parsePlaygroundInput('hex',value));
 assert.throws(()=>parsePlaygroundInput('text','x'.repeat(PLAYGROUND_LIMIT+1)));
});

test('actual C handles empty, Unicode, all byte values and the input limit',()=>{
 const random=new Uint8Array(PLAYGROUND_LIMIT);let state=0x12345678;
 for(let i=0;i<random.length;i++){state^=state<<13;state^=state>>>17;state^=state<<5;random[i]=state&255;}
 const samples=[new Uint8Array(),parsePlaygroundInput('text','ABABABAB'),parsePlaygroundInput('text','汉字🙂\0ABC'),Uint8Array.from({length:256},(_,i)=>i),new Uint8Array(PLAYGROUND_LIMIT).fill(65),random];
 for(const bytes of samples){
  const result=run(bytes);
  assert.deepEqual(result.restored,bytes);assert.deepEqual(new Uint8Array(inflateSync(result.packed)),bytes);
  assert.deepEqual(result.records.map(r=>r.kind),[1,2,3,4,5,6,7]);
  assert.deepEqual(result.records.map(r=>r.result),[0,1,0,0,1,0,1]);
  assert.equal(result.records[1].inputBefore,bytes.length);assert.equal(result.records[1].inputAfter,0);
  assert.equal(result.records[4].inputBefore,result.packed.length);assert.equal(result.records[4].inputAfter,0);
  assert.equal(result.records[4].outputBefore-result.records[4].outputAfter,bytes.length);
  assert.equal(module._codec_packed(),0);assert.equal(module._codec_restored(),0);
 }
});

test('successive C runs reset their records and result ownership',()=>{
 for(let i=0;i<24;i++)assert.equal(run(new Uint8Array(i*17).fill(i)).restored.length,i*17);
 module._codec_reset();assert.equal(module._codec_record_count(),0);
 assert.equal(module._codec_run(0,PLAYGROUND_LIMIT+1),-1);
 assert.equal(module._codec_packed(),0);module._codec_reset();
});
