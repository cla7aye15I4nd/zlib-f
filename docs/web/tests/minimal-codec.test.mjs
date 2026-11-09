import test from 'node:test';
import assert from 'node:assert/strict';
import {MINIMAL_LIMIT,MATCH,END,parseMinimalInput,lz77,canonicalBook,encodeMinimal,decodeMinimal,runMinimal,hexBytes} from '../static/minimal-codec-model.mjs';
const utf8=value=>new TextEncoder().encode(value);
const hex=value=>Uint8Array.from(value.replace(/\s/g,'').match(/../g)||[],x=>parseInt(x,16));
const GOLDEN=hex('00 08 00 04 00 41 02 00 42 02 01 00 02 01 01 02 18 00 08 00 1b');
/** Test-side parser uses numeric canonical recurrence and string consumption.
 * It imports neither the production codebook builder nor the receiver. */
function independentRead(packet) {
  let offset=0;
  const get=()=>{assert.ok(offset<packet.length,'metadata available');return packet[offset++];};
  const u16=()=>get()*256+get();
  const size=u16(),n=u16(),entries=[];
  assert.ok(size<=512&&n>=1&&n<=258);
  let last=-1;
  for(let i=0;i<n;i++){const symbol=u16(),length=get();assert.ok(symbol>last&&symbol<=257&&length>=1&&length<=32);entries.push({symbol,length});last=symbol;}
  assert.ok(entries.some(e=>e.symbol===257));
  const counts=Array(33).fill(0);for(const e of entries)counts[e.length]++;
  const next=Array(33).fill(0);for(let length=1;length<=32;length++)next[length]=(next[length-1]+counts[length-1])*2;
  const kraft=entries.reduce((sum,e)=>sum+2**(-e.length),0);
  assert.ok(kraft===1||(n===1&&entries[0].symbol===257&&entries[0].length===1));
  const codes=new Map();
  for(let length=1;length<=32;length++)for(const e of entries.filter(e=>e.length===length))codes.set((next[length]++).toString(2).padStart(length,'0'),e.symbol);
  const payload=Array.from(packet.slice(offset),b=>b.toString(2).padStart(8,'0')).join('');
  let pos=0;const out=[];
  const number=()=>{assert.ok(pos+16<=payload.length);const value=parseInt(payload.slice(pos,pos+16),2);pos+=16;return value;};
  while(true){
    let code='';do{assert.ok(pos<payload.length,'END must arrive');code+=payload[pos++];assert.ok(code.length<=32);}while(!codes.has(code));
    const symbol=codes.get(code);if(symbol===257)break;
    if(symbol===256){const distance=number(),length=number();assert.ok(distance>=1&&distance<=out.length&&length>=3&&out.length+length<=size);for(let i=0;i<length;i++)out.push(out[out.length-distance]);}
    else{assert.ok(out.length<size);out.push(symbol);}
  }
  assert.equal(out.length,size);assert.ok(payload.length-pos<8);assert.match(payload.slice(pos),/^0*$/);
  return Uint8Array.from(out);
}
function fixture(size,book,bits) {
  const bytes=[size>>>8,size&255,book.length>>>8,book.length&255];
  for(const [symbol,length] of book)bytes.push(symbol>>>8,symbol&255,length);
  bits=bits.padEnd(Math.ceil(bits.length/8)*8,'0');
  for(let pos=0;pos<bits.length;pos+=8)bytes.push(parseInt(bits.slice(pos,pos+8),2));
  return Uint8Array.from(bytes);
}
const num=n=>n.toString(2).padStart(16,'0');
test('published ABABABAB packet is an exact independent golden fixture',()=>{
  assert.equal(hexBytes(encodeMinimal(utf8('ABABABAB')).packet),hexBytes(GOLDEN));
  assert.deepEqual(decodeMinimal(GOLDEN).output,utf8('ABABABAB'));
  assert.deepEqual(independentRead(GOLDEN),utf8('ABABABAB'));
  const r=runMinimal(utf8('ABABABAB'));
  assert.deepEqual(r.book.map(e=>[e.symbol,e.frequency,e.bits]),[[65,1,'00'],[66,1,'01'],[256,1,'10'],[257,1,'11']]);
  assert.equal(r.metadata.length,16);assert.equal(r.payloadBits,40);assert.equal(r.padding,0);
  assert.deepEqual(r.fields.map(e=>[e.start,e.end]),[[0,2],[2,4],[4,6],[6,22],[22,38],[38,40]]);
});
test('hand-authored overlapping packet and singleton END decode without encoder state',()=>{
  const overlap=fixture(4,[[65,1],[256,2],[257,2]],'0'+'10'+num(1)+num(3)+'11');
  assert.deepEqual(decodeMinimal(overlap).output,utf8('AAAA'));
  assert.deepEqual(independentRead(overlap),utf8('AAAA'));
  const empty=hex('00 00 00 01 01 01 01 00');
  assert.deepEqual(encodeMinimal(new Uint8Array()).packet,empty);
  assert.deepEqual(decodeMinimal(empty).output,new Uint8Array());
  assert.deepEqual(independentRead(empty),new Uint8Array());
});
test('receiver reconstructs length order independently and supports the 32-bit limit',()=>{
  const reordered=fixture(2,[[65,2],[66,2],[257,1]],'10110');
  assert.deepEqual(decodeMinimal(reordered).output,utf8('AB'));
  assert.deepEqual(independentRead(reordered),utf8('AB'));
  const longBook=Array.from({length:32},(_,i)=>[i,Math.min(i+1,32)]);
  longBook.push([257,32]);
  const longEnd=fixture(0,longBook,'1'.repeat(32));
  assert.deepEqual(decodeMinimal(longEnd).output,new Uint8Array());
  assert.deepEqual(independentRead(longEnd),new Uint8Array());
});
test('greedy LZ77 uses minimum length three and nearest longest match including overlap',()=>{
  assert.deepEqual(lz77(utf8('AAAA')).map(t=>[t.symbol,t.distance,t.length]),[[65,undefined,undefined],[256,1,3],[257,undefined,undefined]]);
  assert.ok(lz77(utf8('ABAB')).every(t=>t.symbol!==MATCH));
  const tokens=lz77(utf8('ABCABCABCABC'));
  assert.deepEqual(tokens[3],{symbol:MATCH,start:3,end:12,distance:3,length:9});
  assert.equal(tokens.at(-1).symbol,END);
});
test('Unicode, all byte values, boundary input and unequal frequencies round trip through two parsers',()=>{
  const all=Uint8Array.from({length:256},(_,i)=>i);
  const samples=[utf8('你好，压缩 🌱\0'),all,Uint8Array.from([...all,...all]),utf8('A'.repeat(512)),utf8('AA0AA1AA2AA3AA4AA5AA6AA7AA8AA9')];
  for(const bytes of samples){const encoded=encodeMinimal(bytes);assert.deepEqual(decodeMinimal(encoded.packet).output,bytes);assert.deepEqual(independentRead(encoded.packet),bytes);assert.equal(runMinimal(bytes).equal,true);}
  const book=encodeMinimal(samples.at(-1)).book;
  assert.ok(book.find(e=>e.symbol===65).length<book.find(e=>e.symbol===48).length);
});
test('deterministic generated byte sequences are independently decoded',()=>{
  let state=0x512ab;
  const random=()=>{state=(Math.imul(state,1664525)+1013904223)>>>0;return state;};
  for(let sample=0;sample<100;sample++){
    const length=random()%513,alphabet=sample%2?256:5;
    const bytes=Uint8Array.from({length},()=>random()%alphabet),r=encodeMinimal(bytes);
    assert.deepEqual(decodeMinimal(r.packet).output,bytes);
    assert.deepEqual(independentRead(r.packet),bytes);
    assert.deepEqual(encodeMinimal(bytes).packet,r.packet);
  }
});
test('input parsing accepts arbitrary bytes and enforces a byte cap',()=>{
  assert.deepEqual(parseMinimalInput('hex','00 ff\n4100'),hex('00ff4100'));
  assert.deepEqual(parseMinimalInput('text','你'),hex('e4bda0'));
  assert.equal(MINIMAL_LIMIT,512);
  for(const value of ['a','fg','00,ff','0 0 f'])assert.throws(()=>parseMinimalInput('hex',value));
  assert.throws(()=>parseMinimalInput('text','你'.repeat(171)),/limit/);
  assert.throws(()=>encodeMinimal(new Uint8Array(513)),/512/);
});
test('rejects invalid books, metadata truncation and output size declarations',()=>{
  for(const entries of [[],[{symbol:257,length:0}],[{symbol:257,length:33}],[{symbol:258,length:1}],[{symbol:65,length:1}],[{symbol:65,length:2},{symbol:257,length:2}],[{symbol:65,length:1},{symbol:66,length:1},{symbol:257,length:1}],[{symbol:257,length:1},{symbol:257,length:1}]])assert.throws(()=>canonicalBook(entries));
  for(let n=0;n<GOLDEN.length;n++)assert.throws(()=>decodeMinimal(GOLDEN.slice(0,n)));
  for(const packet of [fixture(513,[[257,1]],'0'),fixture(0,[],'0'),fixture(0,[[257,1],[65,1]],'0'),fixture(0,[[65,1],[65,2],[257,2]],'0')])assert.throws(()=>decodeMinimal(packet));
});
test('rejects malformed payload bounds, END, padding and extra bytes',()=>{
  const book=[[65,1],[256,2],[257,2]];
  const malformed=[
    fixture(3,book,'10'+num(1)+num(3)+'11'), // no history
    fixture(4,book,'0'+'10'+num(0)+num(3)+'11'),
    fixture(4,book,'0'+'10'+num(2)+num(3)+'11'),
    fixture(3,book,'0'+'10'+num(1)+num(2)+'11'),
    fixture(3,book,'0'+'10'+num(1)+num(3)+'11'), // expansion too long
    fixture(2,[[65,1],[257,1]],'01'), // early END
    fixture(0,[[65,1],[257,1]],'01'), // literal beyond declared length
    fixture(0,[[257,1]],'1'), // unused singleton prefix
    fixture(0,[[257,1]],'01'), // nonzero padding
    Uint8Array.from([...GOLDEN,0]),
  ];
  for(const packet of malformed)assert.throws(()=>decodeMinimal(packet));
  const noEnd=GOLDEN.slice();noEnd[noEnd.length-1]&=0xfc;assert.throws(()=>decodeMinimal(noEnd));
});
