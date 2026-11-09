import test from 'node:test';
import assert from 'node:assert/strict';
import {inflateRawSync} from 'node:zlib';
import {alphabetExample,dynamicHeaderExample,fixedExample,canonicalCodes,numericBits,packBits,hex} from '../static/deflate-format-model.mjs';

// A separate packet-only reader uses sorted-length integer assignment, rather
// than the model's per-length counter algorithm. It receives no encoder tables.
function readExample(packet,prefix=[]){
 let cursor=0;
 function number(width){let value=0;for(let i=0;i<width;i++,cursor++)value+=((packet[cursor>>3]>>(cursor%8))&1)*2**i;return value;}
 function book(lengths){let value=0,previous=0;const result=new Map();for(const {length,symbol} of lengths.map((length,symbol)=>({length,symbol})).filter(x=>x.length).sort((a,b)=>a.length-b.length||a.symbol-b.symbol)){value*=2**(length-previous);result.set(length+':'+value,symbol);value++;previous=length;}return result;}
 function symbol(table){let code=0;for(let width=1;width<=15;width++){code=code*2+number(1);const found=table.get(width+':'+code);if(found!==undefined)return found;}throw Error('Example code not found');}
 assert.equal(number(1),1);const type=number(2);let ll,dist,headerEnd=3;
 if(type===1){ll=book(Array.from({length:288},(_,s)=>s<144?8:s<256?9:s<280?7:8));dist=book(Array(32).fill(5));}
 else{assert.equal(type,2);const nl=number(5)+257,nd=number(5)+1,nc=number(4)+4,order=[16,17,18,0,8,7,9,6,10,5,11,4,12,3,13,2,14,1,15],cl=Array(19).fill(0);for(const s of order.slice(0,nc))cl[s]=number(3);const description=book(cl),lengths=[];while(lengths.length<nl+nd){const s=symbol(description);if(s<16)lengths.push(s);else if(s===16)lengths.push(...Array(number(2)+3).fill(lengths.at(-1)));else lengths.push(...Array(number(s===17?3:7)+(s===17?3:11)).fill(0));}assert.equal(lengths.length,nl+nd);ll=book(lengths.slice(0,nl));dist=book(lengths.slice(nl));headerEnd=cursor;}
 const output=[...prefix],events=[];
 for(;;){const start=cursor,s=symbol(ll);if(s<256){output.push(s);events.push({kind:'literal',start,end:cursor});continue;}if(s===256)break;assert.ok(s===260||s===265);const length=s===260?6:11+number(1);const d=symbol(dist);assert.ok(d===1||d===4);const distance=d===1?2:5+number(1);for(let i=0;i<length;i++)output.push(output[output.length-distance]);events.push({kind:'match',start,end:cursor,length,distance});}
 return {output:Uint8Array.from(output),cursor,headerEnd,events};
}

test('real fixed block matches the published five bytes and independent receivers',()=>{
 const ex=fixedExample();assert.equal(hex(ex.packet),'73 74 82 40 00');assert.equal(ex.bits.length,38);assert.equal(ex.padding,2);assert.equal(inflateRawSync(ex.packet).toString(),'ABABABAB');const decoded=readExample(ex.packet);assert.equal(Buffer.from(decoded.output).toString(),'ABABABAB');assert.equal(decoded.cursor,38);assert.equal(decoded.headerEnd,3);
});

test('dynamic block independently reconstructs both books from116header bits',()=>{
 const ex=dynamicHeaderExample();assert.equal(hex(ex.packet),'25 c1 31 11 00 00 00 40 c0 6c f4 0f 65 70 8f 0b');assert.equal(ex.headerBits.length,116);assert.equal(ex.payloadBits,'000111010');assert.equal(ex.padding,3);assert.equal(ex.expanded.length,263);assert.deepEqual(ex.expanded,[...ex.literalLengths,...ex.distanceLengths]);assert.equal(inflateRawSync(ex.packet).toString(),'ABABABAB');const decoded=readExample(ex.packet);assert.equal(decoded.headerEnd,116);assert.equal(decoded.cursor,125);assert.equal(Buffer.from(decoded.output).toString(),'ABABABAB');
});

test('one payload cursor changes books and remains stationary during overlap copying',()=>{
 const ex=alphabetExample();assert.deepEqual(ex.fields.map(f=>f.book),['ll','ll','ll','distance','ll']);assert.equal(ex.steps.at(-1).cursor,9);assert.equal(Buffer.from(ex.steps.at(-1).output).toString(),'ABABABAB');const copies=ex.steps.filter(s=>s.kind==='copy');assert.equal(copies.length,6);assert.deepEqual(copies.map(s=>s.cursor),Array(6).fill(7));for(const s of copies){assert.equal(s.target-s.source,2);assert.equal(s.output[s.target],s.output[s.source]);}assert.deepEqual(ex.distanceBook,[{symbol:1,length:1,bits:'0'}]);
});

test('extra bits bypass both books, with an explicit already-emitted prefix',()=>{
 const ex=alphabetExample('extra');assert.equal(ex.bits,'1110110'); // 11 | 1 | 0 | 1 | 10
 assert.deepEqual(ex.fields.map(f=>f.book),['ll',null,'distance',null,'ll']);assert.equal(Buffer.from(ex.prefix).toString(),'ABCDEF');assert.equal(Buffer.from(ex.steps.at(-1).output).toString(),'ABCDEFABCDEFABCDEF');assert.equal(ex.steps.find(s=>s.kind==='length').length,11);assert.equal(ex.steps.find(s=>s.kind==='length-extra').length,12);assert.equal(ex.steps.find(s=>s.kind==='distance').distance,5);assert.equal(ex.steps.find(s=>s.kind==='distance-extra').distance,6);
 // Serialize this different pair of books directly, with a simple description
 // alphabet. A raw decoder supplies the stated prefix as its existing context.
 const description=Array(19).fill(0);description[0]=1;description[1]=description[2]=2;const order=[16,17,18,0,8,7,9,6,10,5,11,4,12,3,13,2,14,1,15],codes=new Map(canonicalCodes(description).map(x=>[x.symbol,x.bits]));
 const header='101'+numericBits(ex.lengths.length-257,5)+numericBits(ex.distances.length-1,5)+numericBits(14,4)+order.slice(0,18).map(s=>numericBits(description[s],3)).join('')+[...ex.lengths,...ex.distances].map(n=>codes.get(n)).join('');const packet=packBits(header+ex.bits);
 const expected='ABCDEFABCDEF';assert.equal(inflateRawSync(packet,{dictionary:Buffer.from(ex.prefix)}).toString(),expected);const independent=readExample(packet,ex.prefix);assert.equal(Buffer.from(independent.output).toString(),'ABCDEF'+expected);assert.equal(independent.events.at(-1).length,12);assert.equal(independent.events.at(-1).distance,6);
});

test('header repeats expand at exact positions and zero lengths never become leaves',()=>{
 const ex=dynamicHeaderExample();assert.deepEqual(ex.runs.map(r=>r.end),[65,66,67,205,256,257,260,261,262,263]);assert.deepEqual(ex.literalBook.map(r=>[r.symbol,r.bits]),[[65,'00'],[66,'01'],[256,'10'],[260,'11']]);assert.deepEqual(ex.descriptionBook.map(r=>[r.symbol,r.bits]),[[0,'1110'],[1,'1111'],[2,'0'],[17,'110'],[18,'10']]);assert.equal(ex.provided.length,18);assert.equal(ex.descriptionLengths[15],0);assert.equal(ex.literalBook.length,4);assert.equal(ex.distanceBook.length,1);
});
