import test from 'node:test';
import assert from 'node:assert/strict';
import {adlerTrace,crcBitTrace,crcByteTrace} from '../static/zlib-checksum-models.mjs';
const bytes=s=>[...s].map(c=>c.charCodeAt(0));
test('standard-seed traces agree with independently checked checksum vectors',()=>{
  for(const [s,adler,crc] of [['',1,0],['AB',0x00c60084,0x30694c07],['ABABABAB',0x093c020d,0x94b093a4],['123456789',0x091e01de,0xcbf43926]]){
    assert.equal(adlerTrace(bytes(s)).at(-1).value,adler);
    assert.equal(crcBitTrace(bytes(s)).at(-1).value,crc);
    assert.equal(crcByteTrace(bytes(s)).at(-1).value,crc);
  }
});
test('a byte lookup combines exactly eight reflected bit updates for all byte values',()=>{
  for(let byte=0;byte<256;byte++){
    const input=[0x41,byte,0xff];const bit=crcBitTrace(input),table=crcByteTrace(input);
    for(let prefix=1;prefix<=input.length;prefix++)assert.equal(bit[prefix*9].register,table[prefix].register);
  }
});
