// Byte/bit teaching traces with the standard initial checksum values.
export const ADLER_BASE=65521;
export const CRC_POLY=0xedb88320;
export function adlerTrace(bytes){
  let a=1,b=0;const states=[{a,b,value:1,byte:null,index:0}];
  for(const [i,byte] of bytes.entries()){
    if(!Number.isInteger(byte)||byte<0||byte>255)throw new RangeError('Expected a byte');
    a=(a+byte)%ADLER_BASE;b=(b+a)%ADLER_BASE;
    states.push({a,b,value:((b<<16)|a)>>>0,byte,index:i+1});
  }
  return states;
}
export function crcTableEntry(byte){
  let r=byte>>>0;
  for(let i=0;i<8;i++)r=((r>>>1)^((r&1)?CRC_POLY:0))>>>0;
  return r;
}
export function crcBitTrace(bytes){
  let register=0xffffffff;
  const states=[{register,byte:null,byteIndex:0,bit:0,operation:'start',value:0}];
  for(const [index,byte] of bytes.entries()){
    if(!Number.isInteger(byte)||byte<0||byte>255)throw new RangeError('Expected a byte');
    register=(register^byte)>>>0;
    states.push({register,byte,byteIndex:index,bit:0,operation:'byte',value:(register^0xffffffff)>>>0});
    for(let bit=1;bit<=8;bit++){
      const low=register&1;
      register=((register>>>1)^(low?CRC_POLY:0))>>>0;
      states.push({register,byte,byteIndex:index,bit,operation:low?'xor':'shift',value:(register^0xffffffff)>>>0});
    }
  }
  return states;
}
export function crcByteTrace(bytes){
  let register=0xffffffff;
  const states=[{register,value:0,index:0}];
  for(const [i,byte] of bytes.entries()){
    const slot=(register^byte)&255;
    register=((register>>>8)^crcTableEntry(slot))>>>0;
    states.push({register,value:(register^0xffffffff)>>>0,index:i+1,slot});
  }
  return states;
}
