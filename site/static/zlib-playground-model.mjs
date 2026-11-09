export const PLAYGROUND_LIMIT = 256 * 1024;
export const PLAYGROUND_PREVIEW = 64;
export class PlaygroundInputError extends Error {
  constructor(code) { super(code); this.name='PlaygroundInputError'; this.code=code; }
}
export function parsePlaygroundInput(mode, value) {
  if (typeof value !== 'string') throw new PlaygroundInputError('mode');
  let bytes;
  if (mode === 'text') bytes=new TextEncoder().encode(value);
  else if (mode === 'hex') {
    const compact=value.replace(/\s/g,'');
    if (!/^[0-9a-f]*$/i.test(compact) || compact.length % 2) throw new PlaygroundInputError('hex');
    if (compact.length/2 > PLAYGROUND_LIMIT) throw new PlaygroundInputError('limit');
    bytes=Uint8Array.from({length:compact.length/2},(_,i)=>parseInt(compact.slice(i*2,i*2+2),16));
  } else throw new PlaygroundInputError('mode');
  if (bytes.length > PLAYGROUND_LIMIT) throw new PlaygroundInputError('limit');
  return bytes;
}
export function playgroundHex(bytes, limit=PLAYGROUND_PREVIEW) {
  return Array.from(bytes.subarray(0,limit),byte=>byte.toString(16).padStart(2,'0')).join(' ');
}
export const PLAYGROUND_KINDS = Object.freeze({1:'deflateInit',2:'deflate',3:'deflateEnd',4:'inflateInit',5:'inflate',6:'inflateEnd',7:'compare'});
export function readPlaygroundRecords(heap,pointer,count) {
  if (!Number.isInteger(count)||count<0||count>8||pointer<0||pointer+count*32>heap.byteLength)throw new RangeError('Invalid call records');
  const view=new DataView(heap.buffer,heap.byteOffset,heap.byteLength);
  return Array.from({length:count},(_,i)=>{
    const offset=pointer+i*32,kind=view.getUint32(offset,true);
    if(!PLAYGROUND_KINDS[kind])throw new RangeError('Invalid call kind');
    return {kind,result:view.getInt32(offset+4,true),inputBefore:view.getUint32(offset+8,true),inputAfter:view.getUint32(offset+12,true),outputBefore:view.getUint32(offset+16,true),outputAfter:view.getUint32(offset+20,true),totalInput:view.getUint32(offset+24,true),totalOutput:view.getUint32(offset+28,true)};
  });
}
