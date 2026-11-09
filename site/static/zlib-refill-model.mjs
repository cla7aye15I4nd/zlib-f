// One legal window size and one chosen snapshot of the ordinary fill_window path.
export const REFILL_CASE = Object.freeze({windowSize:512,capacity:1024,minLookahead:262,maxDistance:250,strstart:800,lookahead:100,availableInput:300,inputCursor:900,trackedLogical:700});
const inputByte = logical => ({logical,value:48+logical%10});
export function initialRefillState() {
  const c=REFILL_CASE, prev=Array(c.windowSize).fill(0);
  prev[700&511]=650; prev[650&511]=600; prev[600&511]=500;
  return {phase:0,windowSize:c.windowSize,capacity:c.capacity,strstart:c.strstart,lookahead:c.lookahead,base:0,inputCursor:c.inputCursor,availableInput:c.availableInput,
    bytes:Array.from({length:c.capacity},(_,i)=>i<c.inputCursor?inputByte(i):{logical:null,value:0}),prev,copied:0,loaded:0};
}
export function slideRefillWindow(before) {
  const w=before.windowSize,end=before.strstart+before.lookahead;
  if(before.lookahead>=262||before.strstart<w+(w-262)||end>before.capacity)throw new RangeError('Slide preconditions');
  const more=before.capacity-end,count=w-more,bytes=before.bytes.map(cell=>({...cell}));
  for(let i=0;i<count;i++)bytes[i]={...before.bytes[w+i]};
  // Byte indices are continuous. Only predecessor slots use a masked index.
  const position=p=>p>=w?p-w:0;
  return {...before,phase:1,base:before.base+w,strstart:before.strstart-w,bytes,prev:before.prev.map(position),copied:count,loaded:0};
}
export function loadRefillInput(before) {
  const end=before.strstart+before.lookahead,count=Math.min(before.availableInput,before.capacity-end),bytes=before.bytes.map(cell=>({...cell}));
  for(let i=0;i<count;i++)bytes[end+i]=inputByte(before.inputCursor+i);
  return {...before,phase:2,bytes,prev:before.prev.slice(),lookahead:before.lookahead+count,inputCursor:before.inputCursor+count,availableInput:before.availableInput-count,loaded:count};
}
export function refillSnapshots() {const before=initialRefillState(),slid=slideRefillWindow(before);return [before,slid,loadRefillInput(slid)];}
export function refillFacts(state) {
  const end=state.strstart+state.lookahead,trackedIndex=REFILL_CASE.trackedLogical-state.base;
  return {end,free:state.capacity-end,historyStart:Math.max(0,state.strstart-REFILL_CASE.maxDistance),logicalStart:state.base+state.strstart,trackedIndex,distance:state.strstart-trackedIndex,slot:trackedIndex&(state.windowSize-1),predecessor:state.prev[trackedIndex&(state.windowSize-1)]};
}
