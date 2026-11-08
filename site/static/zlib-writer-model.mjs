// Fixed raw-block teaching trace. Fields follow the selected send_bits branch order.
export const FIXED_FIELDS = Object.freeze([
  {name:'header',value:3,width:3},
  {name:'A',value:0x8e,width:8},
  {name:'B',value:0x4e,width:8},
  {name:'length',value:0x10,width:7},
  {name:'distance',value:0x10,width:5},
  {name:'end',value:0,width:7},
]);

export function writerTrace(fields=FIXED_FIELDS){
  let buffer=0,valid=0;
  const bytes=[],logical=[];
  const snapshots=[{name:'start',buffer,valid,bytes:[],logical:[],added:[]}];
  for(const {name,value,width} of fields){
    if(!Number.isInteger(width)||width<1||width>15||!Number.isInteger(value)||value<0||value>=2**width)throw new RangeError('Field must fit 1..15 bits');
    const before=bytes.length;
    for(let bit=0;bit<width;bit++)logical.push((value>>>bit)&1);
    if(valid>16-width){
      buffer=(buffer|(value<<valid))&0xffff;
      bytes.push(buffer&255,(buffer>>>8)&255);
      buffer=value>>>(16-valid);
      valid+=width-16;
    }else{
      buffer|=value<<valid;
      valid+=width;
    }
    snapshots.push({name,buffer,valid,bytes:[...bytes],logical:[...logical],added:bytes.slice(before)});
  }
  const before=bytes.length;
  if(valid>8)bytes.push(buffer&255,(buffer>>>8)&255);
  else if(valid>0)bytes.push(buffer&255);
  snapshots.push({name:'windup',buffer:0,valid:0,bytes:[...bytes],logical:[...logical],added:bytes.slice(before)});
  return snapshots;
}
