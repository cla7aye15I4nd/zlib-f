/** Receiver-order bits for ordinary valid DEFLATE teaching examples. */
export const CL_ORDER=[16,17,18,0,8,7,9,6,10,5,11,4,12,3,13,2,14,1,15];
export const numericBits=(value,width)=>Array.from({length:width},(_,i)=>(value>>>i)&1).join('');
export const hex=bytes=>Array.from(bytes,b=>b.toString(16).padStart(2,'0')).join(' ');
export function canonicalCodes(lengths){const counts=Array(16).fill(0),next=Array(16).fill(0);for(const length of lengths)if(length)counts[length]++;let code=0;for(let n=1;n<16;n++){code=(code+counts[n-1])*2;next[n]=code;}return lengths.flatMap((length,symbol)=>length?[{symbol,length,bits:(next[length]++).toString(2).padStart(length,'0')}]:[]);}
const code=(book,symbol)=>book.find(row=>row.symbol===symbol).bits;
export function packBits(bits){const bytes=new Uint8Array(Math.ceil(bits.length/8));for(let i=0;i<bits.length;i++)if(bits[i]==='1')bytes[i>>3]|=1<<(i%8);return bytes;}
function locate(fields){let cursor=0;return fields.map((f,index)=>{const start=cursor;cursor+=f.bits.length;return {...f,index,start,end:cursor};});}
export function alphabetExample(name='short'){
 const long=name==='extra',length=long?12:6,distance=long?6:2,lengthSymbol=long?265:260,distanceSymbol=long?4:1;
 const lengths=Array(lengthSymbol+1).fill(0);for(const s of [65,66,256,lengthSymbol])lengths[s]=2;
 const distances=Array(distanceSymbol+1).fill(0);distances[distanceSymbol]=1;
 const literalBook=canonicalCodes(lengths),distanceBook=canonicalCodes(distances),fields=[];
 if(!long)for(const symbol of [65,66])fields.push({kind:'literal',book:'ll',symbol,bits:code(literalBook,symbol)});
 fields.push({kind:'length',book:'ll',symbol:lengthSymbol,base:long?11:6,width:long?1:0,bits:code(literalBook,lengthSymbol)});
 if(long)fields.push({kind:'length-extra',book:null,value:1,bits:'1'});
 fields.push({kind:'distance',book:'distance',symbol:distanceSymbol,base:long?5:2,width:long?1:0,bits:code(distanceBook,distanceSymbol)});
 if(long)fields.push({kind:'distance-extra',book:null,value:1,bits:'1'});
 fields.push({kind:'end',book:'ll',symbol:256,bits:code(literalBook,256)});
 const located=locate(fields),bits=located.map(f=>f.bits).join(''),prefix=long?Array.from('ABCDEF',c=>c.charCodeAt(0)):[];
 let output=[...prefix],cursor=0,knownLength=null,knownDistance=null;
 const steps=[{kind:'start',cursor,output:[...output],book:null}];
 const save=(kind,field,more={})=>steps.push({kind,cursor,output:[...output],book:field?.book??null,field:field?.index,symbol:field?.symbol,length:knownLength,distance:knownDistance,...more});
 for(const field of located){cursor=field.end;
  if(field.kind==='literal'){output.push(field.symbol);save(field.kind,field);}
  else if(field.kind==='length'){knownLength=field.base;save(field.kind,field,{width:field.width,base:field.base});}
  else if(field.kind==='length-extra'){knownLength+=field.value;save(field.kind,field,{extra:field.value});}
  else if(field.kind==='distance'){knownDistance=field.base;save(field.kind,field,{width:field.width,base:field.base});}
  else if(field.kind==='distance-extra'){knownDistance+=field.value;save(field.kind,field,{extra:field.value});}
  else save(field.kind,field);
  if((field.kind==='distance'&&!field.width)||field.kind==='distance-extra')for(let i=0;i<length;i++){const source=output.length-distance,target=output.length;output.push(output[source]);save('copy',null,{source,target,remaining:length-i-1});}
 }
 return {name,long,length,distance,lengthSymbol,distanceSymbol,literalBook,distanceBook,lengths,distances,fields:located,bits,prefix,steps};
}
export function dynamicHeaderExample(){
 const {lengths:literalLengths,distances:distanceLengths,literalBook,distanceBook,bits:payloadBits}=alphabetExample();
 const descriptionLengths=Array(19).fill(0);for(const [s,n] of [[2,1],[18,2],[17,3],[0,4],[1,4]])descriptionLengths[s]=n;
 const descriptionBook=canonicalCodes(descriptionLengths),instructions=[{symbol:18,extra:54},{symbol:2},{symbol:2},{symbol:18,extra:127},{symbol:18,extra:40},{symbol:2},{symbol:17,extra:0},{symbol:2},{symbol:0},{symbol:1}];
 const fields=[{kind:'header',bits:'101'},{kind:'literal-count',value:4,bits:numericBits(4,5)},{kind:'distance-count',value:1,bits:numericBits(1,5)},{kind:'description-count',value:14,bits:numericBits(14,4)}];
 for(const symbol of CL_ORDER.slice(0,18))fields.push({kind:'description-length',symbol,value:descriptionLengths[symbol],bits:numericBits(descriptionLengths[symbol],3)});
 const expanded=[],runs=[];
 for(const instruction of instructions){const {symbol}=instruction,start=expanded.length,count=symbol===18?11+instruction.extra:symbol===17?3+instruction.extra:1,value=symbol<16?symbol:0;
  fields.push({kind:'description-symbol',symbol,bits:code(descriptionBook,symbol)});
  if(symbol>=17)fields.push({kind:'description-extra',symbol,value:instruction.extra,bits:numericBits(instruction.extra,symbol===18?7:3)});
  expanded.push(...Array(count).fill(value));runs.push({...instruction,start,end:expanded.length,count,value});
 }
 const header=locate(fields),headerBits=header.map(f=>f.bits).join(''),bits=headerBits+payloadBits;
 return {literalLengths,distanceLengths,descriptionLengths,literalBook,distanceBook,descriptionBook,provided:CL_ORDER.slice(0,18).map(symbol=>({symbol,length:descriptionLengths[symbol]})),instructions,runs,expanded,fields:header,headerBits,payloadBits,packet:packBits(bits),padding:(8-bits.length%8)%8};
}
export function fixedExample(){const ll=canonicalCodes(Array.from({length:288},(_,s)=>s<144?8:s<256?9:s<280?7:8)),d=canonicalCodes(Array(32).fill(5));const fields=locate([{kind:'header',bits:'110'},...[65,66,260].map(symbol=>({kind:'ll',symbol,bits:code(ll,symbol)})),{kind:'distance',symbol:1,bits:code(d,1)},{kind:'end',symbol:256,bits:code(ll,256)}]);const bits=fields.map(f=>f.bits).join('');return {fields,bits,packet:packBits(bits),padding:2};}
