/** A complete teaching format. This is NOT a DEFLATE or zlib encoder. */
export const MINIMAL_LIMIT = 512;
export const MATCH = 256;
export const END = 257;
const fail = message => { throw new Error(message); };
export const hexBytes = bytes => Array.from(bytes, x => x.toString(16).padStart(2, '0')).join(' ');
export function parseMinimalInput(mode, value) {
  let bytes;
  if (mode === 'text') bytes = new TextEncoder().encode(value);
  else if (mode === 'hex') {
    const compact = value.replace(/\s/g, '');
    if (!/^(?:[0-9a-fA-F]{2})*$/.test(compact)) fail('hex');
    bytes = Uint8Array.from(compact.match(/../g) || [], x => parseInt(x, 16));
  } else fail('mode');
  if (bytes.length > MINIMAL_LIMIT) fail('limit');
  return bytes;
}
function checkedBytes(bytes) {
  if (!(bytes instanceof Uint8Array)) fail('Expected Uint8Array');
  if (bytes.length > MINIMAL_LIMIT) fail('Input exceeds 512 bytes');
}
export function lz77(bytes) {
  checkedBytes(bytes);
  const tokens = [];
  for (let pos = 0; pos < bytes.length;) {
    let length = 0, distance = 0;
    // Ascending distance gives the nearest source on a longest-match tie.
    for (let d = 1; d <= pos; d++) {
      let n = 0;
      while (pos + n < bytes.length && bytes[pos + n] === bytes[pos + n - d]) n++;
      if (n > length) {length = n; distance = d;}
    }
    if (length >= 3) {tokens.push({symbol:MATCH, start:pos, end:pos+length, distance, length}); pos += length;}
    else {tokens.push({symbol:bytes[pos], start:pos, end:pos+1}); pos++;}
  }
  tokens.push({symbol:END, start:bytes.length, end:bytes.length});
  return tokens;
}
/** Canonical codes use increasing (length, symbol), with ordinary MSB-first bits. */
export function canonicalBook(entries) {
  if (!entries.length || entries.length > 258) fail('Invalid alphabet count');
  const seen = new Set();
  for (const e of entries) {
    if (!Number.isInteger(e.symbol) || e.symbol < 0 || e.symbol > END || seen.has(e.symbol)) fail('Invalid or duplicate symbol');
    if (!Number.isInteger(e.length) || e.length < 1 || e.length > 32) fail('Invalid code length');
    seen.add(e.symbol);
  }
  if (!seen.has(END)) fail('Missing END code');
  const ordered = entries.map(e=>({...e})).sort((a,b)=>a.length-b.length || a.symbol-b.symbol);
  let code = 0n, previous = 0;
  for (const e of ordered) {
    code <<= BigInt(e.length - previous);
    if (code >= (1n << BigInt(e.length))) fail('Oversubscribed codebook');
    e.bits = code.toString(2).padStart(e.length, '0');
    code++; previous = e.length;
  }
  if (ordered.length === 1) {
    if (ordered[0].symbol !== END || ordered[0].length !== 1) fail('Invalid singleton codebook');
  } else if (code !== (1n << BigInt(previous))) fail('Incomplete codebook');
  return ordered.sort((a,b)=>a.symbol-b.symbol);
}
export function huffmanBook(tokens) {
  const counts = new Map();
  for (const t of tokens) counts.set(t.symbol, (counts.get(t.symbol)||0)+1);
  let serial = 0;
  const queue = [...counts].map(([symbol,weight])=>({symbol,weight,min:symbol,id:serial++}));
  const merges=[];
  const order=(a,b)=>a.weight-b.weight || a.min-b.min || a.id-b.id;
  while(queue.length>1) {
    queue.sort(order); const left=queue.shift(),right=queue.shift();
    const node={weight:left.weight+right.weight,min:Math.min(left.min,right.min),id:serial++,left,right};
    merges.push({left:left.id,right:right.id,id:node.id,weight:node.weight,leftWeight:left.weight,rightWeight:right.weight});
    queue.push(node);
  }
  const entries=[];
  const walk=(node,depth)=>{if(node.symbol!==undefined)entries.push({symbol:node.symbol,length:Math.max(1,depth),frequency:node.weight,node:node.id});else{walk(node.left,depth+1);walk(node.right,depth+1);}};
  walk(queue[0],0);
  return {book:canonicalBook(entries),merges,tree:queue[0]};
}
export function encodeMinimal(bytes) {
  checkedBytes(bytes);
  const tokens=lz77(bytes),{book,merges,tree}=huffmanBook(tokens),lookup=new Map(book.map(e=>[e.symbol,e]));
  const metadata=[bytes.length>>>8,bytes.length&255,book.length>>>8,book.length&255];
  for (const e of book) metadata.push(e.symbol>>>8,e.symbol&255,e.length);
  let bits=''; const fields=[];
  const put=(kind,value,token)=>{const start=bits.length;bits+=value;fields.push({kind,bits:value,start,end:bits.length,token});};
  tokens.forEach((token,i)=>{
    put('symbol',lookup.get(token.symbol).bits,i);
    if(token.symbol===MATCH){put('distance',token.distance.toString(2).padStart(16,'0'),i);put('length',token.length.toString(2).padStart(16,'0'),i);}
  });
  const payloadBits=bits.length,padding=(8-bits.length%8)%8;
  if(padding)put('padding','0'.repeat(padding),null);
  const payload=Uint8Array.from(bits.match(/.{8}/g)||[],x=>parseInt(x,2));
  return {input:bytes.slice(),tokens,book,merges,tree,fields,payloadBits,padding,metadata:Uint8Array.from(metadata),payload,packet:Uint8Array.from([...metadata,...payload])};
}
/** Receiver gets ONLY packet bytes; encoder tokens, tree and source are not arguments. */
export function decodeMinimal(packet) {
  if (!(packet instanceof Uint8Array)) fail('Expected packet bytes');
  let at=0;
  const byte=()=>{if(at>=packet.length)fail('Truncated metadata');return packet[at++];};
  const word=()=>byte()*256+byte();
  const rawLength=word(),count=word();
  if(rawLength>MINIMAL_LIMIT)fail('Declared output exceeds 512 bytes');
  if(count<1||count>258)fail('Invalid alphabet count');
  const entries=[];let previous=-1;
  for(let i=0;i<count;i++){
    const symbol=word(),length=byte();
    if(symbol<=previous)fail('Codebook symbols must increase');
    entries.push({symbol,length});previous=symbol;
  }
  const book=canonicalBook(entries),payloadOffset=at;
  const root={};
  for(const e of book){let node=root;for(const bit of e.bits)node=node[bit]??={};node.symbol=e.symbol;}
  let bitAt=at*8;
  const read=()=>{if(bitAt>=packet.length*8)fail('Truncated payload');const bit=(packet[bitAt>>>3]>>>(7-(bitAt&7)))&1;bitAt++;return bit;};
  const number=()=>{let value=0;for(let n=0;n<16;n++)value=value*2+read();return value;};
  const output=[],events=[];
  while(true){
    const start=bitAt-payloadOffset*8;let node=root;
    while(node.symbol===undefined){node=node[read()];if(!node)fail('Unused prefix');}
    const symbol=node.symbol,symbolEnd=bitAt-payloadOffset*8;
    if(symbol===END){events.push({kind:'end',symbol,start,end:symbolEnd,outputLength:output.length});break;}
    if(symbol===MATCH){
      const distance=number(),length=number(),end=bitAt-payloadOffset*8;
      if(distance<1||distance>output.length)fail('Invalid backward distance');
      if(length<3||output.length+length>rawLength)fail('Invalid match length');
      events.push({kind:'match',symbol,start,symbolEnd,end,distance,length,outputLength:output.length});
      for(let n=0;n<length;n++){
        const source=output.length-distance,target=output.length,value=output[source];output.push(value);
        events.push({kind:'copy',source,target,value,distance,remaining:length-n-1,start,end,outputLength:output.length});
      }
    }else{
      if(output.length>=rawLength)fail('Output exceeds declared length');
      output.push(symbol);events.push({kind:'literal',symbol,value:symbol,start,end:symbolEnd,target:output.length-1,outputLength:output.length});
    }
  }
  if(output.length!==rawLength)fail('END before declared output length');
  const usedBits=bitAt-payloadOffset*8,padding=(8-(bitAt%8))%8;
  if(packet.length*8-bitAt!==padding)fail('Trailing bytes after END');
  for(let i=0;i<padding;i++)if(read()!==0)fail('Nonzero padding');
  return {output:Uint8Array.from(output),book,events,rawLength,payloadOffset,payloadBits:usedBits,padding};
}
export function runMinimal(bytes) {
  const encoded=encodeMinimal(bytes),decoded=decodeMinimal(encoded.packet);
  const equal=decoded.output.length===bytes.length&&bytes.every((value,i)=>value===decoded.output[i]);
  return {...encoded,decoded,equal};
}
