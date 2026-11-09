/** Complete, explicitly selected record streams measured with unmodified trees.c
 * at zlib commit 757f0527154291bcf6bfbd6396ecde6bedd2db95 (level 6,
 * memLevel 8, packed layout). Counts include END_BLOCK; description includes
 * HLIT/HDIST/HCLEN, raw code-length widths, run codes and their extra bits.
 * These are internal record traces, not default match-selection predictions.
 */
export const BLOCK_CASES = Object.freeze([
  {id:'match',bytes:8,fixed:35,payload:9,description:116},
  {id:'short',bytes:16,fixed:135,payload:34,description:111},
  {id:'repeat',bytes:256,fixed:2055,payload:484,description:111},
  {id:'broad',bytes:256,fixed:2167,payload:2058,description:214},
].map(Object.freeze));
export const pad8 = bits => (8 - bits % 8) % 8;
export function blockCandidates(example,{offset=0,fixed=false,raw=true}={}) {
  if(!Number.isInteger(offset)||offset<0||offset>7)throw new RangeError('bit offset must be 0–7');
  const dynamic = example.payload+example.description;
  const fixedEstimate = Math.ceil((example.fixed+3)/8);
  const dynamicEstimate = Math.ceil((dynamic+3)/8);
  const compressed = fixed||fixedEstimate<=dynamicEstimate?'fixed':'dynamic';
  const estimate = compressed==='fixed'?fixedEstimate:dynamicEstimate;
  const storedEligible=raw&&example.bytes<=65535;
  const selected=storedEligible&&example.bytes+4<=estimate?'stored':compressed;
  const rows=[
    {kind:'stored',header:3,description:32,payload:8*example.bytes,padding:pad8(offset+3),eligible:storedEligible,estimate:example.bytes+4},
    {kind:'fixed',header:3,description:0,payload:example.fixed,padding:pad8(offset+3+example.fixed),eligible:true,estimate:fixedEstimate},
    {kind:'dynamic',header:3,description:example.description,payload:example.payload,padding:pad8(offset+3+dynamic),eligible:!fixed,estimate:dynamicEstimate},
  ].map(row=>({...row,
    // Stored padding follows its header; final compressed padding follows EOB.
    order:row.kind==='stored'?['header','padding','description','payload']:['header','description','payload','padding'],
    total:row.header+row.description+row.payload+row.padding}));
  return {selected,compressed,estimate,rows};
}
