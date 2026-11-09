import {mountCopy} from './zlib-copy.js?v=zh-2';
import {mountSearch} from './zlib-search.js';
import {mountLookup} from './zlib-lookup.js?v=zh-2';
import {mountOverlay} from './zlib-overlay.js?v=zh-2';
import {mountTableProof} from './zlib-table-proof.js';
import {mountHuffman,mountOwnership} from './zlib-basic.js?v=zh-2';
import {mountStream} from './zlib-stream.js?v=zh-2';
import {mountWindow} from './zlib-window.js?v=2';
import {mountWriter} from './zlib-writer.js?v=zh-2';
import {mountAdler,mountCrc} from './zlib-checksums.js';
import {mountRoundtrip} from './zlib-roundtrip-scene.js?v=reader-1';
import {mountRefill} from './zlib-refill-scene.js?v=reader-1';
import {mountBlockcost} from './zlib-blockcost-scene.js?v=reader-1';
import {mountLengths} from './zlib-lengths-scene.js?v=reader-1';
import {mountFastpath} from './zlib-fastpath-scene.js?v=reader-1';
import {mountCheckpoint} from './zlib-checkpoint-scene.js?v=reader-1';
import {mountPlayground} from './zlib-playground.js?v=reader-1';

const mounts={copy:mountCopy,window:mountWindow,search:mountSearch,huffman:mountHuffman,lookup:mountLookup,stream:mountStream,overlay:mountOverlay,'table-proof':mountTableProof,ownership:mountOwnership,writer:mountWriter,adler:mountAdler,crc:mountCrc,roundtrip:mountRoundtrip,refill:mountRefill,blockcost:mountBlockcost,lengths:mountLengths,fastpath:mountFastpath,checkpoint:mountCheckpoint,playground:mountPlayground};
const titles={
  playground:['换一份输入，运行真正的 C 程序','Change the input and run the actual C program'],
  roundtrip:['同一份原文的三种表示','Three representations of the same original'],
  refill:['字节换了地址，内容与距离保持对应','New addresses, the same bytes and distances'],
  blockcost:['把描述成本也算进去','Include the cost of the description'],
  lengths:['一条描述，展开多个码长','One description expands into several lengths'],
  fastpath:['先检查整条指令需要的空间','Check room for a whole instruction first'],
  checkpoint:['从一个检查点继续、重置或复制','Continue, reset or copy a checkpoint'],
  copy:['逐字节扩展历史','Grow history, one byte at a time'],
  window:['从重复片段到滑动窗口','From repetition to a sliding window'],
  search:['沿候选链寻找匹配','Follow the candidate chain'],
  huffman:['短码怎样占用编码空间','How short codes occupy code space'],
  lookup:['查看，不等于消耗','Inspecting is not consuming'],
  stream:['小缓冲区，多次取回同一份结果','A small buffer, one result across calls'],
  overlay:['最终容量与沿途的边界','Final capacity, intermediate boundaries'],
  'table-proof':['相同的访问，不同的答案','The same access. A different answer.'],
  ownership:['资源的整个生命周期','A resource’s whole lifetime'],
  writer:['从六个字段到五个字节','Six fields become five bytes'],
  adler:['两个累加量逐字节前进','Two running sums, one byte at a time'],
  crc:['八次逐位更新与一次查表','Eight bit updates, one table lookup'],
};
class ZlibDemo extends HTMLElement {
  connectedCallback(){
    if(this.ready)return;this.ready=true;this.timer=null;
    this.lang=document.documentElement.lang==='en'?'en':'zh';
    this.t=(zh,en)=>this.lang==='en'?en:zh;
    this.abort=new AbortController();
    const kind=this.getAttribute('kind'),title=titles[kind];
    if(!mounts[kind])return;
    this.innerHTML=`<div class="zl-demo-head"><span>${this.t('动手试试','TRY IT')}</span><strong>${this.t(...title)}</strong><span class="zl-demo-mark" aria-hidden="true">↗</span></div><div class="zl-controls"></div><div class="zl-view"></div><output class="zl-status" aria-live="polite"></output>`;
    this.controls=this.querySelector('.zl-controls');this.view=this.querySelector('.zl-view');this.status=this.querySelector('.zl-status');
    mounts[kind](this);
  }
  on(node,event,fn){node.addEventListener(event,fn,{signal:this.abort.signal});}
  stop(){clearInterval(this.timer);this.timer=null;const b=this.querySelector('[data-play]');if(b)b.textContent=this.t('播放','Play');}
  disconnectedCallback(){this.stop();this.abort?.abort();this.ready=false;}
}
if(!customElements.get('zlib-demo'))customElements.define('zlib-demo',ZlibDemo);

function arrangeEssay(){
  const body=document.querySelector('.article-body');if(!body||body.dataset.arranged)return;
  body.dataset.arranged='true';
  for(const kind of ['copy','lookup']){
    const demo=body.querySelector(`zlib-demo[kind="${kind}"]`),mount=demo?.closest('.zl-demo-mount');
    if(!mount)continue;
    let heading=mount.previousElementSibling;
    while(heading&&heading.tagName!==(body.dataset.overview?'H2':'H3'))heading=heading.previousElementSibling;
    if(!heading)continue;
    const nodes=[];let node=heading;
    while(node){if(node!==heading&&['H2','H3'].includes(node.tagName))break;nodes.push(node);node=node.nextElementSibling;}
    const section=document.createElement('section');section.className='zl-scene';section.dataset.kind=kind;
    section.setAttribute('aria-labelledby',heading.id);
    const text=document.createElement('div');text.className='zl-scene-text';
    const after=document.createElement('div');after.className='zl-scene-after';
    const visual=document.createElement('div');visual.className='zl-scene-visual';
    heading.before(section);section.append(text,visual,after);
    let passedDemo=false;
    for(const child of nodes){if(child===mount){visual.append(child);passedDemo=true;}else (passedDemo?after:text).append(child);}
  }
  for(const kind of ['overlay','stream','huffman','window','search']){
    const mount=body.querySelector(`zlib-demo[kind="${kind}"]`)?.closest('.zl-demo-mount');
    mount?.classList.add(kind==='huffman'?'zl-mediumwidth':'zl-fullwidth',`zl-${kind}-wide`);
  }
  const headings=[...body.querySelectorAll('h2,h3')];
  let currentId='how-zlib-works',scheduled=false;
  const progress=document.querySelector('.zl-progress i');
  const update=()=>{
    scheduled=false;let current=headings[0];
    for(const heading of headings){if(heading.getBoundingClientRect().top<=150)current=heading;else break;}
    currentId=current?.id||'how-zlib-works';
    const rect=body.getBoundingClientRect(),ratio=Math.max(0,Math.min(1,(-rect.top+150)/(rect.height-window.innerHeight+150)));
    if(progress)progress.style.transform=`scaleX(${ratio})`;
  };
  window.addEventListener('scroll',()=>{if(!scheduled){scheduled=true;requestAnimationFrame(update);}},{passive:true});
  const contents=document.querySelector('.zl-contents');
  contents?.querySelectorAll('a').forEach(a=>a.addEventListener('click',()=>contents.open=false));
  document.querySelectorAll('[data-language]').forEach(a=>a.addEventListener('click',()=>{update();const url=new URL(a.href);url.hash=currentId;a.href=url.href;}));
  update();
  if(location.hash){
    const settle=()=>requestAnimationFrame(()=>document.getElementById(decodeURIComponent(location.hash.slice(1)))?.scrollIntoView({behavior:'instant'}));
    if(document.fonts)document.fonts.ready.then(settle);else settle();
  }
}
const boot=()=>{customElements.upgrade(document);arrangeEssay();};
if(document.readyState==='loading')document.addEventListener('DOMContentLoaded',boot,{once:true});else boot();
window.addEventListener('pageshow',boot);
window.addEventListener('spa:navigation',boot);
