import {mountCopy} from './zlib-copy.js';
import {mountSearch} from './zlib-search.js';
import {mountLookup} from './zlib-lookup.js';
import {mountOverlay} from './zlib-overlay.js';
import {mountTableProof} from './zlib-table-proof.js';
import {mountHuffman,mountStream,mountOwnership} from './zlib-basic.js';
import {mountWriter} from './zlib-writer.js';
import {mountAdler,mountCrc} from './zlib-checksums.js';

const mounts={copy:mountCopy,search:mountSearch,huffman:mountHuffman,lookup:mountLookup,stream:mountStream,overlay:mountOverlay,'table-proof':mountTableProof,ownership:mountOwnership,writer:mountWriter,adler:mountAdler,crc:mountCrc};
const titles={
  copy:['逐字节扩展历史','Grow history, one byte at a time'],
  search:['沿候选链寻找匹配','Follow the candidate chain'],
  huffman:['短码怎样占用编码空间','How short codes occupy code space'],
  lookup:['查看，不等于消耗','Inspecting is not consuming'],
  stream:['容器换了，历史继续','New buffers. The same history.'],
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
  for(const kind of ['copy','search','lookup']){
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
  for(const kind of ['overlay','stream','huffman']){
    const mount=body.querySelector(`zlib-demo[kind="${kind}"]`)?.closest('.zl-demo-mount');
    mount?.classList.add(kind==='huffman'?'zl-mediumwidth':'zl-fullwidth',`zl-${kind}-wide`);
  }
  const parts=[...body.querySelectorAll('#how-zlib-works,#verifying-zlib')];
  parts.forEach((p,i)=>p.dataset.part=i===0?'01 / ALGORITHM':'02 / VERIFICATION');
  const headings=[...body.querySelectorAll('h2,h3')];
  let currentId='how-zlib-works',scheduled=false;
  const links=[...document.querySelectorAll('[data-part-link]')];
  const progress=document.querySelector('.zl-progress i');
  const update=()=>{
    scheduled=false;let current=headings[0];
    for(const heading of headings){if(heading.getBoundingClientRect().top<=150)current=heading;else break;}
    currentId=current?.id||'how-zlib-works';
    const second=(document.getElementById('verifying-zlib')?.getBoundingClientRect().top??Infinity)<=150;
    links.forEach(link=>link.classList.toggle('active',link.dataset.partLink===(second?'2':'1')));
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
