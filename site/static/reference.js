// Search uses the complete, statically rendered contract text. No backend is needed.
function initSearch(){
  const input=document.getElementById('api-search');if(!input)return;
  const group=document.getElementById('api-group'),scope=document.getElementById('api-scope');
  const rows=[...document.querySelectorAll('.rf-api-row')],count=document.getElementById('api-count');
  const en=document.documentElement.lang==='en';
  const params=new URLSearchParams(location.search);
  if([...group.options].some(option=>option.value===params.get('group')))group.value=params.get('group');
  if(params.has('q'))input.value=params.get('q');
  const update=()=>{
    const words=input.value.trim().toLocaleLowerCase().split(/\s+/).filter(Boolean);let visible=0;
    for(const row of rows){
      const show=(!group.value||row.dataset.group===group.value)&&(!scope.value||row.dataset.scope===scope.value)&&words.every(word=>row.dataset.search.toLocaleLowerCase().includes(word));
      row.hidden=!show;if(show)visible++;
    }
    count.textContent=en?`${visible} entries`:`${visible} 个条目`;
    document.getElementById('api-empty').hidden=visible>0;
  };
  input.addEventListener('input',update);group.addEventListener('change',update);scope.addEventListener('change',update);
  update();
}

function initLanguage(){
  document.querySelectorAll('[data-language]').forEach(link=>link.addEventListener('click',()=>{
    const target=new URL(link.href);target.hash=location.hash;link.href=target.href;
  }));
}

let library;
function mermaidLibrary(){
  if(!library)library=new Promise((resolve,reject)=>{
    const script=document.createElement('script');
    script.src=new URL('./vendor/mermaid-12.2.0.js',document.currentScript?.src||new URL('reference.js',document.querySelector('script[src*="reference.js"]').src)).href;
    script.onload=async()=>{
      await document.fonts.ready;
      window.mermaid.initialize({startOnLoad:false,securityLevel:'strict',theme:'base',
        fontFamily:'NanSans, PingFang SC, Microsoft YaHei, sans-serif',htmlLabels:false,
        themeVariables:{fontFamily:'NanSans, PingFang SC, Microsoft YaHei, sans-serif',fontSize:'15px',primaryColor:'#e7e7e7',primaryTextColor:'#333333',primaryBorderColor:'#b3b3b3',lineColor:'#7b7b7b',secondaryColor:'#dadada',tertiaryColor:'#ededed'},
        flowchart:{htmlLabels:false,curve:'linear',useMaxWidth:false,wrappingWidth:220,nodeSpacing:36,rankSpacing:48,padding:20}});
      resolve(window.mermaid);
    };
    script.onerror=reject;document.head.append(script);
  });
  return library;
}

function initDiagrams(){
  const blocks=[...document.querySelectorAll('pre > code.language-mermaid')];if(!blocks.length)return;
  const en=document.documentElement.lang==='en';
  const observer=new IntersectionObserver(entries=>{
    for(const entry of entries){
      if(!entry.isIntersecting)continue;observer.unobserve(entry.target);
      const node=entry.target.querySelector('.mermaid');
      const rendererURL=new URL(document.querySelector('script[src*="reference.js"]').src);
      const viewURL=new URL('./diagram-view.mjs',rendererURL);viewURL.search=rendererURL.search;
      Promise.all([mermaidLibrary(),import(viewURL.href)])
        .then(async([lib,view])=>{
          await lib.run({nodes:[node],suppressErrors:false});
          view.mountDiagramView(entry.target,en);
        }).catch(()=>{entry.target.querySelector('.rf-diagram-source').open=true;});
    }
  },{rootMargin:'250px'});
  blocks.forEach(code=>{
    const figure=document.createElement('figure');figure.className='rf-diagram';
    const visual=document.createElement('div');visual.className='mermaid';visual.textContent=code.textContent;
    const viewport=document.createElement('div');viewport.className='rf-diagram-scroll';viewport.tabIndex=0;
    viewport.setAttribute('role','region');viewport.setAttribute('aria-label',en?'Relationship diagram; scroll to inspect all nodes':'关系图，可滚动查看全部节点');
    const canvas=document.createElement('div');canvas.className='rf-diagram-canvas';canvas.append(visual);viewport.append(canvas);
    const details=document.createElement('details');details.className='rf-diagram-source';
    const summary=document.createElement('summary');summary.textContent=en?'Diagram source':'图示源码';
    const source=document.createElement('pre');source.textContent=code.textContent;
    details.append(summary,source);figure.append(viewport,details);code.parentElement.replaceWith(figure);observer.observe(figure);
  });
}

initSearch();initLanguage();initDiagrams();
