// All targets and links are built into the page; filtering changes only visibility.
for (const map of document.querySelectorAll('[data-progress-map]')) {
  const controls=map.querySelector('[data-progress-controls]');
  const search=map.querySelector('[data-progress-search]');
  const group=map.querySelector('[data-progress-group]');
  const status=map.querySelector('[data-progress-status]');
  const sections=[...map.querySelectorAll('[data-progress-group-section]')];
  const count=map.querySelector('[data-progress-count]');
  const en=document.documentElement.lang==='en';
  controls.hidden=false;
  const update=()=>{
    const words=search.value.toLowerCase().trim().split(/\s+/).filter(Boolean);
    const filtered=words.length||group.value||status.value;
    let visible=0;
    for(const section of sections){
      let members=0;
      for(const row of section.querySelectorAll('[data-progress-row]')){
        const show=(!group.value||section.dataset.progressGroupSection===group.value)&&(!status.value||row.dataset.progressState===status.value)&&words.every(w=>row.dataset.progressName.includes(w));
        row.hidden=!show;
        if(show){members++;visible++;}
      }
      section.hidden=!members;
      if(filtered&&members)section.open=true;
    }
    count.textContent=en?`${visible} matching targets`:`${visible} 项匹配目标`;
    map.querySelector('[data-progress-empty]').hidden=visible!==0;
  };
  const reveal=element=>{
    if(!element||!map.contains(element))return;
    search.value='';status.value='';group.value='';update();
    for(let ancestor=element;ancestor&&ancestor!==map;ancestor=ancestor.parentElement){
      if(ancestor instanceof HTMLDetailsElement)ancestor.open=true;
    }
  };
  const hashTarget=()=>{
    if(!location.hash.startsWith('#pg-'))return;
    reveal(document.getElementById(decodeURIComponent(location.hash.slice(1))));
  };
  map.addEventListener('click',event=>{
    const link=event.target.closest('[data-progress-open],[data-progress-target-link]');
    if(link)reveal(document.getElementById(link.hash.slice(1)));
  });
  search.addEventListener('input',update);group.addEventListener('change',update);status.addEventListener('change',update);
  map.querySelector('[data-progress-reset]').addEventListener('click',()=>{
    search.value='';group.value='';status.value='';update();
    for(const section of sections)section.open=false;
  });
  window.addEventListener('hashchange',hashTarget);
  update();hashTarget();
}

// HTML nodes keep their labels readable; SVG draws only directed connections.
for(const graph of document.querySelectorAll('[data-dependency-graph]')){
  const data=JSON.parse(graph.querySelector('[data-progress-graph-data]').textContent);
  const map=graph.closest('[data-progress-map]');
  const targets=new Map(data.targets.map(t=>[t.id,t]));
  const groups=new Map(data.groups.map(g=>[g.id,g]));
  const viewport=graph.querySelector('[data-graph-scroll]');
  const size=graph.querySelector('[data-graph-size]');
  const canvas=graph.querySelector('[data-graph-canvas]');
  const overview=graph.querySelector('[data-graph-groups]');
  const focus=graph.querySelector('[data-graph-focus]');
  const picker=graph.querySelector('[data-graph-picker]');
  const detail=graph.querySelector('[data-graph-detail]');
  const instruction=graph.querySelector('[data-graph-instruction]');
  const en=document.documentElement.lang==='en';
  const T=(zh,enText)=>en?enText:zh;
  const svgNS='http://www.w3.org/2000/svg';
  let mode='groups',selected=picker.value||data.targets[0].id,scale=1,width=1230,height=730;
  graph.querySelector('[data-graph-toolbar]').hidden=false;
  function element(tag,cls,text){const e=document.createElement(tag);if(cls)e.className=cls;if(text!==undefined)e.textContent=text;return e;}
  function svgElement(tag,attrs){const e=document.createElementNS(svgNS,tag);for(const [k,v] of Object.entries(attrs))e.setAttribute(k,v);return e;}
  function applyScale(){
    canvas.style.transform=`scale(${scale})`;
    size.style.width=`${width*scale}px`;size.style.height=`${height*scale}px`;
    viewport.classList.toggle('can-pan',width*scale>viewport.clientWidth+1);
  }
  function mark(key){
    const nodes=mode==='groups'?[...overview.querySelectorAll('[data-graph-group]')]:[...focus.querySelectorAll('[data-graph-target-node]')];
    const edges=[...(mode==='groups'?overview:focus).querySelectorAll('[data-graph-edge]')];
    const connected=new Set(key?[key]:[]);
    for(const edge of edges){
      const related=key&&(edge.dataset.from===key||edge.dataset.to===key);
      if(related){connected.add(edge.dataset.from);connected.add(edge.dataset.to);}
      edge.classList.toggle('is-muted',!!key&&!related);edge.classList.toggle('is-related',!!related);
    }
    for(const node of nodes){const id=node.dataset.graphGroup||node.dataset.graphTargetNode;node.classList.toggle('is-muted',!!key&&!connected.has(id));node.classList.toggle('is-related',!!key&&connected.has(id));}
  }
  function targetButton(id,center=false){
    const target=targets.get(id),button=element('button','pg-focus-node'+(center?' is-selected':''));
    button.type='button';button.dataset.graphTargetNode=id;
    button.append(element('code','',target.name),element('span','pg-badge pg-'+target.status,target.statusLabel));
    if(center)button.setAttribute('aria-current','true');
    return button;
  }
  function renderTarget(){
    const target=targets.get(selected),incoming=data.edges.filter(e=>e.to===selected),outgoing=data.edges.filter(e=>e.from===selected);
    focus.replaceChildren();
    const svg=svgElement('svg',{class:'pg-focus-edges','aria-hidden':'true'}),defs=svgElement('defs',{});
    for(const kind of ['proof','call']){
      const marker=svgElement('marker',{id:`pg-focus-${kind}-arrow`,viewBox:'0 0 10 10',refX:'9',refY:'5',markerWidth:'7',markerHeight:'7',orient:'auto'});
      marker.append(svgElement('path',{d:'M1 1 L9 5 L1 9 Z'}));defs.append(marker);
    }
    svg.append(defs);focus.append(svg);
    const columns=[
      [T('依赖的目标','Targets used here'),[...new Set(incoming.map(e=>e.from))]],
      [T('当前目标','Selected target'),[selected]],
      [T('使用它的目标','Targets using it'),[...new Set(outgoing.map(e=>e.to))]],
    ];
    for(let i=0;i<columns.length;i++){
      const col=element('div','pg-focus-column'),list=element('div','pg-focus-nodes');
      col.append(element('h4','',columns[i][0]),list);
      for(const id of columns[i][1]){const button=targetButton(id,i===1);button.dataset.graphColumn=i;list.append(button);}
      if(!columns[i][1].length)list.append(element('p','pg-focus-none',T('没有记录直接关系','No recorded direct connection')));
      focus.append(col);
    }
    const vertical=viewport.clientWidth<600;focus.classList.toggle('is-vertical',vertical);
    width=vertical?Math.max(300,viewport.clientWidth):1050;focus.style.width=width+'px';canvas.style.width=`${width}px`;canvas.style.transform='none';focus.hidden=false;overview.hidden=true;
    height=focus.offsetHeight;canvas.style.height=`${height}px`;
    svg.setAttribute('viewBox',`0 0 ${width} ${height}`);
    const base=focus.getBoundingClientRect();
    const box=(id,col)=>focus.querySelector(`[data-graph-target-node="${id}"][data-graph-column="${col}"]`).getBoundingClientRect();
    for(const edge of [...incoming,...outgoing]){
      const left=edge.to===selected?box(edge.from,0):box(selected,1);
      const right=edge.to===selected?box(selected,1):box(edge.to,2);
      const pairBoth=data.edges.some(other=>other.from===edge.from&&other.to===edge.to&&other.kind!==edge.kind);
      const offset=pairBoth?(edge.kind==='proof'?-7:7):0;
      let path;
      if(vertical){
        if(edge.to===selected){
          const rail=10+incoming.indexOf(edge)*20/Math.max(1,incoming.length-1),x1=left.left-base.left,y1=left.top+left.height/2-base.top,x2=right.left+right.width/2-base.left,y2=right.top-base.top-4;
          path=`M${x1},${y1} H${rail} V${y2-18} Q${rail},${y2-12} ${rail+6},${y2-12} H${x2-6} Q${x2},${y2-12} ${x2},${y2-6} V${y2}`;
        }else{
          const rail=width-(edge.kind==='proof'?12:20),x1=left.right-base.left,y1=left.top+left.height/2-base.top,x2=right.right-base.left+4,y2=right.top+right.height/2-base.top;
          path=`M${x1},${y1} H${rail} V${y2} H${x2}`;
        }
      }else{
        const x1=left.right-base.left,y1=left.top+left.height/2-base.top+offset,x2=right.left-base.left-4,y2=right.top+right.height/2-base.top+offset,middle=(x1+x2)/2;
        path=`M${x1},${y1} C${middle},${y1} ${middle},${y2} ${x2},${y2}`;
      }
      const edgeGroup=svgElement('g',{class:`pg-diagram-edge pg-edge-${edge.kind}`,'data-graph-edge':'','data-from':edge.from,'data-to':edge.to});
      edgeGroup.append(svgElement('path',{d:path,'marker-end':`url(#pg-focus-${edge.kind}-arrow)`}));svg.append(edgeGroup);
    }
    detail.replaceChildren(element('strong','',target.name),element('span','',groups.get(target.group).label+' · '+target.statusLabel+' · '+incoming.length+T(' 条上游关系',' upstream connection'+(incoming.length===1?'':'s'))+' · '+outgoing.length+T(' 条下游关系',' downstream connection'+(outgoing.length===1?'':'s'))));
    const evidence=element('a','',T('展开目标证据','Open target evidence')+' ↗');evidence.href='#pg-'+target.id;evidence.dataset.progressTargetLink='';detail.append(evidence);
    instruction.textContent=T('箭头从上游指向当前目标，再指向下游。点击相邻节点继续查看；可缩放，放大后可左右拖动。','Arrows run from upstream targets through the selection to downstream targets. Select a neighbor to continue; zoom in to pan sideways.');
  }
  function render(){
    for(const b of graph.querySelectorAll('[data-graph-mode]'))b.setAttribute('aria-pressed',String(b.dataset.graphMode===mode));
    if(mode==='target')renderTarget();
    else{
      overview.hidden=false;focus.hidden=true;width=1230;height=730;canvas.style.width=width+'px';canvas.style.height=height+'px';
      detail.replaceChildren(element('p','',T('悬停或聚焦节点可突出相连的路径。点击组件，进入具体目标的依赖图。','Hover or focus a node to highlight connected paths. Select a component to inspect actual target dependencies.')));
      instruction.textContent=T('从左向右看依赖。连线数字是跨组件关系条数；节点内列出组件内部关系。点击节点查看具体目标。','Read dependencies from left to right. Edge numbers count connections between components; nodes count internal connections. Select a node to inspect actual targets.');
    }
    applyScale();
    mark(null);
  }
  function choose(id){if(!targets.has(id))return;const wasGroups=mode==='groups';selected=id;picker.value=id;mode='target';if(wasGroups)scale=1;render();viewport.scrollLeft=Math.max(0,width*scale/2-viewport.clientWidth/2);focus.querySelector('[aria-current]')?.focus({preventScroll:true});viewport.scrollIntoView({block:'start',behavior:matchMedia('(prefers-reduced-motion: reduce)').matches?'auto':'smooth'});}
  graph.addEventListener('click',event=>{
    const modeButton=event.target.closest('[data-graph-mode]');
    if(modeButton){mode=modeButton.dataset.graphMode;scale=1;render();viewport.scrollLeft=mode==='groups'?0:Math.max(0,width*scale/2-viewport.clientWidth/2);return;}
    const component=event.target.closest('[data-graph-group]');
    if(component){
      event.preventDefault();const members=data.targets.filter(t=>t.group===component.dataset.graphGroup);
      const primary=members.find(t=>t.name===component.dataset.graphGroup)||[...members].sort((a,b)=>data.edges.filter(e=>e.from===b.id||e.to===b.id).length-data.edges.filter(e=>e.from===a.id||e.to===a.id).length)[0];
      choose(primary.id);return;
    }
    const neighbor=event.target.closest('[data-graph-target-node]');if(neighbor){choose(neighbor.dataset.graphTargetNode);return;}
    const zoom=event.target.closest('[data-graph-zoom]');
    if(zoom){const center=(viewport.scrollLeft+viewport.clientWidth/2)/scale;scale=zoom.dataset.graphZoom==='reset'?1:Math.max(.8,Math.min(2.5,scale+(zoom.dataset.graphZoom==='in'?.15:-.15)));applyScale();viewport.scrollLeft=Math.max(0,center*scale-viewport.clientWidth/2);}
  });
  for(const [eventName,clear] of [['pointerover',false],['focusin',false],['pointerout',true],['focusout',true]])graph.addEventListener(eventName,event=>{
    const node=event.target.closest('[data-graph-group],[data-graph-target-node]');if(!node||node.contains(event.relatedTarget))return;
    mark(clear?null:node.dataset.graphGroup||node.dataset.graphTargetNode);
  });
  picker.addEventListener('change',()=>choose(picker.value));
  let drag=null;
  viewport.addEventListener('pointerdown',event=>{
    if(event.pointerType==='touch'||event.button!==0||event.target.closest('button,a,select')||!viewport.classList.contains('can-pan'))return;
    drag={x:event.clientX,left:viewport.scrollLeft};viewport.setPointerCapture(event.pointerId);viewport.classList.add('is-dragging');
  });
  viewport.addEventListener('pointermove',event=>{if(drag){viewport.scrollLeft=drag.left+drag.x-event.clientX;event.preventDefault();}});
  const stopDrag=()=>{drag=null;viewport.classList.remove('is-dragging');};
  viewport.addEventListener('pointerup',stopDrag);viewport.addEventListener('pointercancel',stopDrag);

  map.addEventListener('click',event=>{const link=event.target.closest('[data-graph-target]');if(link)choose(link.dataset.graphTarget);});
  let lastWidth=0;
  const resized=()=>{if(lastWidth===viewport.clientWidth)return;lastWidth=viewport.clientWidth;render();};
  if(typeof ResizeObserver!=='undefined')new ResizeObserver(resized).observe(viewport);else window.addEventListener('resize',resized);
  document.fonts.ready.then(render);
  render();
}
