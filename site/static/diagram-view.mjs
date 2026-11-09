export function diagramBox(svg) {
  const box=(svg.getAttribute('viewBox')||'').trim().split(/[\s,]+/).map(Number);
  if(box.length===4&&box.every(Number.isFinite)&&box[2]>0&&box[3]>0)
    return {width:Math.ceil(box[2]),height:Math.ceil(box[3])};
  const width=Number.parseFloat(svg.getAttribute('width'));
  const height=Number.parseFloat(svg.getAttribute('height'));
  if(Number.isFinite(width)&&Number.isFinite(height)&&width>0&&height>0)
    return {width:Math.ceil(width),height:Math.ceil(height)};
  throw new Error('Diagram has no finite drawing area');
}

export function diagramScale(requested) {
  return Math.max(.8,Math.min(2.5,Number.isFinite(requested)?requested:1));
}

export function mountDiagramView(figure,en=false) {
  const svg=figure.querySelector('.mermaid svg');
  if(!svg)throw new Error('Diagram did not produce an SVG');
  if(figure.dataset.diagramReady)return;
  const {width,height}=diagramBox(svg);
  const viewport=figure.querySelector('.rf-diagram-scroll');
  const canvas=figure.querySelector('.rf-diagram-canvas');
  const visual=figure.querySelector('.mermaid');
  const t=(zh,english)=>en?english:zh;
  const toolbar=document.createElement('div');toolbar.className='rf-diagram-controls';
  toolbar.innerHTML=`<span>${t('关系图','Relationship diagram')}</span><div role="group" aria-label="${t('图形缩放','Diagram zoom')}"><button type="button" data-diagram-zoom="out" aria-label="${t('缩小图形','Zoom out')}">−</button><output aria-label="${t('缩放比例','Zoom level')}">100%</output><button type="button" data-diagram-zoom="in" aria-label="${t('放大图形','Zoom in')}">＋</button><button type="button" data-diagram-zoom="reset">${t('原始大小','Actual size')}</button></div>`;
  figure.prepend(toolbar);
  const hint=document.createElement('p');hint.className='rf-diagram-hint';
  hint.textContent=t('可滚动查看完整关系，也可用 Tab 进入图内后按方向键移动。','Scroll to inspect the complete diagram, or focus it with Tab and use the arrow keys.');
  viewport.after(hint);
  let scale=1;
  svg.style.maxWidth='none';svg.style.width=`${width}px`;svg.style.height=`${height}px`;
  visual.style.width=`${width}px`;visual.style.height=`${height}px`;
  const render=()=>{
    canvas.style.width=`${Math.ceil(width*scale)}px`;canvas.style.height=`${Math.ceil(height*scale)}px`;
    visual.style.transform=`scale(${scale})`;
    toolbar.querySelector('output').textContent=Math.round(scale*100)+'%';
    toolbar.querySelector('[data-diagram-zoom="out"]').disabled=scale<=.8;
    toolbar.querySelector('[data-diagram-zoom="in"]').disabled=scale>=2.5;
  };
  toolbar.addEventListener('click',event=>{
    const button=event.target.closest('[data-diagram-zoom]');if(!button)return;
    const centerX=(viewport.scrollLeft+viewport.clientWidth/2)/scale;
    const centerY=(viewport.scrollTop+viewport.clientHeight/2)/scale;
    scale=diagramScale(button.dataset.diagramZoom==='reset'?1:scale+(button.dataset.diagramZoom==='in'?.2:-.2));
    render();viewport.scrollLeft=Math.max(0,centerX*scale-viewport.clientWidth/2);viewport.scrollTop=Math.max(0,centerY*scale-viewport.clientHeight/2);
  });
  figure.dataset.diagramReady='true';render();
}
