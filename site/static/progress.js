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
