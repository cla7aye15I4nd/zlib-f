const legacy=document.getElementById('bk-legacy-links');
if(legacy&&location.hash){
  const route=JSON.parse(legacy.textContent)[decodeURIComponent(location.hash.slice(1))];
  if(route)location.replace(new URL(route,location.href));
}
if(location.hash){
  const initialHash=location.hash;
  Promise.all([document.fonts.ready,customElements.whenDefined('zlib-demo')]).then(()=>{
    if(location.hash===initialHash)requestAnimationFrame(()=>{
      document.getElementById(decodeURIComponent(initialHash.slice(1)))?.scrollIntoView({behavior:'instant'});
    });
  });
}
const chapters=[...document.querySelectorAll('.bk-article h2[id]')];
const sectionLinks=[...document.querySelectorAll('.bk-global-dialog .toc a[href^="#"]')];
if(chapters.length&&sectionLinks.length){
  let scheduled=false;
  const update=()=>{
    scheduled=false;let current=chapters[0].id;
    for(const heading of chapters){if(heading.getBoundingClientRect().top<=150)current=heading.id;else break;}
    for(const a of sectionLinks){if(a.hash==='#'+current)a.setAttribute('aria-current','location');else a.removeAttribute('aria-current');}
  };
  addEventListener('scroll',()=>{if(!scheduled){scheduled=true;requestAnimationFrame(update);}},{passive:true});
  update();
}

for(const language of document.querySelectorAll("[data-language]")){language.addEventListener("click",()=>{let current=null;for(const heading of document.querySelectorAll(".bk-article h2[id],.bk-article h3[id]")){if(heading.getBoundingClientRect().top<=150)current=heading;else break;}const target=new URL(language.href);target.hash=current?.id||location.hash;language.href=target.href;});}
