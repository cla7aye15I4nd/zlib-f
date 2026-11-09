for(const figure of document.querySelectorAll('[data-codec-trace]')){
  const data=JSON.parse(figure.querySelector('#bk-trace-data').textContent),select=figure.querySelector('[data-trace-case]');
  const zh=document.documentElement.lang==='zh',t=(cn,en)=>zh?cn:en;
  const baseline=data.cases.find(c=>c.name==='default').compressed_bytes;
  const max=Math.max(data.input.bytes,...data.cases.map(c=>c.compressed_bytes));
  const set=(key,value)=>figure.querySelector(`[data-trace-${key}]`).textContent=value;
  const update=()=>{
    const c=data.cases.find(c=>c.name===select.value),d=c.deflate_init,delta=c.compressed_bytes-baseline;
    set('compressed',c.compressed_bytes.toLocaleString());
    set('block',({stored:t('原样存储','Stored'),fixed:t('固定编码','Fixed codes'),dynamic:t('动态编码','Dynamic codes')})[c.first_block.type]);
    set('difference',(delta>0?'+':'')+delta.toLocaleString()+t(' 字节',' bytes'));
    set('calls',`${c.deflate_calls} / ${c.inflate_calls}`);
    set('settings',`level ${d.level} · windowBits ${d.window_bits} · memLevel ${d.memory_level} · strategy ${d.strategy} · inflate windowBits ${c.inflate_init.window_bits}`);
    figure.querySelector('[data-trace-bar]').style.width=(100*c.compressed_bytes/max)+'%';
  };
  select.addEventListener('change',update);update();
}
