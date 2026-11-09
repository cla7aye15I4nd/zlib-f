import {BLOCK_CASES,blockCandidates} from './zlib-blockcost-model.mjs';

export function mountBlockcost(host){
  const T=host.t;
  let index=0,stage=0;
  const names={stored:T('原样存储','Stored'),fixed:T('固定编码','Fixed'),dynamic:T('动态编码','Dynamic')};
  const cases=[T('A、B、向后 2 字节复制 6 字节','A, B, copy 6 bytes from distance 2'),T('16 个字面量：A×8 B×4 C×2 D×2','16 literals: A×8 B×4 C×2 D×2'),T('A×8 B×4 C×2 D×2，重复 16 次','A×8 B×4 C×2 D×2, repeated 16 times'),T('256 个字面量：字节 0–255','256 literals: bytes 0–255')];
  host.controls.innerHTML=`<label>${T('选定的完整指令流','Complete selected instruction stream')}<select data-case>${cases.map((s,i)=>`<option value="${i}">${s}</option>`).join('')}</select></label><label class="zbc-check"><input type="checkbox" data-fixed>${T('只允许固定或原样（Z_FIXED）','Allow fixed or stored only (Z_FIXED)')}</label><label class="zbc-check"><input type="checkbox" data-raw checked>${T('原字节仍可读取','Original bytes still readable')}</label><label>${T('此前已写入当前字节的位数','Earlier bits in the current byte')}: <output data-offset>0</output><input type="range" min="0" max="7" value="0" step="1" data-align aria-label="${T('此前位数','Earlier bit count')}"></label><div class="zbc-steps"><button type="button" data-back>${T('上一步','Back')}</button><button type="button" data-next>${T('加入块描述','Add block description')}</button></div>`;
  host.view.innerHTML=`<p class="zbc-purpose">${T('把同一组选定指令写成最终块，有三种候选。先比较载荷，再加上编码描述与块头，最后观察选择及对齐。','Write the same selected instructions as a final block in three candidate forms. Compare payloads, add code descriptions and headers, then observe selection and alignment.')}</p><ol class="zbc-progress"><li>${T('指令载荷','Instruction payload')}</li><li>${T('块头与编码描述','Header and description')}</li><li>${T('选择与对齐','Choice and alignment')}</li></ol><div class="zbc-chart"></div><div class="zbc-key"><span class="zbc-header">${T('块头','Header')}</span><span class="zbc-description">${T('描述／长度字段','Description / length fields')}</span><span class="zbc-payload">${T('载荷；压缩块含结束符','Payload; compressed blocks include end marker')}</span><span class="zbc-padding">${T('对齐位','Alignment')}</span></div><div class="zbc-explain"></div><p class="zbc-provenance">${T('这些是选定记录的完整块，成本取自项目固定版本的树构造与块写入器。未模拟默认压缩器如何寻找匹配。','These are complete blocks of selected records, measured with the project’s pinned tree constructor and block writer. They do not simulate the default compressor’s match decisions.')}</p>`;
  const select=host.controls.querySelector('[data-case]'),forced=host.controls.querySelector('[data-fixed]'),raw=host.controls.querySelector('[data-raw]'),align=host.controls.querySelector('[data-align]'),next=host.controls.querySelector('[data-next]'),back=host.controls.querySelector('[data-back]');
  function render(){
    const f=BLOCK_CASES[index],offset=Number(align.value),model=blockCandidates(f,{offset,fixed:forced.checked,raw:raw.checked});
    host.controls.querySelector('[data-offset]').textContent=String(offset);back.disabled=stage===0;next.disabled=stage===2;next.textContent=stage===0?T('加入块描述','Add block description'):T('应用选择规则','Apply selection rule');
    host.view.querySelectorAll('.zbc-progress li').forEach((n,i)=>{n.classList.toggle('zbc-active',i===stage);if(i===stage)n.setAttribute('aria-current','step');else n.removeAttribute('aria-current');});
    const max=Math.max(...model.rows.map(r=>stage===0?r.payload:stage===1?r.total-r.padding:r.total));
    const chart=host.view.querySelector('.zbc-chart');
    if(!chart.childElementCount)chart.innerHTML=model.rows.map(r=>`<div class="zbc-row" data-kind="${r.kind}"><div class="zbc-row-title"><strong>${names[r.kind]}</strong><span data-tag></span><b data-total></b></div><div class="zbc-track" role="img">${r.order.map(part=>`<span class="zbc-${part}" data-part="${part}"></span>`).join('')}</div><p data-parts></p></div>`).join('');
    for(const r of model.rows){
      const row=chart.querySelector(`[data-kind="${r.kind}"]`),shown={header:stage>0?r.header:0,description:stage>0?r.description:0,payload:r.payload,padding:stage===2?r.padding:0};
      const total=Object.values(shown).reduce((x,y)=>x+y,0);
      row.classList.toggle('zbc-selected',stage===2&&r.kind===model.selected);row.classList.toggle('zbc-excluded',stage===2&&!r.eligible);
      row.querySelector('[data-total]').textContent=T(`${total} 位`,`${total} bits`);
      row.querySelector('[data-tag]').textContent=stage!==2?'':r.kind===model.selected?T('实际选择','Selected'):!r.eligible?(r.kind==='stored'?T('原字节不可用','Raw bytes unavailable'):T('Z_FIXED 排除动态','Z_FIXED excludes dynamic')):'';
      const labels={header:T('块头','header'),description:r.kind==='stored'?T('长度字段','length fields'):T('编码描述','code description'),payload:T('载荷','payload'),padding:T('对齐','padding')};
      const detail=stage===0?T(`载荷 ${r.payload}`,`Payload ${r.payload}`):r.order.filter(part=>part!=='padding'||stage===2).map(part=>`${labels[part]} ${shown[part]}`).join(' + ');
      row.querySelector('[data-parts]').textContent=detail;
      row.querySelector('.zbc-track').setAttribute('aria-label',`${names[r.kind]}: ${detail} = ${total}`);
      for(const [part,value]of Object.entries(shown))row.querySelector(`[data-part="${part}"]`).style.width=`${100*value/max}%`;
    }
    const payloadLesson=index===0?T('动态载荷只要 9 位，比固定的 35 位短；但这还没有告诉解码器使用哪些码。','The dynamic payload takes only 9 bits, against 35 fixed bits; it has not yet taught the decoder which codes to use.'):index===1?T('把结束符计入后，动态载荷是 34 位。它与前面的四符号教学树不同，因为现在结束符也要占一个叶子。','With the end marker included, the dynamic payload is 34 bits. Unlike the earlier four-symbol teaching tree, this tree also needs an end-marker leaf.'):index===2?T('重复更多次，短码带来的节省随符号次数增长。编码描述仍为 111 位。','More repetition multiplies the savings from short words. The description still costs 111 bits.'):T('所有字节各出现一次，频率接近均匀，动态编码很难靠短码抵消描述成本。','Every byte occurs once. Nearly uniform frequencies leave little opportunity to repay the dynamic description.');
    const explain=host.view.querySelector('.zbc-explain');
    if(stage===0)explain.textContent=payloadLesson;
    else if(stage===1)explain.textContent=payloadLesson+' '+T(`动态块在载荷前还要写 ${f.description} 位描述和 3 位块头。原样块用 32 位保存长度及其补码。`,`Dynamic output adds ${f.description} description bits and a 3-bit header. Stored output uses 32 bits for its length and complement.`);
    else{
      const fixedRow=model.rows[1],dynamicRow=model.rows[2];
      explain.innerHTML=`<p>${T('实现先比较完整压缩候选的向上取整字节数，再检查原样存储。平局选固定编码；Z_FIXED 也只排除动态编码。','The implementation compares rounded complete compressed candidates, then tests stored output. Fixed wins a tie; Z_FIXED also excludes only dynamic coding.')}</p><div class="zbc-equations"><code>${T('固定估计（字节）','Fixed estimate (bytes)')} = ⌈(${f.fixed} + 3) / 8⌉ = ${fixedRow.estimate}</code><code>${T('动态估计（字节）','Dynamic estimate (bytes)')} = ⌈(${f.payload} + ${f.description} + 3) / 8⌉ = ${dynamicRow.estimate}</code><code>${T('原样比较（字节）','Stored comparison (bytes)')}: ${f.bytes} + 4 ${f.bytes+4<=model.estimate?'≤':'>'} ${model.estimate}${raw.checked?'':T('；原字节不可用','; raw bytes unavailable')}</code></div><p>${T(`结果：${names[model.selected]}。上图对齐位按此前的 ${offset} 位计算，不参与这段选择公式。原样块在块头之后对齐，压缩块在结束符之后对齐。`,`Result: ${names[model.selected]}. Padding accounts for ${offset} earlier bits but does not enter this selection formula. Stored blocks align after the header; compressed final blocks align after the end marker.`)}</p>`;
    }
    host.status.textContent=T(`第 ${stage+1} 步，共三步。`,`Step ${stage+1} of three. `)+(stage===2?T(`选择${names[model.selected]}；当前对齐下新增 ${model.rows.find(r=>r.kind===model.selected).total} 位。`,`Selected ${names[model.selected]}; adds ${model.rows.find(r=>r.kind===model.selected).total} bits at this alignment.`):payloadLesson);
  }
  host.on(select,'change',()=>{index=Number(select.value);render();});for(const el of [forced,raw])host.on(el,'change',render);host.on(align,'input',render);host.on(next,'click',()=>{stage=Math.min(2,stage+1);render();});host.on(back,'click',()=>{stage=Math.max(0,stage-1);render();});render();
}
