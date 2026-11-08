import {writerTrace,FIXED_FIELDS} from './zlib-writer-model.mjs';

export function mountWriter(host){
  const T=host.t,trace=writerTrace();let step=0;
  const names={header:T('块头','Header'),A:'A',B:'B',length:T('长度 6','Length 6'),distance:T('距离 2','Distance 2'),end:'END_BLOCK',windup:'bi_windup',start:T('初始状态','Initial state')};
  host.controls.innerHTML=`<button type="button" data-back>${T('上一步','Back')}</button><button type="button" data-next>${T('写入下一字段','Write next field')}</button><button type="button" data-reset>${T('重置','Reset')}</button><label>${T('执行进度','Execution')}<input type="range" min="0" max="7" value="0" step="1" aria-label="${T('位写入执行进度','Bit writer execution')}"></label>`;
  host.view.innerHTML=`<div class="bk-writer-fields">${[...FIXED_FIELDS,{name:'windup',width:2}].map(f=>`<div data-field="${f.name}">${names[f.name]}<b>${f.name==='windup'?T('补齐','pad'):f.width+' bit'}</b></div>`).join('')}</div><div class="bk-writer-label"><span>${T('16 位暂存器 · bi_buf','16-bit register · bi_buf')}</span><code data-register></code><span data-valid></span></div><div class="bk-writer-register">${Array.from({length:16},(_,i)=>`<span data-bit="${i}">·<small>${i}</small></span>`).join('')}</div><div class="bk-writer-ends"><span>${T('最低位 · 下一次先输出','LOW BIT · EMITTED FIRST')}</span><span>${T('最高位','HIGH BIT')}</span></div><div class="bk-writer-label" style="margin-top:30px"><span>${T('已写入 pending 的字节','Bytes emitted to pending')}</span><span>${T('尚未交给调用者','Not yet delivered to the caller')}</span></div><div class="bk-writer-bytes">${Array.from({length:5},(_,i)=>`<span data-byte="${i}">··</span>`).join('')}</div><div class="bk-writer-equation" data-equation></div>`;
  const range=host.controls.querySelector('input'),next=host.controls.querySelector('[data-next]'),back=host.controls.querySelector('[data-back]');
  const hex=value=>value.toString(16).padStart(2,'0').toUpperCase();
  const render=()=>{
    const s=trace[step];range.value=String(step);next.disabled=step===trace.length-1;back.disabled=step===0;
    next.textContent=step===6?'bi_windup':T('写入下一字段','Write next field');
    for(const [i,node] of [...host.view.querySelectorAll('[data-field]')].entries()){node.classList.toggle('done',i<step);node.classList.toggle('current',i===step-1);}
    host.view.querySelector('[data-register]').textContent='0x'+s.buffer.toString(16).padStart(4,'0').toUpperCase();
    host.view.querySelector('[data-valid]').textContent='bi_valid = '+s.valid;
    for(const node of host.view.querySelectorAll('[data-bit]')){
      const i=Number(node.dataset.bit);node.classList.toggle('valid',i<s.valid);node.firstChild.textContent=i<s.valid?String((s.buffer>>>i)&1):'·';
    }
    for(const node of host.view.querySelectorAll('[data-byte]')){const byte=s.bytes[Number(node.dataset.byte)];node.classList.toggle('emitted',byte!==undefined);node.textContent=byte===undefined?'··':hex(byte);}
    host.view.querySelector('[data-equation]').textContent=step===7
      ? T('38 个有效位 + 2 个补齐位 = 5 个字节','38 meaningful bits + 2 padding bits = 5 bytes')
      : T(`已写出的 ${s.bytes.length*8} 位 + bi_buf 中的 ${s.valid} 位 = ${s.logical.length} 个有效位`,`${s.bytes.length*8} emitted bits + ${s.valid} held bits = ${s.logical.length} meaningful bits`);
    host.status.textContent=step===0
      ?T('选定 fixed 块和三个符号；从空的位缓冲与 pending 开始。','A fixed block and three symbols are selected. Start with empty bit and pending buffers.')
      :T(`执行 ${names[s.name]}：`,`${names[s.name]}: `)+(s.added.length?T(`新增字节 ${s.added.map(hex).join(' ')}。`,`emits ${s.added.map(hex).join(' ')}. `):T('本步没有新增 pending 字节。','No pending bytes added in this step. '))+(step===7?T('这五个字节是 raw DEFLATE；封装与交付另行处理。','These five bytes are raw DEFLATE. Wrapping and delivery are separate.'):T(`保留 ${s.valid} 位，供下一个字段接续。`,`${s.valid} bits remain for the next field.`));
  };
  host.on(next,'click',()=>{step++;render();});host.on(back,'click',()=>{step--;render();});host.on(range,'input',()=>{step=Number(range.value);render();});host.on(host.controls.querySelector('[data-reset]'),'click',()=>{step=0;render();});render();
}
