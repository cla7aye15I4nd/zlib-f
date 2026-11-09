import {adlerTrace,crcBitTrace,crcByteTrace} from './zlib-checksum-models.mjs';
const hex=(v,n=8)=>v.toString(16).padStart(n,'0').toUpperCase();
const choices='<option>AB</option><option>ABABABAB</option><option>ABC</option>';

export function mountAdler(host){
  const T=host.t;let step=0;
  host.controls.innerHTML=`<label>${T('字节序列','Bytes')}<select aria-label="${T('Adler 教学输入','Adler teaching input')}">${choices}</select></label><button type="button" data-next>${T('接收下一字节','Accept next byte')}</button><button type="button" data-reset>${T('重置','Reset')}</button>`;
  host.view.innerHTML=`<div class="bk-checksum-input"></div><div class="bk-adler-sums"><div><small>a</small><strong data-a>1</strong><span>${T('字节和 · 初值 1','Byte sum · starts at 1')}</span></div><i>→</i><div><small>s</small><strong data-b>0</strong><span>${T('累计 a · 初值 0','Sum of a · starts at 0')}</span></div></div><div class="bk-checksum-formula" data-equation></div><div class="bk-checksum-result"><span>Adler-32</span><code data-result></code></div>`;
  const select=host.controls.querySelector('select'),next=host.controls.querySelector('[data-next]');
  const render=()=>{
    const bytes=[...select.value].map(c=>c.charCodeAt(0)),trace=adlerTrace(bytes),s=trace[step],old=trace[Math.max(0,step-1)];
    host.view.querySelector('.bk-checksum-input').innerHTML=bytes.map((b,i)=>`<span class="${i<step?'processed':''}">${String.fromCharCode(b)}<small>0x${hex(b,2)}</small></span>`).join('');
    host.view.querySelector('[data-a]').textContent=s.a;host.view.querySelector('[data-b]').textContent=s.b;
    host.view.querySelector('[data-result]').textContent='0x'+hex(s.value);
    host.view.querySelector('[data-equation]').textContent=step?`a = (${old.a} + ${s.byte}) mod 65521 = ${s.a}   ·   s = (${old.b} + ${s.a}) mod 65521 = ${s.b}`:T('先更新 a，再把新的 a 加入 s。','Update a first, then add the new a into s.');
    next.disabled=step===bytes.length;host.status.textContent=T(`已处理 ${step} / ${bytes.length} 字节。默认初值，逐字节取模的教学递推。`,`Processed ${step} / ${bytes.length} bytes. Standard initial value, teaching recurrence with reduction after each byte.`);
  };
  host.on(next,'click',()=>{step++;render();});host.on(select,'change',()=>{step=0;render();});host.on(host.controls.querySelector('[data-reset]'),'click',()=>{step=0;render();});render();
}

export function mountCrc(host){
  const T=host.t;let step=0;
  host.controls.innerHTML=`<label>${T('字节序列','Bytes')}<select aria-label="${T('CRC 教学输入','CRC teaching input')}">${choices}</select></label><button type="button" data-next>${T('执行下一步','Next operation')}</button><button type="button" data-byte>${T('完成当前字节','Complete byte')}</button><button type="button" data-reset>${T('重置','Reset')}</button>`;
  host.view.innerHTML=`<div class="bk-checksum-input"></div><div class="bk-writer-label"><span>${T('内部寄存器 r · 最高位在左','Internal register r · high bit on the left')}</span><code data-register></code></div><div class="bk-crc-register">${Array.from({length:32},(_,i)=>`<span data-bit="${31-i}">1</span>`).join('')}</div><div class="bk-checksum-formula" data-operation></div><div class="bk-crc-byte"><span data-position></span><span data-table></span></div><div class="bk-checksum-result"><span>${T('当前 r 的最终异或值','Final XOR of current r')}</span><code data-result></code></div>`;
  const select=host.controls.querySelector('select'),next=host.controls.querySelector('[data-next]'),byteButton=host.controls.querySelector('[data-byte]');
  const render=()=>{
    const bytes=[...select.value].map(c=>c.charCodeAt(0)),trace=crcBitTrace(bytes),s=trace[step],old=trace[Math.max(0,step-1)],done=step===trace.length-1;
    host.view.querySelector('.bk-checksum-input').innerHTML=bytes.map((b,i)=>`<span class="${step&&i<=s.byteIndex?'processed':''}">${String.fromCharCode(b)}<small>0x${hex(b,2)}</small></span>`).join('');
    host.view.querySelector('[data-register]').textContent='0x'+hex(s.register);
    for(const node of host.view.querySelectorAll('[data-bit]')){const bit=(s.register>>>Number(node.dataset.bit))&1;node.textContent=bit;node.classList.toggle('one',!!bit);}
    host.view.querySelector('[data-operation]').textContent=s.operation==='start'?T('内部初值为 FFFFFFFF；每字节先异或，再执行八次逐位更新。','Start with FFFFFFFF. XOR a byte, then perform eight bit updates.'):s.operation==='byte'?`r = 0x${hex(old.register)} XOR 0x${hex(s.byte,2)}`:`r = (0x${hex(old.register)} >>> 1)${s.operation==='xor'?' XOR EDB88320':''}   ·   ${T('旧最低位','old low bit')} = ${old.register&1}`;
    host.view.querySelector('[data-position]').textContent=step?T(`字节 ${s.byteIndex+1} · 已做 ${s.bit} / 8 次逐位更新`,`Byte ${s.byteIndex+1} · ${s.bit} / 8 bit updates`):T('尚未读取字节','No byte read yet');
    const byteTrace=crcByteTrace(bytes),target=(step?s.byteIndex:0)+1;
    host.view.querySelector('[data-table]').textContent=T(`本字节完成后的查表目标：${hex(byteTrace[target].register)}`,`Table target after completing this byte: ${hex(byteTrace[target].register)}`);
    host.view.querySelector('[data-result]').textContent='0x'+hex(s.value);next.disabled=byteButton.disabled=done;
    host.status.textContent=done?T('全部字节完成；此时的最终异或值是这段输入的 CRC-32。','All bytes complete. The final-XOR value is the CRC-32 of this input.'):T('逐位教学递推；一次字节查表合并的是同一组八次更新。','Bitwise teaching recurrence. A byte-table lookup combines the same eight updates.');
  };
  host.on(next,'click',()=>{step++;render();});host.on(byteButton,'click',()=>{const max=select.value.length*9;step=Math.min(max,(Math.floor(step/9)+1)*9);render();});host.on(select,'change',()=>{step=0;render();});host.on(host.controls.querySelector('[data-reset]'),'click',()=>{step=0;render();});render();
}
