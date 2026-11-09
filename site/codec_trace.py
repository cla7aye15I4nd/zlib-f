"""Recorded configuration experiments with the pinned C implementation."""
from pathlib import Path
import html,json,os
ROOT=Path(__file__).resolve().parent
LABELS={'default':('默认参数','Default settings'),'level-0':('级别 0','Level 0'),'level-1':('级别 1','Level 1'),'level-9':('级别 9','Level 9'),'filtered':('过滤策略','Filtered strategy'),'huffman-only':('仅 Huffman','Huffman only'),'rle':('游程策略','Run-length strategy'),'fixed':('固定编码策略','Fixed-code strategy')}

def render_trace(current,lang):
    zh=lang=='zh';t=lambda a,b:a if zh else b
    data=json.loads((ROOT/'content/codec-trace.json').read_text())
    def asset(name):return os.path.relpath(ROOT/'dist/static/examples'/name,current.parent).replace(os.sep,'/')
    options=[]
    for case in data['cases']:
        if case['name'] in LABELS:label=LABELS[case['name']][not zh]
        else:
            d=case['deflate_init'];i=case['inflate_init']
            label=t('窗口／内存','Window/memory')+f' {d["window_bits"]}/{d["memory_level"]}'
            if case['wrapper']!='zlib':label=case['wrapper']+f' / {d["window_bits"]}'
            if i['window_bits']!=d['window_bits']:label+=t('，解码 ','; decode ')+str(i['window_bits'])
        options.append(f'<option value="{case["name"]}">{html.escape(label)}</option>')
    fields=[('compressed','压缩字节','Compressed bytes'),('block','首块类型','First block type'),('difference','相对默认','Change from default'),('calls','压缩／解压调用','Encode/decode calls')]
    default=data['cases'][0]
    defaults={'compressed':f"{default['compressed_bytes']:,}",'block':t('动态编码','Dynamic codes'),'difference':t('0 字节','0 bytes'),'calls':f"{default['deflate_calls']} / {default['inflate_calls']}"}
    cards=''.join(f'<div><dt>{t(cn,en)}</dt><dd data-trace-{key}>{defaults[key]}</dd></div>' for key,cn,en in fields)
    return f'''<figure class="bk-codec-trace" data-codec-trace aria-label="{t('相同输入的 C 配置运行','C configuration runs for the same input')}"><figcaption>{t('同一份输入，不同的配置','One input, different configurations')}</figcaption><p>{t('192 KiB 输入包含重复文本、长重复段与伪随机字节；每次供给和接收至多 4096 字节。选择参数，比较这次源码运行的结果。','The 192 KiB input contains repeated text, long runs and pseudorandom bytes. Each input/output slice holds at most 4096 bytes. Select settings to compare these source-run results.')}</p><label>{t('运行配置','Run settings')}<select data-trace-case aria-label="{t('选择 C 运行配置','Choose C run settings')}">{''.join(options)}</select></label><dl>{cards}</dl><div class="bk-trace-bar" aria-hidden="true"><i data-trace-bar></i></div><p class="bk-trace-settings" data-trace-settings><code>level 6 · windowBits 15 · memLevel 8 · strategy 0 · inflate windowBits 15</code></p><details><summary>{t('输入、构建与完整记录','Input, build and complete record')}</summary><p>{t('记录版本','Recorded version')} <code>{html.escape(data['zlib_version'])}</code>；<code>uInt</code> {data['build']['sizeof_uint']*8} / <code>unsigned long</code> {data['build']['sizeof_ulong']*8} / <code>pointer</code> {data['build']['sizeof_pointer']*8} {t('位','bits')}。</p><p>{t('输入摘要','Input digest')} <code>{data['input']['sha256']}</code></p><p><a href="{asset('codec-trace.c')}">{t('C 输入生成器与调用程序','C input generator and calling program')}</a> · <a href="{asset('codec-trace.json')}">{t('全部运行记录','Complete run record')}</a></p></details><script type="application/json" id="bk-trace-data">{json.dumps(data)}</script></figure>'''
