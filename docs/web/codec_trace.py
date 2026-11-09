"""Explain one configuration difference after its mechanism has been introduced."""
from pathlib import Path
import html,json,os
ROOT=Path(__file__).resolve().parent
COMPARISONS={
 'window':(('缩小近期保留范围','Retain a shorter history'),('窗口决定较远的重复是否还能成为来源。下面只改变窗口大小，其他设置相同。','The window determines whether distant repetitions remain available. Only its size changes below.'),('window-9','512 字节窗口','512-byte window'),('default','32 KiB 窗口','32 KiB window')),
 'search':(('增加匹配工作的投入','Spend more work on matching'),('两次运行都使用延迟匹配。级别 9 提高搜索与延迟决定的阈值；级别表示工作策略，恢复出的字节没有质量等级之分。','Both runs use lazy matching. Level 9 raises search and delayed-decision thresholds. Level selects working rules; it does not grade the quality of recovered bytes.'),('default','默认匹配投入：级别 6','Default matching effort: level 6'),('level-9','更多匹配投入：级别 9','More matching effort: level 9')),
 'storage':(('改变记录容量与块边界','Change record capacity and block boundaries'),('记录区装满会触发块提交。内存级别同时改变索引和记录容量，因此下面的大小差异包含两者的影响。','Filling record storage triggers block emission. Memory level changes both index and record capacity; both affect the size comparison below.'),('default','普通容量：内存级别 8','Ordinary capacity: memory level 8'),('memory-1','缩小容量：内存级别 1','Smaller capacity: memory level 1')),
}
def render_trace(current,lang,comparison='window'):
    spec=COMPARISONS[comparison];t=lambda cn,en:cn if lang=='zh' else en
    data=json.loads((ROOT/'content/codec-trace.json').read_text());cases={c['name']:c for c in data['cases']}
    rows=[]
    for name,cn,en in spec[2:]:
        size=cases[name]['compressed_bytes'];percent=size/data['input']['bytes']*100
        rows.append(f'<div class="bk-comparison-row"><dt>{html.escape(t(cn,en))}</dt><dd><strong>{size:,}</strong> {t("字节","bytes")}<span class="bk-comparison-bar" aria-hidden="true"><i style="width:{percent:.3f}%"></i></span><small>{t("恢复后逐字节等于原文","Recovered bytes equal the original")}</small></dd></div>')
    def asset(name):return os.path.relpath(ROOT/'dist/static/examples'/name,current.parent).replace(os.sep,'/')
    return f'''<figure class="bk-codec-comparison" data-codec-comparison="{comparison}"><figcaption>{t(*spec[0])}</figcaption><p>{t(*spec[1])}</p><p class="bk-comparison-input">{t('两次运行使用同一份 196,608 字节原文，其中有重复文本、连续重复字节和不规则字节。每次供给与接收至多 4096 字节；以下比较压缩后的字节数。','Both runs use the same 196,608 original bytes: repeated text, runs and irregular bytes. Each input/output slice holds at most 4096 bytes. The comparison measures compressed bytes.')}</p><dl>{''.join(rows)}</dl><p class="bk-comparison-source">{t('这些数来自','These measurements come from')} <a href="{asset('codec-trace.c')}">{t('固定源码的 C 调用程序','the fixed-source C calling program')}</a>{t('；输入和参数保存在','; the input and settings are preserved in')} <a href="{asset('codec-trace.json')}">{t('运行记录','its run record')}</a>{t('。','.')}</p></figure>'''
