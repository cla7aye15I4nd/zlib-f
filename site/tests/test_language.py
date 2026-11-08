"""Language checks distinguish explanatory text from exact program data."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from language import audit_chinese_html


class ChineseLanguageTests(unittest.TestCase):
    def test_chinese_shell_does_not_hide_english_body(self):
        html = '<html lang="zh"><nav>中文目录</nav><article><p>This page records evidence and unfinished work for every target.</p></article><footer>中文页脚</footer></html>'
        self.assertTrue(audit_chinese_html(html))

    def test_chinese_explanation_with_named_quantities_passes(self):
        html = '<h2>预读量与搜索距离</h2><p>窗口容量 W 以字节计。<code>MAX_DIST(s)</code> 表示允许搜索的最远距离。</p>'
        self.assertEqual(audit_chinese_html(html), [])

    def test_exact_c_and_lean_comments_are_excluded(self):
        html = '<pre><code class="language-c">/* This page records evidence and unfinished work. */ int n = 4;</code></pre><pre><code class="language-lean">/-- To confirm the old statement. -/ def p := True</code></pre>'
        self.assertEqual(audit_chinese_html(html), [])

    def test_plaintext_contract_prose_is_not_exempt(self):
        html = '<pre><code class="language-text">Pre: crc1 is the CRC of A and crc2 is the CRC of B.</code></pre>'
        self.assertTrue(audit_chinese_html(html))

    def test_equations_and_literal_bytes_pass(self):
        html = '<pre><code class="language-text">pending ≤ B + 3q\na := (a + b) mod M\ns := (s + a) mod M\n73 74 82 40 00\nA B A B A B\n0123ABCDABCDwxyz</code></pre><h3>Goal.inflate</h3><h1>public-inflate-end.lean</h1><td>gzread, gzfread, gzgetc, gzgetc_, gzungetc, gzgets</td>'
        self.assertEqual(audit_chinese_html(html), [])

    def test_quoted_source_error_string_passes(self):
        html = '<pre><code class="language-text">"request does not fit in a size_t"\n"out of room to push characters"</code></pre>'
        self.assertEqual(audit_chinese_html(html), [])

    def test_mixed_chinese_and_untranslated_sentence_fails(self):
        html = '<p>本节说明。This function consumes the next input byte and updates the count. 下面继续。</p>'
        self.assertTrue(audit_chinese_html(html))

    def test_inline_spans_do_not_hide_english_sentence(self):
        words = 'This function consumes the next input byte and updates the count.'.split()
        html = '<p>'+''.join('<span>'+word+'</span>' for word in words)+'</p>'
        self.assertTrue(audit_chinese_html(html))

    def test_short_controls_and_units_fail(self):
        for html in ('<button>Show dependencies</button>', '<span>5 bytes</span>',
                     '<span>literal A</span>', '<th>Preconditions</th>'):
            with self.subTest(html=html):
                self.assertTrue(audit_chinese_html(html))

    def test_reader_reminders_fail_but_precise_open_work_passes(self):
        for text in ('待确认', '仍是 to confirm', '命题存在不代表目标已经证明'):
            self.assertTrue(audit_chinese_html('<p>'+text+'</p>'))
        self.assertEqual(audit_chinese_html('<p>尚未完成动态表安装到解码循环的不变量连接。</p>'), [])

    def test_mermaid_human_labels_checked_identifiers_retained(self):
        self.assertTrue(audit_chinese_html('<pre><code class="language-mermaid">flowchart LR\nA[Input history] --> B[Copy bytes]</code></pre>'))
        self.assertEqual(audit_chinese_html('<pre><code class="language-mermaid">flowchart LR\nA[build_tree] --> B[gen_codes]</code></pre>'), [])

    def test_nested_highlighted_source_keeps_exact_comments(self):
        html = '<pre class="rf-source-code"><code class="language-lean syntax-highlight"><span>-- This page records evidence and unfinished work.</span></code></pre>'
        self.assertEqual(audit_chinese_html(html), [])

    def test_source_view_exemption_does_not_exempt_explanatory_prose(self):
        html = '<pre class="rf-source-code"><span>-- A source comment is retained exactly.</span></pre><p>This function reads the next input byte and updates the count.</p>'
        self.assertTrue(audit_chinese_html(html))


if __name__ == '__main__':
    unittest.main()
