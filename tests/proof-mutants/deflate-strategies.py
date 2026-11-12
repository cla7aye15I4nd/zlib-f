#!/usr/bin/env python3
"""Semantic proof mutants of batch B (fill_window, longest_match and the strategies).

Usage: python3 tests/proof-mutants/deflate-strategies.py <copy of the workspace> <mutant name>
then `lake build` the targets of tests/proof-mutants/deflate-strategies.tsv in that copy.

Each mutant changes one check or one computation in the translation (ZlibF/Zlib). The proofs restate
the code they reason about (`... := rfl` sources, `unfold`/`simp` copies, and the case splits on the
code's conditions), so a plain mutant is caught by those restatements and shows nothing. This script
makes the same edit in every restatement and in the case splits on the mutated condition, and repairs
the arithmetic facts that only restate the mutated expression, as a person repairing the proof would.
The mutant counts only if the first error is then in a semantic lemma: a room bound, a window bound or
a distance bound (deflate-strategies.tsv records where).
"""
import re, sys, pathlib
w = pathlib.Path(sys.argv[1]); name = sys.argv[2]
P = 'ZlibF/Proof/'
Z = 'ZlibF/Zlib/'
T = Z + 'deflate_strategies.c.lean'
B = Z + 'deflate_base.c.lean'


def files_with(text):
    """Every translation or proof file that contains `text`."""
    out = []
    for d in (Z, P):
        for p in sorted((w / d).glob('*.lean')):
            if text in p.read_text():
                out.append(str(p.relative_to(w)))
    return out


def everywhere(old, new):
    return [(f, old, new) for f in files_with(old)]


MORE = '(d.window_size - d.lookahead.toUInt64 - d.strstart.toUInt64).toUInt32'
MORE1 = '(d.window_size - d.lookahead.toUInt64 - d.strstart.toUInt64 + 1).toUInt32'
# fill_more_nat restated for the mutated `more`: the free space plus one.
MORE_NAT_OLD = '''    (fillMore d).toNat = d.window_size.toNat - (d.strstart.toNat + d.lookahead.toNat) := by'''
MORE_NAT_NEW = '''    (fillMore d).toNat = d.window_size.toNat - (d.strstart.toNat + d.lookahead.toNat) + 1 := by'''
MORE_NAT_TAIL_OLD = '''  unfold fillMore
  rw [UInt64.toNat_toUInt32, second, Nat.mod_eq_of_lt (by omega)]'''
MORE_NAT_TAIL_NEW = '''  have third : (d.window_size - d.lookahead.toUInt64 - d.strstart.toUInt64 + 1).toNat =
      d.window_size.toNat - (d.strstart.toNat + d.lookahead.toNat) + 1 := by
    rw [UInt64.toNat_add, second, show (1 : UInt64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
  unfold fillMore
  rw [UInt64.toNat_toUInt32, third, Nat.mod_eq_of_lt (by omega)]'''

# The slide threshold without MAX_DIST's MIN_LOOKAHEAD: `strstart >= wsize + w_size` (never true).
SLIDE_RE = re.compile(r'\+ \(((?:\(slideState d\)|[A-Za-z_][A-Za-z0-9_]*)\.w_size) - MIN_LOOKAHEAD_u\)')
THRESH_ROOM_OLD = '''  have threshold : (d.w_size + d.w_size).toNat = 2 * d.w_size.toNat - 262 := by
    rw [UInt32.toNat_add, sub, Nat.mod_eq_of_lt (by omega)]
    omega'''
THRESH_ROOM_NEW = '''  have threshold : (d.w_size + d.w_size).toNat = 2 * d.w_size.toNat := by
    rw [UInt32.toNat_add, Nat.mod_eq_of_lt (by omega)]
    omega'''
THRESH_SRC_OLD = '''    (d.w_size + d.w_size).toNat = 2 * d.w_size.toNat - 262 := by
  have bounds := slide_window_sizes good
  have sub : (d.w_size - MIN_LOOKAHEAD_u).toNat = d.w_size.toNat - 262 := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; change 262 ≤ _; omega)]
    rfl
  rw [UInt32.toNat_add, sub, Nat.mod_eq_of_lt (by omega)]
  omega'''
THRESH_SRC_NEW = '''    (d.w_size + d.w_size).toNat = 2 * d.w_size.toNat := by
  have bounds := slide_window_sizes good
  rw [UInt32.toNat_add, Nat.mod_eq_of_lt (by omega)]
  omega'''


def slide_never():
    edits = []
    for d in (Z, P):
        for p in sorted((w / d).glob('*.lean')):
            if SLIDE_RE.search(p.read_text()):
                edits.append(('RE', str(p.relative_to(w))))
    return edits + [(P + 'deflate.c.engine.fill-room.lean', THRESH_ROOM_OLD, THRESH_ROOM_NEW),
                    (P + 'deflate.c.engine.fill-slide-source.lean', THRESH_SRC_OLD, THRESH_SRC_NEW)]


LIMIT = 'let limit : UInt32 := if d.strstart > maxd then d.strstart - maxd else 0'
LIMIT_PROOF_OLD = '''  obtain ⟨L, hL⟩ : ∃ L : UInt32, L = (if d.strstart > d.w_size - MIN_LOOKAHEAD_u then d.strstart - (d.w_size - MIN_LOOKAHEAD_u) else 0) :=
    ⟨_, rfl⟩'''
LIMIT_PROOF_NEW = '''  obtain ⟨L, hL⟩ : ∃ L : UInt32, L = 0 :=
    ⟨_, rfl⟩'''
LIMIT_SAME_OLD = '''  have hLsame : (if d.strstart > d.w_size - MIN_LOOKAHEAD_u then d.strstart - (d.w_size - MIN_LOOKAHEAD_u) else 0) = L := hL.symm'''
LIMIT_SAME_NEW = '''  have hLsame : (0 : UInt32) = L := hL.symm'''
STREND = 'return (← Ptr.lt scan strend, scan, m)'
STREND_R = 'do return (← Ptr.lt scan strend, scan, m)'

FAST_REFILL = '''  -- if (s->lookahead < MIN_LOOKAHEAD) { ... }
  if (← rd s (·.lookahead)) < MIN_LOOKAHEAD_u then'''
FAST_REFILL_SRC = '''theorem fast_body_source (s : DeflateStatePtr) (flush : Int32) (st : LoopS) :
    deflate_fast_body s flush st = (do
      if (← rd s (·.lookahead)) < MIN_LOOKAHEAD_u then'''
FAST_SPLIT_OLD = '''  rw [fast_body_source]
  by_cases small : d.lookahead < MIN_LOOKAHEAD_u
  · have short : d.lookahead.toNat < 262 := UInt32.lt_iff_toNat_lt.mp small'''
FAST_SPLIT_NEW = '''  rw [fast_body_source]
  by_cases small : d.lookahead < MIN_MATCH_u
  · have short : d.lookahead.toNat < 262 := by
      have := UInt32.lt_iff_toNat_lt.mp small; change _ < 3 at this; omega'''
FAST_BIG_OLD = '''  · have big : 262 ≤ d.lookahead.toNat := by
      have := small; rw [UInt32.lt_iff_toNat_lt] at this; change ¬ _ < 262 at this; omega
    have room := head.inv.shape.room
    obtain ⟨st', h', iterRun, loop', less⟩ := finishIter head acc pending'''
FAST_BIG_NEW = '''  · have big : 3 ≤ d.lookahead.toNat := by
      have := small; rw [UInt32.lt_iff_toNat_lt] at this; change ¬ _ < 3 at this; omega
    have room := head.inv.shape.room
    obtain ⟨st', h', iterRun, loop', less⟩ := finishIter head acc pending'''

FAST_INSERT = 'if d.match_length ≤ d.max_lazy_match && d.lookahead ≥ MIN_MATCH_u then'
FAST_INSERT_M = 'if d.match_length ≤ d.max_lazy_match then'

SLOW_INSERT = 'if ss ≤ max_insert then'
SLOW_INSERT_M = 'if ss ≤ max_insert + 1 then'

LAZY_FLUSH = 'if bflush then FLUSH_BLOCK_ONLY s 0'
LAZY_FLUSH_M = 'if false then FLUSH_BLOCK_ONLY s 0'

HAVE = 'if len > have_ then len := have_'
HAVE_M = 'if len > have_ + 1 then len := have_ + 1'
LEFT = 'if left > len then left := len'

FR = P + 'deflate.c.engine.fill-read.lean'
# The concrete first read (empty window of 65536 bytes) restated for the mutated `more` (65537).
FIRST_READ = [(FR, 'rbLen z.avail_in 65536', 'rbLen z.avail_in 65537'),
              (FR, 'rbLen_nat z.avail_in 65536', 'rbLen_nat z.avail_in 65537'),
              (FR, 'n.toNat = min z.avail_in.toNat 65536', 'n.toNat = min z.avail_in.toNat 65537'),
              (FR, '    65536 npos bound', '    65537 npos bound'),
              (FR, 'show ((65536 : UInt64) - (0 : UInt32).toUInt64 - (0 : UInt32).toUInt64).toUInt32 = 65536 from rfl',
               'show ((65536 : UInt64) - (0 : UInt32).toUInt64 - (0 : UInt32).toUInt64 + 1).toUInt32 = 65537 from rfl')]
FIRST_NOSLIDE = [(FR, 'show ¬ ((0 : UInt32) ≥ 32768 + (32768 - 262))', 'show ¬ ((0 : UInt32) ≥ 32768 + 32768)')]

LC = P + 'deflate.c.engine.lmcond.lean'
LMCOND = [(LC, '| none => (decide (S + (t + n) < S + 258),', '| none => (! decide (S + 258 < S + (t + n)),'),
          (LC, """    have : OkOn h (Ptr.lt (Ptr.ref (BRef.blk wb) (S + t)) (Ptr.ref (BRef.blk wb) (S + 258))) (decide (S + t < S + 258)) :=""",
               """    have : OkOn h (Ptr.lt (Ptr.ref (BRef.blk wb) (S + 258)) (Ptr.ref (BRef.blk wb) (S + t))) (decide (S + 258 < S + t)) :=""")]

LM = P + 'deflate.c.engine.lmmain.lean'
NICE_SPLIT_OLD = """  by_cases hg : d.prev_length ≥ d.good_match <;> by_cases hn : d.nice_match.toUInt32 > d.lookahead
  · obtain ⟨r, h', ms, best, hr, hrest⟩ := key (d.max_chain_length >>> 2) d.lookahead.toInt32
    refine ⟨r, h', ms, best, ?_, hrest⟩
    simp only [hg, hn, ite_true]; simp only [lmRest, bind_app, pure_app, M_ite_app] at hr; exact hr
  · obtain ⟨r, h', ms, best, hr, hrest⟩ := key (d.max_chain_length >>> 2) d.nice_match
    refine ⟨r, h', ms, best, ?_, hrest⟩
    simp only [hg, hn, ite_true, ite_false]; simp only [lmRest, bind_app, pure_app, M_ite_app] at hr; exact hr
  · obtain ⟨r, h', ms, best, hr, hrest⟩ := key d.max_chain_length d.lookahead.toInt32
    refine ⟨r, h', ms, best, ?_, hrest⟩
    simp only [hg, hn, ite_true, ite_false]; simp only [lmRest, bind_app, pure_app, M_ite_app] at hr; exact hr
  · obtain"""
NICE_SPLIT_NEW = """  by_cases hg : d.prev_length ≥ d.good_match
  · obtain ⟨r, h', ms, best, hr, hrest⟩ := key (d.max_chain_length >>> 2) d.nice_match
    refine ⟨r, h', ms, best, ?_, hrest⟩
    simp only [hg, ite_true]; simp only [lmRest, bind_app, pure_app, M_ite_app] at hr; exact hr
  · obtain"""
NICE_LAST_OLD = """    simp only [hg, hn, ite_true, ite_false]; simp only [lmRest, bind_app, pure_app, M_ite_app] at hr; exact hr

end"""
NICE_LAST_NEW = """    simp only [hg, ite_false]; simp only [lmRest, bind_app, pure_app, M_ite_app] at hr; exact hr

end"""

US = P + 'deflate.c.universal-strategies.lean'
FAST_COND = [(US, '(d4.match_length ≤ d4.max_lazy_match && d4.lookahead ≥ MIN_MATCH_u)', '(decide (d4.match_length ≤ d4.max_lazy_match))')]

MAXI = 'd.strstart + d.lookahead - MIN_MATCH_u'
MAXI_M = '(d.strstart + d.lookahead - MIN_MATCH_u + 1)'

SL = P + 'deflate.c.universal-stored-loop.lean'
HAVE_SPLIT = [(SL, '> z.avail_out - (d.bi_valid.toUInt32 + 42) >>> 3\n', '> z.avail_out - (d.bi_valid.toUInt32 + 42) >>> 3 + 1\n'),
              (SL, '¬ (z.avail_out - (d.bi_valid.toUInt32 + 42) >>> 3).toNat <', '¬ (z.avail_out - (d.bi_valid.toUInt32 + 42) >>> 3 + 1).toNat <')]
LEFT_DEF = [(SL, 'def directLeft (left len : UInt32) : UInt32 := if left > len then len else left',
             'def directLeft (left len : UInt32) : UInt32 := if false then len else left')]

LI = P + 'deflate.c.engine.lminner.lean'
LMINNER = [(LI, 'by_cases hlt : S + (j + 8) < S + 258', 'by_cases hlt : ¬ S + 258 < S + (j + 8)')]
MA = P + 'deflate.c.engine.match-advance.lean'
SA = P + 'deflate.c.engine.short-match-advance.lean'
MAXI_NAT = [(P + 'deflate.c.engine.short-match-words.lean', 'change ¬ d.strstart.toNat + 1 ≤ d.strstart.toNat + 2 - 3\n',
             'change ¬ d.strstart.toNat + 1 ≤ d.strstart.toNat + 2 - 3 + 1\n'),
            (SA, """    ((d.strstart + d.lookahead - MIN_MATCH_u + 1)).toNat = d.strstart.toNat + d.lookahead.toNat - 3 := by""",
                 """    ((d.strstart + d.lookahead - MIN_MATCH_u + 1)).toNat = d.strstart.toNat + d.lookahead.toNat - 3 + 1 := by"""),
            (SA, """  rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, sum]; change 3 ≤ _; omega), sum]
  rfl""", """  rw [UInt32.toNat_add, UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, sum]; change 3 ≤ _; omega), sum]
  simp only [show (1 : UInt32).toNat = 1 from rfl, show MIN_MATCH_u.toNat = 3 from rfl]
  rw [Nat.mod_eq_of_lt (by omega)]"""),
(MA, """    ((d.strstart + d.lookahead - MIN_MATCH_u + 1)).toNat = d.strstart.toNat + d.lookahead.toNat - 3 := by""",
                 """    (d.strstart + d.lookahead - MIN_MATCH_u + 1).toNat = d.strstart.toNat + d.lookahead.toNat - 3 + 1 := by"""),
            (MA, """  rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, sum]; change 3 ≤ _; omega), sum]
  rfl""", """  rw [UInt32.toNat_add, UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, sum]; change 3 ≤ _; omega), sum]
  simp only [show (1 : UInt32).toNat = 1 from rfl, show MIN_MATCH_u.toNat = 3 from rfl]
  rw [Nat.mod_eq_of_lt (by omega)]""")]

# The limit restated for the mutated code: zero. lmRest_ok takes the MAX_DIST limit as its premise.
LIMIT_REGION = ('REGION', P + 'deflate.c.engine.lmmain.lean',
                '  have hlimit : L.toNat = lmLimit d.strstart.toNat (d.w_size.toNat - 262) := by\n',
                '  have hLsame :', '  have hlimit : L.toNat = 0 := by rw [hL]; rfl\n')

M = {
    'fill-more-room': everywhere(MORE, MORE1)
    + [(P + 'deflate.c.engine.fill-room.lean', MORE_NAT_OLD, MORE_NAT_NEW),
       (P + 'deflate.c.engine.fill-room.lean', MORE_NAT_TAIL_OLD, MORE_NAT_TAIL_NEW)] + FIRST_READ,
    'fill-slide-threshold': None,  # computed below: needs the regex pass first
    'lm-limit-dropped': everywhere(LIMIT, 'let limit : UInt32 := 0')
    + [(P + 'deflate.c.engine.lmmain.lean', LIMIT_PROOF_OLD, LIMIT_PROOF_NEW),
       (P + 'deflate.c.engine.lmmain.lean', LIMIT_SAME_OLD, LIMIT_SAME_NEW), LIMIT_REGION],
    'lm-window-end': [(T, STREND, 'return (! (← Ptr.lt strend scan), scan, m)'),
                      (P + 'deflate.c.engine.lmcond.lean', STREND_R, 'do return (! (← Ptr.lt strend scan), scan, m)')] + LMCOND + LMINNER,
    'lm-nice-clamp': everywhere('  if nice_match.toUInt32 > d.lookahead then nice_match := d.lookahead.toInt32\n', '')
    + [(LM, NICE_SPLIT_OLD, NICE_SPLIT_NEW), (LM, NICE_LAST_OLD, NICE_LAST_NEW)],
    'fast-refill-test': [(T, FAST_REFILL, FAST_REFILL.replace('< MIN_LOOKAHEAD_u then', '< MIN_MATCH_u then')),
                         (P + 'deflate.c.universal-strategies.lean', FAST_REFILL_SRC,
                          FAST_REFILL_SRC.replace('< MIN_LOOKAHEAD_u then', '< MIN_MATCH_u then')),
                         (P + 'deflate.c.universal-strategies.lean', FAST_SPLIT_OLD, FAST_SPLIT_NEW),
                         (P + 'deflate.c.universal-strategies.lean', FAST_BIG_OLD, FAST_BIG_NEW)],
    'fast-insert-bound': everywhere(FAST_INSERT, FAST_INSERT_M) + FAST_COND,
    'slow-insert-bound': everywhere(MAXI, MAXI_M) + MAXI_NAT,
    'slow-lazy-flush': everywhere(LAZY_FLUSH, LAZY_FLUSH_M),
    'stored-have-room': everywhere(HAVE, HAVE_M) + HAVE_SPLIT,
    'stored-left-clip': everywhere(LEFT, 'if false then left := len') + LEFT_DEF,
}
if name == 'fill-slide-threshold':
    M[name] = slide_never() + FIRST_NOSLIDE

if name not in M:
    sys.exit(f'unknown mutant {name}')
for edit in M[name]:
    if edit[0] == 'REGION':  # replace from the start text up to (not including) the end text
        _, f, start, end, new = edit
        p = w / f; s = p.read_text()
        i = s.find(start); j = s.find(end, i)
        if i < 0 or j < 0:
            sys.exit(f'missing region in {f}')
        p.write_text(s[:i] + new + s[j:])
        print(f, 'region')
        continue
    if edit[0] == 'RE':
        p = w / edit[1]; s = p.read_text()
        s2, n = SLIDE_RE.subn(r'+ \1', s)
        p.write_text(s2)
        print(edit[1], n)
        continue
    f, old, new = edit
    p = w / f; s = p.read_text()
    if old not in s:
        sys.exit(f'missing in {f}: {old[:80]}')
    p.write_text(s.replace(old, new))
    print(f, s.count(old))
