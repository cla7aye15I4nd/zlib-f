# The overlay certificates with the region scan and the choice row (lit_bufsize = 128 or 256):
# solve, round, verify exactly, emit Lean.
#
#   python3 overlay_cert_choice.py --size N                summary (largest repair excess per case)
#   python3 overlay_cert_choice.py --size N --lean FILE    write ZlibF/Math/DeflateOverlayCertificate<N>.lean
#
# Needs z3 (the Python module) for the exact multiplier LP. See README.md.
#
# For lengths ll, dl and actual frequencies fl, fd of a block with at most 127 symbols, and the
# header length H, the replay proves  H + E <= 999  from
#   header:  2 (H - 71 - Delta) <= sum of the region charges (scan of both trees under kappa1),
#   choice:  H + sum fl ll + sum fd dl + 1 <= sum fl sl + 5 sum fd,
#   Kraft, Fibonacci (W = 130), end of block, symbol count, balance, and the forced leaves:
#   case none: no forced leaf;  case dist: forced leaves only in the distance tree, which then has
#   exactly two nonzero lengths;  case lit: forced leaves in the literal/length tree, which then has
#   exactly two nonzero lengths (any distance tree).
# Delta <= DMAX (per case). Each class of entries is a sixteen-case omega check.
import os, sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
L = int(sys.argv[sys.argv.index('--size') + 1]) if '--size' in sys.argv else 128
assert L in (128, 256)
W = L + 2
DEN = 1024
S = DEN * 2**15
DTARGET = 110 if L == 128 else 250
BUDGET = 8 * L - 25
F = [0, 1]
for i in range(40): F.append(F[-1] + F[-2])
if L == 128:   # kappa1; symbols 10..15 unused at this size
    KLIST = [2, 8, 8, 6, 5, 4, 3, 4, 4, 3, 7, 7, 7, 7, 7, 7, 7, 3, 3]
    LIT_A, LIT_B, OTHER_B = 9, 1, 4            # region charges, scaled by 2
else:          # kappa0
    KLIST = [2, 7, 7, 5, 5, 4, 4, 4, 4, 3, 4, 4, 7, 7, 7, 7, 7, 3, 7]
    LIT_A, LIT_B, OTHER_B = 6, 2, 4
K1 = {k: KLIST[k] for k in range(19)}
KNAME, REFNAME, ML = ('κ1', 'refLen1', 1) if L == 128 else ('κ0', 'refLen0', 2)
PE = [0] + [max(K1[x], 3) for x in range(1, 16)]          # charge of a nonzero entry, before scaling
def fmax(x): return (W - F[x]) // F[x + 1] if W >= F[x] else 0
LEN_EXTRA = [0]*8 + [1]*4 + [2]*4 + [3]*4 + [4]*4 + [5]*4 + [0]
DIST_EXTRA = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13]
# region charges, scaled by 2: literal region (0..256) nonzero 2 pe + 9, zero 1; length and
# distance regions nonzero 2 pe, zero 4
def charge(region, x):
    if x == 0: return LIT_B if region == 'lit' else OTHER_B
    return 2 * PE[x] + (LIT_A if region == 'lit' else 0)
# classes: name, tree, region, positions, kind, extra, static length
CLASSES = [('LIT8', 0, 'lit', list(range(0, 144)), 'LIT', 0, 8),
           ('LIT9', 0, 'lit', list(range(144, 256)), 'LIT', 0, 9),
           ('EOB', 0, 'lit', [256], 'EOB', 0, 7)]
for (e, s, lo, hi) in [(0, 7, 257, 264), (1, 7, 265, 268), (2, 7, 269, 272), (3, 7, 273, 276), (4, 7, 277, 279),
                       (4, 8, 280, 280), (5, 8, 281, 284), (0, 8, 285, 285)]:
    CLASSES.append((f'LEN{e}S{s}', 0, 'len', list(range(lo, hi + 1)), 'LEN', e, s))
for e in range(14):
    CLASSES.append((f'DIST{e}', 1, 'dist', [v for v in range(30) if DIST_EXTRA[v] == e], 'DIST', e, 5))
def ex(kind, x, e):
    return max(0, x + e - 9) if kind == 'LEN' else max(0, x + e - 15) if kind == 'DIST' else 0
def fs(kind, x): return [1] if kind == 'EOB' else sorted({1, fmax(x)})
CASES = {'none': {'dummy': (False, False), 'two': (False, False)},
         'dist': {'dummy': (False, True), 'two': (False, True)},
         'lit': {'dummy': (True, True), 'two': (True, False)}}
def dummyable(c, case):
    t = c[1]
    return CASES[case]['dummy'][t] and any(v <= 2 for v in c[3])

def mterms(kind):
    return {'LIT': {'mu': 1}, 'LEN': {'mu': 1, 'nuP': 1, 'nuM': -1}, 'DIST': {'nuP': -1, 'nuM': 1}, 'EOB': {}}[kind]

def solve(case):
    """The multiplier LP, solved exactly (z3 over the rationals)."""
    import z3
    names = ['lam0', 'lam1', 'mu', 'nu', 'wh', 'rho0', 'rho1', 'D0', 'D1'] + ['A_' + c[0] for c in CLASSES]
    v = {n: z3.Real(n) for n in names}
    o = z3.Optimize()
    for n in names:
        if n != 'nu': o.add(v[n] >= 0)
    o.add(v['wh'] <= 1)
    o.add(v['mu'] + v['nu'] >= 0, -v['nu'] >= 0)
    m = {'LIT': v['mu'], 'LEN': v['mu'] + v['nu'], 'DIST': -v['nu'], 'EOB': z3.RealVal(0)}
    def q(fr): return z3.Q(fr.numerator, fr.denominator)
    for c in CLASSES:
        n, t, region, pos, kind, e, s_ = c
        two = CASES[case]['two'][t]
        rho = v[f'rho{t}'] if two else 0
        o.add(v['wh'] * q(Fr(charge(region, 0), 2)) <= v['A_' + n])
        for x in range(1, 16):
            if fmax(x) >= 1:
                for f in fs(kind, x):
                    o.add(v['wh'] * q(Fr(charge(region, x), 2)) + (1 - v['wh']) * f * s_ + f * ex(kind, x, e) <=
                          v[f'lam{t}'] * q(Fr(2**(15 - x), 2**15)) + v['A_' + n] + f * m[kind] + (1 - v['wh']) * f * x + rho)
            if dummyable(c, case):
                o.add(v['wh'] * q(Fr(charge(region, x), 2)) <=
                      v[f'lam{t}'] * q(Fr(2**(15 - x), 2**15)) + v['A_' + n] + v[f'D{t}'] + rho)
    obj = v['lam0'] + v['lam1'] + v['mu'] * (L - 1) + v['wh'] * (71 + DTARGET + 1) + 3 * v['D0'] + 3 * v['D1'] + \
        2 * v['rho0'] + 2 * v['rho1'] + sum(len(c[3]) * v['A_' + c[0]] for c in CLASSES)
    o.minimize(obj)
    assert o.check() == z3.sat
    mo = o.model()
    def val(n):
        r = mo.eval(v[n], model_completion=True)
        return float(Fr(r.numerator_as_long(), r.denominator_as_long()))
    out = {n: val(n) for n in names}
    out['nuP'], out['nuM'] = max(0.0, out['nu']), max(0.0, -out['nu'])
    return out

def certificate(case):
    sol = solve(case)
    q = {n: Fr(round(v * DEN), DEN) for n, v in sol.items()}
    wh = q['wh']; wc = 1 - wh
    nu = q['nuP'] - q['nuM']
    m = {'LIT': q['mu'], 'LEN': q['mu'] + nu, 'DIST': -nu, 'EOB': Fr(0)}
    assert 0 <= wh <= 1 and all(v >= 0 for v in m.values()) and q['lam0'] >= 0 and q['lam1'] >= 0
    rho = [q['rho0'] if CASES[case]['two'][0] else Fr(0), q['rho1'] if CASES[case]['two'][1] else Fr(0)]
    rho = [max(Fr(0), r) for r in rho]
    A, D = {}, {0: Fr(0), 1: Fr(0)}
    for c in CLASSES:
        n, t, region, pos, kind, e, s = c
        need = wh * Fr(charge(region, 0), 2)
        for x in range(1, 16):
            if fmax(x) < 1: continue
            for f in fs(kind, x):
                lhs = wh * Fr(charge(region, x), 2) + wc * f * s + f * ex(kind, x, e)
                rhs = q[f'lam{t}'] * Fr(2**(15 - x), 2**15) + f * m[kind] + wc * f * x + rho[t]
                need = max(need, lhs - rhs)
        A[n] = need
    for c in CLASSES:
        n, t, region, pos, kind, e, s = c
        if dummyable(c, case):
            D[t] = max(D[t], max(wh * Fr(charge(region, x), 2) - q[f'lam{t}'] * Fr(2**(15 - x), 2**15) - A[n] - rho[t]
                                 for x in range(1, 16)))
    # exact re-verification at every frequency
    for c in CLASSES:
        n, t, region, pos, kind, e, s = c
        assert wh * Fr(charge(region, 0), 2) <= A[n]
        for x in range(1, 16):
            for f in range(0, fmax(x) + 1):
                if kind == 'EOB' and f != 1: continue
                if f == 0 and not dummyable(c, case): continue
                lhs = wh * Fr(charge(region, x), 2) + wc * f * s + f * ex(kind, x, e)
                rhs = q[f'lam{t}'] * Fr(2**(15 - x), 2**15) + A[n] + f * m[kind] + wc * f * x + rho[t] + \
                    (D[t] if f == 0 else 0)
                assert lhs <= rhs, (case, n, x, f)
    # H + E <= wh (71 + Delta) - wc + lam0 + lam1 + mu (L - 1) + sum A + 3 D + 2 rho
    B0 = -wc + q['lam0'] + q['lam1'] + q['mu'] * (L - 1) + 3 * D[0] + 3 * D[1] + 2 * rho[0] + 2 * rho[1]
    B0 += sum(len(c[3]) * A[c[0]] for c in CLASSES) + wh * 71
    dmax = (BUDGET - B0) / wh if wh > 0 else Fr(10**9)
    return dict(q=q, wh=wh, wc=wc, m=m, A=A, D=D, rho=rho, B0=B0, dmax=dmax)

def scaled(v):
    s = v * S
    assert s.denominator == 1, v
    return s.numerator

if __name__ == '__main__' and '--lean' not in sys.argv:
    for case in CASES:
        c = certificate(case)
        print(f'L {L} case {case}: H + E <= {float(c["B0"]):.2f} + {float(c["wh"]):.4f} Delta; Delta <= {float(c["dmax"]):.2f}')

# ---------------------------------------------------------------- Lean emission
def scaled(v):
    s = v * S
    assert s.denominator == 1, v
    return s.numerator

FIBS = ', '.join(f'f{i}' for i in range(17))
RC = 'rcases x with ' + ' | '.join(['_'] * 16) + ' | x'

def lean_all():
    certs = {case: certificate(case) for case in CASES}
    out = []
    w = out.append
    w('import ZlibF.Math.DeflateOverlayCertificate')
    w('')
    w('/-!')
    w(f'# The memLevel {ML} overlay certificate (`lit_bufsize = {L}`)')
    w('')
    w(f'Generated by `tests/goals/overlay-adversarial/certificate/overlay_cert_choice.py --size {L} --lean`; do not edit.')
    w('The test `certificate/regenerate.sh` regenerates it and compares.')
    w('')
    w('For the lengths `ll`, `dl`, the actual frequencies `fl`, `fd` and the header length `H` of a')
    w(f'dynamic block with at most {L - 1} symbols, `H + E ≤ {BUDGET}`, from the header row (the region charges of')
    w(f'the scan under the reference code `{KNAME}`, plus the repair excess `Δ`), the choice row, Kraft, the')
    w(f'Fibonacci bound (weight {W}), the end of block, the symbol count and the balance. Three cases:')
    w('no forced leaf (`certificate_none`); forced leaves only in the distance tree, which then has two')
    w('nonzero lengths (`certificate_dist`); forced leaves in the literal/length tree, which then has two')
    w('nonzero lengths (`certificate_lit`). Each class of entries is a sixteen-case `omega` check.')
    w('-/')
    w('')
    w(f'namespace ZlibF.Math.DeflateOverlayCertificate{L}')
    w('open ZlibF.Math.DeflateSymbols')
    w('open Zlib.Trees.HuffmanAbstract (fib)')
    w('open ZlibF.Math.DeflateOverlaySmall (fib_values)')
    w('open ZlibF.Math.DeflateOverlayCertificate (kraftTerm lengthExtra distanceExtra literalExcess distanceExcess')
    w('  mass_split mass_const lengthExtra_le distanceExtra_le)')
    w('set_option autoImplicit false')
    w('')
    if L == 128:
        w('/-- The reference bit-length code `κ1` (symbols 0..18; 10..15 are unused at `lit_bufsize = 128`). -/')
    else:
        w(f'/-- The reference bit-length code `{KNAME}` (symbols 0..18). -/')
    w(f'def {REFNAME} : Nat → Nat')
    for k in range(19): w(f'  | {k} => {KLIST[k]}')
    w('  | _ => 0')
    w('')
    w('/-- The region charge of an entry of length `x` in the literal region (positions 0..256),')
    w(f'scaled by 2: {LIT_B} for a zero, `2·max({KNAME}[x], 3) + {LIT_A}` for a length. -/')
    w('def literalRegionCharge : Nat → Nat')
    for x in range(16): w(f'  | {x} => {charge("lit", x)}')
    w('  | _ => 0')
    w('')
    w(f'/-- The region charge of an entry in the length or distance region, scaled by 2: {OTHER_B} for a zero,')
    w(f'`2·max({KNAME}[x], 3)` for a length. -/')
    w('def otherRegionCharge : Nat → Nat')
    for x in range(16): w(f'  | {x} => {charge("len", x)}')
    w('  | _ => 0')
    w('')
    w('/-- The region charge of literal/length entry `v` at length `x`. -/')
    w('def literalCharge (v x : Nat) : Nat := if v ≤ 256 then literalRegionCharge x else otherRegionCharge x')
    w('')
    w('/-- The fixed code length of literal/length symbol `v`. -/')
    w('def staticLen (v : Nat) : Nat := if v < 144 then 8 else if v < 256 then 9 else if v < 280 then 7 else 8')
    w('')
    w('/-- One for a nonzero length. -/')
    w('def isUsed (x : Nat) : Nat := if x = 0 then 0 else 1')
    w('')
    simps = 'literalRegionCharge, otherRegionCharge, kraftTerm, reduceIte, Nat.reduceEqDiff, Nat.reduceAdd, ' \
            'Nat.reduceSub, Nat.reducePow, Nat.reduceMul, ' + ', '.join(f'f{i}' for i in range(17))
    for case, cr in certs.items():
        wh, wc = cr['wh'], cr['wc']
        WH2 = scaled(wh / 2); WC = scaled(wc)
        lam = [scaled(cr['q']['lam0'] / 2**15), scaled(cr['q']['lam1'] / 2**15)]
        rho = [scaled(r) for r in cr['rho']]
        Dh = [scaled(cr['D'][0]), scaled(cr['D'][1])]
        cr['ints'] = dict(WH2=WH2, WC=WC, lam=lam, rho=rho, Dh=Dh)
        w(f'/-! ## Case `{case}` -/')
        w('')
        for c in CLASSES:
            n, t, region, pos, kind, e, s_ = c
            dum = dummyable(c, case)
            chfun = 'literalRegionCharge' if region == 'lit' else 'otherRegionCharge'
            th = 9 if kind == 'LEN' else 15
            exterm = f' + {S} * (f * (x + {e} - {th}))' if kind in ('LEN', 'DIST') else ''
            A = scaled(cr['A'][n]); M = scaled(cr['m'][kind])
            w(f'theorem entry_{case}_{n} (x f d r : Nat) (hx : x ≤ 15)')
            if kind == 'EOB':
                w(f'    (used : f = 1 ∧ 1 ≤ x ∧ f * fib (x + 1) + fib x ≤ {W}) (dummy : d = 0)')
            elif dum:
                w(f'    (used : f ≠ 0 → 1 ≤ x ∧ f * fib (x + 1) + fib x ≤ {W})')
                w(f'    (dummy : x ≠ 0 → f = 0 → d = {Dh[t]}) (zero : x = 0 → d = 0 ∨ d = {Dh[t]})')
            else:
                w(f'    (used : f ≠ 0 → 1 ≤ x ∧ f * fib (x + 1) + fib x ≤ {W})')
                w('    (dummy : x ≠ 0 → f ≠ 0) (zero : d = 0)')
            w(f'    (count : r = {rho[t]} * isUsed x) :')
            w(f'    {WH2} * {chfun} x + {WC} * (f * {s_}){exterm} ≤')
            w(f'      {lam[t]} * kraftTerm x + {A} + d + f * {M} + {WC} * (f * x) + r := by')
            w(f'  obtain ⟨{FIBS}, _⟩ := fib_values')
            w('  subst count')
            w('  simp only [isUsed]')
            if kind == 'EOB':
                w('  obtain ⟨one, pos, fit⟩ := used')
                w('  subst one dummy')
                w(f'  {RC} <;> simp only [{simps}] at fit pos hx ⊢ <;> omega')
                w('')
                continue
            w('  by_cases hf : f = 0')
            w('  · subst hf')
            w('    by_cases x0 : x = 0')
            if dum:
                w('    · subst x0')
                w(f'      rcases zero rfl with h | h <;> subst h <;> simp only [{simps}] <;> omega')
                w('    · have hd := dummy x0 rfl')
                w('      subst hd')
                w(f'      {RC} <;> simp only [{simps}] at x0 hx ⊢ <;> omega')
            else:
                w('    · subst x0 zero')
                w(f'      simp only [{simps}]; omega')
                w('    · exact absurd rfl (dummy x0)')
            w('  · obtain ⟨pos, fit⟩ := used hf')
            if not dum: w('    subst zero')
            w(f'    {RC} <;> simp only [{simps}] at fit pos hx ⊢ <;> omega')
            w('')
    return out, certs

LIT_RANGES = [(0, 7, 257, 264), (1, 7, 265, 268), (2, 7, 269, 272), (3, 7, 273, 276), (4, 7, 277, 279),
              (4, 8, 280, 280), (5, 8, 281, 284), (0, 8, 285, 285)]
DIST_RANGES = [(0, 0, 3)] + [(e, 2 * e + 2, 2 * e + 3) for e in range(1, 14)]

def disj(var, lo, hi):
    return ' ∨ '.join(f'{var} = {k}' for k in range(lo, hi + 1))

def tail128(certs):
    out = []
    w = out.append
    for case, cr in certs.items():
        I = cr['ints']; WH2, WC, lam, rho, Dh = I['WH2'], I['WC'], I['lam'], I['rho'], I['Dh']
        A = {n: scaled(v) for n, v in cr['A'].items()}
        M = {k: scaled(v) for k, v in cr['m'].items()}
        dumL = CASES[case]['dummy'][0]; dumD = CASES[case]['dummy'][1]
        twoL = CASES[case]['two'][0]; twoD = CASES[case]['two'][1]
        # allowance functions
        w(f'/-- The share of literal/length entry `v` in case `{case}` (scaled). -/')
        w(f'def literalAllow_{case} (v : Nat) : Nat :=')
        chain = f'(if v < 144 then {A["LIT8"]} else if v < 256 then {A["LIT9"]} else if v = 256 then {A["EOB"]}'
        for (e, s_, lo, hi) in LIT_RANGES[:-1]:
            chain += f' else if v ≤ {hi} then {A[f"LEN{e}S{s_}"]}'
        chain += f' else {A["LEN0S8"]})'
        w('  ' + chain + (f' + (if v ≤ 2 then {Dh[0]} else 0)' if dumL else ''))
        w('')
        w(f'def distanceAllow_{case} (v : Nat) : Nat :=')
        chain = f'(if v ≤ 3 then {A["DIST0"]}'
        for (e, lo, hi) in DIST_RANGES[1:-1]:
            chain += f' else if v ≤ {hi} then {A[f"DIST{e}"]}'
        chain += f' else {A["DIST13"]})'
        w('  ' + chain + (f' + (if v ≤ 2 then {Dh[1]} else 0)' if dumD else ''))
        w('')
        w(f'def literalRate_{case} (v : Nat) : Nat := if v < 256 then {M["LIT"]} else if v = 256 then 0 else {M["LEN"]}')
        w('')
        # per-entry dispatch, literal tree
        dcond = 'v ≤ 2' if dumL else 'False'
        w('set_option maxRecDepth 100000 in')
        w(f'theorem literal_entry_{case} (ll fl : Nat → Nat) (v : Nat) (hv : v < 286) (hx : ll v ≤ 15)')
        w(f'    (used : fl v ≠ 0 → 1 ≤ ll v ∧ fl v * fib (ll v + 1) + fib (ll v) ≤ {W})')
        w(f'    (dummy : ll v ≠ 0 → fl v = 0 → {dcond}) (eob : fl 256 = 1) :')
        w(f'    {WH2} * literalCharge v (ll v) + {WC} * (fl v * staticLen v) + {S} * (fl v * literalExcess v (ll v)) ≤')
        w(f'      {lam[0]} * kraftTerm (ll v) + literalAllow_{case} v + fl v * literalRate_{case} v + {WC} * (fl v * ll v) +')
        w(f'        {rho[0]} * isUsed (ll v) := by')
        w('  by_cases a : v < 144')
        w('  · have ex : literalExcess v (ll v) = 0 := by simp [literalExcess, show v < 257 by omega]')
        w(f'    simp only [literalCharge, staticLen, literalAllow_{case}, literalRate_{case}, ex, a, show v ≤ 256 by omega,')
        w('      show v < 256 by omega, ite_true, Nat.mul_zero, Nat.add_zero]')
        if dumL:
            w(f'    have q := entry_{case}_LIT8 (ll v) (fl v) (if v ≤ 2 then {Dh[0]} else 0) _ hx used')
            w('      (fun x0 f0 => by simp [dummy x0 f0]) (fun _ => by by_cases s : v ≤ 2 <;> simp [s]) rfl')
        else:
            w(f'    have q := entry_{case}_LIT8 (ll v) (fl v) 0 _ hx used (fun x0 f0 => absurd (dummy x0 f0) id) rfl rfl')
        w('    omega')
        w('  by_cases b : v < 256')
        w('  · have ex : literalExcess v (ll v) = 0 := by simp [literalExcess, show v < 257 by omega]')
        w(f'    simp only [literalCharge, staticLen, literalAllow_{case}, literalRate_{case}, ex, a, b, show v ≤ 256 by omega,')
        w('      ite_true, ite_false, Nat.mul_zero, Nat.add_zero]')
        if dumL:
            w('    simp only [show ¬ v ≤ 2 by omega, ite_false, Nat.add_zero]')
            w(f'    have q := entry_{case}_LIT9 (ll v) (fl v) 0 _ hx used (fun x0 f0 => by have := dummy x0 f0; omega) rfl rfl')
        else:
            w(f'    have q := entry_{case}_LIT9 (ll v) (fl v) 0 _ hx used (fun x0 f0 => absurd (dummy x0 f0) id) rfl rfl')
        w('    omega')
        w('  by_cases c : v = 256')
        w('  · subst c')
        w('    have ex : literalExcess 256 (ll 256) = 0 := by simp [literalExcess]')
        w(f'    simp (config := {{ decide := true }}) only [literalCharge, staticLen, literalAllow_{case}, literalRate_{case}, ex,')
        w('      ite_true, ite_false, Nat.mul_zero, Nat.add_zero, eob, Nat.one_mul, Nat.mul_one]')
        w('    have u := used (by omega)')
        w('    rw [eob] at u')
        w(f'    have q := entry_{case}_EOB (ll 256) 1 0 _ hx ⟨rfl, u⟩ rfl rfl')
        w('    simp only [Nat.one_mul, Nat.mul_one, Nat.add_zero] at q ⊢')
        w('    omega')
        w('  have nodummy : ll v ≠ 0 → fl v ≠ 0 := fun x0 f0 => by have := dummy x0 f0; omega')
        w('  have ex : literalExcess v (ll v) = ll v + lengthExtra (v - 257) - 9 := by')
        w('    simp [literalExcess, show ¬ v < 257 by omega]')
        w('  rw [ex]')
        w(f'  simp only [literalCharge, staticLen, literalAllow_{case}, literalRate_{case}, a, b, c, show ¬ v ≤ 256 by omega,')
        w('    ite_false]' + (' ' if False else ''))
        if dumL: w('  simp only [show ¬ v ≤ 2 by omega, ite_false, Nat.add_zero]')
        for (e, s_, lo, hi) in LIT_RANGES:
            cond = f'v ≤ {hi}' if hi < 285 else 'True'
            w(f'  by_cases r{lo} : v ≤ {hi}')
            w(f'  · have range : {disj("v", max(lo, 257), hi)} := by omega')
            w(f'    have q := entry_{case}_LEN{e}S{s_} (ll v) (fl v) 0 _ hx used nodummy rfl rfl')
            w('    rcases range with ' + ' | '.join(['rfl'] * (hi - lo + 1)) + ' <;>')
            w('      simp (config := { decide := true }) only [lengthExtra, ite_true, ite_false, Nat.reduceSub] at q ⊢ <;> omega')
        w('  omega')
        w('')
        # per-entry dispatch, distance tree
        dcond = 'v ≤ 2' if dumD else 'False'
        w('set_option maxRecDepth 100000 in')
        w(f'theorem distance_entry_{case} (dl fd : Nat → Nat) (v : Nat) (hv : v < 30) (hx : dl v ≤ 15)')
        w(f'    (used : fd v ≠ 0 → 1 ≤ dl v ∧ fd v * fib (dl v + 1) + fib (dl v) ≤ {W})')
        w(f'    (dummy : dl v ≠ 0 → fd v = 0 → {dcond}) :')
        w(f'    {WH2} * otherRegionCharge (dl v) + {WC} * (fd v * 5) + {S} * (fd v * distanceExcess v (dl v)) ≤')
        w(f'      {lam[1]} * kraftTerm (dl v) + distanceAllow_{case} v + fd v * {M["DIST"]} + {WC} * (fd v * dl v) +')
        w(f'        {rho[1]} * isUsed (dl v) := by')
        w('  simp only [distanceExcess]')
        w('  have nodummy : dl v ≠ 0 → fd v ≠ 0 → True := fun _ _ => trivial')
        for (e, lo, hi) in DIST_RANGES:
            w(f'  by_cases r{lo} : v ≤ {hi}')
            w(f'  · have range : {disj("v", lo, hi)} := by omega')
            if e == 0 and dumD:
                w('    rcases range with rfl | rfl | rfl | rfl')
                for vv in range(4):
                    if vv <= 2:
                        w(f'    · have q := entry_{case}_DIST0 (dl {vv}) (fd {vv}) {Dh[1]} _ hx used (fun _ _ => rfl) (fun _ => Or.inr rfl) rfl')
                        w(f'      have al : distanceAllow_{case} {vv} = {A["DIST0"]} + {Dh[1]} := by simp [distanceAllow_{case}]')
                        w(f'      have ex0 : distanceExtra {vv} = 0 := rfl')
                        w('      rw [ex0, al]')
                        w('      exact Nat.le_trans q (Nat.le_of_eq (by ac_rfl))')
                        continue
                    else:
                        w(f'    · have q := entry_{case}_DIST0 (dl {vv}) (fd {vv}) 0 _ hx used')
                        w('        (fun x0 f0 => absurd (dummy x0 f0) (by decide)) (fun _ => Or.inl rfl) rfl')
                    w(f'      simp (config := {{ decide := true }}) only [distanceExtra, distanceAllow_{case}, ite_true, ite_false,')
                    w('        Nat.add_zero] at q ⊢')
                    w('      omega')
                continue
            elif e == 0:
                w(f'    have q := entry_{case}_DIST0 (dl v) (fd v) 0 _ hx used (fun x0 f0 => absurd (dummy x0 f0) id) rfl rfl')
            elif dumD:
                w(f'    have q := entry_{case}_DIST{e} (dl v) (fd v) 0 _ hx used (fun x0 f0 => by have := dummy x0 f0; omega) rfl rfl')
            else:
                w(f'    have q := entry_{case}_DIST{e} (dl v) (fd v) 0 _ hx used (fun x0 f0 => absurd (dummy x0 f0) id) rfl rfl')
            w('    rcases range with ' + ' | '.join(['rfl'] * (hi - lo + 1)) + ' <;>')
            w(f'      simp (config := {{ decide := true }}) only [distanceExtra, distanceAllow_{case}, ite_true, ite_false,')
            w('        Nat.add_zero] at q ⊢ <;> omega')
        w('  omega')
        w('')
        # sums
        litSum = 0
        for v in range(286):
            if v < 144: a_ = A['LIT8']
            elif v < 256: a_ = A['LIT9']
            elif v == 256: a_ = A['EOB']
            else:
                a_ = next(A[f'LEN{e}S{s_}'] for (e, s_, lo, hi) in LIT_RANGES if lo <= v <= hi)
            litSum += a_ + (Dh[0] if (dumL and v <= 2) else 0)
        distSum = 0
        for v in range(30):
            a_ = next(A[f'DIST{e}'] for (e, lo, hi) in DIST_RANGES if lo <= v <= hi)
            distSum += a_ + (Dh[1] if (dumD and v <= 2) else 0)
        w(f'theorem literal_share_sum_{case} : mass literalAllow_{case} 286 = {litSum} := by')
        w('  rw [show 286 = 3 + 283 from rfl, mass_split, show 283 = 141 + 142 from rfl, mass_split,')
        w('    show 142 = 112 + 30 from rfl, mass_split]')
        w(f'  have c1 : mass (fun k => literalAllow_{case} (3 + k)) 141 = 141 * literalAllow_{case} 3 := by')
        w('    rw [← mass_const]; apply mass_congr; intro k lt')
        w(f'    simp only [literalAllow_{case}, show 3 + k < 144 by omega, show ¬ (3 + k ≤ 2) by omega, ite_true, ite_false,')
        w('      show (3 : Nat) < 144 by omega, show ¬ ((3 : Nat) ≤ 2) by omega]')
        w(f'  have c2 : mass (fun k => literalAllow_{case} (3 + (141 + k))) 112 = 112 * literalAllow_{case} 144 := by')
        w('    rw [← mass_const]; apply mass_congr; intro k lt')
        w(f'    simp only [literalAllow_{case}, show ¬ (3 + (141 + k) < 144) by omega, show 3 + (141 + k) < 256 by omega,')
        w('      show ¬ (3 + (141 + k) ≤ 2) by omega, ite_true, ite_false, show ¬ ((144 : Nat) < 144) by omega,')
        w('      show (144 : Nat) < 256 by omega, show ¬ ((144 : Nat) ≤ 2) by omega]')
        w('  rw [c1, c2]')
        w(f'  simp (config := {{ decide := true }}) only [mass, literalAllow_{case}, ite_true, ite_false, Nat.reduceAdd,')
        w('    Nat.reduceMul]')
        w('')
        w(f'theorem distance_share_sum_{case} : mass distanceAllow_{case} 30 = {distSum} := by')
        w(f'  simp (config := {{ decide := true }}) only [mass, distanceAllow_{case}, ite_true, ite_false, Nat.reduceAdd]')
        w('')
        # the certificate
        wh, wc = cr['wh'], cr['wc']
        dmax = int(cr['dmax'])
        w(f'/-- **The memLevel 1 certificate, case `{case}`**: with `Δ ≤ {dmax}`. -/')
        w(f'theorem certificate_{case} (ll fl dl fd : Nat → Nat) (H Δ : Nat) (small : Δ ≤ {dmax})')
        w('    (lenL : ∀ v, v < 286 → ll v ≤ 15) (lenD : ∀ v, v < 30 → dl v ≤ 15)')
        w('    (kraftL : mass (fun v => kraftTerm (ll v)) 286 ≤ 2 ^ 15)')
        w('    (kraftD : mass (fun v => kraftTerm (dl v)) 30 ≤ 2 ^ 15)')
        w(f'    (usedL : ∀ v, v < 286 → fl v ≠ 0 → 1 ≤ ll v ∧ fl v * fib (ll v + 1) + fib (ll v) ≤ {W})')
        w(f'    (usedD : ∀ v, v < 30 → fd v ≠ 0 → 1 ≤ dl v ∧ fd v * fib (dl v + 1) + fib (dl v) ≤ {W})')
        w(f'    (dummyL : ∀ v, v < 286 → ll v ≠ 0 → fl v = 0 → {"v ≤ 2" if dumL else "False"})')
        w(f'    (dummyD : ∀ v, v < 30 → dl v ≠ 0 → fd v = 0 → {"v ≤ 2" if dumD else "False"})')
        if twoL: w('    (twoL : mass (fun v => isUsed (ll v)) 286 ≤ 2)')
        if twoD: w('    (twoD : mass (fun v => isUsed (dl v)) 30 ≤ 2)')
        w('    (eob : fl 256 = 1)')
        w(f'    (symbols : mass (fun v => if v = 256 then 0 else fl v) 286 ≤ {L - 1})')
        w('    (balance : mass (fun v => if v < 257 then 0 else fl v) 286 = mass fd 30)')
        w('    (header : 2 * H ≤ 2 * (71 + Δ) + mass (fun v => literalCharge v (ll v)) 286 +')
        w('      mass (fun v => otherRegionCharge (dl v)) 30)')
        w('    (choice : H + mass (fun v => fl v * ll v) 286 + mass (fun v => fd v * dl v) 30 + 1 ≤')
        w('      mass (fun v => fl v * staticLen v) 286 + 5 * mass fd 30) :')
        w('    H + mass (fun v => fl v * literalExcess v (ll v)) 286 +')
        w(f'      mass (fun v => fd v * distanceExcess v (dl v)) 30 ≤ {BUDGET} := by')
        w(f'  have sumL : mass (fun v => {WH2} * literalCharge v (ll v) + {WC} * (fl v * staticLen v) +')
        w(f'      {S} * (fl v * literalExcess v (ll v))) 286 ≤')
        w(f'      mass (fun v => {lam[0]} * kraftTerm (ll v) + literalAllow_{case} v + fl v * literalRate_{case} v +')
        w(f'        {WC} * (fl v * ll v) + {rho[0]} * isUsed (ll v)) 286 :=')
        w(f'    mass_mono fun v hv => literal_entry_{case} ll fl v hv (lenL v hv) (usedL v hv) (dummyL v hv) eob')
        w(f'  have sumD : mass (fun v => {WH2} * otherRegionCharge (dl v) + {WC} * (fd v * 5) +')
        w(f'      {S} * (fd v * distanceExcess v (dl v))) 30 ≤')
        w(f'      mass (fun v => {lam[1]} * kraftTerm (dl v) + distanceAllow_{case} v + fd v * {M["DIST"]} +')
        w(f'        {WC} * (fd v * dl v) + {rho[1]} * isUsed (dl v)) 30 :=')
        w(f'    mass_mono fun v hv => distance_entry_{case} dl fd v hv (lenD v hv) (usedD v hv) (dummyD v hv)')
        w('  simp only [mass_add, mass_mul_left, mass_mul_right] at sumL sumD')
        w('  have rates : mass (fun v => fl v * literalRate_' + case + ' v) 286 =')
        w(f'      {M["LIT"]} * mass (fun v => if v < 256 then fl v else 0) 286 +')
        w(f'        {M["LEN"]} * mass (fun v => if v < 257 then 0 else fl v) 286 := by')
        w('    rw [← mass_mul_left, ← mass_mul_left, ← mass_add]')
        w('    apply mass_congr')
        w('    intro v _')
        w(f'    simp only [literalRate_{case}]')
        w('    by_cases a : v < 256')
        w('    · simp [a, show v < 257 by omega, Nat.mul_comm]')
        w('    · by_cases b : v = 256')
        w('      · subst b; simp')
        w('      · simp [a, b, show ¬ v < 257 by omega, Nat.mul_comm]')
        w('  have split : mass (fun v => if v = 256 then 0 else fl v) 286 =')
        w('      mass (fun v => if v < 256 then fl v else 0) 286 + mass (fun v => if v < 257 then 0 else fl v) 286 := by')
        w('    rw [← mass_add]')
        w('    apply mass_congr')
        w('    intro v _')
        w('    by_cases a : v < 256')
        w('    · simp [a, show v ≠ 256 by omega, show v < 257 by omega]')
        w('    · by_cases b : v = 256')
        w('      · subst b; simp')
        w('      · simp [a, b, show ¬ v < 257 by omega]')
        w('  have fdx : mass (fun v => fd v * 5) 30 = 5 * mass fd 30 := by rw [mass_mul_right, Nat.mul_comm]')
        w(f'  have dx : mass (fun v => fd v * {M["DIST"]}) 30 = {M["DIST"]} * mass fd 30 := by')
        w('    rw [mass_mul_right, Nat.mul_comm]')
        w(f'  rw [literal_share_sum_{case}, rates] at sumL')
        w(f'  rw [distance_share_sum_{case}] at sumD')
        w('  rw [split] at symbols')
        w('  have muL := mass_mul_left (fun v => fl v * staticLen v) 286 ' + str(WC))
        w('  have cnt0 : mass (fun v => isUsed (ll v)) 286 ≤ 286 := by')
        w('    have := mass_mono (n := 286) (f := fun v => isUsed (ll v)) (g := fun _ => 1)')
        w('      (fun v _ => by simp only [isUsed]; split <;> omega)')
        w('    rw [mass_const] at this; omega')
        w('  have cnt1 : mass (fun v => isUsed (dl v)) 30 ≤ 30 := by')
        w('    have := mass_mono (n := 30) (f := fun v => isUsed (dl v)) (g := fun _ => 1)')
        w('      (fun v _ => by simp only [isUsed]; split <;> omega)')
        w('    rw [mass_const] at this; omega')
        if not twoL and rho[0] != 0: raise SystemExit('rho0 without a two-leaf fact')
        if not twoD and rho[1] != 0: raise SystemExit('rho1 without a two-leaf fact')
        w('  omega')
        w('')
    for case in certs: w(f'#print axioms certificate_{case}')
    w('')
    w(f'end ZlibF.Math.DeflateOverlayCertificate{L}')
    return out

if __name__ == '__main__' and '--lean' in sys.argv:
    out, certs = lean_all()
    out += tail128(certs)
    open(sys.argv[sys.argv.index('--lean') + 1], 'w').write('\n'.join(out) + '\n')
