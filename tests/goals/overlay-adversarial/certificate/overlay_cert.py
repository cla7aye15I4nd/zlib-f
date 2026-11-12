# The memLevel 2 overlay certificate: solve, round, verify exactly, emit Lean.
#
#   python3 overlay_cert.py                 summary (bound, largest admissible repair excess)
#   python3 overlay_cert.py --bound         the integer bound only
#   python3 overlay_cert.py --lean FILE     write the Lean replay (ZlibF/Math/DeflateOverlayCertificate.lean)
#
# Needs the solver built from lpsolve.c: $LPSOLVE, or ./lpsolve next to this file. See README.md.
#
# The bound: for a block at lit_bufsize L = 256 with lengths ll (literal tree, 286 entries), dl
# (distance tree, 30 entries) and actual frequencies fl, fd,
#   71 + sum_v entryCost(ll v) + sum_v entryCost(dl v) + E <= BOUND,
# E = sum_{v >= 257} fl v (ll v + e - 9) + sum_v fd v (dl v + e - 15) (truncated), from Kraft per
# tree, the Fibonacci bound f F(x+1) + F(x) <= L + 2 for used codes, nonzero-length unused codes
# only at index <= 2, the EOB frequency 1, at most L - 1 symbols, and as many length codes as
# distance codes. The certificate is a set of multipliers: per tree a Kraft multiplier, a symbol
# multiplier mu, a balance multiplier nu, an allowance per class of entries and per dummy. Each
# entry's cost is at most its share; the shares add up to BOUND.
import os, sys, subprocess
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
L = 256
W = L + 2
DEN = 8                 # multipliers are multiples of 1/DEN
S = DEN * 2**15         # scale of the Lean replay
F = [0, 1]
for i in range(40): F.append(F[-1] + F[-2])
K0 = [2, 7, 7, 5, 5, 4, 4, 4, 4, 3, 4, 4, 7, 7, 7, 7, 7, 3, 7]
ENTRY = [2] + [max(K0[x], 3) for x in range(1, 16)]
def fmax(x): return (W - F[x]) // F[x + 1] if W >= F[x] else 0
LEN_EXTRA = [0]*8 + [1]*4 + [2]*4 + [3]*4 + [4]*4 + [5]*4 + [0]
DIST_EXTRA = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13]
# classes: (name, tree, size, kind, extra, has dummies)
CLASSES = [('LIT', 0, 256, 'LIT', 0, True), ('EOB', 0, 1, 'EOB', 0, False)]
CLASSES += [(f'LEN{e}', 0, LEN_EXTRA.count(e), 'LEN', e, False) for e in range(6)]
CLASSES += [(f'DIST{e}', 1, DIST_EXTRA.count(e), 'DIST', e, e == 0) for e in range(14)]
def ex(kind, x, e):
    return max(0, x + e - 9) if kind == 'LEN' else max(0, x + e - 15) if kind == 'DIST' else 0
def mterms(kind):
    return {'LIT': {'mu': 1}, 'LEN': {'mu': 1, 'nuP': 1, 'nuM': -1}, 'DIST': {'nuP': -1, 'nuM': 1}, 'EOB': {}}[kind]
def fs(kind, x): return [1] if kind == 'EOB' else sorted({1, fmax(x)})

def solve():
    names = ['lam0', 'lam1', 'mu', 'nuP', 'nuM'] + ['A_' + c[0] for c in CLASSES] + ['D0', 'D1']
    idx = {n: i for i, n in enumerate(names)}
    rows = []
    def ge(coef, rhs): rows.append(({k: -v for k, v in coef.items()}, -rhs))
    for (n, t, size, kind, e, dum) in CLASSES:
        ge({'A_' + n: 1}, 2)
        for x in range(1, 16):
            if fmax(x) < 1: continue
            for f in fs(kind, x):
                c = {f'lam{t}': Fr(2**(15 - x), 2**15), 'A_' + n: 1}
                for k, v in mterms(kind).items(): c[k] = c.get(k, 0) + f * v
                ge(c, ENTRY[x] + f * ex(kind, x, e))
        if dum:
            for x in range(1, 16):
                ge({f'lam{t}': Fr(2**(15 - x), 2**15), 'A_' + n: 1, f'D{t}': 1}, ENTRY[x])
    obj = {'lam0': 1, 'lam1': 1, 'mu': L - 1, 'D0': 3, 'D1': 3}
    for (n, t, size, kind, e, dum) in CLASSES: obj['A_' + n] = size
    text = [f"{len(rows)} {len(names)}"]
    for coef, b in rows:
        row = ['0'] * len(names)
        for k, v in coef.items(): row[idx[k]] = repr(float(v))
        text.append(' '.join(row) + ' ' + repr(float(b)))
    text.append(' '.join(repr(-float(obj.get(n, 0))) for n in names))
    out = subprocess.run([os.environ.get('LPSOLVE', os.path.join(HERE, 'lpsolve'))], input='\n'.join(text),
                         capture_output=True, text=True, check=True).stdout.split('\n')
    return dict(zip(names, map(float, out[1].split())))

def certificate():
    sol = solve()
    q = {n: Fr(round(v * DEN), DEN) for n, v in sol.items()}
    nu = q['nuP'] - q['nuM']
    m = {'LIT': q['mu'], 'LEN': q['mu'] + nu, 'DIST': -nu, 'EOB': Fr(0)}
    assert all(v >= 0 for v in m.values()) and q['lam0'] >= 0 and q['lam1'] >= 0
    A, D = {}, {}
    for (n, t, size, kind, e, dum) in CLASSES:   # least allowance that makes every entry fit
        need = Fr(2)
        for x in range(1, 16):
            if fmax(x) < 1: continue
            for f in fs(kind, x):
                need = max(need, ENTRY[x] + f * ex(kind, x, e) - q[f'lam{t}'] * Fr(2**(15 - x), 2**15) - f * m[kind])
        A[n] = need
    for (n, t, size, kind, e, dum) in CLASSES:
        if dum:
            D[t] = max(Fr(0), max(ENTRY[x] - q[f'lam{t}'] * Fr(2**(15 - x), 2**15) - A[n] for x in range(1, 16)))
    # exact re-verification of every inequality the Lean replay checks, at every frequency
    for (n, t, size, kind, e, dum) in CLASSES:
        assert A[n] >= 2
        for x in range(1, 16):
            for f in range(0, fmax(x) + 1):
                if kind == 'EOB' and f != 1: continue
                allow = A[n] + (D[t] if (f == 0 and dum) else 0)
                if f == 0 and not dum: continue
                lhs = ENTRY[x] + f * ex(kind, x, e)
                rhs = q[f'lam{t}'] * Fr(2**(15 - x), 2**15) + allow + f * m[kind]
                assert lhs <= rhs, (n, x, f)
    B = Fr(71) + q['lam0'] + q['lam1'] + q['mu'] * (L - 1) + 3 * D[0] + 3 * D[1]
    B += sum(size * A[n] for (n, t, size, kind, e, dum) in CLASSES)
    return q, m, A, D, B

def scaled(v):
    s = v * S
    assert s.denominator == 1, v
    return s.numerator

def lean(q, m, A, D, B):
    bound = B.numerator // B.denominator
    lam = [scaled(q['lam0'] / 2**15), scaled(q['lam1'] / 2**15)]   # per unit of 2^(15-x)
    out = []
    w = out.append
    w('import ZlibF.Math.DeflateOverlaySmall')
    w('import ZlibF.Math.DeflateWeightedMass')
    w('')
    w('/-!')
    w('# The memLevel 2 overlay certificate (`lit_bufsize = 256`)')
    w('')
    w('Generated by `tests/goals/overlay-adversarial/certificate/overlay_cert.py --lean`; do not edit.')
    w('The test `certificate/regenerate.sh` regenerates it and compares.')
    w('')
    w('For the literal/length tree (lengths `ll`, actual frequencies `fl`, 286 entries) and the')
    w('distance tree (`dl`, `fd`, 30 entries) of one block with at most 255 symbols:')
    w('')
    w(f'  `71 + Σ entryCost (ll v) + Σ entryCost (dl v) + E ≤ {bound}`,')
    w('')
    w('`E` the excess per occurrence: `x + e − 9` for a length code, `x + e − 15` for a distance code.')
    w('Facts used: Kraft per tree, the Fibonacci bound `f·F(x+1) + F(x) ≤ 258` for used codes, unused')
    w('codes with a nonzero length only at index ≤ 2, the end-of-block frequency 1, at most 255')
    w('symbols, as many length codes as distance codes. The certificate is a set of multipliers,')
    w(f'scaled by {S}: each entry costs at most its share (`entry_*`, a sixteen-case `omega` check),')
    w('and the shares add up to the bound.')
    w('-/')
    w('')
    w('namespace ZlibF.Math.DeflateOverlayCertificate')
    w('open ZlibF.Math.DeflateSymbols')
    w('open Zlib.Trees.HuffmanAbstract (fib)')
    w('open ZlibF.Math.DeflateOverlaySmall (fib_values)')
    w('set_option autoImplicit false')
    w('')
    w('/-- The reference bit-length code `κ0` (symbols 0..18). -/')
    w('def refLen : Nat → Nat')
    for k, v in enumerate(K0): w(f'  | {k} => {v}')
    w('  | _ => 0')
    w('')
    w('/-- The header cost charged to one entry of a length sequence: 2 for a zero, `max(κ0[x], 3)`')
    w('for a length `x`. -/')
    w('def entryCost : Nat → Nat')
    for x in range(16): w(f'  | {x} => {ENTRY[x]}')
    w('  | _ => 7')
    w('')
    w('/-- Extra bits of length code `c` (symbol `257 + c`). -/')
    w('def lengthExtra : Nat → Nat')
    for c, v in enumerate(LEN_EXTRA): w(f'  | {c} => {v}')
    w('  | _ => 0')
    w('')
    w('/-- Extra bits of distance code `c`. -/')
    w('def distanceExtra : Nat → Nat')
    for c, v in enumerate(DIST_EXTRA): w(f'  | {c} => {v}')
    w('  | _ => 0')
    w('')
    w('/-- The Kraft share of a length: `2^(15 − x)`, none for a zero. -/')
    w('def kraftTerm (x : Nat) : Nat := if x = 0 then 0 else 2 ^ (15 - x)')
    w('')
    w('/-- The excess of literal/length symbol `v` at length `x`. -/')
    w('def literalExcess (v x : Nat) : Nat := if v < 257 then 0 else x + lengthExtra (v - 257) - 9')
    w('')
    w('/-- The excess of distance code `v` at length `x`. -/')
    w('def distanceExcess (v x : Nat) : Nat := x + distanceExtra v - 15')
    w('')
    # allowances
    w('/-- The allowance of a length code by its extra bits (scaled). -/')
    w('def lengthAllow : Nat → Nat')
    for e in range(6): w(f'  | {e} => {scaled(A[f"LEN{e}"])}')
    w('  | _ => 0')
    w('')
    w('/-- The allowance of a distance code by its extra bits (scaled). -/')
    w('def distanceAllow : Nat → Nat')
    for e in range(14): w(f'  | {e} => {scaled(A[f"DIST{e}"])}')
    w('  | _ => 0')
    w('')
    w('/-- The share of literal/length entry `v` (scaled), dummies included. -/')
    w('def literalAllow (v : Nat) : Nat :=')
    w(f'  (if v < 256 then {scaled(A["LIT"])} else if v = 256 then {scaled(A["EOB"])} else lengthAllow (lengthExtra (v - 257))) +')
    w(f'    (if v ≤ 2 then {scaled(D[0])} else 0)')
    w('')
    w('/-- The share of distance entry `v` (scaled), dummies included. -/')
    w(f'def distanceShare (v : Nat) : Nat := distanceAllow (distanceExtra v) + (if v ≤ 2 then {scaled(D[1])} else 0)')
    w('')
    w('/-- The frequency multiplier of literal/length entry `v` (scaled). -/')
    w(f'def literalRate (v : Nat) : Nat := if v < 256 then {scaled(m["LIT"])} else if v = 256 then 0 else {scaled(m["LEN"])}')
    w('')
    fibs = ', '.join(f'f{i}' for i in range(17))
    simps = 'entryCost, kraftTerm, reduceIte, Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceSub, Nat.reducePow, Nat.reduceMul, ' + \
        ', '.join(f'f{i}' for i in range(17))
    rc = 'rcases x with ' + ' | '.join(['_'] * 16) + ' | x'
    def entry_lemma(name, kind, e, t, dum, allow, rate):
        th = 9 if kind == 'LEN' else 15
        excess = f' + f * (x + {e} - {th})' if kind in ('LEN', 'DIST') else ''
        lam_ = lam[t]
        w(f'theorem entry_{name} (x f d : Nat) (hx : x ≤ 15)')
        if kind == 'EOB':
            w('    (used : f = 1 ∧ 1 ≤ x ∧ f * fib (x + 1) + fib x ≤ 258) (dummy : d = 0) :')
        else:
            w('    (used : f ≠ 0 → 1 ≤ x ∧ f * fib (x + 1) + fib x ≤ 258)')
            if dum: w(f'    (dummy : x ≠ 0 → f = 0 → d = {scaled(D[t])}) (zero : x = 0 → d = 0 ∨ d = {scaled(D[t])}) :')
            else: w('    (dummy : x ≠ 0 → f ≠ 0) (zero : d = 0) :')
        w(f'    {S} * (entryCost x{excess}) ≤ {lam_} * kraftTerm x + {allow} + d + f * {rate} := by')
        w(f'  obtain ⟨{fibs}, _⟩ := fib_values')
        if kind == 'EOB':
            w('  obtain ⟨one, pos, fit⟩ := used')
            w('  subst one dummy')
            w(f'  {rc} <;> simp only [{simps}] at fit pos hx ⊢ <;> omega')
            return
        w('  by_cases hf : f = 0')
        w('  · subst hf')
        w('    by_cases x0 : x = 0')
        if dum:
            w('    · subst x0')
            w(f'      rcases zero rfl with h | h <;> subst h <;> simp only [{simps}] <;> omega')
            w('    · have hd := dummy x0 rfl')
            w('      subst hd')
            w(f'      {rc} <;> simp only [{simps}] at x0 hx ⊢ <;> omega')
        else:
            w('    · subst x0 zero')
            w(f'      simp only [{simps}]; omega')
            w('    · exact absurd rfl (dummy x0)')
        w('  · obtain ⟨pos, fit⟩ := used hf')
        if not dum: w('    subst zero')
        w(f'    {rc} <;> simp only [{simps}] at fit pos hx ⊢ <;> omega')
        w('')
    entry_lemma('literal', 'LIT', 0, 0, True, scaled(A['LIT']), scaled(m['LIT']))
    w('')
    entry_lemma('end', 'EOB', 0, 0, False, scaled(A['EOB']), 0)
    w('')
    for e in range(6):
        entry_lemma(f'length{e}', 'LEN', e, 0, False, scaled(A[f'LEN{e}']), scaled(m['LEN']))
    for e in range(14):
        entry_lemma(f'distance{e}', 'DIST', e, 1, e == 0, scaled(A[f'DIST{e}']), scaled(m['DIST']))
    data = dict(bound=bound, S=S, lam=lam, B=B,
                lit_share_sum=sum(scaled(A['LIT']) for v in range(256)) + scaled(A['EOB']) +
                sum(scaled(A[f'LEN{LEN_EXTRA[c]}']) for c in range(29)) + 3 * scaled(D[0]),
                dist_share_sum=sum(scaled(A[f'DIST{DIST_EXTRA[c]}']) for c in range(30)) + 3 * scaled(D[1]),
                mu=scaled(m['LIT']), muLen=scaled(m['LEN']), nuD=scaled(m['DIST']),
                dummy=(scaled(D[0]), scaled(D[1])))
    return out, data

def tail(dt):
    S = dt['S']; L0, L1 = dt['lam']
    out = []
    w = out.append
    w('theorem mass_split (f : Nat → Nat) (a b : Nat) :')
    w('    mass f (a + b) = mass f a + mass (fun k => f (a + k)) b := by')
    w('  induction b with')
    w('  | zero => rfl')
    w('  | succ b ih =>')
    w('    show mass f (a + b) + f (a + b) = mass f a + (mass (fun k => f (a + k)) b + f (a + b))')
    w('    rw [ih]; omega')
    w('')
    w('theorem mass_const (c n : Nat) : mass (fun _ => c) n = n * c := by')
    w('  induction n with')
    w('  | zero => simp [mass]')
    w('  | succ n ih => simp only [mass, ih, Nat.succ_mul]')
    w('')
    w('theorem lengthExtra_le (c : Nat) : lengthExtra c ≤ 5 := by')
    w('  unfold lengthExtra; split <;> omega')
    w('')
    w('theorem distanceExtra_le (c : Nat) : distanceExtra c ≤ 13 := by')
    w('  unfold distanceExtra; split <;> omega')
    w('')
    w('theorem distanceExtra_pos (c : Nat) (big : 4 ≤ c) (lt : c < 30) : distanceExtra c ≠ 0 := by')
    w('  rcases c with _ | _ | _ | _ | c')
    w('  all_goals try omega')
    w('  rcases c with ' + ' | '.join(['_'] * 26) + ' | c')
    w('  all_goals first | omega | (simp only [distanceExtra]; omega)')
    w('')
    w(f'theorem literal_share_sum : mass literalAllow 286 = {dt["lit_share_sum"]} := by')
    w('  rw [show 286 = 3 + 283 from rfl, mass_split, show 283 = 253 + 30 from rfl, mass_split,')
    w('    show 30 = 1 + 29 from rfl, mass_split]')
    w('  have mid : mass (fun k => literalAllow (3 + k)) 253 = 253 * literalAllow 3 := by')
    w('    rw [← mass_const]')
    w('    apply mass_congr')
    w('    intro k lt')
    w('    simp only [literalAllow, show 3 + k < 256 by omega, show ¬ (3 + k ≤ 2) by omega,')
    w('      show (3 : Nat) < 256 by omega, show ¬ ((3 : Nat) ≤ 2) by omega, ite_true, ite_false]')
    w('  rw [mid]')
    w('  simp (config := { decide := true }) only [literalAllow, lengthAllow, lengthExtra, Nat.reduceAdd,')
    w('    Nat.reduceSub, Nat.reduceMul, ite_true, ite_false]')
    w('')
    w(f'theorem distance_share_sum : mass distanceShare 30 = {dt["dist_share_sum"]} := by')
    w('  simp (config := { decide := true }) only [mass, distanceShare, distanceAllow, distanceExtra,')
    w('    Nat.reduceAdd, Nat.reduceMul, ite_true, ite_false]')
    w('')
    D0, D1 = dt['dummy']
    mu, muLen, nuD = dt['mu'], dt['muLen'], dt['nuD']
    w('/-- Each literal/length entry costs at most its share. -/')
    w('theorem literal_entry (ll fl : Nat → Nat) (v : Nat) (hv : v < 286) (hx : ll v ≤ 15)')
    w('    (used : fl v ≠ 0 → 1 ≤ ll v ∧ fl v * fib (ll v + 1) + fib (ll v) ≤ 258)')
    w('    (dummy : ll v ≠ 0 → fl v = 0 → v ≤ 2) (eob : fl 256 = 1) :')
    w(f'    {S} * (entryCost (ll v) + fl v * literalExcess v (ll v)) ≤')
    w(f'      {L0} * kraftTerm (ll v) + literalAllow v + fl v * literalRate v := by')
    w('  by_cases lit : v < 256')
    w('  · have ex : literalExcess v (ll v) = 0 := by simp [literalExcess, show v < 257 by omega]')
    w('    rw [ex, Nat.mul_zero, Nat.add_zero]')
    w('    simp only [literalAllow, literalRate, lit, ite_true]')
    w(f'    have e := entry_literal (ll v) (fl v) (if v ≤ 2 then {D0} else 0) hx used')
    w('      (fun x0 f0 => by simp [dummy x0 f0]) (fun _ => by by_cases s : v ≤ 2 <;> simp [s])')
    w('    omega')
    w('  by_cases endc : v = 256')
    w('  · subst endc')
    w('    have ex : literalExcess 256 (ll 256) = 0 := by simp [literalExcess]')
    w('    rw [ex, Nat.mul_zero, Nat.add_zero, eob]')
    w('    simp (config := { decide := true }) only [literalAllow, literalRate, ite_true, ite_false]')
    w('    have u := used (by omega)')
    w('    rw [eob] at u')
    w('    have e := entry_end (ll 256) 1 0 hx ⟨rfl, u⟩ rfl')
    w('    omega')
    w('  have ex : literalExcess v (ll v) = ll v + lengthExtra (v - 257) - 9 := by')
    w('    simp [literalExcess, show ¬ v < 257 by omega]')
    w('  rw [ex]')
    w('  simp only [literalAllow, literalRate, lit, endc, ite_false, show ¬ v ≤ 2 by omega, Nat.add_zero]')
    w('  have nodummy : ll v ≠ 0 → fl v ≠ 0 := fun x0 f0 => by have := dummy x0 f0; omega')
    w('  have le5 := lengthExtra_le (v - 257)')
    w('  generalize lengthExtra (v - 257) = e at le5 ⊢')
    w('  rcases e with _ | _ | _ | _ | _ | _ | e')
    for e in range(6):
        w(f'  · have q := entry_length{e} (ll v) (fl v) 0 hx used nodummy rfl')
        w('    simp only [lengthAllow, Nat.add_zero] at q ⊢; omega')
    w('  · omega')
    w('')
    w('/-- Each distance entry costs at most its share. -/')
    w('theorem distance_entry (dl fd : Nat → Nat) (v : Nat) (hv : v < 30) (hx : dl v ≤ 15)')
    w('    (used : fd v ≠ 0 → 1 ≤ dl v ∧ fd v * fib (dl v + 1) + fib (dl v) ≤ 258)')
    w('    (dummy : dl v ≠ 0 → fd v = 0 → v ≤ 2) :')
    w(f'    {S} * (entryCost (dl v) + fd v * distanceExcess v (dl v)) ≤')
    w(f'      {L1} * kraftTerm (dl v) + distanceShare v + fd v * {nuD} := by')
    w('  simp only [distanceExcess, distanceShare]')
    w('  by_cases low : v ≤ 2')
    w('  · have e0 : distanceExtra v = 0 := by')
    w('      rcases v with _ | _ | _ | v <;> first | rfl | omega')
    w('    rw [e0]')
    w(f'    have q := entry_distance0 (dl v) (fd v) (if v ≤ 2 then {D1} else 0) hx used')
    w('      (fun x0 f0 => by simp [dummy x0 f0]) (fun _ => by by_cases s : v ≤ 2 <;> simp [s])')
    w('    simp only [distanceAllow] at q ⊢')
    w('    omega')
    w('  have nodummy : dl v ≠ 0 → fd v ≠ 0 := fun x0 f0 => by have := dummy x0 f0; omega')
    w('  simp only [low, ite_false, Nat.add_zero]')
    w('  by_cases three : v = 3')
    w('  · subst three')
    w('    have q := entry_distance0 (dl 3) (fd 3) 0 hx used (fun x0 f0 => absurd f0 (nodummy x0)) (fun _ => Or.inl rfl)')
    w('    simp only [distanceAllow, distanceExtra, Nat.add_zero] at q ⊢; omega')
    w('  have pos := distanceExtra_pos v (by omega) hv')
    w('  have le13 := distanceExtra_le v')
    w('  generalize distanceExtra v = e at pos le13 ⊢')
    w('  rcases e with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | e')
    w('  · omega')
    for e in range(1, 14):
        w(f'  · have q := entry_distance{e} (dl v) (fd v) 0 hx used nodummy rfl')
        w('    simp only [distanceAllow, Nat.add_zero] at q ⊢; omega')
    w('  · omega')
    w('')
    w(f'/-- **The memLevel 2 certificate.** -/')
    w('theorem certificate (ll fl dl fd : Nat → Nat)')
    w('    (lenL : ∀ v, v < 286 → ll v ≤ 15) (lenD : ∀ v, v < 30 → dl v ≤ 15)')
    w('    (kraftL : mass (fun v => kraftTerm (ll v)) 286 ≤ 2 ^ 15)')
    w('    (kraftD : mass (fun v => kraftTerm (dl v)) 30 ≤ 2 ^ 15)')
    w('    (usedL : ∀ v, v < 286 → fl v ≠ 0 → 1 ≤ ll v ∧ fl v * fib (ll v + 1) + fib (ll v) ≤ 258)')
    w('    (usedD : ∀ v, v < 30 → fd v ≠ 0 → 1 ≤ dl v ∧ fd v * fib (dl v + 1) + fib (dl v) ≤ 258)')
    w('    (dummyL : ∀ v, v < 286 → ll v ≠ 0 → fl v = 0 → v ≤ 2)')
    w('    (dummyD : ∀ v, v < 30 → dl v ≠ 0 → fd v = 0 → v ≤ 2)')
    w('    (eob : fl 256 = 1)')
    w('    (symbols : mass (fun v => if v = 256 then 0 else fl v) 286 ≤ 255)')
    w('    (balance : mass (fun v => if v < 257 then 0 else fl v) 286 = mass fd 30) :')
    w('    71 + mass (fun v => entryCost (ll v)) 286 + mass (fun v => entryCost (dl v)) 30 +')
    w('      mass (fun v => fl v * literalExcess v (ll v)) 286 +')
    w(f'      mass (fun v => fd v * distanceExcess v (dl v)) 30 ≤ {dt["bound"]} := by')
    w('  -- every entry within its share, summed')
    w(f'  have sumL : mass (fun v => {S} * (entryCost (ll v) + fl v * literalExcess v (ll v))) 286 ≤')
    w(f'      mass (fun v => {L0} * kraftTerm (ll v) + literalAllow v + fl v * literalRate v) 286 :=')
    w('    mass_mono fun v hv => literal_entry ll fl v hv (lenL v hv) (usedL v hv) (dummyL v hv) eob')
    w(f'  have sumD : mass (fun v => {S} * (entryCost (dl v) + fd v * distanceExcess v (dl v))) 30 ≤')
    w(f'      mass (fun v => {L1} * kraftTerm (dl v) + distanceShare v + fd v * {nuD}) 30 :=')
    w('    mass_mono fun v hv => distance_entry dl fd v hv (lenD v hv) (usedD v hv) (dummyD v hv)')
    w('  rw [mass_mul_left, mass_add, mass_add, mass_add, mass_mul_left] at sumL sumD')
    w('  rw [mass_mul_right] at sumD')
    w('  -- the frequency shares: symbols at mu, length codes at mu + nu, distance codes at -nu')
    w('  have rates : mass (fun v => fl v * literalRate v) 286 =')
    w(f'      {mu} * mass (fun v => if v < 256 then fl v else 0) 286 +')
    w(f'        {muLen} * mass (fun v => if v < 257 then 0 else fl v) 286 := by')
    w('    rw [← mass_mul_left, ← mass_mul_left, ← mass_add]')
    w('    apply mass_congr')
    w('    intro v _')
    w('    simp only [literalRate]')
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
    w('  rw [literal_share_sum] at sumL')
    w('  rw [distance_share_sum] at sumD')
    w('  rw [rates] at sumL')
    w('  rw [split] at symbols')
    w('  omega')
    return out

def main():
    q, m, A, D, B = certificate()
    if '--bound' in sys.argv:
        print(B.numerator // B.denominator); return
    if '--lean' in sys.argv:
        out, data = lean(q, m, A, D, B)
        out += tail(data)
        out += ['', '#print axioms certificate', '', 'end ZlibF.Math.DeflateOverlayCertificate']
        open(sys.argv[sys.argv.index('--lean') + 1], 'w').write('\n'.join(out) + '\n')
        return
    print(f'L {L}: bound {float(B):.3f} ({B}), budget {8 * L - 25}, largest repair excess {float(8 * L - 25 - B):.3f}')

if __name__ == '__main__':
    main()
