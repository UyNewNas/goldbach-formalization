"""Independent algebra/model regressions and byte inventory, NOT Lean validation.

Run with Python 3 and SymPy. No repository producer, Lean command, network or
project finite guard is executed. Numerical S below is only a model; it is
not an evaluation of the locked Lean smoothTransition definition.
"""
from __future__ import annotations

import hashlib
import itertools
import json
import math
from fractions import Fraction as Q
from pathlib import Path
import random
import re
from typing import Any

ROOT = Path(__file__).resolve().parent
RNG = random.Random(20261104)


def strip_lean_comments(text: str) -> str:
    out: list[str] = []
    i = depth = 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1; i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1; i += 2
        elif depth:
            if text[i] == '\n': out.append('\n')
            i += 1
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        else:
            out.append(text[i]); i += 1
    assert depth == 0, 'Unterminated comment'
    return ''.join(out)


def git_blob(data: bytes) -> str:
    return hashlib.sha1(f'blob {len(data)}\0'.encode() + data).hexdigest()


def static_checks() -> list[dict[str, Any]]:
    records = []
    for path in sorted(ROOT.glob('P3*.lean')):
        raw = path.read_bytes()
        text = raw.decode()
        code = strip_lean_comments(text)
        bad = re.findall(r'\b(?:sorry|admit|axiom|unsafe|partial|native_decide)\b|#(?:eval|reduce|guard)\b', code)
        assert not bad, (path.name, bad)
        stack: list[str] = []
        pairs = {')': '(', ']': '[', '}': '{', '⟩': '⟨'}
        for char in code:
            if char in '([{⟨': stack.append(char)
            elif char in pairs:
                assert stack and stack.pop() == pairs[char], (path.name, char)
        assert not stack, (path.name, stack)
        decls = []
        for no, line in enumerate(code.splitlines(), 1):
            match = re.match(r'\s*(private\s+)?(?:@\[[^]]*\]\s*)?(def|theorem|lemma|abbrev|inductive)\s+(\w+)', line)
            if match:
                decls.append({'name': match[3], 'kind': match[2], 'line': no, 'private': bool(match[1])})
        records.append({'path': path.name, 'bytes': len(raw), 'lines': len(text.splitlines()),
                        'sha256': hashlib.sha256(raw).hexdigest(), 'git_blob_sha': git_blob(raw),
                        'imports': re.findall(r'^import\s+(\S+)', code, re.M),
                        'declarations': decls, 'forbidden_scan': 'NO_MATCH'})
    return records


def group_cases() -> int:
    for _ in range(800):
        d, g = RNG.randrange(0, 9), RNG.randrange(2, 7)
        assignment = [RNG.randrange(g) for _ in range(d)]
        u = [Q(RNG.randrange(1, 14), RNG.randrange(1, 9)) for _ in range(d)]
        v = [Q(RNG.randrange(1, 14), RNG.randrange(1, 9)) for _ in range(d)]
        base = [math.prod((u[i] for i in range(d) if assignment[i] == j), start=Q(1)) for j in range(g)]
        values = [base[j]*math.prod((v[i] for i in range(d) if assignment[i] == j), start=Q(1)) for j in range(g)]
        assert values == [math.prod((u[i]*v[i] for i in range(d) if assignment[i] == j), start=Q(1)) for j in range(g)]
        assert math.prod(values, start=Q(1)) == math.prod((u[i]*v[i] for i in range(d)), start=Q(1))
        chosen = RNG.sample(range(g), 2)
        pair_slots = [0 if j == chosen[0] else 1 if j == chosen[1] else None for j in assignment]
        for r in (0, 1):
            assert [i for i in range(d) if pair_slots[i] == r] == [i for i in range(d) if assignment[i] == chosen[r]]
    return 800


def transition(x: float) -> float:
    if x <= 0: return 0.0
    if x >= 1: return 1.0
    a, b = -1/x, -1/(1-x)
    # Stable evaluation of exp(a)/(exp(a)+exp(b)).
    if a >= b: return 1/(1+math.exp(b-a))
    t = math.exp(a-b)
    return t/(1+t)


def numerical_factor_cases() -> int:
    L = math.log(2)
    def eta(r: float) -> float: return transition(r-1)
    def ts(y: float) -> float: return eta(math.exp(y))
    def hat(y: float) -> float: return ts(y+L)-ts(y)
    cases = 0
    for _ in range(1000):
        y = RNG.uniform(-4, 4)
        k = RNG.randrange(0, 13)
        lhs = math.fsum(hat(y-j*L) for j in range(k))
        rhs = ts(y+L)-ts(y+L-k*L)
        assert abs(lhs-rhs) < 3e-13
        assert -1e-13 <= hat(y) <= 1+1e-13
        assert abs(hat(y)-(eta(2*math.exp(y))-eta(math.exp(y)))) < 2e-13
        if y <= -L or y >= L: assert abs(hat(y)) < 1e-13
        cases += 1
    for _ in range(300):
        y = RNG.uniform(0, 8)
        k = math.ceil((y+L)/L)
        assert abs(math.fsum(hat(y-j*L) for j in range(k))-1) < 3e-13
        cases += 1
    return cases


def circuit(v: list[Q]) -> list[Q]:
    a, b, c, d = v
    return [a, (1-a)*b*c, (1-a)*(1-b*c)*d, (1-a)*(1-b*c)*(1-d)]


def signed_source_cases() -> int:
    for _ in range(600):
        n, nq = RNG.randrange(0, 13), RNG.randrange(0, 7)
        weights = [circuit([Q(RNG.randrange(11), 10) for _ in range(4)]) for _ in range(n)]
        extra = [Q(RNG.randrange(11), 10)*Q(RNG.randrange(11), 10) for _ in range(n)]
        rho = [Q(RNG.randrange(-4, 5), 4) for _ in range(nq)]
        tests = [[Q(RNG.randrange(-20, 21), 7) for _ in range(n)] for _ in range(nq)]
        lhs = sum((rho[q]*tests[q][t]*weights[t][lane]*extra[t]
                   for lane in range(4) for q in range(nq) for t in range(n)), Q(0))
        rhs = sum((rho[q]*tests[q][t]*extra[t] for q in range(nq) for t in range(n)), Q(0))
        assert lhs == rhs
    return 600


def jet_cases() -> int:
    import sympy as sp
    x, y, t = sp.symbols('x y t', real=True)
    s = sp.symbols('s', positive=True)
    variables = [x, y]
    # These test the chain/product-rule algorithm, not the analytic derivative
    # bounds of smoothTransition. The exponential composition is retained.
    scalars = [t**3-2*t+1, (sp.exp(t)-1)**2+sp.exp(t)]
    slopes = [[sp.Rational(1, 2), -1], [1, sp.Rational(3, 2)]]
    offsets = [sp.Rational(1, 3), sp.Rational(-2, 5)]
    def ev(e):
        kind = e[0]
        if kind == 'c': return sp.sympify(e[1])
        if kind == 'a': return slopes[e[1]][e[2]]
        if kind == 'f':
            j, n = e[1:]
            z = offsets[j]+s*sum(slopes[j][i]*variables[i] for i in range(2))
            return sp.diff(scalars[j], t, n).subs(t, z)
        if kind == '+': return ev(e[1])+ev(e[2])
        if kind == '*': return ev(e[1])*ev(e[2])
        raise AssertionError(e)
    def jet(i, e):
        if e[0] in ('c', 'a'): return ('c', 0)
        if e[0] == 'f': return ('*', ('a', e[1], i), ('f', e[1], e[2]+1))
        if e[0] == '+': return ('+', jet(i, e[1]), jet(i, e[2]))
        return ('+', ('*', jet(i, e[1]), e[2]), ('*', e[1], jet(i, e[2])))
    f, g = ('f', 0, 0), ('f', 1, 0)
    examples = [f, g, ('*', f, g), ('*', ('+', ('c', 1), ('*', ('c', -1), f)), g)]
    count = 0
    for e in examples:
        for order in range(3):
            for directions in itertools.product(range(2), repeat=order):
                j, lhs = e, ev(e)
                for i in directions:
                    lhs = sp.diff(lhs, variables[i]); j = jet(i, j)
                assert sp.expand(lhs-s**order*ev(j)) == 0
                count += 1
    return count


def main() -> None:
    records = static_checks()
    counts = {'exact_group_and_pair_slot_cases': group_cases(),
              'numerical_log_hat_telescope_and_support_cases': numerical_factor_cases(),
              'exact_signed_same_rho_source_cases': signed_source_cases(),
              'symbolic_mixed_jet_cases': jet_cases()}
    checks = {'status': 'PASS_INDEPENDENT_MODELS_AND_STATIC_SCAN_ONLY', 'counts': counts,
              'lean_executed': False, 'kernel_replay': False, 'transitive_axioms_checked': False,
              'repository_producer_executed': False, 'validates_analytic_bounds': False,
              'validates_python_lean_correspondence': False, 'independent_reviewer': False}
    (ROOT/'CHECKS.json').write_text(json.dumps(checks, indent=2)+'\n')
    (ROOT/'INVENTORY.json').write_text(json.dumps(records, indent=2)+'\n')
    print(json.dumps(checks, indent=2))
    print('proof_lines', sum(r['lines'] for r in records))
    print('declarations', sum(len(r['declarations']) for r in records))


if __name__ == '__main__':
    main()
