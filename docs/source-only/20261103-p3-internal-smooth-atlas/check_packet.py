"""Static inventory and independent finite checks, NOT Lean/kernel validation.

The transcendental transition model is only a numerical sanity test, not
an evaluation of Lean Real.smoothTransition or a proof of correspondence.
No prime asymptotic, null-set theorem or arithmetic PP estimate is tested.
"""
from __future__ import annotations
import hashlib, itertools, json, random, re
from fractions import Fraction as Q
from pathlib import Path
import mpmath as mp

ROOT = Path(__file__).resolve().parent
PROOFS = sorted(p for p in ROOT.glob('*.lean') if p.name != 'VERIFY.lean')

def without_comments(text: str) -> str:
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i): depth += 1; i += 2
        elif depth and text.startswith('-/', i): depth -= 1; i += 2
        elif depth: i += 1
        elif text.startswith('--', i):
            j = text.find('\n', i); i = len(text) if j < 0 else j
        else: out.append(text[i]); i += 1
    assert depth == 0, 'unterminated comment'
    return ''.join(out)

def raw_info(path: Path) -> dict:
    b = path.read_bytes()
    result = {'path': path.name, 'bytes': len(b), 'lines': len(b.splitlines()),
              'sha256': hashlib.sha256(b).hexdigest(),
              'git_blob_sha': hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()}
    if path.suffix == '.lean':
        s = without_comments(b.decode())
        assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b|#eval', s)
        stack, pairs = [], {')':'(', ']':'[', '}':'{', '⟩':'⟨'}
        for ch in s:
            if ch in '([{⟨': stack.append(ch)
            elif ch in pairs:
                assert stack and stack.pop() == pairs[ch], (path.name, ch)
        assert not stack, path.name
        result['imports'] = re.findall(r'^import (\S+)', s, re.M)
        result['declarations'] = [{'kind': a, 'name': n} for a,n in
            re.findall(r'^(?:private\s+)?(def|theorem|abbrev|inductive)\s+([^\s(:]+)', s, re.M)]
    return result

a, h, mu, c = Q(417,5000), Q(19,125), Q(25,128), Q(90621,160000)
def A(t): return (1+t)/2
def C(t): return Q(57,64)-Q(3,2)*t
def args(u,t): return (mu-t-u, c-A(t), c-C(t+u), C(t+u)-A(t))
def owner(u,t):
    if t+u <= mu: return 0
    if A(t) <= c and C(t+u) <= c: return 1
    return 2 if A(t) <= C(t+u) else 3

def circuit(v):
    x,y,z,w = v; p = y*z
    return (x,(1-x)*p,(1-x)*(1-p)*w,(1-x)*(1-p)*(1-w))

points = set()
for i in range(81):
    for j in range(i,81): points.add((a+(h-a)*Q(i,80),a+(h-a)*Q(j,80)))
for i in range(101):
    u = a+(h-a)*Q(i,100)
    for t in (mu-u, Q(10621,80000), Q(17293,80000)-u, (Q(25,32)-3*u)/4):
        if a <= u <= t <= h: points.add((u,t))
for u,t in points:
    bits = tuple(Q(int(z>=0)) for z in args(u,t))
    assert circuit(bits) == tuple(Q(int(i==owner(u,t))) for i in range(4))
    assert sum(circuit(bits)) == 1

unit = [Q(i,4) for i in range(5)]
vs = list(itertools.product(unit, repeat=4))
bs = list(itertools.product([Q(0),Q(1)], repeat=4))
for v in vs:
    w = circuit(v)
    assert sum(w)==1 and all(0<=s<=1 for s in w)
    for b in bs:
        assert all(abs(x-y)<=sum(abs(r-s) for r,s in zip(v,b)) for x,y in zip(w,circuit(b)))

rng = random.Random(2026110306)
for _ in range(2500):
    v = tuple(Q(rng.randrange(101),100) for _ in range(4))
    w = tuple(Q(rng.randrange(101),100) for _ in range(4))
    assert all(abs(x-y)<=sum(abs(r-s) for r,s in zip(v,w))
               for x,y in zip(circuit(v),circuit(w)))

mp.mp.dps = 60
def real(q): return mp.mpf(q.numerator)/q.denominator

def transition(z):
    if z<=0: return mp.mpf(0)
    if z>=1: return mp.mpf(1)
    p, n = mp.exp(-1/z), mp.exp(-1/(1-z))
    return p/(p+n)

numeric_count = 0
for u,t in sorted(points)[::17]:
    for m in (0,3,30,3000):
        z = tuple((m+1)*real(q) for q in args(u,t))
        gates = tuple(transition(x) for x in z)
        edges = tuple(1-transition(x)-transition(-x) for x in z)
        soft = circuit(gates)
        assert abs(sum(soft)-1) < mp.mpf('1e-55')
        assert all(e>=-mp.mpf('1e-55') and e<=1+mp.mpf('1e-55') for e in edges)
        assert all(abs(int(i==owner(u,t))-soft[i]) <= sum(edges)+mp.mpf('1e-50') for i in range(4))
        numeric_count += 1

# Toy finite labels/test values: these are NOT repository Gamma evaluations.
for _ in range(600):
    labels = []
    for j in range(rng.randrange(1,24)):
        v = rng.choice(vs); l = rng.randrange(4)
        F, G = Q(rng.randrange(-50,51),7), Q(rng.randrange(-50,51),11)
        wt = Q(1,rng.randrange(1,100)); keep = bool(rng.randrange(2))
        labels.append((v,l,F-G,wt,keep))
    whole = sum(F for v,l,F,wt,k in labels if k)
    soft = [sum(circuit(v)[i]*F for v,l,F,wt,k in labels if k) for i in range(4)]
    sharp = [sum(F for v,l,F,wt,k in labels if k and l==i) for i in range(4)]
    defect = [sum((Q(int(l==i))-circuit(v)[i])*F for v,l,F,wt,k in labels if k) for i in range(4)]
    assert sum(soft)==whole and sum(defect)==0
    assert all(sharp[i]==soft[i]+defect[i] for i in range(4))
    assert sum(sum(abs(circuit(v)[i]*F) for v,l,F,wt,k in labels if k) for i in range(4)) == sum(abs(F) for v,l,F,wt,k in labels if k)
    # Exact weighted triangle domination; denominator weights are positive.
    H = max([abs(F) for v,l,F,wt,k in labels]+[Q(0)])
    for i in range(4):
        d = abs(sum((Q(int(l==i))-circuit(v)[i])*F*wt for v,l,F,wt,k in labels if k))
        b = H*sum(abs(Q(int(l==i))-circuit(v)[i])*wt for v,l,F,wt,k in labels)
        assert d<=b

# Equality faces are charged, not assigned zero geometric error by fiat.
for m in (0,1,100): assert 1-transition(0)-transition(0)==1

inventory = [raw_info(p) for p in PROOFS]
checks = {
    'static_forbidden_forms': 'NO_MATCH', 'delimiter_check': 'PASS',
    'exact_owner_geometry_cases': len(points),
    'unit_cube_cases':len(vs), 'unit_to_bit_lipschitz_cases':len(vs)*len(bs),
    'random_rational_lipschitz_cases':2500,
    'independent_transition_model_cases':numeric_count,
    'finite_signed_ledger_and_domination_cases':600,
    'compiler_invoked':False, 'kernel_replayed':False,
    'prime_asymptotic_verified':False, 'null_wall_theorem_verified':False,
    'python_lean_correspondence_proved':False,
    'new_external_analytic_input_implemented':False,
    'proof_lines':sum(p['lines'] for p in inventory),
    'proof_declarations':sum(len(p['declarations']) for p in inventory)
}
(ROOT/'INVENTORY.json').write_text(json.dumps(inventory, ensure_ascii=False, separators=(',',':'))+'\n')
(ROOT/'CHECKS.json').write_text(json.dumps(checks, ensure_ascii=False, indent=2)+'\n')
print(json.dumps(checks, ensure_ascii=False, indent=2))
