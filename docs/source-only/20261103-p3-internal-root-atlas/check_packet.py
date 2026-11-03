"""Static inventory and independent finite regressions; NOT a Lean proof check.

Run: python check_packet.py
Only files in this packet are read/written. No network, compiler, project
certificate, native source producer or dependency installation is invoked.
"""
from __future__ import annotations
import hashlib
import json
import random
import re
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
A0, H0, MU, C0 = F(417, 5000), F(19, 125), F(25, 128), F(90621, 160000)
T0, S0 = F(10621, 80000), F(17293, 80000)

def a(x): return (1+x)/2

def c(x): return F(57, 64)-F(3, 2)*x

def v(x): return min(a(x), (32-34*x)/39, c(x))

def original(u, t): return max(v(t), v(t+u), C0)

def owner(u, t):
    if t+u <= MU: return 0
    if a(t) <= C0 and c(t+u) <= C0: return 1
    if a(t) <= c(t+u): return 2
    return 3

def lane_value(k, u, t): return (a(t+u), C0, c(t+u), a(t))[k]

def strip_comments(text: str) -> str:
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i): depth += 1; i += 2
        elif depth and text.startswith('-/', i): depth -= 1; i += 2
        elif depth: i += 1
        elif text.startswith('--', i):
            j = text.find('\n', i); i = len(text) if j < 0 else j
        else: out.append(text[i]); i += 1
    if depth: raise ValueError('Unclosed Lean comment')
    return ''.join(out)

def main() -> None:
    points = {(A0+(H0-A0)*F(i,100), A0+(H0-A0)*F(j,100))
              for i in range(101) for j in range(i,101)}
    boundaries = set()
    for i in range(401):
        u = A0+(H0-A0)*F(i,400)
        for t in (MU-u, T0, S0-u, (F(25,32)-3*u)/4):
            if A0 <= u <= t <= H0: boundaries.add((u,t))
    checks = points | boundaries
    lane_counts = [0]*4
    for u,t in checks:
        k = owner(u,t)
        assert original(u,t) == lane_value(k,u,t)
        assert (original(u,t) == C0) == (t <= T0 and S0 <= t+u)
        assert (k == 1) == (t <= T0 and S0 <= t+u)
        assert (k == 0) == (t+u <= MU)
        assert (a(t) <= c(t+u)) == (3*u+4*t <= F(25,32))
        lane_counts[k] += 1
    assert all(lane_counts)
    # All tests retain signed weights and repeated root values. These are
    # finite toy rows, not evaluations of repository Gamma/Theta or rootQ.
    rng = random.Random(361103)
    rows = sorted(checks)
    for case in range(600):
        chosen = [rng.choice(rows) for _ in range(1+case%37)]
        weights = [F(rng.randint(-13,13),rng.randint(1,7)) for _ in chosen]
        keep = [bool(rng.randrange(2)) for _ in chosen]
        count = [F(rng.randint(-90,90),11) for _ in chosen]
        empty = [F(rng.randint(-20,20),7) for _ in chosen]
        residual = [count[i]-empty[i] for i in range(len(chosen))]
        selected = [i for i,k in enumerate(keep) if k]
        whole = sum(weights[i]*residual[i] for i in selected)
        lane_sum = sum(sum(weights[i]*residual[i] for i in selected
                           if owner(*chosen[i]) == k) for k in range(4))
        roots = {original(*chosen[i]) for i in selected}
        fibre_sum = sum(sum(weights[i]*residual[i] for i in selected
                            if original(*chosen[i]) == q) for q in roots)
        assert whole == lane_sum == fibre_sum
        assert whole + sum(weights[i]*residual[i] for i in range(len(chosen))
                           if not keep[i]) == sum(weights[i]*residual[i] for i in range(len(chosen)))
        # Root-dependent toy normalizer, never replaced by one fixed root.
        atom = lambda q,i: (2+q)/(i+1)
        assert sum(sum(weights[i]*atom(q,i) for i in selected
                       if original(*chosen[i]) == q) for q in roots) == \
               sum(weights[i]*atom(original(*chosen[i]),i) for i in selected)
    primes = [n for n in range(2,301) if all(n%d for d in range(2,int(n**.5)+1))]
    products = {}
    for p in primes:
        for q in primes:
            if p >= q: continue
            assert p*q not in products
            products[p*q] = (p,q)
            for height in (F(0),F(1,10**9),F(1),F(10**9)):
                assert height/F(p*q) <= height/F(p*p)
    inventory = []
    for path in sorted(HERE.glob('P3*.lean')):
        raw = path.read_bytes(); text = raw.decode('utf-8'); clean = strip_comments(text)
        assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b|#(?:eval|reduce)',clean),path.name
        stack = []; pairs = {')':'(',']':'[','}':'{'}
        for ch in clean:
            if ch in '([{': stack.append(ch)
            elif ch in pairs:
                assert stack and stack.pop() == pairs[ch], (path.name,ch)
        assert not stack, path.name
        ds = [{'name':m.group(2),'kind':m.group(1),'line':text[:m.start()].count('\n')+1}
              for m in re.finditer(r'(?m)^(?:private )?(def|abbrev|theorem|inductive) (\w+)',text)]
        inventory.append({'file':path.name,'bytes':len(raw),'lines':len(text.splitlines()),
            'sha256':hashlib.sha256(raw).hexdigest(),
            'git_blob_sha':hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest(),
            'imports':re.findall(r'(?m)^import (\S+)',text),'declarations':ds})
    ledger = json.loads((HERE/'EXTERNAL_INPUTS.json').read_text())
    assert all(x['action'] == 'record_only_not_implemented' for x in ledger['inputs'])
    assert not ledger['implemented_external_inputs'] and not ledger['new_axioms']
    checks_out = {'status':'PASS_STATIC_AND_INDEPENDENT_FINITE_TESTS_ONLY',
        'closed_triangle_cases':len(points),'explicit_boundary_cases':len(boundaries),
        'distinct_geometry_cases':len(checks),'owner_case_counts':lane_counts,
        'signed_partition_root_normalizer_cases':600,'ordered_prime_product_pairs':len(products),
        'reciprocal_bound_cases':4*len(products),
        'proof_files':len(inventory),'proof_lines':sum(x['lines'] for x in inventory),
        'declarations':sum(len(x['declarations']) for x in inventory),
        'lean_executed':False,'kernel_replay':False,'external_inputs_implemented':False,
        'actual_project_certificates_executed':False,'independent_reviewer':False}
    (HERE/'INVENTORY.json').write_text(json.dumps(inventory,ensure_ascii=False,indent=2)+'\n')
    (HERE/'CHECKS.json').write_text(json.dumps(checks_out,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps(checks_out,ensure_ascii=False,indent=2))

if __name__ == '__main__': main()
