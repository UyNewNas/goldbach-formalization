"""Static source checks and independent exact-rational regressions.

NOT Lean elaboration, a project proof guard, a numerical certificate,
a test of analytic asymptotics, or proof of Python/Lean correspondence.
"""
from __future__ import annotations
import hashlib
import json
import re
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent

def strip_comments(text: str) -> str:
    out: list[str] = []
    i = 0
    depth = 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1
            i += 2
        elif depth:
            if text[i] == '\n':
                out.append('\n')
            i += 1
        elif text.startswith('--', i):
            j = text.find('\n', i)
            i = len(text) if j < 0 else j
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise ValueError('Unclosed Lean block comment')
    return ''.join(out)


def v(x: F) -> F:
    return min((1+x)/2, (32-34*x)/39, F(57,64)-F(3,2)*x)


def main() -> None:
    level = F(153,256)-F(3,8)*F(417,5000)
    assert level == F(90621,160000)
    # The original three-way v minimum is used, not a substitute profile.
    nbox = 0
    for i in range(51):
        u = F(1,10)+F(i,5000)
        for j in range(51):
            t = F(3,25)+F(j,5000)
            assert F(417,5000) <= u < t < F(19,125)
            assert max(v(t), v(t+u), level) == level
            nbox += 1
    assert level-(1+F(13,100))/2 == F(221,160000)
    assert level-(F(57,64)-F(3,2)*(F(1,10)+F(3,25))) == F(921,160000)
    # Do not silently extend the plateau to the entire original triangle.
    controls = [(F(1,10), F(14,100)), (F(9,100), F(1,10))]
    for u,t in controls:
        assert F(417,5000) <= u < t < F(19,125)
        assert max(v(t),v(t+u),level) != level
    # Complete numeric domain used by the explicit rank-three corollary.
    margin = (1-F(1,100))*F(9,20)-level*(3*F(19,96)+F(1,1000))
    assert margin > 0
    primes = [n for n in range(2,401)
              if all(n%d for d in range(2,int(n**0.5)+1))]
    reciprocal_checks = 0
    for p in primes:
        for q in primes:
            assert F(1,4*(p-1)*(q-1)) <= F(1,p*q)
            reciprocal_checks += 1
    # Actual half-open power endpoints and target exclusions are modelled
    # with integer powers only. This is not the Lean carrier computation.
    carrier_cases = 0
    label_cases = 0
    heights = [F(1,10**9), F(1), F(10**9)]
    for N in [10**8,10**12,10**16,10**20,10**20+39]:
        pbox = [p for p in primes if N%p and p**10 >= N and p**100 < N**11]
        qbox = [q for q in primes if N%q and q**25 >= N**3 and q**100 < N**13]
        box = [(p,q) for p in pbox for q in qbox]
        for p,q in box:
            assert p < q < N and p**5000 >= N**417 and q**125 < N**19
            label_cases += 1
        m1 = sum((F(1,p*q) for p,q in box), F(0))
        mphi = sum((F(1,(p-1)*(q-1)) for p,q in box), F(0))
        assert mphi/4 <= m1
        for H in heights:
            assert sum((H/F(p*q) for p,q in box),F(0)) == H*m1
        carrier_cases += 1
    inventory = []
    for p in sorted(HERE.glob('P2Gamma*.lean')):
        raw = p.read_bytes()
        text = raw.decode('utf-8')
        clean = strip_comments(text)
        bad = re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b|#(?:eval|reduce)',clean)
        assert not bad, (p.name,bad)
        stack = []
        pairs = {')':'(',']':'[','}':'{','⟩':'⟨'}
        for ch in clean:
            if ch in pairs.values(): stack.append(ch)
            elif ch in pairs:
                assert stack and stack.pop() == pairs[ch], (p.name,ch)
        assert not stack,p.name
        declarations = [{'kind':m.group(1),'name':m.group(2),
                         'line':clean[:m.start()].count('\n')+1}
                        for m in re.finditer(r'(?m)^(?:private\s+)?(def|theorem|abbrev)\s+(\w+)',clean)]
        inventory.append({'file':p.name,'bytes':len(raw),'lines':text.count('\n'),
                          'sha256':hashlib.sha256(raw).hexdigest(),
                          'git_blob_sha':hashlib.sha1(f'blob {len(raw)}\0'.encode()+raw).hexdigest(),
                          'imports':re.findall(r'(?m)^import (\S+)',clean),
                          'declarations':declarations})
    checks = {'status':'STATIC_AND_INDEPENDENT_REGRESSION_PASS',
              'rational_plateau_cases':nbox,'outside_plateau_negative_controls':len(controls),
              'prime_pair_reciprocal_comparisons':reciprocal_checks,
              'target_deleted_integer_power_boxes':carrier_cases,
              'toy_box_label_membership_checks':label_cases,
              'amplitude_values':[str(h) for h in heights],
              'plateau_level':str(level),'rank_three_worst_case_margin':str(margin),
              'new_proof_lines':sum(x['lines'] for x in inventory),
              'new_declarations':sum(len(x['declarations']) for x in inventory),
              'forbidden_forms':'NO_MATCH','delimiter_scan':'PASS',
              'lean_compiled':False,'kernel_replayed':False,
              'analytic_limit_tested':False,'python_lean_correspondence_proved':False}
    (HERE/'INVENTORY.json').write_text(json.dumps(inventory,ensure_ascii=False,indent=2)+'\n')
    (HERE/'CHECKS.json').write_text(json.dumps(checks,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps(checks,ensure_ascii=False,indent=2))

if __name__ == '__main__':
    main()
