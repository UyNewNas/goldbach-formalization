#!/usr/bin/env python3
"""Independent finite checks and source-contract checks; NOT Lean elaboration."""
import hashlib, itertools, json, re
from pathlib import Path
import sympy as s
p=Path(__file__).parent
src=(p/'P3FourierPointCoordinateBridge.lean').read_text()
assert src.count('namespace ImbalancedChen.P3FourierPointCoordinateBridge')==1
names=["chartEquiv_basisDirection","shift_eq_add_direction","chart_shift",
       "coordinateDeriv_pulled_eq_fderiv","orderedDirections_apply",
       "orderedDirections_doubled","mixed_pullback_eq_frechet",
       "mixed_actual_eq_frechet","actualMixedFamily_eq_realFrechet"]
for name in names:
    assert re.search(r'(?m)^(?:private )?theorem '+name+r'\b',src), name
# Remove line and block comments before proof-escape scan.
clean = re.sub(r'/-.*?-/', '', src, flags=re.S)
clean = re.sub(r'--[^\n]*', '', clean)
for pat in [r'\bsorry\b',r'\badmit\b',r'\baxiom\b',r'\bunsafe\b',r'\bnative_decide\b',r'\bpartial\s+def\b']:
    assert not re.search(pat,clean), pat
stack=[]; pairs={')':'(',']':'[','}':'{'}
for ch in clean:
    if ch in '([{': stack.append(ch)
    if ch in ')]}':
        assert stack and stack.pop()==pairs[ch], 'unbalanced'
assert not stack
# Shift-to-point and Euclidean standard vector are identical componentwise.
shift_cases=0
for d in range(1,7):
    p0=[3*j-5 for j in range(d)]
    for i in range(d):
        for t in (-3,-1,0,2,5):
            q=[p0[j]+(t if j==i else 0) for j in range(d)]
            basis=[int(j==i) for j in range(d)]
            assert q == [p0[j]+t*basis[j] for j in range(d)]
            shift_cases+=1
# Ordered list preserves occurrences; differentiating x_i^r twice != once.
ordered_cases=0
for d in range(1,5):
    xs=s.symbols('x:'+str(d))
    f=sum((i+2)*xs[i]**(i+3) for i in range(d))
    f+=s.prod(xs) if d>0 else 1
    for n in range(5):
        for coords in itertools.product(range(d),repeat=n):
            g=f
            for i in reversed(coords):
                g=s.diff(g,xs[i])
            # Independent coefficient-based direct formal directional derivative.
            h=f
            for i in reversed(coords):
                u=s.symbols('t')
                displaced=h.subs(xs[i],xs[i]+u)
                h=s.diff(displaced,u).subs(u,0)
            assert s.expand(g-h)==0, (d,coords)
            ordered_cases+=1
assert s.diff(s.Symbol('v')**3,s.Symbol('v'),2)!=s.diff(s.Symbol('v')**3,s.Symbol('v'))
checks={'source_only':True,'lean':'NOT_RUN','kernel':'NOT_RUN','ci':'NOT_RUN',
  'forbidden_escape_tokens':0,'delimiter_balance':True,
  'point_shift_cases':shift_cases,'ordered_mixed_polynomial_cases':ordered_cases,
  'proof_file_sha256':hashlib.sha256(src.encode()).hexdigest(),
  'proof_lines':len(src.splitlines()),'endpoints':names,
  'warning':'Finite algebra/regression and static scans only; not Lean or analytic verification'}
(p/'CHECKS.json').write_text(json.dumps(checks,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(checks,indent=2))
