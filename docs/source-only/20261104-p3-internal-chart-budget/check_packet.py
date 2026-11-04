"""Independent exact algebra regressions and a byte inventory, NOT Lean validation.

Does not execute repository prime carriers, Lean guards or numerical producers.
The polynomial transition used for jet tests is deliberately not smoothTransition:
these tests concern finite chain/product algebra, not its analytic bounds.
"""
from __future__ import annotations
import hashlib
import itertools
import json
import re
from fractions import Fraction as F
from pathlib import Path
import sympy as sp

ROOT = Path(__file__).resolve().parent

def uncomment(text: str) -> str:
    out, depth, i = [], 0, 0
    while i < len(text):
        if text[i:i+2] == '/-': depth += 1; i += 2; continue
        if depth and text[i:i+2] == '-/': depth -= 1; i += 2; continue
        if not depth and text[i:i+2] == '--':
            j = text.find('\n', i)
            i = len(text) if j < 0 else j
            continue
        if not depth: out.append(text[i])
        elif text[i] == '\n': out.append('\n')
        i += 1
    assert depth == 0, 'unclosed block comment'
    return ''.join(out)

def inventory() -> list[dict]:
    items = []
    for path in sorted(ROOT.glob('*.lean')):
        data = path.read_bytes(); code = uncomment(data.decode())
        assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|extern)\b', code)
        stack = []
        mates = {')':'(', ']':'[', '}':'{', '⟩':'⟨'}
        for c in code:
            if c in '([{⟨': stack.append(c)
            elif c in mates: assert stack and stack.pop() == mates[c], path.name
        assert not stack, path.name
        items.append(dict(path=path.name, bytes=len(data), lines=len(data.decode().splitlines()),
            sha256=hashlib.sha256(data).hexdigest(),
            git_blob_sha=hashlib.sha1(f'blob {len(data)}\0'.encode()+data).hexdigest(),
            imports=re.findall(r'^import\s+(\S+)', code, re.M),
            declarations=[dict(kind=m.group(1), name=m.group(2), line=code[:m.start()].count('\n')+1)
                for m in re.finditer(r'^(?:private\s+)?(theorem|def|abbrev|inductive)\s+(\S+)',code,re.M)],
            forbidden_scan='NO_MATCH', delimiters='BALANCED', lean_elaborated=False))
    return items

# Same polynomial circuit as the four existing weights.
C = lambda c: ('c',sp.Rational(c))
G = lambda j,n=0: ('g',j,n)
A = lambda e,f: ('+',e,f)
M = lambda e,f: ('*',e,f)
sub1 = lambda e:A(C(1),M(C(-1),e))
g = [G(j) for j in range(4)]
lanes = [g[0], M(sub1(g[0]),M(g[1],g[2])),
         M(M(sub1(g[0]),sub1(M(g[1],g[2]))),g[3]),
         M(M(sub1(g[0]),sub1(M(g[1],g[2]))),sub1(g[3]))]

def jet(e, i):
    if e[0] in ('c','a'): return C(0)
    if e[0]=='g': return M(('a',e[1],i),G(e[1],e[2]+1))
    if e[0]=='+': return A(jet(e[1],i),jet(e[2],i))
    return A(M(jet(e[1],i),e[2]),M(e[1],jet(e[2],i)))

def jet_regressions() -> int:
    x = sp.symbols('x0:2'); t = sp.Symbol('t')
    transition = 1+t+t**2+t**3
    coeff = [[-1,-1],[0,-sp.Rational(1,2)],
             [sp.Rational(3,2),sp.Rational(3,2)],[-sp.Rational(3,2),-2]]
    offsets = [sp.Rational(1,7),-sp.Rational(2,5),sp.Rational(3,8),-sp.Rational(1,9)]
    s = sp.Rational(3,2)
    def ev(e):
        if e[0]=='c': return e[1]
        if e[0]=='a': return coeff[e[1]][e[2]]
        if e[0]=='g':
            arg=offsets[e[1]]+s*sum(coeff[e[1]][i]*x[i] for i in range(2))
            return sp.diff(transition,t,e[2]).subs(t,arg)
        if e[0]=='+': return ev(e[1])+ev(e[2])
        return ev(e[1])*ev(e[2])
    count=0
    for e in lanes:
        base=sp.Poly(sp.expand(ev(e)),*x)
        for q in range(4):
            for directions in itertools.product(range(2),repeat=q):
                je=e; expected=base
                for i in reversed(directions): je=jet(je,i); expected=expected.diff(x[i])
                assert sp.Poly(sp.expand(s**q*ev(je)),*x)==expected
                count+=1
    return count

def affine_regressions() -> int:
    coeff = [(-F(1),-F(1)),(F(0),-F(1,2)),(F(3,2),F(3,2)),(-F(3,2),-F(2))]
    offsets = [F(25,128),F(90621,160000)-F(1,2),F(90621,160000)-F(57,64),F(25,64)]
    count=0
    for d in range(4):
        for slot in itertools.product((None,0,1),repeat=d):
            x=[F(2*i-3,7) for i in range(d)]
            for ell in (F(1),F(2),F(7,3)):
                logr=(F(7,13),-F(3,17))
                point=[(logr[i]+sum((x[k] for k in range(d) if slot[k]==i),F(0)))/ell for i in range(2)]
                for m in (0,1,3):
                    s=F(m+1)
                    for j in range(4):
                        a=[F(0) if i is None else coeff[j][i]/ell for i in slot]
                        b=s*(offsets[j]+sum((coeff[j][i]*logr[i]/ell for i in range(2)),F(0)))
                        assert all(abs(v)<=2 for v in a)
                        lhs=b+s*sum((a[k]*x[k] for k in range(d)),F(0))
                        rhs=s*(offsets[j]+sum((coeff[j][i]*point[i] for i in range(2)),F(0)))
                        assert lhs==rhs
                        for z in x: assert 2+s*(z/s)==z+2 and -1+s*(z/s)==z-1
                        count+=1
    return count

def degree_checks() -> int:
    count=0
    for d in range(7):
        for bits in itertools.product((False,True),repeat=d):
            word=[i for i in range(d) for _ in range(2) if bits[i]]
            assert len(word)==2*sum(bits) and len(word)<=2*d
            for B in range(5):
                assert B*len(word)<=B*(2*d)
                count+=1
    return count

def main():
    results=dict(jet_chain_product_cases=jet_regressions(),
        group_affine_and_cutoff_cases=affine_regressions(),
        finite_mixed_degree_cases=degree_checks(),
        lean_compiler_run=False,kernel_replay=False,repository_producer_run=False,
        actual_smoothTransition_evaluated=False,analytic_inputs_verified=False,
        finite_models_prove_lean_correspondence=False)
    inv=inventory()
    (ROOT/'INVENTORY.json').write_text(json.dumps(inv,ensure_ascii=False,indent=2)+'\n')
    (ROOT/'CHECKS.json').write_text(json.dumps(results,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps(results,indent=2))
if __name__=='__main__': main()
