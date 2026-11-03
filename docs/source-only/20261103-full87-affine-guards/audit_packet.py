#!/usr/bin/env python3
"""Source hygiene and exact rational model tests. NOT a Lean/kernel checker.

No archive fixture or original producer is run. A small independent Python
model checks comparison semantics, equalities, finite threshold rounding
and closed-box sign certificates on toy instances only.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import random
import re

ROOT = Path(__file__).resolve().parent
CAP = F(153, 256)


def strip_comments_strings(text: str) -> str:
    out, i, depth, string = [], 0, 0, False
    while i < len(text):
        pair, c = text[i:i+2], text[i]
        if depth:
            if pair == '/-': depth += 1; i += 2
            elif pair == '-/': depth -= 1; i += 2
            else: out.append('\n' if c == '\n' else ' '); i += 1
        elif string:
            if c == '\\': i += 2
            elif c == '"': string = False; i += 1
            else: out.append('\n' if c == '\n' else ' '); i += 1
        elif pair == '/-': depth = 1; i += 2
        elif pair == '--':
            j = text.find('\n', i); i = len(text) if j < 0 else j
        elif c == '"': string = True; i += 1
        else: out.append(c); i += 1
    if depth or string: raise ValueError('Unterminated comment/string')
    return ''.join(out)


@dataclass(frozen=True)
class Affine:
    constant: F
    coefficient: tuple[F, ...]
    def eval(self, t: tuple[F, ...]) -> F:
        assert len(t) == len(self.coefficient)
        return self.constant + sum((a*x for a,x in zip(self.coefficient,t)), F(0))
    def sub(self, b: 'Affine') -> 'Affine':
        return Affine(self.constant-b.constant, tuple(x-y for x,y in zip(self.coefficient,b.coefficient)))
    def interval(self, lo: tuple[F, ...], hi: tuple[F, ...]) -> tuple[F,F]:
        lower = self.constant + sum((a*(l if a >= 0 else h) for a,l,h in zip(self.coefficient,lo,hi)), F(0))
        upper = self.constant + sum((a*(h if a >= 0 else l) for a,l,h in zip(self.coefficient,lo,hi)), F(0))
        return lower, upper


@dataclass(frozen=True)
class Program:
    kind: str
    args: tuple


def leaf(x: Affine) -> Program: return Program('leaf',(x,))
def const(x: F) -> Program: return leaf(Affine(F(x),(F(0),F(0))))


@lru_cache(maxsize=None)
def evaluate(p: Program, t: tuple[F,...]) -> F:
    if p.kind == 'leaf': return p.args[0].eval(t)
    a, b = evaluate(p.args[0],t), evaluate(p.args[1],t)
    if p.kind == 'sup': return max(a,b)
    if p.kind == 'inf': return min(a,b)
    branch = (a < b) if p.kind == 'lt' else (a <= b)
    return evaluate(p.args[2] if branch else p.args[3],t)


@lru_cache(maxsize=None)
def leaves(p: Program) -> frozenset[Affine]:
    if p.kind == 'leaf': return frozenset(p.args)
    return frozenset().union(*(leaves(a) for a in p.args))


def signature(p: Program, t: tuple[F,...]) -> dict:
    values = {a:a.eval(t) for a in leaves(p)}
    return {(a,b):(x<y,x<=y) for a,x in values.items() for b,y in values.items()}


def select(p: Program, sig: dict) -> Affine:
    cache = {}
    def run(q: Program) -> Affine:
        if q in cache: return cache[q]
        if q.kind == 'leaf': result = q.args[0]
        else:
            a,b = run(q.args[0]),run(q.args[1]); lt,le = sig[a,b]
            if q.kind == 'sup': result = b if le else a
            elif q.kind == 'inf': result = a if le else b
            else: result = run(q.args[2] if (lt if q.kind=='lt' else le) else q.args[3])
        cache[q] = result
        return result
    return run(p)


def round_scalar(n: int, x: F) -> F:
    y = max(F(0), min(CAP,x)); z = ((n+1)*y).__floor__()
    return max(F(0),F(z-1,n+1))


def round_program(n: int, p: Program) -> Program:
    y = Program('sup',(const(0),Program('inf',(const(CAP),p))))
    result = const(0)
    # Parallel tests all read y, never the fold's accumulated result.
    for j in range(n,-1,-1):
        result = Program('le',(const(F(j+1,n+1)),y,
            Program('sup',(const(F(j,n+1)),result)),result))
    return result


def tests() -> dict:
    rng = random.Random(20261103)
    count = {'quantizer_scalar_cases':0,'program_semantics_cases':0,
             'quantizer_program_cases':0,'box_certificate_cases':0,'boundary_cases':0}
    for n in range(32):
        pts = {F(k,97) for k in range(-97,195)} | {CAP,F(0)}
        for j in range(n+2):
            x = F(j,n+1)
            pts |= {x,x-F(1,1000003),x+F(1,1000003)}
        for x in pts:
            y = max(F(0),min(CAP,x))
            threshold = max([F(0)]+[F(j,n+1) for j in range(n+1) if F(j+1,n+1)<=y])
            assert threshold == round_scalar(n,x)
            count['quantizer_scalar_cases'] += 1
    atoms = [Affine(F(rng.randrange(-3,4),7),tuple(F(rng.randrange(-3,4),5) for _ in range(2))) for _ in range(9)]
    atoms += [Affine(F(0),(F(0),F(0))),Affine(F(1,2),(F(0),F(0)))]
    def make(depth:int) -> Program:
        if depth == 0: return leaf(rng.choice(atoms))
        kind = rng.choice(('sup','inf','lt','le'))
        return Program(kind,tuple(make(depth-1) for _ in range(2 if kind in ('sup','inf') else 4)))
    points = [(F(a,7),F(b,11)) for a,b in [(0,0),(1,1),(-1,2),(3,5),(2,-3),(-2,-1)]]
    for _ in range(36):
        p = make(2)
        for t in points:
            sig = signature(p,t)
            assert select(p,sig).eval(t) == evaluate(p,t)
            count['program_semantics_cases'] += 1
        for n in (0,1,3,7):
            qp = round_program(n,p)
            for t in points:
                assert evaluate(qp,t) == round_scalar(n,evaluate(p,t))
                output = select(qp,signature(qp,t))
                assert output.coefficient == (F(0),F(0))
                assert output.eval(t) == evaluate(qp,t)
                count['quantizer_program_cases'] += 1
    # Strict and weak equalities must not share a Boolean convention.
    a = leaf(atoms[0]); yes,no = const(2),const(3)
    for t in points:
        assert evaluate(Program('lt',(a,a,yes,no)),t)==3
        assert evaluate(Program('le',(a,a,yes,no)),t)==2
        count['boundary_cases'] += 1
    for _ in range(80):
        a,b = rng.choice(atoms),rng.choice(atoms)
        lo = tuple(F(rng.randrange(-6,2),10) for _ in range(2))
        hi = tuple(x+F(rng.randrange(0,8),10) for x in lo)
        low,high = a.sub(b).interval(lo,hi)
        for u in (F(0),F(1,3),F(1,2),F(1)):
            t = tuple(x+(y-x)*u for x,y in zip(lo,hi))
            value = a.eval(t)-b.eval(t)
            assert low <= value <= high
            if high < 0: assert a.eval(t)<b.eval(t)
            if low >= 0: assert not a.eval(t)<b.eval(t)
            if high <= 0: assert a.eval(t)<=b.eval(t)
            if low > 0: assert not a.eval(t)<=b.eval(t)
            count['box_certificate_cases'] += 1
    raw,cmp,base,n = F(11,20),F(27,50),F(1,2),9
    assert not raw<=cmp and max(base,round_scalar(n,raw))<=cmp
    return {'counts':count,'total_cases':sum(count.values()),
            'scope':'toy rational model ONLY; not source data, kernel checking, or universal verification',
            'raw_guard_counterexample':{'raw_current':str(raw),'comparison':str(cmp),'rounded_current':str(max(base,round_scalar(n,raw))),
                'raw_guard':False,'wrong_recomputed_guard':True}}


def main() -> None:
    info=[]
    for path in sorted(ROOT.glob('*.lean')):
        raw=path.read_bytes(); text=raw.decode(); code=strip_comments_strings(text)
        bad=re.findall(r'(?<![\w\'])\b(?:sorry|admit|axiom|unsafe|native_decide|sorryAx)\b',code)
        assert not bad,(path.name,bad)
        stack=[]; op='([{⟨'; cl=')]}⟩'
        for ch in code:
            if ch in op: stack.append(ch)
            elif ch in cl:
                assert stack and stack.pop()==op[cl.index(ch)],path.name
        assert not stack,path.name
        decls=re.findall(r'^(?:@\[[^\]]+\]\s*)?(?:private\s+)?(?:theorem|def|abbrev|structure|inductive)\s+([\w.]+)',code,re.M)
        assert len(decls)==len(set(decls)),(path.name,'duplicate declaration')
        info.append({'file':path.name,'module':'ImbalancedChen.'+path.stem,
            'bytes':len(raw),'lines':len(text.splitlines()),'sha256':hashlib.sha256(raw).hexdigest(),
            'git_blob_sha1':hashlib.sha1(f'blob {len(raw)}\0'.encode()+raw).hexdigest(),
            'imports':re.findall(r'^import\s+(\S+)',code,re.M),'declarations':decls,
            'forbidden_tokens':bad,'delimiter_check':'passed'})
    graph={f['module']:f['imports'] for f in info}; done=set(); active=set()
    def visit(m):
        if m not in graph or m in done:return
        assert m not in active,'new-module cycle';active.add(m)
        for q in graph[m]:visit(q)
        active.remove(m);done.add(m)
    for m in graph:visit(m)
    regression=tests()
    report={'scope':'static syntax hygiene and exact toy tests only','lean_compiled':False,
        'kernel_replayed':False,'independent_review':False,'transitive_axioms_checked':False,
        'original_archive_loaded':False,'numerical_producer_rerun':False,'all_tables_materialized':False,
        'new_module_graph_acyclic':True,'regression':regression,'files':info}
    (ROOT/'STATIC_QA.json').write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps({'lean_files':len(info),'lean_lines':sum(f['lines'] for f in info),
        'declarations':sum(len(f['declarations']) for f in info),'regression':regression['counts'],
        'total_cases':regression['total_cases'],'static_pass':True},ensure_ascii=False))

if __name__=='__main__':main()
