#!/usr/bin/env python3
"""Lexical hygiene and exact rational toy tests; NOT a Lean/kernel checker.

No numerical archive, producer or literal-row certificate is evaluated. Run in this packet directory.
A failure aborts without generating a passing report.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import hashlib
import json
import random
import re

ROOT = Path(__file__).resolve().parent


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
    if depth or string:
        raise ValueError('Unterminated comment/string')
    return ''.join(out)


CAP=F(153,256)

def rounded(n: int,x:F)->F:
    d=n+1; y=max(F(0),min(CAP,x))
    return max(F(0),F((d*y).__floor__()-1,d))

def lower_gates(t:tuple[F,...],I:set[int])->list[F]:
    out=[F(1,2)]
    for j,v in enumerate(t):
        out.append(sum(t[:j],F(0))+2*v)
        if j not in I:
            out.append(sum((t[i] for i in I),F(0))+
                sum((t[i] for i in range(j) if i not in I),F(0))+2*v)
    return out

def evaluate(a:tuple[F,...],t:tuple[F,...])->F:
    return a[0]+sum((x*y for x,y in zip(a[1:],t)),F(0))

def encode(a:tuple[F,...])->tuple[F,...]:
    return (a[0]+a[4]/2,a[1]-a[4]/2,a[2]-a[4],a[3]-a[4],
            -3*a[4]/2+a[5]/2,a[4]/2-a[5]/2,a[6])

def physical(q:tuple[F,...])->tuple[F,...]:
    return (q[0],q[1],q[2],(1-q[0])/2-q[1]-q[2]-3*q[3]/2+q[4]/2,
            (q[3]-q[4])/2,q[5])

def tests()->dict:
    rng=random.Random(2026110309)
    counts=dict(rounding_range=0,gate_transport=0,fourth_double_debit=0,
                winning_row=0,chart_pullback=0,square_dictionary=0)
    for n in (0,1,3,9,63,255,1023):
        for j in range(601):
            x=CAP*j/600; h=F(1,n+1); y=rounded(n,x)
            assert 0<=y<=x and x-2*h<y
            if y>0: assert y+h<=x
            counts['rounding_range']+=1
    for k in (4,5,6):
        for mask in range(1,2**k):
            I={i for i in range(k) if mask>>i&1}
            for _ in range(18):
                t=tuple(F(rng.randrange(1,20),500) for _ in range(k))
                gates=lower_gates(t,I); M=F(rng.randrange(551,590),1000)
                delta=M-max(gates)
                if delta<=0:continue
                n=max(0,(F(16,1)/delta).__ceil__())
                h=F(1,n+1); y=rounded(n,M)
                assert 4*h<delta and all(g+delta/2<y for g in gates)
                assert y+h<=M
                counts['gate_transport']+=1
                e=delta/16; Mbuf=M-2*e; ybuf=rounded(n,Mbuf)
                assert 8*e<=delta and 8*h<delta
                assert all(g+delta/4<ybuf for g in gates)
                assert ybuf+h+2*e<=M
                counts['fourth_double_debit']+=1
    for _ in range(1800):
        n=rng.randrange(1,100)
        b=F(rng.randrange(0,400),1000)
        parent=max(b,F(rng.randrange(400,520),1000))
        raw=[F(rng.randrange(400,599),1000) for _ in range(10)]
        eligible=[bool(rng.randrange(2)) for _ in raw]
        mapped=[max(b,rounded(n,x)) for x in raw]
        value=max([parent]+[v for v,ok in zip(mapped,eligible) if ok])
        if parent<value:
            winners=[i for i in range(len(raw)) if eligible[i] and mapped[i]==value]
            assert winners and all(value==rounded(n,raw[i]) for i in winners)
        counts['winning_row']+=1
    for _ in range(700):
        a=tuple(F(rng.randrange(-20,21),13) for _ in range(7))
        q=tuple(F(rng.randrange(-20,21),17) for _ in range(6))
        assert evaluate(encode(a),q)==evaluate(a,physical(q))
        counts['chart_pullback']+=1
    # ALL bit masks, all physical square dictionaries; NOT original row-list membership.
    for mask in range(1,64):
        I={i for i in range(6) if mask>>i&1}
        for j in range(6):
            f=(F(0),)+tuple(F(i<j)+2*F(i==j) for i in range(6))
            s=(F(0),)+tuple(F(i in I)+F(i<j and i not in I)+2*F(i==j) for i in range(6))
            for _ in range(3):
                t=tuple(F(rng.randrange(-10,11),19) for _ in range(6))
                assert evaluate(f,t)==sum(t[:j],F(0))+2*t[j]
                assert evaluate(s,t)==sum((t[i] for i in I),F(0))+sum(
                    (t[i] for i in range(j) if i not in I),F(0))+2*t[j]
                counts['square_dictionary']+=1
    M=F(14,25); base=F(1,2); gate=F(27,50)
    new=max(base,rounded(9,M))
    assert gate<M and new<=gate
    return dict(counts=counts,total_cases=sum(counts.values()),
        finite_value_not_a_license=dict(raw=str(M),seed=str(base),gate=str(gate),finite=str(new)),
        scope='Exact Fraction toy algebra ONLY; no original later-row membership or archive byte test')


def blob_sha(data: bytes) -> str:
    return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()


def main() -> None:
    files=[]; graph={}
    names={p.stem for p in ROOT.glob('*.lean')}
    for p in sorted(ROOT.glob('*.lean')):
        raw=p.read_bytes(); text=raw.decode(); code=strip_comments_strings(text)
        bad=re.findall(r'(?<![\w])(?:sorry|admit|axiom|unsafe|native_decide)(?![\w])|#(?:eval|reduce)',code)
        assert not bad, (p.name,bad)
        stack=[]; pairs={')':'(',']':'[','}':'{','⟩':'⟨'}
        for char in code:
            if char in '([{⟨':stack.append(char)
            elif char in pairs:
                assert stack and stack.pop()==pairs[char], (p.name,char)
        assert not stack, (p.name,stack)
        imports=re.findall(r'^import\s+(\S+)',code,re.M)
        declarations=re.findall(r'^(?:(?:private|protected|noncomputable)\s+)*(?:@\[[^\]]+\]\s*)?(def|theorem|lemma|abbrev|structure|inductive)\s+(\S+)',code,re.M)
        files.append(dict(path=p.name,bytes=len(raw),lines=len(text.splitlines()),
                          sha256=hashlib.sha256(raw).hexdigest(),git_blob_sha1=blob_sha(raw),
                          imports=imports,declarations_count=len(declarations)))
        graph[p.stem]=[i.rsplit('.',1)[-1] for i in imports if i.rsplit('.',1)[-1] in names]
    seen=set(); active=set()
    def visit(n):
        assert n not in active, ('cycle',n)
        if n in seen:return
        active.add(n)
        for d in graph[n]:visit(d)
        active.remove(n);seen.add(n)
    for n in graph:visit(n)
    report=dict(scope='lexical hygiene and exact rational toy checks only',
                lean_compiled=False,kernel_replayed=False,independent_review=False,
                transitive_axioms_checked=False,original_archive_loaded=False,
                numerical_producer_rerun=False,full_library_materialized=False,later_literal_membership_evaluated=False,
                new_module_graph_acyclic=True,regression=tests(),files=files)
    (ROOT/'STATIC_QA.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({'lean_files':len(files),'lean_lines':sum(f['lines'] for f in files),
                      'declarations':sum(f['declarations_count'] for f in files),
                      'regression':report['regression']},ensure_ascii=False,indent=2))

if __name__=='__main__':main()
