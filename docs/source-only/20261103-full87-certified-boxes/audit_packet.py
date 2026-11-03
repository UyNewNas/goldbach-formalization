#!/usr/bin/env python3
"""Lexical hygiene and exact rational toy tests; NOT a Lean/kernel checker.

No numerical archive or producer is loaded. Run in this packet directory.
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


@dataclass(frozen=True)
class Affine:
    c: F
    a: tuple[F, ...]
    def value(self, t: tuple[F, ...]) -> F:
        assert len(t) == len(self.a)
        return self.c + sum((x*y for x, y in zip(self.a, t)), F(0))
    def sub(self, other: 'Affine') -> 'Affine':
        return Affine(self.c-other.c, tuple(x-y for x,y in zip(self.a,other.a)))
    def bounds(self, lo: tuple[F, ...], hi: tuple[F, ...]) -> tuple[F, F]:
        assert len(lo) == len(hi) == len(self.a)
        return (
            self.c + sum((a*(l if a >= 0 else h) for a,l,h in zip(self.a,lo,hi)), F(0)),
            self.c + sum((a*(h if a >= 0 else l) for a,l,h in zip(self.a,lo,hi)), F(0)),
        )
    @property
    def mass(self) -> F:
        return sum(map(abs,self.a), F(0))


def certified(atoms: tuple[Affine, ...], t: tuple[F, ...], lo: tuple[F, ...], hi: tuple[F, ...]) -> bool:
    for a,b in product(atoms, repeat=2):
        d = a.sub(b); x = d.value(t); l,u = d.bounds(lo,hi)
        if not ((u < 0 if x < 0 else l >= 0) and (u <= 0 if x <= 0 else l > 0)):
            return False
    return True


def tests() -> dict:
    rng = random.Random(2026110308)
    counts = dict(endpoint_enclosures=0, separated_certificates=0,
                  constant_equalities=0, mesh_coverage=0,
                  projected_labels=0, third_tag_refinements=0,
                  one_dimensional_wall_volume=0)
    for k in range(1,5):
        for _ in range(180):
            a = Affine(F(rng.randrange(-8,9),7), tuple(F(rng.randrange(-6,7),5) for _ in range(k)))
            t = tuple(F(rng.randrange(-5,6),9) for _ in range(k))
            r = F(rng.randrange(1,10),31)
            lo = tuple(x-r for x in t); hi = tuple(x+r for x in t)
            l,u = a.bounds(lo,hi)
            assert a.value(t)-r*a.mass <= l <= u <= a.value(t)+r*a.mass
            for corner in product(*[(l,h) for l,h in zip(lo,hi)]):
                assert l <= a.value(corner) <= u
            counts['endpoint_enclosures'] += 1
            # Deliberately include two equal atoms and unequal constant atoms.
            atoms = (a,a,Affine(F(0),(F(0),)*k),Affine(F(1,3),(F(0),)*k))
            gaps = [abs(d.value(t))/(d.mass+1) for x,y in product(atoms,repeat=2)
                    if any((d:=x.sub(y)).a)]
            if gaps and min(gaps)>0:
                eta = min(gaps)/2
                low = tuple(x-eta for x in t); high=tuple(x+eta for x in t)
                assert certified(atoms,t,low,high)
                counts['separated_certificates'] += 1
            zeros = (Affine(F(0),(F(0),)*k),Affine(F(0),(F(0),)*k),Affine(F(1),(F(0),)*k))
            assert certified(zeros,t,lo,hi)
            counts['constant_equalities'] += 1
    # A crossing wall at the midpoint must FAIL, not be treated as a null identity.
    x = Affine(F(0),(F(1),)); half = Affine(F(1,2),(F(0),))
    assert not certified((x,half),(F(1,2),),(F(0),),(F(1),))
    assert not certified((x,half),(F(1,4),),(F(0),),(F(1),))
    for t0 in [F(j,97) for j in range(97) if F(j,97) != F(1,2)]:
        eta = abs(t0-F(1,2))/2
        for m in (0,1,2,7,31,127,255):
            d=m+1; j=(d*t0).__floor__(); lo=(F(j,d),); hi=(F(j+1,d),)
            mid=((lo[0]+hi[0])/2,)
            if F(1,d)<=eta:
                assert certified((x,half),mid,lo,hi)
            if not certified((x,half),mid,lo,hi):
                assert abs(t0-F(1,2)) < F(2,d)
            counts['mesh_coverage'] += 1
    for m in range(24):
        t=tuple(F(rng.randrange(97),97) for _ in range(8))
        full=tuple(((m+1)*v).__floor__() for v in t)
        for k in (3,4,5,6):
            assert tuple(((m+1)*v).__floor__() for v in t[:k])==full[:k]
            counts['projected_labels'] += 1
    # Exact intersection: fine Ico and original third Ico, including faces.
    for coarse in range(1,8):
        step=F(19,96*(coarse+1))
        for m in (0,3,11):
            for j3 in range(coarse+1):
                cl,cu=j3*step,(j3+1)*step
                for jf in range(m+1):
                    fl,fu=F(jf,m+1),F(jf+1,m+1)
                    l,u=max(fl,cl),min(fu,cu)
                    for v in (fl,fu,cl,cu,(l+u)/2):
                        assert (l<=v<u)==((fl<=v<fu) and (cl<=v<cu))
                        counts['third_tag_refinements'] += 1
    for m in range(1,192):
        d=m+1; bad=0
        for j in range(d):
            lo,hi=(F(j,d),),(F(j+1,d),)
            mid=((lo[0]+hi[0])/2,)
            bad += not certified((x,half),mid,lo,hi)
        assert F(bad,d)<=F(2,d)
        counts['one_dimensional_wall_volume'] += 1
    return {'counts':counts, 'total_cases':sum(counts.values()),
            'crossing_wall_midpoint_rejected':True,
            'scope':'exact Fraction toy instances; NOT the original data or a universal proof'}


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
                numerical_producer_rerun=False,full_library_materialized=False,
                new_module_graph_acyclic=True,regression=tests(),files=files)
    (ROOT/'STATIC_QA.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({'lean_files':len(files),'lean_lines':sum(f['lines'] for f in files),
                      'declarations':sum(f['declarations_count'] for f in files),
                      'regression':report['regression']},ensure_ascii=False,indent=2))

if __name__=='__main__':main()
