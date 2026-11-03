#!/usr/bin/env python3
"""Lexical hygiene and exact-rational toy regressions, NOT Lean verification.
No original archive, fixture, numerical producer or external theorem is run.
Run in this directory. Failures abort; a passing JSON is written only at end.
"""
from __future__ import annotations
import hashlib
import itertools
import json
import pathlib
import random
import re
from fractions import Fraction as F

ROOT = pathlib.Path(__file__).resolve().parent
CAP = F(153, 256)


def strip_lean(text: str) -> str:
    out, i, depth, string = [], 0, 0, False
    while i < len(text):
        pair = text[i:i+2]
        if depth:
            if pair == '/-': depth += 1; i += 2
            elif pair == '-/': depth -= 1; i += 2
            else: out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif string:
            if text[i] == '\\': i += 2
            elif text[i] == '"': string = False; i += 1
            else: out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif pair == '/-': depth = 1; i += 2
        elif pair == '--':
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        elif text[i] == '"': string = True; i += 1
        else: out.append(text[i]); i += 1
    assert not depth and not string, 'unterminated comment or string'
    return ''.join(out)


def blob(data: bytes) -> str:
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def rounded(n: int, x: F) -> F:
    d = n + 1
    y = max(F(0), min(CAP, x))
    return max(F(0), F((d*y).__floor__()-1, d))


def protect(n: int, b: F, x: F) -> F:
    return max(b, rounded(n, x))


def witness(n: int, b: F, seed: F, values: list[F], active: list[bool]):
    raw = max([seed] + [v for v, a in zip(values, active) if a])
    old, new = protect(n, b, seed), protect(n, b, raw)
    tag = next((i for i, (v, a) in enumerate(zip(values, active))
                if a and v == raw), None) if old < new else None
    return old, raw, new, tag


def regressions() -> dict:
    rng = random.Random(11032026)
    count = dict(raw_winner=0, boundary=0, mask_collision=0,
                 certified_box=0, rejected_box=0, ancestor=0, gate_transport=0)
    for _ in range(7000):
        n = rng.randrange(1, 120)
        b, seed = F(rng.randrange(-10, 90), 100), F(rng.randrange(-20, 90), 100)
        vals = [F(rng.randrange(-30, 100), 100) for _ in range(rng.randrange(9))]
        act = [bool(rng.randrange(2)) for _ in vals]
        old, raw, new, tag = witness(n, b, seed, vals, act)
        assert (tag is None) == (not old < new)
        if tag is not None:
            assert act[tag] and vals[tag] == raw
            assert new == rounded(n, vals[tag])
            assert not any(a and v == raw for v, a in zip(vals[:tag], act[:tag]))
        assert old <= new
        count['raw_winner'] += 1
    # Original closed-fourth / half-open-fifth conventions, including equality.
    for x in [F(-1, 10), F(0), F(1, 2), F(1), F(11, 10)]:
        a4, a5 = F(0) <= x <= 1, F(0) <= x < 1
        r4 = witness(99, F(1,2), F(1,2), [F(29,50)], [a4])
        r5 = witness(99, F(1,2), F(1,2), [F(29,50)], [a5])
        assert (r4[-1] is not None) == a4
        assert (r5[-1] is not None) == a5
        count['boundary'] += 1
    # Equality with inherited seed must remain none even with an attaining row.
    for n in range(1, 100):
        assert witness(n,F(1,2),F(29,50),[F(29,50)],[True])[-1] is None
        count['boundary'] += 1
    # Same cap, different true maximizing rows/masks: scalar lookup is insufficient.
    states = [witness(39,F(1,2),F(1,2),
                      [F(29,50)+F(t,200),F(29,50)-F(t,200)], [True,True])
              for t in [-1,1]]
    assert states[0][2] == states[1][2] == F(11,20)
    assert states[0][3] != states[1][3]
    count['mask_collision'] += 1
    # A raw-current guard must not be reevaluated using a rounded parent.
    assert not F(11,20) <= F(27,50)
    assert protect(9,F(1,2),F(11,20)) <= F(27,50)
    count['boundary'] += 1
    # Complete exact comparison signature on 1D closed boxes: tag and cap fixed.
    for n in [4,9,19,39]:
        d = n + 1
        lines = [(F(0), F(0)), (CAP,F(0)), (F(1,2),F(0)),
                 (F(29,50),F(1,100)), (F(29,50),F(-1,100)),
                 (F(0),F(1)), (F(1),F(0))]
        lines += [(F(j+1,d),F(0)) for j in range(n+1)]
        def signature(t):
            v = [a+b*t for a,b in lines]
            return [(x<y,x<=y) for x in v for y in v]
        def certificate(lo,hi):
            s = signature((lo+hi)/2)
            for ((a,b),(c,dv)),bits in zip(itertools.product(lines,repeat=2),s):
                low, high = sorted([a-c+(b-dv)*lo,a-c+(b-dv)*hi])
                if not ((high<0 if bits[0] else 0<=low) and
                        (high<=0 if bits[1] else 0<low)):
                    return False
            return True
        for m in [7,15,31]:
            for j in range(-m,m):
                lo,hi=F(j,m),F(j+1,m)
                if not certificate(lo,hi):
                    count['rejected_box'] += 1
                    continue
                ref=None
                for k in range(5):
                    t=lo+(hi-lo)*F(k,4)
                    current=witness(n,F(1,2),F(1,2),
                        [F(29,50)+t/100,F(29,50)-t/100],[True,True])
                    pair=(current[2],current[3])
                    if ref is None: ref=pair
                    assert pair==ref and signature(t)==signature((lo+hi)/2)
                count['certified_box'] += 1
    for _ in range(1000):
        t=[F(rng.randrange(100),100) for _ in range(8)]
        u=t[:5]+[F(rng.randrange(100),100) for _ in range(3)]
        for k in [4,5]:
            def local(x):
                v=[F(1,2)+sum(x[:k])/100,F(29,50)-sum(x[:k])/200]
                return witness(49,F(1,2),F(1,2),v,[True,True])[-1]
            assert local(t)==local(u)
            count['ancestor']+=1
    for n in range(10,90):
        h=F(1,n+1)
        for delta in [F(1,50),F(1,25),F(2,25),F(1,10)]:
            M=F(29,50)
            if 4*h<delta:
                g=M-delta
                assert g+delta/2<rounded(n,M)
                assert rounded(n,M)+h<=M
                count['gate_transport']+=1
    assert count['certified_box'] > 0 and count['rejected_box'] > 0
    return {'counts':count,'total':sum(count.values()),
            'scope':'exact-rational toy model only; no original archive or Lean evaluation'}


def main() -> None:
    files, graph = [], {}
    for p in sorted(ROOT.glob('*.lean')):
        data=p.read_bytes(); text=data.decode('utf-8'); clean=strip_lean(text)
        assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b',clean),p.name
        stack=[]; pairs={')':'(',']':'[','}':'{','⟩':'⟨'}
        for c in clean:
            if c in pairs.values(): stack.append(c)
            elif c in pairs:
                assert stack and stack.pop()==pairs[c],(p.name,c)
        assert not stack,p.name
        decls=re.findall(r'(?m)^(?:@\[.*?\]\s*)?(?:private\s+)?(?:def|abbrev|theorem|lemma)\s+([\w.]+)',clean)
        assert len(decls)==len(set(decls)),p.name
        imports=re.findall(r'(?m)^import\s+(\S+)',clean)
        graph[p.stem]=[x.split('.')[-1] for x in imports]
        files.append({'file':p.name,'bytes':len(data),'lines':len(text.splitlines()),
                      'declarations':len(decls),'sha256':hashlib.sha256(data).hexdigest(),
                      'git_blob_sha1':blob(data),'imports':imports})
    seen=set(); pending=set()
    def visit(name):
        assert name not in pending,'new-module cycle'
        if name in seen or name not in graph:return
        pending.add(name)
        for dep in graph[name]:visit(dep)
        pending.remove(name);seen.add(name)
    for key in graph:visit(key)
    report={'scope':'lexical hygiene and toy regressions, not formal verification',
            'compiled':False,'kernel_replayed':False,'independent_review':False,
            'transitive_axioms_checked':False,'original_archive_loaded':False,
            'external_proofs_implemented':False,'new_module_graph_acyclic':True,
            'files':files,'regression':regressions()}
    (ROOT/'STATIC_QA.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'modules':len(files),'lines':sum(f['lines'] for f in files),
                      'declarations':sum(f['declarations'] for f in files),
                      'regression':report['regression']},indent=2))

if __name__=='__main__':main()
