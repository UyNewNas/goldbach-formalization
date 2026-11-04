#!/usr/bin/env python3
"""Deterministic lexical checks and exact rational TOY regressions.

NOT a Lean parser, elaborator, kernel check, archive evaluator, or proof.
No network, original data fixture, or numerical producer is used.
Run from any directory; a failed assertion aborts before a passing report.
"""
from __future__ import annotations
from collections import Counter
from fractions import Fraction as F
from hashlib import sha1, sha256
from itertools import product
from pathlib import Path
import json
import re

HERE = Path(__file__).resolve().parent
CAP = F(153, 256)


def strip_lean(text: str) -> str:
    out, depth, i, quoted = [], 0, 0, False
    while i < len(text):
        pair = text[i:i + 2]
        if depth:
            if pair == '/-': depth += 1; i += 2; continue
            if pair == '-/': depth -= 1; i += 2; continue
            out.append('\n' if text[i] == '\n' else ' '); i += 1; continue
        if quoted:
            if text[i] == '\\': out.extend('  '); i += 2; continue
            if text[i] == '"': quoted = False
            out.append('\n' if text[i] == '\n' else ' '); i += 1; continue
        if pair == '/-': depth = 1; i += 2; continue
        if pair == '--':
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
            continue
        if text[i] == '"': quoted = True; out.append(' '); i += 1; continue
        out.append(text[i]); i += 1
    assert depth == 0 and not quoted, 'unclosed comment/string'
    return ''.join(out)


def lexical_checks() -> list[dict]:
    files, graph = [], {}
    for path in sorted(HERE.glob('*.lean')):
        raw = path.read_bytes(); text = raw.decode('utf-8'); code = strip_lean(text)
        forbidden = re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by)\b|#(?:eval|reduce)', code)
        assert not forbidden, (path.name, forbidden)
        stack = []
        pairs = {')':'(', ']':'[', '}':'{', '⟩':'⟨'}
        for ch in code:
            if ch in pairs.values(): stack.append(ch)
            elif ch in pairs:
                assert stack and stack.pop() == pairs[ch], (path.name, 'delimiter')
        assert not stack, (path.name, 'unclosed delimiter')
        names = re.findall(r'^\s*(?:private\s+)?(?:theorem|lemma|def|abbrev)\s+([\w.\u0080-\uffff]+)', code, re.M)
        assert len(names) == len(set(names)), (path.name, 'duplicate local declaration')
        imports = re.findall(r'^import\s+(\S+)', code, re.M)
        graph['ImbalancedChen.' + path.stem] = imports
        files.append({'path':path.name,'lines':len(text.splitlines()),'declarations':names,
                      'imports':imports,'sha256':sha256(raw).hexdigest(),
                      'git_blob_sha1':sha1(f'blob {len(raw)}\0'.encode()+raw).hexdigest()})
    seen, active = set(), set()
    def visit(node):
        assert node not in active, 'new-module import cycle'
        if node in seen: return
        active.add(node)
        for dep in graph.get(node, []):
            if dep in graph: visit(dep)
        active.remove(node); seen.add(node)
    for node in graph: visit(node)
    return files


def clamp(x: F) -> F: return max(F(0), min(CAP, x))

def rounded(n: int, x: F) -> F:
    y = clamp(x); d = n+1
    return max(F(0), F((d*y).__floor__()-1, d))


def threshold_round(n: int, x: F) -> F:
    return max([F(0)]+[F(j,n+1) for j in range(n+1) if F(j+1,n+1) <= clamp(x)])


# A small immutable affine comparison language, separate from Lean source.
# Affines are (constant, coefficients); programs support exactly the five
# existing constructors: leaf, sup, inf, strict, and nonstrict branch.
def leaf(c, coeff=()): return ('leaf', F(c), tuple(F(x) for x in coeff))
def branch(a,b,yes,no,strict=False): return ('lt' if strict else 'le',a,b,yes,no)
def ev(p,t):
    op=p[0]
    if op=='leaf': return p[1]+sum((a*x for a,x in zip(p[2],t)),F(0))
    if op=='sup': return max(ev(p[1],t),ev(p[2],t))
    if op=='inf': return min(ev(p[1],t),ev(p[2],t))
    a,b=ev(p[1],t),ev(p[2],t)
    return ev(p[3] if (a<b if op=='lt' else a<=b) else p[4],t)


def leaves(p):
    if p[0]=='leaf': return {p}
    return set().union(*(leaves(child) for child in p[1:]))


def extremum(a,b,lo,hi):
    c=a[1]-b[1]; size=max(len(a[2]),len(b[2]))
    av=a[2]+(F(0),)*(size-len(a[2])); bv=b[2]+(F(0),)*(size-len(b[2]))
    coeff=[x-y for x,y in zip(av,bv)]
    low=c+sum((q*(lo[i] if q>=0 else hi[i]) for i,q in enumerate(coeff)),F(0))
    high=c+sum((q*(hi[i] if q>=0 else lo[i]) for i,q in enumerate(coeff)),F(0))
    return low,high


def certified(p,lo,hi):
    center=tuple((l+h)/2 for l,h in zip(lo,hi))
    for a,b in product(leaves(p),repeat=2):
        diff=ev(a,center)-ev(b,center); low,high=extremum(a,b,lo,hi)
        if not ((high<0 if diff<0 else 0<=low) and (high<=0 if diff<=0 else 0<low)):
            return False
    return True


def square_gates(t,selected):
    # Matches the finite Option(Bool x Fin k) dictionary, including repeated
    # half gates for selected complementary indices.
    result=[F(1,2)]
    for j in range(len(t)):
        result.append(sum(t[:j],F(0))+2*t[j])
        result.append(F(1,2) if j in selected else
            sum((t[i] for i in selected),F(0))+
            sum((t[i] for i in range(j) if i not in selected),F(0))+2*t[j])
    return result


def compiled_square_gates(t,selected):
    k=len(t); rows=[leaf(F(1,2),(0,)*k)]
    for j in range(k):
        rows.append(leaf(0,[int(i<j)+2*int(i==j) for i in range(k)]))
        rows.append(leaf(F(1,2),(0,)*k) if j in selected else
            leaf(0,[int(i in selected)+int(i<j and i not in selected)+2*int(i==j)
                    for i in range(k)]))
    return [ev(a,t) for a in rows]


def filter_value(n,seed,actions):
    accepted=[i for i,(raw,eligible,gates,upper) in enumerate(actions)
              if eligible and all(g<rounded(n,raw) for g in gates)
              and rounded(n,raw)+F(1,n+1)<=upper]
    value=max([seed]+[rounded(n,actions[i][0]) for i in accepted])
    tag=next((i for i in accepted if rounded(n,actions[i][0])==value),None) if seed<value else None
    return value,tag,accepted


def regressions():
    counts=Counter()
    for n in (0,1,9,39,99,199):
        points=[F(-1),F(0),CAP,F(1),F(2)]
        points += [F(j,80) for j in range(-2,83)]
        points += [F(j+1,n+1) for j in range(n+1)]
        for x in points:
            assert threshold_round(n,x)==rounded(n,x)
            counts['single_quantizer_threshold']=counts['single_quantizer_threshold']+1
    # Independent six-coordinate square formulas; not original source rows.
    for z in range(1,21):
        t=tuple(F(z+i+1,200) for i in range(6))
        for bits in range(64):
            I={i for i in range(6) if bits>>i&1}
            assert square_gates(t,I)==compiled_square_gates(t,I)
            counts['six_coordinate_gate_dictionary']+=1
    # Nonvacuous loss of old raw-max provenance after the filter.
    actions=[(F(59,100),True,[F(117,200)],F(3,5)),
             (F(57,100),True,[F(27,50)],F(57,100))]
    v,tag,acc=filter_value(99,F(13,25),actions)
    assert v==F(14,25) and tag==1 and acc==[1]
    assert actions[tag][0] < max(a[0] for a in actions)
    assert rounded(99,v)!=v, 'a second quantizer must be observably wrong'
    counts['old_raw_winner_rejected_and_no_double_rounding']+=1
    for n,seed,raw0,raw1,flag0,flag1 in product(
            (39,99,199),(F(1,2),F(13,25)),
            (F(27,50),F(57,100),F(59,100)),
            (F(27,50),F(57,100)),(False,True),(False,True)):
        for gate in (F(1,2),F(27,50),rounded(n,raw0)):
            actions=[(raw0,flag0,[gate],F(3,5)),(raw1,flag1,[F(1,2)],F(59,100))]
            value,tag,acc=filter_value(n,seed,actions)
            assert seed<=value<=max(seed,rounded(n,max(raw0,raw1)))
            assert (tag is None)==(value==seed)
            if tag is not None:
                raw,eligible,gates,upper=actions[tag]
                assert tag in acc and eligible and value==rounded(n,raw)
                assert all(g<value for g in gates) and value+F(1,n+1)<=upper
            if not acc: assert value==seed
            counts['filtered_winner_and_true_inheritance']+=1
    # Strict lower equality rejects; nonstrict upper equality accepts.
    r=F(14,25); raw=F(57,100); h=F(1,100)
    assert filter_value(99,F(1,2),[(raw,True,[r],r+h)])[1] is None
    assert filter_value(99,F(1,2),[(raw,True,[r-h],r+h)])[1]==0
    assert filter_value(99,F(1,2),[(raw,False,[r-h],r+h)])[1] is None
    counts['lower_upper_raw_guard_boundary']=3
    # Compact one-dimensional program with a licensed higher action below
    # x=2/25 and a licensed lower fallback action above it. Output labels
    # differ from values; certification checks EVERY affine difference.
    g=leaf(F(11,20),(F(1,4),)); top=leaf(F(57,100)); lower=leaf(F(11,20))
    scalar=branch(g,top,top,lower,strict=True)
    trace=branch(g,top,leaf(1),leaf(2),strict=True)
    for j in range(100):
        lo=(F(j,100),); hi=(F(j+1,100),)
        ok=certified(scalar,lo,hi) and certified(trace,lo,hi)
        center=((lo[0]+hi[0])/2,)
        samples=(lo,center,hi)
        if ok:
            for t in samples:
                assert ev(scalar,t)==ev(scalar,center) and ev(trace,t)==ev(trace,center)
            counts['joint_closed_box_certified']+=1
        else: counts['joint_closed_box_rejected']+=1
        # Exact fallback works even on equality and outside the unit cube.
        for t in samples:
            lookup=ev(scalar,center) if ok else ev(scalar,t)
            label=ev(trace,center) if ok else ev(trace,t)
            assert lookup==ev(scalar,t) and label==ev(trace,t)
            counts['exact_value_and_tag_fallback']+=1
    assert ev(trace,(F(2,25),))==2
    assert not (certified(scalar,(F(7,100),),(F(9,100),)) and
                certified(trace,(F(7,100),),(F(9,100),)))
    counts['crossing_wall_rejected']=1
    for later in product((F(1,100),F(2,3),F(3,4)),repeat=2):
        t8=(F(1,25),F(1,50),F(1,100),F(1,200),F(1,300),F(1,400))+later
        assert ev(scalar,t8[:6])==ev(scalar,t8[:6]+tuple(reversed(later)))
        assert ev(trace,t8[:6])==ev(trace,t8[:6]+tuple(reversed(later)))
        counts['own_sixth_projection']+=1
    return {'counts':dict(sorted(counts.items())),'total_cases':sum(counts.values()),
            'scope':'exact rational TOY models only; not original arrays, Lean evaluation, or universal proof',
            'counterexample':{'raw_max':'59/100','raw_max_rounded':'29/50','rejected_lower_gate':'117/200',
                              'accepted_raw':'57/100','filtered_value':'14/25','selected_index':1,
                              'wrong_second_round':'11/20'}}


def main():
    files=lexical_checks(); model=regressions()
    report={'scope':'lexical hygiene and finite exact-rational regression only',
            'lean_compiled':False,'kernel_replayed':False,'independent_review':False,
            'transitive_axioms_checked':False,'original_archives_evaluated':False,
            'new_module_graph_acyclic':True,'regression':model,'files':files}
    data=json.dumps(report,ensure_ascii=False,indent=2,sort_keys=True)+'\n'
    (HERE/'STATIC_QA.json').write_text(data,encoding='utf-8')
    print(json.dumps({'files':len(files),'lines':sum(f['lines'] for f in files),
                      'declarations':sum(len(f['declarations']) for f in files),
                      'regression':model},ensure_ascii=False,indent=2))

if __name__=='__main__': main()
