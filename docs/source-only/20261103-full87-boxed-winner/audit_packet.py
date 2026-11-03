#!/usr/bin/env python3
"""Lexical checks and exact rational toy tests only; NOT a Lean checker.

No original NPY/BIN fixture, original numerical producer, literal-row
membership certificate, Lean compiler, or network connection is used.
Run in place; a failed assertion prevents a passing report from being saved.
"""
from __future__ import annotations

from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import random
import re

ROOT = Path(__file__).resolve().parent
CAP = F(153, 256)


def strip_comments_strings(text: str) -> str:
    out: list[str] = []
    i = depth = 0
    string = False
    while i < len(text):
        pair, c = text[i:i + 2], text[i]
        if depth:
            if pair == '/-':
                depth += 1
                i += 2
            elif pair == '-/':
                depth -= 1
                i += 2
            else:
                out.append('\n' if c == '\n' else ' ')
                i += 1
        elif string:
            if c == '\\':
                i += 2
            elif c == '"':
                string = False
                i += 1
            else:
                out.append('\n' if c == '\n' else ' ')
                i += 1
        elif pair == '/-':
            depth = 1
            i += 2
        elif pair == '--':
            j = text.find('\n', i)
            i = len(text) if j < 0 else j
        elif c == '"':
            string = True
            i += 1
        else:
            out.append(c)
            i += 1
    if depth or string:
        raise ValueError('Unterminated comment or string')
    return ''.join(out)


def blob_sha(raw: bytes) -> str:
    return hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()


def rounded(n: int, x: F) -> F:
    d = n + 1
    y = max(F(0), min(CAP, x))
    return max(F(0), F((d * y).__floor__() - 1, d))


def gates(t: tuple[F, ...], mask: int) -> list[F]:
    I = {i for i in range(len(t)) if mask >> i & 1}
    ans = [F(1, 2)]
    for j, tj in enumerate(t):
        ans.append(sum(t[:j], F(0)) + 2 * tj)
        ans.append(F(1, 2) if j in I else
                   sum((t[i] for i in I), F(0)) +
                   sum((t[i] for i in range(j) if i not in I), F(0)) + 2 * tj)
    return ans


def tent(s: F) -> F:
    return min((1 + s) / 2, F(57, 64) - 3 * s / 2)


def tests() -> dict:
    """Exact toy comparisons, NOT execution of any Lean proof or archive."""
    rng = random.Random(2026110337)
    counts = dict(label_compilation=0, full_box_label=0,
                  exact_fallback=0, scalar_collision=0, saved_plane_bounds=0,
                  saved_guard_converse=0, chronological_guard=0)
    # Independent finite affine-program/label-trace evaluator.
    # An affine value is (constant, coefficients); the toy dimension is two.
    def aff(c, x=0, y=0): return (F(c), (F(x), F(y)))
    def ae(a, t): return a[0] + sum((u*v for u,v in zip(a[1],t)), F(0))
    def leaf(a): return ('leaf',a)
    def pe(p,t):
        if p[0]=='leaf': return ae(p[1],t)
        a,b=pe(p[1],t),pe(p[2],t)
        if p[0]=='sup': return max(a,b)
        if p[0]=='inf': return min(a,b)
        return pe(p[3] if (a<b if p[0]=='lt' else a<=b) else p[4],t)
    def leaves(p):
        if p[0]=='leaf': return {p[1]}
        out=set()
        for q in p[1:]: out |= leaves(q)
        return out
    def signature(p,t):
        return {(a,b):(ae(a,t)<ae(b,t),ae(a,t)<=ae(b,t)) for a in leaves(p) for b in leaves(p)}
    def select(p,sg):
        if p[0]=='leaf': return p[1]
        a,b=select(p[1],sg),select(p[2],sg)
        if p[0]=='sup': return b if sg[a,b][1] else a
        if p[0]=='inf': return a if sg[a,b][1] else b
        return select(p[3] if sg[a,b][0 if p[0]=='lt' else 1] else p[4],sg)
    def trace_eval(tr,t):
        if tr[0]=='tag': return tr[1]
        strict,l,r,yes,no=tr[1:]
        a,b=pe(l,t),pe(r,t)
        return trace_eval(yes if (a<b if strict else a<=b) else no,t)
    def compile_trace(tr):
        if tr[0]=='tag': return leaf(aff(tr[1]))
        strict,l,r,yes,no=tr[1:]
        return ('lt' if strict else 'le',l,r,compile_trace(yes),compile_trace(no))
    def cert(p,sg,lo,hi):
        for a in leaves(p):
            for b in leaves(p):
                c=a[0]-b[0]; cs=[x-y for x,y in zip(a[1],b[1])]
                low=c+sum((u*(l if u>=0 else h) for u,l,h in zip(cs,lo,hi)),F(0))
                high=c+sum((u*(h if u>=0 else l) for u,l,h in zip(cs,lo,hi)),F(0))
                lt,le=sg[a,b]
                if not ((high<0 if lt else 0<=low) and (high<=0 if le else 0<low)):
                    return False
        return True
    points=[(F(x,4),F(y,4)) for x in range(-4,5) for y in range(-4,5)]
    for case in range(32):
        p1=leaf(aff(F(rng.randrange(-3,4),5),F(rng.randrange(-3,4),4),F(1,3)))
        p2=leaf(aff(F(rng.randrange(-3,4),5),F(1,2),F(rng.randrange(-3,4),4)))
        tr=('branch',bool(case%2),p1,p2,
            ('branch',False,p1,p1,('tag',7),('tag',99)),
            ('branch',True,p1,p1,('tag',99),('tag',3)))
        p=compile_trace(tr)
        for t in points:
            sg=signature(p,t); tag=trace_eval(tr,t)
            chosen=select(p,sg)
            assert pe(p,t)==tag and chosen==aff(tag)
            counts['label_compilation']+=1
        for k in range(8):
            lo=(F(k,8),F(0)); hi=(F(k+1,8),F(1,8))
            center=tuple((l+h)/2 for l,h in zip(lo,hi)); sg=signature(p,center)
            good=cert(p,sg,lo,hi)
            for t in ((lo[0],lo[1]),(hi[0],lo[1]),(lo[0],hi[1]),hi,center):
                if good:
                    assert trace_eval(tr,t)==trace_eval(tr,center)
                    counts['full_box_label']+=1
                else:
                    assert ae(select(p,signature(p,t)),t)==trace_eval(tr,t)
                    counts['exact_fallback']+=1
    # Same scalar finite cap, DIFFERENT action labels. Original inherited
    # branch yields no action; tie ordering picks the first real witness.
    vals=[]
    for x in (F(-1),F(0),F(1)):
        endpoints=[F(113,200)+x/1000,F(113,200)-x/1000]
        raw=max(endpoints); cap=max(F(1,2),rounded(99,raw))
        winner=next(i for i,v in enumerate(endpoints) if v==raw)
        vals.append((cap,winner))
        counts['scalar_collision']+=1
    assert len({v for v,_ in vals})==1 and vals[0][1]!=vals[-1][1]
    assert vals[1][1]==0
    # All 31 old-plane choices dominate the corresponding exact tent.
    # Bounds include arbitrary original midpoint plane choices and empty
    # subproducts. No row acceptance or original Source is fabricated here.
    for case in range(250):
        t=tuple(sorted((F(rng.randrange(1,190),1000) for _ in range(6)),reverse=True))
        midpoint=tuple(F(rng.randrange(0,250),1000) for _ in range(6))
        def subset(m,tt): return sum((tt[j] for j in range(5) if m>>j&1),F(0))
        def plane(m):
            mid=subset(m,midpoint); u=subset(m,t)
            aa=(1+mid)/2; cc=F(57,64)-F(3,2)*mid
            return (1+u)/2 if aa<=cc and aa<=CAP else F(57,64)-F(3,2)*u if cc<=CAP else CAP
        W=CAP-F(3,8)*t[2]; upper=max([W]+[plane(m) for m in range(1,32)])
        for m in range(32):
            assert tent(subset(m,t))<=upper
            counts['saved_plane_bounds']+=1
        six=max(tent(t[0]),tent(t[0]+t[1]),tent(sum(t[:3],F(0))),
                W,tent(t[0]+t[2]),tent(t[1]+t[2]))
        assert six<=upper
        e=F(rng.randrange(0,100),1000000); seed=six-2*e
        fourth=max([seed]+[tent(subset(m,t))-2*e for m in range(1,16)])
        fifth=max([fourth]+[tent(subset(m,t))-2*e for m in range(1,32)])
        assert fifth<=upper
        H3=t[0]+t[1]+3*t[2]; H5=sum(t[:4],F(0))+3*t[4]
        if H3<seed and H5<seed:
            for source in (False,True):
                actual=source and H3<seed and H5<seed and fifth<=upper
                assert actual==source
                counts['saved_guard_converse']+=1
    # Chronological guards depend on raw priors. A first raw attaining
    # action is selected only on a strict finite update.
    for _ in range(500):
        base=F(1,2); fifth=F(rng.randrange(510,550),1000); current=fifth
        actions=[]
        for stage in range(8):
            prior=current; candidates=[]
            for row in range(4):
                M=F(rng.randrange(530,598),1000); cmp=F(rng.randrange(520,590),1000)
                gate=prior<=cmp<M
                if gate:
                    actions.append((stage,row,prior,M)); candidates.append(M)
            current=max([prior]+candidates)
        for n in (9,99,999):
            c5=max(base,rounded(n,fifth)); c6=max(base,rounded(n,current))
            tag=next((a for a in actions if a[-1]==current),None) if c5<c6 else None
            assert (tag is not None)==(c5<c6)
            if tag is not None: assert c6==rounded(n,tag[-1]) and tag in actions
            counts['chronological_guard']+=1
    return dict(counts=counts,total_cases=sum(counts.values()),
        scope='Exact rational TOY cases only; not original archives, Lean elaboration or universal verification',
        same_scalar_different_tags=[(str(v),tag) for v,tag in vals])


def main() -> None:
    files = []
    graph = {}
    names = {p.stem for p in ROOT.glob('*.lean')}
    for p in sorted(ROOT.glob('*.lean')):
        raw = p.read_bytes()
        text = raw.decode()
        code = strip_comments_strings(text)
        bad = re.findall(r'(?<![\w])(?:sorry|admit|axiom|unsafe|native_decide)(?![\w])|#(?:eval|reduce)', code)
        assert not bad, (p.name, bad)
        stack = []
        pairs = {')': '(', ']': '[', '}': '{', '⟩': '⟨'}
        for char in code:
            if char in '([{⟨':
                stack.append(char)
            elif char in pairs:
                assert stack and stack.pop() == pairs[char], (p.name, char)
        assert not stack, (p.name, stack)
        imports = re.findall(r'^import\s+(\S+)', code, re.M)
        decl = re.findall(r'^(?:(?:private|protected|noncomputable)\s+)*(?:@\[[^\]]+\]\s*)?'
                          r'(def|theorem|lemma|abbrev|structure|inductive)\s+(\S+)', code, re.M)
        files.append(dict(path=p.name, bytes=len(raw), lines=len(text.splitlines()),
                          sha256=hashlib.sha256(raw).hexdigest(), git_blob_sha1=blob_sha(raw),
                          imports=imports, declarations_count=len(decl)))
        graph[p.stem] = [i.rsplit('.', 1)[-1] for i in imports if i.rsplit('.', 1)[-1] in names]
    seen, active = set(), set()
    def visit(name: str) -> None:
        assert name not in active, ('cycle', name)
        if name in seen:
            return
        active.add(name)
        for dep in graph[name]:
            visit(dep)
        active.remove(name)
        seen.add(name)
    for name in graph:
        visit(name)
    report = dict(scope='Lexical hygiene, graph check and exact rational toy tests only',
                  lean_compiled=False, kernel_replayed=False, independent_review=False,
                  transitive_axioms_checked=False, original_archive_loaded=False,
                  numerical_producer_rerun=False, original_later_row_certificates_evaluated=False,
                  new_slots5_finite_proof_evaluated=False,
                  new_module_graph_acyclic=True, regression=tests(), files=files)
    report['generator'] = 'audit_packet.py; reports include file inventories and may be re-expanded'
    (ROOT / 'STATIC_QA.json').write_text(json.dumps(report, ensure_ascii=False, separators=(',', ':')) + '\n')
    print(json.dumps(dict(lean_files=len(files), lean_lines=sum(f['lines'] for f in files),
                          declarations=sum(f['declarations_count'] for f in files),
                          regression=report['regression']), ensure_ascii=False, indent=2))


if __name__ == '__main__':
    main()
