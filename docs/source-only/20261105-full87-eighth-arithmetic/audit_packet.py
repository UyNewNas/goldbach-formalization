#!/usr/bin/env python3
"""Finite exact-model regressions and lexical hygiene, NOT Lean verification.

Uses small synthetic policies/carriers. No original NPY/BIN, numerical producer,
source-row certificate, prime-mean asymptotic or kernel proof is evaluated.
Run from this packet, or pass its directory as the sole positional argument.
"""
from __future__ import annotations
from fractions import Fraction as F
from itertools import product
from collections import Counter
from pathlib import Path
from math import gcd, prod
from functools import lru_cache
import hashlib, json, re, sys


def signed(R, h, T, pre, positive, mass, xs):
    if not xs:
        return (mass if positive else -mass) * T(positive, pre)
    p, *tail = xs
    tail = tuple(tail)
    out = signed(R, h, T, pre, positive, mass, tail)
    if R(not positive, (p,) + pre):
        out += signed(R, h, T, (p,) + pre, not positive, mass * h(p), tail)
    return out


def leaves(R, h, pre, positive, mass, xs):
    if not xs:
        return [(pre, positive, mass)]
    p, *tail = xs
    tail = tuple(tail)
    out = leaves(R, h, pre, positive, mass, tail)
    if R(not positive, (p,) + pre):
        out += leaves(R, h, (p,) + pre, not positive, mass * h(p), tail)
    return out


def frontier(k, R, h, pre, positive, mass, xs):
    if len(pre) >= k:
        return [(pre, positive, mass, tuple(xs))]
    if not xs:
        return []
    p, *tail = xs
    tail = tuple(tail)
    out = frontier(k, R, h, pre, positive, mass, tail)
    if R(not positive, (p,) + pre):
        out += frontier(k, R, h, (p,) + pre, not positive, mass*h(p), tail)
    return out


def primes(N):
    return tuple(p for p in range(2, N+1)
                 if all(p % d for d in range(2, int(p**0.5)+1)))


@lru_cache(maxsize=None)
def phi(d):
    # Trial-factor phi, rather than enumerating residues up to a product modulus.
    if d == 0:
        return 0
    out, remaining, p = d, d, 2
    while p*p <= remaining:
        if remaining % p == 0:
            out -= out // p
            while remaining % p == 0:
                remaining //= p
        p += 1
    if remaining > 1:
        out -= out // remaining
    return out


def div(a,b):
    return F(a,b) if b else F(0)


def counts(N,d):
    ps=primes(N)
    ap=sum(p==N if d==0 else (p-N)%d==0 for p in ps)
    centre=sum((p==N if d==0 else (p-N)%d==0) and N%p==0 for p in ps)
    mean=div(sum(gcd(p,d)==1 for p in ps),phi(d))
    drop=div(sum(d%p==0 for p in ps),phi(d))
    receiver=sum((N-p==0 if d==0 else (N-p)%d==0) for p in ps if N%p!=0)
    return F(ap),F(centre),mean,drop,F(receiver)


def model_tests():
    n=Counter()
    def check(kind, cond):
        if not cond:
            raise AssertionError(kind)
        n[kind]+=1
    for d in range(501):
        check('totient_factorization_vs_enumeration',
              phi(d)==(sum(gcd(a,d)==1 for a in range(1,d+1)) if d else 0))
    carriers=[(),(2,),(5,3,2),(11,7,5,3,2)]
    for mode in range(4):
        R=lambda b,p: b or (sum(p)+mode)%3!=1
        C=lambda b,p: b or (len(p)+mode)%3!=1
        for xs in carriers:
            for scalar in (F(1),F(2,3),F(-1,2)):
                h=lambda p:scalar/F(p)
                T=lambda b,p:F((2 if b else 7)*(1+sum(p)),3)
                U=lambda b,p:F((3 if b else -2)*(1+prod(p)),5)
                val=signed(R,h,T,(),True,F(1),xs)
                leafsum=sum(((v if b else -v)*T(b,p)
                             for p,b,v in leaves(R,h,(),True,F(1),xs)),F(0))
                check('signed_tree_vs_leaves',val==leafsum)
                check('terminal_linearity',signed(R,h,lambda b,p:2*T(b,p)-3*U(b,p),(),True,F(1),xs)
                      ==2*val-3*signed(R,h,U,(),True,F(1),xs))
                for k in (0,1,2,4):
                    P=lambda b,p: R(b,p) if len(p)<=k else C(b,p)
                    total=signed(P,h,T,(),True,F(1),xs)-val
                    stopped=sum((signed(C,h,T,p,b,v,t)-signed(R,h,T,p,b,v,t)
                                 for p,b,v,t in frontier(k,R,h,(),True,F(1),xs)),F(0))
                    check('splice_frontier_identity',total==stopped)
    # Duplicate occurrences are intentionally retained; a set conversion is wrong.
    for tags in product((None,0,1), repeat=4):
        xs=[(tag,F(i%2+1)) for i,tag in enumerate(tags)]
        xs=[(c,v if c is not None else F(0)) for c,v in xs]
        direct=sum((v for _,v in xs),F(0))
        split=sum((sum((v for c,v in xs if c==j),F(0)) for j in (0,1)),F(0))
        check('owner_partition_with_repeats',direct==split)
    duplicate=[(0,F(2)),(0,F(2)),(1,F(-1))]
    check('deduplication_is_rejected',sum(v for _,v in duplicate)!=sum(v for _,v in set(duplicate)))
    # A genuinely rank-eight stopped source. Ordinary-like prefix tests are
    # synthetic: no assertion that these are the original 87 source coordinates.
    xs=(29,23,19,17,13,11,7,5,3,2)
    for k in (2,4,8):
        for pattern in range(4):
            anc=lambda p:p[-k:] if len(p)>=k else ()
            owner=lambda p:None if not anc(p) or (sum(anc(p))+pattern)%3==0 else (sum(anc(p))%2)
            old=lambda b,p: b or prod(p)*(p[0] if p else 1)**2<10**16
            fresh=lambda b,p:old(b,p) if owner(p) is None else (b or prod(p)*(p[0] if p else 1)**2<10**(11+owner(p)))
            P=lambda b,p:old(b,p) if len(p)<=k else fresh(b,p)
            # Distinct beta branches and a nonmultiplicative full-modulus test.
            G=lambda d:F((d%7)+1,phi(d) or 1)
            T=lambda b,p:sum((v*G(a*prod(p)) for a,v in
                              ((1,F(1)),(2,F(-1,3) if b else F(-2,3)),(3,F(1,7) if b else F(-1,5)))),F(0))
            saving=signed(old,lambda _:F(1),T,(),True,F(1),xs)-signed(P,lambda _:F(1),T,(),True,F(1),xs)
            Fxs=frontier(k,old,lambda _:F(1),(),True,F(1),xs)
            owned=F(0)
            for c in (0,1):
                for p,b,v,t in Fxs:
                    if owner(p)==c:
                        owned+=signed(old,lambda _:F(1),T,p,b,v,t)-signed(fresh,lambda _:F(1),T,p,b,v,t)
            check('ranked_owned_full_beta_saving',owned==saving)
            for p,b,v,t in Fxs:
                if owner(p) is None:
                    check('no_owner_descendant_cancellation',signed(old,lambda _:F(1),T,p,b,v,t)==signed(fresh,lambda _:F(1),T,p,b,v,t))
    for N in range(0,41):
        for d in range(0,46):
            ap,centre,mean,drop,rec=counts(N,d)
            check('exact_coprime_density_correction',mean==len(primes(N))*div(1,phi(d))-drop)
            check('actual_receiver_centre_correction',rec==ap-centre)
    check('uncorrected_mean_is_rejected',counts(10,6)[2]!=len(primes(10))*div(1,phi(6)))
    check('centre_prime_is_retained_as_error',counts(7,1)[1]==1 and counts(7,1)[0]-counts(7,1)[4]==1)
    for N in (2,6,7,10,14,30):
        for seed in range(12):
            old={d:F(((d+seed)%7)-3,d+1) for d in (1,2,3,6,10)}
            new={d:F(((2*d+seed)%9)-4,d+2) for d in (1,3,5,7,15)}
            gain=lambda G:sum((v*G(d) for d,v in old.items()),F(0))-sum((v*G(d) for d,v in new.items()),F(0))
            budget=lambda G:sum((abs(v)*abs(G(d)) for d,v in list(old.items())+list(new.items())),F(0))
            dens=lambda d:div(1,phi(d)); err=lambda d:counts(N,d)[0]-counts(N,d)[2]
            drop=lambda d:counts(N,d)[3]; centre=lambda d:counts(N,d)[1]
            receiver=lambda d:counts(N,d)[4]
            lhs=gain(receiver); rhs=len(primes(N))*gain(dens)+gain(err)-gain(drop)-gain(centre)
            check('signed_same_realization_mean_ledger',lhs==rhs)
            check('finite_absolute_payment_bound',abs(lhs-len(primes(N))*gain(dens))<=budget(err)+budget(drop)+budget(centre))
    return {'cases':dict(sorted(n.items())),'total_cases':sum(n.values()),
            'scope':'exact synthetic finite model only; NOT original-source or Lean verification'}


def stripped(text):
    """Remove nested block comments, line comments and strings."""
    out=[]; i=0; depth=0; in_string=False
    while i<len(text):
        if depth:
            if text.startswith('/-',i):depth+=1;i+=2
            elif text.startswith('-/',i):depth-=1;i+=2
            else:out.append('\n' if text[i]=='\n' else ' ');i+=1
        elif in_string:
            if text[i]=='\\':i+=2
            elif text[i]=='"':in_string=False;i+=1
            else:i+=1
        elif text.startswith('/-',i):depth=1;i+=2
        elif text.startswith('--',i):
            end=text.find('\n',i);i=len(text) if end<0 else end
        elif text[i]=='"':in_string=True;i+=1
        else:out.append(text[i]);i+=1
    if depth or in_string:raise AssertionError('unterminated comment/string')
    return ''.join(out)


def lexical(root):
    rows=[]; graph={}
    pairs={')':'(',']':'[','}':'{','⟩':'⟨'}
    for path in sorted(root.glob('*.lean')):
        raw=path.read_bytes(); code=stripped(raw.decode('utf-8'))
        assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',code),path
        stack=[]
        for ch in code:
            if ch in pairs.values():stack.append(ch)
            elif ch in pairs:
                assert stack and stack.pop()==pairs[ch],(path.name,ch)
        assert not stack,path.name
        decls=re.findall(r'^(?:private\s+)?(?:@\[[^\]]+\]\s*)?(?:theorem|def|lemma|abbrev|structure|inductive)\s+(\w+(?:\.\w+)*)',code,re.M)
        assert len(decls)==len(set(decls)),path.name
        imports=re.findall(r'^import\s+([\w.]+)',code,re.M)
        graph['ImbalancedChen.'+path.stem]=imports
        rows.append({'path':path.name,'lines':len(raw.splitlines()),'declarations':decls,'imports':imports,
                     'sha256':hashlib.sha256(raw).hexdigest(),
                     'git_blob_sha1':hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()})
    seen=set(); active=set()
    def visit(node):
        if node in seen:return
        assert node not in active,'new module cycle'
        active.add(node)
        for nxt in graph[node]:
            if nxt in graph:visit(nxt)
        active.remove(node);seen.add(node)
    for node in graph:visit(node)
    return rows


def main():
    root=Path(sys.argv[1]).resolve() if len(sys.argv)>1 else Path(__file__).resolve().parent
    report={'scope':'lexical checks and independent exact finite model',
            'lean_compiled':False,'kernel_replayed':False,'transitive_axioms_checked':False,
            'independent_review':False,'original_archive_evaluated':False,
            'asymptotic_mean_proved':False,'regression':model_tests(),'files':lexical(root)}
    report['new_module_graph_acyclic']=True
    (root/'STATIC_QA.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({'total_cases':report['regression']['total_cases'],
                     'lean_lines':sum(f['lines'] for f in report['files']),
                     'named_declarations':sum(len(f['declarations']) for f in report['files']),
                     'lean_compiled':False},indent=2))

if __name__=='__main__':main()
