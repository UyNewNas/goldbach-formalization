from pathlib import Path
import hashlib, json, re
from fractions import Fraction as F
import math
import sympy as sp

ROOT = Path(__file__).resolve().parent
SPECS = {
 'P3HBLogScalarProfiles.lean':['inverseLogProfile_contDiff','exists_scalar_derivative_bound'],
 'P3SmoothScalarJets.lean':['mixed_evalS','exists_family_mixed_boundS'],
 'P3HBLogSourceDictionary.lean':['eventually_log_domains','normalized_product_eq_original','unit_log_slot_zero'],
 'P3U5HBLogChart.lean':['eval_hbExpr','hbProfile_eq_physical','same_rho_hb_partition'],
 'P3U5HBLogMixedL1.lean':['exists_hbProfile_mixed_bound','exists_hbD_polylog'],
}

def check_sources():
    count=0
    for name,decls in SPECS.items():
        p=ROOT/name
        assert p.exists(), f'Missing implementation: {name}'
        text=p.read_text()
        # strip nested Lean block comments, then line comments
        out=[]; i=0; depth=0
        while i<len(text):
            if text[i:i+2]=='/-': depth+=1; i+=2
            elif depth and text[i:i+2]=='-/': depth-=1; i+=2
            elif depth: i+=1
            else: out.append(text[i]); i+=1
        assert depth==0, name
        clean=re.sub(r'--[^\n]*','', ''.join(out))
        assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b|#eval|#reduce',clean),name
        for decl in decls:
            assert re.search(r'\btheorem\s+'+re.escape(decl)+r'\b',clean), (name,decl)
        stack=[]
        pairs={')':'(',']':'[','}':'{'}
        for ch in clean:
            if ch in '([{': stack.append(ch)
            elif ch in ')]}':
                assert stack and stack.pop()==pairs[ch], (name,'unbalanced delimiters')
        assert not stack, (name,'unclosed delimiters')
        count+=1
    return count

def check_formulas():
    rng_count=0
    for d in range(1,5):
        for g in range(1,d+1):
            group=[i%g for i in range(d)]
            pick=[group.index(j) for j in range(g)]
            for seed in range(1,41):
                # integer inputs include units; no denominator is asserted positive for empty/unit groups
                n=[1+(seed*(i+1)%13) for i in range(d)]
                if seed%7==0: n[pick[0]]=1
                prod=[math.prod(n[i] for i in range(d) if group[i]==j) for j in range(g)]
                if min(prod)<=1: continue
                for j in range(g):
                    assert 1<=n[pick[j]]<=prod[j]
                    ratio=math.log(n[pick[j]])/math.log(prod[j])
                    assert 0<=ratio<=1+1e-14
                ell=F(seed+2)
                # exact normalized affine logs, independent of transcendental evaluation
                logs=[F(i+seed,7) for i in range(d)]
                a=F(1)
                b=F(1)
                for j in range(g):
                    lg=sum(logs[i] for i in range(d) if group[i]==j)
                    a*= (logs[pick[j]]/ell)/(lg/ell)
                    b*=logs[pick[j]]/lg
                assert a==b
                rng_count+=1
    x,y,b,c,ell=sp.symbols('x y b c ell',positive=True)
    poly=1+x+x*y+y**3
    ratio=(b+x)/(c+x+y)
    combined=poly*ratio**2
    derivatives=0
    for q in range(6):
        for r in range(6-q):
            assert sp.simplify(sp.diff(combined,x,q,y,r)-sum(
                sp.binomial(q,i)*sp.binomial(r,j)*sp.diff(poly,x,i,y,j)*
                sp.diff(ratio**2,x,q-i,y,r-j) for i in range(q+1) for j in range(r+1)))==0
            derivatives+=1
    # Threshold algebra uses log(c), log(C) as arbitrary real offsets.
    domains=0
    for alpha in [F(1,100),F(1,20),F(1,4),F(1,2)]:
        for lc in [F(-5),F(-1),F(0),F(2)]:
            for lC in [F(-2),F(0),F(1),F(5)]:
                for extra in range(16):
                    ell=max(F(1),2*abs(lc)/alpha,lC)+extra
                    assert lc+alpha*ell>=alpha*ell/2
                    assert lC+ell<=2*ell
                    domains+=1
    def step(t):
        if t<=0: return 0.0
        if t>=1: return 1.0
        left=math.exp(-1/t); right=math.exp(-1/(1-t))
        return left/(left+right)
    def inverse_profile(a,y):
        return 0.0 if y==0 else step(2*y/a-1)*(1-step(y-2))/y
    guards=0
    for a in [0.005,0.025,0.125,0.25,0.5]:
        for j in range(41):
            y=a+(2-a)*j/40
            assert abs(inverse_profile(a,y)-1/y)<=1e-10
            guards+=1
        for y in [-2,-1,0,a/4,a/2,3,4]:
            assert abs(inverse_profile(a,y))<1e-12
            guards+=1
    # Counterexample: slot-by-slot inverse logs would be undefined at a unit even
    # though the correct full-group inverse is defined and the HB term is zero.
    assert math.log(1)/math.log(6)==0
    return {'group_ratio_cases':rng_count,'symbolic_mixed_product_cases':derivatives,
            'exact_log_domain_budget_cases':domains,'numerical_guard_cases':guards,
            'unit_wrong_denominator_negative_control':True}

if __name__=='__main__':
    result={'source_contracts':check_sources(),**check_formulas(),
            'lean_compiled':False,'kernel_replayed':False}
    print(json.dumps(result,indent=2))
