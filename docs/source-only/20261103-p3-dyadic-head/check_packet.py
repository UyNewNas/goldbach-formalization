"""Static inventory and independent toy regression, NOT a Lean proof check.

Run normally to print results. Optional --checks and --inventory write JSON
receipts; no Lean process, project producer, or network request is launched.
"""
from pathlib import Path
import argparse
import hashlib, json, re, collections

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent)
parser.add_argument("--checks", type=Path)
parser.add_argument("--inventory", type=Path)
args = parser.parse_args()
root = args.root
if not root.is_dir():
    parser.error(f"Not a directory: {root}")

def strip_comments(s):
    out=[]; i=0; depth=0; string=False
    while i<len(s):
        if depth:
            if s.startswith('/-',i): depth+=1; i+=2
            elif s.startswith('-/',i): depth-=1; i+=2
            else:
                if s[i]=='\n': out.append('\n')
                i+=1
        elif not string and s.startswith('/-',i): depth=1; i+=2
        elif not string and s.startswith('--',i):
            j=s.find('\n',i); i=len(s) if j<0 else j
        else:
            ch=s[i]; out.append(ch)
            if ch=='"' and (i==0 or s[i-1]!='\\'): string=not string
            i+=1
    if depth: raise ValueError('Unclosed block comment')
    return ''.join(out)

inventory=[]
for p in sorted(root.glob('P2*.lean')):
    b=p.read_bytes(); s=b.decode(); clean=strip_comments(s)
    forbidden=re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by)\b|#(?:eval|reduce)\b',clean)
    assert not forbidden,(p,forbidden)
    ds=[]
    for m in re.finditer(r'(?m)^(private\s+)?(def|theorem|abbrev|lemma)\s+([^\s({:]+)',clean):
        ds.append({'name':m.group(3),'kind':m.group(2),'private':bool(m.group(1)),
                   'line':clean[:m.start()].count('\n')+1})
    inventory.append({'file':p.name,'bytes':len(b),'lines':len(s.splitlines()),
      'git_blob_sha':hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest(),
      'sha256':hashlib.sha256(b).hexdigest(),'declarations':ds,
      'imports':re.findall(r'(?m)^import\s+(\S+)',s)})

checks=0; prefix_checks=0; disjoint_checks=0
for P in range(65):
    D=max(1,P.bit_length())
    def piece(d,n,L):
        if (n//(2**d))%2 != 1: return set()
        b=n//(2**(d+1))
        return {p for p in range(2*b*2**d+1,(2*b+1)*2**d+1) if L<p<=P}
    for n in range(P+1):
        cnt=collections.Counter(p for d in range(D) for p in piece(d,n,0))
        assert cnt==collections.Counter(range(1,n+1))
        prefix_checks+=1
    for a in range(P+1):
        for b in range(a,P+1):
            for L in set([0,a//2,a]):
                cnt=collections.Counter()
                for d in range(D):
                    cnt.update(piece(d,b,L))
                    cnt.subtract(piece(d,a,L))
                cnt={k:v for k,v in cnt.items() if v}
                assert cnt==dict.fromkeys(range(a+1,b+1),1),(P,L,a,b,cnt)
                checks+=1
    for d in range(D):
        cnt=collections.Counter()
        for b in range(P+1):
            cnt.update(p for p in range(2*b*2**d+1,(2*b+1)*2**d+1) if 0<p<=P)
        assert all(n<=1 for n in cnt.values())
        disjoint_checks+=1
result={'checks_are_not_formal_verification':True,
        'new_source_comment_stripped_admission_scan':'NO_MATCH',
        'python_combinatorial_regression':{'cap_range':[0,64], 'prefix_cases':prefix_checks,
        'clipped_interval_cases':checks, 'same_scale_disjointness_cases':disjoint_checks,
        'result':'PASS'},
        'lean_compiler_invoked':False,'kernel_replay':False,
        'repository_numeric_producer_invoked':False,'repository_finite_guards_evaluated':False,
        'proof_files':len(inventory),'proof_lines':sum(x['lines'] for x in inventory),
        'declaration_count':sum(len(x['declarations']) for x in inventory)}
if args.checks:
    args.checks.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n', encoding='utf-8')
if args.inventory:
    args.inventory.write_text(json.dumps(inventory,ensure_ascii=False,indent=2)+'\n', encoding='utf-8')
print(json.dumps(result,ensure_ascii=False,indent=2))
