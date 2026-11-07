"""Emit compact directed rational witnesses for the whole adopted mask.

Lean's ordinary kernel is required to check every emitted witness.  Python
is only the untrusted producer; it never supplies a claimed proof token.
"""
from pathlib import Path
from fractions import Fraction as Q
import hashlib, importlib.util, json

ROOT=Path(__file__).resolve().parents[3]
spec=importlib.util.spec_from_file_location('paired_decode',ROOT/'verification/part2/import_paired_v2.py')
decode=importlib.util.module_from_spec(spec);spec.loader.exec_module(decode)
raw=(ROOT/'verification/part2/data/corpus-renewal-paired-certificate-v2-20261010.json').read_bytes()
assert hashlib.sha256(raw).hexdigest()==decode.SOURCE_SHA256
source=json.loads(raw)
by_pair={(r[1],r[2]):r for r in source['rows']}
assert len(by_pair)==17572
strips=[];lower=upper=0
for i in range(326,512):
    js=sorted(j for ti,j in by_pair if ti==i)
    assert js==list(range(js[0],512))
    values=[]
    for j in js:
        tl,tr,ul,ur=decode.coordinates(i,j)
        Z=Q(by_pair[i,j][3])
        assert Z==min(ul,3*(1-tr-ur)/13)
        lt=decode.rational_log_bounds(tr/tl,1)
        lu=decode.rational_log_bounds(ur/ul,1)
        lz=decode.rational_log_bounds(Z/decode.A,6)
        lo=decode.floor(decode.K/80*lt[0]*lu[0]*(1/decode.A-(1+lz[1])/Z)*decode.CELL_SCALE)
        hi=decode.ceil(decode.K/80*lt[1]*lu[1]*(1/decode.A-(1+lz[0])/Z)*decode.CELL_SCALE)
        ns=[int(x*decode.LOG_SCALE) for pair in [lt,lu,lz] for x in pair]+[lo,hi]
        assert all(x>=0 for x in ns)
        values.append('⟨'+', '.join(map(str,ns))+'⟩')
        lower+=lo;upper+=hi
    strips.append(f'def approximations{i} : List Approximation :=\n  [\n    '+',\n    '.join(values)+'\n  ]\n')
header='''import ImbalancedChen.Certificates.PairedV2FullChecker

/-! Generated untrusted integer witnesses; acceptance is the separate
ordinary-kernel theorem in PairedV2FullCertificate.  All 17572 adopted grid
pairs appear in their canonical FullMask.Row location. Source SHA256:
f6d31386f93cf77888ea4771ffa549a1cf61dca700bac618ff7646566a02f9b7. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

'''
text=header+'\n'.join(strips)+'\n'
text+='def approximations : Fin 186 → List Approximation :=\n  !['
text+=', '.join('approximations'+str(i) for i in range(326,512))+''']

def approximation (r : Row) : Approximation :=
  (approximations r.1).getD r.2.val default

end ImbalancedChen.Certificates.PairedV2.FullMask
'''
dest=ROOT/'ImbalancedChen/Certificates/PairedV2FullCertificateData.lean'
dest.write_text(text,encoding='utf-8',newline='\n')
report={'source_sha256':decode.SOURCE_SHA256,'rows':len(by_pair),'strips':len(strips),
    'lower_numerator':str(lower),'upper_numerator':str(upper),'denominator':str(decode.CELL_SCALE),
    'lower':str(Q(lower,decode.CELL_SCALE)),'upper':str(Q(upper,decode.CELL_SCALE)),
    'generated_source_sha256':hashlib.sha256(text.encode()).hexdigest(),
    'lean_status':'NOT_YET_CHECKED','no_trust_in_producer':True}
(Path(__file__).parent/'full-certificate-import.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
