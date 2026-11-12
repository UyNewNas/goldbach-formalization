"""Static source/hash inventory only. Never invokes Lean, Lake or proof evaluation."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

BASE = Path('E:/timot/Documents/FilesForGPT/Myath')
REPO = BASE / 'goldbach-proof-continuation'
MIRROR = BASE / 'goldbach-proof-github-sync-20261110.git'
OUT = BASE / 'output/resume-20261112/t01/p3-grouped'
P3 = 'a29bd6b4cba6d1b7e8cd48165f3a0f76f040082b'
PAPER = '9731290e8f53cffda44129906cde6a965eaa869b'

def digest(data):
    return hashlib.sha256(data).hexdigest()

def blob(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()

def git(*args):
    return subprocess.check_output(['git', '--git-dir=' + str(MIRROR), *args])

tree = {}
for line in git('ls-tree', '-r', P3).decode().splitlines():
    attrs, path = line.split('\t', 1)
    if attrs.split()[1] == 'blob':
        tree[path] = attrs.split()[2]

selected = [
 ('P5ActualEtaPsiOccurrenceBudget', 'docs/source-only/20261028-resume-30c/pp_derivatives/P5ActualEtaPsiOccurrenceBudget.lean', 'Actual grouped cutoffs; exact arbitrary-word identity; fixed-rank chart budget'),
 ('P5GroupedOccurrenceLogShift', '.lake/proof-continuation/source-reviews/drafts/20261028-PrimeProducts-PhaseB4-HBFamily-GroupLog/P5GroupedOccurrenceLogShift.lean', 'Unique original owner, original group products and exact log shift'),
 ('P5OccurrenceWordFourFactorLeibniz', 'docs/source-only/20261028-resume-30/pp_derivatives/P5OccurrenceWordFourFactorLeibniz.lean', 'Existing complete ordered four-factor allocation, including repeats'),
 ('P5OccurrenceLeibnizAllocation', '.lake/proof-continuation/source-reviews/drafts/20261028-PrimeProducts-PhaseB7-HBFamily-Allocation/P5OccurrenceLeibnizAllocation.lean', 'Original finite allocation and one-letter calculus predecessor'),
 ('P5AllWordAmbientOccurrenceBound', '.lake/proof-continuation/source-reviews/drafts/20261028-PrimeProducts-PhaseB6-HBFamily-WordChain/P5AllWordAmbientOccurrenceBound.lean', 'Actual occurrence words and conditional real ambient Family budget'),
 ('P5GroupedAmbientOccurrenceChain', '.lake/proof-continuation/source-reviews/drafts/20261028-PrimeProducts-PhaseB5-HBFamily-AmbientChain/P5GroupedAmbientOccurrenceChain.lean', 'True grouped ambient chain predecessor'),
 ('P5MixedEulerTwoStepLeibniz', '.lake/proof-continuation/source-reviews/drafts/20261028-PrimeProducts-PhaseB3-HBFamily-Calculus/P5MixedEulerTwoStepLeibniz.lean', 'Original Euler calculus predecessor'),
 ('P5AdmissibleAllRankIntegerGeometricFamily', '.lake/proof-continuation/source-reviews/drafts/20261028-PrimeProducts-PhaseB-HBFamily-AllRanks/P5AdmissibleAllRankIntegerGeometricFamily.lean', 'Original real Family definition; its primitive mixedEuler field is not discharged by this inventory'),
 ('P5ActualOccurrencePlateauWordBudget', 'docs/source-only/20261028-resume-30b/pp_derivatives/P5ActualOccurrencePlateauWordBudget.lean', 'Actual compact plateau supplier'),
 ('P5OccurrenceEuclideanMixedIntegral', 'docs/source-only/20261028-resume-30c/pp_fourier/P5OccurrenceEuclideanMixedIntegral.lean', 'Exact all-word complexification, Euclidean coordinate and L1 transport'),
 ('P5ActualAllRankOccurrenceFourierBridge', 'docs/source-only/20261028-resume-30c/pp_fourier/P5ActualAllRankOccurrenceFourierBridge.lean', 'Existing actual-chart mixedD and Fourier consumer, retaining Family premise'),
 ('P5ActualEuclideanPhysicalFourier', 'docs/source-only/20261028-resume-30b/pp_fourier/P5ActualEuclideanPhysicalFourier.lean', 'Existing normalization and genuine physical Fourier transport'),
 ('P3ActualHBChildMixedFourier', 'docs/source-only/20261110-yellow-closure-10t/t06_actual_mixed_fourier/P3ActualHBChildMixedFourier.lean', 'Existing actual child conversion, translated bases and coupled arbitrary-word refined chart'),
 ('P3ActualUpperPairChildFourier', 'docs/source-only/20261110-yellow-closure-10t/t06_actual_mixed_fourier/P3ActualUpperPairChildFourier.lean', 'Existing concrete legal-width real rank-two refined chart consumer'),
 ('P4BArbitraryWidthUpperPairOccurrence', 'docs/source-only/20261102-resume-30j/upper_pp/P4BArbitraryWidthUpperPairOccurrence.lean', 'Existing actual rank-two ambient occurrence supplier, no abstract Family input'),
]

rows = []
for name, rel, role in selected:
    path = REPO / rel
    data = path.read_bytes()
    text = data.decode('utf-8-sig')
    oid = blob(data)
    matches = sorted(p for p, sha in tree.items() if sha == oid)
    rows.append({
      'module': 'ImbalancedChen.' + name,
      'source_path': str(path).replace('\\', '/'),
      'sha256': digest(data), 'git_blob_sha1': oid, 'bytes': len(data),
      'suggested_install_path': 'ImbalancedChen/' + name + '.lean',
      'role': role,
      'latest_P3_same_path_blob': tree.get(rel),
      'latest_P3_exact_blob_paths': matches,
      'latest_P3_contains_exact_bytes': bool(matches),
      'direct_imports': re.findall(r'^import\s+([^\r\n]+)', text, re.M),
      'declarations': [ {'line': i, 'text': s.strip()}
        for i,s in enumerate(text.splitlines(),1)
        if re.match(r'^(?:@\[.*?\]\s*)?(?:theorem|def|abbrev|structure)\s', s)],
      'claim': 'REUSED_UNCHANGED_SOURCE_ONLY_NOT_COMPILED_OR_KERNEL_VERIFIED'
    })

latest = []
for name in ['P3HBOriginalGroupCoordinateMixed', 'P3HBOriginalGroupLeibnizAllocation',
             'P3HBOriginalGroupProductFirstDerivative', 'P3HBOriginalGroupJetLeibnizStep']:
    rel = 'docs/source-only/20261105-p3-fourier-coordinate-ibp/' + name + '.lean'
    data = git('show', P3 + ':' + rel)
    latest.append({'path':rel,'commit':P3,'git_blob_sha1':blob(data),
                   'sha256':digest(data),'bytes':len(data),'modified':False})

papers = []
for rel in ['proof-library/source/distribution-prime-product-completion-20261010.txt',
            'proof-library/source/actual-k-distribution-joint-audit.tex']:
    data = subprocess.check_output(['git','-C',str(BASE/'chen-imbalanced-semiprimes'),
                                    'show', PAPER+':'+rel])
    papers.append({'repository':'chen-imbalanced-semiprimes','commit':PAPER,
                   'path':rel,'sha256':digest(data),'git_blob_sha1':blob(data)})

reviews=[]
for rel in ['docs/source-only/20261028-resume-30c/reviews/pp_transfer.md',
            'docs/source-only/20261028-resume-30c/reviews/pp_transfer.json',
            'docs/source-only/20261110-yellow-closure-10t/t06_actual_mixed_fourier/REGISTRY.json',
            'docs/source-only/20261110-yellow-closure-10t/t06_actual_mixed_fourier/REPORT.md',
            'docs/source-only/20261110-yellow-closure-10t/t10_review_analytic_kernel/REGISTRY.json']:
    p=REPO/rel
    data=p.read_bytes()
    reviews.append({'path':str(p).replace('\\','/'),'sha256':digest(data),
                    'git_blob_sha1':blob(data),'bytes':len(data)})

record={
 'schema':'T01_P3_ACTUAL_GROUPED_DERIVATIVE_REUSE_V1',
 'status':'STATIC_REUSE_AUDIT_NO_NEW_LEAN',
 'p3_snapshot':P3, 'new_lean_sources':[],
 'new_proof_required_for_actual_partition_group_identity':False,
 'selected_reused_source_roots_and_named_predecessors':rows,
 'latest_P3_generic_sources_inspected_unchanged':latest,
 'manuscript_sources':papers,'existing_scope_reviews':reviews,
 'completeness_boundary':'Named source reuse map, not an exhaustive installation/build manifest. Exact project and Mathlib closure still require installation and remote verification.',
 'no_new_compile_or_kernel_credit':True,
 'whole_PP_closed':False, 'whole_original_W_membership_closed':False,
 'arbitrary_overlapping_J_generic_P3_claim_closed':False,
 'mathlib_pin':'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1',
 'lean_pin':'leanprover/lean4:v4.33.0-rc1',
 'verification_performed':['source reads','immutable local Git reads','SHA256/Git-blob identity metadata','existing source-review receipt reuse'],
 'prohibited_execution_performed':False,
}
(OUT/'REUSE_MAP.json').write_text(json.dumps(record,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps({'reused_sources':len(rows),'absent_exact_bytes_in_latest_P3':[r['module'] for r in rows if not r['latest_P3_contains_exact_bytes']], 'reuse_map_sha256':digest((OUT/'REUSE_MAP.json').read_bytes())},indent=2))
