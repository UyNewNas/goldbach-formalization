"""Atomically reuse12reviewed exact supplier postimages and the sealed HB owner. No proof commands."""
from pathlib import Path
import hashlib
import json
import shutil
import subprocess
import sys

ROOT = Path(sys.argv[1])
P15_SLUG = sys.argv[2]
P14_SLUG = sys.argv[3]
WORK = Path('/workspace/p14-continue-20261128')
P15 = Path('/workspace/p15-continue-20261127')
BRANCH = 'codex/p1-4-continuation-20261125'

def git(*args, text=True):
    return subprocess.check_output(['git', *args], cwd=WORK, text=text)

def sha(b):
    return hashlib.sha256(b).hexdigest()

assert not git('status', '--porcelain')
ADOPTION_ROOT = Path(__file__).resolve().parent
precheck = json.loads((ADOPTION_ROOT / 'PRECHECK.json').read_text())
review = json.loads((ADOPTION_ROOT / 'INDEPENDENT_REVIEW.json').read_text())
assert review['blocking_findings'] == [] and review['postimage_modules'] == 12
assert review['no_hypothesis_or_bound_weakening_found'] and review['no_conflicting_accepted_P14_implementation_variant_found_in_checked_evidence']
assert git('rev-parse', 'HEAD').strip() == precheck['p14_head'] == review['p14_base']
assert subprocess.check_output(['git','rev-parse','HEAD'], cwd=P15, text=True).strip() == precheck['p15_head'] == review['p15_source_commit']
assert json.loads((ADOPTION_ROOT / 'STATIC_THEOREM_SIGNATURE_PRECHECK.json').read_text())['all_public_private_theorem_signatures_preserved_after_stated_qualification']
assert json.loads((ADOPTION_ROOT / 'HISTORICAL_P14_POSTIMAGE_MATCHES.json').read_text())['matching_modules'] == 9
expected = {row['module']:row for row in precheck['mismatched_sources']}
assert len(expected) == 12
postimages = []
published = json.loads((ROOT / 'PUBLISHED.json').read_text())
assert published['remote_head_verified'] and published['source_and_archive_git_blobs_verified']
assert not published.get('additional_publications')
attempt = json.loads((ROOT / 'ACCEPTED_ATTEMPT.json').read_text())['attempt']
result = json.loads((ROOT / attempt / 'VALIDATION_RESULTS.json').read_text())
assert result['status'] == 'PASS_ISOLATED_NORMAL_KERNEL_FULL_OWNED'
assert json.loads((ROOT / 'INDEPENDENT_REVIEW.json').read_text())['blocking_findings'] == []
archive = json.loads((ROOT / 'ARCHIVE.json').read_text())
assert sha((ROOT / archive['archive']).read_bytes()) == archive['sha256']
source = Path(result['source']['path']).read_bytes()
assert sha(source) == result['source']['sha256']
rel = result['module'].replace('.', '/') + '.lean'
assert sha(git('show', 'HEAD:' + rel, text=False)) == json.loads((ROOT / 'SOURCE_CHANGE_PLAN.json').read_text())['original_source_sha256']
checks = []
for row in json.loads((ROOT / 'REUSED_CONTEXTS.json').read_text()) + json.loads((ROOT / 'ORDINARY_ACTUAL_SOURCE_CLOSURE.json').read_text())['sources']:
    h = sha(git('show', 'HEAD:' + row['module'].replace('.', '/') + '.lean', text=False))
    if h != row['source']['sha256']:
        old = expected[row['module']]
        assert h == old['p14_source_sha256']
        assert row['source'] == old['accepted_p15_source']
        data = subprocess.check_output(['git','show',precheck['p15_head'] + ':' + old['path']],cwd=P15)
        assert sha(data) == row['source']['sha256']
        postimages.append((old, data))
        h = row['source']['sha256']
    checks.append(dict(module=row['module'], sha256=h))
assert len(postimages) == 12 and len(checks) == 71
assert {old['module'] for old,_ in postimages} == set(expected)
base = git('rev-parse', 'HEAD').strip()
docs_rel = 'docs/p1/20261128/' + P14_SLUG
docs = WORK / docs_rel
assert not docs.exists()
adoption_docs_rel = 'docs/p1/20261128/p14-hb-supplier-source-reuse'
adoption_docs = WORK / adoption_docs_rel
assert not adoption_docs.exists()
# All read-only checks finish before the first working-tree mutation.
for old, data in postimages:
    assert sha(git('show','HEAD:' + old['path'],text=False)) == old['p14_source_sha256']
    target = WORK / old['path']
    target.parent.mkdir(parents=True,exist_ok=True)
    target.write_bytes(data)
adoption_docs.mkdir(parents=True)
for name in ['PRECHECK.json','INDEPENDENT_REVIEW.json','STATIC_THEOREM_SIGNATURE_PRECHECK.json','HISTORICAL_P14_POSTIMAGE_MATCHES.json']:
    shutil.copyfile(ADOPTION_ROOT / name,adoption_docs / name)
shutil.copyfile(__file__,adoption_docs / 'reuse_with_source_postimages.py')
adoption = dict(status='PASS_EXACT_EXISTING_SUPPLIER_SOURCE_ADOPTION',p15_origin_commit=precheck['p15_head'],p14_base_commit=base,postimage_source_pairs=precheck['mismatched_sources'],final71source_bindings=checks,ordinary_supplier_independent_owner_kernel_full_owned_not_claimed=True,HBTransport_only_owned=13,HBTransport_only_private=0,new_normal_or_kernel_commands=0,new_proof_credit=0,original_register='18/21',three_ProperPower_HOLDs_unchanged=True,whole_P1_4_complete=False,whole_P1_5_complete=False)
(adoption_docs / 'ADOPTION.json').write_text(json.dumps(adoption,indent=2)+'\n')
(adoption_docs / 'README.md').write_text('# Reuse existing HB supplier source postimages\n\nAdopt exactly12 existing P15/Member supplier source variants with the sealed HBTransport owner. Nine postimages already occur as exact Git blobs in this branch historical verification archive. All81 supplier theorem statements retain their original hypotheses and targets after explicit qualification of the intended dyadic R. Local product parentheses clarify individual factors in proof steps. No proof command is replayed, no new mathematical credit is claimed for ordinary suppliers, and no full Lake import-closure acceptance is inferred. Final71 project-source bindings are recorded. P1.4/P1.5,18/21 and three ProperPower HOLDs remain open/unchanged.\n')
shutil.copytree(P15 / 'docs/p1/20261128' / P15_SLUG, docs)
(WORK / rel).write_bytes(source)
if (docs / 'prepare_input.py').exists():
    (docs / 'P14_INPUT_SETUP.md').write_text('# P1.4 original input setup\n\nFrom the repository root:\n\n```sh\npython3 ' + docs_rel + '/prepare_input.py --repository .\n```\n\nThe helper verifies the original tracked fourth payload and prepares the include-reader alias. It runs no Lean command; original acceptance scope and archive are reused unchanged.\n')
(docs / 'P14_SOURCE_REUSE.json').write_text(json.dumps(dict(status='PASS_EXACT_ACCEPTED_SOURCE_REUSE',
    p15_origin_commit=published['commit'], p14_base_commit=base,
    source_sha256=result['source']['sha256'], import_source_checks=checks,
    transitive_parent_reuse_provenance_retained=True,
    new_normal_or_kernel_commands=0, new_proof_credit=0,
    whole_P1_4_complete=False, whole_P1_5_complete=False), indent=2) + '\n')
for check in checks:
    check_rel = check['module'].replace('.', '/') + '.lean'
    check_data = (WORK / check_rel).read_bytes() if check['module'] in expected else git('show','HEAD:' + check_rel,text=False)
    assert sha(check_data) == check['sha256']
subprocess.run(['git', 'add', '--sparse', rel, docs_rel,adoption_docs_rel,*[old['path'] for old,_ in postimages]], cwd=WORK, check=True)
subprocess.run(['git', '-c', 'core.whitespace=cr-at-eol', 'diff', '--cached', '--check'], cwd=WORK, check=True)
body = Path('/tmp/' + P14_SLUG + '-commit.txt')
body.write_text('Reuse accepted ' + result['module'].split('.')[-1] + '\n\nAtomically adopt12reviewed exact existing ordinary HB supplier source postimages and the unchanged accepted P1.5 HB owner/evidence. All71source closure hashes match the original acceptance;81supplier theorem statements retain original hypotheses/targets after intended R qualification. Nine supplier postimages already exist in P14 historical Git. Ordinary dependencies keep their original acceptance scopes; no independent supplier owner credit is inferred. Zero normal/kernel replay and zero new proof credit. P1.4 and P1.5 remain open.\n')
subprocess.run(['git', 'commit', '-F', str(body)], cwd=WORK, check=True)
subprocess.run(['git', 'push', 'origin', 'HEAD:' + BRANCH], cwd=WORK, check=True)
head = git('rev-parse', 'HEAD').strip()
assert git('ls-remote', 'origin', 'refs/heads/' + BRANCH).split()[0] == head
assert sha(git('show', head + ':' + rel, text=False)) == result['source']['sha256']
assert sha(git('show', head + ':' + docs_rel + '/' + archive['archive'], text=False)) == archive['sha256']
for check in checks:
    assert sha(git('show', head + ':' + check['module'].replace('.', '/') + '.lean', text=False)) == check['sha256']
assert not git('status', '--porcelain')
(ADOPTION_ROOT / 'PUBLISHED.json').write_text(json.dumps(dict(commit=head,remote_branch=BRANCH,remote_head_verified=True,all71Git_source_blobs_verified=True,source_archive_verified=True,new_normal_or_kernel_commands=0,new_proof_credit=0,whole_P1_4_complete=False,whole_P1_5_complete=False),indent=2)+'\n')
published['additional_publications'] = [dict(commit=head, remote_branch=BRANCH,
    remote_head_source_archive_verified=True, new_proof_commands=0)]
(ROOT / 'PUBLISHED.json').write_text(json.dumps(published, indent=2) + '\n')
print('P14_REUSED', head)
