"""Read-only source joins for the bounded P3 successor review."""
import hashlib
import json
import os
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASE = HERE.parents[1]
ROOT = BASE.parents[1]
GIT = ROOT / 'goldbach-proof-github-sync-20261110.git'
HEAD = '4ccc54e1423db03315957dc79138a89d4dab7efd'
GEOMETRY = '4733b07d186b2b6aad89e5b9b782c35cc27ebd37'
MATHLIB = 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1'
DRAFT = ROOT / 'goldbach-proof-continuation/.lake/proof-continuation/source-reviews/drafts'
MIRROR = ROOT / 'goldbach-variable-envelope/.lake/ntfs-source-backups/mathlib'


def read(path):
    path = path.absolute()
    return Path('\\\\?\\' + str(path)).read_bytes() if os.name == 'nt' else path.read_bytes()


def sha(data):
    return hashlib.sha256(data).hexdigest()


def identity(data):
    blob = b'blob ' + str(len(data)).encode() + b'\0' + data
    return {'bytes': len(data), 'sha256': sha(data), 'gitBlob': hashlib.sha1(blob).hexdigest()}


def record(path):
    return {'path': path.relative_to(ROOT).as_posix(), **identity(read(path))}


def git(commit, path):
    return subprocess.check_output(
        ['git', '--no-replace-objects', '--git-dir=' + str(GIT), '-c', 'protocol.allow=never',
         'show', commit + ':' + path], env={**os.environ, 'GIT_NO_LAZY_FETCH': '1'})


def at(commit, path, expected):
    data = git(commit, path)
    actual = identity(data)
    assert actual['sha256'] == expected['sha256'] and actual['bytes'] == expected['bytes']
    assert actual['gitBlob'] == expected.get('git_blob', expected.get('git_blob_sha1'))
    return {'commit': commit, 'path': path, **actual}


def save(name, data):
    (HERE / name).write_bytes((json.dumps(data, ensure_ascii=False, indent=2)+'\n').encode())


def main():
    previous = HERE.parent / 'ALLOWLIST.json'
    assert sha(read(previous)) == 'c4270fb6673e4315279a09c9fe474e937024a87fe39225b55f6d46fae111b021'
    assert read(previous) == git(HEAD, 'docs/source-only/20261112-resume/t14-p3-staging-review/ALLOWLIST.json')
    r30_path = BASE / 't01/selection47-resolve/RESOLVED3_PUBLIC_SELECTOR_DELTA.json'
    r30 = {r['module']: at(r['origin']['commit'], r['origin']['path'], r)
           for r in json.loads(read(r30_path))['files']}
    geometry_path = 'docs/source-only/20261112-resume/t04/kuznetsov-next/api-selection/SELECTION.json'
    geometry_bytes = git(GEOMETRY, geometry_path)
    assert geometry_bytes == read(BASE / 't04/kuznetsov-next/api-selection/SELECTION.json')
    geometry_manifest = json.loads(geometry_bytes)
    geometry = {r['module']: at(GEOMETRY, geometry_path.rsplit('/api-selection/', 1)[0] + '/' + r['selected_path'], r['selected'])
                for r in geometry_manifest['selected_modules']}
    for row in geometry_manifest['preexisting_selected']:
        old = at(row['revision'], row['path'], row)
        assert old['gitBlob'] == r30['ImbalancedChen.' + row['module']]['gitBlob']
    subset = {'ImbalancedChen.' + short for short in ['Part3ActualCuspEigenbasisNativeLabels',
              'Part3GammaActualEigenSmoothRepresentative', 'Part3PlanarFourierSeriesClassicalCalculus',
              'Part3SmoothIntegerUnitPartition']}
    assert len(r30) == 3 and len(geometry) == 14
    assert not subset & (set(geometry) | set(r30))

    b8_owner = DRAFT / '20261026b-GammaCompactness/full-cusp-eigenbasis-registry.json'
    b8 = json.loads(read(b8_owner))['candidates'][-1]
    guards = []
    for g in b8['import_preimage_guards']:
        entry = record(Path(g['source_path']))
        assert entry['sha256'] == g['sha256'] and g['dependency_ready_to_install'] is False
        guards.append(dict(module=g['module_name'], historical_ready_to_install=False, **entry))
    assert len(guards) == 3 and b8['ready_to_install'] is False
    d4_owner = DRAFT / '20261026b-DefectCaccioppoli/phase12-eigen-regularity/actual-eigen-smooth-registry.json'
    bd_owner = DRAFT / '20261026b-LocalH1Tests/phase12-eigen-regularity/integration-registry-04.json'
    d4 = json.loads(read(d4_owner))
    bd = json.loads(read(bd_owner))['entries'][0]
    frozen = {}
    for r in [b8, d4, bd]:
        path=Path(r['candidate_path']); source = record(path)
        assert source['sha256']==r['candidate_sha256']
        frozen[path.stem] = {**source, 'historical_ready_to_install': r['ready_to_install']}
    seed_path='ImbalancedChen/Part3SmoothIntegerUnitPartition.lean'
    seed_bytes=git(HEAD, seed_path)
    assert sha(seed_bytes)=='3eb60ea1153e4138bb21f6ca54d240f6d02bbb88639d38da69bbbc9e11b3620d'
    frozen['Part3SmoothIntegerUnitPartition']={'commit':HEAD,'path':seed_path,**identity(seed_bytes)}

    pin_path=ROOT/'goldbach-proof-continuation/docs/source-only/20261110-yellow-closure-10t/t01_remote_fifth_kernel/repairs/PINNED_EXTERNAL_TREES.json'
    pins={pkg['package']:pkg for pkg in json.loads(read(pin_path))}
    assert pins['mathlib']['sha']==MATHLIB and pins['Lean']['ref']=='v4.33.0-rc1'
    expected={r['path']:r for r in pins['mathlib']['files']}
    subjects={
        'Analysis/Normed/Operator/Bilinear':[431,432],
        'Analysis/Normed/Operator/Basic':[199,200],
        'Topology/Algebra/Module/ContinuousLinearMap/Basic':[710,711],
        'Analysis/Normed/Group/Constructions':[241,243],
        'Analysis/Calculus/ContDiff/Bounds':[155],
        'Analysis/Calculus/ContDiff/FTaylorSeries':[116,120],
        'Analysis/SpecialFunctions/SmoothTransition':[206],
        'Analysis/Calculus/ContDiff/Defs':[908,1160,1172],
        'Topology/Defs/Filter':[134],
        'Analysis/Calculus/SmoothSeries':[122,123,124],
    }
    api=[]
    for stem, line_numbers in subjects.items():
        path='Mathlib/'+stem+'.lean'; source=read(MIRROR/path)
        ids=identity(source); assert ids['gitBlob']==expected[path]['git_blob_sha1'] and ids['bytes']==expected[path]['bytes']
        lines=source.decode().splitlines()
        api.append({'commit':MATHLIB,'path':path,**ids,'source_lines':{n:lines[n-1] for n in line_numbers}})
    save('INPUT_AND_DEDUP.json',dict(prior_publication=HEAD,prior_review=record(previous),
         R30_selector=record(r30_path),R30_verified=r30,geometry_selector={'commit':GEOMETRY,'path':geometry_path,**identity(geometry_bytes)},
         geometry14_verified=geometry,R30_three_reused_in_geometry_by_blob=True,four_review_modules_overlap=[],
         originals=frozen,native_labels_owner=record(b8_owner),native_labels_direct_dependencies=guards,
         representative_owner=record(d4_owner),fourier_calculus_owner=record(bd_owner), external_source_tree=record(pin_path),
         lean_ref=pins['Lean']['ref'],mathlib_commit=MATHLIB,api=api,source_closure_complete=False,kernel_verified=False))


def compare_frozen_packet():
    author = BASE / 't13-p3-staging/successor'
    registry_path = author / 'REGISTRY.json'
    registry = json.loads(read(registry_path))
    assert sha(read(registry_path)) == 'f0bdb5e0bf5f197716af1e3a3eeaa4f2911734ec90beee6013dee84ac025d0e7'
    listed = {row['relative_path'] for row in registry['files']}
    assert len(listed)==len(registry['files'])
    assert {p.relative_to(author).as_posix() for p in author.rglob('*') if p.is_file()}==listed|{'REGISTRY.json'}
    for row in registry['files']:
        ids=identity(read(author/row['relative_path']))
        assert (ids['bytes'],ids['sha256'],ids['gitBlob'])==(row['bytes'],row['sha256'],row['git_blob_sha1'])

    evidence = json.loads(read(HERE / 'INPUT_AND_DEDUP.json'))
    pairs = []
    expected_counts = [5,25,20,9]
    for i, row in enumerate(json.loads(read(author/'SOURCE_SELECTIONS.json'))['rows']):
        name=row['module'].rsplit('.',1)[1]
        origin=evidence['originals'][name]
        original=(git(origin['commit'],origin['path']) if 'commit' in origin else read(ROOT/origin['path']))
        expected=original
        edits=[]

        def replace(before,after,count):
            nonlocal expected
            old=before.encode(); new=after.encode()
            assert expected.count(old)==count, (name,before)
            edits.append(dict(occurrences=count,old=before,new=after))
            expected=expected.replace(old,new)

        if name=='Part3GammaActualEigenSmoothRepresentative':
            replace('open scoped UpperHalfPlane','open scoped UpperHalfPlane Topology ContDiff',1)
        elif name=='Part3PlanarFourierSeriesClassicalCalculus':
            replace('ContinuousLinearMap.opNorm_le_bound (norm_nonneg _)',
                    'ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)',2)
            replace('ContinuousLinearMap.smulRightL_apply,','ContinuousLinearMap.smulRightL_apply_apply,',2)
        elif name=='Part3SmoothIntegerUnitPartition':
            replace('open Set Filter\n','open Set Filter\nopen scoped ContDiff\n',1)
            replace('Real.smoothTransition.contDiff (n := ∞)',
                    'Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))',3)
        else:
            assert name=='Part3ActualCuspEigenbasisNativeLabels' and row['ready_to_install'] is False
        selected=Path(row['selected_postimage']['path']); actual=read(selected)
        assert actual==expected and sha(original)==row['preimage']['sha256']
        assert identity(actual)['gitBlob']==row['selected_postimage']['git_blob_sha1']
        def headers(data):
            source=data.decode()
            found={}
            for m in re.finditer(r'^(?:@\[[^\n]*?\]\s+)?(?:private )?(?:def|theorem|abbrev|lemma) ([\w.]+)',source,re.M):
                depth=0; stop=m.end()
                while stop<len(source):
                    ch=source[stop]; depth+=(ch in '([{')-(ch in ')]}'); assert depth>=0
                    if depth==0 and source[stop:stop+2]==':=':break
                    stop+=1
                assert stop<len(source) and m.group(1) not in found
                found[m.group(1)]=source[m.start():stop]
            return found
        pre_headers=headers(original)
        assert headers(actual)==pre_headers and len(pre_headers)==expected_counts[i]
        assert row['ready_to_install'] is False
        pairs.append(dict(module=row['module'],preimage=origin,selected=record(selected),
                          install_path=row['install_path'],independently_reproduced_edits=edits,
                          explicit_decl_count=len(pre_headers),unchanged_explicit_headers=list(pre_headers),
                          ready_to_install=False,disposition=('SOURCE_ONLY_POSTIMAGE' if edits else 'REUSE_HISTORICALLY_HELD_ORIGINAL')))
    assert len(pairs)==4 and sum(r['explicit_decl_count'] for r in pairs)==59
    save('ALLOWLIST.json',dict(schema='T14_P3_SUCCESSOR_INDEPENDENT_STATIC_CHOICES_V1',
         author_registry=record(registry_path),hashed_author_registry_members=len(listed),
         review=record(HERE/'REVIEW.md'),input_and_dedup=record(HERE/'INPUT_AND_DEDUP.json'),
         independent_readback=record(Path(__file__).resolve()),sources=pairs,unchanged_headers=59,
         changed_headers=0,new_postimages=3,existing_unchanged_source=1,
         prior_R30_and_geometry_bytes_reused=17,new_mathematical_declarations=0,
         ready_to_install=False,source_closure_complete=False,compiler_run=False,
         full_type_equality_verified=False,kernel_verified=False,proof_credit=0))


if __name__=='__main__':
    main()
    compare_frozen_packet()
