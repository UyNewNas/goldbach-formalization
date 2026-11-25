#!/usr/bin/env python3
"""Copy frozen Geometry/Moments/shape suppliers without compiling any of them."""
from pathlib import Path
import hashlib,json,re,subprocess
ROOT=Path(__file__).resolve().parent
BASE=ROOT.parent
PROJECT=ROOT/'project';OBJECTS=ROOT/'objects'
for p in [PROJECT/'ImbalancedChen',OBJECTS/'ImbalancedChen',ROOT/'logs',ROOT/'attempts',ROOT/'owners',ROOT/'provenance']:
    p.mkdir(parents=True,exist_ok=True)

def fp(p):
    p=Path(p);b=p.read_bytes();return {'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}

def copy(p,q):
    p=Path(p);q=Path(q);assert not q.exists(),q
    q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(p.read_bytes())
    assert p.read_bytes()==q.read_bytes()
    return {'original':fp(p),'copy':fp(q)}

geometry=BASE/'archive-geometry00-typed'
gc=geometry/'FULL_SOURCE_CLOSURE.json'
assert fp(gc)['sha256']=='c82b5463eab8b9d2237268517ffe0579cdf682af11f88b96ab2de2416ce66f2b'
grow=json.loads(gc.read_text())['sources_objects_and_receipts'];assert len(grow)==303
moment=BASE/'archive-cell00-shapes'
mb=json.loads((moment/'BOOTSTRAP.json').read_text())
mrows=[{'module':x['module'],'source':x['source']['copy'],'object':x['object']['copy']}
       for x in mb['reused_sources_objects']]
assert len(mrows)==42
mn=json.loads((moment/'logs/normal-shape-v2-result.json').read_text())
mk=json.loads((moment/'logs/kernel-shape-v2-result.json').read_text())
assert mn['status']==mk['status']=='succeeded' and mn['source']==mk['source'] and mn['object']==mk['object']
assert mn['source']['sha256']=='1c077c3ed062c0682fe11af0b530458b734b490f4415f6d7d77323e26cd11159'
assert mn['object']['sha256']=='c8c151d48f14c9ab0b416c026443ce8ed329cf3336ddcc6808edd067db82f8b6'
mrows.append({'module':mn['module'],'source':mn['source'],'object':mn['object']})
reused={}
for family,rows in [('geometry_typed',grow),('moment_shape',mrows)]:
    for row in rows:
        for kind in ['source','object']:
            assert fp(row[kind]['path'])==row[kind]
        mod=row['module'];mp=Path(mod.replace('.','/'))
        if mod in reused:
            item=reused[mod]
            for kind in ['source','object']:
                assert item[kind]['original']['sha256']==row[kind]['sha256'],('Shared source/object differs',mod,kind)
            item['additional_origins'].append({'family':family,'source':row['source'],'object':row['object']})
            continue
        item={'module':mod,'family':family,'source':copy(row['source']['path'],PROJECT/mp.with_suffix('.lean')),
              'object':copy(row['object']['path'],OBJECTS/mp.with_suffix('.olean')),
              'additional_origins':[],'extra_object_siblings':[],'recompiled':False}
        original=Path(row['object']['path'])
        for p in original.parent.glob(original.name+'.*'):
            item['extra_object_siblings'].append(copy(p,OBJECTS/mp.parent/p.name))
        reused[mod]=item
assert len(reused)==339,len(reused)
provenance=[]
for label,p in [
    ('GeometryTyped_FULL_SOURCE_CLOSURE.json',gc),
    ('GeometryTyped_FULL_ACCEPTANCE_MANIFEST.json',geometry/'FULL_ACCEPTANCE_MANIFEST.json'),
    ('MomentShape_SOURCE_MANIFEST.json',moment/'SOURCE_MANIFEST.json'),
    ('MomentShape_normal_result.json',moment/'logs/normal-shape-v2-result.json'),
    ('MomentShape_kernel_result.json',moment/'logs/kernel-shape-v2-result.json')]:
    provenance.append(copy(p,ROOT/'provenance'/label))
archive=Path('/workspace/p26-source-closure/ImbalancedChen/P2OriginalSaving19Archive.lean')
assert fp(archive)['sha256']=='f48ba6e6522a3a76bd81ef1be15875563163a4df6e7891c1422b6562ee31ed49'
head=subprocess.check_output(['git','-C','/workspace/p26-source-closure','rev-parse','HEAD'],text=True).strip()
gitbytes=subprocess.check_output(['git','-C','/workspace/p26-source-closure','show',head+':ImbalancedChen/P2OriginalSaving19Archive.lean'])
assert gitbytes==archive.read_bytes()
archive_copy=copy(archive,ROOT/'provenance/OriginalArchive.lean')
fixtures=[fp(Path('/workspace/p26-original-inputs')/name) for name in [
    'eighth-third-minorant-extension-20261009-a23-s23_low-00-cell.witness.json',
    'eighth-third-moment-refinement-20261009-a23-low-00.witness.json']]
assert [x['sha256'] for x in fixtures]==[
    '87e3c3da5a86a3ea16c1dcae3a5735ea8b0dc7db05d42b5f5cc3aae66cd54691',
    'd88e9d02334dfa840f81c0e2be8e97d559978ac3848fdea13990deced9a65052']
gb=json.loads((geometry/'BOOTSTRAP.json').read_text())
result={'schema':'saving19_cell00_geometry_joint_shape_bootstrap_v1','reused_module_count':len(reused),
        'reused_helpers':list(reused.values()),'reused_geometry_inventory':303,'reused_moment_shape_inventory':43,
        'shared_inventory_modules':7,'provenance':provenance,
        'original_archive':archive_copy,'original_archive_git_commit':head,
        'original_fixtures':fixtures,'external_LEAN_PATH_roots':gb['external_LEAN_PATH_roots'],
        'all_suppliers_recompiled':False,'production_modified':False,'remote_jobs_submitted':False,
        'P1_strict_claimed':False,'Archive_CellShape0_alias_connected':False}
p=ROOT/'BOOTSTRAP.json';assert not p.exists();p.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'bootstrap':fp(p),'reused_module_count':len(reused),
                  'copied_object_bytes':sum(x['object']['copy']['bytes'] for x in reused.values())},indent=2))
