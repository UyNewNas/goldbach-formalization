"""Complete offline recovery+Shape check with independently frozen job outputs."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
CHECKER = HERE / 'readback.py'
spec = importlib.util.spec_from_file_location('reviewed_readback', CHECKER)
r = importlib.util.module_from_spec(spec)
spec.loader.exec_module(r)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--archive', required=True, type=Path)
    p.add_argument('--external-success', required=True, type=Path)
    p.add_argument('--run-stdout', required=True, type=Path)
    p.add_argument('--recovery', required=True, type=Path)
    p.add_argument('--capture-observation', required=True, type=Path)
    args=p.parse_args()
    recpin={'bytes':4245880,'sha256':'8a0b3afab2c32114fc124a69071160f05a1c3dc8ef84d4a19b3ae4866a66b8c6'}
    cert='3ce215e5339bf2363d6004c8427a3c8c5e8197d82ca6b933bf4e49d9aef1f089'
    workflow='e3f9588b43b5d3bb08a24f6938c1e6dde2e9968a719f06f28bbcd8166e822d3e'
    bundle={'bytes':1057200,'sha256':'3a7f08f9f47c68a25bbc300ea2124cbfecd5332a74e425e3dba494d0540630d4'}
    binding='7425ce0a4d3c5907e55a74041f6f12456559f9d854a774fa648a16c2cd6f0f34'
    success=r.decode(args.external_success.read_bytes()); capture=r.decode(args.capture_observation.read_bytes())
    rr,rm=r.archive(args.recovery,recpin['bytes'],recpin['sha256']);view,rec=r.recovery(rr,rm,cert,workflow)
    r.same(capture['export']['archive'],dict(recpin,path=r.REC+'/RECOVERY_EXPORT.tar.xz'),'retained recovery exterior')
    for key in ('certificate','history','current_runtime_guard'):r.same(capture['certified'][key],view[key],'external capture '+key)
    so,sm=r.archive(args.archive,bundle['bytes'],bundle['sha256']);v=r.shape(so,sm,rr,view,binding,workflow)
    r.same(success['archive'],dict(bundle,path=r.SHAPE+'/exports/shape-evidence.tar.xz'),'external Shape archive')
    r.same((success['status'],success['accepted_steps'],success['accepted_targets'],success['P2_6_complete']),('SINGLE_SHAPE_SUCCESS',3,1,False),'external disposition')
    for key,n,size,digest in [('success','verification/SUCCESS.json',1767,'aa85ba34e6d36512e0c7ffc73c493d3870a551f868e9496dc740ff65479cc594'),('combined_index','COMBINED_INDEX.json',736,'eb681180a96cb5d9a12026b2839d9ccc70e6aeba8efad0376b48359562ac56c6')]:
        expected={'bytes':size,'sha256':digest,'path':r.SHAPE+'/'+n}
        r.same(success[key],expected,'out-of-band '+key)
        r.same(r.ident(so[n],r.SHAPE+'/'+n),expected,'archived '+key)
    r.same(len(so[r.TOOL+'/RECOVERY_BINDING.json']),967,'binding length')
    events=[r.decode(s) for s in args.run_stdout.read_bytes().splitlines() if s.strip()]
    completed=[e for e in events if e.get('status')=='accepted']
    r.same([e['mode'] for e in completed], list(r.MODES),'original process output mode order')
    for e in completed:
        metrics=v['metrics'][e['mode']]
        r.same((metrics['elapsed_seconds'],metrics['peak_rss_bytes']),(e['elapsed_seconds'],e['peak_rss_bytes']),'cloud metrics '+e['mode'])
    name=r.MODULE+'.geometryPacked05_parse_decode_shape'
    owned=r.decode(so['verification/owned-declarations.json'])
    endpoint,=[d for d in owned['declarations'] if d['name']==name]
    r.need('GeometryShape' in endpoint['type'] and 'SourceJson.parse' in endpoint['type'] and 'decodeGeometry' in endpoint['type'] and 'concreteGeometry05' in endpoint['type'],'required endpoint type components')
    source=so['project/'+r.REL+'.lean']
    r.same(r.pin(source),{'bytes':7508,'sha256':'fd381d234ea1c9100d9248542273663df8b3042282326410a9fe8aaf961d90bb'},'reviewed repaired source')
    r.same(so[r.TOOL+'/owned-audits/'+r.SHORT+'.lean'],(r.REF/r.OLD_TOOL/'owned-audits'/(r.SHORT+'.lean')).read_bytes(),'unchanged original compiled audit')
    report={'status':'PASS_REAL_SHAPE_EXPORT_INDEPENDENT_READBACK','job':'64419527e8294cd2880cc7575368f6d5','archive':success['archive'],'member_count':len(so),'SUCCESS':success['success'],'COMBINED_INDEX':success['combined_index'],'capture_certificate':view['certificate'],'binding':r.ident(so[r.TOOL+'/RECOVERY_BINDING.json'],r.SHAPE+'/'+r.TOOL+'/RECOVERY_BINDING.json'),'recovery_archive':recpin,'ten_root_files':rec['ten_root_files'],'ten_root_bytes':rec['ten_root_bytes'],'shape':v,'owned_endpoint':endpoint,'new_formal_scope':'Cell05 parser and concrete decoder output with finite GeometryShape','P2_6_complete':False,'proof_commands_launched_by_this_readback':0}
    print(json.dumps(report,indent=2,sort_keys=True))


if __name__=='__main__':
    main()
