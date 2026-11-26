#!/usr/bin/env python3
"""Freeze the bounded audit and read-only probe; no new Lean sources."""
from pathlib import Path, PurePosixPath
import ast
import hashlib
import io
import json
import sys
import tarfile

sys.dont_write_bytecode = True
from audit_cell12 import DOCS, HERE, REPO, fp, pin_data, protected, write_new


def main():
    audit = json.loads((DOCS/'LOCAL_AUDIT.json').read_text())
    assert protected() == audit['protected_files']
    entries = {}
    for path in sorted(HERE.glob('*.py')):
        ast.parse(path.read_text(), filename=str(path))
        entries[str(path.relative_to(REPO))] = path
    for name in ['SUPPLIER_MAP.json', 'RAW12_HISTORY_LOCATORS.json', 'STRESS_EXECUTION_PLAN.json',
                 'STRUCTURAL_COST_MODEL.json', 'LOCAL_AUDIT.json', 'REPORT.md']:
        path = DOCS/name
        entries[str(path.relative_to(REPO))] = path
    members = [{'member': member, **pin_data(path.read_bytes())} for member,path in sorted(entries.items())]
    contents = {'schema': 'cell12_bounded_stress_audit_package_v1',
                'status': 'SOURCE_REUSE_AUDIT_RAW12_CONTEXT_GATE_PENDING', 'members': members,
                'existing_candidate_owners': 7, 'new_Lean_sources': 0, 'new_Lean_steps_run': 0,
                'future_maximum_missing_steps': 21, 'full_supplier_kernel_closed': False}
    output = DOCS/'cell12-stress-audit-v1.tar.xz'
    assert not output.exists()
    with tarfile.open(output, 'w:xz', preset=6) as tar:
        for member,path in sorted(entries.items()):
            data=path.read_bytes()
            info=tarfile.TarInfo(member)
            info.size,info.mode,info.mtime=len(data),0o644,0
            tar.addfile(info,io.BytesIO(data))
        data=(json.dumps(contents,indent=2)+'\n').encode()
        info=tarfile.TarInfo('PACKAGE_CONTENTS.json')
        info.size,info.mode,info.mtime=len(data),0o644,0
        tar.addfile(info,io.BytesIO(data))
    expected={row['member']:row for row in members}
    seen=set()
    with tarfile.open(output, 'r:xz') as tar:
        for item in tar:
            relative=PurePosixPath(item.name)
            assert item.isfile() and item.name not in seen and not relative.is_absolute() and '..' not in relative.parts
            seen.add(item.name)
            data=tar.extractfile(item).read()
            if item.name=='PACKAGE_CONTENTS.json':
                assert json.loads(data)==contents
            else:
                assert pin_data(data)=={key:expected[item.name][key] for key in ('bytes','sha256')}
                assert data==entries[item.name].read_bytes()
    assert seen==set(entries)|{'PACKAGE_CONTENTS.json'}
    assert protected()==audit['protected_files']
    write_new(DOCS/'PACKAGE.json',{**contents,'archive':fp(output),'archive_members_checked':len(seen)})
    handoff=DOCS/'HANDOFF_STAGING_FILES.txt'
    stage=set(entries)|{str(path.relative_to(REPO)) for path in [output,DOCS/'PACKAGE.json',handoff]}
    write_new(handoff,'\n'.join(sorted(stage))+'\n')
    backup=Path('/workspace/scratch/59264dd64286/p26-transfer/cell12-stress-audit-v1')
    for path in [output,DOCS/'PACKAGE.json',handoff,DOCS/'REPORT.md',DOCS/'RAW12_HISTORY_LOCATORS.json',HERE/'probe_raw12.py']:
        write_new(backup/path.name,path.read_bytes())
        assert (backup/path.name).read_bytes()==path.read_bytes()
    print(json.dumps({'status':contents['status'],'archive':fp(output),'archive_members':len(seen),
                      'handoff_files':len(stage),'existing_candidates':7,'new_Lean_steps_run':0,
                      'backup':str(backup/output.name)}))


if __name__=='__main__':
    main()
