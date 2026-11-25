#!/usr/bin/env python3
"""Compile the pinned reader and new companion, reusing the checked bridge."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parent
LOCAL = ROOT / 'local'
LIB = LOCAL / 'lib/lean'
READER_ROOT = LOCAL / 'reader-source'
REPO = Path('/workspace/p26-recovery')
PRODUCTION = Path('/workspace/p26-source-closure')
RUNTIME = Path('/workspace/library-files/p34-runtime/lean-4.33.0-rc1-linux')
PACKAGES = Path('/workspace/library-files/p34-proof-work/.lake/packages')
COMMIT = '508d757913ea9c536c0d4f95abb35c090b940a29'
READER_PATH = 'ImbalancedChen/P2OriginalSaving19SourceJson.lean'
READER_SHA = 'ae38e3ed3f11d8bc3350b9d35d1fed164a4494210ed993b2b99e8cd709f93424'
BRIDGE_PATH = 'ImbalancedChen/P2OriginalSaving19CharInputBridge.lean'
BRIDGE_SHA = '18d5e23b30fd7333bb2b3a80c4bedae0ff4f8e190b45833c390a6cbffc1bba21'
BRIDGE_OBJECT_SHA = 'aec6d507428f15642aaf6cb0767dae7b5ec7965325e0d1c2f2166f66bfc12e70'
COMPANION_PATH = 'ImbalancedChen/P2OriginalSaving19SourceJsonCharInput.lean'
DECLARATIONS = [
    'parseChars',
    'parse_ofList',
    'parseChars_eq_parse_ofList',
    'parse_eq_parseChars_of_chars_eq',
    'parse_eq_parseChars_of_ofList_eq',
    'parse_bind_eq_parseChars_bind_of_ofList_eq',
]
NAMESPACE = 'ImbalancedChen.P2OriginalSaving19Archive.SourceJson.'


def fingerprint(path):
    data = path.read_bytes()
    return {'path': str(path), 'bytes': len(data),
            'sha256': hashlib.sha256(data).hexdigest()}


def main():
    lean = RUNTIME / 'bin/lean'
    checker = RUNTIME / 'bin/leanchecker'
    version = subprocess.check_output([str(lean), '--version']).decode().strip()
    assert '4.33.0-rc1' in version and '62eed1db4d67327ec8120be05f1a1b0847d74561' in version
    blob = subprocess.check_output(['git', 'show', COMMIT + ':' + READER_PATH], cwd=REPO)
    assert len(blob) == 6035 and hashlib.sha256(blob).hexdigest() == READER_SHA
    assert (PRODUCTION / READER_PATH).read_bytes() == blob
    assert fingerprint(ROOT / BRIDGE_PATH)['sha256'] == BRIDGE_SHA
    bridge_object = LIB / Path(BRIDGE_PATH).with_suffix('.olean')
    assert fingerprint(bridge_object)['sha256'] == BRIDGE_OBJECT_SHA
    generic_result = json.loads((LOCAL / 'DIAGNOSTIC.json').read_text())
    assert generic_result['status'] == 'LOCAL_GENERIC_NORMAL_AND_KERNEL_PASS_NO_ARCHIVE_ACCEPTANCE'
    for row in generic_result['commands']:
        assert row['exit_code'] == 0
        assert row['source']['sha256'] == BRIDGE_SHA
        assert row['object']['sha256'] == BRIDGE_OBJECT_SHA

    for relative in (BRIDGE_PATH, COMPANION_PATH):
        text = (ROOT / relative).read_text()
        assert not re.search(r'\b(?:sorry|admit|native_decide|unsafe)\b|^\s*axiom\s+', text, re.M)

    reader_source = READER_ROOT / READER_PATH
    reader_source.parent.mkdir(parents=True, exist_ok=True)
    if reader_source.exists():
        assert reader_source.read_bytes() == blob
    else:
        reader_source.write_bytes(blob)

    env = os.environ.copy()
    env['PATH'] = str(RUNTIME / 'bin') + os.pathsep + env.get('PATH', '')
    env['LEAN_PATH'] = ':'.join(map(str, [LIB] + sorted(PACKAGES.glob('*/.lake/build/lib/lean'))))
    marker = RUNTIME / 'lib/lean/Lean.olean'
    marker_before = fingerprint(marker)
    production_before = fingerprint(PRODUCTION / READER_PATH)
    result = {
        'status': 'COMPANION_LOCAL_DIAGNOSTIC_STARTED_NO_ARCHIVE_ACCEPTANCE',
        'source_commit': COMMIT, 'source_origin_path': READER_PATH,
        'reader_source': fingerprint(reader_source),
        'generic_bridge_source': fingerprint(ROOT / BRIDGE_PATH),
        'generic_bridge_object_reused': fingerprint(bridge_object),
        'generic_bridge_recompiled': False, 'lean_version': version,
        'lean': fingerprint(lean), 'leanchecker': fingerprint(checker),
        'LEAN_PATH': env['LEAN_PATH'],
        'Core_imported': False, 'original_fixtures_loaded': False,
        'production_modified': False, 'P34_sources_or_objects_modified': False,
        'remote_jobs_started': False, 'archive_complete': False,
        'only_cell00_proved': False, 'commands': [],
    }

    def run(stage, module, command, cwd, source, output=None):
        log = LOCAL / (module + '-' + stage + '.log')
        started = time.monotonic()
        with log.open('w') as stream:
            completed = subprocess.run(command, cwd=cwd, env=env, stdout=stream,
                                       stderr=subprocess.STDOUT, timeout=60)
        row = {'stage': stage, 'module': module, 'command': command,
               'cwd': str(cwd), 'elapsed_seconds': time.monotonic() - started,
               'exit_code': completed.returncode, 'source': fingerprint(source),
               'log': fingerprint(log)}
        if output is not None and output.exists():
            row['object'] = fingerprint(output)
        result['commands'].append(row)
        print(json.dumps(row, sort_keys=True), flush=True)
        if completed.returncode != 0:
            result['status'] = 'COMPANION_LOCAL_DIAGNOSTIC_FAILED_NO_ARCHIVE_ACCEPTANCE'
            (LOCAL / 'COMPANION_DIAGNOSTIC.json').write_text(json.dumps(result, indent=2) + '\n')
            print(log.read_text(), flush=True)
            raise SystemExit(completed.returncode)

    for relative, source_root in ((READER_PATH, READER_ROOT), (COMPANION_PATH, ROOT)):
        source = source_root / relative
        module = relative.removesuffix('.lean').replace('/', '.')
        output = LIB / Path(relative).with_suffix('.olean')
        assert not output.exists(), f'Refusing to recompile an existing module: {module}'
        run('normal', module, [str(lean), '-j1', '-M4096', '-o', str(output), str(source)],
            source_root, source, output)
        run('kernel', module, [str(checker), '--verbose', module], source_root, source, output)

    audit = LOCAL / 'CompanionInterfacesAudit.lean'
    audit.write_text('import ImbalancedChen.P2OriginalSaving19SourceJsonCharInput\n\n' +
                     '\n'.join('#check ' + NAMESPACE + name + '\n#print axioms ' + NAMESPACE + name
                               for name in DECLARATIONS) + '\n')
    run('types-axioms', 'CompanionInterfacesAudit', [str(lean), '-j1', '-M4096', str(audit)],
        ROOT, audit)
    audit_text = (LOCAL / 'CompanionInterfacesAudit-types-axioms.log').read_text()
    records = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit_text)
    assert {name for name, _ in records} == {NAMESPACE + name for name in DECLARATIONS}
    result['interface_axioms'] = {}
    for name, axioms in records:
        found = {x.strip() for x in axioms.split(',') if x.strip()}
        assert found <= {'propext', 'Classical.choice', 'Quot.sound'}, (name, found)
        result['interface_axioms'][name] = sorted(found)
    assert fingerprint(marker) == marker_before
    assert fingerprint(PRODUCTION / READER_PATH) == production_before
    assert fingerprint(bridge_object)['sha256'] == BRIDGE_OBJECT_SHA
    result['runtime_marker_unchanged'] = marker_before
    result['production_reader_unchanged'] = production_before
    result['status'] = 'COMPANION_LOCAL_NORMAL_KERNEL_TYPES_AXIOMS_PASS_NO_ARCHIVE_ACCEPTANCE'
    (LOCAL / 'COMPANION_DIAGNOSTIC.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'status': result['status'], 'archive_complete': False}), flush=True)


if __name__ == '__main__':
    main()
