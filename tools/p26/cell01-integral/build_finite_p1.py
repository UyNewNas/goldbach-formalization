"""Bounded missing-row builds on P1; P2 join qualification remains separate."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

BASE = Path('/workspace/p26-cell01-finite-build-v2-20261128')
SYSROOT = Path('/workspace/toolchains/lean-4.33.0-rc1-linux')
PACKAGES = Path('/workspace/blue-member-build/.lake/packages')
EXTRA_SEARCH = []
RUNTIME_LABEL = 'P1'
CURRENT = Path('/workspace/p26-current439-20261128')
OLD = Path('/workspace/p26-continuation-59264dd64286/cell01-finite-suppliers-P1')
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def pin(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return {'path': str(path), 'bytes': path.stat().st_size, 'sha256': h.hexdigest()}


def main(rows):
    assert rows and len(rows) == len(set(rows))
    assert all(1 <= n < 144 and not 98 <= n <= 106 for n in rows)
    objects = BASE / 'objects'
    objects.mkdir(exist_ok=True)
    # Lean selects a package directory before resolving a module filename.
    # Materialize the complete selected project union in the first directory.
    for directory in [CURRENT / 'objects', OLD / 'objects']:
        for source in sorted((directory / 'ImbalancedChen').rglob('*.olean')):
            target = objects / source.relative_to(directory)
            target.parent.mkdir(parents=True, exist_ok=True)
            if target.exists():
                assert pin(target)['sha256'] == pin(source)['sha256'], str(target)
            else:
                os.link(source, target)
    native = PACKAGES / 'goldbach/.lake/build/lib/lean'
    for extension in ['*.ir', '*.so']:
        for source in sorted((native / 'ImbalancedChen').rglob(extension)):
            target = objects / source.relative_to(native)
            target.parent.mkdir(parents=True, exist_ok=True)
            if not target.exists(): os.link(source, target)
    search = [objects, CURRENT / 'objects', OLD / 'objects']
    search += sorted(PACKAGES.glob('*/.lake/build/lib/lean'))
    search += EXTRA_SEARCH
    search.append(SYSROOT / 'lib/lean')
    env = os.environ.copy()
    env.pop('CONTROL_PLANE_API_KEY', None)
    env['PATH'] = str(SYSROOT / 'bin') + ':' + env.get('PATH', '')
    env['LEAN_PATH'] = ':'.join(map(str, search[:-1]))
    env['LEAN_NUM_THREADS'] = '1'
    template_path = BASE / 'FINITE_IMPORT_TEMPLATE.json'
    imports = json.loads(template_path.read_text())
    input_paths = {template_path, Path(__file__), BASE / 'OwnedTemplate.lean', BASE / 'MANIFEST.json'}
    for module in imports:
        rel = module.replace('.', '/')
        chosen = next((directory / (rel + '.olean') for directory in search
                       if (directory / (rel + '.olean')).is_file()), None)
        assert chosen is not None, module
        input_paths.add(chosen)
        for suffix in ['.olean.private', '.olean.server']:
            item = chosen.with_suffix(suffix)
            if item.is_file(): input_paths.add(item)
        for suffix in ['.ir', '.so']:
            for directory in search:
                item = directory / (rel + suffix)
                if item.is_file():
                    input_paths.add(item)
                    break
        if module.startswith('ImbalancedChen.'):
            candidates = [CURRENT / 'sources' / (rel + '.lean'), OLD / 'project' / (rel + '.lean')]
            source = next((p for p in candidates if p.exists()), None)
            assert source is not None, module
            input_paths.add(source)
    for name in ['lean', 'leanchecker']:
        input_paths.add(SYSROOT / 'bin' / name)
    input_paths.update(SYSROOT.glob('lib/*.so*'))
    input_paths.update(SYSROOT.glob('lib/lean/*.so*'))
    manifest = json.loads((BASE / 'MANIFEST.json').read_text())
    for row in rows:
        rel = f'project/ImbalancedChen/P2OriginalSaving19Cell01Row{row:03d}Finite.lean'
        item = pin(BASE / rel)
        assert all(item[k] == manifest['files'][rel][k] for k in ['bytes', 'sha256'])
        input_paths.add(BASE / rel)
    inputs = [pin(path) for path in sorted(input_paths)]
    batch = BASE / ('batch-' + '-'.join(map(str, rows)))
    batch.mkdir(exist_ok=False)
    fingerprint = batch / 'INPUT_FINGERPRINTS.json'
    fingerprint.write_text(json.dumps(inputs, indent=2) + '\n')
    print(json.dumps({'input_files': len(inputs), 'input_bytes': sum(i['bytes'] for i in inputs),
                      'rows': rows, 'free_disk_bytes': shutil.disk_usage(BASE).free}), flush=True)
    flags = ['--trust=0', '-DwarningAsError=true', '-j1', '-M8192',
             '-DmaxRecDepth=1000000', '-DmaxHeartbeats=0']

    def build(row):
        assert shutil.disk_usage(BASE).free > 64 * 1024**2, 'Leave disk headroom; checkpoint current batch.'
        name = f'P2OriginalSaving19Cell01Row{row:03d}Finite'
        module = 'ImbalancedChen.' + name
        out = batch / name
        out.mkdir()
        source = BASE / 'project/ImbalancedChen' / (name + '.lean')
        obj = objects / 'ImbalancedChen' / (name + '.olean')
        obj.parent.mkdir(exist_ok=True)
        assert not obj.exists(), 'Do not repeat a completed row.'
        audit = out / 'OwnedAudit.lean'
        audit.write_text((BASE / 'OwnedTemplate.lean').read_text().replace('Row098Finite', f'Row{row:03d}Finite'))
        state = {'status': 'running', 'formal_acceptance': False, 'P2_6_complete': False,
                 'scope': f'One exact original finite row under pinned {RUNTIME_LABEL} inputs; no original-floor/integral endpoint or current P2 import-join acceptance.',
                 'row': row, 'module': module, 'source': pin(source), 'audit_source': pin(audit),
                 'inputs': pin(fingerprint), 'lean_path': env['LEAN_PATH'], 'commands': []}

        def save():
            (out / 'RUN.json').write_text(json.dumps(state, indent=2) + '\n')

        for label, argv in [
            ('normal', [SYSROOT / 'bin/lean', *flags, '-o', obj, source]),
            ('kernel', [SYSROOT / 'bin/leanchecker', module]),
            ('owned', [SYSROOT / 'bin/lean', *flags, audit]),
        ]:
            log = out / (label + '.log')
            record = {'label': label, 'argv': list(map(str, argv)), 'cwd': str(BASE)}
            state['commands'].append(record)
            save()
            started = time.monotonic()
            with log.open('wb') as stream:
                result = subprocess.run(record['argv'], cwd=BASE, env=env,
                    stdout=stream, stderr=subprocess.STDOUT, timeout=360)
            record.update(exit_code=result.returncode, seconds=time.monotonic() - started, log=pin(log))
            save()
            if result.returncode or 'sorryAx' in log.read_text():
                state['status'] = 'failed'
                save()
                raise RuntimeError(name + ' ' + label + '\n' + log.read_text()[-2500:])
        declarations, inventories, completes, actual_imports = [], [], [], []
        for line in (out / 'owned.log').read_text().splitlines():
            if not line.startswith('P26_GEOMETRY01_AUDIT_'): continue
            tag, raw = line.split(' ', 1)
            item = json.loads(raw)
            if tag.endswith('_DECL'):
                assert item['module'] == module and not (item['unsafe'] or item['partial'] or item['axiom'])
                assert set(item['axioms']) <= ALLOWED and '⋯' not in item['type']
                declarations.append(item)
            elif tag.endswith('_INVENTORY'): inventories.append(item)
            elif tag.endswith('_COMPLETE'): completes.append(item)
            elif tag.endswith('_IMPORTS'): actual_imports.append(item)
        assert len(inventories) == len(completes) == len(actual_imports) == 1
        assert set(actual_imports[0]) == set(imports) | {module}
        names = sorted(i['name'] for i in declarations)
        assert len(names) == len(set(names)) == 292
        assert names == sorted(inventories[0]['serialized']) == sorted(inventories[0]['environment'])
        assert completes[0] == {'module': module, 'count': len(names)}
        state.update(status='passed_local_finite_checks', object=pin(obj), owned_declarations=len(names))
        save()
        print(json.dumps({'row': row, 'status': state['status'], 'owned_declarations': len(names)}), flush=True)
        return state

    with ThreadPoolExecutor(max_workers=2) as workers:
        results = list(workers.map(build, rows))
    for item in inputs:
        assert pin(Path(item['path'])) == item, item['path']
    for result in results:
        for key in ['source', 'audit_source', 'object']:
            assert pin(Path(result[key]['path'])) == result[key]
    summary = {'status': 'passed_local_finite_checks', 'formal_acceptance': False, 'P2_6_complete': False,
               'rows': rows, 'owned_declarations': sum(r['owned_declarations'] for r in results),
               'inputs': pin(fingerprint), 'external_and_project_inputs_rechecked': len(inputs),
               'results': [pin(batch / f'P2OriginalSaving19Cell01Row{n:03d}Finite/RUN.json') for n in rows]}
    (batch / 'SUMMARY.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('rows', nargs='+', type=int)
    main(parser.parse_args().rows)
