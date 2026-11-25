#!/usr/bin/env python3
"""Recover/check seven exact existing Git blobs and their selection overlay.

No Lean, Lake, cloud task, production install, proof edit, Git checkout, or
reference update is performed. --write writes only inside this recovery package.
The default checks the frozen package against the recorded immutable sources.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
LIGHT = ROOT / 'docs/source-only/20261126-p2-5-lightweight-original-schedule'
FAMILY = ROOT / 'docs/source-only/20261125-p2-5-fourteen-family'
COMMIT = '9b1b19b44e756777738a8b37ef677429c60eb5e3'
TREE = 'b8853b75b3cb5e616708a6f0d4968480d9e47a3a'
LIGHT_MANIFEST_SHA = '3460264894b89f6a3737c56ffa8a96a3e067cb89a353a05751bdc60a7ee0b371'
LIGHT_GRAPH_SHA = '8183b8324f60ba49f00c868bbf410c46ae553e794db8c4b0071505104fd97f1a'
SCHEDULE_MAP_SHA = '66635d48a92fe38540c47ebf95e2600538ad8bb95b644b792d8b786588afdcd1'
PREFIX = 'ImbalancedChen.'
ROWS = [
    ('P2Saving16ActionGatesClosedBox', '20261120-p2-saving16-action-gates',
     '43fa343912b1044cc037c1d6c86ab584e4ac08b3',
     'dbe5c449f7cadb6ad520a6ff3abb70f60e5e93cb88df6db60751f8e38352cfb6', 7918,
     'P2Saving16ActualUpperCornerCap', 'specified_missing_owner'),
    ('P2Saving16OriginalPhysicalEightSource', '20261120-p2-saving16-original-physical-eight',
     'd0c502884b50f0e0fb02b1b9ddebf36f244aea60',
     '9398acbfd56c442d45b80851f65e23096341a070305a04a75aab5c9d20ef13eb', 12914,
     'P2Saving16NegativeCoefficientComparison', 'specified_missing_owner'),
    ('P2Saving16All96ClosedBox', '20261120-p2-saving16-all96-closed-box',
     '107530a34ac5206b3a5dfedac82063a228921695',
     '345f94fb41f48b588d09764bfd30e5433361762047fd2bd21e73168661cf8aa1', 9400,
     'P2Saving16ActionGatesClosedBox', 'existing_schedule_map_provider_now_reached'),
    ('P2Saving16ThreeCapRows', '20261120-p2-saving16-three-cap-rows',
     '335c7c24a144e1fce82fb61f2e6380a31f9f2106',
     '257a8f0961fbf64c6eb54b87f64f445d8e0c8ba0c363c0861b74281d3349acde', 11404,
     'P2Saving16All96ClosedBox', 'exact_recursive_import_provider'),
    ('P2Saving16FourHistoryRows', '20261120-p2-saving16-four-history-rows',
     '03ca6011ffddba5b4329723350f3517b5bbe8b99',
     '184e3edbdb5aab27a72e6fdddec12a5dd482320e1317b96f7ef601b203d5a42a', 9301,
     'P2Saving16ThreeCapRows', 'exact_recursive_import_provider'),
    ('P2Saving16SevenOrderRowsCarrier', '20261120-p2-saving16-seven-order-rows',
     '37c57fd5201e670bdb973c8a7b29ee6921c947b5',
     'e4701f91f55b5789eca72b743696ab679019240b5a82d47ac1c129fc170fee1b', 10340,
     'P2Saving16FourHistoryRows', 'exact_recursive_import_provider'),
    ('P2Saving16FourthRowSignedProduct', '20261120-p2-saving16-fourth-row',
     '9e88640cc2a6d7f3aac5100eb7ec68784d8788b0',
     '149aaadfe4797c110c307a4e87f38444897af2a0128e3a29caa796bb6af54a07', 7683,
     'P2Saving16SevenOrderRowsCarrier', 'exact_recursive_import_provider'),
]
IMPORTERS = [
    ('P2Saving16ActualUpperCornerCap',
     'docs/source-only/20261120-p2-saving16-upper-corner/P2Saving16ActualUpperCornerCap.lean',
     '91d14c01229b7d1640147e7c09b092892c1596b93eacb672deb9a174e15310cc'),
    ('P2Saving16NegativeCoefficientComparison',
     'docs/source-only/20261120-p2-saving16-negative-switch/P2Saving16NegativeCoefficientComparison.lean',
     '98ede46aae64caff3023391b884dc899a363c3eb26f7e97e34418a1bcdd1c4cd'),
]


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def git(*args):
    env = dict(os.environ)
    env['GIT_OPTIONAL_LOCKS'] = '0'
    return subprocess.check_output(['git', *args], cwd=ROOT, env=env, timeout=60)


def relative(path):
    return str(path.relative_to(ROOT))


def imports(raw):
    result = []
    for line in raw.decode().splitlines():
        if line.startswith('import '):
            names = line.removeprefix('import ').split()
            assert all(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*', n) for n in names)
            result.extend(names)
    return result


def json_bytes(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode()


def check_lightweight_package():
    raw = (LIGHT / 'MANIFEST.json').read_bytes()
    assert sha(raw) == LIGHT_MANIFEST_SHA
    manifest = json.loads(raw)
    for row in manifest['files']:
        data = (LIGHT / row['path']).read_bytes()
        assert len(data) == row['bytes'] and sha(data) == row['sha256'], row['path']


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--write', action='store_true')
    args = ap.parse_args()
    check_lightweight_package()
    graph_path = LIGHT / 'DEPENDENCY_REDUCTION.json'
    graph_raw = graph_path.read_bytes()
    assert sha(graph_raw) == LIGHT_GRAPH_SHA
    base = json.loads(graph_raw)
    selected = {name: dict(row) for name, row in base['after_module_selection'].items()}
    schedule_path = FAMILY / 'SCHEDULE_SOURCE_MAP.json'
    schedule_raw = schedule_path.read_bytes()
    assert sha(schedule_raw) == SCHEDULE_MAP_SHA
    schedule = json.loads(schedule_raw)
    assert git('show', '-s', '--format=%H', COMMIT).decode().strip() == COMMIT
    assert git('show', '-s', '--format=%T', COMMIT).decode().strip() == TREE
    recovered, files = [], {}
    for name, folder, blob, digest, size, caller, role in ROWS:
        path = f'docs/source-only/{folder}/{name}.lean'
        raw = git('show', COMMIT + ':' + path)
        assert len(raw) == size and sha(raw) == digest, name
        assert git('rev-parse', COMMIT + ':' + path).decode().strip() == blob, name
        assert hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest() == blob
        text = raw.decode()
        assert 'namespace ' + PREFIX + name in text
        markers = [word for word in ['SOURCE_ONLY', 'UNCOMPILED', 'UNEVALUATED'] if word in text]
        assert len(markers) == 3, name
        source_imports = imports(raw)
        declarations = [{'kind': match[0], 'name': match[1]} for match in re.findall(
            r'^(?:(?:private|protected|noncomputable) )*(def|abbrev|theorem|lemma|structure|inductive|instance)\s+([^\s(:]+)',
            text, re.M)]
        out = 'ImbalancedChen/' + name + '.lean'
        files[out] = raw
        row = {
            'module': PREFIX + name, 'selected_path': relative(HERE / out),
            'sha256': digest, 'bytes': size, 'imports': source_imports,
            'origin': {'repository': 'UyNewNas/goldbach-formalization', 'commit': COMMIT,
                       'tree': TREE, 'path': path, 'git_blob_sha1': blob,
                       'sha256': digest, 'bytes': size},
            'required_by': PREFIX + caller, 'selection_role': role,
            'source_status_markers': markers, 'source_declarations': declarations,
            'recovered_bytes_equal_original_blob': True, 'source_rewritten': False,
            'compiled_or_audited_by_this_recovery': False, 'accepted': False,
        }
        assert row['module'] not in selected, row['module']
        selected[row['module']] = row
        recovered.append(row)
        if name == 'P2Saving16All96ClosedBox':
            old = next(r for r in schedule['upstream_sources'] if r['path'] == path)
            assert old['known_source_checkpoint'] == COMMIT and old['git_blob_sha1'] == blob
            assert old['sha256'] == digest and old['bytes'] == size
            row['already_named_schedule_map_record'] = old

    importer_checks = []
    for name, path, expected in IMPORTERS:
        raw = git('show', COMMIT + ':' + path)
        assert sha(raw) == expected == selected[PREFIX + name]['sha256']
        importer_checks.append({'module': PREFIX + name, 'commit': COMMIT, 'path': path,
                                'sha256': expected, 'matches_existing_selection': True})
    for row in recovered:
        assert row['module'] in selected[row['required_by']]['imports'], row['module']

    def closure(root):
        seen, missing, stack, cycles = set(), [], [], []

        def visit(name):
            if not name.startswith(PREFIX):
                return
            if name in stack:
                cycles.append(stack[stack.index(name):] + [name])
                return
            if name in seen:
                return
            seen.add(name)
            if name not in selected:
                missing.append({'module': name, 'import_path': stack + [name]})
                return
            stack.append(name)
            for dependency in selected[name]['imports']:
                visit(dependency)
            stack.pop()

        visit(root)
        return {'module_count': len(seen), 'modules': sorted(seen),
                'missing_providers': missing, 'cycles': cycles}

    closures = {root: closure(root) for root in base['comparisons']}
    assert all(not row['missing_providers'] and not row['cycles'] for row in closures.values())
    assert closures[PREFIX + 'P4AOriginalR17PaidIntegral']['module_count'] == 1487
    assert closures[PREFIX + 'P2Saving16R17StrictFourteenCorners']['module_count'] == 1517
    provenance = {
        'schema': 'p25-original-schedule-exact-source-recovery-v1',
        'status': 'SOURCE_RECOVERED_ONLY_NOT_INSTALLED_NOT_COMPILED_NOT_ACCEPTED',
        'checkpoint': {'repository': 'UyNewNas/goldbach-formalization', 'commit': COMMIT, 'tree': TREE},
        'scope': 'Seven existing source-only blobs needed after resolving the two recorded opaque import providers. No proof or source rewrite.',
        'source_count': len(recovered), 'sources': recovered,
        'existing_importer_byte_identity': importer_checks,
        'unchanged_lightweight_package': {'path': relative(LIGHT / 'MANIFEST.json'), 'sha256': LIGHT_MANIFEST_SHA},
        'unchanged_schedule_map': {'path': relative(schedule_path), 'sha256': SCHEDULE_MAP_SHA},
        'recovery_search_boundary': 'Only exact recursively encountered module names in the known checkpoint and the existing source map; no global filename scan, new proof, or remote code search.',
        'owned_impact': 'Each recovered source owner remains uncompiled/unaccepted. Future normal compilation, kernel replay and full serialized/environment owned audit must include all generated and private declarations.',
        'production_installations': [], 'lean_executions': [], 'cloud_actions': [],
        'accepted': False, 'finite_cell_credit': False, 'all14_integral_credit': False,
        'Q96_proved': False, 'P2_5_proved': False,
    }
    files['SOURCE_PROVENANCE.json'] = json_bytes(provenance)
    combined = {
        'schema': 'p25-original-schedule-recovered-selection-overlay-v1',
        'status': 'STATIC_IMPORT_GRAPH_WITH_ALL_PROVIDERS_NOT_AN_ACCEPTANCE_RECEIPT',
        'base_graph': {'path': relative(graph_path), 'sha256': LIGHT_GRAPH_SHA,
                       'selected_map_key': 'after_module_selection'},
        'overlay_rule': 'Keep every base provider/version unchanged. Add exactly the seven byte-identical source rows below. The union defines this combined selection view.',
        'base_provider_count': len(base['after_module_selection']),
        'overlay_provider_count': len(recovered), 'combined_provider_count': len(selected),
        'overlays': recovered, 'closures': closures,
        'previous_all14_opaque_nodes': base['comparisons'][PREFIX + 'P2Saving16R17StrictFourteenCorners']['after']['missing_providers'],
        'source_materialization_limit': 'Only the seven added providers are materialized by this package. Historical base source paths/transforms and the existing two IntegralDefinitions deduplication hunks remain required before an actual complete installation.',
        'unchanged_remaining_distribution_obligation': base['remaining_distribution_obligation'],
        'unchanged_compatibility_owners': 'The three old heavy endpoint postimages in the frozen lightweight package remain compatibility-only, outside these two root closures.',
        'accepted': False, 'finite_cell_credit': False, 'all14_integral_credit': False,
        'Q96_proved': False, 'P2_5_proved': False,
    }
    files['COMBINED_SELECTION.json'] = json_bytes(combined)
    for name, raw in files.items():
        path = HERE / name
        if args.write:
            path.parent.mkdir(parents=True, exist_ok=True)
            if path.exists():
                assert path.read_bytes() == raw, 'Refuse to overwrite different recovery bytes: ' + name
            else:
                path.write_bytes(raw)
        else:
            assert path.read_bytes() == raw, name
    check_lightweight_package()
    print(json.dumps({'status': 'EXACT_BLOB_RECOVERY_STATIC_CHECK_ONLY', 'sources': len(recovered),
                      'files_checked': len(files),
                      'closure_counts': {name: row['module_count'] for name, row in closures.items()},
                      'missing_providers': [], 'source_rewrites': 0,
                      'lightweight_package_unchanged': True, 'lean_executions': 0, 'cloud_actions': 0}))


if __name__ == '__main__':
    main()
