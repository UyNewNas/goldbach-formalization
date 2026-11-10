"""Author-side source/JSON/import metadata only. No Lean or proof execution.

The original1046 and v2 graph are reused, not rediscovered. Only newly selected
published sources have their import text read. All Git hashes name raw bytes.
"""
from __future__ import annotations
import copy
import hashlib
import json
import re
import subprocess
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASE = HERE.parent
WORKSPACE = BASE.parents[4]
MIRROR = WORKSPACE / 'goldbach-proof-github-sync-20261110.git'
COMMIT = '62af0da0e7668d17d1add82141f009b89010211a'
PREFIX = 'docs/source-only/20261110-yellow-closure-10t/'


def sha(payload):
    return hashlib.sha256(payload).hexdigest()


def desc(payload):
    return {'bytes': len(payload), 'sha256': sha(payload),
            'git_blob_sha1': hashlib.sha1(b'blob ' + str(len(payload)).encode() + b'\0' + payload).hexdigest()}


def read(path):
    return Path('\\\\?\\' + str(path.resolve())).read_bytes()


def local_json(path):
    return json.loads(read(path))


def git(path):
    return subprocess.check_output(['git', '--git-dir=' + str(MIRROR), 'show', COMMIT + ':' + path])


def published_json(path):
    return json.loads(git(path))


def write(name, value):
    (HERE / name).write_bytes((json.dumps(value, indent=2, ensure_ascii=False) + '\n').encode())


def imports(payload):
    # Same module-header reader as the frozen v1/v2 import inventory. Comments
    # are stripped; syntax/evaluation is intentionally not performed here.
    text = payload.decode('utf-8-sig')
    text = re.sub(r'/\-.*?\-/', '', text, flags=re.S)
    text = re.sub(r'--[^\n]*', '', text)
    return [m for line in text.splitlines() if re.match(r'^\s*(?:public\s+)?import\s+', line)
            for m in re.sub(r'^\s*(?:public\s+)?import\s+', '', line).split()]


def main():
    old = local_json(BASE / 'full87_remote_v2/EXACT_INSTALL_MANIFEST.json')
    selected = {r['module']: copy.deepcopy(r) for r in old['files']}
    old_names = set(selected)
    tree = subprocess.check_output(['git', '--git-dir=' + str(MIRROR), 'ls-tree', '-r', '--name-only', COMMIT]).decode().splitlines()
    names = defaultdict(list)
    for p in tree:
        if p.endswith('.lean'):
            names[Path(p).name].append(p)
    owner_records, changes, payloads = [], [], {}
    explicit = {}

    def select(path, expected=None, reason='owner-pinned actual paid-I87 source'):
        module = 'ImbalancedChen.' + Path(path).stem
        if module in explicit and explicit[module] != path:
            raise ValueError('Conflicting explicit variants: ' + module)
        explicit[module] = path
        payload = git(path)
        d = desc(payload)
        if expected and any(d[k] != expected[k] for k in ['sha256', 'bytes'] if k in expected):
            raise ValueError('Published owner input differs: ' + path)
        row = {'module': module, 'install_path': module.replace('.', '/') + '.lean',
               **d, 'imports': imports(payload), 'origin': {'kind': 'git', 'commit': COMMIT, 'path': path},
               'selection': 'actual_R17_paid_I87_extension', 'source_variant_reason': reason}
        previous = selected.get(module)
        if previous:
            for k in ['core_selection', 'semantic_group', 'semantic_supersedes']:
                if k in previous:
                    row[k] = previous[k]
            if previous['sha256'] != d['sha256']:
                changes.append({'module': module, 'pre': previous, 'post': row, 'reason': reason})
        selected[module] = row
        payloads[module] = payload
        return module

    t04_dir = PREFIX + 't04_compiler_physical_payment/'
    t03_dir = PREFIX + 't03_saved87_actual_gain/'
    t05_dir = PREFIX + 't05_all22_actual_density/'
    owner_paths = [t04_dir + 'successor/REGISTRY.json', t04_dir + 'successor_transport/REGISTRY.json',
                   t03_dir + 'successor_R17_transport/REGISTRY.json', t03_dir + 'successor_R17_paid/REGISTRY.json',
                   t05_dir + 'successor_G14/R17_REGISTRY.json']
    owners = {p: published_json(p) for p in owner_paths}
    for path in owner_paths:
        owner_records.append({'path': path, 'commit': COMMIT, **desc(git(path))})

    # Atomic semantic environment: retain the selected four, pin their exact
    # now-published objects instead of depending on mutable checkout bytes.
    for row in old['semantic_selection']['selections']:
        path = t05_dir + 'successor_G14/r17_compat/' + row['module'].split('.')[-1] + '.lean'
        select(path, row['post'], 'atomic all-four R17 mathematical semantic correction')

    new_roots = []
    for r in owners[t04_dir + 'successor/REGISTRY.json']['files']:
        select(t04_dir + 'successor/' + r['path'], r, 'reviewed corrected whole-third source, prior12 collection')
    for r in owners[t04_dir + 'successor_transport/REGISTRY.json']['files']:
        new_roots.append(select(t04_dir + 'successor_transport/' + r['name'], r, 'reviewed complete26 rectangular transport collection'))
    for r in owners[t03_dir + 'successor_R17_transport/REGISTRY.json']['new_lean']:
        path = r['path'].removeprefix('goldbach-proof-continuation/')
        new_roots.append(select(path, r, 'original four-source R17 signed transport and same-cutoff variant'))
    paid = owners[t03_dir + 'successor_R17_paid/REGISTRY.json']['new_source']
    primary = select(paid['path'], paid, 'actual signed density/count terminal with original I87 and actual corrected rho')
    new_roots.append(primary)
    for name, h in [('P4AOriginalNonsingletonComparison', 'f35dd6869dea5a4b51d78539332f9d4898fc61d49fa94ce07bf090f713252f7b'),
                    ('P4AOriginalNonsingletonEighthParent', '4129c55486ffead49d264e9542dbef574940f6ee020a26c8665280ae119c1846')]:
        new_roots.append(select(t05_dir + 'successor_G14/' + name + '.lean', {'sha256': h}, 'actual R17 nonsingleton comparison and eighth-parent interface'))

    # Mandatory namespace compatibility patch, solely on the isolated copy.
    module = 'ImbalancedChen.P4AOriginalOrderedThirdFullPolicy'
    row = selected[module]
    pre = copy.deepcopy(row)
    patch_path = t04_dir + 'successor/PUBLIC_API.patch'
    patch_record = {'path': patch_path, 'commit': COMMIT, **desc(git(patch_path))}
    if patch_record['sha256'] != '92f023f7921196d1c5c089c10348b8941c1006c460ea6fb69aebaf97e4f1d7cf':
        raise ValueError('Unreviewed FullPolicy public API patch')
    old_text = 'open P1OriginalVariableFourthContinuation (finiteMax)\nopen P2OriginalFourthCapProducerInterface (producerEligible)'
    new_text = 'open P1OriginalVariableFourthContinuation (finiteMax producerEligible)'
    payload = payloads[module]
    if payload.count(old_text.encode()) != 1 or pre['sha256'] != '5a29602d2b9a79384b497714186b757bb6a60d34c3e0e7738cda8a0177bd03fd':
        raise ValueError('Wrong FullPolicy preimage')
    output = payload.replace(old_text.encode(), new_text.encode())
    if sha(output) != '01f09fb673c06fb7950c3eff48dbe9dc815c9dc983afe6f61341a171475a2324':
        raise ValueError('Wrong FullPolicy API patch result')
    row.update(desc(output))
    row['pre_input'] = {**desc(payload), 'origin': pre['origin']}
    row['transform'] = [{'old': old_text, 'new': new_text, 'count': 1}]
    row['isolated_API_patch'] = patch_record
    payloads[module] = output
    changes.append({'module': module, 'pre': pre, 'post': copy.deepcopy(row), 'reason': 'mandatory exact public API namespace patch; no declaration change'})

    def resolve(module, caller):
        if module in selected:
            return
        basename = module.split('.')[-1] + '.lean'
        candidates = names.get(basename, [])
        if module == 'ImbalancedChen.P4AOriginalSavedSixthWordAccess':
            path = t05_dir + 'successor_G4_API/' + basename
            select(path, {'sha256': '84db8e1359c4e47e3bffd10cc7ca76a62a4c01c546d55ecbeb67c0613f60637f'},
                   'reviewed parser API proof-body correction, old a6b10008 version explicitly superseded')
        elif len(candidates) == 1:
            select(candidates[0], reason='unique published exact module required by ' + caller)
        else:
            # Multiple identical published copies are not semantically ambiguous.
            payload_variants = defaultdict(list)
            for p in candidates:
                payload_variants[sha(git(p))].append(p)
            if len(payload_variants) == 1:
                path = sorted(candidates, key=lambda p: (not p.startswith('ImbalancedChen/'), len(p), p))[0]
                select(path, reason='byte-identical published alternatives required by ' + caller)
                selected[module]['identical_published_alternatives'] = sorted(candidates)
            else:
                unresolved[module] = {'caller': caller, 'candidates': dict(payload_variants)}

    unresolved = {}
    seen = set()
    def visit(module):
        if module in seen:
            return
        seen.add(module)
        for imp in selected[module]['imports']:
            if imp.startswith('ImbalancedChen.'):
                resolve(imp, module)
                if imp in selected:
                    visit(imp)
    for module in new_roots:
        visit(module)

    # The12 source collection is inventory; only true imports or explicit26
    # audit roots become active. No missing dependency is dropped to save work.
    actual_paid = set()
    def closure(module, acc):
        if module in acc:
            return
        acc.add(module)
        for imp in selected[module]['imports']:
            if imp.startswith('ImbalancedChen.') and imp in selected:
                closure(imp, acc)
    closure(primary, actual_paid)
    active = set(old['targets'][0]['closure_modules']) | seen
    fresh = sorted(set(old['fresh_kernel_modules']) | active | {'ImbalancedChen.Full87R17PaidAudit'})
    project_additions = sorted(set(selected) - old_names)
    new_active = sorted(active - set(old['targets'][0]['closure_modules']))
    extensions = [selected[n] for n in project_additions]
    discovery = {
        'schema': 'full87-paid-I87-v3-exact-source-closure-discovery', 'compiled': False, 'kernel_verified': False,
        'source_commit': COMMIT, 'base_manifest': desc(read(BASE / 'full87_remote_v2/EXACT_INSTALL_MANIFEST.json')),
        'owner_registries': owner_records, 'mandatory_FullPolicy_patch': patch_record,
        'primary_module': primary, 'new_scope_roots': sorted(set(new_roots)),
        'actual_paid_terminal_closure': sorted(actual_paid), 'new_scope_closure': sorted(seen),
        'active_module_names': sorted(active), 'new_active_module_names': new_active,
        'additional_source_records': extensions, 'changed_source_records': changes,
        'full_selected_files': sorted(selected.values(), key=lambda r: r['module']),
        'mandatory_legacy_kernel_modules': old['fresh_kernel_modules'], 'fresh_kernel_modules': fresh,
        'unresolved': unresolved,
        'counts': {'installed': len(selected), 'active': len(active), 'new_source_inventory': len(project_additions),
                   'new_active': len(new_active), 'actual_paid_closure': len(actual_paid), 'new_scope_closure': len(seen),
                   'fresh_kernel': len(fresh), 'legacy_kernel': len(old['fresh_kernel_modules'])}}
    write('SOURCE_CLOSURE_DISCOVERY.json', discovery)
    print(json.dumps({'counts': discovery['counts'], 'unresolved': unresolved}, indent=2))


if __name__ == '__main__':
    main()
