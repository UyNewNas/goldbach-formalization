#!/usr/bin/env python3
"""Read exact relocated evidence without rewriting historical JSON or running Lean."""
from pathlib import Path, PurePosixPath
import hashlib
import json
import re
import stat

ROW001 = 'ImbalancedChen.P2OriginalSaving19Cell01Row001Finite'
ROW001_SOURCE_SHA = 'c15da8c66ab55245dfab3ea2bbcdbc7c070dbe71bff6e7da38b476ce44808876'
ROW001_OBJECT_SHA = 'ff3b1fde26acd4a453c52088a15168eeb9f594765e2e997e3c8db765da093713'
ROW001_ORIGIN = PurePosixPath('/workspace/p26-continuation-59264dd64286/cell01-row001-finite')
MODES = ('normal', 'kernel', 'owned')
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def canonical(path, exists=False):
    path = Path(path)
    need(path.is_absolute() and '..' not in path.parts, f'Absolute canonical path required: {path}')
    current = Path(path.anchor)
    for index, part in enumerate(path.parts[1:]):
        current /= part
        try:
            info = current.lstat()
        except FileNotFoundError:
            need(not exists, f'Missing required path: {current}')
            continue
        need(not stat.S_ISLNK(info.st_mode), f'Symlinked path rejected: {current}')
        if index < len(path.parts) - 2:
            need(stat.S_ISDIR(info.st_mode), f'Non-directory ancestor: {current}')
    return path


def within(root, path, exists=False):
    root, path = canonical(root), canonical(path, exists)
    need(path.is_relative_to(root), f'Path escapes root: {path} / {root}')
    return path


def disjoint(left, right):
    left, right = canonical(left), canonical(right)
    need(not left.is_relative_to(right) and not right.is_relative_to(left),
         f'Roots overlap in an ancestor direction: {left} / {right}')


def identity(ref):
    need(isinstance(ref, dict) and all(key in ref for key in ('path', 'bytes', 'sha256')),
         'Missing file identity fields')
    path, size, digest = ref['path'], ref['bytes'], ref['sha256']
    need(isinstance(path, str) and '\x00' not in path and PurePosixPath(path).is_absolute()
         and '..' not in PurePosixPath(path).parts, 'Unsafe historical file path')
    need(isinstance(size, int) and not isinstance(size, bool) and size >= 0,
         'Invalid historical file size')
    need(isinstance(digest, str) and re.fullmatch(r'[0-9a-f]{64}', digest), 'Invalid SHA256')
    return {'path': path, 'bytes': size, 'sha256': digest}


def same(left, right):
    return isinstance(left, dict) and isinstance(right, dict) and all(
        key in left and key in right and left[key] == right[key] for key in ('bytes', 'sha256'))


def fp(path):
    path = canonical(path, True)
    need(stat.S_ISREG(path.lstat().st_mode), f'Regular input file required: {path}')
    digest, size = hashlib.sha256(), 0
    with path.open('rb') as stream:
        for part in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(part)
            size += len(part)
    return {'path': str(path), 'bytes': size, 'sha256': digest.hexdigest()}


def pinned(path, expected):
    actual = fp(path)
    need(same(actual, expected), f'Missing or changed exact input: {path}')
    return actual


def read(path):
    return json.loads(canonical(path, True).read_text())


def write_new(stage, path, value):
    path = within(stage, path)
    within(stage, path.parent).mkdir(parents=True, exist_ok=True)
    within(stage, path)
    with path.open('x') as stream:
        json.dump(value, stream, indent=2)
        stream.write('\n')


def row001_body_allowed(original):
    """Permit its independently supplied cache/source only, never receipt bodies."""
    path = PurePosixPath(original)
    if not path.is_relative_to(ROW001_ORIGIN):
        return True
    relative = path.relative_to(ROW001_ORIGIN)
    base = ROW001.replace('.', '/')
    return str(relative) in {'project/' + base + '.lean', 'objects/' + base + '.olean',
                            'objects/' + base + '.olean.server',
                            'objects/' + base + '.olean.private', 'objects/' + base + '.ir'}


class Frozen:
    def __init__(self):
        self.files = {}

    def add(self, path, expected=None):
        actual = pinned(path, expected) if expected is not None else fp(path)
        previous = self.files.setdefault(actual['path'], actual)
        need(previous == actual, f'Conflicting frozen current input: {path}')
        return actual

    def check(self):
        for path, expected in self.files.items():
            pinned(path, expected)


class EvidenceStore:
    """Resolve (original path, size, SHA) to an explicitly registered P1 file.

    The raw historical JSON is never rewritten and there is no automatic
    fallback to an old path. Same names from distinct historical revisions
    can only resolve through their own complete byte identities.
    """
    def __init__(self, stage, read_roots, frozen=None):
        self.stage = canonical(stage)
        self.read_roots = [canonical(root, True) for root in read_roots]
        need(self.read_roots and all(root.is_dir() for root in self.read_roots), 'Missing read roots')
        for root in self.read_roots:
            disjoint(self.stage, root)
        self.frozen = frozen or Frozen()
        self.bindings = {}
        self.capsule_pins = []

    def allowed_current(self, path):
        path = canonical(path, True)
        need(any(path.is_relative_to(root) for root in self.read_roots),
             f'Current evidence provider outside frozen read roots: {path}')
        return path

    def register(self, original, current):
        original = identity(original)
        need(row001_body_allowed(original['path']),
             'ROW001_REMOTE_ONLY: local reconstruction of original receipt/evidence bodies is forbidden')
        current = self.allowed_current(current)
        actual = self.frozen.add(current, original)
        key = tuple(original[k] for k in ('path', 'bytes', 'sha256'))
        previous = self.bindings.setdefault(key, str(current))
        need(previous == str(current), 'Ambiguous relocated evidence identity')
        return actual

    def resolve(self, original):
        original = identity(original)
        need(row001_body_allowed(original['path']), 'ROW001_REMOTE_ONLY: full body resolution is forbidden')
        key = tuple(original[k] for k in ('path', 'bytes', 'sha256'))
        need(key in self.bindings, f'UNRESOLVED_ORIGINAL_EVIDENCE: {original["path"]}')
        current = self.allowed_current(self.bindings[key])
        self.frozen.add(current, original)
        return current

    def json(self, original):
        return read(self.resolve(original))

    def text(self, original):
        return self.resolve(original).read_text()

    def add_selected_capsule(self, root, manifest_pin):
        root = self.allowed_current(root)
        need(root.is_dir(), 'Capsule extraction root is not a directory')
        manifest_path = self.allowed_current(manifest_pin['path'])
        self.frozen.add(manifest_path, manifest_pin)
        manifest = read(manifest_path)
        need(manifest['schema'] == 'p26_cell01_selected_rows_cloud_export_v1',
             'Unsupported selected-row capsule schema')
        members = manifest['members']
        seen = set()
        for row in members:
            relative = PurePosixPath(row['member'])
            need(row['member'] and not relative.is_absolute() and '..' not in relative.parts and
                 row['member'] not in seen, 'Unsafe or duplicate capsule member')
            seen.add(row['member'])
            current = within(root, root / row['member'], True)
            self.frozen.add(current, row)
            if 'path' in row:
                self.register(row, current)
        actual = set()
        for path in root.rglob('*'):
            canonical(path, True)
            if path.is_file():
                actual.add(str(path.relative_to(root)))
        allowed = seen | {str(manifest_path.relative_to(root))} if manifest_path.is_relative_to(root) else seen
        need(actual == allowed, 'Capsule extraction has missing or unmanifested bodies')
        self.capsule_pins.append(fp(manifest_path))
        return manifest


def verify_row001_remote(record, expected_source, current_object, current_sidecars,
                         current_checker, store):
    """Validate a compact remote-attestation boundary; do not read remote bodies."""
    need(record['mode'] == 'remote_verified_predecessor' and record['module'] == ROW001,
         'Remote-only exception is restricted to original row001')
    need(expected_source['bytes'] == 71505 and expected_source['sha256'] == ROW001_SOURCE_SHA and
         current_object['sha256'] == ROW001_OBJECT_SHA, 'Row001 source/object differs from accepted identity')
    summary = store.json(record['summary'])
    mcp = store.json(record['mcp_task'])
    script = store.resolve(record['review_script'])
    need(summary['schema'] == 'p26_row001_remote_predecessor_join_v2' and summary['status'] == 'PASS',
         'A complete current remote-join summary is required; the historical summary alone is insufficient')
    need(mcp['status'] == 'succeeded' and mcp['exit_code'] == 0 and mcp['output_truncated'] is False,
         'Remote verification MCP task was not successfully completed')
    need(summary['task_id'] == mcp['task_id'] == record['task_id'] and
         summary['project_id'] == mcp['project_id'] == record['project_id'],
         'Remote task/project locator is not bound to the actual MCP task')
    need(summary['review_script'] == record['review_script'] and
         same(fp(script), record['review_script']) and summary['recorded_command'] == mcp['command'],
         'Remote verification command/script binding differs')
    need(summary['module'] == ROW001 and same(summary['source'], expected_source) and
         same(summary['object'], current_object), 'Remote verified source/object does not match P1 imports')
    need([{k: ref[k] for k in ('bytes', 'sha256')} for ref in summary['object_sidecars']] ==
         [{k: ref[k] for k in ('bytes', 'sha256')} for ref in current_sidecars],
         'Remote verified object sidecars differ')
    need(same(summary['stock_checker_binary'], current_checker), 'Remote stock checker bytes differ')
    chains = summary['chains']
    need(list(chains) == list(MODES), 'Remote summary does not identify all three ordered chains')
    locators = []
    for mode in MODES:
        chain = chains[mode]
        need(chain['mode'] == mode and chain['status'] == 'PASS_EXACT_CHAIN' and
             chain['module'] == ROW001 and same(chain['source'], expected_source) and
             same(chain['object'], current_object), 'Incomplete remote chain identity')
        for key in ('receipt', 'command', 'result', 'log'):
            ref = identity(chain[key])
            need(PurePosixPath(ref['path']).is_relative_to(ROW001_ORIGIN), 'Remote evidence locator escapes original row001 stage')
            locators.append({'mode': mode, 'kind': key, **ref})
    owned = summary['full_owned']
    need(owned['serialized_equals_environment'] is True and owned['complete_types'] is True and
         owned['all_transitive_axioms_checked'] is True and owned['declaration_count'] == 292 and
         set(owned['axioms_union']) <= ALLOWED_AXIOMS and owned['unsafe_partial_new_axiom_count'] == 0,
         'Remote complete owned inventory/type/axiom check is incomplete')
    supplier = summary['supplier_closure']
    need(supplier['modules'] == 399 and supplier['source_object_pairs_verified'] == 798 and
         supplier['historical_pending_preserved'] is True and
         supplier['same_byte_kernel_addendum_verified'] is True and supplier['fully_kernel_closed'] is True,
         'Remote original supplier closure is incomplete')
    need(summary['live_source_object_same_bytes'] is True and summary['read_only'] is True and
         summary['Lean_commands'] == 0 and summary['raw_evidence_transferred'] is False,
         'Remote attestation scope or live-byte check differs')
    need(re.fullmatch(r'[0-9a-f]{64}', summary['runtime_import_inventory_sha256']) and
         summary['runtime_binary_hashes_verified'] is True, 'Remote runtime/import context unbound')
    return {'module': ROW001, 'status': 'ACCEPTED_BY_EXACT_REMOTE_IN_PLACE_VERIFICATION',
            'source': expected_source, 'object': current_object, 'object_sidecars': current_sidecars,
            'summary': record['summary'], 'mcp_task': record['mcp_task'],
            'review_script': record['review_script'], 'remote_locators': locators,
            'receipt_bodies_checked_locally': False, 'receipt_bodies_checked_on_P3': True,
            'full_owned_declarations': 292,
            'runtime_import_inventory_sha256': summary['runtime_import_inventory_sha256']}
