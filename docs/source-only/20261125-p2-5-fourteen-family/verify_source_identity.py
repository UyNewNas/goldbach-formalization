#!/usr/bin/env python3
"""Verify the finite extraction's source evidence, without invoking Lean or Lake."""

from pathlib import Path
import hashlib
import json
import re
import subprocess


PACKAGE = Path(__file__).resolve().parent
ROOT = PACKAGE.parents[2]


def sha(data):
    return hashlib.sha256(data).hexdigest()


def blob(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def read_json(name):
    return json.loads((PACKAGE / name).read_bytes())


def code_mask(text):
    """Mask comments, strings and quoted identifiers, retaining source positions."""
    result = list(text)
    at = 0
    while at < len(text):
        stop = None
        if text.startswith('--', at):
            stop = text.find('\n', at)
            if stop < 0:
                stop = len(text)
        elif text.startswith('/-', at):
            level, pos = 1, at + 2
            while level:
                assert pos < len(text), 'unclosed comment'
                if text.startswith('/-', pos):
                    level += 1
                    pos += 2
                elif text.startswith('-/', pos):
                    level -= 1
                    pos += 2
                else:
                    pos += 1
            stop = pos
        elif text[at] == '"':
            pos = at + 1
            while pos < len(text):
                if text[pos] == '\\':
                    pos += 2
                elif text[pos] == '"':
                    pos += 1
                    break
                else:
                    pos += 1
            stop = pos
        elif text[at] == '«':
            stop = text.find('»', at + 1) + 1
            assert stop > 0, 'unclosed quoted identifier'
        if stop is None:
            at += 1
        else:
            for pos in range(at, stop):
                if result[pos] not in '\r\n':
                    result[pos] = ' '
            at = stop
    return ''.join(result)


def quote_universe(data):
    text = data.decode()
    matches = list(re.finditer(r'(?<![\w.])universe(?!\w)', code_mask(text)))
    for match in reversed(matches):
        a, b = match.span()
        text = text[:a] + '«universe»' + text[b:]
    return text.encode()


def imports(data):
    return [token for match in re.finditer(r'^import\s+([^\r\n]+)', code_mask(data.decode()), re.M)
            for token in match.group(1).split()]


def declaration_names(data):
    names, scope = [], []
    for line in code_mask(data.decode()).splitlines():
        match = re.match(r'^namespace ([\w.]+)\s*$', line)
        if match:
            current = '.'.join(value for kind, value in scope if kind == 'namespace')
            name = match.group(1)
            # All extraction files use root namespaces. Relative namespace
            # segments in dependencies are accumulated for conflict checking.
            if name.startswith('_root_.'):
                name = name[len('_root_.'):]
                assert not current
            scope.append(('namespace', name))
            continue
        if re.match(r'^(?:noncomputable )?section(?:\s|$)', line):
            scope.append(('section', ''))
            continue
        if re.match(r'^end(?:\s|$)', line):
            if scope:
                scope.pop()
            continue
        match = re.match(r'^(private )?(theorem|def|abbrev|inductive|structure) ([A-Za-z_][A-Za-z_0-9]*)\b', line)
        if match:
            namespace = '.'.join(value for kind, value in scope if kind == 'namespace')
            names.append((namespace + '.' + match.group(3), match.group(2), bool(match.group(1))))
    return names


def checked_slice(data, record):
    a, b = record['start'], record['end_exclusive']
    result = data[a:b]
    assert b - a == record['bytes'] == len(result)
    assert sha(result) == record['sha256']
    return result


def parts(command, kind):
    if kind == 'inductive':
        split = command.index(b' where')
    elif b':=' in command:
        split = command.index(b':=')
    else:
        equation = re.search(rb'\r?\n[ \t]*\|', command)
        assert equation
        split = equation.start()
    return command[:split], command[split:]


identity = read_json('FINITE_CORE_DECLARATION_IDENTITY.json')
support = read_json('SUPPORT_SOURCE_SELECTION.json')
closure = read_json('CLOSURE_SELECTION.json')
core = (ROOT / identity['target_path']).read_bytes()
assert sha(core) == identity['target_sha256']
assert blob(core) == identity['target_git_blob_sha1']
assert len(identity['declarations']) == 31
assert declaration_names(core) == [(r['name'], r['kind'], r['visibility'] == 'private')
                                   for r in identity['declarations']]

exact_commands = exact_headers = exact_bodies = quotations = aliases = 0
for item in identity['declarations']:
    pre_record, post_record = item['preimage'], item['postimage']
    pre = (ROOT / pre_record['path']).read_bytes()
    assert sha(pre) == pre_record['source_sha256']
    assert blob(pre) == pre_record['git_blob_sha1']
    pre_block = checked_slice(pre, pre_record['block'])
    post_block = checked_slice(core, post_record['block'])
    transformed = pre_block
    quote_changes = [c for c in item['transformations'] if c['kind'] == 'identifier_quoting']
    for change in reversed(quote_changes):
        a, b = change['preimage_byte_start'], change['preimage_byte_end']
        assert transformed[a:b] == b'universe'
        transformed = transformed[:a] + '«universe»'.encode() + transformed[b:]
    assert transformed == quote_universe(pre_block)
    for change in item['transformations']:
        if change['kind'] == 'deprecated_alias_rename':
            assert item['name'] == 'ImbalancedChen.P4AOriginalFull87StrictActionTrim.mem_trim'
            assert change['before'] == 'mem_setOf_eq' and change['after'] == 'mem_ofPred_eq'
            assert transformed.count(b'mem_setOf_eq') == 1
            transformed = transformed.replace(b'mem_setOf_eq', b'mem_ofPred_eq')
            aliases += 1
        else:
            assert change['kind'] == 'identifier_quoting'
    assert transformed == post_block, item['name']
    pre_command = checked_slice(pre, pre_record['declaration'])
    post_command = checked_slice(core, post_record['declaration'])
    ph, pb = parts(pre_command, item['kind'])
    qh, qb = parts(post_command, item['kind'])
    assert sha(ph) == pre_record['header_sha256'] and sha(pb) == pre_record['body_sha256']
    assert sha(qh) == post_record['header_sha256'] and sha(qb) == post_record['body_sha256']
    assert item['byte_identity'] == {'block': pre_block == post_block,
                                    'declaration': pre_command == post_command,
                                    'header': ph == qh, 'body': pb == qb}
    exact_commands += pre_command == post_command
    exact_headers += ph == qh
    exact_bodies += pb == qb
    quotations += len(quote_changes)

assert (exact_commands, exact_headers, exact_bodies, quotations, aliases) == (18, 29, 19, 14, 1)
private = [r for r in identity['declarations'] if r['visibility'] == 'private']
assert len(private) == 1 and private[0]['short_name'] == 'attach_indicator'
assert private[0]['byte_identity']['declaration']
assert private[0]['private_relocation']['generated_kernel_fullname_preserved'] is False

owner_quote_count = 0
for owner in identity['owners']:
    pre = (ROOT / owner['preimage_path']).read_bytes()
    post = (ROOT / owner['postimage_path']).read_bytes()
    assert sha(pre) == owner['preimage_sha256'] and blob(pre) == owner['preimage_git_blob_sha1']
    assert sha(post) == owner['postimage_sha256'] and blob(post) == owner['postimage_git_blob_sha1']
    assert not (ROOT / (owner['module'].replace('.', '/') + '.lean')).exists()
    transformed = pre
    for removed in sorted(owner['removed_declarations'], key=lambda r: r['preimage_block']['start'], reverse=True):
        checked_slice(pre, removed['preimage_block'])
        record = removed['preimage_block']
        transformed = transformed[:record['start']] + transformed[record['end_exclusive']:]
    newline = b'\r\n' if pre.count(b'\r\n') == pre.count(b'\n') else b'\n'
    transformed = ('import ' + identity['target_module']).encode() + newline + transformed
    if owner['module'] == 'ImbalancedChen.P2Saving16FirstRowCompilerFibre':
        transformed = transformed.replace(b'import ImbalancedChen.P2Saving16Full87SourceBinding',
                                          b'import ImbalancedChen.P2OriginalSaving16Full87SourceBinding')
    transformed = quote_universe(transformed)
    assert transformed == post, owner['module']
    moved = {r['name'] for r in owner['removed_declarations']}
    assert not moved.intersection(name for name, _, _ in declaration_names(post))
    for remaining in owner['remaining_declarations']:
        before = checked_slice(pre, remaining['preimage_declaration'])
        after = checked_slice(post, remaining['postimage_declaration'])
        assert quote_universe(before) == after
        assert (before == after) == remaining['byte_identical']
        owner_quote_count += remaining['identifier_quoting_count']

whole = identity['whole14']
pre = (ROOT / whole['preimage_path']).read_bytes()
post = (ROOT / whole['postimage_path']).read_bytes()
assert sha(pre) == whole['preimage_sha256'] and sha(post) == whole['postimage_sha256']
assert pre.split(b'\n', 1)[1] == post.split(b'\n', 1)[1]
assert imports(post) == [identity['target_module']]
for item in whole['declarations']:
    assert checked_slice(pre, item['preimage_declaration']) == checked_slice(post, item['postimage_declaration'])
assert sum(r['kind'] == 'def' for r in whole['declarations']) == 2
assert sum(r['kind'] == 'theorem' for r in whole['declarations']) == 14

support_aliases = 0
for item in support['support']:
    pre = (ROOT / item['preimage_path']).read_bytes()
    post = (ROOT / item['destination']).read_bytes()
    assert sha(pre) == item['preimage_sha256'] and blob(pre) == item['preimage_git_blob_sha1']
    assert sha(post) == item['postimage_sha256'] and blob(post) == item['postimage_git_blob_sha1']
    if item['transformations']:
        assert item['module'] == 'ImbalancedChen.P4AOriginalFull87HistoryCore'
        assert len(item['transformations']) == 1
        assert pre.count(b'mem_setOf_eq') == 1
        assert pre.replace(b'mem_setOf_eq', b'mem_ofPred_eq') == post
        support_aliases += 1
    else:
        assert pre == post
    historical = item['historical_own_acceptance']
    if historical:
        receipt_bytes = (ROOT / historical['retained_copy']).read_bytes()
        assert sha(receipt_bytes) == historical['sha256']
        receipt = json.loads(receipt_bytes)
        assert receipt['modules'][item['module']] == item['preimage_sha256']
        assert receipt['source_plus_five_outputs'][item['module']] == historical['source_plus_five_outputs']
assert support_aliases == 1

seen, active, cycles, missing = {}, [], [], []


def visit(module):
    if not module.startswith('ImbalancedChen.'):
        return
    if module in active:
        cycles.append(active[active.index(module):] + [module])
        return
    if module in seen:
        return
    path = ROOT / (module.replace('.', '/') + '.lean')
    if not path.exists():
        missing.append(module)
        return
    data = path.read_bytes()
    seen[module] = (sha(data), blob(data), imports(data))
    active.append(module)
    for child in seen[module][2]:
        visit(child)
    active.pop()


visit(closure['root'])
assert len(seen) == closure['module_count'] == 362
assert not missing and not cycles
assert set(seen) == {r['module'] for r in closure['modules']}
for record in closure['modules']:
    assert seen[record['module']] == (record['sha256'], record['git_blob_sha1'], record['imports'])
assert not [m for m in seen if any(s in m for s in ['R17PaidIntegral', 'Original28918', 'Saving16OwnedIntegral'])]
prior = closure['prior_selection']
prior_bytes = (ROOT / prior['path']).read_bytes()
assert sha(prior_bytes) == prior['sha256']
assert json.loads(prior_bytes)['module_count'] == 1688
assert len(closure['protected_current371_hashes']) == 371
for path, expected in closure['protected_current371_hashes'].items():
    assert sha((ROOT / path).read_bytes()) == expected, path

# Check the exact old Git tree without checking out files or reading mutable HEAD.
tree = subprocess.check_output(['git', 'ls-tree', '-r', '-z', identity['baseline']['head'], '--', 'ImbalancedChen'], cwd=ROOT)
baseline = {}
git_eol_normalized_paths = []
git_lfs_resolved_paths = []
git_symlink_sources = []
for entry in tree.split(b'\0'):
    if not entry:
        continue
    metadata, raw_path = entry.split(b'\t', 1)
    mode, kind, expected_blob = metadata.decode().split()
    path = raw_path.decode()
    if not path.endswith('.lean'):
        continue
    assert kind == 'blob'
    data = (ROOT / path).read_bytes()
    if mode == '120000':
        assert (ROOT / path).is_symlink(), path
        target = str((ROOT / path).readlink()).encode()
        assert blob(target) == expected_blob, path
        git_symlink_sources.append(path)
    elif blob(data) != expected_blob:
        if blob(data.replace(b'\r\n', b'\n')) == expected_blob:
            git_eol_normalized_paths.append(path)
        else:
            # Some committed .lean blobs are Git LFS pointers, while the
            # checkout contains their resolved source bytes. Check the pointer
            # hash and size; never replace payload source with pointer text.
            pointer = subprocess.check_output(['git', 'cat-file', 'blob', expected_blob], cwd=ROOT)
            match = re.fullmatch(rb'version https://git-lfs.github.com/spec/v1\noid sha256:([0-9a-f]{64})\nsize ([0-9]+)\n', pointer)
            assert match, path
            assert sha(data) == match.group(1).decode() and len(data) == int(match.group(2)), path
            git_lfs_resolved_paths.append(path)
    baseline[path] = sha(data)
assert len(baseline) == identity['baseline']['production_lean_count'] == 3778
assert sha(json.dumps(baseline, sort_keys=True).encode()) == identity['baseline']['production_path_hash_map_sha256']

public_names = {r['name'] for r in identity['declarations'] if r['visibility'] == 'public'}
owners_by_name = {name: [] for name in public_names}
for module in seen:
    data = (ROOT / (module.replace('.', '/') + '.lean')).read_bytes()
    for name, _, private in declaration_names(data):
        if name in public_names and not private:
            owners_by_name[name].append(module)
assert all(value == [identity['target_module']] for value in owners_by_name.values()), owners_by_name

for path in closure['production_new_files']:
    data = (ROOT / path).read_bytes()
    code = code_mask(data.decode())
    assert not re.search(r'\b(?:sorry|native_decide|unsafe)\b', code), path
    assert not re.search(r'^\s*axiom\b', code, re.M), path
    assert not re.search(r'\bby\s+admit\b|^\s*admit\s*$', code, re.M), path
    assert not re.search(r'set_option\s+(?:warningAsError|linter\.deprecated)\s+false', code), path
    assert quote_universe(data) == data, path

result = {
    'status': 'STATIC_SOURCE_CHECKS_PASS / NOT_COMPILED',
    'baseline': identity['baseline']['head'],
    'core_sha256': identity['target_sha256'],
    'whole14_sha256': whole['postimage_sha256'],
    'core_declarations': 31, 'public_declarations': 30, 'private_relocations': 1,
    'exact_declaration_commands': exact_commands, 'exact_headers': exact_headers,
    'exact_bodies': exact_bodies, 'core_universe_identifier_quotings': quotations,
    'remaining_owner_universe_identifier_quotings': owner_quote_count,
    'core_deprecated_alias_renames': aliases, 'support_deprecated_alias_renames': support_aliases,
    'whole14_definitions': 2, 'whole14_theorem_bodies': 14,
    'whole14_import_only_change_verified': True,
    'source_graph_modules': len(seen), 'missing_project_imports': missing, 'cycles': cycles,
    'seven_heavy_owners_not_installed': True, 'public_moved_names_have_one_production_owner': True,
    'all_preexisting_production_sources_unchanged': len(baseline),
    'baseline_git_text_attribute_eol_normalized_paths': git_eol_normalized_paths,
    'baseline_git_lfs_payloads_verified': git_lfs_resolved_paths,
    'baseline_git_source_symlinks_verified': git_symlink_sources,
    'protected_current371_unchanged': True,
    'placeholder_or_unsafe_proof_syntax_found': False,
    'admit_definition_is_an_existing_admission_predicate': True,
    'lean_executed': False, 'lake_executed': False, 'cloud_job_started': False,
    'git_mutation_performed': False,
}
print(json.dumps(result, ensure_ascii=False, indent=2))
