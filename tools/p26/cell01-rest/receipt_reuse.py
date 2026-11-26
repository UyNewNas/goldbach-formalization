"""Exact AST mirror of the batch receipt validator; no command execution."""
from pathlib import Path
import json
import re
from Geometry01Decoding_verify import ALLOWED, fp, parse_owned, read, same

def validated_receipt(path, module, mode, source, obj, audit, context):
    prior = read(path)
    # A successful normal receipt is a recovery obligation even when later
    # context or evidence checks prevent reuse. Never rebuild its lost object.
    if (mode == 'normal' and prior.get('mode') == 'normal' and
        prior.get('status') == 'succeeded' and prior.get('exit_code') == 0 and
        prior.get('module') == module and same(prior.get('source'), source)):
        if obj is None or not same(prior.get('object'), obj):
            raise RuntimeError('RESTORE_EXACT_ACCEPTED_OBJECT: ' + json.dumps({
                'module': module, 'normal_receipt': str(path),
                'required_object': prior.get('object'), 'live_object': obj,
                'normal_recompilation_allowed': False}, sort_keys=True))
    if (prior.get('status') != 'succeeded' or prior.get('exit_code') != 0 or
        prior.get('module') != module or prior.get('mode') != mode or
        not same(prior.get('source'), source) or not same(prior.get('object'), obj) or
        prior.get('runtime_context_sha256') != context['runtime_context_sha256'] or
        not same(prior.get('supplier_manifest'), context['supplier_manifest']) or
        (mode == 'owned' and not same(prior.get('audit_source'), audit))):
        return None
    assert source['path'] == prior['source']['path'] and obj['path'] == prior['object']['path']
    assert same(fp(source['path']), source) and same(fp(obj['path']), obj)
    old_run = read(Path(path).parent.parent / 'RUN.json')
    assert all(prior.get(key) == value for key, value in old_run.items())
    for key in ('lean_version', 'mathlib_commit', 'lean_binary', 'leanchecker_binary',
                'LEAN_PATH', 'cwd', 'mathlib_package_object_roots', 'required_mathlib_packages'):
        assert prior[key] == context[key], ('Prior runtime context differs', key)
    assert prior['full_supplier_kernel_closed'] is True
    assert prior['cloud_source_generation'] is False and prior['suppliers_recompiled'] is False
    for key in ('command', 'log', 'input_fingerprints', 'supplier_installation'):
        assert same(fp(prior[key]['path']), prior[key]), ('Prior receipt dependency changed', key)
    command = read(prior['command']['path'])
    assert all(prior.get(key) == value for key, value in command.items())
    expected_flags = ['-j1', f"-M{prior['rss_limit_bytes'] // (1024**2)}",
                      '-DmaxRecDepth=1000000', '-DmaxHeartbeats=0']
    if mode == 'normal':
        expected_argv = [prior['lean_binary']['path'], *expected_flags, '-o', obj['path'],
                         str(Path(source['path']).relative_to(Path(prior['cwd'])))]
        assert prior['object_before'] is None
        text = Path(prior['log']['path']).read_text()
        printed = {axiom.strip() for group in re.findall(r'depends on axioms: \[([^\]]*)\]', text)
                   for axiom in group.split(',') if axiom.strip()}
        assert printed <= ALLOWED and sorted(printed) == prior['printed_axioms']
    elif mode == 'kernel':
        expected_argv = [prior['leanchecker_binary']['path'], '--verbose', module]
        assert same(prior['object_before'], obj)
    else:
        assert mode == 'owned' and same(prior['object_before'], obj)
        assert prior['audit_source']['path'] == audit['path'] and same(fp(audit['path']), audit)
        expected_argv = [prior['lean_binary']['path'], *expected_flags, audit['path']]
        assert same(fp(prior['owned_declarations']['path']), prior['owned_declarations'])
        owned = parse_owned(Path(prior['log']['path']).read_text(), module)
        assert owned == read(prior['owned_declarations']['path'])
        assert owned['owned_declaration_count'] == prior['owned_declaration_count']
    assert prior['argv'] == expected_argv, 'Prior command is not the required exact mode'
    return prior
