#!/usr/bin/env python3
"""Read-only revalidation of the published row000 original-floor artifact.

No Lean command is invoked. The archive stays immutable; stdout is a short
verification report. Supplier object bodies are deliberately absent, so this
check validates preserved evidence, not the current remote supplier filesystem.
"""
import hashlib
import importlib.util
import json
from pathlib import Path, PurePosixPath
import tarfile


def main():
    repo = Path(__file__).resolve().parents[2]
    folder = repo / 'docs/verification/20261126-p26/cell01-row000-original-floor'
    archive = folder / 'evidence.tar.xz'
    manifest_bytes = (folder / 'EXPORT_MANIFEST.json').read_bytes()
    assert hashlib.sha256(archive.read_bytes()).hexdigest() == '1b88f393c1ccb1e9cd3c9804e86277ab9089badcd7b68b3f417cf74b6a02cea7'
    assert hashlib.sha256(manifest_bytes).hexdigest() == '43b345b5477dbd8a7ef4fef44f55e4815415db375160e355a53f02ae60e29567'
    manifest = json.loads(manifest_bytes)
    listed = {row['archive_member']: row for row in manifest['files']}
    assert len(listed) == len(manifest['files']) == 417
    with tarfile.open(archive) as tar:
        members = tar.getmembers()
        assert len(members) == len({m.name for m in members}) == 418
        assert {m.name for m in members} == set(listed) | {'CELL01_ORIGINAL_FLOOR_EXPORT_MANIFEST.json'}
        contents = {}
        for member in members:
            path = PurePosixPath(member.name)
            assert member.isfile() and not path.is_absolute() and '..' not in path.parts
            data = tar.extractfile(member).read()
            contents[member.name] = data
            if member.name in listed:
                row = listed[member.name]
                assert len(data) == row['bytes'] and hashlib.sha256(data).hexdigest() == row['sha256']
        assert contents['CELL01_ORIGINAL_FLOOR_EXPORT_MANIFEST.json'] == manifest_bytes

    def read_pin(pin):
        if 'archive_member' in pin:
            choices = [pin['archive_member']]
        else:
            choices = [name for name, row in listed.items()
                       if row['path'] == pin['path'] and row['sha256'] == pin['sha256']]
        assert len(choices) == 1, ('ambiguous or missing evidence', pin)
        data = contents[choices[0]]
        assert len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256']
        return data

    def read_json(pin):
        return json.loads(read_pin(pin))

    owner = manifest['owner']
    module = owner['module']
    source, obj = read_pin(owner['source']), read_pin(owner['object'])
    assert hashlib.sha256(source).hexdigest() == '044746b6376ae5efdac05dd97b77ba9840c91435001acf3e7a402015b272ede8'
    assert (repo / (module.replace('.', '/') + '.lean')).read_bytes() == source
    assert [name for name in listed if name.endswith('.olean')] == [owner['object']['archive_member']]
    receipts, modes = [], {}
    for mode in ('normal', 'kernel', 'owned'):
        receipt = read_json(owner['steps'][mode])
        assert receipt['module'] == module and receipt['mode'] == mode
        assert receipt['status'] == 'succeeded' and receipt['all_frozen_inputs_unchanged']
        assert read_pin(receipt['source']) == source and read_pin(receipt['object']) == obj
        context = read_json(receipt['context'])
        result = read_json(receipt['command_result'])
        command = read_json(result['command'])
        assert all(result[key] == value for key, value in command.items())
        assert result['module'] == module and result['mode'] == mode
        assert result['status'] == 'succeeded' and result['exit_code'] == 0
        assert not result['timed_out'] and result['error'] is None
        assert result['cwd'] == context['project'] and result['LEAN_PATH'] == context['LEAN_PATH']
        assert result['source'] == receipt['source'] and result['log'] == receipt['log']
        read_pin(result['input_fingerprints'])
        log = read_pin(receipt['log']).decode()
        if mode == 'normal':
            assert result['object_before'] is None
            assert result['argv'][0] == context['lean_binary']['path']
            assert result['argv'][-3:] == ['-o', receipt['object']['path'], module.replace('.', '/') + '.lean']
        elif mode == 'kernel':
            assert result['object_before'] == receipt['object']
            assert result['argv'] == [context['leanchecker_binary']['path'], '--verbose', module]
        else:
            assert result['object_before'] == receipt['object']
            assert result['audit_source'] == receipt['audit_source']
            assert result['argv'][0] == context['lean_binary']['path']
            assert result['argv'][-1] == receipt['audit_source']['path']
            assert read_pin(receipt['audit_source']) == read_pin(owner['audit'])
            helper_path = repo / 'tools/p26/export_cell01_row000.py'
            assert hashlib.sha256(helper_path.read_bytes()).hexdigest() == '4113667629d137e0f47b73b4551710380fb5a9c123a21b9853f352ae62869c07'
            spec = importlib.util.spec_from_file_location('p26_owned_parser', helper_path)
            helper = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(helper)
            parsed = helper.parse_owned(log, module)
            assert parsed == read_json(receipt['owned_declarations'])
            assert parsed['owned_declaration_count'] == owner['owned_declaration_count'] == 10
            assert parsed['axioms_union'] == ['Classical.choice', 'Quot.sound', 'propext']
        receipts.append(receipt)
        modes[mode] = {'receipt_sha256': owner['steps'][mode]['sha256'], 'exit_code': 0}
    assert all(r['context'] == receipts[0]['context'] for r in receipts)
    assert all(r['object'] == receipts[0]['object'] for r in receipts)
    assert manifest['prior_accepted_proof_chain_count'] == 71
    assert not manifest['P2_6_complete_claimed'] and not manifest['Lean_invoked_by_exporter']
    print(json.dumps({'schema': 'p26_published_original_floor_recovery_review_v1',
        'status': 'PASS', 'archive_members_verified': 418, 'listed_members_verified': 417,
        'new_step_chains_verified': modes, 'new_owner_objects': 1,
        'full_owned_declarations': 10, 'full_types_and_transitive_axioms': True,
        'axioms_union': parsed['axioms_union'], 'source_recovered_byte_identically': True,
        'old_supplier_object_bodies_included': False,
        'live_supplier_files_rechecked_in_this_local_review': False,
        'prior_evidence_members_rehashed': True, 'Lean_commands_executed': 0,
        'source_comment_historical_candidate_status_preserved': True,
        'cell': 1, 'original_floor_rows': [0], 'P2_6_complete': False}, indent=2))


if __name__ == '__main__':
    main()
