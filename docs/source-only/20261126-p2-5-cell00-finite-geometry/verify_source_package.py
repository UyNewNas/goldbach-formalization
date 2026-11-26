#!/usr/bin/env python3
"""Read-only source/provenance checks. Never runs Lean or awards proof credit."""
import hashlib
import json
import re
from pathlib import Path


PACKAGE = Path(__file__).resolve().parent
ROOT = PACKAGE.parents[2]


def digest(data):
    return hashlib.sha256(data).hexdigest()


def read_json(name):
    return json.loads((PACKAGE / name).read_bytes())


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def check_pin(pin):
    data = (ROOT / pin['path']).read_bytes()
    require(digest(data) == pin['sha256'], 'hash mismatch: ' + pin['path'])
    if 'bytes' in pin:
        require(len(data) == pin['bytes'], 'length mismatch: ' + pin['path'])
    return data


def project_imports(data):
    # splitlines handles the unchanged historical CRLF sources as well as LF.
    return [match.group(1) for line in data.decode().splitlines()
            if (match := re.fullmatch(
                r'[ \t]*import[ \t]+(ImbalancedChen\.[A-Za-z0-9_.]+)[ \t]*', line))]


def closure_modules(graph, root):
    seen = set()

    def visit(module):
        if module in seen:
            return
        seen.add(module)
        for dependency in graph[module]['project_imports']:
            visit(dependency)

    visit(root)
    return seen


def main():
    selection = read_json('SOURCE_SELECTION.json')
    dependencies = read_json('DEPENDENCY_STATUS.json')
    host = read_json('HOST_DIAGNOSTICS.json')
    require(selection['P2_5_proved'] is False, 'source metadata claims P2.5')
    require(host['proof_credit'] is False and host['lean_executed'] is False,
            'host diagnostics promoted to proof')
    require(len(selection['source_candidates']) == 7, 'candidate scope changed')
    require(len(selection['initial_new_or_changed_owners_to_verify']) == 5,
            'initial owner scope changed')
    sources = {}
    preimages = {}
    for row in selection['source_candidates']:
        data = check_pin(row['candidate'])
        sources[row['module']] = data.decode()
        require(project_imports(data) == row['project_imports'],
                'candidate imports changed: ' + row['module'])
        if row['preimage']:
            preimages[row['module']] = check_pin(row['preimage']).decode()
        else:
            require(not (ROOT / row['install_path']).exists(),
                    'new source installed in production during source-only preparation')
        # This lexical check complements review; it is not the future axiom audit.
        uncommented = re.sub(r'/\-.*?\-/', '', data.decode(), flags=re.S)
        uncommented = re.sub(r'--[^\n]*', '', uncommented)
        require(not re.search(r'\b(sorry|admit|native_decide|axiom|unsafe|partial)\b',
                              uncommented), 'forbidden proof escape in ' + row['module'])
    prefix = 'ImbalancedChen.'
    archive_name = prefix + 'P2OriginalSaving16OriginalArchive'
    ownership_name = prefix + 'P2OriginalSaving16PullingOwnership'
    induction_name = prefix + 'P2OriginalSaving16PullingFaceInduction'
    original = preimages[archive_name]
    ownership = preimages[ownership_name]
    blocks = {
        'evalQ': original[original.index('def evalQ ('):original.index('def castPoint (')],
        'interiorCandidate': original[
            original.index('/-- A deterministic rational interior candidate'):
            original.index('theorem original_headers :')],
        'FaceRecord': ownership[
            ownership.index('structure FaceRecord where'):ownership.index('def decodeFace (')],
        'decodeFace': ownership[
            ownership.index('def decodeFace ('):ownership.index('def parsedFaces (')],
    }
    for row in selection['moved_commands']:
        block = blocks[row['name']]
        require(digest(block.encode()) == row['sha256'], 'moved command pin changed')
        target = sources[prefix + ('P2OriginalSaving16FiniteGeometryCore'
                         if row['name'] in ('evalQ', 'interiorCandidate')
                         else 'P2OriginalSaving16FaceDecoderCore')]
        require(target.count(block) == 1, 'moved command not byte-identical')
        require('namespace ' + row['namespace'] + '\n' in target,
                'moved command namespace changed')
    expected_archive = original.replace(
        'import ImbalancedChen.P2OriginalSaving16FiniteArchive\n',
        'import ImbalancedChen.P2OriginalSaving16FiniteArchive\n'
        'import ImbalancedChen.P2OriginalSaving16FiniteGeometryCore\n', 1)
    for name in ('evalQ', 'interiorCandidate'):
        expected_archive = expected_archive.replace(blocks[name], '', 1)
    require(sources[archive_name] == expected_archive,
            'OriginalArchive changed beyond exact relocation/import')
    expected_ownership = ownership.replace(
        'import ImbalancedChen.P2OriginalSaving16PullingFaceInduction\n',
        'import ImbalancedChen.P2OriginalSaving16PullingFaceInduction\n'
        'import ImbalancedChen.P2OriginalSaving16FaceDecoderCore\n', 1)
    expected_ownership = expected_ownership.replace(
        blocks['FaceRecord'] + blocks['decodeFace'], '', 1)
    require(sources[ownership_name] == expected_ownership,
            'PullingOwnership changed beyond exact relocation/import')
    expected_induction = preimages[induction_name].replace(
        'import ImbalancedChen.P2OriginalSaving16OriginalArchive\n',
        'import ImbalancedChen.P2OriginalSaving16FiniteGeometryCore\n', 1)
    require(sources[induction_name] == expected_induction,
            'PullingFaceInduction body or statements changed')
    check_pin(selection['source_only_patch'])
    for pin in selection['prior_receipt_pins']:
        check_pin(pin)
    graph = dependencies['candidate_project_source_closure']
    require(len(graph) == dependencies['candidate_project_closure_count'],
            'closure count changed')
    for module, row in graph.items():
        data = check_pin(row)
        require(project_imports(data) == row['project_imports'],
                'closure imports changed: ' + module)
    literal = dependencies['literal96']
    actual = closure_modules(graph, literal['module'])
    require(actual == set(literal['project_closure_modules']),
            'Literal96 closure changed')
    prior = json.loads(check_pin(literal['pinned_round2_graph']))['modules']
    prior_graph = {module: {'project_imports': [x for x in row['imports']
                    if x.startswith('ImbalancedChen.')]}
                   for module, row in prior.items()}
    require(actual == closure_modules(prior_graph, literal['module']),
            'Literal96 module set differs from pinned prior graph')
    require(literal['owner_row'] == {'accepted': False, 'declarations': 0, 'reused': False},
            'Literal96 blocked status was relabelled')
    for row in dependencies['accepted_suppliers'].values():
        check_pin(row['source'])
        require(row['source']['sha256'] ==
                row['object_from_actual_consumer005']['source_sha256'],
                'supplier source/object mismatch')
    for pin in host['inputs']:
        check_pin(pin)
    patterns = dependencies['existing_patterns_package']
    for key in ('typed', 'original', 'dependency_selection', 'literal42_source',
                'literal42_receipt'):
        check_pin(patterns[key])
    require(patterns['literal42_round4_owner'] ==
            {'accepted': True, 'declarations': 15, 'reused': True},
            'Literal42 owner status changed')
    return {
        'status': 'STATIC_SOURCE_PROVENANCE_CHECKS_PASSED_NOT_LEAN_ACCEPTANCE',
        'source_candidates': len(sources),
        'fresh_or_changed_initial_owners': 5,
        'exact_moved_command_blocks': 4,
        'mechanical_postimages': 3,
        'current_source_closure': len(graph),
        'literal96_project_closure': len(actual),
        'literal96_owner_accepted': False,
        'typed_geometry_closure': len(closure_modules(
            graph, prefix + 'P2Saving16Cell00TypedGeometry')),
        'typed_pulling_closure': len(closure_modules(
            graph, prefix + 'P2Saving16Cell00TypedPulling')),
        'production_preimages_unchanged': True,
        'lean_ast_or_elaboration_executed': False,
        'kernel_or_cloud_executed': False,
        'P2_5_proved': False,
    }


if __name__ == '__main__':
    print(json.dumps(main(), sort_keys=True, indent=2))
