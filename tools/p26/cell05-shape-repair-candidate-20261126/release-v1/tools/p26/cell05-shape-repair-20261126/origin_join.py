#!/usr/bin/env python3
"""Read the existing P2 fields-only join; never create a provider or runtime guard."""
from pathlib import Path
import sys

sys.dont_write_bytecode = True
from boundary import BOUNDARY, TARGET, TOOL_REL
from receipt_checks import canonical, disjoint, fp, read, require, same
from fields_only_join import validate_join


def validate_origin():
    """The old fourteen-target stage stays byte-for-byte valid and read-only."""
    require(sys.flags.optimize == 0, 'Historical validators require assertions enabled')
    origin = canonical(BOUNDARY['original_stage'], True)
    here = origin / BOUNDARY['original_tool_relative_path']
    package_path, verifier_path = origin / 'PACKAGE_CONTENTS.json', here / 'CONNECTIONS14_VERIFIER.json'
    require(same(fp(package_path), BOUNDARY['original_package_manifest']) and
            same(fp(verifier_path), BOUNDARY['original_verifier']), 'Original frozen package differs')
    verifier = read(verifier_path)
    require(verifier['schema'] == 'cell05_connections14_frozen_verifier_v1' and
            len(verifier['targets']) == 14 and verifier['targets'][-1] == BOUNDARY['original_target'],
            'Original fourteen-owner source boundary differs')
    frozen = [fp(package_path), fp(verifier_path)]
    for row in verifier['workflow_files']:
        path = canonical(here / row['relative_path'], True)
        require(path.is_relative_to(here) and same(fp(path), row), 'Original workflow file changed')
        frozen.append(fp(path))
    for target in verifier['targets']:
        relative = Path(target['module'].replace('.', '/') + '.lean')
        for path in (origin / 'sources' / relative, origin / 'project' / relative):
            require(same(fp(path), target['source']), 'Original accepted context source changed')
            frozen.append(fp(path))
    joined = validate_join(here)
    require(joined['supplier_count'] == 88 and joined['actual_selected_supplier_union'] == 83 and
            joined['old_Lean_commands_executed'] == joined['compatibility_kernel_replays'] == 0,
            'Original fields-only join no longer has its accepted scope')
    require(joined['runtime_guard'] == BOUNDARY['runtime_guard'],
            'Repair must use the exact original guard; recapture or replacement is forbidden')
    for name in ('supplier_project', 'supplier_objects'):
        require(joined[name] == BOUNDARY[name], 'Repair supplier provider changed')
    registry = read(here / 'SUPPLIER_REGISTRY.json')
    suppliers = {row['module']: row for row in registry['suppliers']}
    require(len(suppliers) == 88 and set(BOUNDARY['expected_old_dependency_modules']) <= set(suppliers) and
            TARGET not in suppliers, 'Exact old dependency boundary is unavailable')
    joined = dict(joined)
    joined.update(origin_stage=str(origin), supplier_join=fp(here / 'SUPPLIER_JOIN.json'),
                  registry=registry, actual_repair_supplier_union=42,
                  frozen_evidence=[*joined['frozen_evidence'], *frozen])
    return joined


def require_separate_stage(stage, joined, package=None):
    stage = canonical(stage)
    for root in (joined['origin_stage'], joined['supplier_project'], joined['supplier_objects'],
                 str(Path(joined['supplier_project']).parent), joined['fields_context']['stage']):
        disjoint(stage, canonical(root, True))
    if package is not None:
        disjoint(stage, canonical(package, True))
    require(stage / TOOL_REL != Path(joined['origin_stage']) / BOUNDARY['original_tool_relative_path'],
            'Repair cannot write into the original workflow')
    return stage
