"""CI-only strict one-module preflight; full102 acceptance remains mandatory.

This program must not be run locally. It parses the actual original exporter
output and binds the unchanged target object on both sides of that export.
It does not replace the later complete closure kernel replay or type audit.
"""
from __future__ import annotations

from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
MODULE = 'ImbalancedChen.FinitePiIntegral'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inventory(log: Path) -> dict:
    lines = log.read_text().splitlines()
    def records(prefix: str) -> list:
        return [json.loads(line[len(prefix):]) for line in lines if line.startswith(prefix)]
    assert not any(line.startswith('P0_ROUND6_INVENTORY_MISMATCH ') for line in lines)
    serialized = records('P0_ROUND6_SERIALIZED ')
    declarations = records('P0_ROUND6_DECL ')
    counts = records('P0_ROUND6_MODULE ')
    totals = [int(line.removeprefix('P0_ROUND6_COUNT ')) for line in lines
              if line.startswith('P0_ROUND6_COUNT ')]
    assert len(serialized) == 1 and serialized[0]['module'] == MODULE
    row = serialized[0]
    assert row['is_module'] is False and row['import_all'] is True and row['has_data'] is True
    names = row['serialized_constant_names']
    owned = row['environment_constant_names']
    assert isinstance(names, list) and names and all(isinstance(n, str) and n for n in names)
    assert isinstance(owned, list) and all(isinstance(n, str) and n for n in owned)
    assert Counter(names) == Counter(owned)
    assert row['serialized_constant_count'] == len(names)
    assert all(n == 1 for n in Counter(names).values()), 'Duplicate serialized declaration'
    assert Counter(d['name'] for d in declarations) == Counter(names)
    assert len(declarations) == len(names)
    for declaration in declarations:
        assert declaration['module'] == MODULE
        assert all(declaration[key] is False for key in ['is_unsafe', 'is_partial', 'is_axiom'])
        assert isinstance(declaration['axioms'], list) and set(declaration['axioms']) <= ALLOWED
        for key in ['type', 'readable_type']:
            value = declaration[key]
            assert isinstance(value, str) and value.strip() and '⋯' not in value
    assert counts == [{'module': MODULE, 'count': len(names)}]
    assert totals == [len(names)]
    assert lines.count('P0_ROUND6_PHASE serialized_inventory_exact_match') == 1
    return {'module': MODULE, 'serialized_declarations': len(names),
            'complete_full_types': len(declarations), 'complete_readable_types': len(declarations),
            'transitive_axiom_records': len(declarations), 'allowed_axioms': sorted(ALLOWED),
            'owned_serialized_multiplicities_exact': True}


def inputs(manifest: dict, project: Path, logs: Path) -> dict:
    source = next(row for row in manifest['modules'] if row['module'] == MODULE)
    installed = project / source['install_path']
    data = installed.read_bytes()
    assert len(data) == source['bytes'] and sha(installed) == source['sha256']
    assert hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == source['git_blob']
    object_path = project / '.lake/build/lib/lean/ImbalancedChen/FinitePiIntegral.olean'
    assert object_path.is_file()
    for name in ['CandidateAudit.lean', 'FinitePiPilot.lean']:
        assert (project / name).read_bytes() == (logs / name).read_bytes()
    return {'module': MODULE, 'source': source,
            'object_path': object_path.relative_to(project).as_posix(), 'object_sha256': sha(object_path),
            'full_audit_sha256': sha(project / 'CandidateAudit.lean'),
            'pilot_audit_sha256': sha(project / 'FinitePiPilot.lean'),
            'diagnostic_template_sha256': sha(HERE / manifest['diagnostic_template']['path']),
            'manifest_sha256': sha(HERE / 'P2_VALIDATION_MANIFEST.json'),
            'bundle_registry_sha256': sha(HERE / 'REGISTRY.json'),
            'driver_binding_sha256': sha(logs / 'DRIVER_BINDING.json'),
            'build_log_sha256': sha(logs / 'finitepi-build.log'),
            'driver_commit': os.environ['GITHUB_SHA'], 'run_id': os.environ['GITHUB_RUN_ID'],
            'run_attempt': os.environ['GITHUB_RUN_ATTEMPT'], 'job': os.environ['GITHUB_JOB']}


def expected_receipt(manifest: dict, project: Path, logs: Path) -> dict:
    before = logs / 'FINITEPI_PILOT_BEFORE.json'
    bound = inputs(manifest, project, logs)
    assert json.loads(before.read_text()) == bound, 'Pilot source/object/configuration changed'
    return {'status': 'PASS_STRICT_SINGLE_MODULE_PREFLIGHT_ONLY', 'inputs': bound,
            'before_sha256': sha(before), 'types_log_sha256': sha(logs / 'finitepi-types.log'),
            'inventory': inventory(logs / 'finitepi-types.log'),
            'whole_p2_accepted': False, 'whole_p4_accepted': False,
            'full102_kernel_types_axioms_and_final_gate_still_required': True}


def validate_receipt(manifest: dict, project: Path, logs: Path) -> dict:
    expected = expected_receipt(manifest, project, logs)
    assert json.loads((logs / 'FINITEPI_PILOT_ACCEPTANCE.json').read_text()) == expected
    return expected


def main() -> None:
    assert os.environ.get('GITHUB_ACTIONS') == 'true', 'Root-authorized CI only; never execute locally'
    from p2_validation import load_bound_bundle
    manifest, binding = load_bound_bundle()
    project, logs = Path(os.environ['PROJECT']), Path(os.environ['LOGS'])
    assert json.loads((logs / 'DRIVER_BINDING.json').read_text()) == binding
    mode = sys.argv[1]
    if mode == 'before':
        path = logs / 'FINITEPI_PILOT_BEFORE.json'
        assert not path.exists()
        path.write_text(json.dumps(inputs(manifest, project, logs), indent=2) + '\n')
    elif mode == 'verify':
        receipt = expected_receipt(manifest, project, logs)
        (logs / 'FINITEPI_PILOT_ACCEPTANCE.json').write_text(json.dumps(receipt, indent=2) + '\n')
    elif mode == 'require':
        validate_receipt(manifest, project, logs)
    else:
        raise SystemExit('Unknown pilot mode')


if __name__ == '__main__':
    main()
