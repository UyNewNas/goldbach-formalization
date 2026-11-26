#!/usr/bin/env python3
"""Install exact frozen candidate bytes from a Git checkout and prior metadata.

This performs no Lean-source generation, proof execution, Git operation or
network transfer. Different existing destination bytes are never overwritten.
"""
from pathlib import Path
import argparse
import hashlib
import json


def fp(path):
    raw = path.read_bytes()
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def canonical_path(path):
    path = Path(path).absolute()
    if '..' in path.parts or path.is_symlink() or path.resolve() != path:
        raise ValueError(('Noncanonical or symlinked path', str(path)))
    return path


def stage_path(stage, path):
    stage, path = canonical_path(stage), canonical_path(path)
    if not path.is_relative_to(stage):
        raise ValueError(('Write target escapes stage', str(path), str(stage)))
    return path


def stage_mkdir(stage, path, *, exist_ok):
    path = stage_path(stage, path)
    path.mkdir(parents=True, exist_ok=exist_ok)
    stage_path(stage, path)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', type=Path, default=Path(__file__).resolve().parents[3])
    ap.add_argument('--stage', type=Path, default=Path('/workspace/p26-continuation-59264dd64286/cell01-rest-finite'))
    ap.add_argument('--base-stage', type=Path, default=Path('/workspace/p26-continuation-59264dd64286/cell01-row001-finite'))
    ap.add_argument('--check-only', action='store_true')
    args = ap.parse_args()
    repo, stage, base = map(canonical_path, (args.repo, args.stage, args.base_stage))
    plan = json.loads((repo / 'tools/p26/cell01-rest/STAGING_PLAN.json').read_text())
    assert plan['new_proof_owners'] == 142 and plan['supplier_objects_included'] is False
    for root in (repo, base):
        if stage.is_relative_to(root) or root.is_relative_to(stage):
            raise ValueError(('Stage and input roots must be disjoint', str(stage), str(root)))
    validated = []
    for row in plan['files']:
        relative, member = Path(row['relative_source']), Path(row['archive_member'])
        assert not relative.is_absolute() and '..' not in relative.parts
        assert not member.is_absolute() and '..' not in member.parts
        root = repo if row['origin'] == 'repo' else base
        assert row['origin'] in {'repo', 'base-stage'}
        source, destination = root / relative, stage_path(stage, stage / member)
        assert source.is_file() and source.resolve() == source
        assert fp(source) == {key: row[key] for key in ('bytes', 'sha256')}
        if destination.exists():
            assert destination.is_file() and destination.resolve() == destination
            assert fp(destination) == fp(source), ('Refusing destination overwrite', str(destination))
        validated.append((source, destination, row))
    if not args.check_only:
        for source, destination, row in validated:
            stage_path(stage, destination)
            assert source.is_file() and source.resolve() == source
            assert fp(source) == {key: row[key] for key in ('bytes', 'sha256')}
            if not destination.exists():
                stage_mkdir(stage, destination.parent, exist_ok=True)
                stage_path(stage, destination)
                with destination.open('xb') as output:
                    output.write(source.read_bytes())
            assert fp(destination) == {key: row[key] for key in ('bytes', 'sha256')}
    print(json.dumps({'status': 'CHECKED' if args.check_only else 'STAGED_EXACT_BYTES',
                      'stage': str(stage), 'files': len(validated), 'new_owners': 142,
                      'source_generation': False, 'Lean_invoked': False}), flush=True)


if __name__ == '__main__':
    main()
