#!/usr/bin/env python3
"""Install the frozen source package by exact bytes, retain its join, then run new steps."""
from pathlib import Path, PurePosixPath
import argparse
import json
import os
import sys

sys.dont_write_bytecode = True
from boundary import BOUNDARY, TARGET
from receipt_checks import TOOL_REL, canonical, disjoint, fp, read, require, same, tree_files


def install_package(package, stage):
    package, stage = canonical(package, True), canonical(stage)
    disjoint(package, stage)
    for root in (BOUNDARY['original_stage'], BOUNDARY['original_fields_stage'],
                 str(Path(BOUNDARY['supplier_project']).parent)):
        disjoint(stage, canonical(root, True))
        disjoint(package, canonical(root, True))
    manifest_pin = fp(package / 'PACKAGE_CONTENTS.json')
    stage_manifest = canonical(stage / 'PACKAGE_CONTENTS.json')
    if stage_manifest.exists():
        require(same(fp(stage_manifest), manifest_pin), 'Stage is bound to another frozen package')
    manifest = read(package / 'PACKAGE_CONTENTS.json')
    require(manifest['schema'] == 'cell05_shape_repair_source_package_v1' and
            manifest['target_count'] == 1 and manifest['planned_new_steps'] == 3 and
            manifest['accepted_steps'] == 0 and manifest['repair_source_ready'] is True, 'Wrong frozen source-only package scope')
    expected = {}
    for row in manifest['members']:
        name = row['member']
        relative = PurePosixPath(name)
        require(name and not relative.is_absolute() and '..' not in relative.parts and
                str(relative) == name and name not in expected, 'Unsafe or duplicate package member')
        require(name.startswith('sources/ImbalancedChen/') or name.startswith(str(TOOL_REL) + '/'),
                'Package member is outside the exact source/tool roots')
        require(not name.endswith('.olean'), 'Source deployment cannot contain supplier/new object bodies')
        source, destination = package / name, canonical(stage / name)
        require(same(fp(source), row), f'Package input differs: {source}')
        if destination.exists():
            require(same(fp(destination), row), f'Refusing to replace a different stage file: {destination}')
        expected[name] = (source, destination, row)
    require({name for name in expected if name.startswith('sources/')} ==
            {'sources/' + TARGET.replace('.', '/') + '.lean'}, 'Package must contain only the fixed ShapeArrays source')
    tree_files(package, set(expected) | {'PACKAGE_CONTENTS.json'})
    for source, destination, row in expected.values():
        destination.parent.mkdir(parents=True, exist_ok=True)
        canonical(destination.parent, True)
        if not destination.exists():
            os.link(source, destination)
        require(same(fp(destination), row), f'Installed package bytes differ: {destination}')
    require(fp(package / 'PACKAGE_CONTENTS.json') == manifest_pin, 'Package manifest changed while installing')
    if not stage_manifest.exists():
        os.link(package / 'PACKAGE_CONTENTS.json', stage_manifest)
    require(same(fp(stage_manifest), manifest_pin), 'Installed package manifest differs')
    return stage / TOOL_REL


def main():
    require(sys.flags.optimize == 0, 'Run without Python optimization')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--stage', type=Path, required=True)
    parser.add_argument('--attempt', required=True)
    parser.add_argument('--rss-gib', type=int, default=6)
    parser.add_argument('--wall-seconds', type=int, default=900)
    parser.add_argument('--max-new-steps', type=int)
    parser.add_argument('--preflight-only', action='store_true')
    args = parser.parse_args()
    package = Path(__file__).absolute().parents[3]
    here = install_package(package, args.stage)
    argv = [sys.executable, '-B', str(here / 'verify_shape.py'), '--stage', str(args.stage),
            '--attempt', args.attempt, '--rss-gib', str(args.rss_gib), '--wall-seconds', str(args.wall_seconds)]
    if args.max_new_steps is not None:
        argv += ['--max-new-steps', str(args.max_new_steps)]
    if args.preflight_only:
        argv.append('--preflight-only')
    os.execv(sys.executable, argv)


if __name__ == '__main__':
    main()
