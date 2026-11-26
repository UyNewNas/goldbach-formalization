#!/usr/bin/env python3
"""Install the frozen source package by exact bytes, retain its join, then run new steps."""
from pathlib import Path, PurePosixPath
import argparse
import json
import os
import sys

sys.dont_write_bytecode = True
from receipt_checks import TOOL_REL, canonical, disjoint, fp, read, require, same, tree_files


def install_package(package, stage):
    package, stage = canonical(package, True), canonical(stage)
    disjoint(package, stage)
    manifest_pin = fp(package / 'PACKAGE_CONTENTS.json')
    stage_manifest = canonical(stage / 'PACKAGE_CONTENTS.json')
    if stage_manifest.exists():
        require(same(fp(stage_manifest), manifest_pin), 'Stage is bound to another frozen package')
    manifest = read(package / 'PACKAGE_CONTENTS.json')
    require(manifest['schema'] == 'cell05_connections14_source_package_v1' and
            manifest['target_count'] == 14 and manifest['planned_new_steps'] == 42 and
            manifest['accepted_steps'] == 0, 'Wrong frozen source-only package scope')
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
    tree_files(package, set(expected) | {'PACKAGE_CONTENTS.json'})
    if (stage / 'verification').exists():
        require((stage / TOOL_REL / 'SUPPLIER_JOIN.json').exists(),
                'Historical attempts exist but their immutable join is missing; exact recovery required')
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
    parser.add_argument('--provider', type=Path, required=True)
    parser.add_argument('--attempt', required=True)
    parser.add_argument('--rss-gib', type=int, default=6)
    parser.add_argument('--wall-seconds', type=int, default=900)
    parser.add_argument('--max-new-steps', type=int)
    parser.add_argument('--preflight-only', action='store_true')
    args = parser.parse_args()
    package = Path(__file__).absolute().parents[3]
    disjoint(canonical(package, True), canonical(args.provider))
    disjoint(canonical(args.stage), canonical(args.provider))
    here = install_package(package, args.stage)
    # The join CLI validates an existing guard and never recaptures it on resume.
    import subprocess
    subprocess.run([sys.executable, '-B', str(here / 'fields_only_join.py'), '--provider', str(args.provider)], check=True)
    argv = [sys.executable, '-B', str(here / 'verify_connections14.py'), '--stage', str(args.stage),
            '--attempt', args.attempt, '--rss-gib', str(args.rss_gib), '--wall-seconds', str(args.wall_seconds)]
    if args.max_new_steps is not None:
        argv += ['--max-new-steps', str(args.max_new_steps)]
    if args.preflight_only:
        argv.append('--preflight-only')
    os.execv(sys.executable, argv)


if __name__ == '__main__':
    main()
