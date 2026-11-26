#!/usr/bin/env python3
"""On P1, revalidate the existing 45 steps and build only a relocatable supplier capsule."""
from pathlib import Path
import argparse
import json
import os
import sys

sys.dont_write_bytecode = True
from evidence_io import canonical, dump_new, fp, member_name, read, require, same
from supplier_capsule import build_row_capsule


def main():
    require(sys.flags.optimize == 0, 'Python optimization would disable inherited owned-inventory assertions')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    here = canonical(Path(os.path.abspath(__file__)).parent, True)
    manifest = read(here / 'CAPSULE_BUILD_MANIFEST.json')
    require(manifest['schema'] == 'cell05_row_capsule_builder_source_package_v1', 'Unknown builder package')
    require(len({row['relative_path'] for row in manifest['files']}) == len(manifest['files']), 'Duplicate builder file pin')
    for row in manifest['files']:
        member_name(row['relative_path'])
        require(same(fp(here / row['relative_path']), row), 'Builder source/metadata differs from its frozen package')
    report_path = canonical(args.output.with_name(args.output.name + '.json'))
    require(not report_path.exists(), 'Refuse existing capsule report')
    report = build_row_capsule(here, args.output)
    dump_new(report_path, report)
    print(json.dumps(report, indent=2), flush=True)


if __name__ == '__main__':
    main()
