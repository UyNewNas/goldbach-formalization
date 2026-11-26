#!/usr/bin/env python3
"""Deploy five exact historical RESULT byte strings from existing tracked xz.

Default is read-only. This is transport/decompression only: no Lean, no receipt
reserialization, no old-path overwrite and no new proof acceptance.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import lzma
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

PACKAGE = 'docs/source-only/20261126-p2-5-cache-rematerialization/'
PREFIX = 'docs/verification/20261126-p2-5-resumed/'
MAX_DECOMPRESSED = 32 * 1024 * 1024
RESERVE = 320 * 1024 * 1024
FIXED_TARGETS = {
    PREFIX+'consumer-attempt004/RESULT.json': (5016911, '2c8f7b252d2e42f8ac09a6be391401258b0ed8fda1da57dd50cc7269f50b193a'),
    PREFIX+'consumer-attempt005/RESULT.json': (5049315, 'bc26ddfa2b6a06ce4935430f6bedaf2419c7a1033723c98efe499f24116fdf88'),
    PREFIX+'field-explicit-attempt005/RESULT.json': (4822231, '812f43171da6572a897020df007846c3dfd4776253c4e851824b91536380f716'),
    PREFIX+'field-final-attempt004/RESULT.json': (4809977, 'c8f52525af889be955ffaa245d40ead84f560fea0de0f04e53ae202afeaab1f2'),
    PREFIX+'field-symbolic-attempt006/RESULT.json': (4867343, '82123af5bc4f1e9334da8f578de11147effe73da0a7ab90b55459abbb25bcb0e'),
}


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha_bytes(data):
    return hashlib.sha256(data).hexdigest()


def sha_file(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def beneath(repo, relative):
    path = Path(relative)
    require(not path.is_absolute() and '..' not in path.parts, 'Invalid relative deployment path')
    return repo / path


def reject_symlinks(path):
    for item in [path, *path.parents]:
        require(not item.is_symlink(), 'Symlink destination/ancestor refused: '+str(item))


def decode_entry(repo, row):
    source = beneath(repo, row['capsule'])
    require(source.is_file() and not source.is_symlink(), 'Capsule is not a regular file')
    require(source.stat().st_size == row['capsule_bytes'] and sha_file(source) == row['capsule_sha256'],
            'Capsule size/SHA mismatch: '+str(source))
    with lzma.open(source, 'rb') as stream:
        raw = stream.read(MAX_DECOMPRESSED + 1)
    require(len(raw) <= MAX_DECOMPRESSED, 'Decompressed capsule exceeds fixed bound')
    if row['format'] == 'raw_xz':
        output = raw
    elif row['format'] == 'xz_evidence_list':
        records = json.loads(raw)
        require(isinstance(records, list), 'Expected actual evidence list')
        matches = [r for r in records if isinstance(r, dict) and r.get('name') == 'RESULT.json']
        require(len(matches) == 1, 'RESULT member is missing or duplicated')
        member = matches[0]
        require(member.get('encoding', 'utf-8') == 'utf-8' and isinstance(member['content'], str),
                'RESULT must be the original UTF-8 content string')
        output = member['content'].encode('utf-8')
        require(member['bytes'] == row['target_bytes'] and member['sha256'] == row['target_sha256'],
                'Capsule RESULT descriptor differs from the frozen original')
    else:
        raise RuntimeError('Unsupported receipt transport format')
    require(len(output) == row['target_bytes'] and sha_bytes(output) == row['target_sha256'],
            'Recovered RESULT bytes differ; no target was written')
    return output


def target_state(target, expected_bytes, expected_sha):
    reject_symlinks(target)
    if not os.path.lexists(target):
        return 'ABSENT'
    require(target.is_file() and target.stat().st_size == expected_bytes and sha_file(target) == expected_sha,
            'Existing RESULT conflicts; never overwrite: '+str(target))
    return 'ALREADY_EXACT'


def install_exclusive(target, data, expected_sha):
    require(sha_bytes(data) == expected_sha, 'Installer input changed')
    if target_state(target, len(data), expected_sha) == 'ALREADY_EXACT':
        return 'ALREADY_EXACT'
    target.parent.mkdir(parents=True, exist_ok=True)
    fd, name = tempfile.mkstemp(prefix='.receipt-bootstrap-', dir=target.parent)
    temporary = Path(name)
    try:
        with os.fdopen(fd, 'wb') as out:
            out.write(data)
            out.flush()
            os.fsync(out.fileno())
        require(sha_file(temporary) == expected_sha, 'Temporary receipt copy differs')
        try:
            os.link(temporary, target, follow_symlinks=False)
            action = 'INSTALLED_EXACT_ORIGINAL_BYTES'
        except FileExistsError:
            require(target_state(target, len(data), expected_sha) == 'ALREADY_EXACT',
                    'Concurrent target creation conflicts')
            action = 'ALREADY_EXACT'
        require(target_state(target, len(data), expected_sha) == 'ALREADY_EXACT', 'Installed bytes differ')
        return action
    finally:
        # Only our exclusive temporary inode is removed, never an old target.
        temporary.unlink(missing_ok=True)


def publication_check(repo, args, rows):
    require(re.fullmatch(r'[0-9a-f]{40}', args.publication or ''), 'Apply needs a full publication commit')
    require(sha_file(__file__) == args.runner_sha, 'Bootstrap runner SHA mismatch')
    def git(*items):
        return subprocess.check_output(['git', *items], cwd=repo, timeout=120)
    require(git('rev-parse', 'HEAD').decode().strip() == args.publication,
            'Checkout the new publication before deployment')
    require(not git('status', '--porcelain', '--untracked-files=no').strip(), 'Tracked checkout is dirty')
    published = [(PACKAGE+'bootstrap_receipts.py', Path(__file__).resolve()),
                 (PACKAGE+'RECEIPT_BOOTSTRAP_SELECTION.json', Path(args.manifest).resolve())]
    published += [(r['capsule'], beneath(repo, r['capsule'])) for r in rows]
    for relative, path in published:
        require(git('show', args.publication+':'+relative) == path.read_bytes(),
                'Deployment input differs from publication: '+relative)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repository', default='/workspace/p25-q96-20261125')
    parser.add_argument('--manifest', required=True)
    parser.add_argument('--manifest-sha', required=True)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--plan', action='store_true')
    modes.add_argument('--apply', action='store_true')
    parser.add_argument('--publication')
    parser.add_argument('--runner-sha')
    args = parser.parse_args()
    repo = Path(args.repository).resolve()
    require(sha_file(args.manifest) == args.manifest_sha, 'Deployment manifest SHA mismatch')
    manifest = json.loads(Path(args.manifest).read_text())
    require(manifest['schema'] == 'p25-exact-receipt-bootstrap-v1', 'Unexpected deployment schema')
    rows = manifest['entries']
    require(len(rows) == 5 and {r['target']:(r['target_bytes'],r['target_sha256']) for r in rows} == FIXED_TARGETS,
            'Deployment is limited to the five exact original RESULT files')
    if args.apply:
        require(repo == Path('/workspace/p25-q96-20261125'), 'Apply requires the fixed P3 checkout')
        publication_check(repo, args, rows)
    prepared, report_rows = [], []
    for row in rows:
        data = decode_entry(repo, row)
        target = beneath(repo, row['target'])
        state = target_state(target, len(data), row['target_sha256'])
        prepared.append((row,target,data,state))
        report_rows.append({'target':str(target),'bytes':len(data),'sha256':row['target_sha256'],
                            'capsule':row['capsule'],'state':state})
    report = {'schema':'p25-exact-receipt-bootstrap-result-v1',
        'observed_utc':datetime.now(timezone.utc).isoformat(),
        'status':'READ_ONLY_PLAN', 'repository':str(repo), 'publication_commit':args.publication,
        'manifest_sha256':args.manifest_sha, 'receipts':report_rows,
        'new_formal_credit':False, 'lean_executions':[], 'receipts_reserialized':False}
    if not args.apply:
        print(json.dumps(report, indent=2))
        return 0
    needed = sum(len(data) for _,_,data,state in prepared if state == 'ABSENT')
    require(shutil.disk_usage(repo).free >= needed + RESERVE, 'Insufficient receipt payload plus 320 MiB reserve')
    try:
        for entry, (row,target,data,_) in zip(report_rows,prepared):
            entry['action'] = install_exclusive(target,data,row['target_sha256'])
        publication_check(repo,args,rows)
        report['status'] = 'FIVE_ORIGINAL_RECEIPTS_EXACT'
        print(json.dumps(report,indent=2))
        return 0
    except Exception as error:
        report.update(status='FAILED',error=type(error).__name__+': '+str(error))
        print(json.dumps(report,indent=2))
        raise


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except Exception as error:
        print(type(error).__name__+': '+str(error),file=sys.stderr)
        raise SystemExit(1)
