"""Restore missing files from official per-module mathlib archives, matching a frozen snapshot."""
from concurrent.futures import ThreadPoolExecutor
from hashlib import sha256, file_digest
from pathlib import Path
from tempfile import TemporaryDirectory
from time import monotonic
import argparse
import json
import os
import shutil
import subprocess

MATHLIB = Path('/workspace/compile-deps/mathlib')
LIB = MATHLIB / '.lake/build/lib/lean'
SNAPSHOT = Path('/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/qualifications/attempt-003/EXTERNAL_SNAPSHOT.json')
SNAPSHOT_SHA = 'ad4386f160e7d59bcaca2820fb9123434d05593595b266ca24fa742e48367d27'
MATHLIB_PIN = 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1'
CACHE = 'http://lakecache.blob.core.windows.net/mathlib4-master/f/'
LEANTAR = '/workspace/toolchains/lean-4.33.0-rc1-linux/bin/leantar'
SUFFIXES = ('.olean.private', '.olean.server', '.ir.sig', '.olean', '.ir')
ROOT = Path('/workspace/p25-round9-external-cache-recovery-20261127')
GIB = 2**30


def digest(p):
    with p.open('rb') as f:
        return file_digest(f, 'sha256').hexdigest()


def verified(p, row):
    return p.is_file() and p.stat().st_size == row['bytes'] and digest(p) == row['sha256']


def grouped_snapshot():
    if digest(SNAPSHOT) != SNAPSHOT_SHA:
        raise ValueError('Frozen snapshot digest changed')
    commit = subprocess.check_output(['git', '-C', str(MATHLIB), 'rev-parse', 'HEAD'], text=True).strip()
    if commit != MATHLIB_PIN:
        raise ValueError('Mathlib checkout changed')
    groups = {}
    for absolute, row in json.loads(SNAPSHOT.read_bytes())['files'].items():
        p = Path(absolute)
        if not p.is_relative_to(LIB):
            continue
        relative = p.relative_to(LIB).as_posix()
        suffix = next((s for s in SUFFIXES if relative.endswith(s)), None)
        if not suffix:
            continue
        name = relative[:-len(suffix)].replace('/', '.')
        if name == 'Mathlib' or name.startswith('Mathlib.'):
            groups.setdefault(name, {})[suffix] = row
    if len(groups) != 8301 or any(set(group) != set(SUFFIXES) for group in groups.values()):
        raise ValueError('Unexpected frozen module scope')
    return groups


def target(name, suffix):
    return LIB / (name.replace('.', '/') + suffix)


def recover(job):
    name, key, rows, missing = job
    filename = key + '.ltar'
    with TemporaryDirectory(prefix='module-', dir=ROOT) as temporary:
        stage = Path(temporary)
        archive = stage / filename
        subprocess.run(['curl', '--silent', '--show-error', '--fail', '--location', '--retry', '4',
                        '--retry-delay', '2', '--max-time', '90', CACHE + filename, '-o', str(archive)],
                       check=True)
        subprocess.run([LEANTAR, '-C', str(stage), '-x', '--jobs', '1', str(archive)], check=True)
        for suffix, row in rows.items():
            staged = stage / '.lake/build/lib/lean' / target(name, suffix).relative_to(LIB)
            if not verified(staged, row):
                raise ValueError(f'Official archive digest mismatch: {name}{suffix}')
        if shutil.disk_usage(ROOT).free < GIB:
            raise ValueError('Free space below existing round-9 reserve')
        installed = []
        for suffix in missing:
            dest = target(name, suffix)
            dest.parent.mkdir(parents=True, exist_ok=True)
            staged = stage / '.lake/build/lib/lean' / dest.relative_to(LIB)
            try:
                os.link(staged, dest)
                installed.append(suffix)
            except FileExistsError:
                if not verified(dest, rows[suffix]):
                    raise ValueError(f'Conflicting existing path: {dest}')
        return {'module': name, 'key': key, 'official_archive_sha256': digest(archive),
                'download_bytes': archive.stat().st_size, 'installed': installed}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--module-list-sha256', required=True)
    parser.add_argument('--keys-sha256', required=True)
    args = parser.parse_args()
    groups = grouped_snapshot()
    modules = sorted(groups)
    names_hash = sha256(('\n'.join(modules) + '\n').encode()).hexdigest()
    if names_hash != args.module_list_sha256:
        raise ValueError('Local and P2 module order differs')
    packed = b''.join(p.read_bytes() for p in sorted(ROOT.glob('keys-*.bin')))
    if len(packed) != 8 * len(modules) or sha256(packed).hexdigest() != args.keys_sha256:
        raise ValueError('Official key mapping digest differs')
    jobs = []
    missing_bytes = 0
    for i, name in enumerate(modules):
        missing = []
        for suffix, row in groups[name].items():
            dest = target(name, suffix)
            if os.path.lexists(dest):
                if not verified(dest, row):
                    raise ValueError(f'Existing file differs: {dest}')
            else:
                missing.append(suffix)
                missing_bytes += row['bytes']
        if missing:
            jobs.append((name, packed[i * 8:(i + 1) * 8].hex(), groups[name], missing))
    if shutil.disk_usage(ROOT).free < GIB + missing_bytes:
        raise ValueError('Insufficient capacity for the remaining exact files and original disk reserve')
    log = ROOT / 'restored-modules.jsonl'
    completed = 0
    total = len(jobs)
    started = monotonic()
    print(f'Starting exact recovery: {total} packages, {missing_bytes} missing bytes', flush=True)
    # Small bounded batches keep scratch and queued work finite if any download fails.
    with log.open('a') as out, ThreadPoolExecutor(max_workers=6) as pool:
        for start in range(0, total, 64):
            for result in pool.map(recover, jobs[start:start + 64]):
                out.write(json.dumps(result, sort_keys=True) + '\n')
                completed += 1
            out.flush()
            if start % 256 == 0 or completed == total:
                print(f'Checked and installed {completed}/{total} in {monotonic() - started:.1f}s', flush=True)
    for name, rows in groups.items():
        if not all(verified(target(name, suffix), row) for suffix, row in rows.items()):
            raise ValueError(f'Post-install mismatch: {name}')
    summary = {'status': 'ALL_FROZEN_MATHLIB_OBJECTS_AND_COMPANIONS_MATCH',
               'snapshot_sha256': SNAPSHOT_SHA, 'mathlib_pin': MATHLIB_PIN,
               'module_list_sha256': names_hash, 'keys_sha256': args.keys_sha256,
               'scope_modules': len(groups), 'postverified_files': len(groups)*len(SUFFIXES),
               'initially_missing_bytes': missing_bytes, 'packages_this_run': completed,
               'restored_modules_log_sha256': digest(log), 'free_bytes': shutil.disk_usage(ROOT).free,
               'Lean_executed': False}
    (ROOT/'recovery-result.json').write_text(json.dumps(summary, sort_keys=True, indent=2)+'\n')
    print(json.dumps(summary, sort_keys=True), flush=True)


if __name__ == '__main__':
    main()
