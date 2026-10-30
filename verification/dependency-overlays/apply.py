#!/usr/bin/env python3
"""Apply only the reviewed, pinned goldbach overlay. No network or Lean execution."""
import hashlib
import json
from pathlib import Path, PurePosixPath
import subprocess
import sys
import tempfile


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def git(cwd, *args):
    return subprocess.check_output(['git', '-C', str(cwd), *args], stderr=subprocess.PIPE)


def safe(root, rel):
    p = PurePosixPath(rel)
    require(bool(p.parts) and not p.is_absolute() and all(x not in ('.', '..') for x in p.parts)
            and str(p) == rel and '\\' not in rel, 'unsafe relative path: ' + rel)
    candidate = root.joinpath(*p.parts)
    cursor = root
    for part in p.parts:
        cursor = cursor / part
        require(not cursor.is_symlink(), 'symlink path rejected: ' + rel)
    require(candidate.resolve().is_relative_to(root.resolve()), 'path escaped root')
    return candidate


def main():
    require(len(sys.argv) == 2, 'usage: apply.py PROJECT_ROOT')
    root = Path(sys.argv[1]).resolve(strict=True)
    bundle = Path(__file__).resolve().parent / 'stage002'
    manifest_bytes = (bundle / 'manifest.json').read_bytes()
    m = json.loads(manifest_bytes)
    activation = json.loads((bundle / 'activation.json').read_text())
    require(activation.get('status') == 'PASS', 'overlay activation is not independently accepted')
    require(activation.get('manifestSha256') == sha(manifest_bytes), 'activation manifest mismatch')
    review_bytes = (bundle / 'acceptance-review.json').read_bytes()
    require(activation.get('reviewSha256') == sha(review_bytes), 'acceptance review hash mismatch')
    review = json.loads(review_bytes)
    require(review.get('status') == 'PASS' and review.get('overlayPatchSha256') == m['patchSha256'],
            'acceptance review is not a PASS for this overlay')
    require(m['package'] == 'goldbach' and m['patchFile'] == 'dependency.patch', 'unexpected package/patch')
    patch_path = safe(bundle, m['patchFile'])
    patch = patch_path.read_bytes()
    require(sha(patch) == m['patchSha256'], 'patch hash mismatch')
    lock = json.loads((root / 'lake-manifest.json').read_text())
    packages = [p for p in lock['packages'] if p['name'] == 'goldbach']
    require(len(packages) == 1 and packages[0]['type'] == 'git' and packages[0]['rev'] == m['basePin'],
            'project dependency pin mismatch')
    require(lock['packagesDir'] == '.lake/packages', 'unexpected packagesDir')
    dep = safe(root, '.lake/packages/goldbach')
    require(dep.is_dir(), 'goldbach dependency not materialized')
    require(git(dep, 'rev-parse', '--show-toplevel').decode().strip() == str(dep), 'not dependency git root')
    require(git(dep, 'rev-parse', 'HEAD').decode().strip() == m['basePin'], 'dependency HEAD pin mismatch')
    flags = git(dep, 'ls-files', '-v', '-z').split(b'\0')
    require(all(not f or f[:1] == b'H' for f in flags), 'hidden/skip-worktree index entries rejected')
    require(not git(dep, 'diff', '--cached', '--name-only', '-z'), 'staged dependency changes rejected')
    # Build output is the only untracked directory tolerated, including ignored files.
    require(not git(dep, 'ls-files', '--others', '--exclude=.lake/', '-z'), 'extra untracked dependency content')
    names = set(m['files'])
    require(len(names) == 3, 'expected exact three-file overlay')
    changes = git(dep, 'diff', '--name-only', '-z', 'HEAD').decode().split('\0')
    require(set(filter(None, changes)) <= names, 'extra tracked dependency changes')
    bases = {}
    states = []
    for rel, meta in m['files'].items():
        target = safe(dep, rel)
        require(target.is_file(), 'missing source ' + rel)
        entry = git(dep, 'ls-tree', 'HEAD', '--', rel).decode().strip().split()
        require(len(entry) == 4 and entry[0] == '100644' and entry[1] == 'blob'
                and entry[2] == meta['baseGitBlob'], 'base blob/mode mismatch: ' + rel)
        require(target.stat().st_mode & 0o111 == 0, 'changed executable source mode')
        base = git(dep, 'show', 'HEAD:' + rel)
        require(sha(base) == meta['baseSha256'], 'base SHA mismatch: ' + rel)
        bases[rel] = base
        digest = sha(target.read_bytes())
        require(digest in (meta['baseSha256'], meta['patchedSha256']), 'working source SHA mismatch: ' + rel)
        states.append('base' if digest == meta['baseSha256'] else 'patched')
    require(len(set(states)) == 1, 'mixed base/patched dependency state rejected')
    # Validate patch effects on isolated files before any dependency mutation.
    with tempfile.TemporaryDirectory(prefix='goldbach-overlay-check-') as tmp:
        tmp = Path(tmp)
        for rel, base in bases.items():
            target = safe(tmp, rel)
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(base)
        subprocess.run(['git', 'apply', '--check', str(patch_path)], cwd=tmp, check=True, capture_output=True)
        subprocess.run(['git', 'apply', str(patch_path)], cwd=tmp, check=True, capture_output=True)
        found = {str(p.relative_to(tmp)) for p in tmp.rglob('*') if p.is_file() or p.is_symlink()}
        require(found == names, 'patch changed file set')
        for rel, meta in m['files'].items():
            require(sha(safe(tmp, rel).read_bytes()) == meta['patchedSha256'], 'patch result SHA mismatch: ' + rel)
    if states[0] == 'base':
        git(dep, 'apply', '--check', str(patch_path))
        git(dep, 'apply', str(patch_path))
    for rel, meta in m['files'].items():
        require(sha(safe(dep, rel).read_bytes()) == meta['patchedSha256'], 'post-apply SHA mismatch')
    print(json.dumps({'status': 'PASS', 'state': 'applied' if states[0] == 'base' else 'already-applied',
                      'basePin': m['basePin'], 'patchSha256': m['patchSha256'],
                      'notice': 'authorized patched dependency, not original fixed source'}))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, OSError, subprocess.CalledProcessError) as exc:
        print('overlay verification failed: ' + str(exc), file=sys.stderr)
        sys.exit(1)
