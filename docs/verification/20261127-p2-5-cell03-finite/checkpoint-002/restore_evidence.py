"""Verify/reconstruct the frozen 775-file checkpoint without invoking Lean.

The 147-file delta references 628 already-published files. All inputs are
verified before any output file is written. This does not grant proof credit.
"""
from pathlib import Path
import argparse
import base64
import hashlib
import json
import lzma
import subprocess

BASE = 'a0eb3b8f66f47f382b0e551be1d5d7c319f8bdab'
DIRECTORY = 'docs/verification/20261127-p2-5-cell03-finite'
DELTA_SHA = 'b61cfbaba08e29dbc43556271eedf81f23728c1ba98d2d3c371be88fb6e6a813'
BASE_SHA = '197c79787aac8e6182926799e937e8b093020d627c42e8484398dca38d794760'


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def relative(name):
    path = Path(name)
    require(not path.is_absolute() and '..' not in path.parts and path.parts,
            'Unsafe relative path: ' + name)
    return path


def checked(raw, row, name):
    require(len(raw) == row['bytes'] and digest(raw) == row['sha256'],
            'Byte/hash mismatch: ' + name)
    return raw


def members(document):
    result = {}
    for name, row in document['files'].items():
        relative(name)
        result[name] = checked(base64.b64decode(row['base64'], validate=True), row, name)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--delta', type=Path, required=True)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    repo = args.repo.resolve(strict=True)

    def git_file(path):
        relative(path)
        return subprocess.check_output(['git', 'show', BASE + ':' + path], cwd=repo)

    old_parts = json.loads(git_file(DIRECTORY + '/ARTIFACT_PARTS.json'))
    row = old_parts['artifacts']['ACTUAL_EVIDENCE_DICT64.json.xz']
    require(row['sha256'] == BASE_SHA, 'Wrong baseline archive')
    chunks, offset = [], 0
    for part in row['parts']:
        require(part['offset'] == offset, 'Wrong baseline part order')
        raw = checked(git_file(DIRECTORY + '/' + part['path']), part, part['path'])
        chunks.append(raw)
        offset += len(raw)
    baseline_raw = checked(b''.join(chunks), row, 'baseline archive')
    baseline_doc = json.loads(lzma.decompress(baseline_raw))
    baseline = members(baseline_doc)
    require(len(baseline) == baseline_doc['file_count'] == 625, 'Wrong baseline count')
    delta_raw = args.delta.read_bytes()
    require(digest(delta_raw) == DELTA_SHA, 'Wrong delta archive')
    delta_doc = json.loads(lzma.decompress(delta_raw))
    require(delta_doc['baseline_publication'] == BASE and
            delta_doc['baseline_evidence_sha256'] == BASE_SHA, 'Wrong baseline reference')
    changed = members(delta_doc)
    references = delta_doc['reused_published_files']
    require(len(changed) == delta_doc['new_or_revised_file_count'] == 147 and
            len(references) == 628 and not set(changed) & set(references), 'Wrong delta partition')
    files, counts = {}, {'published_evidence_capsule': 0, 'published_repository_file': 0}
    for name, ref in references.items():
        relative(name)
        if ref['source'] == 'published_evidence_capsule':
            require(ref['member'] == name, 'Renamed baseline member')
            raw = baseline[name]
        elif ref['source'] == 'published_repository_file':
            raw = git_file(ref['repository_path'])
        else:
            raise ValueError('Unknown reference source')
        files[name] = checked(raw, ref, name)
        counts[ref['source']] += 1
    files.update(changed)
    require(len(files) == delta_doc['full_current_file_count'] == 775 and
            counts == {'published_evidence_capsule': 623, 'published_repository_file': 5},
            'Wrong reconstructed coverage')
    require(set(baseline) <= set(files) and set(changed) & set(baseline) ==
            {'DECODER_RESUME.log', 'SUMMARY_DECODER.json'}, 'Unexpected baseline replacement')
    require(delta_doc['accepted_owner_count'] == 55 and
            all(delta_doc[k] is False for k in
                ('P2_5_proved', 'physical_geometry_proved', 'complete_all_63')),
            'Checkpoint scope changed')
    if args.output:
        require(not args.output.is_symlink(), 'Output directory must not be a symlink')
        output = args.output.resolve()
        targets = {}
        for name, raw in files.items():
            target = output / relative(name)
            require(not target.is_symlink() and target.resolve().is_relative_to(output),
                    'Output path escapes directory: ' + name)
            if target.exists():
                require(target.is_file() and target.read_bytes() == raw,
                        'Preserve different existing file: ' + name)
            targets[target] = raw
        for target, raw in targets.items():
            if not target.exists():
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(raw)
    index = {name: {'bytes': len(raw), 'sha256': digest(raw)} for name, raw in sorted(files.items())}
    print(json.dumps({'verified_evidence_files': len(files), 'accepted_owners': 55,
                      'new_or_revised_files': 147, 'reused_published_files': 628,
                      'file_index_sha256': digest(json.dumps(index, sort_keys=True,
                                                            separators=(',', ':')).encode()),
                      'wrote_files': bool(args.output), 'new_Lean_invocations': 0,
                      'new_proof_credit': False, 'P2_5_proved': False}, sort_keys=True))


if __name__ == '__main__':
    main()
