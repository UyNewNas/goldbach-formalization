#!/usr/bin/env python3
"""Prepare the two-call Archive loader repair and v2 diagnostics; never compile.

The original production source and v1 diagnostic bytes are read from the fixed
Git commit. Only the named output directory is written. --check only compares
the reproducible candidate files with existing output files.
"""
from pathlib import Path
import argparse
import difflib
import hashlib
import json
import re
import subprocess

BASE = 'aa8e91cd99e6b3f6c61417271ab105d3077d010d'
REL = 'ImbalancedChen/P2OriginalSaving19Archive.lean'
V1_PREFIX = 'docs/verification/20261125-p26/archive/'
V2_PREFIX = 'docs/verification/20261125-p26/archive-v2/'
CORE = 'ImbalancedChen.P2OriginalSaving19ArchiveCore'
PARSE00 = 'ImbalancedChen.P2OriginalSaving19ArchiveParse00'
ORIGINAL_SHA = 'b8821bbc996d6fdbc19fd359b1be9dd4be181064f7fe1b2f36b8b5a27996a9b6'
OLD_CORE_SHA = 'b784118a845f0470a231ce349ddead8f3a6f0d9f6aa297f10079acbffdda9960'
PARSE_SHA = '8550c64fea8f8716042df6509d9cdb29b93a77eb3fd74ca212398b9ce3cb430d'
REFERENCE = 'ImbalancedChen/P4AOriginalNewFifthArchiveReader.lean'
REFERENCE_SHA = '59d3c878507d07dff88790ed2c9fc626768fd7155dc3250c01763273e2f0d5b6'
OLD = 'let s ← liftIO <| IO.FS.readFile p'.encode()
NEW = 'let s ← IO.FS.readFile p'.encode()
BOUNDARY = b'/-- Closed pure kernel checks, deliberately NOT run in this source task.'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def module_path(module):
    return module.replace('.', '/') + '.lean'


def json_bytes(value):
    return (json.dumps(value, indent=2, ensure_ascii=False, sort_keys=True) + '\n').encode()


def build(repo):
    def git(path):
        return subprocess.check_output(['git', 'show', BASE + ':' + path], cwd=repo)

    original = git(REL)
    old_core = git(V1_PREFIX + module_path(CORE))
    parse = git(V1_PREFIX + module_path(PARSE00))
    reference = git(REFERENCE)
    assert sha(original) == ORIGINAL_SHA and len(original) == 10836
    assert sha(old_core) == OLD_CORE_SHA and sha(parse) == PARSE_SHA
    assert sha(reference) == REFERENCE_SHA
    assert b'let c \xe2\x86\x90 IO.FS.readBinFile' in reference
    assert b'let f \xe2\x86\x90 IO.FS.readBinFile' in reference
    assert original.count(OLD) == old_core.count(OLD) == 2
    assert original.count(NEW) == old_core.count(NEW) == 0
    repaired = original.replace(OLD, NEW)
    assert repaired.replace(NEW, OLD) == original
    assert len(OLD) - len(NEW) == 10
    old_boundary = original.index(BOUNDARY)
    boundary = repaired.index(BOUNDARY)
    assert old_boundary == 8171 and boundary == 8151
    assert old_core[:old_boundary] == original[:old_boundary]
    core = repaired[:boundary] + old_core[old_boundary:]
    assert core == old_core.replace(OLD, NEW)
    assert core[:boundary] == repaired[:boundary]
    assert repaired[boundary:] == original[old_boundary:]
    changed_lines = [i + 1 for i, (a, b) in enumerate(zip(original.splitlines(), repaired.splitlines())) if a != b]
    assert changed_lines == [28, 37] and len(original.splitlines()) == len(repaired.splitlines())
    assert all(old.replace(OLD, NEW) == new for old, new in zip(original.splitlines(), repaired.splitlines()))
    outputs = {REL: repaired, module_path(CORE): core, module_path(PARSE00): parse}
    replacements = [
        {'module': 'ImbalancedChen.P2OriginalSaving19Archive', 'path': REL,
         'before_sha256': sha(original), 'after_sha256': sha(repaired),
         'bytes_before': len(original), 'bytes_after': len(repaired)},
        {'module': CORE, 'path': module_path(CORE),
         'before_sha256': sha(old_core), 'after_sha256': sha(core),
         'bytes_before': len(old_core), 'bytes_after': len(core)},
    ]
    manifest = {
        'schema': 'p26_saving19_archive_loader_monadlift_repair_v2',
        'base_commit': BASE, 'source_repository_path': REL,
        'source_sha256': sha(repaired), 'source_bytes': len(repaired),
        'source_git_blob': hashlib.sha1(('blob ' + str(len(repaired)) + '\0').encode() + repaired).hexdigest(),
        'original_source_sha256': sha(original), 'original_source_bytes': len(original),
        'source_repair': {'old_expression': OLD.decode(), 'new_expression': NEW.decode(),
                          'occurrences': 2, 'changed_lines': changed_lines,
                          'deleted_bytes_per_occurrence': 10, 'total_deleted_bytes': 20,
                          'reverse_replacement_equals_original': True},
        'slice_start_byte': 0, 'slice_end_byte_exclusive': boundary,
        'original_slice_end_byte_exclusive': old_boundary,
        'slice_first_line': 1, 'slice_last_line_inclusive': len(repaired[:boundary].splitlines()),
        'slice_sha256': sha(repaired[:boundary]), 'slice_byte_identical_to_repaired_production': True,
        'slice_endpoint': 'after complete def moments and before the first general parse-success guard comment',
        'candidate_files': [
            {'module': m, 'path': V2_PREFIX + module_path(m), 'install_path': module_path(m),
             'sha256': sha(outputs[module_path(m)]), 'bytes': len(outputs[module_path(m)])}
            for m in (CORE, PARSE00)],
        'known_preimage_repairs_for_root_only': replacements,
        'diagnostic_driver_may_replace_existing_source': False,
        'parse00_source_unchanged': True,
        'existing_direct_io_elaborator_reference': {
            'commit': BASE, 'path': REFERENCE, 'sha256': REFERENCE_SHA,
            'description': 'Term elaborator directly binds IO.FS.readBinFile without an explicit liftIO identifier.'},
        'reported_failure': {'job': 'job_55c8ed8cfb6c45f9bd2d7dd4080c9e82',
                             'elapsed_seconds': 13.465, 'lines': [28, 37],
                             'message': 'Unknown identifier liftIO',
                             'secondary_errors': 'two term elaborators were not implemented',
                             'evidence_source': 'parent-provided actual cloud failure; no repeated compilation'},
        'status': 'UNCOMPILED_LOADER_REPAIR_AND_DIAGNOSTIC_CANDIDATE',
        'archive_complete': False, 'only_cell00_proved': False,
    }
    audit = {
        'diagnostic_only': True, 'compiled': False, 'remote_jobs_started': False,
        'pure_parsers_executed': False, 'loaders_executed': False,
        'fixture_mathematical_audit_performed': False,
        'production_change_exactly_two_loader_calls': True,
        'changed_production_lines': changed_lines,
        'reverse_replacement_equals_original': True,
        'core_change_exactly_two_loader_calls': core == old_core.replace(OLD, NEW),
        'core_prefix_byte_identical_to_repaired_production': True,
        'production_tail_after_prefix_byte_identical': True,
        'parse00_source_byte_identical': sha(parse) == PARSE_SHA,
        'data_paths_records_decoders_definitions_theorem_statements_unchanged': True,
        'geometry_loader_call_count': core.count(b'originalGeometryText% ') - 1,
        'moment_loader_call_count': core.count(b'originalMomentText% ') - 1,
        'parse00_theorems': re.findall(r'^theorem (\S+)', parse.decode(), re.M),
        'closed_decide_proof_count': parse.count(b':= by decide'),
        'forbidden_token_hits': [],
        'original_maxRecDepth_preserved': 1000000,
        'heartbeat_override_added': False,
        'candidate_prefix_bytes': boundary, 'old_prefix_bytes': old_boundary,
        'prefix_deleted_bytes': old_boundary - boundary,
        'general_archive_acceptance_claimed': False,
        'archive_complete': False, 'only_cell00_proved': False,
        'original_git_and_production_worktree_not_modified': True,
    }
    for path, data in outputs.items():
        audit['forbidden_token_hits'].extend(
            {'path': path, 'token': m.group()} for m in re.finditer(r'\b(?:sorry|admit|axiom|native_decide|unsafe)\b', data.decode()))
    assert not audit['forbidden_token_hits']
    assert audit['geometry_loader_call_count'] == audit['moment_loader_call_count'] == 13
    assert audit['parse00_theorems'] == ['geometry_parse_00', 'moment_parse_00']
    assert audit['closed_decide_proof_count'] == 2
    patch = []
    for path, old, new in ((REL, original, repaired), (module_path(CORE), old_core, core)):
        patch.extend(difflib.diff_bytes(difflib.unified_diff, old.splitlines(keepends=True), new.splitlines(keepends=True),
                                       fromfile=('a/' + path).encode(), tofile=('b/' + path).encode()))
    report = f'''# Saving19 Archive loader repair and v2 diagnostic candidate

## Observed failure and proposed repair

Parent-reported cloud job `job_55c8ed8cfb6c45f9bd2d7dd4080c9e82` failed after
13.465 seconds: production-prefix lines 28 and 37 referenced unknown identifier
`liftIO`, followed by the two term elaborators being unavailable. Parse00 was
not run. These candidates have not been compiled and claim no repair success.

Each of the two loader lines changes exactly as follows:

```lean
{OLD.decode()}
```

to the direct IO bind already used by repository term elaborators:

```lean
{NEW.decode()}
```

The inspected reference is `{BASE}:{REFERENCE}`, source SHA256
`{REFERENCE_SHA}`. It directly binds `IO.FS.readBinFile` twice inside a term
elaborator. This supports the implicit MonadLift form; it is not a fresh
compilation of the text loader.

## Exact byte boundary

Deleting `liftIO <| ` removes **10 ASCII bytes per occurrence**, including the
trailing space. The production file is {len(repaired)} bytes, reduced from
{len(original)}. The original 8,171-byte prefix becomes **8,151 bytes**; its SHA256 is
`{sha(repaired[:boundary])}`. Core copies that repaired prefix byte-for-byte.
The rest of production Archive and the entire Parse00 source are byte-identical
to their originals. No record, parser, path, default, guard, theorem statement,
proof body outside the two IO binds, recursion limit, or witness is changed.

## Candidate files and installation boundary

- `{REL}`: exactly the two production loader call repairs.
- `{module_path(CORE)}`: the same two-call repair to the previous diagnostic Core.
- `{module_path(PARSE00)}`: unchanged two cell-00 closed parse proofs.
- `SOURCE_MANIFEST.json`: old/new source pins, exact prefix and source origins.
- `STATIC_AUDIT.json`: only checks performed while producing these files.
- `known_preimage_repairs.patch`: review aid for the two known-preimage edits.
- `build_candidate.py`: reproducible generator; never invokes Lean or loads witnesses.

Only Root may install the two known-preimage replacements after checking and
backing up the original production and failed Core files. The v2 diagnostic
driver accepts only an absent target or the exact new bytes. It never performs
the replacements. Publish the new diagnostic files under `{V2_PREFIX}` and the
production repair at its normal path in a descendant of `{BASE}`.

The v1 directory, v1 driver and its failed evidence are retained. The independent
v2 evidence root starts without reusing the failed Core's build provenance.

## Acceptance boundary

Both original loaders still read all 26 original files from the unchanged
`../goldbach-research/` paths, including all thirteen cells. The v2 driver keeps
normal compilation, leanchecker, complete owned types/axioms, runtime review,
and actual loader-input before/after binding. It does not change audit limits,
templates, truncation gates or fixture checks. No external mathematical audit
is substituted for a proof.

Core contains no original parse-success proof. Parse00 still attempts only
the two cell-00 parse checks. `archive_complete` remains false; no cell is
reported proved before complete acceptance.
'''
    outputs.update({'SOURCE_MANIFEST.json': json_bytes(manifest), 'STATIC_AUDIT.json': json_bytes(audit),
                    'REPORT.md': report.encode(), 'known_preimage_repairs.patch': b''.join(patch)})
    return outputs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-root', type=Path, default=Path('/workspace/p26-source-closure'))
    parser.add_argument('--output', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    outputs = build(args.source_root.resolve())
    for rel, data in outputs.items():
        path = args.output / rel
        if args.check:
            assert path.read_bytes() == data, 'candidate output differs: ' + str(path)
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
    print(json.dumps({'status': 'STATIC_REPRODUCTION_PASS' if args.check else 'CANDIDATE_WRITTEN_UNCOMPILED',
                      'files': {rel: {'bytes': len(data), 'sha256': sha(data)} for rel, data in outputs.items()},
                      'compiled': False, 'archive_complete': False}, sort_keys=True))


if __name__ == '__main__':
    main()
