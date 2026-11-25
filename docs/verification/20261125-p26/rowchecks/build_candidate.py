#!/usr/bin/env python3
"""Create the approved Saving19 fastDet proof-representation candidate; no compilation."""
from pathlib import Path
import argparse
import difflib
import hashlib
import json
import re
import subprocess

BASE = '298670f119d24874b719facb3ef756f1e01223a1'
MODULE = 'P2OriginalSaving19Original28918'
CHECKER = 'P2Winner9RowArithmeticChecker'
OLD_PROOF = b'theorem original_data_checks : \xe2\x88\x80 r, RowDataChecks r := by decide\n'
NEW_PROOF = '''theorem original_data_checks : ∀ r, RowDataChecks r := by
  simp only [RowDataChecks, ← P2Winner9RowArithmeticChecker.fastDet_eq]
  decide
'''.encode()
ADDED_IMPORT = b'import ImbalancedChen.P2Winner9RowArithmeticChecker\n'

def sha(b):
    return hashlib.sha256(b).hexdigest()

def git_blob(b):
    return hashlib.sha1(('blob '+str(len(b))+'\0').encode()+b).hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-root', type=Path, default=Path('/workspace/p26-p1-reference'))
    parser.add_argument('--output', type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    src = args.source_root.resolve()
    out = args.output.resolve()
    source_path = src/'ImbalancedChen'/(MODULE+'.lean')
    checker_path = src/'ImbalancedChen'/(CHECKER+'.lean')
    original = source_path.read_bytes()
    checker = checker_path.read_bytes()
    source_records = []
    for name, path, data in [(MODULE, source_path, original), (CHECKER, checker_path, checker)]:
        rel = 'ImbalancedChen/'+name+'.lean'
        assert subprocess.check_output(['git', 'show', BASE+':'+rel], cwd=src) == data
        source_records.append({'module': name, 'source_path': str(path),
            'repository_path': rel, 'base_commit': BASE, 'verified_against_commit': True,
            'sha256': sha(data), 'git_blob': git_blob(data), 'bytes': len(data)})
    assert original.count(OLD_PROOF) == 1
    anchor = b'import ImbalancedChen.P2OriginalSaving19Archive\n'
    assert original.count(anchor) == 1
    assert ADDED_IMPORT not in original
    candidate = original.replace(anchor, anchor+ADDED_IMPORT, 1).replace(OLD_PROOF, NEW_PROOF, 1)
    restored = candidate.replace(ADDED_IMPORT, b'', 1).replace(NEW_PROOF, OLD_PROOF, 1)
    assert restored == original
    statement = OLD_PROOF.split(b':=')[0]
    assert NEW_PROOF.split(b':=')[0] == statement
    public = lambda b: re.findall(rb'^(?:(?:noncomputable|private|protected)\s+)*(?:def|abbrev|theorem|lemma|structure|inductive|instance)\b[^\n]*', b, re.M)
    original_headers = public(original)
    candidate_headers = public(candidate)
    normalize_header = lambda b: b.split(b':=')[0].rstrip()
    assert [normalize_header(x) for x in original_headers] == [normalize_header(x) for x in candidate_headers]
    gs = original.index(b'def RowDataChecks ')
    ge = original.index(b'\ninstance (r : OriginalRowIndex) : Decidable (RowDataChecks r)', gs)
    guard = original[gs:ge]
    assert guard in candidate
    assert guard.count(b'(edgeQ r).det') == 2
    iface_start = checker.index(b'theorem fastDet_eq ')
    iface_end = checker.index(b'\n/-- Ordered vertices', iface_start)
    interface = checker[iface_start:iface_end]
    assert b'{n : \xe2\x84\x95}' in interface
    forbidden = [(m.group(), candidate[:m.start()].count(b'\n')+1)
                 for m in re.finditer(rb'\b(?:sorry|admit|axiom|native_decide|unsafe)\b', candidate)]
    assert not forbidden
    (out/'ImbalancedChen').mkdir(parents=True, exist_ok=True)
    candidate_path = out/'ImbalancedChen'/(MODULE+'.lean')
    candidate_path.write_bytes(candidate)
    rel = 'ImbalancedChen/'+MODULE+'.lean'
    patch = b''.join(difflib.diff_bytes(difflib.unified_diff,
        original.splitlines(keepends=True), candidate.splitlines(keepends=True),
        fromfile=('a/'+rel).encode(), tofile=('b/'+rel).encode()))
    (out/'candidate.patch').write_bytes(patch)
    check = subprocess.run(['git', 'apply', '--check', '--whitespace=error-all',
                            str(out/'candidate.patch')], cwd=src, capture_output=True, text=True)
    assert check.returncode == 0, check.stderr
    assert source_path.read_bytes() == original
    assert checker_path.read_bytes() == checker
    manifest = {'base_commit': BASE, 'sources': source_records,
        'candidate_path': str(candidate_path), 'candidate_sha256': sha(candidate),
        'patch_sha256': sha(patch), 'guard_definition_sha256': sha(guard),
        'fastDet_eq_source_slice_sha256': sha(interface),
        'historical_accepted_source_prefix_supplied_by_parent': 'bef1fb6c',
        'historical_olean_credit_transferred': False}
    (out/'SOURCE_MANIFEST.json').write_text(json.dumps(manifest, indent=2)+'\n')
    audit = {'compiled': False, 'remote_jobs_started': False,
        'production_sources_unchanged': True,
        'only_added_import_and_replaced_original_data_checks_proof': True,
        'full_source_recovered_by_reversing_those_two_edits': True,
        'declaration_header_count': len(original_headers),
        'same_declaration_headers': True,
        'original_data_checks_statement_byte_identical': True,
        'RowDataChecks_definition_byte_identical': True,
        'RowDataChecks_matrix_det_occurrences': 2,
        'proof_requests_reverse_fastDet_eq_rewrite': True,
        'simp_only_elaboration_verified': False,
        'rewritten_lean_goal_observed': False,
        'closed_decide_kernel_checked': False,
        'performance_measured': False,
        'new_det_algorithm_or_correctness_theorem': False,
        'literal_data_modified': False,
        'current_checker_dependency_chain_reaccepted': False,
        'historical_olean_credit_transferred': False,
        'forbidden_construct_hits': [],
        'git_apply_check': {'exit_code': check.returncode,
                            'stdout': check.stdout, 'stderr': check.stderr}}
    (out/'STATIC_AUDIT.json').write_text(json.dumps(audit, indent=2)+'\n')
    report = '''# Saving19 original_data_checks fastDet representation candidate

## Status

This is an **uncompiled performance candidate**, based on P1 source commit
`'''+BASE+'''`. Production files and literal data are unchanged. No Lean or remote
compilation was started. No speedup or successful certificate evaluation is claimed.

## Exact change

The sole candidate Lean file is `ImbalancedChen/P2OriginalSaving19Original28918.lean`.
It adds exactly one import:

```lean
import ImbalancedChen.P2Winner9RowArithmeticChecker
```

It replaces only the proof body of the existing closed theorem:

```lean
theorem original_data_checks : ∀ r, RowDataChecks r := by
  simp only [RowDataChecks, ← P2Winner9RowArithmeticChecker.fastDet_eq]
  decide
```

`candidate.patch` is the complete diff. No declaration is added, removed or renamed.
All public statements, all definitions, and every other proof body remain unchanged.
Reversing this import and this one proof-body substitution recovers the original
source bytes exactly.

## Mathematical and data content retained

`RowDataChecks` contains exactly two `(edgeQ r).det` occurrences: determinant
nonvanishing and the physical-volume equality. The existing generic interface is:

```lean
'''+interface.decode().strip()+'''
```

The candidate requests reverse rewriting with this existing equality at dimension
8 over the rationals, then requests the same closed finite proof with `decide`.
No determinant implementation or correctness theorem is introduced here.

The complete unchanged `RowDataChecks` conjunction still requires:

- determinant nonvanishing;
- every original vertex's full `PhysicalQ` condition;
- positive total gap;
- physical-volume equality and mean-gap equality;
- every factor's computed weighted mean;
- every factor maximum's domination and attainment;
- the original Jensen evaluator equality;
- the original geometry Q96 floor equality.

The universal quantifier remains over every original row. No geometry, mean,
maximum, Q96 or other conjunct is deleted or replaced by a premise. No source
literal or archive record is changed.

## Verification boundary

Static checks confirm exact preservation of the statement, definitions, other
proofs, declaration headers and literal references. The patch passes
`git apply --check --whitespace=error-all` on the specified P1 snapshot.

The `simp only` tactic has **not** been elaborated. Although the retained definition
contains the two intended determinant expressions and the reused theorem is generic
in `n`, actual rewriting under the outer universal binder, subsequent decidability
elaboration, runtime and kernel acceptance still require Lean validation. This
candidate does not assert that the transformed goal has already been observed.

The parent identified prior accepted source prefix `bef1fb6c...`. That historical
source/`.olean` acceptance is not transferred to the current P1 dependency version.
The current `P2Winner9RowArithmeticChecker` and its dependency chain must be
reaccepted in the actual target environment. This directory does not copy any
historical `.olean` or assign acceptance credit.

## Provenance

Original row module SHA-256: `'''+sha(original)+'''`.
Current checker SHA-256: `'''+sha(checker)+'''`.
Unchanged `RowDataChecks` slice SHA-256: `'''+sha(guard)+'''`.
Candidate SHA-256: `'''+sha(candidate)+'''`.

`SOURCE_MANIFEST.json` records absolute paths, Git blob IDs and source commit
verification. `STATIC_AUDIT.json` records precisely which checks ran and which
Lean/resource checks remain unperformed. `build_candidate.py` reproduces this
single-file overlay without invoking a compiler.
'''
    (out/'REPORT.md').write_text(report)
    print(json.dumps({'candidate': str(candidate_path), 'patch': str(out/'candidate.patch'),
        'only_two_authorized_edits': True, 'same_declaration_headers': len(original_headers),
        'guard_det_occurrences': 2, 'source_sha256': sha(original),
        'checker_sha256': sha(checker), 'patch_check_exit_code': check.returncode,
        'compiled': False, 'simp_elaboration_pending': True}, indent=2))

if __name__ == '__main__':
    main()
