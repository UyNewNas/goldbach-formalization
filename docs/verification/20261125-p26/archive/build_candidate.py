#!/usr/bin/env python3
"""Extract the exact Saving19 archive prefix and two cell-00 diagnostics; no compilation."""
from pathlib import Path
import argparse
import difflib
import hashlib
import json
import re
import subprocess

BASE = '298670f119d24874b719facb3ef756f1e01223a1'
REL = Path('ImbalancedChen/P2OriginalSaving19Archive.lean')
BOUNDARY = b'/-- Closed pure kernel checks, deliberately NOT run in this source task.'
CORE = 'P2OriginalSaving19ArchiveCore'
PARSE00 = 'P2OriginalSaving19ArchiveParse00'
CORE_SUFFIX = b'''/-!
DIAGNOSTIC CANDIDATE ONLY. The byte-identical original prefix ends above,
including both loaders, all thirteen geometry/moment strings, the pure
decoders and the typed geometry/moments definitions. The original general
parse-success, cell-shape and row-shape guards are deliberately outside
this diagnostic module. This file has not been compiled.
-/

end ImbalancedChen.P2OriginalSaving19Archive
'''
PARSE_SOURCE = '''import ImbalancedChen.P2OriginalSaving19ArchiveCore

/-!
DIAGNOSTIC CANDIDATE ONLY / NOT COMPILED.

Two closed pure parse checks for original cell 00. The imported Core keeps
all original loaders and all thirteen entries of each text dictionary;
only these two proof goals are restricted to cell 00. No original data,
parser implementation or typed fallback definition has been changed.
This module does not assert the full Archive guards or any other cell.
-/
namespace ImbalancedChen.P2OriginalSaving19ArchiveParse00

set_option maxRecDepth 1000000

open P2OriginalSaving19Archive

theorem geometry_parse_00 :
    geometryParse (0 : Fin 13) = .ok (geometry 0) := by decide

theorem moment_parse_00 :
    momentParse (0 : Fin 13) = .ok (moments 0) := by decide

#print axioms geometry_parse_00
#print axioms moment_parse_00

end ImbalancedChen.P2OriginalSaving19ArchiveParse00
'''

def sha(b):
    return hashlib.sha256(b).hexdigest()

def blob_id(b):
    return hashlib.sha1(('blob '+str(len(b))+'\0').encode()+b).hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-root', type=Path, default=Path('/workspace/p26-p1-reference'))
    parser.add_argument('--output', type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    src = args.source_root.resolve()
    out = args.output.resolve()
    source = (src/REL).read_bytes()
    committed = subprocess.check_output(['git', 'show', BASE+':'+str(REL)], cwd=src)
    assert source == committed, 'source does not match the authorized P1 snapshot'
    boundary = source.index(BOUNDARY)
    prefix = source[:boundary]
    assert prefix.endswith(b'def moments (c : Fin 13) : Moments := (momentParse c).toOption.getD default\n\n')
    assert source.count(BOUNDARY) == 1
    core = prefix + CORE_SUFFIX
    parse = PARSE_SOURCE.encode()
    assert core[:len(prefix)] == prefix
    core_imports = [x for x in core.decode().splitlines() if x.startswith('import ')]
    assert core_imports == [
        'import ImbalancedChen.P2OriginalSaving19MomentFloorConsumer',
        'import ImbalancedChen.P2OriginalSaving19SourceJson',
    ]
    theorem_names = re.findall(r'^theorem (\S+)', parse.decode(), re.M)
    assert theorem_names == ['geometry_parse_00', 'moment_parse_00']
    assert parse.count(b':= by decide') == 2
    assert b'theorem geometry_parse_success' not in core
    assert b'theorem moments_parse_success' not in core
    assert b'def CellShape' not in core
    assert b'def RowShape' not in core
    forbidden = []
    for name, data in [(CORE, core), (PARSE00, parse)]:
        forbidden.extend((name, m.group()) for m in re.finditer(r'\b(?:sorry|admit|axiom|native_decide|unsafe)\b', data.decode()))
    assert not forbidden
    (out/'ImbalancedChen').mkdir(parents=True, exist_ok=True)
    outputs = {CORE: core, PARSE00: parse}
    for name, data in outputs.items():
        (out/'ImbalancedChen'/(name+'.lean')).write_bytes(data)
    patch = []
    for name, data in sorted(outputs.items()):
        patch.extend(difflib.diff_bytes(difflib.unified_diff, [], data.splitlines(keepends=True),
            fromfile=b'/dev/null', tofile=('b/ImbalancedChen/'+name+'.lean').encode()))
    (out/'candidate.patch').write_bytes(b''.join(patch))
    assert (src/REL).read_bytes() == source, 'production Archive was modified'
    manifests = {
        'base_commit': BASE,
        'source_path': str(src/REL), 'source_repository_path': str(REL),
        'source_sha256': sha(source), 'source_git_blob': blob_id(source),
        'source_bytes': len(source), 'verified_against_commit': True,
        'slice_start_byte': 0, 'slice_end_byte_exclusive': len(prefix),
        'slice_first_line': 1, 'slice_last_line_inclusive': len(prefix.splitlines()),
        'slice_sha256': sha(prefix), 'slice_byte_identical': True,
        'slice_endpoint': 'after the complete def moments and before the first general parse-success guard comment',
        'source_preserved_after_generation': True,
        'candidate_files': [{'path': str(out/'ImbalancedChen'/(name+'.lean')),
                             'sha256': sha(data), 'bytes': len(data)}
                            for name, data in sorted(outputs.items())],
    }
    (out/'SOURCE_MANIFEST.json').write_text(json.dumps(manifests, indent=2)+'\n')
    audit = {
        'diagnostic_only': True, 'compiled': False, 'remote_jobs_started': False,
        'pure_parsers_executed': False, 'loaders_executed': False,
        'general_archive_acceptance_claimed': False,
        'core_imports': core_imports, 'parse00_theorems': theorem_names,
        'closed_decide_proof_count': 2, 'forbidden_token_hits': forbidden,
        'original_namespace_preserved': 'ImbalancedChen.P2OriginalSaving19Archive',
        'original_maxRecDepth_preserved': 1000000,
        'parse00_maxRecDepth': 1000000,
        'heartbeat_override_added': False,
        'all_twenty_six_loader_calls_preserved': True,
        'geometry_loader_call_count': prefix.count(b'originalGeometryText% ') - 1,
        'moment_loader_call_count': prefix.count(b'originalMomentText% ') - 1,
        'production_archive_unchanged': True,
    }
    assert audit['geometry_loader_call_count'] == 13
    assert audit['moment_loader_call_count'] == 13
    (out/'STATIC_AUDIT.json').write_text(json.dumps(audit, indent=2)+'\n')
    report = '''# Saving19 Archive cell-00 parsing diagnostic candidate

## Scope and status

This candidate extracts the original loader/text/parser prefix of
`P2OriginalSaving19Archive` and adds exactly two closed cell-00 proof goals.
It is **uncompiled diagnostic source**, with no claim that the complete Archive,
cell shapes, row shapes, geometry, moments, Q96 binding, or other cells have passed.
No remote compilation, parser execution, loader execution, or data rewrite was
performed while creating this candidate. The production Archive was not changed.

## Files

- `ImbalancedChen/P2OriginalSaving19ArchiveCore.lean`: the original prefix through
  `geometry` and `moments`, with the original namespace and definition bodies.
- `ImbalancedChen/P2OriginalSaving19ArchiveParse00.lean`: imports only Core and
  defines `geometry_parse_00` and `moment_parse_00`, each with `by decide`.
- `candidate.patch`: two additive files only; no production-file mutation.
- `SOURCE_MANIFEST.json`: exact source commit/path/hash and slice provenance.
- `STATIC_AUDIT.json`: checks actually performed and diagnostics not performed.
- `build_candidate.py`: deterministic extraction from the specified P1 snapshot;
  it never invokes Lean or a remote service.

## Exact source slice

Source commit: `'''+BASE+'''`.
Source path: `'''+str(src/REL)+'''`.
Source Git blob: `'''+blob_id(source)+'''`.
Source SHA-256: `'''+sha(source)+'''`.

The first **'''+str(len(prefix))+''' bytes**, source lines **1–'''+str(len(prefix.splitlines()))+'''**, are copied
byte-for-byte. The slice ends after the complete `def moments` and its following
blank line. The next source text is the comment introducing the original general
parse-success guards, which is excluded.

Slice SHA-256: `'''+sha(prefix)+'''`.

Core retains exactly the original imports:

```lean
import ImbalancedChen.P2OriginalSaving19MomentFloorConsumer
import ImbalancedChen.P2OriginalSaving19SourceJson
```

The original loader elaborators, both thirteen-entry String dictionaries,
`parseInteger`, rational decoders, all record structures and decoders,
`geometryParse`, `momentParse`, `geometry`, and `moments` are unchanged.
The original namespace `ImbalancedChen.P2OriginalSaving19Archive` is preserved.
The only appended Core content is a diagnostic comment and the closing namespace.

## The two intended kernel goals

```lean
theorem geometry_parse_00 :
    geometryParse (0 : Fin 13) = .ok (geometry 0) := by decide

theorem moment_parse_00 :
    momentParse (0 : Fin 13) = .ok (moments 0) := by decide
```

There are no hypotheses. The corresponding `#print axioms` commands are included
for the later compilation transcript. No output from those commands is claimed
here. The diagnostic file sets `maxRecDepth` to the same original 1,000,000 and
adds no heartbeat override.

## Resource measurement boundary

Only the two closed parse proofs are restricted to cell 00. Core still contains
**all thirteen geometry loader calls and all thirteen moment loader calls**.
Consequently its elaboration still reads and embeds all 26 original String
literals. This preserves the requested data representation; it does not turn the
Core loader into a two-file loader.

The unchanged loaders resolve their original paths relative to the compilation
working directory, including the sibling `../goldbach-research/` directory.
Cell 00 uses the original files:

- `eighth-third-minorant-extension-20261009-a23-s23_low-00-cell.witness.json`
- `eighth-third-moment-refinement-20261009-a23-low-00.witness.json`

All other original entries must remain available for Core's unchanged loader.
The diagnostic imports Core rather than the production Archive; those two files
contain the same public definitions and must not be imported together into one
Lean environment. Integrating a permanent production split is outside this
candidate and has not been performed.
'''
    (out/'REPORT.md').write_text(report)
    print(json.dumps({'output': str(out), 'lean_files': len(outputs),
                      'source_commit_verified': True, 'prefix_bytes': len(prefix),
                      'prefix_lines': len(prefix.splitlines()),
                      'prefix_sha256': sha(prefix), 'source_unchanged': True,
                      'closed_decide_goals': 2, 'compiled': False}, indent=2))

if __name__ == '__main__':
    main()
