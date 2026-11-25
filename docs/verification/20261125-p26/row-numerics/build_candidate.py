#!/usr/bin/env python3
"""Mechanical RowNumerics extraction; never invokes Lean or changes production."""
from pathlib import Path
import difflib
import hashlib
import json
import shutil

ROOT = Path(__file__).resolve().parent
PRODUCTION = Path('/workspace/p26-source-closure')
SCHEMA_DONOR = Path('/workspace/p26-recovery-candidates/archive-schema')
ORIGINAL = ROOT / 'syntax-only/ImbalancedChen/P2OriginalSaving19Original28918.lean'
EXPECTED_ORIGINAL = '05a98da484b41a8e5e0842c31b86b74df0a94bfc2e51ff4c64b9daddf092dd4f'
INVALID_ORIGINAL = ROOT / 'history/original-ed126/P2OriginalSaving19Original28918.lean'
MODULE = 'ImbalancedChen.P2OriginalSaving19RowNumerics'
ENVIRONMENT = [
    'P2PositiveAffineSimplexLogJensen',
    'P2DegreeSixLogGapSoundness',
    'P2OriginalLogMomentQ96Checker',
]


def sha(b):
    return hashlib.sha256(b).hexdigest()


def fp(p):
    b = p.read_bytes()
    return {'path': str(p), 'bytes': len(b), 'sha256': sha(b)}


def copy_exact(src, dst):
    if dst.exists():
        assert dst.read_bytes() == src.read_bytes(), str(dst)
    else:
        shutil.copyfile(src, dst)


def main():
    original = ORIGINAL.read_bytes()
    assert sha(original) == EXPECTED_ORIGINAL
    invalid_original = INVALID_ORIGINAL.read_bytes()
    assert sha(invalid_original) == 'ed126d258139d3ee671f164852f816255138657a035f74af67a0f610637c24b4'
    assert invalid_original.count(b'8.factorial') == 2
    assert original == invalid_original.replace(b'8.factorial', b'Nat.factorial 8')
    pairs = [
        ('QPoint', b'abbrev QPoint', b'abbrev rawVertex'),
        ('comparisonQ', b'def comparisonQ', b'def newQ'),
        ('newQ', b'def newQ', b'def thirdQ'),
        ('thirdQ', b'def thirdQ', b'def totalQ'),
        ('totalQ', b'def totalQ', b'def gapQ'),
        ('gapQ', b'def gapQ', b'def factorsQ'),
        ('factorsQ', b'def factorsQ', b'def realPoint'),
        ('PhysicalQ', b'def PhysicalQ', b'instance (t : QPoint)'),
        ('PhysicalQ_decidable_instance', b'instance (t : QPoint)', b'theorem comparison_cast'),
    ]
    slices = []
    for name, start, end in pairs:
        a = original.index(start)
        b = original.index(end, a + len(start))
        piece = original[a:b]
        slices.append({'name': name, 'start': a, 'end': b, 'bytes': len(piece),
                       'sha256': sha(piece), 'piece': piece})
    header = b'''import ImbalancedChen.P2OriginalSaving19ArchiveSchema
import ImbalancedChen.P2OriginalLogMomentQ96Checker
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
Data-independent representation of the original Saving19 row arithmetic.
The original rational coordinate declarations below retain their namespace,
types and definition bytes. The finite interface takes the true archive
GeometryRow and nine ordered rational vertices; it proves no concrete data
guard, parse success, shape, floor, ownership, or integral bound.
-/
namespace ImbalancedChen.P2OriginalSaving19Original28918

open scoped BigOperators

'''
    suffix = (ROOT / 'RowNumerics.suffix.lean.txt').read_bytes()
    new_source = header + b''.join(s['piece'] for s in slices) + suffix
    target = ROOT / 'ImbalancedChen/P2OriginalSaving19RowNumerics.lean'
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(new_source)
    overlay = original
    for record in sorted(slices, key=lambda s: s['start'], reverse=True):
        overlay = overlay[:record['start']] + overlay[record['end']:]
    added_import = b'import ImbalancedChen.P2OriginalSaving19RowNumerics\n'
    first_import = b'import ImbalancedChen.P2OriginalSaving19Archive\n'
    assert overlay.count(first_import) == 1
    overlay = overlay.replace(first_import, first_import + added_import, 1)
    bridge = '''/-- The generic finite interface is exactly the original row predicate.
This source-only overlay requires the Schema-based Archive migration; no
closed original guard is used to prove this definitional bridge. -/
theorem rowDataChecksFor_iff_original (r : OriginalRowIndex) :
    P2OriginalSaving19RowNumerics.RowDataChecksFor
      (rawVertex r) (rawGeometryRow r) ↔ RowDataChecks r :=
  P2OriginalSaving19RowNumerics.rowDataChecksFor_iff_originalForm
    rawVertex rawGeometryRow r

'''.encode('utf-8')
    marker = b'/-- This is a closed pure proofterm request, NOT a hypothesis and NOT an\n'
    assert overlay.count(marker) == 1
    overlay = overlay.replace(marker, bridge + marker, 1)
    overlay_path = ROOT / 'overlay/ImbalancedChen/P2OriginalSaving19Original28918.lean'
    overlay_path.parent.mkdir(parents=True, exist_ok=True)
    overlay_path.write_bytes(overlay)
    patch = ''.join(difflib.unified_diff(
        original.decode().splitlines(keepends=True), overlay.decode().splitlines(keepends=True),
        fromfile='a/ImbalancedChen/P2OriginalSaving19Original28918.lean',
        tofile='b/ImbalancedChen/P2OriginalSaving19Original28918.lean'))
    (ROOT / 'Original28918.overlay.patch').write_text(patch)
    # Keep accepted suppliers in a setup-only subtree, never as new owner sources.
    setup = []
    for name in ENVIRONMENT:
        src = PRODUCTION / 'ImbalancedChen' / (name + '.lean')
        dst = ROOT / 'local/ImbalancedChen' / (name + '.lean')
        dst.parent.mkdir(parents=True, exist_ok=True)
        copy_exact(src, dst)
        setup.append({'module': 'ImbalancedChen.' + name, 'source': fp(src),
                      'local_source': fp(dst), 'environment_setup_only': True})
    reused = []
    for name in ['P2OriginalSaving19SourceJson', 'P2OriginalSaving19ArchiveSchema']:
        src = SCHEMA_DONOR / 'ImbalancedChen' / (name + '.lean')
        prod = PRODUCTION / 'ImbalancedChen' / (name + '.lean')
        assert src.read_bytes() == prod.read_bytes()
        obj = SCHEMA_DONOR / 'objects/ImbalancedChen' / (name + '.olean')
        dst = ROOT / 'local/ImbalancedChen' / (name + '.lean')
        dstobj = ROOT / 'local/objects/ImbalancedChen' / (name + '.olean')
        dst.parent.mkdir(parents=True, exist_ok=True)
        dstobj.parent.mkdir(parents=True, exist_ok=True)
        copy_exact(src, dst)
        copy_exact(obj, dstobj)
        reused.append({'module': 'ImbalancedChen.' + name, 'source': fp(src),
                       'object': fp(obj), 'local_source': fp(dst), 'local_object': fp(dstobj),
                       'recompiled': False})
    # Every retained byte is unchanged after deleting only the approved slices.
    expected_retained = original
    for record in sorted(slices, key=lambda s: s['start'], reverse=True):
        expected_retained = expected_retained[:record['start']] + expected_retained[record['end']:]
    assert overlay.replace(added_import, b'', 1).replace(bridge, b'', 1) == expected_retained
    for record in slices:
        assert new_source.count(record['piece']) == 1
    a, b = original.index(b'def RowDataChecks'), original.index(b'\ninstance (r : OriginalRowIndex)')
    assert original[a:b] in overlay
    (ROOT / 'logs').mkdir(exist_ok=True)
    manifest = {
        'schema': 'p26_row_numerics_mechanical_extraction_v1',
        'original_source': fp(ORIGINAL),
        'invalid_historical_original_source': fp(INVALID_ORIGINAL),
        'explicit_syntax_fix_manifest': fp(ROOT / 'syntax-only/SYNTAX_FIX_MANIFEST.json'),
        'new_owner': fp(target), 'module': MODULE,
        'overlay': fp(overlay_path), 'overlay_compiled': False,
        'moved_declarations': [{k: v for k, v in r.items() if k != 'piece'} for r in slices],
        'all_retained_original_bytes_unchanged': True,
        'RowDataChecks_exact_bytes_retained': True,
        'RowDataChecks_sha256': sha(original[a:b]),
        'new_interface_factorial_syntax': 'Nat.factorial 8 agrees with explicit corrected-source baseline; overlay clauses byte-preserved from that baseline',
        'new_closed_actual_data_guards': 0,
        'environment_setup': setup, 'reused_objects': reused,
        'source_only_overlay_blocker': 'current production Archive f48 still defines Schema FQNs; requires Schema-based Archive facade before acceptance',
        'production_modified': False, 'compiler_executed_by_builder': False,
    }
    (ROOT / 'EXTRACTION_MANIFEST.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps({'new_owner': manifest['new_owner'], 'overlay': manifest['overlay'],
                      'retained_original_bytes_unchanged': True}, indent=2))


if __name__ == '__main__':
    main()
