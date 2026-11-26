#!/usr/bin/env python3
"""Recover exact accepted cell01 typed sources and emit only the missing tail.

This is an untrusted source generator, not a Lean compiler or proof checker.
The archived original-token quotation and field-wise row renderer are reused
under pinned hashes. Every generated claim still requires ordinary Lean
elaboration and kernel replay. No archived source, object or receipt is written.
"""
from pathlib import Path
import argparse
import hashlib
import importlib
import json
import re
import sys

sys.dont_write_bytecode = True

DEFAULT_LEGACY = Path('/workspace/p26-recovery-candidates/geometry-direct-packed/attempts/cell01-full-v2/typed-v1')
DEFAULT_REPO = Path(__file__).resolve().parents[2]
NS = 'ImbalancedChen.P2OriginalSaving19Geometry01Shape'
DECODE_NS = 'ImbalancedChen.P2OriginalSaving19Geometry01Decoding'


def fp(path):
    path = Path(path)
    b = path.read_bytes()
    return {'path': str(path), 'bytes': len(b), 'sha256': hashlib.sha256(b).hexdigest()}


def write_exact(path, content):
    path = Path(path)
    b = content.encode() if isinstance(content, str) else content
    if path.exists():
        assert path.read_bytes() == b, ('Refusing source drift', str(path))
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(b)
    return fp(path)


def shape_head(imports, description):
    return ''.join('import ImbalancedChen.' + name + '\n' for name in imports) + f'''
/-! {description}
These claims concern the concrete output of the original cell01 decoder.
Finite checks are split into at most eight records per theorem. -/
namespace {NS}
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open {DECODE_NS}

'''


def row_property(index, indent='    '):
    return f'''let g := concreteGeometry01.rows[{index}]!
{indent}g.simplexId = {index} ∧
{indent}g.vertexIds.size = 9 ∧ g.vertexIds.toList.Nodup ∧
{indent}(∀ i : Fin 9, g.vertexIds[i.val]! < concreteGeometry01.vertices.size) ∧
{indent}g.factorMaxima.size = 10 ∧ g.gapWeightedMeans.size = 10'''


def vertex_property(index, indent='    '):
    return f'''(concreteGeometry01.vertices[{index}]!).size = 8 ∧
{indent}(concreteGeometry01.vertexValues[{index}]!).factors.size = 10'''


def shape_foot(theorems):
    return '\n'.join('#print axioms ' + name for name in theorems) + '\nend ' + NS + '\n'


def ranged_glue(name, size, count, property_text, block_prefix):
    out = f'theorem {name} : ∀ r : Fin {count},\n    {property_text} := by\n  intro r\n  have hr := r.isLt\n'
    for block in range(count // size):
        start, end = block * size, (block + 1) * size
        prefix = '  ' + '  ' * block
        if end < count:
            out += prefix + f'by_cases h{block} : r.val < {end}\n'
            branch = prefix + '· '
        else:
            branch = prefix
        bound = f'h{block}' if end < count else 'r.isLt'
        if start == 0:
            out += branch + f'simpa only [Nat.zero_add] using {block_prefix}_block_{block:03d} ⟨r.val, {bound}⟩\n'
        else:
            out += branch + f'have hb : r.val - {start} < {size} := by omega\n'
            p = prefix + ('  ' if end < count else '')
            out += p + f'have he : {start} + (r.val - {start}) = r.val := by omega\n'
            out += p + f'simpa only [he] using {block_prefix}_block_{block:03d} ⟨r.val - {start}, hb⟩\n'
        if end < count:
            out += prefix + '·\n'
    return out + '\n'


def emit_shape(repo):
    files, order = [], []

    def save(short, text):
        assert not re.search(r'\b(?:sorry|admit|native_decide|unsafe)\b|(?m:^\s*axiom\b)', text)
        files.append(write_exact(repo / 'ImbalancedChen' / (short + '.lean'), text))
        order.append('ImbalancedChen.' + short)

    base = 'P2OriginalSaving19Geometry01ShapeBase'
    text = shape_head(['P2OriginalSaving19Geometry01Decoded'], 'Metadata and cardinalities of the complete original typed geometry01.')
    metadata = [('dimension', 'concreteGeometry01.dimension = 8'),
                ('physical_jacobian', 'concreteGeometry01.physicalJacobian = 1'),
                ('row_count', 'concreteGeometry01.rows.size = 144'),
                ('vertex_count', 'concreteGeometry01.vertices.size = 40'),
                ('vertex_values_size', 'concreteGeometry01.vertexValues.size = concreteGeometry01.vertices.size'),
                ('facet_count', 'concreteGeometry01.facetOriginalIndices.size = 12'),
                ('facet_vertices_size', 'concreteGeometry01.facetVertices.size = 12'),
                ('face_count', 'concreteGeometry01.faces.size = 79')]
    text += '\n'.join(f'theorem {name} : {statement} := by rfl\n' for name, statement in metadata)
    text += '\n' + shape_foot([name for name, _ in metadata])
    save(base, text)
    row_imports = []
    for block in range(18):
        short = f'P2OriginalSaving19Geometry01ShapeRows{block:03d}'
        row_imports.append(short)
        text = shape_head([base], f'Original row shape, records {block * 8} through {block * 8 + 7}.')
        text += f'theorem rows_block_{block:03d} : ∀ r : Fin 8,\n    {row_property(f"({block * 8} + r.val)")} := by\n  decide +kernel\n\n'
        text += shape_foot([f'rows_block_{block:03d}'])
        save(short, text)
    vertex_imports = []
    for block in range(5):
        short = f'P2OriginalSaving19Geometry01ShapeVertices{block:03d}'
        vertex_imports.append(short)
        text = shape_head([base], f'Original vertex and factor-array shape, records {block * 8} through {block * 8 + 7}.')
        text += f'theorem vertices_block_{block:03d} : ∀ r : Fin 8,\n    {vertex_property(f"({block * 8} + r.val)")} := by\n  decide +kernel\n\n'
        text += shape_foot([f'vertices_block_{block:03d}'])
        save(short, text)
    text = shape_head(row_imports + vertex_imports, 'Complete shape of all 144 original cell01 rows and all 40 original vertices.')
    text += ranged_glue('all_rows', 8, 144, row_property('r.val'), 'rows')
    text += ranged_glue('all_vertices_bang', 8, 40, vertex_property('r.val'), 'vertices')
    text += '''theorem all_vertices (v : Fin concreteGeometry01.vertices.size) :
    (concreteGeometry01.vertices[v]).size = 8 ∧
    (concreteGeometry01.vertexValues[v.val]!).factors.size = 10 := by
  have hv : v.val < 40 := by simpa only [vertex_count] using v.isLt
  have h := all_vertices_bang ⟨v.val, hv⟩
  rw [getElem!_pos concreteGeometry01.vertices v.val v.isLt] at h
  exact h

'''
    text += shape_foot(['all_rows', 'all_vertices_bang', 'all_vertices'])
    save('P2OriginalSaving19Geometry01Shape', text)
    return files, order


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--legacy-root', type=Path, default=DEFAULT_LEGACY)
    parser.add_argument('--repo-root', type=Path, default=DEFAULT_REPO)
    args = parser.parse_args()
    legacy, repo = args.legacy_root.resolve(), args.repo_root.resolve()
    assert str(repo).startswith('/tmp/'), 'Only the isolated /tmp checkout may be written.'
    progress = json.loads((legacy / 'PROGRESS.json').read_text())
    accepted = set(progress['accepted_owners'])
    assert len(accepted) == 96
    recovered = []
    for manifest in sorted((legacy / 'owners').glob('*.json')):
        owner = json.loads(manifest.read_text())
        source = Path(owner['source']['path'])
        assert fp(source) == owner['source']
        target = repo / 'ImbalancedChen' / source.name
        recovered.append({'module': owner['module'], 'source': write_exact(target, source.read_bytes()),
                          'original_source': owner['source'], 'owner_manifest': fp(manifest),
                          'status': 'normal_and_kernel_accepted' if owner['module'] in accepted else 'normal_only_kernel_receipt_missing'})
    assert len(recovered) == 97
    pinned = {
        'generate.py': '90410fd0d357d23aeec801eeb514b6d0abd77c39fcddc89c17b8e52af974ac46',
        'render_rows.py': '14fb8143546a9ad0260dee4416f5f9c7a8c92aef375f4476fccaf5f3337f8f6d',
        'quotation.py': 'fc122c1df0d10a295e759df63d2b804475a9bd8563f3608896fb7f17a741fc80',
        'raw_planner.py': '49c74fc7dc61c64a2519fb3fcce7ec571d097530840e0806d6af491f27ac8e18',
    }
    for name, digest in pinned.items():
        assert fp(legacy / name)['sha256'] == digest, ('Legacy renderer drift', name)
    sys.path.insert(0, str(legacy))
    g = importlib.import_module('generate')
    generated, order = [], []

    def save(short, source, obligations):
        source = source.replace('\ndef ', '\nnoncomputable def ')
        if short == 'P2OriginalSaving19Geometry01DirectPackedDecoded':
            short = 'P2OriginalSaving19Geometry01Decoded'
            source = source.replace('namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding', 'namespace ' + DECODE_NS)
            source = source.replace('end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding', 'end ' + DECODE_NS)
            source = source.replace('open ImbalancedChen.P2OriginalSaving19Geometry00Decoding',
                                    'open ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding')
        assert not re.search(r'\b(?:sorry|admit|native_decide|unsafe)\b|(?m:^\s*axiom\b)', source)
        result = {'module': 'ImbalancedChen.' + short,
                  'source': write_exact(repo / 'ImbalancedChen' / (short + '.lean'), source),
                  'planned_obligations': obligations, 'status': 'source_only_pending_cloud_compile_and_kernel_replay'}
        generated.append(result)
        order.append(result['module'])
        return result

    g.save = save
    for block in range(67, 73):
        g.block('simplices', block)
    g.complete()
    shape_files, shape_order = emit_shape(repo)
    report = {'cell': 1, 'raw_original': g.fp(g.RAW_PATH),
              'accepted_typed_owner_count': 96, 'normal_only_owner_count': 1,
              'normal_only_module': 'ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows066',
              'recovered': recovered, 'generated': generated,
              'shape_sources': shape_files,
              'cloud_order': ['KERNEL_REPLAY_ONLY ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows066'] + order + shape_order,
              'reused_generator_sources': [fp(legacy / name) for name in ['generate.py', 'render_rows.py', 'quotation.py', 'raw_planner.py']],
              'local_compiler_calls': 0, 'cloud_compiler_calls': 0,
              'source_is_proof': False, 'typed_geometry_proved_by_this_continuation': False}
    report_path = repo / 'docs/verification/20261126-p26/Geometry01Decoding_CONTINUATION.json'
    write_exact(report_path, json.dumps(report, indent=2) + '\n')
    print(json.dumps({'copied_sources': len(recovered), 'new_decoder_sources': len(generated),
                      'new_shape_sources': len(shape_files), 'report': str(report_path)}, indent=2))


if __name__ == '__main__':
    main()
