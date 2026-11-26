#!/usr/bin/env python3
"""Field-wise certificates for the original GeometryRow decoder.

The raw span planner supplies candidate character/numeric quotations only.
Every getter, integer parse, rational parse and decoder composition is certified
by Lean against the reused original JSON AST and the unchanged ArchiveSchema.
"""
import argparse
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def row_short(index):
    return f'P2OriginalSaving19Geometry01DecodedRow{index:03d}'


def render_row(g, index):
    chunks = g.chunks_for(g.FIELDS['simplices'])
    chunk = next(c for c in chunks if c['first'] <= index < c['after'])
    block = chunk['index']
    imports = ['P2OriginalSaving19ArchiveRationalChars',
               f'P2OriginalSaving19Geometry01DirectSimplicesBlock{block:03d}']
    s = ''
    raw = g.item_name('Rows', index)
    typed = g.typed_name('Rows', index)
    node = g.FIELDS['simplices'].children[index]
    fields = {f.key.scalar: f.value for f in node.fields}
    prefix = f'geometryRow{index:03d}'
    names = []
    s += f'''def {raw} : SourceJson :=
  ({g.orig_push('simplices', chunk['index'])} []).get ⟨{chunk['after']-1-index}, by decide +kernel⟩

def {typed} : GeometryRow :=
  {g.record_value('simplices', node)}

'''
    for key, field, typ in [('simplex_id', 'simplexId', 'Nat'),
                            ('vertex_ids', 'vertexIds', '(Array Nat)')]:
        name = f'{prefix}_{field}_read'
        s += g.mark(f'Row_{index:03d}_{field}_before')
        s += f'''theorem {name} :
    {raw}.getObjValAs? {typ} "{key}" = .ok {typed}.{field} := by decide +kernel

'''
        names.append(name)
    for key, field in [('physical_volume', 'physicalVolume'),
                       ('mean_gap', 'meanGap'),
                       ('jensen_bound', 'jensenBound')]:
        token = fields[key].scalar
        parts = token.split('/')
        assert len(parts) == 2 and all(re.fullmatch(r'-?[0-9]+', x) for x in parts)
        numerator, denominator = parts
        stem = f'{prefix}_{field}'
        ns, ds = stem + 'NumeratorChars', stem + 'DenominatorChars'
        text = stem + 'Text'
        s += f'''def {ns} : List Char := {g.base.quote_list(numerator)}
def {ds} : List Char := {g.base.quote_list(denominator)}
def {text} : String := String.ofList ({ns} ++ '/' :: {ds})

'''
        s += g.mark(f'Row_{index:03d}_{field}_before_field')
        s += f'''theorem {stem}_field :
    {raw}.getObjVal? "{key}" = .ok (.str {text}) := by rfl

theorem {stem}_numerator_no_slash :
    {ns}.all (fun c => c != '/') = true := by decide +kernel

theorem {stem}_numerator_parse :
    SourceJson.intChars {ns} = some ({numerator} : Int) := by decide +kernel

theorem {stem}_denominator_parse :
    SourceJson.intChars {ds} = some ({denominator} : Int) := by decide +kernel

theorem {stem}_denominator_nonzero : ({denominator} : Int) ≠ 0 := by decide +kernel

theorem {stem}_parse :
    parseRational {text} = .ok {typed}.{field} :=
  original_rational_fraction_of_chars {ns} {ds}
    ({numerator} : Int) ({denominator} : Int)
    {stem}_numerator_no_slash {stem}_numerator_parse
    {stem}_denominator_parse {stem}_denominator_nonzero

theorem {stem}_read :
    rationalField {raw} "{key}" = .ok {typed}.{field} :=
  original_rationalField_of_string {raw} "{key}" {text}
    {typed}.{field} {stem}_field {stem}_parse

'''
        names += [stem + suffix for suffix in ['_field', '_numerator_no_slash',
                  '_numerator_parse', '_denominator_parse', '_denominator_nonzero', '_parse', '_read']]
        s += g.mark(f'Row_{index:03d}_{field}_complete')
    for key, field in [('factor_maxima', 'factorMaxima'), ('gap_weighted_means', 'gapWeightedMeans')]:
        name = f'{prefix}_{field}_read'
        s += g.mark(f'Row_{index:03d}_{field}_before')
        s += f'''theorem {name} :
    rationalArrayField {raw} "{key}" = .ok {typed}.{field} := by decide +kernel

'''
        names.append(name)
        s += g.mark(f'Row_{index:03d}_{field}_complete')
    floor = fields['jensen_floor_Q96'].scalar
    floor_text = f'{prefix}_floorText'
    floor_chars = f'{prefix}_floorChars'
    s += f'''def {floor_chars} : List Char := {g.base.quote_list(floor)}
def {floor_text} : String := String.ofList {floor_chars}

theorem {prefix}_floor_text_read :
    {raw}.getObjValAs? String "jensen_floor_Q96" = .ok {floor_text} := by rfl

theorem {prefix}_floor_chars_parse :
    SourceJson.intChars {floor_chars} = some ({floor} : Int) := by decide +kernel

theorem {prefix}_floor_parse :
    parseInteger {floor_text} = .ok {typed}.jensenFloorQ96 := by
  simp only [{floor_text}, parseInteger, String.toList_ofList, {prefix}_floor_chars_parse]
  rfl

theorem {g.decode_name('Rows', index)} :
    decodeGeometryRow {raw} = .ok {typed} :=
  original_geometryRow_of_fields {raw} {typed} {floor_text}
    {prefix}_simplexId_read {prefix}_vertexIds_read
    {prefix}_physicalVolume_read {prefix}_meanGap_read
    {prefix}_factorMaxima_read {prefix}_gapWeightedMeans_read
    {prefix}_jensenBound_read {prefix}_floor_text_read {prefix}_floor_parse

'''
    names += [prefix + '_floor_text_read', prefix + '_floor_chars_parse',
              prefix + '_floor_parse', g.decode_name('Rows', index)]
    s += g.mark(f'Row_{index:03d}_original_decoder_complete')
    return s, names, {
        'original_key': 'simplices', 'row_index': index,
        'original_raw_span': [node.start, node.end], 'source_chunk': chunk,
        'all_original_GeometryRow_schema_fields': 8,
        'vertex_ids_original_order_preserved': True,
        'original_JSON_getter_and_original_intChars_guards': True,
        'original_rational_slash_and_denominator_nonzero_checks': True,
        'whole_row_decide_replaced_with_opaque_field_composition': True,
        'original_decoder_unchanged': True,
        'candidate_rationals': 'exact source numerator/denominator expressions, no host normalization',
        'original_JSON_access': 'List.get with kernel-checked bound, no fallback'}
