#!/usr/bin/env python3
"""Continue the accepted cell01 pilot on the unchanged production packed input.

Host plans are candidates. Only normal compilation plus independent kernel
receipts certify generated original-reader equations.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import sys

WORK = Path(__file__).resolve().parent
BASELINE = WORK.parents[1]
PILOT = WORK.parent / 'cell01-pilot-v1'
sys.path.insert(0, str(BASELINE))
from generate import Engine, fp, write_new, marker
import raw_planner as base
import fragment_templates as fragments


class FullEngine(Engine):
    def __init__(self):
        frozen = json.loads((BASELINE / 'SOURCE_ONLY_MANIFEST.json').read_text())
        for row in frozen['files']:
            assert all(fp(BASELINE / row['relative_path'])[k] == row[k]
                       for k in ['path', 'bytes', 'sha256'])
        super().__init__(1, Path('/workspace/p26-original-inputs') /
            'eighth-third-minorant-extension-20261009-a23-s23_low-01-cell.witness.json', WORK)
        self.field_index = {field.key.scalar: i for i, field in enumerate(self.node.fields)}

    def prepare_frozen(self):
        accepted = json.loads((PILOT / 'SOURCE_INPUTS.json').read_text())['inputs']
        rows = []
        for row in accepted:
            assert fp(row['source']['path']) == row['source']
            assert fp(row['object']['path']) == row['object']
            rows.append({k: row[k] for k in ['module', 'source', 'object', 'project_imports']})
        assert len(rows) == 10
        write_new(WORK / 'FROZEN_SUPPLIERS.json', json.dumps({
            'inputs': rows, 'accepted_pilot_manifest': fp(PILOT / 'SOURCE_MANIFEST.json'),
            'baseline_manifest': fp(BASELINE / 'SOURCE_ONLY_MANIFEST.json'),
            'published_pilot_commit': '94148a71e2bc9b6627a98eeebd961f78076b4f08',
            'recompiled': False, 'cell00_geometry_modules_imported': False}, indent=2) + '\n')
        write_new(WORK / 'run_owner.py', (PILOT / 'run_owner.py').read_bytes())

    def save(self, short, text, scope, plan):
        frozen_modules = {row['module'] for row in
            json.loads((WORK / 'FROZEN_SUPPLIERS.json').read_text())['inputs']}
        assert 'ImbalancedChen.' + short not in frozen_modules, 'Accepted owner must only be reused.'
        text = text.replace('\ndef ', '\nnoncomputable def ')
        path = self.project / 'ImbalancedChen' / (short + '.lean')
        write_new(path, text)
        imports = re.findall(r'(?m)^import\s+(ImbalancedChen\.\S+)', text)
        known = self.registry()
        seen, closure = set(), []

        def visit(module):
            if module in seen:
                return
            seen.add(module)
            row = known[module]
            assert fp(row['source']['path']) == row['source']
            for dep in row['project_imports']:
                visit(dep)
            closure.append(row)

        for module in imports:
            visit(module)
        record = {
            'module': 'ImbalancedChen.' + short, 'source': fp(path), 'scope': scope,
            'project_imports': imports, 'dependency_closure': closure,
            'fixture': fp(self.fixture), 'planned_obligations': plan,
            'production_input_FQN': self.expected['definition'],
            'generator': fp(Path(__file__)),
            'whole_cell_parse_claimed': bool(plan.get('whole_parse_success_theorem', False)),
            'all13_pass_claimed': False, 'host_plan_is_proof': False,
            'production_modified': False, 'remote_jobs_submitted': False,
            'accepted_dependencies_recompiled': False,
        }
        write_new(WORK / 'owners' / (short + '.json'), json.dumps(record, indent=2) + '\n')
        return record

    def block_plan(self, key):
        node = self.fields[key].value
        chunks = self.chunks_for(node)
        groups = []
        if key == 'active8_enumeration':
            old = json.loads((PILOT / 'owners' /
                (self.tag + 'Active8EnumerationBlock000.json')).read_text())
            assert chunks[:4] == old['planned_obligations']['selected_chunks']
            groups.append(chunks[:4])
            chunks = chunks[4:]
        group = []
        for chunk in chunks:
            if group and (len(group) == 8 or chunk['end'] - group[0]['start'] > 4096):
                groups.append(group)
                group = []
            group.append(chunk)
        if group:
            groups.append(group)
        return node, groups

    def field_tag(self, key):
        return ''.join(part.title() for part in key.split('_'))

    def prior(self, key):
        index = self.field_index[key]
        assert index >= 5
        if index == 5:
            return ('ImbalancedChen.' + self.tag + 'Metadata05',
                    'Metadata05.metadataAcc', 'Metadata05.sourceChars_through_metadata')
        prior_key = self.node.fields[index - 1].key.scalar
        tag = self.field_tag(prior_key)
        return ('ImbalancedChen.' + self.tag + tag + 'Field',
                tag + 'Field.fieldAcc', tag + 'Field.sourceChars_through_field')

    def field_header(self, key):
        field = self.fields[key]
        node = field.value
        index = self.field_index[key]
        prior_module, prior_acc, prior_whole = self.prior(key)
        tag = self.field_tag(key)
        nested = tag + 'Field'
        short = self.tag + tag + 'Header'
        need = 1 + max(field.key.quoted_need, node.need)
        actual = len(self.raw) - index
        text = self.head([prior_module], 'Exact original object header; unchanged duplicate-key and error branches.')
        text += f'namespace {nested}\n\n'
        text += f'''def headerChars : List Char := {base.chars(self.raw, field.prefix_start, node.start)}
def fieldKey : String := String.ofList {base.quote_list(key)}
def afterValue (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}}' :: ending => .ok (.obj (((fieldKey, result.1) :: {prior_acc}).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fieldKey, result.1) :: {prior_acc})
  | _ => .error "object separator missing"

theorem object_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + {need}) (SourceJson.white (headerChars ++ rest)) {prior_acc} =
      (SourceJson.value (fuel + {need-1}) rest).bind (afterValue (fuel + {need-1})) := by rfl

'''
        text += self.emit_split('header_original', field.prefix_start, node.start, 'headerChars')
        text += f'''theorem object_original_header (fuel : Nat) :
    SourceJson.object (fuel + {need}) (SourceJson.white (sourceRest {field.prefix_start})) {prior_acc} =
      (SourceJson.value (fuel + {need-1}) (sourceRest {node.start})).bind (afterValue (fuel + {need-1})) :=
  (congrArg (fun chars => SourceJson.object (fuel + {need}) (SourceJson.white chars) {prior_acc})
    header_original_split).trans (object_header fuel (sourceRest {node.start}))

theorem sourceChars_pending_value :
    SourceJson.value {len(self.raw)+1} sourceChars =
      (SourceJson.value {actual-1} (sourceRest {node.start})).bind (afterValue {actual-1}) :=
  {prior_whole}.trans (object_original_header {actual-need})

'''
        text += self.foot(['object_header', 'header_original_prefix', 'header_original_split',
                          'object_original_header', 'sourceChars_pending_value'], nested)
        return self.save(short, text, 'Original parent header and real pending value continuation',
                         {'key': key, 'header_span': [field.prefix_start, node.start],
                          'actual_object_fuel': actual, 'value_fuel_offset': node.need,
                          'field_value_not_yet_discharged': True})

    def array_value(self, key):
        node, groups = self.block_plan(key)
        tag = self.field_tag(key)
        nested = tag + 'Value'
        blocks = [tag + f'Block{i:03d}' for i in range(len(groups))]
        imports = ['ImbalancedChen.' + self.tag + name for name in blocks]
        text = self.head(imports, f'Composition of every original {key} block; no full-array reduction.')
        text += f"namespace {nested}\n\ndef arrayOpenChars : List Char := ['[']\n"
        text += 'def arrayAcc000 : List SourceJson := []\n'
        for i, block in enumerate(blocks):
            text += f'def arrayAcc{i+1:03d} : List SourceJson := {block}.blockPush arrayAcc{i:03d}\n'
        text += f'def arrayValue : SourceJson := .arr (arrayAcc{len(groups):03d}.reverse)\n\n'
        text += self.emit_split('array_open', node.start, node.start + 1, 'arrayOpenChars')
        text += f'''theorem value_array_open (fuel : Nat) :
    SourceJson.value (fuel + {node.need}) (sourceRest {node.start}) =
      SourceJson.array (fuel + {node.need-1}) (SourceJson.white (sourceRest {node.start+1})) [] :=
  (congrArg (SourceJson.value (fuel + {node.need})) array_open_split).trans (by rfl)

theorem array_all_blocks (fuel : Nat) :
    SourceJson.array (fuel + {node.need-1}) (SourceJson.white (sourceRest {node.start+1})) [] =
      .ok (arrayValue, sourceRest {node.end}) := by
  calc
'''
        for i, (block, selected) in enumerate(zip(blocks, groups)):
            lhs = f'SourceJson.array (fuel + {node.need-1}) (SourceJson.white (sourceRest {node.start+1})) []' if i == 0 else '_'
            last = selected[-1]
            rhs = (f'.ok (arrayValue, sourceRest {node.end})' if last['final'] else
                   f'SourceJson.array (fuel + {last["after_offset"]}) (SourceJson.white (sourceRest {last["end"]})) arrayAcc{i+1:03d}')
            text += f'    {lhs} = {rhs} := {block}.array_block_original fuel arrayAcc{i:03d}\n'
        text += f'''
theorem value_array_original (fuel : Nat) :
    SourceJson.value (fuel + {node.need}) (sourceRest {node.start}) =
      .ok (arrayValue, sourceRest {node.end}) :=
  (value_array_open fuel).trans (array_all_blocks fuel)

'''
        text += self.foot(['array_open_prefix', 'array_open_split', 'value_array_open',
                          'array_all_blocks', 'value_array_original'], nested)
        return self.save(self.tag + tag + 'Value', text, 'Complete original array value equation, exact original remainder',
                         {'key': key, 'array_span': [node.start, node.end], 'items': len(node.children),
                          'blocks': len(groups), 'complete_array_value_proved': True})

    def array_field(self, key):
        field = self.fields[key]
        node = field.value
        index = self.field_index[key]
        prior_module, prior_acc, prior_whole = self.prior(key)
        tag = self.field_tag(key)
        nested = tag + 'Field'
        value = tag + 'Value.arrayValue'
        value_theorem = tag + 'Value.value_array_original'
        need = 1 + max(field.key.quoted_need, node.need)
        actual = len(self.raw) - index
        assert field.separator == ','
        text = self.head(['ImbalancedChen.' + self.tag + tag + 'Header',
                          'ImbalancedChen.' + self.tag + tag + 'Value'],
                         'Insert the completed original array into its original parent object.')
        text += f'''namespace {nested}

def separatorChars : List Char := {base.chars(self.raw, node.end, field.prefix_end)}
def fieldAcc : List (String × SourceJson) := (fieldKey, {value}) :: {prior_acc}

theorem after_value_separator (fuel : Nat) (tail : List Char) :
    (Except.ok ({value}, separatorChars ++ tail)).bind (afterValue (fuel + {need-1})) =
      SourceJson.object (fuel + {need-1}) (SourceJson.white tail) fieldAcc := by rfl

'''
        text += self.emit_split('separator_original', node.end, field.prefix_end, 'separatorChars')
        text += f'''theorem object_original_field (fuel : Nat) :
    SourceJson.object (fuel + {need}) (SourceJson.white (sourceRest {field.prefix_start})) {prior_acc} =
      SourceJson.object (fuel + {need-1}) (SourceJson.white (sourceRest {field.prefix_end})) fieldAcc := by
  calc
    SourceJson.object (fuel + {need}) (SourceJson.white (sourceRest {field.prefix_start})) {prior_acc} =
        (SourceJson.value (fuel + {need-1}) (sourceRest {node.start})).bind (afterValue (fuel + {need-1})) :=
      object_original_header fuel
    _ = (Except.ok ({value}, sourceRest {node.end})).bind (afterValue (fuel + {need-1})) :=
      congrArg (fun result => result.bind (afterValue (fuel + {need-1})))
        ({value_theorem} (fuel + {need-1-node.need}))
    _ = (Except.ok ({value}, separatorChars ++ sourceRest {field.prefix_end})).bind
          (afterValue (fuel + {need-1})) :=
      congrArg (fun rest => (Except.ok ({value}, rest)).bind (afterValue (fuel + {need-1})))
        separator_original_split
    _ = SourceJson.object (fuel + {need-1}) (SourceJson.white (sourceRest {field.prefix_end})) fieldAcc :=
      after_value_separator fuel (sourceRest {field.prefix_end})

theorem sourceChars_through_field :
    SourceJson.value {len(self.raw)+1} sourceChars =
      SourceJson.object {actual-1} (SourceJson.white (sourceRest {field.prefix_end})) fieldAcc :=
  {prior_whole}.trans (object_original_field {actual-need})

'''
        text += self.foot(['after_value_separator', 'separator_original_prefix', 'separator_original_split',
                          'object_original_field', 'sourceChars_through_field'], nested)
        return self.save(self.tag + tag + 'Field', text, 'Complete original field and exact next root-object state',
                         {'key': key, 'field_span': [field.prefix_start, field.prefix_end],
                          'actual_object_fuels': [actual, actual-1], 'complete_field_proved': True})


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('action', choices=['prepare', 'header', 'block', 'value', 'field'])
    ap.add_argument('--key', default='active8_enumeration')
    ap.add_argument('--block', type=int, default=1)
    args = ap.parse_args()
    engine = FullEngine()
    if args.action == 'prepare':
        node, groups = engine.block_plan(args.key)
        print(json.dumps({'key': args.key, 'items': len(node.children), 'blocks': len(groups),
                          'frozen_pilot_block_reused': True, 'remaining_raw_spans':
                          [[g[0]['start'], g[-1]['end']] for g in groups[1:]]}, indent=2))
    else:
        record = {'header': lambda: engine.field_header(args.key),
                  'block': lambda: engine.array_block_owner(args.key, args.block),
                  'value': lambda: engine.array_value(args.key),
                  'field': lambda: engine.array_field(args.key)}[args.action]()
        print(json.dumps({k: record[k] for k in ['module', 'source', 'planned_obligations']}, indent=2))
