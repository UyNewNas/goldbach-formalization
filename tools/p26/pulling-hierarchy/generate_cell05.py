"""Generate a small original-data pilot for the scalable sibling certificates."""
import hashlib
import json
from pathlib import Path

ROOT = Path('/workspace/p26-proof-continuation-20261127')
STAGE = Path('/workspace/p26-cell00-next-20261128')
data = json.loads((STAGE / 'PULLING_FORMS_05.json').read_text())
assert data['formal_acceptance'] is False and data['rows'] == 56
raw = Path(data['source']['resolved_actual_path']).read_bytes()
assert hashlib.sha256(raw).hexdigest() == data['source']['sha256']
assert len(data['nodes']) == 49 and sum(len(n['separators']) for n in data['nodes']) == 61
namespace = 'ImbalancedChen.P2OriginalSaving19Cell05GroupedSeparation'
prefix = 'P2OriginalSaving19Cell05GroupedSeparation'


def leaves(ref):
    if 'row' in ref:
        return '[' + str(ref['row']) + ']'
    return f'leaves{ref["node"]:03d}'


def groups(node):
    return '[' + ', '.join(leaves(child) for child in node['children']) + ']'


def mem_cases(count, expression):
    if count == 1:
        return ['  simpa only [List.mem_singleton] using ' + expression]
    return []


def member_proof(references, values):
    assert len(references) == len(values) and values

    def cases(proofs):
        if len(proofs) == 1:
            return ['have h := List.mem_singleton.mp hg', 'subst group', 'exact ' + proofs[0]]
        rest = cases(proofs[1:])
        return ['rcases List.mem_cons.mp hg with h | hg',
                '· subst group', '  exact ' + proofs[0],
                '· ' + rest[0], *['  ' + line for line in rest[1:]]]

    lines = ['intro group hg', *cases(values)]
    return 'by\n' + '\n'.join('    ' + line for line in lines)


def pairwise_term(node_id, child_count, start=0):
    if start + 1 == child_count:
        return '(by simp only [List.pairwise_singleton])'
    refs = list(range(start + 1, child_count))
    values = [f'sep{node_id:03d}_{start}_{j}' for j in refs]
    head = member_proof(refs, values)
    tail = pairwise_term(node_id, child_count, start + 1)
    return '(List.Pairwise.cons (' + head + ') ' + tail + ')'


header = f'''import ImbalancedChen.P2OriginalSaving19Cell05AllRowGaps
import ImbalancedChen.P2OriginalSaving19GroupedSeparation

/-! Original Cell05 sibling-cone candidate coefficients and row groups.
All numerical and group-coverage obligations are checked in later owners. -/
namespace {namespace}
noncomputable section
open P2OriginalSaving19GroupedSeparation
open P2OriginalSaving19RationalAffineSeparator
open P2OriginalSaving19Cell05AllRowGaps
'''
texts = {}
forms = ',\n  '.join('![' + ', '.join(f'({x} : ℚ)' for x in row) + ']' for row in data['forms'])
body = f'def forms : Array Form := #[\n  {forms}]\n'
for i, node in enumerate(data['nodes']):
    body += f'def leaves{i:03d} : List (Fin 56) := List.flatten {groups(node)}\n'
body += f'def rootLeaves : List (Fin 56) := {leaves(data["root"])}\n'
texts['Data'] = header + body + f'end\nend {namespace}\n'
body = f'''import ImbalancedChen.{prefix}Data
namespace {namespace}
noncomputable section
open P2OriginalSaving19GroupedSeparation
open P2OriginalSaving19Cell05AllRowGaps
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
'''
for i, node in enumerate(data['nodes']):
    for a, b, form in node['separators']:
        body += f'''theorem sep{i:03d}_{a}_{b} :
    Separated boundedRowVertex05 {leaves(node['children'][a])} {leaves(node['children'][b])} := by
  refine ⟨forms[{form}]!, ?_⟩
  decide +kernel
'''
texts['Signs'] = body + f'end\nend {namespace}\n'
body = f'''import ImbalancedChen.{prefix}Signs
import ImbalancedChen.P2OriginalSaving19Cell05PhysicalMomentRow
namespace {namespace}
noncomputable section
open MeasureTheory
open P2OriginalSaving19GroupedSeparation
open P2OriginalSaving19Cell05AllRowGaps
open P2OriginalSaving19Cell05PhysicalMomentRow
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def Rel (r s : Fin 56) : Prop := AEDisjoint volume (physicalSimplex r) (physicalSimplex s)
'''
for i, node in enumerate(data['nodes']):
    values = [('(by simp only [List.pairwise_singleton])' if 'row' in child
               else f'node{child["node"]:03d}') for child in node['children']]
    inside = member_proof(node['children'], values)
    between = pairwise_term(i, len(node['children']))
    body += f'''theorem node{i:03d} : leaves{i:03d}.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices {groups(node)}
    ({inside})
    {between}
'''
body += f'''theorem original_root_cover : ∀ r : Fin 56, r ∈ rootLeaves := by
  decide +kernel
theorem all_original_pairs : Pairwise Rel :=
  pairwise_from_cover (fun r => (row r).linear) (fun r => (row r).base)
    rootLeaves original_root_cover node{data['root']['node']:03d}
#print axioms all_original_pairs
end
end {namespace}
'''
texts['Complete'] = body
patch = '*** Begin Patch\n'
for suffix, text in texts.items():
    target = ROOT / 'ImbalancedChen' / (prefix + suffix + '.lean')
    patch += '*** Add File: ' + str(target) + '\n'
    patch += ''.join('+' + line + '\n' for line in text.splitlines())
patch += '*** End Patch\n'
(STAGE / 'grouped05.patch').write_text(patch)
print({'modules': len(texts), 'bytes': sum(len(t.encode()) for t in texts.values()),
       'sibling_separators': 61, 'original_rows': 56, 'formal_acceptance': False})
