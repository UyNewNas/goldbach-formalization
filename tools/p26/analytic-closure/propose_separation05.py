"""Emit closed Lean candidates for proposed original Cell05 separators."""
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
INPUT = Path('/workspace/p26-separation05-20261128/PREFLIGHT.json')
PREFIX = 'P2OriginalSaving19Cell05Separation'


def candidates():
    data = json.loads(INPUT.read_text())
    assert data['formal_acceptance'] is False and data['pair_count'] == 1540 and not data['missing']
    raw = Path(data['source']['path']).read_bytes()
    assert len(raw) == data['source']['bytes']
    assert hashlib.sha256(raw).hexdigest() == data['source']['sha256']
    assert len(data['forms']) == 78
    pool = ',\n  '.join('![' + ', '.join('(' + str(x) + ' : ℚ)' for x in row) + ']'
                         for row in data['forms'])
    table = [[0] * 56 for _ in range(56)]
    for r, s, index in data['pairs']:
        assert 0 <= r < s < 56 and 0 <= index < 78
        table[r][s] = index
    selectors = ',\n  '.join('#[' + ', '.join(map(str, row)) + ']' for row in table)
    sources = {}
    sources['Data'] = f'''import ImbalancedChen.P2OriginalSaving19Cell05AllRowGaps

/-! Proposed separating forms; only later closed sign proofs grant credit.
The forms are witnesses, not trusted premises about original vertices. -/
namespace ImbalancedChen.{PREFIX}
noncomputable section
open scoped BigOperators
open P2OriginalSaving19RowNumericsPure P2OriginalSaving19Cell05AllRowGaps
abbrev Form := Fin 9 → ℚ
def pool : Array Form := #[
  {pool}]
def selectors : Array (Array ℕ) := #[
  {selectors}]
def separator (r s : Fin 56) : Form := pool[(selectors[r.val]!)[s.val]!]!
def evalQ (a : Form) (x : QPoint) : ℚ := a 0 + ∑ j : Fin 8, a j.succ * x j
def Checks (r s : Fin 56) : Prop :=
  (∃ j : Fin 8, separator r s j.succ ≠ 0) ∧
  (∀ i : Fin 9, 0 ≤ evalQ (separator r s) (boundedRowVertex05 r i)) ∧
  (∀ i : Fin 9, evalQ (separator r s) (boundedRowVertex05 s i) ≤ 0)
instance (r s : Fin 56) : Decidable (Checks r s) := by
  unfold Checks
  infer_instance
end
end ImbalancedChen.{PREFIX}
'''
    for block in range(14):
        name = f'Block{block:03d}'
        text = f'''import ImbalancedChen.{PREFIX}Data

/-! Closed signs on the actual parser-bound original vertices. -/
namespace ImbalancedChen.{PREFIX}.{name}
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
'''
        for r in range(block * 4, block * 4 + 4):
            text += f'''theorem row{r:03d} : ∀ s : Fin 56, ({r} : Fin 56) < s → Checks {r} s := by
  decide +kernel

'''
        text += f'end ImbalancedChen.{PREFIX}.{name}\n'
        sources[name] = text
    imports = '\n'.join(f'import ImbalancedChen.{PREFIX}Block{b:03d}' for b in range(14))
    text = f'''{imports}

/-! All 1,540 original Cell05 pairs have a proper separating affine form.
This finite theorem has no measure or integral conclusion. -/
namespace ImbalancedChen.{PREFIX}
theorem all_pairs (r s : Fin 56) (h : r < s) : Checks r s := by
  fin_cases r
'''
    for r in range(56):
        text += f'  · exact Block{r // 4:03d}.row{r:03d} s h\n'
    text += f'\n#print axioms all_pairs\nend ImbalancedChen.{PREFIX}\n'
    sources['Complete'] = text
    return sources


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--emit', action='store_true')
    args = parser.parse_args()
    sources = candidates()
    if args.emit:
        print('*** Begin Patch')
        for suffix, source in sources.items():
            target = ROOT / 'ImbalancedChen' / (PREFIX + suffix + '.lean')
            if target.exists():
                assert target.read_text() == source
                continue
            print('*** Add File: ' + str(target))
            print(''.join('+' + line + '\n' for line in source.splitlines()), end='')
        print('*** End Patch')
    else:
        print(json.dumps({'candidate_modules': len(sources),
                          'candidate_bytes': sum(len(s.encode()) for s in sources.values()),
                          'formal_acceptance': False}))


if __name__ == '__main__':
    main()
