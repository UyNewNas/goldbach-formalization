"""Emit original Cell00 finite-check candidates from exact proposed forms."""
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
INPUT = Path('/workspace/p26-cell00-next-20261128/SEPARATION_PROPOSAL.json')
PREFIX = 'P2OriginalSaving19Cell00Separation'


def candidates():
    data = json.loads(INPUT.read_text())
    assert data['formal_acceptance'] is False and data['pair_count'] == 1540 and not data['missing']
    raw = Path(data['source']['path']).read_bytes()
    assert len(raw) == data['source']['bytes'] and hashlib.sha256(raw).hexdigest() == data['source']['sha256']
    assert len(data['forms']) == 79 and data['rows'] == 56 and data['vertices'] == 28
    pool = ',\n  '.join('![' + ', '.join('(' + str(x) + ' : ℚ)' for x in row) + ']'
                         for row in data['forms'])
    table = [[0] * 56 for _ in range(56)]
    for r, s, index in data['pairs']:
        assert 0 <= r < s < 56 and 0 <= index < 79
        table[r][s] = index
    selectors = ',\n  '.join('#[' + ', '.join(map(str, row)) + ']' for row in table)
    sources = {'Data': f'''import ImbalancedChen.P2OriginalSaving19Geometry00BoundedAccess
import ImbalancedChen.P2OriginalSaving19RowNumericsPure

/-! Proposed rational forms; the closed sign proofs are separate.
All evaluations use the original parser-bound Cell00 coordinates. -/
namespace ImbalancedChen.{PREFIX}
noncomputable section
open scoped BigOperators
open P2OriginalSaving19RowNumericsPure P2OriginalSaving19Geometry00BoundedAccess
abbrev Form := Fin 9 → ℚ
def pool : Array Form := #[
  {pool}]
def selectors : Array (Array ℕ) := #[
  {selectors}]
def separator (r s : Fin 56) : Form := pool[(selectors[r.val]!)[s.val]!]!
def evalQ (a : Form) (x : QPoint) : ℚ := a 0 + ∑ j : Fin 8, a j.succ * x j
def Checks (r s : Fin 56) : Prop :=
  (∃ j : Fin 8, separator r s j.succ ≠ 0) ∧
  (∀ i : Fin 9, 0 ≤ evalQ (separator r s) (boundedRowVertex r i)) ∧
  (∀ i : Fin 9, evalQ (separator r s) (boundedRowVertex s i) ≤ 0)
instance (r s : Fin 56) : Decidable (Checks r s) := by
  unfold Checks
  infer_instance
end
end ImbalancedChen.{PREFIX}
'''}
    accepted = json.loads((ROOT / 'docs/verification/20261128-p26-cell05-integral/source/RUN.json').read_text())['project_closure']
    for suffix in [f'Block{i:03d}' for i in range(14)] + ['Complete']:
        name = 'ImbalancedChen.P2OriginalSaving19Cell05Separation' + suffix
        path = ROOT / (name.replace('.', '/') + '.lean')
        raw = path.read_bytes()
        assert hashlib.sha256(raw).hexdigest() == accepted[name]['source']['sha256']
        text = raw.decode().replace('P2OriginalSaving19Cell05Separation', PREFIX).replace('Cell05', 'Cell00')
        if suffix == 'Complete':
            text = 'import Mathlib.Tactic.FinCases\n' + text
        sources[suffix] = text
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
