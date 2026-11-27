"""Instantiate the accepted replay/audit procedure for the exact Cell01 join."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
STAGE = Path('/workspace/p26-cell01-next-20261128')
BASE = [
    'ImbalancedChen.P2OriginalSaving19Cell05SourceAttachment',
    'ImbalancedChen.P2OriginalSaving19Cell00SourceAttachment',
    'ImbalancedChen.P2OriginalSaving19Cell05GroupedSeparationComplete',
]
ROOT_MODULE = 'ImbalancedChen.P2OriginalSaving19Cell01Row000OriginalFloorBridge'


def main():
    modules = json.loads((STAGE / 'INCOMING_BASE_MODULES.json').read_text())
    assert len(modules) == len(set(modules)) == 407
    old = ROOT / 'tools/p26/cell00-integral'
    replay = (old / 'ReplayJoin.lean').read_text()
    replay = replay.replace('P26_CELL00', 'P26_CELL01').replace('wanted.size == 468', 'wanted.size == 407')
    start = replay.index('  let baseImports : Array Import := #[')
    end = replay.index('  let (_, fullState)', start)
    replay = replay[:start] + ('  let baseImports : Array Import := #[\n' +
        ',\n'.join('    { module := `' + n + ' }' for n in BASE) + ']\n' +
        '  let (_, baseState) ← (importModulesCore baseImports).run\n' +
        '  let base ← finalizeImport baseState baseImports {} 0 false false\n' +
        '  let allImports := baseImports ++ #[\n' +
        '    { module := `' + ROOT_MODULE + ' }]\n') + replay[end:]
    replay = replay.replace('ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic.geometryChars00',
                            'ImbalancedChen.P2OriginalSaving19Archive.geometryPacked01')
    replay = replay.replace('quotedCharacters geometry.value', 'quotedPackedCharacters geometry.value')
    replay = replay.replace('momentPacked00', 'momentPacked01').replace('low-00', 'low-01')
    (HERE / 'ReplayJoin.lean').write_text(replay)
    audit = (old / 'OwnedSuppliersAudit.lean').read_text()
    start = audit.index('import Lean.Util.CollectAxioms')
    audit = '\n'.join('import ' + n for n in BASE + [ROOT_MODULE]) + '\n' + audit[start:]
    start = audit.index('  for moduleName in #[')
    end = audit.index('] do\n    let some idx', start)
    audit = audit[:start] + '  for moduleName in #[\n' + ',\n'.join('      `' + n for n in modules) + audit[end:]
    audit = audit.replace('P26_CELL00', 'P26_CELL01').replace('p26SharedProofBodyCheck', 'p26Cell01SharedProofBodyCheck')
    (HERE / 'OwnedSuppliersAudit.lean').write_text(audit)
    print(json.dumps({'incoming_modules': len(modules), 'base_imports': BASE, 'root': ROOT_MODULE}))


if __name__ == '__main__':
    main()
