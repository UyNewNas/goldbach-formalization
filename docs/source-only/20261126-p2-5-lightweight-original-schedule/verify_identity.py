#!/usr/bin/env python3
"""Check or prepare the literal source-only ordinary-schedule owner relocation.

No Lean, Lake, network, git mutation, source installation, or acceptance gate
is invoked. --write writes only inside this package. Without it, all frozen
preimages/postimages and declaration-identity evidence must already match.
"""
from pathlib import Path
import argparse
import difflib
import hashlib
import json
import re
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
BASE = ROOT / 'docs/source-only/20261125-p2-5-fourteen-family/PREIMAGE_CLOSURE_SELECTION_1688.json'
PREFIX = 'ImbalancedChen.'
PATHS = {
    'P4AOriginalFull87ActualSavedEndpoint': 'docs/source-only/20261110-yellow-closure-10t/t03_saved87_actual_gain/P4AOriginalFull87ActualSavedEndpoint.lean',
    'P4AOriginalR17Full87SavedEndpoint': 'docs/source-only/20261110-yellow-closure-10t/t03_saved87_actual_gain/successor_R17_transport/P4AOriginalR17Full87SavedEndpoint.lean',
    'P4AOriginalArchiveFourteenPositivePresieve': 'docs/source-only/20261102-resume-30r/all22_actual_sources/P4AOriginalArchiveFourteenPositivePresieve.lean',
    'P4AOriginalR17PaidIntegral': 'docs/source-only/20261123-resume/ten-task-continuation/selected-api/ImbalancedChen/P4AOriginalR17PaidIntegral.lean',
    'P4AOriginalCompleteSixthChronology': 'docs/source-only/20261102-resume-30s/s09_actual_full_sixth/P4AOriginalCompleteSixthChronology.lean',
    'P4AOriginalCatalogFiveArchiveSchedule': 'docs/source-only/20261102-resume-30s/s13_all22_actual_ledger/P4AOriginalCatalogFiveArchiveSchedule.lean',
    'P4AOriginalFull87SourceDispatch': 'docs/source-only/20261102-resume-30s/s10_full87_actual_history/P4AOriginalFull87SourceDispatch.lean',
    'P4AOriginalOrderedThirdFullPolicy': 'docs/source-only/20261110-yellow-closure-10t/t04_compiler_physical_payment/successor/P4AOriginalOrderedThirdFullPolicy.lean',
    'P4AOriginalHistoricalFirstStop': 'docs/source-only/20261110-yellow-closure-10t/t05_all22_actual_density/P4AOriginalHistoricalFirstStop.lean',
    'P4AOriginalHistoricalThirdOccurrence': 'docs/source-only/20261110-yellow-closure-10t/t05_all22_actual_density/P4AOriginalHistoricalThirdOccurrence.lean',
    'P4AOriginalHistoricalThirdActualRoot': 'docs/source-only/20261110-yellow-closure-10t/t05_all22_actual_density/P4AOriginalHistoricalThirdActualRoot.lean',
    'P4AOriginalThirdFallbackOccurrence': 'docs/source-only/20261110-yellow-closure-10t/t05_all22_actual_density/P4AOriginalThirdFallbackOccurrence.lean',
}


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def json_bytes(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode()


def source_declarations(raw):
    return re.findall(rb'^(?:(?:private|protected|noncomputable) )*(?:def|abbrev|theorem|lemma|structure|inductive|instance)\s+([^\s(:]+)', raw, re.M)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--write', action='store_true')
    args = ap.parse_args()
    selected = {r['module']: r for r in json.loads(BASE.read_text())['modules']}
    origins = {name: (ROOT / path).read_bytes() for name, path in PATHS.items()}
    before = dict(origins)
    for name, raw in before.items():
        row = selected[PREFIX + name]
        for repair in row.get('published_install_transform', []):
            old, new = repair['old'].encode(), repair['new'].encode()
            assert raw.count(old) == repair['count'], name
            raw = raw.replace(old, new, repair['count'])
        assert digest(raw) == row['sha256'], name
        before[name] = raw
    after = dict(before)
    replacement_log = {name: [] for name in before}

    def replace(name, old, new, purpose):
        assert after[name].count(old) == 1, (name, old[:80])
        replacement_log[name].append({'old': old.decode(), 'new': new.decode(), 'purpose': purpose})
        after[name] = after[name].replace(old, new, 1)

    def block(owner, first, following):
        raw = before[owner]
        begin = raw.index(first)
        finish = raw.index(following, begin)
        return raw[begin:finish]

    endpoint = 'P4AOriginalFull87ActualSavedEndpoint'
    r17 = 'P4AOriginalR17Full87SavedEndpoint'
    archive = 'P4AOriginalArchiveFourteenPositivePresieve'
    scheduled = block(endpoint, b'/-- The trim and resolution,', b'private theorem scheduled_mono')
    ordinary = block(r17, b'def Ordinary ', b'def PositivePresieve ')
    helper = block(r17, b'/-- Refine only the existing common third mesh thresholds.', b'theorem original_ordinary_source ')
    ordinary_source = block(r17, b'theorem original_ordinary_source ', b'theorem original_ordinary_saved ')
    schedule = block(archive, b'/-- The same pre-N archive schedule with the actual fourth bank. -/', b'def data ')
    data = block(archive, b'def data ', b'theorem data_eq_original_heldData ')
    helper_public = helper.replace(b'private theorem with_common_history', b'theorem with_common_history', 1)
    assert helper_public != helper and helper.count(b'private theorem with_common_history') == 1

    new = {
        'P4AOriginalFull87ScheduleDefinitions': (
            'import Mathlib.Data.Real.Basic\nimport Mathlib.Algebra.Ring.Parity\n\n'
            '/-! Source-only relocation of the existing Scheduled definition.\n'
            'Its formula and original namespace are unchanged; no numerical endpoint is imported. -/\n'
            'namespace ImbalancedChen.P4AOriginalFull87ActualSavedEndpoint\n'
            'noncomputable section\n\n').encode() + scheduled + b'end\nend ImbalancedChen.P4AOriginalFull87ActualSavedEndpoint\n',
        'P4AOriginalR17OrdinarySource': (
            'import ImbalancedChen.P4AOriginalFull87ScheduleDefinitions\n'
            'import ImbalancedChen.P4AOriginalR17EighthSignedTransport\n'
            'import ImbalancedChen.P4AOriginalFull87UnionActualGain\n\n'
            '/-! Source-only relocation of the existing ordinary integral source.\n'
            'All formulas and proof bodies are retained. The existing common-history\n'
            'helper is public solely so the original saved endpoint can still call it. -/\n'
            'namespace ImbalancedChen.P4AOriginalR17Full87SavedEndpoint\n'
            'noncomputable section\n'
            'open scoped Classical BigOperators\n'
            'open VariableEnvelope (mu)\n'
            'open P4AOriginalFull87SourceDictionary (Cell)\n'
            'open P4AOriginalFull87SourcePrimeTests (cellIntegral)\n'
            'open P4AOriginalFull87ActualSavedEndpoint (Scheduled)\n'
            'open P4AOriginalFull87UnionHistory (sixthPolicy policy)\n'
            'open P4AOriginalFull87HistoryCore (width)\n'
            'open P4AOriginalFull87OrdinarySignedGain (common_history_on_trim)\n'
            'open P4AOriginalR17EighthParent (orderedSixth orderedEighth)\n'
            'open P4AOriginalR17EighthSignedTransport (raw_difference)\n'
            'open P4AOriginalVariableFifthPhysicalLedger (raw physical)\n'
            'open P5OriginalCommonPositivePresieve (normalize)\n\n').encode() + ordinary + helper_public + ordinary_source + b'end\nend ImbalancedChen.P4AOriginalR17Full87SavedEndpoint\n',
        'P4AOriginalArchiveScheduleData': (
            'import ImbalancedChen.P5OriginalFourthFifthSourceInputs\n'
            'import ImbalancedChen.P4AOriginalCommonArchiveSchedule\n\n'
            '/-! Source-only relocation of the existing actual archive schedule/data.\n'
            'The fixed schedule, original byte bank and admission filter are unchanged. -/\n'
            'namespace ImbalancedChen.P4AOriginalArchiveFourteenPositivePresieve\n'
            'noncomputable section\n'
            'open scoped Classical BigOperators\n'
            'open P5OriginalCommonRefinedConstructor P5OriginalFourthFifthSourceInputs\n'
            'open P4AOriginalCausalHistory P4AOriginalCommonArchiveSchedule\n\n').encode() + schedule + data + b'end\nend ImbalancedChen.P4AOriginalArchiveFourteenPositivePresieve\n',
    }
    moves = [
        (endpoint, 'Scheduled', 'P4AOriginalFull87ScheduleDefinitions', scheduled, scheduled),
        (r17, 'Ordinary', 'P4AOriginalR17OrdinarySource', ordinary, ordinary),
        (r17, 'with_common_history', 'P4AOriginalR17OrdinarySource', helper, helper_public),
        (r17, 'original_ordinary_source', 'P4AOriginalR17OrdinarySource', ordinary_source, ordinary_source),
        (archive, 'schedule', 'P4AOriginalArchiveScheduleData', schedule, schedule),
        (archive, 'data', 'P4AOriginalArchiveScheduleData', data, data),
    ]
    for owner, name, target, old, moved in moves:
        replace(owner, old, b'', 'Relocate ' + name + ' to ' + target + ' without duplicate definition')
        assert new[target].count(moved) == 1
    for name, target in [(endpoint, 'P4AOriginalFull87ScheduleDefinitions'), (r17, 'P4AOriginalR17OrdinarySource'), (archive, 'P4AOriginalArchiveScheduleData')]:
        first = before[name].splitlines(keepends=True)[0]
        replace(name, first, ('import ImbalancedChen.' + target + '\n').encode() + first, 'Import relocated declarations under their original namespaces')
    replace('P4AOriginalR17PaidIntegral', b'import ImbalancedChen.P4AOriginalR17Full87SavedEndpoint\n',
            b'import ImbalancedChen.P4AOriginalR17OrdinarySource\n', 'Only original_ordinary_source is consumed; retain the entire selected-api theorem body')
    for name in ['P4AOriginalCompleteSixthChronology', 'P4AOriginalCatalogFiveArchiveSchedule', 'P4AOriginalFull87SourceDispatch']:
        replace(name, b'import ImbalancedChen.P4AOriginalArchiveFourteenPositivePresieve',
                b'import ImbalancedChen.P4AOriginalArchiveScheduleData', 'Consume the unchanged actual schedule/data without the closed fourteen numeric endpoint')
    replace('P4AOriginalOrderedThirdFullPolicy', b'import ImbalancedChen.P4AOriginalNewFifthCounting\n',
            b'import ImbalancedChen.P4AOriginalFull87DataPolicy\n', 'Use the existing finite policy provider; no NewFifthCounting declaration is referenced')
    replace('P4AOriginalHistoricalFirstStop', b'import ImbalancedChen.P4AOriginalThirdFallbackPaidDensity\n',
            b'import ImbalancedChen.P4AOriginalFull87RawChronology\nimport ImbalancedChen.P4ASameRhoCompact\n',
            'Use the referenced raw chronology and original ordinary root instead of the later paid density endpoint')
    replace('P4AOriginalHistoricalThirdOccurrence', b'import ImbalancedChen.P4AOriginalHistoricalFirstStop\n',
            b'import ImbalancedChen.P4AOriginalHistoricalFirstStop\nimport ImbalancedChen.P4AOriginalThirdFallbackAdmission\n',
            'Retain the directly used admission source after removing the accidental transitive import')
    replace('P4AOriginalHistoricalThirdActualRoot', b'import ImbalancedChen.P4AOriginalHistoricalThirdMajorant\n',
            b'import ImbalancedChen.P4AOriginalHistoricalThirdMajorant\nimport ImbalancedChen.P4AOriginalFourPositiveEndpoints\nimport ImbalancedChen.P4AOriginalNewFifthUnion\nimport ImbalancedChen.P4AOriginalFull87JointPhysicalBudget\n',
            'Retain exactly referenced endpoints/union/budget providers after the transitive paid-density import is removed')
    replace('P4AOriginalThirdFallbackOccurrence', b'import ImbalancedChen.P4AOriginalNewFifthPaidDensity\n',
            b'import ImbalancedChen.P4AOriginalFull87RawChronology\nimport ImbalancedChen.P4AOriginalNewFifthUnion\n',
            'Use only the actual raw third increment and concrete data; no NewFifthPaidDensity declaration is referenced')

    files = {}
    identity_moves = []
    for owner, name, target, old, moved in moves:
        declaration = re.search(rb'^(?:private )?(?:def|theorem) ' + name.encode() + rb'\b', old, re.M)
        assert declaration is not None
        old_command = old[declaration.start():].rstrip()
        new_command = old_command.removeprefix(b'private ') if name == 'with_common_history' else old_command
        assert new_command in new[target]
        old_visible = old_command.removeprefix(b'private ')
        assert old_visible == new_command
        identity_moves.append({
            'original_owner': PREFIX + owner, 'new_owner': PREFIX + target,
            'declaration': PREFIX + owner + '.' + name,
            'old_command_sha256': digest(old_command), 'new_command_sha256': digest(new_command),
            'statement_and_body_bytes_unchanged': True,
            'visibility_change': 'private_to_public_existing_helper' if name == 'with_common_history' else None,
            'declaration_bytes_identical': old_command == new_command,
            'new_mathematical_statement': False,
        })
    owner_rows = []
    for name, raw in before.items():
        reconstructed = raw
        for change in replacement_log[name]:
            old, replacement = change['old'].encode(), change['new'].encode()
            assert reconstructed.count(old) == 1
            reconstructed = reconstructed.replace(old, replacement, 1)
        assert reconstructed == after[name]
        removed = {declaration for owner, declaration, *_ in moves if owner == name}
        assert [n.decode() for n in source_declarations(after[name])] == [n.decode() for n in source_declarations(raw) if n.decode() not in removed]
        before_path = 'before/ImbalancedChen/' + name + '.lean'
        after_path = 'after/ImbalancedChen/' + name + '.lean'
        files[before_path], files[after_path] = raw, after[name]
        if origins[name] != raw:
            files['archived-origin/ImbalancedChen/' + name + '.lean'] = origins[name]
        owner_rows.append({'module': PREFIX + name, 'origin_path': PATHS[name],
                           'archived_origin_sha256': digest(origins[name]),
                           'previously_selected_context_repairs_reused': selected[PREFIX + name].get('published_install_transform', []),
                           'before_path': before_path, 'before_sha256': digest(raw),
                           'after_path': after_path, 'after_sha256': digest(after[name]),
                           'source_declarations_before': len(source_declarations(raw)),
                           'source_declarations_after': len(source_declarations(after[name])),
                           'all_retained_declaration_bytes_unchanged': True,
                           'exact_changes': replacement_log[name]})
    new_rows = []
    for name, raw in new.items():
        path = 'ImbalancedChen/' + name + '.lean'
        files[path] = raw
        new_rows.append({'module': PREFIX + name, 'path': path, 'sha256': digest(raw), 'bytes': len(raw),
                         'source_declarations': [n.decode() for n in source_declarations(raw)]})
    receipt = {'schema': 'p25-lightweight-ordinary-schedule-declaration-identity-v1',
               'status': 'SOURCE_ONLY_NOT_COMPILED_NO_ACCEPTANCE',
               'baseline_selection': {'path': str(BASE.relative_to(ROOT)), 'sha256': digest(BASE.read_bytes())},
               'moves': identity_moves, 'old_owner_postimages': owner_rows, 'new_owners': new_rows,
               'source_declarations_moved': 6, 'byte_identical_moves': 5,
               'existing_helper_visibility_changes': 1,
               'new_formula_or_hypothesis': False, 'proof_body_changes': False,
               'parameter_and_target_changes': False,
               'owned_impact': 'All twelve changed old owners and all three new owners require a complete serialized/environment owned inventory, including generated declarations, and independent strict compilation/kernel replay. The moved private helper acquires its public original-namespace name; exact generated names/counts require future audit.',
               'required_full_owned_modules': [PREFIX + n for n in [*before, *new]],
               'lean_executions': [], 'cloud_actions': [], 'accepted': False, 'P2_5_proved': False}
    files['DECLARATION_IDENTITY.json'] = json_bytes(receipt)
    patch = []
    for name, raw in before.items():
        patch.extend(difflib.unified_diff(raw.decode().splitlines(keepends=True), after[name].decode().splitlines(keepends=True),
                                         fromfile='a/ImbalancedChen/' + name + '.lean', tofile='b/ImbalancedChen/' + name + '.lean'))
    for name, raw in new.items():
        patch.extend(difflib.unified_diff([], raw.decode().splitlines(keepends=True), fromfile='/dev/null',
                                         tofile='b/ImbalancedChen/' + name + '.lean'))
    files['mechanical-owner-relocation.patch'] = ''.join(patch).encode()
    for relative, raw in files.items():
        path = HERE / relative
        if args.write:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(raw)
        else:
            assert path.read_bytes() == raw, relative
    print(json.dumps({'status': 'STATIC_IDENTITY_ONLY', 'files_checked': len(files), 'moved_declarations': 6,
                      'old_owners': len(before), 'new_owners': len(new), 'strict_compilation_or_audit_run': False}))


if __name__ == '__main__':
    main()
