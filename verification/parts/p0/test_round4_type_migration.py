#!/usr/bin/env python3
"""Fail-closed R4 migration tests. Synthetic compiler records; no Lean is run."""
from collections import Counter
from copy import deepcopy
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import test_type_export_migration as common

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('check_round4_types_for_test', HERE / 'check_round4_types.py')
exporter = importlib.util.module_from_spec(spec)
spec.loader.exec_module(exporter)


def fixture():
    baseline = deepcopy(exporter.historical_baseline())
    declarations = []
    for row in baseline['declarations']:
        text = 'synthetic complete type for ' + row['name']
        row['type_sha256'] = hashlib.sha256(text.encode()).hexdigest()
        counterparts = [(row['expected_name'], row['expected_module'])]
        if 'additional_duplicate' in row:
            duplicate = row['additional_duplicate']
            counterparts.append((duplicate['name'], duplicate['module']))
        for name, module in counterparts:
            record = common.declaration(name, module, row['kind'])
            record['type'] = text
            declarations.append(record)
    bridge = common.declaration(exporter.FINAL_BRIDGE, exporter.FINAL_MODULE)
    bridge['type'] = '(hLower : Prop) (hUpper : Prop) : Prop'
    baseline['final_bridge']['type_sha256'] = hashlib.sha256(bridge['type'].encode()).hexdigest()
    return declarations, bridge, baseline


def serialize(declarations, bridge, shared_declarations=()):
    with patch.dict(common.EXPORTERS, {3: exporter}):
        return common.serialize(3, declarations, bridge, shared_declarations=shared_declarations).replace('P0_ROUND3_', 'P0_ROUND4_')


class Round4MigrationTests(unittest.TestCase):
    def setUp(self):
        self.declarations, self.bridge, self.baseline = fixture()
        self.stdout = serialize(self.declarations, self.bridge)

    def parse(self, stdout=None):
        with patch.object(exporter, 'historical_baseline', return_value=self.baseline):
            return exporter.parse_types(self.stdout if stdout is None else stdout)

    def reject(self, stdout, message=None):
        with self.assertRaisesRegex(RuntimeError, message or '.'):
            self.parse(stdout)

    def test_exact_475_counterparts_cover_all_414_original_types(self):
        declarations, bridge = self.parse()
        self.assertEqual(len(declarations), 475)
        self.assertEqual(len(self.baseline['declarations']), 414)
        self.assertEqual(len({d['module'] for d in declarations}), 16)
        self.assertEqual(bridge['name'], exporter.FINAL_BRIDGE)

    def test_frozen_baseline_keeps_original_hashes_and_exact_migration_counts(self):
        baseline = exporter.historical_baseline()
        self.assertEqual(baseline['source_commit'], 'd2188484e5aa800ee3d403125b1d621cb2dba583')
        self.assertEqual(baseline['source_run'], 41762528251)
        self.assertEqual(Counter(r['migration'] for r in baseline['declarations']),
            Counter(unchanged=224, source_proof_owner_moved=64, public_realization_owner_moved=65, private_realization_renamed=61))
        self.assertEqual(len({r['expected_name'] for r in baseline['declarations']}), 414)
        for row in baseline['declarations']:
            self.assertRegex(row['type_sha256'], r'^[0-9a-f]{64}$')
            if row['migration'] == 'private_realization_renamed':
                self.assertEqual(row['expected_name'], row['name'].replace(
                    '_private.ImbalancedChen.Certificates.PairedV2Batch4To64.0.',
                    '_private.ImbalancedChen.Certificates.PairedV2Batch4To64GeometryChecked.0.', 1))

    def test_all_sixteen_production_sources_and_baseline_are_frozen(self):
        for module in exporter.MODULES:
            self.assertIn(module.replace('.', '/') + '.lean', exporter.FROZEN)
        self.assertEqual(exporter.FROZEN[exporter.HISTORICAL_BASELINE], exporter.HISTORICAL_BASELINE_SHA256)

    def test_tampered_baseline_rejected_even_when_json_valid(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); path = root / exporter.HISTORICAL_BASELINE
            path.parent.mkdir(parents=True)
            path.write_text(json.dumps(self.baseline))
            with patch.object(exporter, 'ROOT', root):
                with self.assertRaisesRegex(RuntimeError, 'baseline changed'):
                    exporter.historical_baseline()

    def test_each_historical_type_hash_is_required_without_normalization(self):
        # Exercise each category, plus the additional private copy.
        names = [next(r['expected_name'] for r in self.baseline['declarations'] if r['migration'] == kind)
                 for kind in ['unchanged', 'source_proof_owner_moved', 'public_realization_owner_moved', 'private_realization_renamed']]
        names.append(next(r['additional_duplicate']['name'] for r in self.baseline['declarations'] if 'additional_duplicate' in r))
        for name in names:
            with self.subTest(name=name):
                self.reject(common.edit_records(self.stdout, 'P0_ROUND4_DECL ',
                    lambda r: r.__setitem__('type', r['type'] + ' '), lambda r: r['name'] == name), 'complete type changed')

    def test_missing_any_of_475_names_rejected_even_with_consistent_counts(self):
        for category in ['unchanged', 'source_proof_owner_moved', 'public_realization_owner_moved', 'private_realization_renamed']:
            name = next(r['expected_name'] for r in self.baseline['declarations'] if r['migration'] == category)
            with self.subTest(category=category):
                self.reject(serialize([d for d in self.declarations if d['name'] != name], self.bridge), 'name-set mismatch')
        name = next(r['additional_duplicate']['name'] for r in self.baseline['declarations'] if 'additional_duplicate' in r)
        self.reject(serialize([d for d in self.declarations if d['name'] != name], self.bridge), 'name-set mismatch')

    def test_only_224_preexisting_records_cannot_pass(self):
        keep = {r['expected_name'] for r in self.baseline['declarations'] if r['migration'] == 'unchanged'}
        self.reject(serialize([d for d in self.declarations if d['name'] in keep], self.bridge))

    def test_extra_unmapped_declaration_rejected(self):
        extra = common.declaration('unexpected.generated', exporter.MODULES[0])
        self.reject(serialize(self.declarations + [extra], self.bridge), 'name-set mismatch')

    def test_unmapped_private_prefix_not_accepted(self):
        declarations = deepcopy(self.declarations)
        row = next(d for d in declarations if 'Batch4To64GeometryChecked.0.' in d['name'])
        row['name'] = row['name'].replace('GeometryChecked.0.', 'UnknownModule.0.')
        self.reject(serialize(declarations, self.bridge), 'name-set mismatch')

    def test_old_private_name_cannot_silently_replace_explicit_new_name(self):
        declarations = deepcopy(self.declarations)
        row = next(d for d in declarations if 'Batch4To64GeometryChecked.0.' in d['name'])
        row['name'] = row['name'].replace('Batch4To64GeometryChecked.0.', 'Batch4To64.0.')
        self.reject(serialize(declarations, self.bridge), 'name-set mismatch')

    def test_wrong_owner_rejected_despite_consistent_serialized_inventory(self):
        declarations = deepcopy(self.declarations)
        row = next(d for d in declarations if d['name'].endswith('row0004_checked'))
        row['module'] = exporter.MODULES[0]
        self.reject(serialize(declarations, self.bridge), 'owner or kind')

    def test_wrong_kind_rejected_despite_consistent_serialized_inventory(self):
        declarations = deepcopy(self.declarations)
        row = next(d for d in declarations if d['name'].endswith('row0004_checked'))
        row['kind'] = 'definition'
        self.reject(serialize(declarations, self.bridge), 'owner or kind')

    def test_final_bridge_full_type_hash_and_both_hypotheses_required(self):
        for text in ['hLower', '(hLower : Prop) (hUpper : Prop) : False']:
            bridge = dict(self.bridge, type=text)
            self.reject(serialize(self.declarations, bridge))

    def test_final_bridge_identity_must_remain_exact(self):
        for field, value in [('name', 'different'), ('module', exporter.MODULES[0]), ('kind', 'definition')]:
            self.reject(serialize(self.declarations, dict(self.bridge, **{field: value})), 'Wrong final bridge')

    def test_declaration_and_bridge_safety_flags_fail_closed(self):
        for prefix in ['P0_ROUND4_DECL ', 'P0_ROUND4_FINAL_BRIDGE ']:
            for flag in ['is_unsafe', 'is_partial', 'is_axiom']:
                for value in [True, None]:
                    self.reject(common.edit_records(self.stdout, prefix, lambda r: r.__setitem__(flag, value)))
                self.reject(common.edit_records(self.stdout, prefix, lambda r: r.pop(flag)))

    def test_forbidden_global_axioms_rejected(self):
        for prefix in ['P0_ROUND4_DECL ', 'P0_ROUND4_FINAL_BRIDGE ']:
            self.reject(common.edit_records(self.stdout, prefix, lambda r: r.__setitem__('axioms', ['sorryAx'])), 'Forbidden axiom')

    def test_truncated_readable_type_rejected(self):
        for marker in ['⋯', '…', '']:
            self.reject(common.edit_records(self.stdout, 'P0_ROUND4_DECL ', lambda r: r.__setitem__('readable_type', marker)), 'truncated')

    def test_missing_extra_duplicate_module_markers_rejected(self):
        for prefix in ['P0_ROUND4_MODULE ', 'P0_ROUND4_SERIALIZED ']:
            line = next(l for l in self.stdout.splitlines() if l.startswith(prefix))
            self.reject(self.stdout.replace(line+'\n', '', 1))
            self.reject(self.stdout+'\n'+line)
            self.reject(common.edit_records(self.stdout, prefix, lambda r: r.__setitem__('module', 'unexpected')))

    def test_missing_duplicate_or_inconsistent_total_rejected(self):
        line = 'P0_ROUND4_COUNT 475'
        for text in [self.stdout.replace(line, ''), self.stdout+'\n'+line, self.stdout.replace(line, 'P0_ROUND4_COUNT 474')]:
            self.reject(text, 'total census')

    def test_bad_owned_shared_partitions_rejected(self):
        edits = [lambda r: r['shared_constant_names'].append(r['owned_constant_names'][0]),
                 lambda r: r['owned_constant_names'].pop(),
                 lambda r: r['serialized_constant_names'].append('extra'),
                 lambda r: r['environment_constant_names'].pop()]
        for edit in edits:
            self.reject(common.edit_records(self.stdout, 'P0_ROUND4_SERIALIZED ', edit))

    def test_count_fields_reject_wrong_values_and_boolean(self):
        for field in ['owned_constant_count', 'shared_constant_count', 'serialized_constant_count', 'extra_codegen_name_count']:
            for value in [-1, True, None]:
                self.reject(common.edit_records(self.stdout, 'P0_ROUND4_SERIALIZED ', lambda r: r.__setitem__(field, value)))

    def test_incomplete_serialized_module_data_rejected(self):
        for field, value in [('is_module', True), ('import_all', False), ('has_data', False)]:
            self.reject(common.edit_records(self.stdout, 'P0_ROUND4_SERIALIZED ', lambda r: r.__setitem__(field, value)))

    def test_missing_extra_duplicate_occurrences_rejected(self):
        prefix = 'P0_ROUND4_OCCURRENCE '
        line = next(l for l in self.stdout.splitlines() if l.startswith(prefix))
        record = json.loads(line[len(prefix):])
        self.reject(self.stdout.replace(line+'\n', '', 1), 'Missing serialized occurrence')
        self.reject(self.stdout+'\n'+line, 'Duplicate serialized occurrence')
        self.reject(self.stdout+'\n'+prefix+json.dumps(dict(record, name='extra')), 'Unexpected serialized occurrence')

    def test_all_occurrence_identity_flags_fail_closed(self):
        for flag in ['type_matches_environment', 'level_params_match_environment', 'kind_matches_environment', 'all_dependencies_present']:
            for value in [False, None]:
                self.reject(common.edit_records(self.stdout, 'P0_ROUND4_OCCURRENCE ', lambda r: r.__setitem__(flag, value)))
            self.reject(common.edit_records(self.stdout, 'P0_ROUND4_OCCURRENCE ', lambda r: r.pop(flag)))

    def test_all_occurrence_safety_flags_fail_closed(self):
        for flag in ['is_unsafe', 'is_partial', 'is_axiom']:
            self.reject(common.edit_records(self.stdout, 'P0_ROUND4_OCCURRENCE ', lambda r: r.__setitem__(flag, True)))
            self.reject(common.edit_records(self.stdout, 'P0_ROUND4_OCCURRENCE ', lambda r: r.pop(flag)))

    def test_raw_sorry_axiom_and_direct_self_reference_rejected(self):
        edits = [lambda r: r.__setitem__('raw_dependency_axioms', ['sorryAx']),
                 lambda r: r.__setitem__('raw_dependency_names', ['sorryAx']),
                 lambda r: r.__setitem__('raw_dependency_names', [r['name']])]
        for edit in edits:
            self.reject(common.edit_records(self.stdout, 'P0_ROUND4_OCCURRENCE ', edit, lambda r: r['kind'] == 'theorem'))

    def test_duplicate_raw_dependencies_and_wrong_expression_counts_rejected(self):
        for edit in [lambda r: r.__setitem__('raw_dependency_names', ['x','x']),
                     lambda r: r.__setitem__('raw_expression_count', 0),
                     lambda r: r.__setitem__('raw_expression_count', True)]:
            self.reject(common.edit_records(self.stdout, 'P0_ROUND4_OCCURRENCE ', edit))

    def shared_fixture(self, external=False):
        record = common.declaration('External.generated', 'External.Owner') if external else next(d for d in self.declarations if d['kind'] == 'theorem')
        module = next(m for m in exporter.MODULES if m != record['module'])
        return serialize(self.declarations, self.bridge, [(module, record)])

    def test_same_name_shared_theorem_passes_exact_occurrence_audit(self):
        self.parse(self.shared_fixture())

    def test_external_owner_shared_theorem_passes_with_all_validation(self):
        self.parse(self.shared_fixture(external=True))

    def test_shared_owner_and_kind_must_match_exported_census(self):
        stdout = self.shared_fixture()
        for field, value in [('owner_module', 'Wrong.Owner'), ('kind', 'definition'), ('shared', False)]:
            self.reject(common.edit_records(stdout, 'P0_ROUND4_OCCURRENCE ', lambda r: r.__setitem__(field,value), lambda r:r['shared']))

    def test_shared_non_theorem_rejected_even_with_external_owner(self):
        stdout = self.shared_fixture(external=True)
        self.reject(common.edit_records(stdout, 'P0_ROUND4_OCCURRENCE ', lambda r: r.__setitem__('kind','definition'), lambda r:r['shared']), 'not a theorem')

    def test_each_shared_validation_flag_must_be_present_and_true(self):
        stdout = self.shared_fixture()
        for flag in ['owner_precedes_serialized','owner_has_serialized_theorem','type_matches_owner','level_params_match_owner','theorem_all_matches_owner_and_environment']:
            self.reject(common.edit_records(stdout, 'P0_ROUND4_OCCURRENCE ', lambda r: r['shared_validation'].__setitem__(flag,False), lambda r:r['shared']))
            self.reject(common.edit_records(stdout, 'P0_ROUND4_OCCURRENCE ', lambda r: r['shared_validation'].pop(flag), lambda r:r['shared']))

    def test_owned_occurrence_cannot_claim_shared_validation(self):
        self.reject(common.edit_records(self.stdout, 'P0_ROUND4_OCCURRENCE ', lambda r: r.__setitem__('shared_validation',{})), 'Owned occurrence')

    def test_external_shared_copies_must_agree_on_owner(self):
        record = common.declaration('External.generated', 'External.Owner')
        stdout = serialize(self.declarations,self.bridge,[(m,record) for m in exporter.MODULES[:2]])
        self.parse(stdout)
        self.reject(common.edit_records(stdout,'P0_ROUND4_OCCURRENCE ',lambda r:r.__setitem__('owner_module','Other.Owner'),
            lambda r:r['shared'] and r['serialized_module']==exporter.MODULES[1]), 'disagree')


if __name__ == '__main__':
    unittest.main()
