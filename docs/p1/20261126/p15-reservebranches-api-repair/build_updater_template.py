#!/usr/bin/env python3
"""Construct the local unbound ReserveBranches wrapper from the frozen predecessor."""
from pathlib import Path
from types import ModuleType
import ast
import hashlib
import json
import pprint
import re

OUT = Path('/tmp/p15-reservebranches-repair')
PREVIOUS = Path('/tmp/p15-lowertrim-repair/apply_lowertrim_repair.py')
PROBE = OUT / 'probe_reservebranches_repair.py'
METADATA = Path('/tmp/p15-ae-actual/ACTUAL_AE_METADATA.json')
AE = 'ca13f51c65d37870b96a6b1eb32ac30e92019fa2'
AD = 'e91af3a5c407bdeea243af7dd3c4248949d83e9b'
AC = '9f2013ad9cb9caac9cec03cb213d9949c4443c65'
TARGET = 'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches'
LOWERTRIM = 'ImbalancedChen.P5OriginalSingletonLowerTrimPaid'
ATLASTRIM = 'ImbalancedChen.P1OriginalSingletonAtlasTrim'

def fp(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}

assert fp(PREVIOUS.read_bytes()) == {'bytes': 33309, 'sha256': 'dbf67e2bce3b2059c3f1833e110c80005f486e22704ac431addedc99732dbc6f'}
metadata = json.loads(METADATA.read_bytes())
probe = ModuleType('frozen_reservebranches_probe'); probe.__file__ = str(PROBE)
exec(compile(PROBE.read_bytes(), str(PROBE), 'exec'), probe.__dict__)
text = PREVIOUS.read_text()
text = re.sub(r'\b(?:AC_ANCHOR|AC|AD|AE)\b',
              lambda m: {'AC_ANCHOR': 'AE_ANCHOR', 'AC': 'AE', 'AD': 'AF', 'AE': 'AG'}[m.group()], text)
text = text.replace('OriginalSingletonLowerTrimPaid', 'OriginalPrimeAtlasReserveBranches')
text = text.replace('LowerTrimPaid', 'ReserveBranches')
text = text.replace('lowertrim', 'reservebranches').replace('LOWERTRIM', 'RESERVEBRANCHES')
text = re.sub(r'\bSYNTHESIS\b', 'LOWERTRIM', text)
text = text.replace('PUBLIC_SYNTHESIS', 'PUBLIC_LOWERTRIM')
text = text.replace('SYNTHESIS_AC_PUBLIC_ACCEPTANCE', 'LOWERTRIM_AE_PUBLIC_ACCEPTANCE')
text = text.replace('collect_ac_acceptance.py', 'collect_ae_acceptance.py')
text = text.replace('ACTUAL_AC_METADATA.json', 'ACTUAL_AE_METADATA.json')
text = text.replace('ACTUAL_AC_ACCEPTANCE_READ.json', 'ACTUAL_AE_ACCEPTANCE_READ.json')
text = text.replace('p15_AC_', 'p15_AE_')
text = text.replace('unchanged_AC_', 'unchanged_AE_').replace('frozen_AC_', 'frozen_AE_')
text = text.replace('published_AD_inputs', 'published_AF_inputs')
text = text.replace('original_AC_AA_Y_W_U_S_Q', 'original_AE_AC_AA_Y_W_U_S_Q')
text = text.replace('AE/AA/Y/W/U/S/Q', 'AE/AC/AA/Y/W/U/S/Q')
text = text.replace('original_AC_context', 'original_AE_context').replace('accepted_AC_bindings', 'accepted_AE_bindings')
text = text.replace('UNCHANGED_ORIGINAL_AC_PREFLIGHT', 'UNCHANGED_ORIGINAL_AE_PREFLIGHT')
text = text.replace('original_AC_four_target_preflight', 'original_AE_two_target_preflight')
text = text.replace('accepted_AC_owners_revalidated', 'accepted_AE_owners_revalidated')
text = text.replace('AC_original_Synthesis_acceptance_preserved', 'AE_original_LowerTrim_and_AtlasTrim_acceptance_preserved')
text = text.replace('Synthesis_AC_and_all_thirteen_earlier_prior_acceptances_preserved',
                    'LowerTrim_AtlasTrim_AE_and_all_fourteen_earlier_prior_acceptances_preserved')
text = text.replace('original_thirteen_prior_identities_and_later_retained_receipts_preserved',
                    'original_fourteen_prior_identities_and_later_retained_receipts_preserved')

def once(old, new):
    global text
    assert text.count(old) == 1, (old, text.count(old))
    text = text.replace(old, new)

def assignment(name, value):
    global text
    matches = [node for node in ast.parse(text).body if isinstance(node, ast.Assign)
               and any(isinstance(t, ast.Name) and t.id == name for t in node.targets)]
    assert len(matches) == 1, name
    old = ast.get_source_segment(text, matches[0])
    once(old, name + ' = ' + pprint.pformat(value, width=105, sort_dicts=False))

assignment('AE', AE); assignment('AE_ANCHOR', AD)
once('AA = ', 'AC = ' + repr(AC) + '\nAA = ')
assignment('FAILED_JOB', 'job_698d39e25f9d4800a912dc27a0bfe84b')
assignment('LOWERTRIM', LOWERTRIM)
once('ACCEPTED = [LOWERTRIM]', 'ATLASTRIM = ' + repr(ATLASTRIM) + '\nACCEPTED = [LOWERTRIM, ATLASTRIM]')
for name in ['BEFORE', 'AFTER', 'SETUP_FP', 'DRIVER_FP', 'MANIFEST_FP']:
    assignment(name, getattr(probe, name))
assignment('INHERITED_EXTRA_PINS', probe.RETAINED_EXTRA_PINS)
assignment('REMAINING', [TARGET, 'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime'])
assignment('INPUTS', None)
once('# Exact AF publication, six raw inputs and actual successful probe identity.',
     '# HOLD until the actual AF publication, seven raw inputs and successful probe identity are bound.')
once("PUBLIC_LOWERTRIM = 'docs/p1/20261125/p15-current-public-acceptance/LOWERTRIM_AE_PUBLIC_ACCEPTANCE.json'",
     "PUBLIC_LOWERTRIM = 'docs/p1/20261125/p15-current-public-acceptance/LOWERTRIM_AE_PUBLIC_ACCEPTANCE.json'\n"
     "PUBLIC_ATLASTRIM = 'docs/p1/20261125/p15-current-public-acceptance/ATLASTRIM_AE_PUBLIC_ACCEPTANCE.json'")
once('Synthesis keeps its original AE acceptance and same-AE reuse. All older owners retain',
     'LowerTrim and AtlasTrim keep their original AE run0/run1 acceptances. All older owners retain')
once('AA/Y/W/U/S/Q or their earlier identities.', 'AC/AA/Y/W/U/S/Q or their earlier identities.')
once('for commit in (AE, AA, Y, W, U, S, Q)', 'for commit in (AE, AC, AA, Y, W, U, S, Q)')
once('{REPAIR, PROBE, DIAGNOSTICS, READ, COLLECTOR, PUBLIC_LOWERTRIM}',
     '{REPAIR, PROBE, DIAGNOSTICS, READ, COLLECTOR, PUBLIC_LOWERTRIM, PUBLIC_ATLASTRIM}')
once("'p15_singleton_lower_trim_paid_one_proof_splice_candidate_v1'",
     "'p15_original_prime_atlas_reserve_branches_one_proof_splice_candidate_v1'")
once("repair['declaration_count'] == 8", "repair['declaration_count'] == 11")
once('(reader.AE, reader.AB, reader.AA, reader.Y, reader.W, reader.U, reader.S, reader.Q, reader.REPO, reader.PROJECT, reader.ROOT,',
     '(reader.AE, reader.AD, reader.AC, reader.AA, reader.Y, reader.W, reader.U, reader.S, reader.Q, reader.REPO, reader.PROJECT, reader.ROOT,')
once('(AE, AE_ANCHOR, AA, Y, W, U, S, Q, REPO, PROJECT, OLD_ROOT, DRIVER_FP, MANIFEST_FP)',
     '(AE, AE_ANCHOR, AC, AA, Y, W, U, S, Q, REPO, PROJECT, OLD_ROOT, DRIVER_FP, MANIFEST_FP)')
once("read['current_read_live_source_count'] == 112 and read['current_read_preserved_dependency_count'] == 111",
     "read['current_read_live_source_count'] == 153 and read['current_read_preserved_dependency_count'] == 151")
once('reader.accepting_runs(runs) == {LOWERTRIM: 0}', 'reader.accepting_runs(runs) == {LOWERTRIM: 0, ATLASTRIM: 1}')
once('for module, index, path in [(LOWERTRIM, 0, PUBLIC_LOWERTRIM)]:',
     'for module, index, path, counts in [(LOWERTRIM, 0, PUBLIC_LOWERTRIM, (10, 10)),\n'
     '                                        (ATLASTRIM, 1, PUBLIC_ATLASTRIM, (11, 9))]:')
once("(owner['owned_count'], owner['public_count']) == (28, 28)", "(owner['owned_count'], owner['public_count']) == counts")
once('len(spec.active) == 112 and len(spec.dependency_pins) == 111',
     'len(spec.active) == 153 and len(spec.dependency_pins) == 151')
once('    active = s.h.closure(spec.graph, REMAINING); watch = active | set(driver.TARGETS)\n'
     '    need(len(spec.graph) == 360 and len(active) == 157 and len(watch) == 160 and spec.active <= active,\n'
     "         'remaining4 source/watch scope differs')",
     '    active = s.h.closure(spec.graph, REMAINING)\n'
     '    union = s.h.closure(spec.graph, ACCEPTED + REMAINING); watch = union | set(driver.TARGETS)\n'
     '    need(len(spec.graph) == 360 and len(active) == 144 and len(union) == 157 and len(watch) == 160 and\n'
     '         union == spec.active | active and set(ACCEPTED).isdisjoint(active),\n'
     "         'separate accepted-prefix/remaining2/union scopes differ')\n"
     "    supplier_modules = set(spec.manifest['previously_accepted_targets']) | set(spec.manifest['accepted_suppliers'])\n"
     "    need(len(spec.manifest['previously_accepted_targets']) == 14 and\n"
     "         set(later['original_supplier_acceptance_bindings']) == union & supplier_modules and\n"
     "         len(later['original_supplier_acceptance_bindings']) == 27 and\n"
     '         len(spec.supplier_evidence) == 25 and spec.supplier_evidence ==\n'
     "         {m: later['original_supplier_acceptance_bindings'][m] for m in spec.active & supplier_modules},\n"
     "         'original AE union and accepted-prefix supplier bindings differ')\n"
     "    remaining_suppliers = {m: later['original_supplier_acceptance_bindings'][m] for m in active & supplier_modules}\n"
     "    need(len(remaining_suppliers) == 24, 'remaining2 original supplier scope differs')")
once('graph, installed = s.h.project_graph(PROJECT, REMAINING)\n'
     '    need(graph == {m: spec.graph[m] for m in active} and\n'
     "         {m: row['sha256'] for m, row in installed.items()} == {m: spec.sources[m] for m in active}, 'live AE graph differs')",
     'graph, installed = s.h.project_graph(PROJECT, ACCEPTED + REMAINING)\n'
     '    need(graph == {m: spec.graph[m] for m in union} and\n'
     "         {m: row['sha256'] for m, row in installed.items()} == {m: spec.sources[m] for m in union}, 'live AE union graph differs')")
once("original_context['selected_live_sources'] == {m: spec.sources[m] for m in active} and\n"
     "         set(original_context['preserved_dependency_artifacts']) == active - set(ACCEPTED + REMAINING)",
     "original_context['selected_live_sources'] == {m: spec.sources[m] for m in union} and\n"
     "         set(original_context['preserved_dependency_artifacts']) == union - set(ACCEPTED + REMAINING)")
once("probe['accepted_prefix_live_source_count'] == 112 and probe['accepted_prefix_dependency_count'] == 111",
     "probe['accepted_prefix_live_source_count'] == 153 and probe['accepted_prefix_dependency_count'] == 151")
once('        active=active, watch=watch, sources=sources, artifacts=artifacts, evidence=evidence,',
     '        active=active, union=union, remaining_suppliers=remaining_suppliers, watch=watch,\n'
     '        sources=sources, artifacts=artifacts, evidence=evidence,')
once('fresh.order == REMAINING and len(fresh.dependency_pins) == 153 and\n'
     '         set(fresh.initial_owners) == set(ACCEPTED + REMAINING) and\n'
     "         all(fresh.initial_owners[m]['status'] == 'MISSING_WITHOUT_NORMAL_RECEIPT' for m in REMAINING) and\n"
     "         all(fresh.initial_owners[m]['status'] == 'BOUND_CURRENT_NORMAL_RECEIPT' and\n"
     '             fresh.dependency_pins[m] == state.artifacts[m] for m in ACCEPTED) and\n'
     "         fresh.supplier_evidence == state.later['original_supplier_acceptance_bindings'] and\n"
     "         len(fresh.supplier_evidence) == 26, 'unchanged AE four-target preflight differs')",
     'fresh.order == REMAINING and len(fresh.dependency_pins) == 142 and\n'
     '         set(fresh.initial_owners) == set(REMAINING) and set(ACCEPTED).isdisjoint(fresh.active) and\n'
     "         all(fresh.initial_owners[m]['status'] == 'MISSING_WITHOUT_NORMAL_RECEIPT' for m in REMAINING) and\n"
     '         fresh.supplier_evidence == state.remaining_suppliers and\n'
     "         len(fresh.supplier_evidence) == 24, 'unchanged AE two-target preflight differs')")
text = text.replace("'active_source_count': 157, 'preserved_dependency_count': 153",
                    "'active_source_count': 144, 'preserved_dependency_count': 142")
once('graph, sources = s.h.project_graph(PROJECT, REMAINING)\n'
     '    need(graph == {m: fresh.graph[m] for m in fresh.active} and\n'
     "         {m: row['sha256'] for m, row in sources.items()} == {m: post.sources[m] for m in fresh.active}, 'post-install graph differs')",
     'graph, sources = s.h.project_graph(PROJECT, ACCEPTED + REMAINING)\n'
     '    need(graph == {m: fresh.graph[m] for m in state.union} and\n'
     "         {m: row['sha256'] for m, row in sources.items()} == {m: post.sources[m] for m in state.union}, 'post-install union graph differs')")
once("'published_source_count': 360, 'other_source_slots_preserved': 359, 'watched_module_count': 160,",
     "'published_source_count': 360, 'other_source_slots_preserved': 359, 'watched_module_count': 160,\n"
     "        'preserved_union_source_count': 157, 'accepted_prefix_source_count': 153, 'accepted_prefix_dependency_count': 151,")
once("'accepted_AE_owners_revalidated': ACCEPTED, 'accepted_prefix_sources': 112, 'accepted_prefix_dependencies': 111,\n"
     "            'active_source_count': 157, 'watched_module_count': 160,",
     "'accepted_AE_owners_revalidated': ACCEPTED, 'accepted_prefix_sources': 153, 'accepted_prefix_dependencies': 151,\n"
     "            'active_source_count': 144, 'preserved_union_source_count': 157, 'watched_module_count': 160,")
ast.parse(text)
assert 'spec.active <= active' not in text
assert 'fresh.initial_owners) == set(ACCEPTED + REMAINING)' not in text
assert 'INPUTS = None' in text
(OUT / 'apply_reservebranches_repair.py').write_text(text)
print(json.dumps({'status': 'UNBOUND_AF_AND_AG_HOLD_TEMPLATE', 'script': fp(text.encode())}, indent=2))
