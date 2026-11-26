from pathlib import Path
import ast,hashlib,json,pprint,re
root=Path('/tmp/p15-synthesis-repair');old=Path('/tmp/p15-mean-repair/apply_mean_repair.py').read_bytes()
assert len(old)==30777 and hashlib.sha256(old).hexdigest()=='51443890bd2e14c00f0a01627afd6fcc76ba260e31533e29fbbd9f7dee74e983'
s=old.decode();s=re.sub(r'\b(?:Y|Z|AA)\b',lambda m:{'Y':'AA','Z':'AB','AA':'AC'}[m[0]],s);s=s.replace('Y_ANCHOR','AA_ANCHOR')
s=s.replace('P5PrimeDivisorMeanCorrection','P5OriginalSharpPrimeSynthesis').replace('MeanCorrection','SharpPrimeSynthesis')
s=s.replace('P5OriginalPrimeEndpointLogPayment','P5PrimeDivisorMeanCorrection')
s=s.replace('PUBLIC_ENDPOINT','PUBLIC_MEAN').replace('ENDPOINT','MEAN').replace('Endpoint','Mean')
s=s.replace('_Y_','_AA_').replace('Y_original_Mean','AA_original_Mean')
s=s.replace('_AA_W_U_S_Q','_AA_Y_W_U_S_Q').replace('AA/W/U/S/Q','AA/Y/W/U/S/Q')
s=s.replace('(AA, W, U, S, Q)','(AA, Y, W, U, S, Q)')
s=s.replace('W/U/S/Q or their earlier identities','Y/W/U/S/Q or their earlier identities')
s=s.replace('p15-mean','p15-synthesis').replace('apply_mean_repair.py','apply_synthesis_repair.py')
s=s.replace('unchanged_AA_mean_repair_reader','unchanged_AA_synthesis_repair_reader')
s=s.replace('collect_y_acceptance.py','collect_aa_acceptance.py')
s=s.replace('ACTUAL_Y_','ACTUAL_AA_').replace('ACTUAL_MEAN_PROBE_RESULT.json','ACTUAL_SYNTHESIS_PROBE_RESULT.json')
s=s.replace('EXACT_SINGLE_MEAN','EXACT_SINGLE_SYNTHESIS')
s=s.replace('p15_prime_divisor_mean_correction_three_proof_splices_candidate_v1','p15_sharp_prime_synthesis_one_proof_splice_candidate_v1')
s=s.replace('three proof splices','one proof splice').replace("len(repair['splices']) == 3","len(repair['splices']) == 1").replace("repair['declaration_count'] == 16","repair['declaration_count'] == 18")
s=re.sub(r'\b(?:110|109|151)\b',lambda m:{'110':'108','109':'107','151':'152'}[m[0]],s)
s=s.replace('(24, 24)','(22, 22)').replace('remaining6','remaining5').replace('six-target','five-target').replace('six_target','five_target')
s=s.replace('len(fresh.supplier_evidence) == 24','len(fresh.supplier_evidence) == 25').replace('all_eleven_earlier_prior_acceptances','all_twelve_earlier_prior_acceptances')
s=s.replace('published_Z_inputs','published_AB_inputs')
a='(reader.AA, reader.X, reader.W, reader.U, reader.S, reader.Q, reader.REPO, reader.PROJECT, reader.ROOT,\n          reader.DRIVER_FP, reader.MANIFEST_FP) ==\n         (AA, AA_ANCHOR, W, U, S, Q, REPO, PROJECT, OLD_ROOT, DRIVER_FP, MANIFEST_FP)'
b='(reader.AA, reader.Z, reader.Y, reader.W, reader.U, reader.S, reader.Q, reader.REPO, reader.PROJECT, reader.ROOT,\n          reader.DRIVER_FP, reader.MANIFEST_FP) ==\n         (AA, AA_ANCHOR, Y, W, U, S, Q, REPO, PROJECT, OLD_ROOT, DRIVER_FP, MANIFEST_FP)'
assert a in s;s=s.replace(a,b)
a="REMAINING = [TARGET,\n    'ImbalancedChen.P5OriginalSharpPrimeSynthesis', 'ImbalancedChen.P5OriginalSingletonLowerTrimPaid',"
b="REMAINING = [TARGET, 'ImbalancedChen.P5OriginalSingletonLowerTrimPaid',"
assert a in s;s=s.replace(a,b)
a="         probe['original_source_and_failed_setup_preserved'] is True and\n"
assert a in s;s=s.replace(a,"         probe['original_twelve_prior_identities_and_later_retained_receipts_preserved'] is True and\n"+a)
meta=json.loads(Path('/tmp/p15-aa-actual/ACTUAL_AA_METADATA.json').read_text());repair=json.loads((root/'REPAIR_CANDIDATE.json').read_text())
fp=lambda b:{'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()};pin=lambda d:{k:d[k] for k in ('bytes','sha256')}
constants={'AA':'ae373b971d2b88f97532dc883d835751dd10c67b','AA_ANCHOR':'bde4a91307cb5e5872b6fc3c1e4a1520908b10c2','FAILED_JOB':'job_2d377894edb64660880d7f3e8783b2ee','DRIVER_FP':fp(Path('/tmp/p15-entrypoint-aa/run_selected.py').read_bytes()),'MANIFEST_FP':fp(Path('/tmp/p15-entrypoint-aa/SOURCE_MANIFEST.json').read_bytes()),'BEFORE':repair['before'],'AFTER':repair['after'],'SETUP_FP':pin(meta['failures']['ImbalancedChen.P5OriginalSharpPrimeSynthesis']['artifact_slots']['/workspace/blue-member-build/.lake/build/ir/ImbalancedChen/P5OriginalSharpPrimeSynthesis.setup.json']),'INPUTS':None}
lines=s.splitlines(True);edits=[]
for node in ast.parse(s).body:
 if isinstance(node,ast.Assign) and len(node.targets)==1 and isinstance(node.targets[0],ast.Name) and node.targets[0].id in constants:
  key=node.targets[0].id;replacement=key+' = '+pprint.pformat(constants[key],width=110,sort_dicts=False)+'\n'
  if key=='AA_ANCHOR':replacement+="Y = 'f6e63d1b9785be30a607fb0ff55151ca95d1a6aa'\n"
  edits.append((node.lineno-1,node.end_lineno,replacement))
assert len(edits)==len(constants)
for a,b,replacement in reversed(edits):lines[a:b]=[replacement]
s=''.join(lines).replace('# Exact AB publication, six raw inputs and actual successful probe identity.','# HOLD until the actual AB publication, successful probe and six exact raw inputs are supplied.')
failed_raw=(root/'ACTUAL_SYNTHESIS_PROBE_RESULT_attempt0.json').read_bytes()
assert fp(failed_raw)=={'bytes':5727,'sha256':'1d3e329e727ce232308131b0b510b8732b34c4241cce44800774735547390e5c'}
failed=json.loads(failed_raw)
failed_retained={failed['candidate']['path']:pin(failed['candidate']),failed['log']['path']:pin(failed['log']),str(Path(failed['candidate']['path']).parent/'ACTUAL_SYNTHESIS_PROBE_RESULT.json'):fp(failed_raw)}
insert='PRIOR_FAILED_PROBES = '+pprint.pformat(repair['prior_failed_whole_module_probes'],width=110,sort_dicts=False)+'\nFAILED_PROBE_RETAINED = '+pprint.pformat(failed_retained,width=110,sort_dicts=False)+'\n\n'
assert s.count('def need(ok, message):')==1
s=s.replace('def need(ok, message):',insert+'def need(ok, message):')
a="         repair['original_failure_metadata'] == PINS[DIAGNOSTICS] and\n"
assert a in s;s=s.replace(a,a+"         repair['prior_failed_whole_module_probes'] == PRIOR_FAILED_PROBES and\n")
a="    extras = {**{p: fp for p, fp in c.reader.PINNED['extra_pins'].items() if p not in mutable},\n"
assert a in s;s=s.replace(a,"    extras = {**FAILED_PROBE_RETAINED,\n        **{p: fp for p, fp in c.reader.PINNED['extra_pins'].items() if p not in mutable},\n")
assert "ARCHIVE_NAME = 'P5OriginalSharpPrimeSynthesis.setup.json'" in s
assert "PUBLIC_MEAN = 'docs/p1/20261125/p15-current-public-acceptance/MEAN_AA_PUBLIC_ACCEPTANCE.json'" in s
assert 'INPUTS = None' in s and '(AA, Y, W, U, S, Q)' in s
assert 'original_AA_five_target_preflight' in s
ast.parse(s);p=root/'apply_synthesis_repair.py';p.write_text(s);print(p.name,len(p.read_bytes()),hashlib.sha256(p.read_bytes()).hexdigest())
