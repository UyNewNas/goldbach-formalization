from pathlib import Path
import ast,hashlib,json,pprint,re
root=Path('/tmp/p15-lowertrim-repair');old=Path('/tmp/p15-synthesis-repair/apply_synthesis_repair.py').read_bytes()
assert len(old)==33049 and hashlib.sha256(old).hexdigest()=='be8d6519aa580ae462e6dfba0775b57651bf2b20c15fdd16ba56e457aab92953'
# Historical extras retain their original Synthesis/Mean paths and identities.
inherited=None
probe_raw=(root/'probe_lowertrim_repair.py').read_bytes()
assert hashlib.sha256(probe_raw).hexdigest()=='09cbbdf5d444691fb04e4f43def73e85026c37a90255c61fa46df6f60c1a561f'
for n in ast.parse(probe_raw).body:
 if isinstance(n,ast.Assign) and isinstance(n.targets[0],ast.Name) and n.targets[0].id=='RETAINED_EXTRA_PINS':inherited=ast.literal_eval(n.value)
assert inherited is not None and len(inherited)==5
s=old.decode();s=re.sub(r'\b(?:AA|AB|AC)\b',lambda m:{'AA':'AC','AB':'AD','AC':'AE'}[m[0]],s);s=s.replace('AA_ANCHOR','AC_ANCHOR')
s=s.replace('P5OriginalSharpPrimeSynthesis','P5OriginalSingletonLowerTrimPaid').replace('SharpPrimeSynthesis','LowerTrimPaid')
s=s.replace('P5PrimeDivisorMeanCorrection','P5OriginalSharpPrimeSynthesis')
s=s.replace('EXACT_SINGLE_SYNTHESIS','EXACT_SINGLE_LOWERTRIM')
s=s.replace('PUBLIC_MEAN','PUBLIC_SYNTHESIS').replace('MEAN','SYNTHESIS').replace('Mean','Synthesis')
s=s.replace('_AA_','_AC_').replace('AA_original_Synthesis','AC_original_Synthesis')
s=s.replace('_AC_Y_W_U_S_Q','_AC_AA_Y_W_U_S_Q').replace('AC/Y/W/U/S/Q','AC/AA/Y/W/U/S/Q')
s=s.replace('(AC, Y, W, U, S, Q)','(AC, AA, Y, W, U, S, Q)')
s=s.replace('Y/W/U/S/Q or their earlier identities','AA/Y/W/U/S/Q or their earlier identities')
s=s.replace('p15-synthesis','p15-lowertrim').replace('apply_synthesis_repair.py','apply_lowertrim_repair.py')
s=s.replace('unchanged_AC_synthesis_repair_reader','unchanged_AC_lowertrim_repair_reader')
s=s.replace('collect_aa_acceptance.py','collect_ac_acceptance.py')
s=s.replace('ACTUAL_AA_','ACTUAL_AC_').replace('ACTUAL_SYNTHESIS_PROBE_RESULT.json','ACTUAL_LOWERTRIM_PROBE_RESULT.json')
s=s.replace('p15_sharp_prime_synthesis_one_proof_splice_candidate_v1','p15_singleton_lower_trim_paid_one_proof_splice_candidate_v1')
s=s.replace("repair['declaration_count'] == 18","repair['declaration_count'] == 8")
s=re.sub(r'\b(?:108|107|152)\b',lambda m:{'108':'112','107':'111','152':'153'}[m[0]],s)
s=s.replace('(22, 22)','(28, 28)').replace('remaining5','remaining4').replace('five-target','four-target').replace('five_target','four_target')
s=s.replace('len(fresh.supplier_evidence) == 25','len(fresh.supplier_evidence) == 26').replace('all_twelve_earlier_prior_acceptances','all_thirteen_earlier_prior_acceptances')
s=s.replace('original_twelve_prior_identities_and_later_retained_receipts_preserved','original_thirteen_prior_identities_and_later_retained_receipts_preserved')
s=s.replace('published_AB_inputs','published_AD_inputs')
s=s.replace("         repair['prior_failed_whole_module_probes'] == PRIOR_FAILED_PROBES and\n",'')
s=s.replace('FAILED_PROBE_RETAINED','INHERITED_EXTRA_PINS')
a='(reader.AC, reader.Z, reader.Y, reader.W, reader.U, reader.S, reader.Q, reader.REPO, reader.PROJECT, reader.ROOT,\n          reader.DRIVER_FP, reader.MANIFEST_FP) ==\n         (AC, AC_ANCHOR, Y, W, U, S, Q, REPO, PROJECT, OLD_ROOT, DRIVER_FP, MANIFEST_FP)'
b='(reader.AC, reader.AB, reader.AA, reader.Y, reader.W, reader.U, reader.S, reader.Q, reader.REPO, reader.PROJECT, reader.ROOT,\n          reader.DRIVER_FP, reader.MANIFEST_FP) ==\n         (AC, AC_ANCHOR, AA, Y, W, U, S, Q, REPO, PROJECT, OLD_ROOT, DRIVER_FP, MANIFEST_FP)'
assert a in s;s=s.replace(a,b)
a="REMAINING = [TARGET, 'ImbalancedChen.P5OriginalSingletonLowerTrimPaid',\n"
assert a in s;s=s.replace(a,'REMAINING = [TARGET,\n')
meta=json.loads(Path('/tmp/p15-ac-actual/ACTUAL_AC_METADATA.json').read_text());repair=json.loads((root/'REPAIR_CANDIDATE.json').read_text())
assert 'prior_failed_whole_module_probes' not in repair
fp=lambda b:{'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()};pin=lambda d:{k:d[k] for k in ('bytes','sha256')}
constants={'AC':'9f2013ad9cb9caac9cec03cb213d9949c4443c65','AC_ANCHOR':'60e6b6e18fbda5f6b0e997d15392b32100e854d9','FAILED_JOB':'job_a108c4d7e2594e1fb5a674382db6600f','DRIVER_FP':fp(Path('/tmp/p15-entrypoint-ac/run_selected.py').read_bytes()),'MANIFEST_FP':fp(Path('/tmp/p15-entrypoint-ac/SOURCE_MANIFEST.json').read_bytes()),'BEFORE':repair['before'],'AFTER':repair['after'],'SETUP_FP':pin(meta['failures']['ImbalancedChen.P5OriginalSingletonLowerTrimPaid']['artifact_slots']['/workspace/blue-member-build/.lake/build/ir/ImbalancedChen/P5OriginalSingletonLowerTrimPaid.setup.json']),'INPUTS':None,'INHERITED_EXTRA_PINS':inherited}
lines=s.splitlines(True);edits=[]
for n in ast.parse(s).body:
 if not (isinstance(n,ast.Assign) and len(n.targets)==1 and isinstance(n.targets[0],ast.Name)):continue
 key=n.targets[0].id
 if key=='PRIOR_FAILED_PROBES':edits.append((n.lineno-1,n.end_lineno,''));continue
 if key not in constants:continue
 replacement=key+' = '+pprint.pformat(constants[key],width=110,sort_dicts=False)+'\n'
 if key=='AC_ANCHOR':replacement+="AA = 'ae373b971d2b88f97532dc883d835751dd10c67b'\n"
 edits.append((n.lineno-1,n.end_lineno,replacement))
assert len(edits)==len(constants)+1
for a,b,replacement in reversed(edits):lines[a:b]=[replacement]
s=''.join(lines).replace('# Exact AD publication, six raw inputs and actual successful probe identity.','# HOLD until the actual AD publication, successful probe and six exact raw inputs are supplied.')
assert 'PRIOR_FAILED_PROBES' not in s and 'prior_failed_whole_module_probes' not in s
assert "ARCHIVE_NAME = 'P5OriginalSingletonLowerTrimPaid.setup.json'" in s
assert "PUBLIC_SYNTHESIS = 'docs/p1/20261125/p15-current-public-acceptance/SYNTHESIS_AC_PUBLIC_ACCEPTANCE.json'" in s
assert 'INPUTS = None' in s and '(AC, AA, Y, W, U, S, Q)' in s and 'original_AC_four_target_preflight' in s
ast.parse(s);p=root/'apply_lowertrim_repair.py';p.write_text(s);print(p.name,len(p.read_bytes()),hashlib.sha256(p.read_bytes()).hexdigest())
