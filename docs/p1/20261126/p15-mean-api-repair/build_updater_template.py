from pathlib import Path
import ast, hashlib, json, pprint, re
root=Path('/tmp/p15-mean-repair')
oldpath=Path('/tmp/p15-endpoint-repair/apply_endpoint_repair.py');raw=oldpath.read_bytes()
assert len(raw)==30797 and hashlib.sha256(raw).hexdigest()=='5496cf213affce3f3f9193ef0500900d86e9da3b236b01c41a0a49c437b64d6c'
s=raw.decode()
# Simultaneously rebind original W / repair X / execution Y to Y / Z / AA.
s=re.sub(r'\b(?:W|X|Y)\b',lambda m:{'W':'Y','X':'Z','Y':'AA'}[m[0]],s)
s=s.replace('W_ANCHOR','Y_ANCHOR')
s=s.replace('P5OriginalPrimeEndpointLogPayment','P5PrimeDivisorMeanCorrection')
s=s.replace('EndpointLogPayment','MeanCorrection')
s=s.replace('P1OriginalSingletonSmoothLicence','P5OriginalPrimeEndpointLogPayment')
s=s.replace('PUBLIC_SMOOTH','PUBLIC_ENDPOINT').replace('SMOOTH','ENDPOINT').replace('Smooth','Endpoint')
s=s.replace('_W_', '_Y_').replace('published_X_inputs','published_Z_inputs')
s=s.replace('W_original_Endpoint', 'Y_original_Endpoint')
s=s.replace('_Y_U_S_Q', '_Y_W_U_S_Q').replace('Y/U/S/Q','Y/W/U/S/Q')
s=s.replace('(Y, U, S, Q)', '(Y, W, U, S, Q)')
s=s.replace('U/S/Q or their earlier identities', 'W/U/S/Q or their earlier identities')
s=s.replace('same-W reuse', 'same-Y reuse')
s=s.replace('p15-endpoint', 'p15-mean').replace('apply_endpoint_repair.py','apply_mean_repair.py')
s=s.replace('unchanged_Y_endpoint_repair_reader','unchanged_Y_mean_repair_reader')
s=s.replace('collect_w_acceptance.py','collect_y_acceptance.py')
s=s.replace('ACTUAL_W_', 'ACTUAL_Y_').replace('ACTUAL_ENDPOINT_PROBE_RESULT.json','ACTUAL_MEAN_PROBE_RESULT.json')
s=s.replace('EXACT_SINGLE_ENDPOINT','EXACT_SINGLE_MEAN')
s=s.replace('p15_endpoint_log_payment_two_proof_splices_candidate_v1','p15_prime_divisor_mean_correction_three_proof_splices_candidate_v1')
s=s.replace('two proof splices','three proof splices').replace("len(repair['splices']) == 2","len(repair['splices']) == 3")
s=s.replace("repair['declaration_count'] == 9","repair['declaration_count'] == 16")
s=s.replace('130','110').replace('129','109').replace('150','151')
s=s.replace('(11, 11)', '(24, 24)')
s=s.replace('remaining7','remaining6').replace('seven-target','six-target').replace('seven_target','six_target')
s=s.replace('len(fresh.supplier_evidence) == 23','len(fresh.supplier_evidence) == 24')
s=s.replace('all_ten_earlier_prior_acceptances','all_eleven_earlier_prior_acceptances')
a='(reader.Y, reader.V, reader.U, reader.S, reader.Q, reader.REPO, reader.PROJECT, reader.ROOT,\n          reader.DRIVER_FP, reader.MANIFEST_FP) ==\n         (Y, Y_ANCHOR, U, S, Q, REPO, PROJECT, OLD_ROOT, DRIVER_FP, MANIFEST_FP)'
b='(reader.Y, reader.X, reader.W, reader.U, reader.S, reader.Q, reader.REPO, reader.PROJECT, reader.ROOT,\n          reader.DRIVER_FP, reader.MANIFEST_FP) ==\n         (Y, Y_ANCHOR, W, U, S, Q, REPO, PROJECT, OLD_ROOT, DRIVER_FP, MANIFEST_FP)'
assert a in s;s=s.replace(a,b)
a="REMAINING = [TARGET, 'ImbalancedChen.P5PrimeDivisorMeanCorrection',\n"
assert a in s;s=s.replace(a,'REMAINING = [TARGET,\n')
# Exact constants from the actual Y metadata and successful whole-module probe.
meta=json.loads(Path('/tmp/p15-y-actual/ACTUAL_Y_METADATA.json').read_text())
repair=json.loads((root/'REPAIR_CANDIDATE.json').read_text())
fp=lambda b:{'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
pin=lambda v:{k:v[k] for k in ('bytes','sha256')}
constants={
 'Y':'f6e63d1b9785be30a607fb0ff55151ca95d1a6aa',
 'Y_ANCHOR':'09bf8a02b4c96798930abe2826cfb27529c01ad3',
 'FAILED_JOB':'job_579a949c0cfa4b85a4b678592bbc7295',
 'DRIVER_FP':fp(Path('/tmp/p15-entrypoint-y/run_selected.py').read_bytes()),
 'MANIFEST_FP':fp(Path('/tmp/p15-entrypoint-y/SOURCE_MANIFEST.json').read_bytes()),
 'BEFORE':repair['before'],'AFTER':repair['after'],
 'SETUP_FP':pin(meta['failures']['ImbalancedChen.P5PrimeDivisorMeanCorrection']['artifact_slots']['/workspace/blue-member-build/.lake/build/ir/ImbalancedChen/P5PrimeDivisorMeanCorrection.setup.json']),
 'INPUTS':None,
}
lines=s.splitlines(True);nodes=ast.parse(s).body;edits=[]
for node in nodes:
 if isinstance(node,ast.Assign) and len(node.targets)==1 and isinstance(node.targets[0],ast.Name) and node.targets[0].id in constants:
  name=node.targets[0].id;replacement=name+' = '+pprint.pformat(constants[name],width=110,sort_dicts=False)+'\n'
  if name=='Y_ANCHOR':replacement+="W = '6484b348b82d8ca6221262bb53f255fa92e9adc8'\n"
  edits.append((node.lineno-1,node.end_lineno,replacement))
assert len(edits)==len(constants)
for a,b,replacement in reversed(edits):lines[a:b]=[replacement]
s=''.join(lines)
s=s.replace('# Exact Z publication, six raw inputs and actual successful probe identity.', '# HOLD until the actual Z publication and its six exact raw inputs are supplied.')
s=s.replace("repair['before'] == BEFORE and repair['after'] == AFTER and len(repair['splices']) == 3 and", "repair['before'] == BEFORE and repair['after'] == AFTER and len(repair['splices']) == 3 and\n         repair['original_failure_metadata'] == PINS[DIAGNOSTICS] and")
# Basename and all original APIs stay concrete; the unbound gate precedes access.
assert "ARCHIVE_NAME = 'P5PrimeDivisorMeanCorrection.setup.json'" in s
assert "PUBLIC_ENDPOINT = 'docs/p1/20261125/p15-current-public-acceptance/ENDPOINT_Y_PUBLIC_ACCEPTANCE.json'" in s
assert "INPUTS = None" in s
assert "(Y, W, U, S, Q)" in s
assert 'original_Y_six_target_preflight' in s
ast.parse(s)
out=root/'apply_mean_repair.py';out.write_text(s)
print(out.name,len(out.read_bytes()),hashlib.sha256(out.read_bytes()).hexdigest())
