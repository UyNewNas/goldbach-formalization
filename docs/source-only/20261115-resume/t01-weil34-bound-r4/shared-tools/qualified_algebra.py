"""Explicit prior-direct-producer input qualification; never stock eligibility.

Install beside the unchanged R2 shared engine. ROOT must first fill and freeze
the actual payload/acquisition slots. No code path executes Lean or fabricates
a Lake trace. The consumer still replays/exports all34 through the R2 gates.
"""
import hashlib
import json
import os
from pathlib import Path
import shutil
import sys
import zipfile
import zlib

from coherent_cache import BASELINE_GUARD, checked, read, require, sha
from weil_scope import BUNDLE, SOURCE, bind, data, installed

MODULE = 'LeanPool.KloostermanWeil.Stepanov.Algebra'
PRIOR_HEAD = '317e76370eb2792fdcdba38f94a3cb361ce40110'
PRIOR_SCOPE = '737d66e3506b0b8879d473414c069579e2ffc6b046e29d803b854809e7db3e5c'
PRIOR_REGISTRY = 'cc0854deb34a33aa19ecb822e67d098310e700b9935c828d5a92fdf3500a74d1'
PROFILE = '26a6b01a52446ad6aae63d5201330b902ec94a1171fb1f0baf9fc61016098491'
LIGHT = 'b5d21169e4591c984352faef4b9cadb9d6d020b5827d9fea3e40f5b2fa2fa5a1'
COLLECTOR = '773e4eab588c0d196c5b7ad86a3a0f90a6a0fe1c225baa7559b2b1380e853a76'
CONSUMER_SOURCE = SOURCE


def file_record(path):
    path = Path(path)
    require(path.is_file() and not path.is_symlink(), 'Missing/nonregular physical qualification input')
    return dict(path=str(path), bytes=path.stat().st_size, sha256=sha(path))


def relative(root, value):
    part = Path(value)
    require(not part.is_absolute() and '..' not in part.parts, 'Prior payload path escape')
    path = root/part
    require(path.resolve().is_relative_to(root), 'Prior payload escaped its disjoint input root')
    return path


def selection(session):
    control, binding = bind()
    require(binding == session.binding and os.environ.get('GITHUB_ACTIONS') == 'true'
            and sys.platform == 'linux' and binding['source_commit'] == CONSUMER_SOURCE
            and binding['run_id'] != '43643644264', 'Current distinct exact GitHub caller/source required')
    path = BUNDLE/'direct-reuse/PRIOR_DIRECT_SELECTION.json'
    require(control['direct_reuse_selection_sha256'] == sha(path), 'ROOT did not pin this exact direct-producer selection')
    selected = read(path)
    require(selected['schema'] == 'weil34-authentic-prior-direct-Algebra-selection-v1'
            and selected['status'] == 'READY_EXACT_RAW_PAYLOADS_INDEPENDENTLY_REVIEWED'
            and selected['reuseReady'] is True
            and selected['module'] == MODULE, 'HOLD: actual raw input and whole protocol review are not ready')
    require(selected['prior_binding']['driver_commit'] == PRIOR_HEAD
            and selected['prior_binding']['run_id'] == '43643644264'
            and selected['prior_binding']['run_attempt'] == '1'
            and selected['prior_binding']['source_manifest_sha256'] == PRIOR_SCOPE
            and selected['prior_binding']['registry_sha256'] == PRIOR_REGISTRY
            and selected['prior_profile_sha256'] == PROFILE
            and selected['prior_light']['sha256'] == LIGHT, 'Wrong genuine prior producer')
    for key in ['raw_checkpoint', 'final_retention']:
        row = selected[key]
        require(isinstance(row['bytes'], int) and row['bytes'] > 0
                and isinstance(row['sha256'], str) and len(row['sha256']) == 64
                and isinstance(row['artifact'], int)
                and isinstance(row['archive_sha256'], str) and len(row['archive_sha256']) == 64
                and isinstance(row['authenticated_acquisition_receipt_sha256'], str)
                and len(row['authenticated_acquisition_receipt_sha256']) == 64,
                'HOLD: ROOT actual raw artifact identity/member/acquisition is missing')
    require(all(isinstance(row['present'], bool) for row in selected['hash_sidecars'])
            and selected['Lake_trace']['present'] is False,
            'HOLD: actual complete raw file census must determine sidecars/no-trace')
    require(selected['additional_ilean']['bytes'] == 30039
            and selected['additional_ilean']['sha256'] == '1e7d220fef29df823690db9f31ce5418e9a8aecfa5a32914c85dc8fb70de2b35',
            'The real sixth .ilean output must accompany the mandatory five modern facets')
    outputs = [*selected['prior_output_facets'],selected['additional_ilean']]
    require(len(outputs) == 6 and len({r['path'] for r in outputs}) == 6
            and {r['path'] for r in selected['hash_sidecars']} == {r['path']+'.hash' for r in outputs}
            and len(selected['hash_sidecars']) == 6
            and selected['Lake_trace']['path'] == selected['prior_output_facets'][0]['path'].removesuffix('.olean')+'.trace',
            'Complete six-output and original sidecar/no-trace facts are mandatory')
    availability = selected['historical_input_availability']
    for key in ['allowlist','pins']: checked(BUNDLE/availability[key]['bundle_relative_path'],availability[key])
    old_allowlist = read(BUNDLE/availability['allowlist']['bundle_relative_path'])
    require(old_allowlist['status'] == 'PASS_FINITE_ORIGINAL_INPUTS_AVAILABLE_REUSE_AND_RUNTIME_HOLD'
            and old_allowlist['original_binding'] == selected['prior_binding']
            and old_allowlist['member_count'] == 32 and old_allowlist['exact_selected_body_bytes'] == 46005496
            and old_allowlist['reuseReady'] is False
            and old_allowlist['acquisition_receipt']['sha256'] == selected['physical_acquisition_receipt']['sha256']
            and next(r for r in old_allowlist['records'] if r['path'].endswith('/R3_ORIGINAL_INPUT_PINS.json'))['sha256']
                == availability['pins']['sha256'], 'Historical input availability review was altered or promoted to runtime authority')
    return selected


def acquisition_index(session):
    selected = selection(session)
    path = BUNDLE/'direct-reuse/PRIOR_ACQUISITION_INDEX.json'
    index = read(path)
    require(index['schema'] == 'weil34-prior-direct-exact-range-acquisition-v1'
            and index['source_reuse_count'] == 1 and index['selected_historical_members'] == 32
            and index['selected_historical_member_bytes'] == 46005496,
            'Wrong independently frozen minimal original-body acquisition scope')
    require(index['source']['sha256'] == selected['original_source']['sha256']
            and index['source']['bytes'] == selected['original_source']['bytes']
            and index['light']['sha256'] == selected['prior_light']['sha256']
            and index['light']['bytes'] == selected['prior_light']['bytes'], 'Acquisition/source/light selection differs')
    require([g['anchor']['artifact'] for g in index['artifacts']] == [14133842374,14133608168]
            and len(index['artifacts'][0]['members']) == 29 and len(index['artifacts'][1]['members']) == 3,
            'Only the 31 newly needed physical members plus existing original CHECKPOINT are admitted')
    checkpoints = [r for g in index['artifacts'] for r in g['members'] if r['member'] == 'CHECKPOINT.json']
    require(len(checkpoints) == 1 and checkpoints[0]['sha256'] == selected['raw_checkpoint']['sha256']
            and checkpoints[0]['bytes'] == selected['raw_checkpoint']['bytes'], 'Wrong actual original checkpoint body')
    require(sum(r['bytes'] for g in index['artifacts'] for r in g['members'])
            - selected['raw_checkpoint']['bytes'] + index['source']['bytes'] == 46005496,
            'Original 32-body exact acquisition byte total differs')
    expected = [index['source'],index['light'],*index['frozen_receipts'],
                *[r for g in index['artifacts'] for r in g['members']]]
    require(len({r['input_relative_path'] for r in expected}) == len(expected), 'Duplicate prior-input destination')
    for group in [dict(anchor=index['light']['anchor']),*index['artifacts']]:
        anchor = group['anchor']
        require(anchor['run'] == 43643644264 and anchor['head_sha'] == PRIOR_HEAD,
                'Prior acquisition would read a different authentic producer')
    for row in index['frozen_receipts']: checked(BUNDLE/row['bundle_relative_path'],row)
    return index,path,expected


def check_acquisition_producer(metadata,anchor):
    require(not metadata['expired'] and metadata['id'] == anchor['artifact']
            and metadata['size_in_bytes'] == anchor['artifactBytes']
            and metadata['digest'] == 'sha256:'+anchor['githubWholeArtifactDigest']
            and metadata['workflow_run']['id'] == anchor['run'] == 43643644264
            and metadata['workflow_run']['head_sha'] == anchor['head_sha'] == PRIOR_HEAD,
            'Prior actual artifact acquisition identity/run/head/digest changed')


def acquire(session):
    """GitHub-only bounded acquisition using the unchanged original reader."""
    from coherent_cache import ArchiveReader
    from weil_cache import WeilSession
    installed(); session.require_fixtures(); WeilSession.stock_qualification_inputs(session)
    index,path,expected = acquisition_index(session)
    root = Path(os.environ['WEIL_DIRECT_INPUTS']).resolve()
    require(not root.exists() and not root.is_relative_to(session.project) and not root.is_relative_to(session.logs),
            'Fresh disjoint original prior-input directory required')
    root.mkdir(parents=True)
    rows = []
    for row in index['frozen_receipts']:
        target = relative(root,row['input_relative_path']); target.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(BUNDLE/row['bundle_relative_path'],target); checked(target,row)
        rows.append(dict(origin='FROZEN_AUTHENTIC_ORIGINAL_ACQUISITION_RECEIPT',**file_record(target)))
    source = index['source']; source_path = session.project/source['project_relative_path']
    checked(source_path,source)
    require(format(zlib.crc32(source_path.read_bytes()) & 0xffffffff,'08x') == source['crc32'], 'Original source CRC differs')
    target = relative(root,source['input_relative_path']); target.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(source_path,target); checked(target,source)
    rows.append(dict(origin='EXACT_CURRENT_STAGED_ALGEBRA_SOURCE_BYTES',**file_record(target)))
    metadata = []
    light = index['light']; reader = ArchiveReader(light['anchor'])
    check_acquisition_producer(reader.metadata,light['anchor'])
    require(reader.metadata['workflow_run']['head_sha'] == PRIOR_HEAD and light['bytes'] == 12591951
            and light['bounded_small_archive_only'] is True, 'Only the fixed small original light archive is permitted')
    target = relative(root,light['input_relative_path'])
    with target.open('xb') as output:
        for offset in range(0,light['bytes'],8*1024*1024):
            output.write(reader.part(offset,min(8*1024*1024,light['bytes']-offset)))
    checked(target,light); metadata.append(reader.metadata)
    rows.append(dict(origin='EXACT_SMALL_LIGHT_WHOLE_BYTES_BOUNDED_206',**file_record(target)))
    for group in index['artifacts']:
        reader = ArchiveReader(group['anchor'])
        check_acquisition_producer(reader.metadata,group['anchor'])
        require(reader.metadata['workflow_run']['head_sha'] == PRIOR_HEAD, 'Prior range producer head changed')
        metadata.append(reader.metadata)
        temporary = root/('.ranges-'+str(group['anchor']['artifact'])); temporary.mkdir()
        for row in group['members']:
            reader.fetch(row['member'],row,temporary)
            target = relative(root,row['input_relative_path']); target.parent.mkdir(parents=True,exist_ok=True)
            require(not target.exists(),'Refuse prior-original acquisition overwrite')
            (temporary/row['member']).rename(target); checked(target,row)
            rows.append(dict(origin='EXACT_AUTHENTIC_STORED_ZIP_MEMBER_RANGE',**file_record(target)))
    for row in expected: checked(relative(root,row['input_relative_path']),row)
    session.emit('WEIL_PRIOR_DIRECT_ACQUISITION.json',dict(status='EXACT_ORIGINAL_BYTES_ONLY_NOT_REUSE_OR_PROOF_ACCEPTANCE',
        index_sha256=sha(path),files=rows,artifacts=metadata,large_whole_archives_downloaded=False,
        small_light_whole_archive_bytes=12591951,source_compiler_events=0,old_ABI_library_bodies_claimed_retained=False))


def validate_acquired_files(acquired,index_path,expected,root):
    require(acquired['status'] == 'EXACT_ORIGINAL_BYTES_ONLY_NOT_REUSE_OR_PROOF_ACCEPTANCE'
            and acquired['index_sha256'] == sha(index_path) and acquired['source_compiler_events'] == 0
            and acquired['large_whole_archives_downloaded'] is False,
            'Missing distinct current-caller exact original-byte acquisition')
    records = {r['path']:{k:r[k] for k in ['path','bytes','sha256']} for r in acquired['files']}
    require(len(records) == len(acquired['files']) == len(expected)
            and records == {str(relative(root,r['input_relative_path'])):
                dict(path=str(relative(root,r['input_relative_path'])),bytes=r['bytes'],sha256=r['sha256']) for r in expected},
            'Current original-byte acquisition has a missing/extra/changed actual member')
    for row in expected: checked(relative(root,row['input_relative_path']),row)


def compare_standard_inputs(standard,current_standard):
    require(standard['source_private_closure'] == current_standard['source_private_closure']
            and standard['importArts'] == current_standard['importArts']
            and standard['search_path_value'] == current_standard['search_path_value'],
            'Current exact source/private artifacts/search no longer equal the original actual inputs')


def check_current_prior_files(original_input):
    for row in original_input['files']: checked(row['path'],row)
    checked(original_input['source']['path'],original_input['source'])


def verify_current_runtime_abi(state,current_state,prior_checkpoint,current_original):
    wrappers = {state['shadow']+'/bin/'+name for name in state['tools']}
    current_wrappers = {current_state['shadow']+'/bin/'+name for name in current_state['tools']}
    previous_runtime = {p:h for p,h in state['runtime_sha256'].items() if p not in wrappers}
    current_runtime = {p:h for p,h in current_state['runtime_sha256'].items() if p not in current_wrappers}
    def abi_map(rows):
        result = {r['original_path']:(r['resolved_path'],r['bytes'],r['sha256']) for r in rows}
        require(len(result) == len(rows) == 8,'Exact eight distinct actual ABI paths required')
        return result
    require(len(previous_runtime) == 11 and previous_runtime == current_runtime
            and abi_map(prior_checkpoint['native_and_toolchain_library_ABI_receipts']) == abi_map(current_original['native_and_toolchain_library_ABI_receipts']),
            'Exact original native compiler/runtime ABI changed')
    for path, expected in previous_runtime.items(): require(sha(path) == expected, 'Current official runtime payload changed')
    for row in prior_checkpoint['native_and_toolchain_library_ABI_receipts']:
        actual = Path(row['original_path']).resolve(strict=True)
        require(str(actual) == row['resolved_path'],'Current actual ABI library resolution differs')
        checked(actual,row)
    require(prior_checkpoint['packages'] == current_original['packages'], 'Original eleven package owners/options changed')


class PriorDirect:
    # R1 remains the default, including every original immutable binding.
    # R4's R3 context varies only these explicit producer parameters.
    module = MODULE
    scope_sha = PRIOR_SCOPE
    light_sha = LIGHT
    input_subdir = ''
    acquisition_receipt = 'WEIL_PRIOR_DIRECT_ACQUISITION.json'
    scope_relative_path = 'direct-reuse/PRIOR_STAGE_A34.json'
    prior_tools = '/home/runner/work/goldbach-formalization/goldbach-formalization/docs/source-only/20261115-resume/t01-weil34-26a6/shared-tools'
    event_count = 23
    source_event_count = 2
    source_event_index = 0
    result_has_ilean = False

    def choose_selection(self, session):
        return selection(session)

    def choose_acquisition_index(self, session):
        return acquisition_index(session)

    def expected_result_facets(self):
        # Historical JSON shape only. Both producer contexts restore/check the
        # mandatory five modern files PLUS the separately recorded real ilean.
        facets = self.selected['prior_output_facets']
        return [*facets, self.selected['additional_ilean']] if self.result_has_ilean else facets

    def __init__(self, session):
        self.session = session; self.selected = self.choose_selection(session)
        self.inputs = (Path(os.environ['WEIL_DIRECT_INPUTS'])/self.input_subdir).resolve()
        require(not self.inputs.is_relative_to(session.project) and not self.inputs.is_relative_to(session.logs),
                'Prior-direct originals must be disjoint from consumer project/logs')
        index,index_path,expected = self.choose_acquisition_index(session)
        acquired = session.receipt(self.acquisition_receipt)
        validate_acquired_files(acquired,index_path,expected,self.inputs)
        self.used_payloads = {}
        self.body_sources = {}
        self.current_authenticated_streams = []
        light_path = relative(self.inputs, self.selected['prior_light']['input_relative_path'])
        checked(light_path, self.selected['prior_light'])
        self.used_payloads[str(light_path)] = file_record(light_path)
        self.light = zipfile.ZipFile(light_path)
        require(self.light.testzip() is None, 'Original light archive CRC failed')
        scope_path = BUNDLE/self.scope_relative_path
        require(sha(scope_path) == self.scope_sha, 'Original exact34 scope bytes changed')
        self.scope = read(scope_path); self.old = self.selected['prior_binding']
        self.cp = self.load_selected('raw_checkpoint')
        self.retention = self.load_selected('final_retention')
        require(self.retention['binding'] == self.old and self.retention['exit_code'] == 0
                and not self.retention['integrity_errors'] and self.retention['collector_sha256'] == COLLECTOR,
                'Original real collector retention failed or belongs to another producer')

    def load_selected(self, key):
        row = self.selected[key]; path = relative(self.inputs, row['input_relative_path'])
        checked(path, row); self.used_payloads[str(path)] = file_record(path)
        acquisition_path = relative(self.inputs, row['acquisition_receipt_relative_path'])
        require(sha(acquisition_path) == row['authenticated_acquisition_receipt_sha256'], 'ROOT acquisition receipt changed')
        acquisition = read(acquisition_path)
        require(acquisition['schema'] in {'READ_ONLY_STORED_ZIP_METADATA_RANGE_RECEIPT_V1','READ_ONLY_STORED_ZIP_PHYSICAL_MEMBER_RANGE_RECEIPT_V1'}
                and acquisition['artifact']['id'] == row['artifact']
                and str(acquisition['artifact']['workflow_run']['id']) == self.old['run_id']
                and acquisition['artifact']['workflow_run']['head_sha'] == self.old['driver_commit']
                and acquisition['artifact']['digest'] == 'sha256:'+row['archive_sha256']
                and not acquisition['failures'] and acquisition['requested_members_complete'],
                'Wrong actual original range/artifact/member authority')
        member = next((m for m in acquisition['members'] if m['name'] == row['member']), None)
        require(member and member['crc_verified'] and member['sha256'] == row['sha256']
                and member['uncompressed_bytes'] == row['bytes'], 'Original actual member receipt does not bind its real body')
        self.used_payloads[str(acquisition_path)] = file_record(acquisition_path)
        return read(path)

    def light_json(self, member):
        value = json.loads(self.light.read(member))
        if isinstance(value, dict) and 'binding' in value:
            require(value['binding'] == self.old, 'Original light receipt rebound to another run')
        return value

    def original_file(self, old_path):
        row = self.cp['files'].get(str(old_path))
        require(row and 'payload' in row and row['payload'].startswith('objects/'),
                'Real prior file lacks original raw retained bytes: '+str(old_path))
        payload = relative(self.inputs, 'raw/'+row['payload'])
        if not payload.is_file() and str(old_path).startswith('/home/runner/work/_temp/weil34-evidence/'):
            # Reuse only actual existing bytes with the same external raw hash.
            # Never reconstruct a nonempty historical stream from a summary.
            member = str(old_path).removeprefix('/home/runner/work/_temp/weil34-evidence/')
            matching = []
            if member in self.light.namelist(): matching.append(('prior-light:'+member,self.light.read(member)))
            if row['bytes'] == 0:
                empty = next((i for i in self.light.infolist() if i.file_size == 0),None)
                if empty: matching.append(('prior-light:'+empty.filename,self.light.read(empty.filename)))
            for stream in self.current_authenticated_streams:
                path = Path(stream)
                if path.is_file() and path.stat().st_size == row['bytes'] and sha(path) == row['sha256']:
                    matching.append(('current-authenticated-stock-stream:'+str(path),path.read_bytes())); break
            for origin,content in matching:
                if len(content) == row['bytes'] and hashlib.sha256(content).hexdigest() == row['sha256']:
                    payload.parent.mkdir(parents=True,exist_ok=True)
                    require(not payload.exists(),'Refuse original-body overwrite')
                    payload.write_bytes(content); self.body_sources[str(payload)] = origin
                    break
        checked(payload, row)
        self.used_payloads[str(payload)] = file_record(payload)
        return payload, row

    def external_file(self, old_path, expected):
        # Files written after the checkpoint (collector stdout/summary/retention)
        # require their actual final-artifact member, never a self-signed digest.
        row = self.selected['post_checkpoint_files'].get(str(old_path))
        require(row and row['sha256'] == expected, 'HOLD: final actual collector stream/member not supplied')
        path = relative(self.inputs,row['input_relative_path']); checked(path,row)
        require(row['artifact'] == self.selected['final_retention']['artifact'], 'Wrong final evidence artifact')
        acquisition_path = relative(self.inputs,row['acquisition_receipt_relative_path'])
        require(sha(acquisition_path) == row['authenticated_acquisition_receipt_sha256'], 'Final actual member acquisition changed')
        acquisition = read(acquisition_path)
        require(acquisition['schema'] == 'READ_ONLY_STORED_ZIP_PHYSICAL_MEMBER_RANGE_RECEIPT_V1'
                and acquisition['artifact']['id'] == row['artifact']
                and str(acquisition['artifact']['workflow_run']['id']) == self.old['run_id']
                and acquisition['artifact']['workflow_run']['head_sha'] == self.old['driver_commit']
                and acquisition['artifact']['digest'] == 'sha256:'+self.selected['final_retention']['archive_sha256']
                and not acquisition['failures'] and acquisition['requested_members_complete'], 'Final member is from another actual producer')
        member = next((m for m in acquisition['members'] if m['name'] == row['member']),None)
        require(member and member['crc_verified'] and member['sha256'] == row['sha256']
                and member['uncompressed_bytes'] == row['bytes'], 'Final raw stream/body does not match its acquisition')
        self.used_payloads[str(path)] = file_record(path)
        self.used_payloads[str(acquisition_path)] = file_record(acquisition_path)
        return path

    def original_json(self, old_path):
        path, _ = self.original_file(old_path)
        return read(path)

    def process(self, p, label, argv):
        logs = '/home/runner/work/_temp/weil34-evidence'
        require(p['argv'] == argv and p['cwd'] == self.selected['prior_project'] and p['exit_code'] == 0
                and p['stdout'] == logs+'/cache-processes/'+label+'.stdout'
                and p['stderr'] == logs+'/cache-processes/'+label+'.stderr', 'Prior actual argv/cwd/exit/stream paths changed')
        original = self.original_json(logs+'/cache-processes/'+label+'.json')
        require(original == dict(binding=self.old, **p), 'Prior process receipt is not its authentic original bytes')
        for kind in ['stdout', 'stderr']:
            path, _ = self.original_file(p[kind])
            require(sha(path) == p[kind+'_sha256'], 'Prior process raw '+kind+' changed')
        return self.original_file(p['stdout'])[0]

    def validate_history(self, current_standard):
        session = self.session; old = self.old
        current_bootstrap = session.receipt('CACHE_BOOTSTRAP_QUALIFICATION.json')
        def bootstrap_processes(value):
            found = [value['dependency_checkout_process'],value['stock_binary_process'],value['stock_cache_get_process'],
                     value['leaf_identity']['search_path_process']]
            found.extend(r['official_current_setup_process'] for r in value['setups'])
            found.extend(v for k,v in value['glibc_identity'].items() if k.endswith('_process'))
            return {Path(p['stdout']).stem:p for p in found}
        current_processes = bootstrap_processes(current_bootstrap)
        current_processes.update({Path(p['stdout']).stem:p for p in [current_standard['stock_process'],current_standard['search_path_process'],
            *[q['process'] for q in current_standard['setup_queries']]]})
        self.current_authenticated_streams = [p[key] for p in current_processes.values() for key in ['stdout','stderr']]
        require(str(session.project) == self.selected['prior_project']
                and session.state['realbin'] == self.selected['prior_realbin']
                and session.state['shadow'] == self.selected['prior_shadow'],
                'Different roots require a separately reviewed explicit mapping; no silent rewrite')
        require(str(self.cp['run_id']) == old['run_id'] and str(self.cp['run_attempt']) == old['run_attempt']
                and self.cp['source_commit'] == old['source_commit'] and self.cp['runtime_audit_valid']
                and self.cp['all_dependency_source_pins_valid'], 'Wrong original checkpoint run/source/runtime')
        rows = [dict(module=r['module'],install_path=r['installation_path'],bytes=r['bytes'],sha256=r['sha256'],imports=r['imports'])
                for r in self.scope['source_rows']]
        graph_hash = hashlib.sha256(json.dumps(rows,sort_keys=True).encode()).hexdigest()
        oldlogs = '/home/runner/work/_temp/weil34-evidence'
        oldbundle = self.prior_tools
        manifest = self.original_json(oldlogs+'/CHECKPOINT_COLLECTOR_INPUT.json')
        audit_bytes = self.light.read('T01Audit.lean')
        expected_manifest = dict(files=rows,data_inputs=[],audit_source=dict(bytes=len(audit_bytes),sha256=hashlib.sha256(audit_bytes).hexdigest()),
            targets=[dict(closure_modules=[r['module'] for r in rows],source_identity_sha256=graph_hash)])
        ret = self.retention
        expected_collector = ['/usr/bin/python3',oldbundle+'/reference/checkpoint_objects_v3.py','--project',self.selected['prior_project'],
            '--manifest',oldlogs+'/CHECKPOINT_COLLECTOR_INPUT.json','--logs',oldlogs,'--output',ret['output']]
        require(ret['argv'] == expected_collector and ret['cwd'] == self.selected['prior_project']
                and ret['collector_bytes'] == 32993 and manifest == expected_manifest
                and ret['source_manifest_sha256'] == self.scope_sha and ret['root_source_count'] == 34
                and ret['root_source_rows_sha256'] == graph_hash and self.cp['source_identity_sha256'] == graph_hash
                and ret['checkpoint_sha256'] == self.selected['raw_checkpoint']['sha256']
                and ret['collector_manifest_sha256'] == self.cp['manifest_sha256'], 'Original collector exact argv/manifest/source graph changed')
        old_provenance = self.original_json(self.selected['prior_project']+'/T01_PROVENANCE.json')
        require(old_provenance == dict(schema='weil34-exact-source-original-profile-provenance-v1',binding=old,
                modules=self.scope['source_rows'],adapter_stage_B='HOLD',full_J=False), 'Original staged provenance changed')
        provenance_file,_ = self.original_file(self.selected['prior_project']+'/T01_PROVENANCE.json')
        require(sha(provenance_file) == ret['provenance_sha256'], 'Original collector provenance hash differs')
        expected_summary = dict(status=self.cp['status'],completed_compile_candidates=self.cp['completed_compile_candidates'],
            module_count=len(self.cp['modules']),payload_blobs=self.cp['saved_unique_payload_blobs'],
            checkpoint_sha256=self.selected['raw_checkpoint']['sha256'],green=False)
        summary_path = self.external_file(oldlogs+'/CHECKPOINT_SUMMARY.json',ret['actual_collector_summary_sha256'])
        require(read(summary_path) == ret['actual_collector_summary'] == expected_summary,
                'Actual original collector summary/source/run binding changed')
        self.external_file(oldlogs+'/checkpoint-collection.log',ret['stdout_sha256'])
        state = self.light_json('runtime/state.json'); audit = self.light_json('runtime/audit.json')
        require(self.cp['runtime_state'] == state and state['guard_sha256'] == BASELINE_GUARD
                and audit['probe'] is True and audit['status'] == 'PASS_RUNTIME_GUARD_ONLY'
                and audit['source_commands'] == self.source_event_count
                and hashlib.sha256(self.light.read('runtime/state.json')).hexdigest() == audit['state_sha256']
                and hashlib.sha256(self.light.read('runtime/compiler-commands.jsonl')).hexdigest() == audit['command_log_sha256'],
                'Original runtime/probe/commands were not genuine')
        checkpoint_summary = {k:self.cp[k] for k in ['source_commit','run_id','run_attempt','manifest_sha256',
                                                   'runtime_audit_valid','all_dependency_source_pins_valid']}
        require(ret['checkpoint_summary'] == checkpoint_summary
                and ret['runtime_state_sha256'] == audit['state_sha256']
                and ret['current_command_log'] == dict(path=state['log'],sha256=audit['command_log_sha256']),
                'Original collector state/current-command/run-attempt receipt changed')
        for member in ['runtime/state.json','runtime/audit.json','runtime/compiler-commands.jsonl']:
            path = oldlogs+'/'+member
            require(self.cp['files'][path]['sha256'] == hashlib.sha256(self.light.read(member)).hexdigest(),
                    'Original checkpoint does not bind its actual runtime/audit/command bytes')
        require(state['input_sha256'] == session.state['input_sha256']
                and state['input_sha256'][str(session.project/'lakefile.toml')] == PROFILE,
                'Original full profile/configuration changed')
        verify_current_runtime_abi(state,session.state,self.cp,session.original())
        require(not self.light.read('CACHE_COMPILER_DENIALS.jsonl'), 'Original denied compiler attempt exists')
        events = [json.loads(line) for line in self.light.read('CACHE_PREEXEC_EVENTS.jsonl').decode().splitlines() if line.strip()]
        commands = [json.loads(line) for line in self.light.read('runtime/compiler-commands.jsonl').decode().splitlines() if line.strip()]
        require(len(events) == len(commands) == self.event_count, 'Original command/event census changed')
        for event, command in zip(events, commands):
            require(event['context'] == old and event['compiler_exec_permitted'] is True
                    and (event['pid'],event['tool'],event['argv'],event['cwd']) ==
                        (command['pid'],command['tool'],command['command'][1:],command['cwd'])
                    and event['raw_argv'] == command['input_args'], 'Original compiler event lacks its own actual command')
        source_events = [e for e in events if e['classification'] == 'EXACT_CURRENT_WEIL34_SOURCE']
        matches = [event for event in source_events if event['physical_inputs'][0] == self.selected['original_source']]
        require(len(source_events) == self.source_event_count and len(matches) == 1
                and source_events[self.source_event_index] == matches[0],
                'Original successful source event changed')
        result = self.light_json('direct-results/'+self.module+'.json')
        original_input = self.light_json('direct-inputs/'+self.module+'.json')
        input_bytes = self.light.read('direct-inputs/'+self.module+'.json')
        require(result['input_binding'] == original_input
                and result['input_binding_sha256'] == hashlib.sha256(input_bytes).hexdigest()
                and result['actual_preexec_event'] == matches[0]
                and matches[0]['physical_inputs'][1]['sha256'] == result['input_binding_sha256'],
                'Actual original source/input/preexec chain changed')
        from weil_cache import normalized_argv
        normalized = normalized_argv(self.module, session.project)
        require(normalized == self.selected['prior_normalized_argv'] == original_input['normalized_argv'],
                'Original compiler/options/output/setup argv changed')
        self.process(result['process'], 'weil-compile-'+self.module,
            ['lake','--no-build','env','lean',*normalized[3:]])
        runtime = self.light_json('WEIL_RUNTIME_PROCESS.json')['process']
        self.process(runtime, 'runtime-audit', ['/usr/bin/python3',oldbundle+'/reused/ci_runtime_guard.py','audit','--probe','--require-source'])
        qualification = self.light_json('CACHE_QUALIFICATION.json')
        standard = self.light_json('WEIL_STANDARD_INPUTS.json')
        bootstrap = self.light_json('CACHE_BOOTSTRAP_QUALIFICATION.json')
        require(qualification['status'] == 'PASS_AUTHENTIC_STOCK_NO_BUILD_CACHE_INPUT_ONLY'
                and qualification['protected_source_compiler_events'] == 0
                and qualification['standard_inputs_sha256'] == hashlib.sha256(self.light.read('WEIL_STANDARD_INPUTS.json')).hexdigest()
                and qualification['bootstrap_qualification_sha256'] == hashlib.sha256(self.light.read('CACHE_BOOTSTRAP_QUALIFICATION.json')).hexdigest()
                and original_input['stock_inputs_sha256'] == qualification['standard_inputs_sha256'], 'Original stock qualification chain changed')
        require(bootstrap['status'] == 'PASS_AUTHENTIC_CACHE_BOOTSTRAP_STOCK_NO_BUILD_INPUT_ONLY'
                and bootstrap['selection_sha256'] == current_bootstrap['selection_sha256']
                and bootstrap['leaf_rule_sha256'] == current_bootstrap['leaf_rule_sha256']
                and bootstrap['bootstrap_source_C_and_link_compiler_events'] == 0 and bootstrap['cold_fallback'] is False,
                'Original authentic Cache144 bootstrap was not the preserved no-build route')
        old_processes = bootstrap_processes(bootstrap)
        require(set(old_processes) <= set(current_processes), 'Original mandatory bootstrap process scope changed')
        for label,p in old_processes.items(): self.process(p,label,current_processes[label]['argv'])
        for row in bootstrap['glibc_identity']['actual_libraries']: checked(row['path'],row)
        require(sha(bootstrap['glibc_identity']['md5_manifest_path']) == bootstrap['glibc_identity']['md5_manifest_sha256'],
                'Current actual glibc package bytes no longer match the genuine prior loader identity')
        names = self.scope['direct_standard_imports']
        self.process(standard['stock_process'], 'weil-standard-stock',
            ['lake','--no-build','build',*['@mathlib/+'+n+':leanArts' for n in names]])
        require(len(standard['setup_queries']) == 5, 'Original actual setup batches missing')
        for offset, query in zip(range(0,len(names),8), standard['setup_queries']):
            batch = names[offset:offset+8]
            stream = self.process(query['process'], 'weil-standard-setup-'+str(offset),
                ['lake','--no-build','--json','query',*['@mathlib/+'+n+':setup' for n in batch]])
            lines = [(number,line) for number,line in enumerate(stream.read_text(encoding='utf-8').splitlines(),1) if line.strip()]
            require(query['names'] == batch and query['offset'] == offset
                    and query['stdout_lines'] == [number for number,_ in lines]
                    and query['values'] == [json.loads(line) for _,line in lines], 'Original ordered raw setup query changed')
        search = standard['search_path_process']
        search_argv = ['lake','--no-build','env','/usr/bin/python3','-c',
            "import os,json;print(json.dumps({k:os.environ.get(k,'') for k in ['LEAN_PATH','LEAN_SYSROOT']}))"]
        self.process(search, 'weil-actual-search-path',search_argv)
        require(read(self.original_file(search['stdout'])[0]) == standard['search_path_value'], 'Original actual search process/value changed')
        compare_standard_inputs(standard,current_standard)
        prior = next(r for r in self.cp['modules'] if r['module'] == self.module)
        require(prior['classification'] == self.selected['original_collector_classification_must_remain']
                and prior['completed_guarded_compile_candidate'] is False and prior['kernel_verified'] is False,
                'Original no-Lake-trace quarantine must not be promoted to stock/proof acceptance')
        capture_path,capture_row = self.original_file(oldlogs+'/WEIL_RAW_CAPTURE.json')
        require(capture_row['sha256'] == ret['raw_capture_sha256'], 'Original retained raw-capture manifest changed')
        capture = read(capture_path)
        require(capture['binding'] == old and not capture['integrity_errors']
                and self.cp['files'][oldlogs+'/'+capture['archive']]['sha256'] == capture['archive_sha256'],
                'Original capture manifest is not bound to the original collector evidence')
        captured = {row['path']:row for row in capture['files']}
        required = [original_input['source'],*original_input['files'],*self.selected['prior_output_facets'],self.selected['additional_ilean']]
        for row in required:
            require(row['path'] in captured and captured[row['path']]['bytes'] == row['bytes']
                    and captured[row['path']]['sha256'] == row['sha256'], 'Original actual source/private/input/output was omitted from retained capture')
        return result, original_input

    def restore_and_compare(self, current_standard, restore=False):
        session = self.session
        result, original_input = self.validate_history(current_standard)
        identity = result['output_identity']
        require(identity['modern'] is True and identity['facets'] == self.expected_result_facets()
                and identity['source'] == self.selected['original_source'], 'Original source/five modern facets changed')
        current_row = next(r for r in data()['source_rows'] if r['module'] == self.module)
        require(current_row['sha256'] == identity['source']['sha256']
                and current_row['bytes'] == identity['source']['bytes']
                and current_row['git_blob'] == identity['source_provenance']['git_blob'], 'Protected source changed; prior object is ineligible')
        prior_source,prior_source_record = self.original_file(identity['source']['path'])
        require(prior_source_record['bytes'] == identity['source']['bytes']
                and prior_source_record['sha256'] == identity['source']['sha256'], 'Original actual source payload changed')
        paths = [*self.selected['prior_output_facets'], self.selected['additional_ilean'], self.selected['prior_setup_identity']]
        for row in self.selected['hash_sidecars']:
            actual = self.cp['files'].get(row['path'])
            require(row['present'] == (actual is not None), 'Sidecar presence differs from the actual original complete census')
            if row['present']:
                require(actual['bytes'] == row['bytes'] and actual['sha256'] == row['sha256'], 'Original sidecar identity changed')
                paths.append(row)
            else: require(not Path(row['path']).exists(), 'Absent original sidecar was synthesized in the consumer')
        trace = self.selected['Lake_trace']['path']
        require(trace not in self.cp['files'] and not Path(trace).exists(), 'A direct output received a fabricated Lake trace')
        for row in paths:
            source, actual = self.original_file(row['path'])
            require(actual['sha256'] == row['sha256'] and actual['bytes'] == row['bytes'], 'Wrong actual raw output/setup payload')
            target = Path(row['path'])
            require(target.resolve().is_relative_to((session.project/'.lake/build').resolve()), 'Prior restore destination escape')
            if restore:
                require(not target.exists(), 'Protected direct output already installed; no overwrite')
                target.parent.mkdir(parents=True, exist_ok=True); shutil.copyfile(source,target)
            checked(target,row)
        # Every actual preexec source/setup/import/library byte, not a digest of
        # a manually authored summary, must equal this consumer's real files.
        check_current_prior_files(original_input)
        from weil_proof import setup_value
        expected_setup, path, files = setup_value(session,self.module,current_standard)
        require(read(path) == original_input['setup'] == expected_setup,
                'Original full ModuleSetup differs from the current genuine source/stock-derived setup')
        require(original_input['setup']['imports'] is None and original_input['setup']['options'] == {}
                and original_input['setup']['isModule'] is True, 'Source header/options/mode changed')
        for row in self.used_payloads.values(): checked(row['path'],row)
        return dict(prior_binding=self.old,prior_process=result['process'],prior_input_binding_sha256=result['input_binding_sha256'],
            current_original_byte_acquisition_sha256=sha(session.logs/self.acquisition_receipt),
            prior_light_sha256=self.light_sha,prior_checkpoint_sha256=self.selected['raw_checkpoint']['sha256'],
            prior_retention_sha256=self.selected['final_retention']['sha256'],
            current_source=file_record(original_input['source']['path']),current_setup=file_record(path),
            current_five_facets=[file_record(row['path']) for row in self.selected['prior_output_facets']],
            current_additional_ilean=file_record(self.selected['additional_ilean']['path']),
            current_all_prior_actual_inputs=[file_record(row['path']) for row in original_input['files']],
            authentic_original_payloads=list(self.used_payloads.values()),source_compiler_events_permitted=0,
            exact_existing_bytes_may_be_deduplicated_only_by_external_raw_hash=True,
            prior_full_tar_or_ABI_library_bodies_claimed_retained=False,
            qualification='PRIOR_DIRECT_COMPILE_INPUT_ONLY_NOT_STOCK_NOT_PROOF_ACCEPTANCE',
            original_collector_quarantine_preserved=True,fresh_all34_kernel_types_axioms_still_required=True)


def protect_policy(policy, project):
    source = str(project/Path(*MODULE.split('.')).with_suffix('.lean'))
    rows = [row for row in policy['admitted_commands'] if row.get('source',{}).get('path') == source]
    require(len(rows) == 1, 'Original exact34 policy must contain exactly one protected source row')
    policy['admitted_commands'] = [row for row in policy['admitted_commands'] if row is not rows[0]]
    stem = str(project/'.lake/build/lib/lean'/Path(*MODULE.split('.')))
    policy['deny_exact_paths'].extend([source,*[stem+suffix for suffix in
        ['.olean','.olean.server','.olean.private','.ir.sig','.ir','.ilean','.trace','.olean.hash',
         '.olean.server.hash','.olean.private.hash','.ir.sig.hash','.ir.hash','.ilean.hash']]])
    setup = str(project/'.lake/build/ir'/Path(*MODULE.split('.')))
    policy['deny_exact_paths'].extend(setup+suffix for suffix in ['.setup.json','.c','.bc','.c.o.export','.c.o.export.trace'])
    return policy


def admit(session):
    from weil_cache import WeilSession
    installed(); session.require_fixtures(); standard = WeilSession.stock_qualification_inputs(session)
    context = PriorDirect(session); result = context.restore_and_compare(standard,restore=True)
    session.emit('WEIL_PRIOR_DIRECT_ALGEBRA_QUALIFICATION.json',result)


def validate(session, standard=None):
    from weil_cache import WeilSession
    installed(); session.require_fixtures()
    if standard is None: standard = WeilSession.stock_qualification_inputs(session)
    result = PriorDirect(session).restore_and_compare(standard)
    require(session.receipt('WEIL_PRIOR_DIRECT_ALGEBRA_QUALIFICATION.json') == dict(binding=session.binding,**result),
            'Prior/direct current-consumer qualification changed after admission')
    return result


if __name__ == '__main__':
    raise SystemExit('Library source only; ROOT must finish actual payload and caller integration before GitHub use')
