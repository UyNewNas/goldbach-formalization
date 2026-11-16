"""R4 exact two-producer direct inputs, built on the reviewed R3 gate.

Source-only HOLD until ROOT binds real missing raw members and independent
review. No Lean invocation, generated producer evidence or stock promotion.
"""
import copy
import hashlib
import json
import os
from pathlib import Path
import shutil
import sys
import zipfile

import qualified_algebra as qa
from coherent_cache import HERE, checked, read, require, sha
from weil_scope import BUNDLE, SOURCE, bind, data, installed

R3_HEAD = '2960e200301de4189c1c2793b918fc8aa7666930'
DRIVER_PARENT = '9706c50031d1b2575ae624501e352aebdcc1b591'
R3_RUN = '43657752592'
R3_SCOPE = '36db0010a096951a6c3e1186949e400c27e6658fb355c5328380cfade5a86290'
R3_LIGHT = 'b4bf5cb681e4f27284ac5d8253180b4b8931bb2dab012f0f0fbb9c1f11c26f9d'
R3_BINDING = dict(scope='WEIL34_PROJECT26A6',driver_commit=R3_HEAD,run_id=R3_RUN,
    run_attempt='1',job='weil34',source_commit='26c8c3ab7017ff27aafb60b5e26f3183f2ed8b7a',
    source_manifest_sha256=R3_SCOPE,
    root_control_sha256='2df4cb797e3584261f99a233eb63577770096cf34a04a618e6e3a63162453c2d',
    registry_sha256='2429762dba441c4e8ea6141533f3e8454800e74e401cdee36cc53bcb4d015fce')
PROTECTED = (
    qa.MODULE,
    'LeanPool.KloostermanWeil.Stepanov.Auxiliary',
    'LeanPool.KloostermanWeil.Stepanov.Parameters',
    'LeanPool.KloostermanWeil.Stepanov.CurveCount',
    'LeanPool.KloostermanWeil.Stepanov.Defect',
    'LeanPool.KloostermanWeil.Stepanov.SpecializedCurve',
    'LeanPool.KloostermanWeil.Carlitz.FactorData',
    'LeanPool.KloostermanWeil.Carlitz.DicksonFiniteAlgebra',
    'LeanPool.KloostermanWeil.Carlitz.CoefficientEquivalence',
    'LeanPool.KloostermanWeil.Carlitz.FactorWeight',
    'LeanPool.KloostermanWeil.Weil.PrimeFoundation',
    'LeanPool.KloostermanWeil.Carlitz.ExtensionDefinitions',
    'LeanPool.KloostermanWeil.Carlitz.MinimalPolynomialInverse',
    'LeanPool.KloostermanWeil.Carlitz.ClassValue',
    'LeanPool.KloostermanWeil.Carlitz.ConjugateDecomposition',
)
FAILED = 'LeanPool.KloostermanWeil.Carlitz.ClassGhost'
SUFFIXES = ('.olean','.olean.server','.olean.private','.ir.sig','.ir','.ilean')


def protected_modules():
    return PROTECTED


def check_partition(selected):
    require(selected['protected_modules'] == list(PROTECTED)
            and selected['fresh_modules'] == 19 and selected['fresh_proof_scope'] == 34,
            'R4 exact15 protected and19 fresh partition changed or failed ClassGhost promoted')
    require(selected['producers'] == {'R1':dict(driver_commit=qa.PRIOR_HEAD,run_id='43643644264',
                source_commit='dca6bab3c54d34937205ac0334e350455ec21a3c',modules=[qa.MODULE]),
            'R3':dict(binding=R3_BINDING,modules=list(PROTECTED[1:]))},
            'R4 genuine producer ownership changed; R3 Algebra is only a carrier')
    rows = selected['r3_modules']
    require([r['module'] for r in rows] == list(PROTECTED[1:]),
            'R4 duplicate, missing or reordered R3 module selection')
    return {r['module']:r for r in rows}


def check_dependency_order(order, rows):
    require(len(order) == len(set(order)) == 34 and order[:15] == list(PROTECTED),
            'R4 protected dependency installation order changed')
    seen = set()
    for name in order:
        require(all(dep not in rows or dep in seen for dep in rows[name]['imports']),
                'R4 dependency was not installed before its consumer')
        seen.add(name)


def selection(session):
    control,binding = bind()
    require(binding == session.binding and os.environ.get('GITHUB_ACTIONS') == 'true'
            and sys.platform == 'linux' and binding['source_commit'] == SOURCE
            and binding['run_id'] not in {'43643644264',R3_RUN}
            and control['driver_base'] == DRIVER_PARENT
            and control['driver_branch'] == 'ci/weil-formalalgebra-20261115',
            'R4 distinct exact-source caller/current parent/same CI branch required')
    path = BUNDLE/'direct-reuse/R4_DIRECT_SELECTION.json'
    require(control['multi_direct_selection_sha256'] == sha(path), 'R4 exact selection is not ROOT pinned')
    selected = read(path)
    require(selected['schema'] == 'weil34-r4-two-producer-direct-selection-v1'
            and selected['status'] == 'READY_EXACT_RAW_PAYLOADS_INDEPENDENTLY_REVIEWED'
            and selected['reuseReady'] is True, 'R4 HOLD: raw physical inputs and full protocol review are not ready')
    require(selected['current_source_commit'] == SOURCE,
            'R4 current published source commit differs from the exact ROOT caller binding')
    rows = check_partition(selected)
    scope = data(); current = {r['module']:r for r in scope['source_rows']}
    check_dependency_order(scope['compile_order'],current)
    require(scope['profile']['bytes'] == 487 and scope['profile']['sha256'] == qa.PROFILE,
            'R4 original complete487B26a6 profile changed')
    oldscope = BUNDLE/'direct-reuse/R3_STAGE_A34.json'
    require(sha(oldscope) == R3_SCOPE, 'R4 authentic producer34 source manifest changed')
    prior = {r['module']:r for r in read(oldscope)['source_rows']}
    for name,row in rows.items():
        require(row['prior_binding'] == R3_BINDING and row['prior_profile_sha256'] == qa.PROFILE,
                'R4 R3 producer binding or full original profile changed')
        require(row['prior_light']['sha256'] == R3_LIGHT and row['prior_light']['bytes'] == 53784325,
                'R4 actual R3 light identity changed')
        check_source(current[name],prior[name],row['original_source'])
        check_six_outputs(name,row)
        for key in ['raw_checkpoint','final_retention']:
            item = row[key]
            require(isinstance(item,dict) and isinstance(item.get('bytes'),int) and item['bytes'] > 0
                    and isinstance(item.get('artifact'),int) and len(item.get('sha256','')) == 64
                    and len(item.get('archive_sha256','')) == 64
                    and len(item.get('authenticated_acquisition_receipt_sha256','')) == 64,
                    'R4 HOLD: missing authentic R3 checkpoint/postcollector acquisition identity')
        require(isinstance(row['original_collector_classification_must_remain'],str)
                and len(row['hash_sidecars']) == 6
                and all(isinstance(r.get('present'),bool) for r in row['hash_sidecars'])
                and row['Lake_trace'].get('present') is False,
                'R4 HOLD: original complete physical sidecar/trace/classification census missing')
    index = BUNDLE/'direct-reuse/R4_ACQUISITION_INDEX.json'
    require(selected['acquisition_index_sha256'] == sha(index), 'R4 actual acquisition index changed')
    return selected


def check_source(current,prior,actual):
    require(all(current[k] == prior[k] for k in ['module','installation_path','bytes','sha256','git_blob','imports','source_module_mode'])
            and (actual['bytes'],actual['sha256']) == (prior['bytes'],prior['sha256']),
            'R4 protected source/header/import/actual producer identity changed')


def check_six_outputs(name,row):
    stem = '/home/runner/work/_temp/t01-project/.lake/build/lib/lean/'+name.replace('.','/')
    outputs = [*row['prior_output_facets'],row['additional_ilean']]
    require(len(outputs) == 6 and [r['path'] for r in outputs] == [stem+s for s in SUFFIXES]
            and all(isinstance(r['bytes'],int) and r['bytes'] > 0 and len(r['sha256']) == 64 for r in outputs),
            'R4 exact six original modern physical outputs required')
    require([r['path'] for r in row['hash_sidecars']] == [r['path']+'.hash' for r in outputs]
            and row['Lake_trace']['path'] == stem+'.trace',
            'R4 complete original sidecar and trace paths changed')


def check_artifact_producer(metadata,anchor):
    require(not metadata['expired'] and metadata['id'] == anchor['artifact']
            and metadata['size_in_bytes'] == anchor['artifactBytes']
            and metadata['digest'] == 'sha256:'+anchor['githubWholeArtifactDigest']
            and metadata['workflow_run']['id'] == anchor['run'] == int(R3_RUN)
            and metadata['workflow_run']['head_sha'] == anchor['head_sha'] == R3_HEAD,
            'R4 original R3 artifact id/run/head/size/digest changed')


def check_acquisition_layout(index):
    require(index['schema'] == 'weil34-r4-finite-physical-acquisition-v1'
            and index['status'] == 'READY_EXACT_RANGES_AND_RAW_IDENTITIES_REVIEWED'
            and index['large_whole_archives_permitted'] is False,
            'R4 HOLD: finite original physical acquisition is incomplete')
    light = index['light']
    require(light['bytes'] == 53784325 and light['sha256'] == R3_LIGHT
            and light['bounded_small_archive_only'] is True,
            'R4 only exact bounded R3 light archive permitted')
    expected = [light,*index['frozen_receipts'],*[r for g in index['artifacts'] for r in g['members']]]
    require(len(expected) == len({r['input_relative_path'] for r in expected}),
            'R4 duplicate physical acquisition destination')
    require(index['artifacts'] and all(g['members'] for g in index['artifacts']),
            'R4 missing finite raw checkpoint/output/setup/postcollector members')
    require(all(not r['member'].lower().endswith(('.zip','.tar','.tar.gz','.tgz'))
                for g in index['artifacts'] for r in g['members']),
            'R4 whole CP/proof/tar/container member acquisition denied')
    require(sum(r['bytes'] for r in expected) == index['exact_selected_body_bytes']
            and all(isinstance(r['bytes'],int) and r['bytes'] >= 0 and len(r['sha256']) == 64 for r in expected),
            'R4 exact bounded body count/length/SHA changed')
    for group in [dict(anchor=light['anchor']),*index['artifacts']]:
        require(group['anchor']['run'] == int(R3_RUN) and group['anchor']['head_sha'] == R3_HEAD,
                'R4 acquisition anchor belongs to another producer')
    return expected


def acquisition_index(session):
    selection(session)
    path = BUNDLE/'direct-reuse/R4_ACQUISITION_INDEX.json'
    index = read(path); expected = check_acquisition_layout(index)
    for row in index['frozen_receipts']: checked(BUNDLE/row['bundle_relative_path'],row)
    return index,path,expected


def acquire(session):
    """Same R3 acquisition phase/reader: R1 first, then disjoint finite R3 bytes."""
    from coherent_cache import ArchiveReader
    from weil_cache import WeilSession
    installed(); session.require_fixtures(); WeilSession.stock_qualification_inputs(session)
    index,path,expected = acquisition_index(session)
    qa.acquire(session)
    root = qa.relative(Path(os.environ['WEIL_DIRECT_INPUTS']).resolve(),'r3')
    require(not root.exists(),'R4 fresh disjoint R3 input subdirectory required')
    root.mkdir()
    rows,metadata = [],[]
    for row in index['frozen_receipts']:
        target = qa.relative(root,row['input_relative_path']); target.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(BUNDLE/row['bundle_relative_path'],target); checked(target,row)
        rows.append(qa.file_record(target))
    light = index['light']; reader = ArchiveReader(light['anchor'])
    check_artifact_producer(reader.metadata,light['anchor']); metadata.append(reader.metadata)
    target = qa.relative(root,light['input_relative_path']); target.parent.mkdir(parents=True,exist_ok=True)
    with target.open('xb') as output:
        for offset in range(0,light['bytes'],8*1024*1024):
            output.write(reader.part(offset,min(8*1024*1024,light['bytes']-offset)))
    checked(target,light); rows.append(qa.file_record(target))
    for group in index['artifacts']:
        reader = ArchiveReader(group['anchor']); check_artifact_producer(reader.metadata,group['anchor'])
        metadata.append(reader.metadata)
        temporary = root/('.ranges-'+str(group['anchor']['artifact']))
        require(not temporary.exists(),'R4 duplicate artifact range group'); temporary.mkdir()
        for row in group['members']:
            reader.fetch(row['member'],row,temporary)
            target = qa.relative(root,row['input_relative_path']); target.parent.mkdir(parents=True,exist_ok=True)
            require(not target.exists(),'R4 original member overwrite denied')
            (temporary/row['member']).rename(target); checked(target,row); rows.append(qa.file_record(target))
    for row in expected: checked(qa.relative(root,row['input_relative_path']),row)
    session.emit('WEIL_R4_R3_ACQUISITION.json',dict(status='EXACT_ORIGINAL_BYTES_ONLY_NOT_REUSE_OR_PROOF_ACCEPTANCE',
        index_sha256=sha(path),files=rows,artifacts=metadata,source_compiler_events=0,
        large_whole_archives_downloaded=False,small_light_whole_archive_bytes=53784325))


def check_input_file_set(original_input,expected_setup,path,files):
    expected = dict(files); expected[str(path)] = qa.file_record(path)
    actual = {r['path']:r for r in original_input['files']}
    require(len(actual) == len(original_input['files']) and actual == expected
            and original_input['setup'] == expected_setup and original_input['setup_path'] == str(path),
            'R4 original full actual input file set/setup differs from current resolved physical inputs')


class R3Direct(qa.PriorDirect):
    """The original full gate, with one explicit authentic R3 producer context."""
    scope_sha = R3_SCOPE
    light_sha = R3_LIGHT
    input_subdir = 'r3'
    acquisition_receipt = 'WEIL_R4_R3_ACQUISITION.json'
    scope_relative_path = 'direct-reuse/R3_STAGE_A34.json'
    prior_tools = '/home/runner/work/goldbach-formalization/goldbach-formalization/docs/source-only/20261115-resume/t01-weil34-direct-r3/shared-tools'
    event_count = 49
    source_event_count = 15
    result_has_ilean = True

    def __init__(self,session,module):
        require(module in PROTECTED[1:],'R4 R3 context cannot own Algebra or failed ClassGhost')
        self.module = module
        self.source_event_index = PROTECTED.index(module)-1
        super().__init__(session)

    def choose_selection(self,session):
        selected = selection(session)
        return next(r for r in selected['r3_modules'] if r['module'] == self.module)

    def choose_acquisition_index(self,session):
        return acquisition_index(session)

    def carrier(self):
        if not hasattr(self,'_genuine_carrier'):
            from carrier_originals import CarrierOriginals
            self._genuine_carrier=CarrierOriginals(self)
        return self._genuine_carrier

    def load_selected(self,key):
        authority=self.carrier();path=authority.original(self.selected[key])
        self.used_payloads.update(authority.original_files)
        return read(path)

    def external_file(self,old_path,expected):
        row=self.selected['post_checkpoint_files'].get(str(old_path))
        require(row is not None and row['sha256']==expected,
                'R4 exact original postcollector stream identity missing')
        authority=self.carrier();path=authority.original(row)
        self.used_payloads.update(authority.original_files)
        return path

    def original_file(self,old_path):
        row=self.cp['files'].get(str(old_path))
        if row is not None and 'payload' in row:
            self.carrier().deduplicate_prior_stream(str(old_path),row)
            self.used_payloads.update(self.carrier().original_files)
        return super().original_file(old_path)

    def validate_history(self,current_standard):
        result,original_input = super().validate_history(current_standard)
        events = [json.loads(x) for x in self.light.read('CACHE_PREEXEC_EVENTS.jsonl').decode().splitlines() if x.strip()]
        source = [e for e in events if e['classification'] == 'EXACT_CURRENT_WEIL34_SOURCE']
        wanted = [self.selected['prior_project']+'/'+n.replace('.','/')+'.lean' for n in [*PROTECTED[1:],FAILED]]
        require([e['physical_inputs'][0]['path'] for e in source] == wanted
                and sum(e['classification'] == 'EXACT_READ_ONLY_TOOLCHAIN_METADATA' for e in events) == 34
                and not any(e['classification'] == 'EXACT_WEIL34_AUDIT' for e in events),
                'R4 R3 actual14 successes/one failure/no Algebra recompile/no auditor event census changed')
        require('direct-results/'+FAILED+'.json' not in self.light.namelist()
                and self.light_json('cache-processes/weil-compile-'+FAILED+'.json')['exit_code'] == 1,
                'R4 failed ClassGhost may never acquire protected successful producer status')
        prior_row = next(r for r in self.scope['source_rows'] if r['module'] == self.module)
        require(result['name'] == self.module and result['output_identity']['source_provenance'] == dict(
                commit=prior_row['source_commit'],git_blob=prior_row['git_blob'],identity_kind='EXACT_PUBLISHED_VENDOR_SOURCE'),
                'R4 actual R3 source provenance changed')
        # A result/selfhash alone is insufficient: all inherited original process,
        # CP, collector, runtime/probe, ABI, raw streams, Cache144, standard39,
        # private/source, preexec, setup and retained-capture gates ran above.
        return result,original_input

    def restore_and_compare(self,current_standard,restore=False):
        result = super().restore_and_compare(current_standard,restore)
        from weil_proof import setup_value
        original_input = self.light_json('direct-inputs/'+self.module+'.json')
        setup,path,files = setup_value(self.session,self.module,current_standard)
        check_input_file_set(original_input,setup,path,files)
        result['current_carrier_authentication_inputs']=self.carrier().authentication_inputs()
        result['original_data_allowlist_sha256']='3ee55e22807f5f818634e6726d4e4e3205ba205624c9ba41903ade4575fdcaaa'
        result['carrier_is_not_proof_producer']=True
        return result


def protected_denial_paths(module,project):
    source = str(project/Path(*module.split('.')).with_suffix('.lean'))
    stem = str(project/'.lake/build/lib/lean'/Path(*module.split('.')))
    setup = str(project/'.lake/build/ir'/Path(*module.split('.')))
    return [source,source+'.hash',*[stem+s for s in SUFFIXES],stem+'.trace',*[stem+s+'.hash' for s in SUFFIXES],
            *[base+s for base in [stem,setup] for s in
              ['.setup.json','.setup.json.hash','.c','.bc','.c.o','.c.o.export','.c.o.export.trace','.o','.o.trace','.a','.so']]]


def protect_policy(policy,project):
    for name in PROTECTED:
        source = str(project/Path(*name.split('.')).with_suffix('.lean'))
        rows = [r for r in policy['admitted_commands'] if r.get('source',{}).get('path') == source]
        require(len(rows) == 1,'R4 each protected module must have exactly one pre-removal compiler admission')
        policy['admitted_commands'] = [r for r in policy['admitted_commands'] if r is not rows[0]]
        policy['deny_exact_paths'].extend(protected_denial_paths(name,project))
    return policy


def validate_census(counts,complete):
    require(all(v == 0 for n,v in counts.items() if n in PROTECTED), 'R4 protected source compiler event denied')
    require(all(v <= 1 for n,v in counts.items() if n not in PROTECTED), 'R4 repeated fresh source compiler event denied')
    require(not complete or all(v == 1 for n,v in counts.items() if n not in PROTECTED), 'R4 missing necessary fresh source compiler event')
    require(len(counts) == 34 and set(PROTECTED) <= set(counts)
            and len(set(counts)-set(PROTECTED)) == 19, 'R4 census must be exact15zero19once')


def required_capture_paths(result):
    require(list(result['modules']) == list(PROTECTED), 'R4 retention needs each exact protected module')
    needed = set()
    for module in PROTECTED:
        current = result['modules'][module]
        # Explicit F4 requirement, independent of recursive filesystem discovery.
        needed.add(current['current_source']['path'])
        needed.add(current['current_setup']['path'])
        needed.update(r['path'] for r in current['current_all_prior_actual_inputs'])
        require(len(current['current_five_facets']) == 5, 'R4 retention missing one original modern output')
        needed.update(r['path'] for r in current['current_five_facets'])
        needed.add(current['current_additional_ilean']['path'])
        needed.update(r['path'] for r in current['authentic_original_payloads'])
        needed.update(r['path'] for r in current.get('current_carrier_authentication_inputs',[]))
    return needed


def admit(session):
    from weil_cache import WeilSession
    installed(); session.require_fixtures(); selected = selection(session)
    standard = WeilSession.stock_qualification_inputs(session)
    qa.admit(session)
    results = {qa.MODULE:qa.validate(session,standard)}
    for module in PROTECTED[1:]:
        results[module] = R3Direct(session,module).restore_and_compare(standard,restore=True)
    value = dict(modules=results,selection_sha256=sha(BUNDLE/'direct-reuse/R4_DIRECT_SELECTION.json'),
        protected=15,fresh=19,fresh_proof_scope=34,stock_eligibility_promoted=False)
    session.emit('WEIL_R4_DIRECT_QUALIFICATION.json',value)


def validate(session,standard=None):
    from weil_cache import WeilSession
    installed(); session.require_fixtures(); selection(session)
    if standard is None: standard = WeilSession.stock_qualification_inputs(session)
    results = {qa.MODULE:qa.validate(session,standard)}
    for module in PROTECTED[1:]:
        results[module] = R3Direct(session,module).restore_and_compare(standard)
    value = dict(modules=results,selection_sha256=sha(BUNDLE/'direct-reuse/R4_DIRECT_SELECTION.json'),
        protected=15,fresh=19,fresh_proof_scope=34,stock_eligibility_promoted=False)
    require(session.receipt('WEIL_R4_DIRECT_QUALIFICATION.json') == dict(binding=session.binding,**value),
            'R4 multi-producer current consumer qualification changed after admission')
    return value


if __name__ == '__main__':
    raise SystemExit('Source-only library; actual missing raw evidence and ROOT/T02 review required')
