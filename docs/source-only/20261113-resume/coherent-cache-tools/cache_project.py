"""Authentic separate r6/r7 root leanArts-only reuse; delegates all payload IO to shared code.

This is compile reuse only. All102 fresh kernel/types/ownership/axiom gates stay.
Never execute locally. A missing or changed input fails without a build fallback.
"""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from coherent_cache import (ArchiveReader, CacheSession, HERE, NATIVE,
                            checked, read, require, sha)

PRODUCERS = {
    'r6': ('P2_R6_PROJECT_86_SELECTION.json','b8b19472fc9f9d6e82d630b89dc39f118ed9e09e22235a7a0801d7b5dd926c6c',
           'P2_R6_PROJECT_86_PAYLOAD_INDEX.json','44203c14066f0c24e3cabf1f353a6f11604db27450a392f0ec30e84397378c14',86),
    'r7_outer': ('P2_R7_OUTER_SELECTION.json','e03fc3bd0539459a836bd63d2b5a9e7a3b81ccfd737fd123cd90031fe8d9998b',
                 'P2_R7_OUTER_PAYLOAD_INDEX.json','c10c60b44c6cad2c8a9a2f36856ec81341f6b646d9282df5d6d93a08b806c370',1)}
ADOPTION = {'producer_selections':{name:{'selection_sha256':v[1],'payload_index_sha256':v[3],'module_count':v[4]}
                                  for name,v in PRODUCERS.items()},
            'module_count':87,'facet_count':696,'source_files':87,'recompile_count':15,
            'historical_runs':[43402135668,43412656063],
            'root_profile_sha256':'b47ab03272d3a7ba7b57b44c279f1e1fe4c5b4702bc9290d1030011e2116d254',
            'stock_facet':'leanArts','native_precompile_adopted':False,
            'protected_source_compiler_events_required':0,'no_cold_rebuild_fallback':True,
            'fresh_full_kernel_types_axioms_scope_count':102,'cache_is_not_proof_acceptance':True}


def load_producer(name):
    require(name in PRODUCERS,'Unknown root cache producer')
    selection_name,selection_sha,index_name,index_sha,count=PRODUCERS[name]
    require(sha(HERE/'inputs'/selection_name)==selection_sha and sha(HERE/'inputs'/index_name)==index_sha,
            'Wrong reviewed root producer inputs')
    selection,index=read(HERE/'inputs'/selection_name),read(HERE/'inputs'/index_name)
    require(selection['whole_artifact']==index['whole_artifact'] and len(selection['rows'])==count
            and selection['module_count']==count and selection['facet_count']==8*count,
            'Wrong original root producer census')
    return selection,index


def load_inputs():
    # Only the source-scope view is combined. Original checkpoints, indexes,
    # classifications, facet payloads and runtime provenance stay separate.
    r6,_=load_producer('r6');outer,_=load_producer('r7_outer')
    outer_name='ImbalancedChen.ActualThirdOriginalP4AOrdinaryOuterMinimum'
    rows=r6['rows']+outer['rows'];names=[r['module'] for r in rows]
    require([r['module'] for r in outer['rows']]==[outer_name]
            and len(names)==len(set(names))==87
            and [n for n in r6['compile_modules'] if n!=outer_name]==outer['compile_modules']
            and len(outer['compile_modules'])==15,'Root87/new15 source partition differs')
    return {'rows':rows,'compile_modules':outer['compile_modules']},None


def validate_all(parent):
    result={}
    for producer in PRODUCERS: result.update(ProjectSession(parent,producer).validate())
    return result


class ProjectSession(CacheSession):
    def __init__(self, parent, producer):
        require(parent.scope == NATIVE, 'Root87 cannot enter the independent Stored graph')
        from p2_validation import load_bound_bundle
        manifest, _ = load_bound_bundle()
        require(manifest['compile_cache']['root_project_cache'] == ADOPTION, 'Root87 not explicitly adopted')
        self.__dict__ = parent.__dict__.copy()
        self.scope = 'P2_PROJECT_87'
        self.producer = producer
        self.selection, self.index = load_producer(producer)
        combined, _ = load_inputs()
        self.anchor = self.index['whole_artifact']
        self.inputs = parent.inputs/('r6-project' if producer=='r6' else 'r7-outer')
        self._raw = None; self._part_cache = {}; self._historical_cache = {}
        old = {r['module']: r for r in combined['rows']}
        new = {r['module']: r for r in manifest['modules']}
        compile_names = combined['compile_modules']
        require(len(new) == 102 and set(old).isdisjoint(compile_names)
                and set(old) | set(compile_names) == set(new), 'Root87/new15 must exactly partition102')
        for name, row in old.items():
            require((new[name]['install_path'],new[name]['bytes'],new[name]['sha256'],new[name]['git_blob']) ==
                    (row['source']['path'],row['source']['bytes'],row['source']['sha256'],row['source_git_blob']),
                    'A protected root source changed')

    def name(self, value):
        return value.replace('CACHE_', 'CACHE_PROJECT_'+self.producer.upper()+'_', 1) if value in {'CACHE_ACQUISITION.json','CACHE_RAW_RESTORE.json','CACHE_QUALIFICATION.json','CACHE_IMPORT_PARTS.json'} else value

    def receipt(self, name):
        return super().receipt(self.name(name))

    def emit(self, name, value):
        super().emit(self.name(name), value)

    def run(self, label, argv):
        return super().run('project-'+self.producer+'-'+label, argv)

    def root_for(self, name=None):
        return self.project

    def rows(self):
        return self.selection['rows']

    def acquire(self):
        self.require_fixtures()
        require(not self.inputs.exists(), 'Fresh r6 project input directory required')
        self.inputs.mkdir()
        reader = ArchiveReader(self.anchor)
        with ThreadPoolExecutor(max_workers=4) as pool:
            results = list(pool.map(lambda item: reader.fetch(item[0], item[1], self.inputs),
                                    self.index['objects'].items()))
        checked(self.inputs/'CHECKPOINT.json', self.index['objects']['CHECKPOINT.json'])
        self.emit('CACHE_ACQUISITION.json', {'status':'EXACT_SELECTIVE_RAW_INPUTS_ONLY',
            'artifact_metadata':reader.metadata,'members':results,
            'input_bytes':sum(r['bytes'] for r in results),'whole_archive_downloaded':False,'proof_acceptance':False})

    def original(self):
        self.receipt('CACHE_ACQUISITION.json')
        checked(self.inputs/'CHECKPOINT.json', self.index['objects']['CHECKPOINT.json'])
        if self._raw is not None: return self._raw
        raw = read(self.inputs/'CHECKPOINT.json')
        require(raw['schema'] == 't01-coherent-build-checkpoint-v3'
                and raw['status'] == 'PRESERVED_BYTES_WITH_PER_MODULE_CLASSIFICATION'
                and str(raw['run_id']) == str(self.anchor['run']) and str(raw['run_attempt']) == '1'
                and raw['source_commit'] == self.selection['original_source_commit']
                and raw['manifest_sha256'] == self.selection['original_manifest_sha256']
                and raw['source_identity_sha256'] == self.selection['original_source_identity_sha256']
                and raw['runtime_audit_valid'] and raw['all_dependency_source_pins_valid']
                and raw['completed_compile_candidates'] == len(self.rows()) and raw['issues'] == []
                and raw['runtime_state']['guard_sha256'] == '837f00360ca1364eb6adede88c05a72122acbbbbff2437c83026f2851836a877'
                and raw['runtime_state']['input_sha256'][raw['runtime_state']['root']+'/lakefile.toml'] == ADOPTION['root_profile_sha256'],
                'Wrong authentic root checkpoint/source/profile/runtime')
        self._raw = raw
        return raw

    def restore(self):
        raw = self.original(); oldroot = raw['runtime_state']['root']
        modules = {r['module']:r for r in raw['modules']}
        for row in self.rows():
            prior = modules[row['module']]
            require(prior['classification'] == row['originalClassification'] == 'COMPILED_CHECKPOINT_ONLY_NOT_KERNEL_ACCEPTANCE'
                    and prior['completed_guarded_compile_candidate'] and not prior['kernel_verified']
                    and not prior['missing_actual_import_artifacts'] and not prior['missing_expected_direct_imports']
                    and not prior['observed_output_descriptor_contradiction']
                    and all(c['matched'] for c in prior['trace_output_descriptor_sidecar_checks'])
                    and len(prior['guarded_source_commands']) == 1
                    and [a.replace(oldroot,'{root}') for a in prior['guarded_source_commands'][0]['command']] == row['guardedCommandNormalized']
                    and prior['lake_depHash'] == row['lake_depHash'] and prior['lake_outputs'] == row['lake_outputs']
                    and prior['source']['payload'] == row['source']['object']
                    and prior['source']['sha256'] == row['source']['sha256']
                    and prior['actual_import_count'] == row['priorActualImportCount']
                    and prior['actual_import_map_sha256'] == row['priorActualImportMapSHA256'],
                    'Unbound/quarantined root compile input')
        super().restore()

    def verify_restored(self, name='CACHE_RAW_RESTORE.json'):
        value = super().verify_restored(name)
        require([r['module'] for r in value['modules']] == [r['module'] for r in self.rows()], 'Root restore census changed')
        for actual, selected in zip(value['modules'], self.rows()):
            require(actual['source']=={'path':str(self.project/selected['source']['path']),
                    'bytes':selected['source']['bytes'],'sha256':selected['source']['sha256']},'Root source receipt differs from frozen selector')
            expected = [{'path':str(self.project/f['path']),'bytes':f['bytes'],'sha256':f['sha256'],'object':f['object']}
                        for f in selected['facets']]
            require(actual['facets'] == expected and len(expected) == 8, 'Root raw facet census changed')
        return value

    def qualify(self):
        raw = self.original(); self.verify_restored()
        names = [r['module'] for r in self.rows()]
        process = self.run('stock-leanArts',['lake','--no-build','build',*['+'+n+':leanArts' for n in names]])
        self.verify_restored()
        rows, shared = self.qualify_setups(raw,names,self.rows(),lambda n:'+'+n+':setup','stock-setup')
        self.verify_restored()
        self.emit('CACHE_IMPORT_PARTS.json', {'parts':shared})
        self.emit('CACHE_QUALIFICATION.json', {'status':'PASS_AUTHENTIC_STOCK_NO_BUILD_CACHE_INPUT_ONLY',
            'stock_process':process,'modules':rows,'physical_parts_receipt_sha256':sha(self.logs/self.name('CACHE_IMPORT_PARTS.json')),
            'protected_source_compiler_events':0,'proof_or_full_kernel_acceptance':False,
            'all_original_caller_gates_still_required':True})
        self.validate()

    def validate(self):
        self.verify_restored(); self.policy_audit(); self.validate_environment(self.original())
        value = self.receipt('CACHE_QUALIFICATION.json'); names = [r['module'] for r in self.rows()]
        require(value['status'] == 'PASS_AUTHENTIC_STOCK_NO_BUILD_CACHE_INPUT_ONLY'
                and value['protected_source_compiler_events'] == 0
                and [r['module'] for r in value['modules']] == names
                and value['stock_process']['argv'] == ['lake','--no-build','build',*['+'+n+':leanArts' for n in names]],
                'Root stock qualification command/census changed')
        processes = [value['stock_process']]
        for offset in range(0,len(names),16):
            batch = value['modules'][offset:offset+16]
            process = batch[0]['official_current_setup_process']
            require(process['argv'] == ['lake','--no-build','--json','query',*['+'+r['module']+':setup' for r in batch]],
                    'Root stock setup query targets changed')
            for number, row in enumerate(batch,1):
                selected = self.rows()[offset+number-1]
                require(row['official_current_setup_process'] == process and row['official_current_setup_stdout_line'] == number
                        and row['current_all_fields_equal_after_explicit_root_mapping'] is True
                        and row['physical_import_count'] == selected['priorActualImportCount']
                        and row['original_import_map_sha256'] == selected['priorActualImportMapSHA256']
                        and row['historical_raw_setup_sha256'] == next(f['sha256'] for f in selected['facets'] if f['path'].endswith('.setup.json')), 'Root setup row changed')
            processes.append(process)
        for process in processes:
            require(process['exit_code'] == 0 and process['cwd'] == str(self.project)
                    and sha(process['stdout']) == process['stdout_sha256'] and sha(process['stderr']) == process['stderr_sha256']
                    and read(Path(process['stdout']).with_suffix('.json')) == {'binding':self.binding,**process},
                    'Root stock process evidence changed')
        require(sha(self.logs/self.name('CACHE_IMPORT_PARTS.json')) == value['physical_parts_receipt_sha256'], 'Root import receipt changed')
        for part in self.receipt('CACHE_IMPORT_PARTS.json')['parts'].values(): checked(part['path'],part)
        return {'project_'+self.producer+'_qualification_sha256':sha(self.logs/self.name('CACHE_QUALIFICATION.json')),
                'project_'+self.producer+'_restore_sha256':sha(self.logs/self.name('CACHE_RAW_RESTORE.json')),
                'project_'+self.producer+'_acquisition_sha256':sha(self.logs/self.name('CACHE_ACQUISITION.json'))}
