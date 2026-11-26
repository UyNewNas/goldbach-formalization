"""GitHub-only adapter to the byte-identical original 32993-byte collector.

The legacy T01 names below are retention aliases, never new compile/proof
objects. Original quarantine/classification rules are executed unchanged.
"""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

from coherent_cache import HERE, NATIVE, bind_inputs, checked, read, sha, write, require


def main():
    scope=os.environ['CACHE_SCOPE'];binding=bind_inputs(scope)
    project=Path(os.environ['PROJECT']).resolve();logs=Path(os.environ['LOGS']).resolve()
    if scope==NATIVE:
        sys.path.insert(0,str(Path(os.environ['GITHUB_WORKSPACE'])/os.environ['P2_BUNDLE']))
        from p2_validation import load_bound_bundle
        manifest,_=load_bound_bundle();sources=manifest['modules'];audit_name='CandidateAudit.lean'
    else:
        control=read(os.environ['CACHE_ROOT_CONTROL'])
        selection=read(Path(os.environ['GITHUB_WORKSPACE'])/control['source_selection']['path'])
        sources=[selection['parent'],*selection['files']];audit_name='StoredBatchAudit.lean'
    audit=project/audit_name;alias=project/'T01Audit.lean'
    provenance=project/'T01_PROVENANCE.json'
    if scope==NATIVE:
        require(not alias.exists() and not provenance.exists(),'Refuse legacy P2 retention alias overwrite')
        if audit.exists():shutil.copyfile(audit,alias)
        write(provenance,{'schema':'original-collector-retention-name-adapter-v1','binding':binding,
            'actual_caller_audit':audit_name,'legacy_alias':'T01Audit.lean','alias_present':alias.exists(),
            'alias_is_not_a_compiled_proof_module':True,'original_collector_classification_not_changed':True})
    else:
        require(alias.is_file() and provenance.is_file() and not alias.is_symlink() and not provenance.is_symlink(),
                'Original Stored stage audit/provenance must be preserved')
    audit_record=({'bytes':alias.stat().st_size,'sha256':sha(alias)} if alias.exists()
                  else {'bytes':0,'sha256':hashlib.sha256(b'').hexdigest()})
    original_provenance_sha=sha(provenance)
    write(logs/'CHECKPOINT_ADAPTER_INPUTS.json',{'binding':binding,'scope':scope,
        'original_collector_audit_slot':{'path':str(alias),**audit_record},'provenance_sha256':original_provenance_sha,
        'caller_actual_audit':audit_name,'stored_original_stage_inputs_preserved':scope!=NATIVE,
        'native_retention_alias_is_not_a_compiled_proof_module':scope==NATIVE})
    adapted={'files':sources,'data_inputs':[],'audit_source':audit_record,
        'targets':[{'closure_modules':[r['module'] for r in sources],
            'source_identity_sha256':hashlib.sha256(json.dumps(sources,sort_keys=True).encode()).hexdigest()}]}
    config=logs/'CHECKPOINT_COLLECTOR_INPUT.json';write(config,adapted)
    # Preserve the actual current protected sources even though this run is
    # forbidden to produce a new compiler-source event for a cache input.
    for restore in [logs/'CACHE_RAW_RESTORE.json',logs/'CACHE_BOOTSTRAP_RESTORE.json']:
        if restore.exists():
            for row in read(restore)['modules']:
                source=row['source'];target=logs/'cached-source-inputs'/Path(source['path']).relative_to(project)
                checked(source['path'],source);target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source['path'],target)
    collector=HERE/'reference/checkpoint_objects_v3.py'
    require(collector.stat().st_size==32993 and sha(collector)=='773e4eab588c0d196c5b7ad86a3a0f90a6a0fe1c225baa7559b2b1380e853a76',
            'Original collector bytes changed')
    output=Path(os.environ['CACHE_CHECKPOINT_OUTPUT']).resolve()
    require(not output.is_relative_to(project) and not output.is_relative_to(logs),'Collector output must be disjoint')
    argv=[sys.executable,str(collector),'--project',str(project),'--manifest',str(config),'--logs',str(logs),'--output',str(output)]
    log=logs/'checkpoint-collection.log';temporary=output.parent/(output.name+'.collector-stdout.log')
    require(not log.exists() and not temporary.exists(),'Collector process already recorded')
    with temporary.open('wb') as stream:result=subprocess.run(argv,cwd=project,stdout=stream,stderr=subprocess.STDOUT)
    shutil.copyfile(temporary,log)
    require(sha(provenance)==original_provenance_sha,'Original stage provenance changed during collection')
    if alias.exists():checked(alias,audit_record)
    write(logs/'CACHE_CHECKPOINT_RETENTION.json',{'binding':binding,'argv':argv,'exit_code':result.returncode,
        'collector_sha256':sha(collector),'adapter_sha256':sha(__file__),'input_sha256':sha(config),
        'stdout_sha256':sha(log),'output':str(output),'proof_acceptance':False,
        'legacy_retention_aliases_are_not_compiled_or_accepted':True})
    require(result.returncode==0,'Original collector failed; raw snapshot remains quarantined')


if __name__=='__main__':main()
