#!/usr/bin/env python3
"""Refresh a receipt ledger without running Lean, Lake, leanchecker, or CI.

Only completed, version-bound execution records can produce a PASS. Existing
snapshots are immutable: use a new --output-dir for every refresh.
"""
import argparse
import collections
import copy
from datetime import datetime, timezone
import json
from pathlib import Path
import re
import subprocess

from ledger_source_helpers import digest, blob, strip_comments, extract_types

ROOT = Path('/workspace/scratch/535d89efd063/p0-round2')
HERE = Path(__file__).resolve().parent
P1 = Path('/workspace/scratch/127408f63891/goldbach-formalization')
P5 = Path('/workspace/scratch/cd30ec11ea1d/goldbach-formalization')
ALLOW = {'propext', 'Classical.choice', 'Quot.sound'}


def read_json(path):
    return json.loads(Path(path).read_text())


def stable_record(r):
    """Exit zero alone is insufficient when record() detects changed inputs."""
    if 'verification_passed' in r and r['verification_passed'] is not True:
        return False
    if r.get('failure_reasons') or r.get('verification_failure_reasons'):
        return False
    if r.get('source_sha256_before') != r.get('source_sha256_after'):
        return False
    if not r.get('source_sha256_before'):
        return False
    before, after = r.get('import_olean_sha256_before'), r.get('import_olean_sha256_after')
    if ('import_olean_sha256_before' in r or 'import_olean_sha256_after' in r) and before != after:
        return False
    if r.get('action') == 'replay' and 'target_olean_sha256_before' in r:
        if r['target_olean_sha256_before'] != r.get('olean_sha256'):
            return False
    return True


def parse_audit_log(text):
    """Parse a full raw audit; partial DECL output never constitutes success."""
    groups = {}
    for line in text.splitlines():
        match = re.match(r'^([A-Z0-9_]*AUDIT)_(DECL|MODULE|COUNT)\s+(.+)$', line.strip())
        if not match:
            continue
        prefix, kind, value = match.groups()
        g = groups.setdefault(prefix, {'declarations': [], 'modules': [], 'counts': [], 'parse_errors': []})
        try:
            item = int(value) if kind == 'COUNT' else json.loads(value)
            g[{'DECL':'declarations', 'MODULE':'modules', 'COUNT':'counts'}[kind]].append(item)
        except (ValueError, TypeError) as exc:
            g['parse_errors'].append(str(exc))
    result = []
    for prefix, g in groups.items():
        reasons = list(g['parse_errors'])
        decls, modules = g['declarations'], g['modules']
        names = [d.get('name') for d in decls]
        counts = collections.Counter(d.get('module') for d in decls)
        declared_counts = {d.get('module'):d.get('count') for d in modules}
        if not decls: reasons.append('no declarations')
        if len(set(names)) != len(names): reasons.append('duplicate declaration names')
        if len(modules) != len(declared_counts): reasons.append('duplicate module summaries')
        if dict(counts) != declared_counts: reasons.append('per-module counts do not match declarations')
        if any(not isinstance(n, int) or n <= 0 for n in declared_counts.values()):
            reasons.append('empty/invalid defining-module inventory')
        if g['counts'] != [len(decls)]: reasons.append('missing, duplicate, or inconsistent final AUDIT_COUNT')
        for d in decls:
            if not all(isinstance(d.get(k), str) for k in ('name', 'module', 'kind', 'type')):
                reasons.append('incomplete declaration record')
            for field in ('type', 'readable_type'):
                if field == 'readable_type' and field not in d:
                    continue
                value = d.get(field)
                if not isinstance(value, str) or not value.strip() or '⋯' in value:
                    reasons.append('missing/invalid/truncated compiler '+field)
            if d.get('kind') == 'axiom': reasons.append('owned axiom declaration')
            if (not isinstance(d.get('axioms'), list) or
                    not all(isinstance(a, str) for a in d.get('axioms', [])) or
                    not set(d.get('axioms', [])).issubset(ALLOW)):
                reasons.append('invalid/forbidden transitive axiom inventory')
        result.append({'prefix':prefix, 'declarations':decls, 'module_counts':declared_counts,
                       'total_declarations':len(decls), 'complete_inventory':not reasons,
                       'rejection_reasons':sorted(set(reasons))})
    return result


def first_lean_diagnostic(log):
    """Keep the first actual diagnostic with its body, not a wrapper verdict."""
    lines = log.splitlines()
    for start, line in enumerate(lines):
        if not re.search(r'\berror(?:\(|:)', line):
            continue
        end = start + 1
        while end < len(lines):
            following = lines[end]
            if (re.search(r':\d+:\d+:\s+(?:error|warning|information)(?:\(|:)', following)
                    or re.match(r'^(?:FRONTEND_|P[0-9]+_AUDIT_)', following)):
                break
            end += 1
        return {'first_real_diagnostic':line,
                'first_real_diagnostic_block':'\n'.join(lines[start:end]).rstrip()}
    return {}


def normalize_repair_receipt(record, origin):
    """Retain historical repair facts without importing their old gate verdicts."""
    item = copy.deepcopy(record)
    path = item.get('path') or item.get('file')
    if not path and item.get('module'):
        path = item['module'].replace('.', '/') + '.lean'
    if not path:
        raise ValueError('repair receipt needs path, file, or module: '+str(origin))
    item['path'] = path
    item['receipt_origin'] = str(origin)
    item['historical_repair_only_current_gates_from_execution_records'] = True
    return item


def compiler_type_markdown(record):
    """Render only compiler fields; never substitute an extracted source head."""
    lines = []
    if 'readable_type' in record:
        lines += ['编译器可读类型（原始 `readable_type` 字段）：','',
                  '```lean',record['readable_type'],'```','']
    lines += ['编译器完整类型（原始 `type` 字段，保留审计的打印设置）：','',
              '```lean',record['type'],'```','']
    return lines


def audit_guards(source):
    clean = re.sub(r'\s+', ' ', strip_comments(source))
    return {
        'defining_module_inventory':'env.constants.fold' in clean and 'env.getModuleIdxFor?' in clean,
        'unsafe_rejected':'info.isUnsafe' in clean and 'throwError' in clean,
        'owned_axiom_rejected':'info.isAxiom' in clean and 'throwError' in clean,
        'transitive_collection':'collectAxioms name' in clean,
        'allowlist_guard':'unless allowed.contains ax do' in clean,
        'compiler_type_printed':'Meta.ppExpr info.type' in clean,
    }


def default_acceptance(base):
    return {'integration':{k:base['accepted_integration'].get(k) for k in ('branch','commit','tree')},
            'accepted_components':[
                {'module':m['module'], 'commit':m['integration_acceptance']['commit'],
                 'source_sha256':m['current_source']['source_sha256'],
                 'source_commit':m['current_source'].get('source_fixed_commit')}
                for m in base['modules'] if m['integration_acceptance']['accepted']],
            'module_overrides':{}, 'additional_modules':[], 'extra_results_jsonl':[]}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base-ledger', type=Path, default=HERE/'module-ledger.json')
    parser.add_argument('--acceptance-file', type=Path,
                        help='JSON: integration, accepted_components, module_overrides, optional extra results/actions')
    parser.add_argument('--output-dir', type=Path, default=ROOT/'ledger-final')
    parser.add_argument('--check-input', action='store_true',
                        help='validate paths and config only; write no ledger and run no verification')
    args = parser.parse_args(argv)
    base = read_json(args.base_ledger)
    config = read_json(args.acceptance_file) if args.acceptance_file else default_acceptance(base)
    accepted = {x['module']:x for x in config.get('accepted_components', [])}
    if len(accepted) != len(config.get('accepted_components', [])):
        raise ValueError('duplicate accepted component modules')
    for module, x in accepted.items():
        if not re.fullmatch(r'[0-9a-f]{40}', x.get('commit','')):
            raise ValueError(f'accepted component {module} needs a full commit SHA')
        if not re.fullmatch(r'[0-9a-f]{64}', x.get('source_sha256','')):
            raise ValueError(f'accepted component {module} needs its exact source SHA256')
    integration = config.get('integration', {})
    if integration.get('commit') and not re.fullmatch(r'[0-9a-f]{40}', integration['commit']):
        raise ValueError('integration.commit must be a full SHA')
    modules = copy.deepcopy(base['modules'])
    seen = {m['module'] for m in modules}
    additions = [read_json(HERE/'bridge-source-inventory.json')] + config.get('additional_modules', [])
    for a in additions:
        if a['module'] in seen:
            continue
        seen.add(a['module'])
        modules.append(dict(a, current_source={}, validation={}, types={},
            integration_acceptance={'accepted':False, 'commit':None}, P0_repairs=[],
            review_notes_from_previous_snapshot=a.get('unclosed_inputs',[])))
    unknown = sorted(set(accepted)-seen)
    if unknown:
        raise ValueError('accepted modules absent from source inventory: '+', '.join(unknown))
    for module, override in config.get('module_overrides', {}).items():
        if module not in seen: raise ValueError('unknown module override: '+module)
        if override.get('source_path') and not Path(override['source_path']).is_file():
            raise ValueError('missing source override: '+override['source_path'])
    if args.output_dir.resolve() == HERE.resolve():
        raise ValueError('refusing to overwrite the original ledger-draft snapshot')
    if args.check_input:
        print(json.dumps({'module_count':len(modules), 'accepted_components_declared':len(accepted),
                          'output_dir':str(args.output_dir), 'writes':False, 'Lean_started':False}, ensure_ascii=False))
        return
    if args.output_dir.exists() and any(args.output_dir.iterdir()):
        raise ValueError('output directory is not empty; select a new --output-dir to preserve snapshots')
    out = args.output_dir
    out.mkdir(parents=True, exist_ok=True)
    start = datetime.now(timezone.utc).isoformat()
    evidence = []
    copied = {}

    def snapshot(path, rel):
        path = Path(path)
        key = str(path)
        if key in copied: return copied[key]
        b = path.read_bytes()
        dest = out/rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(b)
        meta = {'source_path':key, 'snapshot_path':str(dest), 'sha256':digest(b),
                'bytes':len(b), 'mtime_utc':datetime.fromtimestamp(path.stat().st_mtime, timezone.utc).isoformat()}
        evidence.append(meta)
        copied[key] = (b, meta)
        return b, meta

    def save_json(rel, x):
        p = out/rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')

    snapshot(args.base_ledger, 'evidence/base-ledger.json')
    save_json('acceptance-input.json', config)
    if args.acceptance_file: snapshot(args.acceptance_file, 'evidence/acceptance-input-original.json')
    config_rechecks=[]
    for item in base.get('toolchain',{}).get('config_files',[]):
        p=ROOT/'validation'/item['path']
        if not p.exists(): continue
        b,meta=snapshot(p,'evidence/config/'+item['path'])
        if digest(b)!=item['sha256']:
            raise ValueError('locked project configuration changed: '+str(p))
        config_rechecks.append(dict(meta, matches_original_pin=True))
    records = []
    malformed = []
    result_paths = [ROOT/'runtime/logs/results.jsonl', P5.parent/'p5-round2/runtime/logs/results.jsonl']
    result_paths += [Path(p) for p in config.get('extra_results_jsonl', [])]
    for idx, p in enumerate(dict.fromkeys(result_paths)):
        if not p.exists():
            malformed.append({'path':str(p),'reason':'result file unavailable'})
            continue
        b, meta = snapshot(p, f'evidence/results-{idx}.jsonl')
        for lineno, line in enumerate(b.decode().splitlines(),1):
            if not line.strip(): continue
            try:
                r=json.loads(line); r['receipt_origin']=str(p); records.append(r)
            except ValueError as exc:
                malformed.append({'path':str(p),'line':lineno,'reason':str(exc)})
    state_path=P1.parent/'lean-runtime/logs/closure/state.json'
    state={}
    if state_path.exists():
        b, state_evidence=snapshot(state_path,'evidence/p1-closure-state.json'); state=json.loads(b)
        for r in state.values(): records.append(dict(r,action='compile',receipt_origin=str(state_path)))
    unique={}
    for r in records:
        unique[(r.get('action'),r.get('module'),r.get('log'),r.get('source_sha256_before'))]=r
    records=list(unique.values())
    completed_paths={r.get('log') for r in records}
    log_cache={}

    def read_log(r):
        p=Path(r['log'])
        if str(p) not in log_cache:
            if not p.exists(): return ''
            label='p1' if str(p).startswith(str(P1.parent)) else 'p5' if str(p).startswith(str(P5.parent)) else 'p0'
            b,meta=snapshot(p,f'evidence/logs/{label}-{p.name}')
            log_cache[str(p)]=(b.decode(errors='replace'),meta)
        return log_cache[str(p)][0]

    audit_catalog=[]
    for r in records:
        if r.get('action')!='compile' or 'audit' not in r.get('module','').lower(): continue
        log=read_log(r)
        parsed=parse_audit_log(log)
        if not parsed: continue
        source=Path(r['source']) if r.get('source') else None
        source_matches=False; guards={}; source_evidence=None
        if source and source.exists():
            b,source_evidence=snapshot(source,'evidence/audit-sources/'+r['module']+'.lean')
            source_matches=digest(b)==r.get('source_sha256_before')==r.get('source_sha256_after')
            guards=audit_guards(b.decode())
        completion_ok=(r.get('returncode')==0 and r.get('strict') is True and r.get('trustLevel')==0
                       and r.get('metadata_adapter') is False and stable_record(r)
                       and ('FRONTEND_OK module='+r['module']) in log)
        for group in parsed:
            audit_catalog.append(dict(group, audit_module=r['module'], execution_record=r,
                completed_strict_stable=completion_ok, audit_source_hash_matches=source_matches,
                audit_source_evidence=source_evidence, audit_guards=guards,
                can_bind_production=(completion_ok and source_matches and all(guards.values())
                                     and group['complete_inventory'])))
    active=[]
    for d in dict.fromkeys(p.parent for p in result_paths if p.exists()):
        for p in d.glob('*.log'):
            if str(p) in completed_paths: continue
            try:
                with p.open() as f: r=json.loads(f.readline())
                if isinstance(r,dict) and r.get('module'):
                    active.append(dict(r,log=str(p),status='started_without_completed_result'))
            except (ValueError,OSError): pass
    repairs=[]
    repair_paths=[ROOT/'p2-p5-audit/p2-repairs.jsonl',
                  ROOT/'p2-p5-audit/coarse-repairs.jsonl',
                  ROOT/'p3-p4-audit/longslot-leaf-execution-receipt.json']
    repair_paths += [Path(p) for p in config.get('repair_receipt_files', [])]
    for idx, repairs_path in enumerate(dict.fromkeys(repair_paths)):
        if not repairs_path.exists():
            continue
        b,_=snapshot(repairs_path,f'evidence/repair-receipts/{idx}-{repairs_path.name}')
        items=([json.loads(line) for line in b.decode().splitlines() if line.strip()]
               if repairs_path.suffix=='.jsonl' else json.loads(b))
        if isinstance(items,dict): items=[items]
        for item in items:
            repair=normalize_repair_receipt(item,repairs_path)
            repairs.append(repair)
            patch=Path(repair['patch']) if repair.get('patch') else None
            if patch and patch.is_file():
                snapshot(patch,f'evidence/repair-patches/{idx}-{patch.name}')

    all_source_types=[]; all_compiler_types=[]
    for m in modules:
        module=m['module']; original=m['source_original']; prior=copy.deepcopy(m)
        override=config.get('module_overrides',{}).get(module,{})
        if override.get('source_original'): original.update(override['source_original'])
        validation=ROOT/'validation'/m['path']
        fixed=override.get('fixed_source',m.get('latest_fixed_source_update'))
        if override.get('fixed_source'):
            if not re.fullmatch(r'[0-9a-f]{40}', fixed.get('ref','')):
                raise ValueError('new fixed source needs a full commit SHA: '+module)
            fixed_path=Path(fixed['local_path'])
            fixed_bytes=fixed_path.read_bytes()
            if digest(fixed_bytes)!=fixed.get('sha256'):
                raise ValueError('new fixed source bytes mismatch: '+module)
            if fixed.get('git_blob_sha1') and blob(fixed_bytes)!=fixed['git_blob_sha1']:
                raise ValueError('new fixed source blob mismatch: '+module)
            m['latest_fixed_source_update']=copy.deepcopy(fixed)
        if override.get('source_path'):
            source=Path(override['source_path']); origin='explicit source override'
        elif m.get('source_part')=='p1':
            source=P1/m['path']; origin='observed local P1 candidate'
        elif validation.exists():
            source=validation; origin='P0 isolated validation source'
            if fixed and digest(validation.read_bytes())==original['sha256'] and fixed['sha256']!=original['sha256']:
                source=Path(fixed['local_path']); origin='new fixed supplier source; old validation copy retained separately'
        elif m.get('source_path'):
            source=Path(m['source_path']); origin='observed additional production candidate'
        elif fixed:
            source=Path(fixed['local_path']); origin='fixed supplier source'
        else:
            source=Path(original['local_path']); origin='fixed original source copy'
        b,source_evidence=snapshot(source,'snapshot-sources/'+m.get('source_part','unknown')+'/'+m['path'])
        h=digest(b); text=b.decode(); types=extract_types(text,module,h)
        orig_path=Path(original['local_path'])
        if orig_path.exists():
            ob=orig_path.read_bytes()
            if digest(ob)!=original['sha256'] or blob(ob)!=original['git_blob_sha1']:
                raise ValueError('original source manifest changed: '+module)
            original['independently_rehashed_against_intake_manifest']=True
            old_types=extract_types(ob.decode(),module,original['sha256'])
        else:
            old_types=[]; original['original_bytes_available_this_refresh']=False
        fixed_commit=original.get('commit') if h==original['sha256'] else None
        if fixed and fixed['sha256']==h: fixed_commit=fixed['ref']
        accepted_spec=accepted.get(module)
        if accepted_spec and accepted_spec['source_sha256']==h and accepted_spec.get('source_commit'):
            fixed_commit=accepted_spec['source_commit']
        m['current_source']={'source_sha256':h,'git_blob_sha1':blob(b),'source_fixed_commit':fixed_commit,
            'based_on_fixed_commit':original.get('commit') or original.get('based_on_commit') or base['proof_baseline'],
            'origin':origin,'snapshot':source_evidence,'equal_to_original_bytes':h==original['sha256'],
            'source_theorem_declaration_heads_unchanged_from_original':
              [(t['source_name'],t['source_declaration_head']) for t in types]==[(t['source_name'],t['source_declaration_head']) for t in old_types]}
        attempts=sorted([copy.deepcopy(r) for r in records if r.get('module')==module
                         and r.get('action') in ('compile','replay')], key=lambda r:r.get('started_utc',''))
        for r in attempts:
            log=read_log(r)
            r['stable_source_and_recorded_imports']=stable_record(r)
            if r.get('log') in log_cache: r['log_snapshot']=log_cache[r['log']][1]
            r.update(first_lean_diagnostic(log))
        matching=[r for r in attempts if r.get('source_sha256_before')==h and r.get('source_sha256_after')==h]
        strict=[r for r in matching if r['action']=='compile' and r.get('strict') is True and r.get('trustLevel')==0]
        strict_valid=[r for r in strict if r.get('returncode')==0 and stable_record(r) and r.get('metadata_adapter') is False]
        latest=strict[-1] if strict else None
        compile_ok=bool(latest and latest in strict_valid)
        pending=[r for r in active if r.get('module')==module and r.get('source_sha256_before')==h]
        compile_status=('PASS_STRICT_TRUST0' if compile_ok else 'STARTED_NO_COMPLETION' if any(r.get('action')=='compile' for r in pending)
                        else 'FAILED_CURRENT_SOURCE' if strict else 'NOT_RECORDED_CURRENT_SOURCE')
        passing_hashes={r['olean_sha256'] for r in strict_valid if r.get('olean_sha256')}
        replay_attempts=[r for r in matching if r['action']=='replay']
        replays=[r for r in replay_attempts if r.get('returncode')==0 and stable_record(r)
                 and r.get('olean_sha256') in passing_hashes]
        replay_ok=bool(replay_attempts and replay_attempts[-1] in replays)
        ax={'status':'NOT_RECORDED_CURRENT_SOURCE','compiler_printed_types':[],
            'owned_declaration_count':None,'audit_module_kernel_replay':'not observed'}
        bindings=[]
        for audit in audit_catalog:
            if not audit['can_bind_production'] or module not in audit['module_counts']: continue
            ar=audit['execution_record']
            im_before=ar.get('import_olean_sha256_before'); im_after=ar.get('import_olean_sha256_after')
            if not isinstance(im_before,dict) or im_before!=im_after: continue
            objects=im_before.get(module)
            if not isinstance(objects,dict): continue
            main={p:oh for p,oh in objects.items() if p.endswith('.olean')}
            if len(main)!=1 or next(iter(main.values())) not in passing_hashes: continue
            names=[d for d in audit['declarations'] if d['module']==module]
            binding={'method':'recorded audit import objects before/after; primary object matched to current-source strict compile',
                'source_sha256':h,'production_olean_sha256':next(iter(main.values())),
                'audit_import_objects':objects,'import_objects_stable':True,
                'audit_execution_record':ar,'audit_source_evidence':audit['audit_source_evidence'],
                'complete_inventory_count':audit['module_counts'][module],
                'compiler_declarations':names,'audit_prefix':audit['prefix']}
            bindings.append(binding)
        if bindings:
            chosen=sorted(bindings,key=lambda z:z['audit_execution_record'].get('started_utc',''))[-1]
            names=chosen['compiler_declarations']; axiom_set=sorted({a for d in names for a in d['axioms']})
            ax={'status':'PASS_OWNED_DECLARATIONS','owned_declaration_count':len(names),
                'compiler_printed_types':names,'actual_axiom_union':axiom_set,
                'new_axiom_declarations':0,'unsafe_owned_declarations':0,
                'binding':chosen,'all_matching_completed_audits':bindings,
                'scope':'exact listed defining module, including private/generated declarations; not complete project',
                'audit_module_kernel_replay':'not observed'}
        else:
            old_ax=prior.get('validation',{}).get('axioms',{})
            old_hash=prior.get('current_source',{}).get('source_sha256')
            if old_hash==h and old_ax.get('status','').startswith('PASS'):
                ax=copy.deepcopy(old_ax)
                ax['reused_historical_receipt']={'base_ledger':str(args.base_ledger),
                    'base_snapshot_utc':base.get('snapshot_completed_utc'), 'source_sha256':h,
                    'meaning':'retained already-verified historical receipt; no invented import before/after fields'}
        # A distinct replay of an audit module is reported only if actually present.
        bound_audit= ax.get('binding',{}).get('audit_execution_record')
        if bound_audit:
            audit_replays=[r for r in records if r.get('action')=='replay' and r.get('module')==bound_audit['module']
                and r.get('returncode')==0 and stable_record(r)
                and r.get('source_sha256_before')==bound_audit['source_sha256_before']
                and r.get('olean_sha256')==bound_audit.get('olean_sha256')]
            if audit_replays: ax['audit_module_kernel_replay']={'status':'PASS','records':audit_replays}
        declarations=ax.get('compiler_printed_types',[])
        for t in types:
            qualified=t['source_qualified_name']
            found=[d for d in declarations if d['name']==qualified or d['name'].endswith('.'+qualified)]
            if len(found)==1:
                t.update(compiler_printed_type_available=True,compiler_printed_type=found[0]['type'],
                         compiler_declaration_name=found[0]['name'])
                if 'readable_type' in found[0]:
                    t['compiler_printed_readable_type']=found[0]['readable_type']
        m['types']={'source_extracted_count':len(types),'compiler_printed_count':sum(t['compiler_printed_type_available'] for t in types),
                    'compiler_all_declaration_count':len(declarations),'full_source_declaration_heads':types}
        replay_status=('PASS_ORIGINAL_LEANCHECKER' if replay_ok else
            'STARTED_NO_COMPLETION' if any(r.get('action')=='replay' for r in pending) else
            'FAILED_OR_UNBOUND_CURRENT_REPLAY' if replay_attempts else 'NOT_RECORDED_CURRENT_SOURCE')
        m['validation']={'compile':{'status':compile_status,'completed_matching_attempts':strict,
            'active_matching_log_headers':[r for r in pending if r.get('action')=='compile'],
            'stock_lean_cli_or_full_lake_build':False},
            'kernel_replay':{'status':replay_status,
                'completed_matching_attempts':replay_attempts,'exact_compiled_object_lineage_required':True,
                'scope':'named production module only'}, 'axioms':ax,
            'all_completed_attempts_including_old_source_failures':attempts}
        m['P0_repairs']=[r for r in repairs if r['path']==m['path']]
        m['direct_imports']=re.findall(r'^\s*import\s+([^\n]+)',strip_comments(text),re.M)
        m['source_only_text_scan']={'forbidden_tokens_after_comment_removal':re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe)\b',strip_comments(text)),
            'does_not_replace_kernel_or_axiom_audit':True}
        old_notes=prior.get('unclosed_real_inputs_and_gates',prior.get('review_notes_from_previous_snapshot',prior.get('unclosed_inputs',[])))
        m['review_notes_from_previous_snapshot']=old_notes
        m['unclosed_inputs']=override.get('unclosed_inputs',old_notes)
        m['unclosed_inputs_as_of']=override.get('reviewed_utc',base.get('snapshot_completed_utc'))
        m['outstanding_validation_gates']=[name for name,ok in [('strict_compile',compile_ok),('production_kernel_replay',replay_ok),('owned_declaration_axiom_audit',ax['status'].startswith('PASS'))] if not ok]
        exact_acceptance=bool(accepted_spec and accepted_spec['source_sha256']==h)
        effective=exact_acceptance and not m['outstanding_validation_gates']
        m['integration_acceptance']={'accepted':effective,'declared_by_input':bool(accepted_spec),
            'declared_source_hash_matches':exact_acceptance,
            'commit':accepted_spec['commit'] if accepted_spec else None,
            'acceptance_input':str(args.acceptance_file) if args.acceptance_file else 'inherited from base ledger',
            'meaning':'accepted exact-source component with matched gates' if effective else 'candidate; absent declaration, source mismatch, or missing gates cannot be promoted'}
        all_source_types.extend(types)
        all_compiler_types.extend(dict(d,production_source_sha256=h) for d in declarations)

    actions_path=Path(config.get('actions_receipt_path',str(ROOT/'buchstab-actions-receipt.json')))
    actions=read_json(actions_path) if actions_path.exists() else None
    if actions: snapshot(actions_path,'evidence/actions.json')
    same_actions=bool(actions and actions.get('commit')==integration.get('commit'))
    accepted_actual=[m for m in modules if m['integration_acceptance']['accepted']]
    local_head=subprocess.run(['git','-C',str(ROOT/'integration'),'rev-parse','HEAD'],capture_output=True,text=True)
    p1_head=subprocess.run(['git','-C',str(P1),'rev-parse','HEAD'],capture_output=True,text=True)
    p1_targets=[m['module'] for m in modules if m.get('source_part')=='p1']
    p1_fixed_modules={m['module']:m['current_source']['source_fixed_commit'] for m in modules
                      if m.get('source_part')=='p1' and m['current_source'].get('source_fixed_commit')}
    p1_fixed_shas=sorted(set(p1_fixed_modules.values()))
    latest_incrementals=sorted((ROOT/'p1-audit').glob('incremental-*/p1-incremental.json'))
    p1_incremental=read_json(latest_incrementals[-1]) if latest_incrementals else None
    result=copy.deepcopy({k:v for k,v in base.items() if k not in ('modules','evidence_inventory','execution_records','P1_snapshot','observed_unpublished_candidates')})
    result.update(schema='chen-p0-round2-module-ledger-v2',snapshot_started_utc=start,
        snapshot_completed_utc=datetime.now(timezone.utc).isoformat(),
        draft_scope='version-bound read-only refresh; ledger-final is an output name, not a completed final proof claim',
        base_ledger=str(args.base_ledger),acceptance_configuration=config,
        accepted_integration=dict(integration,validated_new_production_modules=len(accepted_actual),
            local_checkout_head=local_head.stdout.strip(),local_checkout_matches_declared_sha=local_head.stdout.strip()==integration.get('commit'),
            full_project_build_on_this_SHA_passed=False,full_project_kernel_and_axiom_gates_passed=False,
            final_hLower_hUpper_free_main_theorem_available=False),
        module_count=len(modules),modules=modules,
        compile_status_counts=dict(collections.Counter(m['validation']['compile']['status'] for m in modules)),
        audit_catalog=audit_catalog,execution_record_parse_issues=malformed,
        locked_project_configuration_rechecks=config_rechecks,
        P1_snapshot={'local_head':p1_head.stdout.strip(),'completed_closure_records':len(state),'active_plan_module_count':688,
            'target_completed_records':{m:state[m] for m in p1_targets if m in state},
            'fixed_delivery_sha_obtained':p1_fixed_shas[0] if len(p1_fixed_shas)==1 else None,
            'fixed_module_commits_obtained':p1_fixed_modules,
            'latest_incremental_receipt':str(latest_incrementals[-1]) if latest_incrementals else None,
            'remote_observation':p1_incremental.get('remote') if p1_incremental else base.get('P1_snapshot'),
            'scope':'local hashes/records are real candidates; absence of a remote ref is not absence of work'},
        actions=actions,actions_match_declared_integration_sha=same_actions,
        actions_interpretation='Use only matching-SHA runs; inspect runner and steps. No CI was started by this refresh.',
        evidence_inventory=evidence,execution_records={'active_log_headers':active,'total_completed_records_read':len(records)},
        compiler_all_declaration_count=len(all_compiler_types),source_theorem_head_count=len(all_source_types))
    save_json('module-ledger.json',result)
    save_json('source-theorem-types.json',all_source_types)
    save_json('compiler-declarations.json',all_compiler_types)
    save_json('audit-catalog.json',audit_catalog)
    render_markdown(out,result,all_source_types,all_compiler_types)
    print(json.dumps({'snapshot':result['snapshot_completed_utc'],'module_count':len(modules),
        'accepted_components':len(accepted_actual),'compile_status_counts':result['compile_status_counts'],
        'compiler_declarations':len(all_compiler_types),'output_dir':str(out),'Lean_started':False},ensure_ascii=False))


def render_markdown(out,result,source_types,compiler_types):
    labels={'PASS_STRICT_TRUST0':'strict / trust 0 通过','PASS_ORIGINAL_LEANCHECKER':'原装内核重放通过',
            'STARTED_NO_COMPLETION':'已启动，无完成记录','FAILED_CURRENT_SOURCE':'当前源失败',
            'FAILED_OR_UNBOUND_CURRENT_REPLAY':'最近重放失败或对象尚未绑定当前源',
            'NOT_RECORDED_CURRENT_SOURCE':'无当前源完成回执'}
    modules=result['modules']; integration=result['accepted_integration']
    lines=['# Part 0 逐模块验证台账（增量快照）','',f"快照：`{result['snapshot_completed_utc']}`。",'',
      f"声明的集成 SHA：`{integration.get('commit')}`；树：`{integration.get('tree')}`。当前本地集成 checkout 为 `{integration.get('local_checkout_head')}`，是否等于该声明：`{integration.get('local_checkout_matches_declared_sha')}`。",'',
      f"本单共 **{len(modules)} 个生产模块**，按配置与匹配验证门实际接收 **{integration['validated_new_production_modules']} 个**。接收配置本身不使验证通过；必须匹配当前源码及完整通过回执。其余保留候选身份。",'',
      '本次仅读取现存记录、源码和配置，没有运行 Lean、Lake、leanchecker 或 CI。完整项目构建、最终项目内核/公理门与无 hLower/hUpper 的最终入口仍未完成。输出目录名 ledger-final 不代表证明目标已经完成。','',
      '| 所属 | 模块 | 编译 | 生产重放 | 公理审计 | 接收 |','|---|---|---|---|---|---|']
    for m in modules:
        v=m['validation'];a=m['integration_acceptance']
        lines.append(f"| {m['part_owner']} | `{m['module']}` | {labels.get(v['compile']['status'],v['compile']['status'])} | {labels.get(v['kernel_replay']['status'],v['kernel_replay']['status'])} | {'通过：'+str(v['axioms'].get('owned_declaration_count'))+' 个 defining-module 声明' if v['axioms']['status'].startswith('PASS') else '无当前源完整审计'} | {'已接收 '+str(a['commit']) if a['accepted'] else '候选'} |")
    lines += ['', '## 类型与审计证据等级','',
      f"`source-theorem-types.json` / `SOURCE_THEOREM_TYPES.md` 收录 {len(source_types)} 个当前源码 theorem/lemma 声明头。`compiler-declarations.json` / `COMPILER_TYPES.md` 收录 {len(compiler_types)} 个有完成审计证据的编译器声明类型，包括 private/generated 声明。两种来源明确区分。",'',
      '新审计只有完成 strict / trust 0、source/import 对象前后一致、DECL/MODULE/COUNT 全部吻合、实际审计源码包含 defining-module 枚举及 unsafe/axiom/传递公理检查，才可绑定生产模块。审计导入的主 .olean 必须与当前源码成功编译对象相同；存在的 .server/.private 也按记录比较前后哈希。历史已验证回执保留原证据等级，没有补造旧记录不具备的 import 捕获字段。','',
      '## 逐模块源码与未闭合输入','']
    for m in modules:
        o=m['source_original'];c=m['current_source'];v=m['validation']
        lines += [f"### {m['part_owner']} — `{m['module']}`",'',f"文件：`{m['path']}`；接收 Part：{', '.join(m.get('receiving_parts',[]))}。",'',
          '| 身份 | 完整值 |','|---|---|',
          f"| 原始固定提交 | `{o.get('commit')}` |" if o.get('commit') else '| 原始固定提交 | 尚未固定，按真实本地候选哈希追踪 |',
          f"| 原始 blob | `{o['git_blob_sha1']}` |",f"| 原始 SHA256 | `{o['sha256']}` |",
          f"| 当前 blob | `{c['git_blob_sha1']}` |",f"| 当前 SHA256 | `{c['source_sha256']}` |",
          f"| 当前固定源码提交 | `{c.get('source_fixed_commit')}` |",'',m.get('interface_scope_review',''),'',
          f"类型：源码 theorem/lemma {m['types']['source_extracted_count']} 个；编译器全部声明 {m['types']['compiler_all_declaration_count']} 个，其中匹配源码 theorem/lemma {m['types']['compiler_printed_count']} 个。",'',
          f"当前尚未完成的验证门：{', '.join(m['outstanding_validation_gates']) if m['outstanding_validation_gates'] else '该生产模块的三个门均有匹配回执'}。",'']
        attempts=v['all_completed_attempts_including_old_source_failures']
        if attempts:
            lines+=['| 实际动作 | 源 SHA256 | exit | 原始日志 |','|---|---|---|---|']
            for r in attempts:
                lines.append(f"| {r['action']} {'strict' if r.get('strict') else ''} | `{r.get('source_sha256_before')}` | {r.get('returncode')} | `{r['log']}` |")
            lines+=['']
            first=next((r for r in attempts if r.get('first_real_diagnostic')),None)
            if first:lines+=['保留的第一处真实诊断：','','```text',first.get('first_real_diagnostic_block',first['first_real_diagnostic']),'```','']
        if v['axioms'].get('binding'):
            lines += [f"公理回执：`{v['axioms']['binding']['audit_execution_record']['log']}`；绑定方法：{v['axioms']['binding']['method']}。",'']
        if v['axioms'].get('reused_historical_receipt'):
            lines += ['公理回执沿用基线台账中已验证的同源历史回执；没有补造 import 前后捕获。','']
        if m.get('unclosed_inputs'):
            lines += [f"接口审查及未闭合输入（审查时刻 `{m.get('unclosed_inputs_as_of')}`；其中早期验证待办以本节当前门状态为准）：",'']+[f'- {x}' for x in m['unclosed_inputs']]+['']
    lines += ['## 全局接口与验证边界','',
      'P5 只需要等待 P4-A 的同一实际 rho 的 K 密度界，不等待 P4-B hUpper。P1 实际权、支持/合法性、P2 实际积分和证书、P3 相应分布误差必须指向同一实际构造。完整 K/c 解析供应者和最终 hLower/hUpper 仍未闭合，不能移入结构或类型类后宣称消除。','',
      f"P1 闭包快照 {result['P1_snapshot']['completed_closure_records']} / {result['P1_snapshot']['active_plan_module_count']}；四个生产目标已有完成记录 {len(result['P1_snapshot']['target_completed_records'])} 个。远端交接状态以附带原始读取时刻为准，404 不代表没有成果。",'',
      f"本单附带 Actions 回执是否匹配声明的集成 SHA：`{result['actions_match_declared_integration_sha']}`。没有运行器或 steps=[] 的运行不能视为 Lean 验证已执行；没有触发新 CI。",'',
      '完整源/对象绑定、原始失败、日志快照、全部编译器声明与公理集合保存在 JSON。新的源码变化必须匹配自己的完成记录；部分日志和进行中任务不会被计作 PASS。','']
    (out/'MODULE_LEDGER.md').write_text('\n'.join(lines))
    source_lines=['# 当前源码 theorem/lemma 声明头','', '源码提取与编译器输出分别标明。','']
    for t in source_types:
        source_lines += [f"## `{t['module']}` / `{t['source_name']}`",'',f"源码 SHA256：`{t['source_sha256']}`；命名空间：`{t['namespace_context']}`。",'', '```lean',t['source_declaration_head'],'```','']
        if t.get('compiler_printed_type_available'):
            source_lines += [f"编译器声明：`{t['compiler_declaration_name']}`。",'']
            record={'type':t['compiler_printed_type']}
            if 'compiler_printed_readable_type' in t:
                record['readable_type']=t['compiler_printed_readable_type']
            source_lines += compiler_type_markdown(record)
    (out/'SOURCE_THEOREM_TYPES.md').write_text('\n'.join(source_lines))
    compiler_lines=['# 完成审计中打印的编译器类型','', '仅包含绑定当前源或明确沿用已验证同源历史回执的完整审计结果。','']
    for d in compiler_types:
        compiler_lines += [f"## `{d['name']}`",'',f"定义模块：`{d['module']}`；kind：`{d['kind']}`；源码 SHA256：`{d['production_source_sha256']}`。",'']
        compiler_lines += compiler_type_markdown(d)
        compiler_lines += ['传递公理：'+', '.join('`'+a+'`' for a in d['axioms'])+'。','']
    (out/'COMPILER_TYPES.md').write_text('\n'.join(compiler_lines))


if __name__=='__main__':
    main()
