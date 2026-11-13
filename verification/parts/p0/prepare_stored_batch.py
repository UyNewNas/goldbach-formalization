"""Materialize reviewed kernel-bounded proof expressions; never invokes Lean."""
import hashlib, json, os, pathlib, re, sys
assert os.environ.get('GITHUB_ACTIONS') == 'true', 'Remote GitHub generation only; never run locally'
root=pathlib.Path(os.environ['PROJECT']); logs=pathlib.Path(os.environ['LOGS'])
mode=sys.argv[1]
modules=[f'ImbalancedChen.Data.P5SubdivisionStoredBlock{k:03}' for k in range(64,72)]
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def snapshot():
    paths=list(root.glob('ImbalancedChen/**/*.lean'))+list(root.glob('.lake/build/lib/lean/**/*.olean*'))+list(root.glob('.lake/packages/*/.lake/build/lib/lean/**/*.olean*'))
    return {str(p.relative_to(root)):digest(p) for p in sorted(paths) if p.is_file()}
if mode=='prepare':
    receipt=[]
    for block in range(64,72):
        p=root/f'ImbalancedChen/Data/P5SubdivisionStoredBlock{block:03}.lean';before=p.read_text();base=4096*block; size=1817 if block==71 else 4096; count=(size+63)//64
        old=f'theorem source_index_at : ∀ j : Fin rows.size, (rows[j.val]).sourceIndex = {base} + j.val := by\n  decide'
        assert before.count(old)==1 and f'theorem rows_size : rows.size = {size} := rfl' in before
        chunks=[]
        for k in range(count):
            off=64*k; width=min(64,size-off)
            chunks.append(f'private theorem source_index_chunk_{k} : ∀ j : Fin {width}, (rows[{off} + j.val]\'(by rw [rows_size]; have := j.isLt; omega)).sourceIndex = {base} + ({off} + j.val) := by\n  decide +kernel\n')
        proof=[f'theorem source_index_at : ∀ j : Fin rows.size, (rows[j.val]).sourceIndex = {base} + j.val := by','  intro j','  have hj := j.isLt',f'  change j.val < {size} at hj']
        for k in range(count):
            if k<count-1: proof.append(f'  by_cases h{k} : j.val < {64*(k+1)}');prefix='  · ';indent='    '
            else:prefix='  ';indent='  '
            width=min(64,size-64*k)
            fin_bound='Nat.mod_lt _ (by decide)' if width==64 else 'by omega'
            proof.extend([prefix+f'have hi : {64*k} + j.val % 64 = j.val := by omega',indent+f'have hc := source_index_chunk_{k} ⟨j.val % 64, {fin_bound}⟩',indent+'simpa only [hi, Nat.zero_add] using hc'])
        after=before.replace(old,'\n'.join(chunks+['\n'.join(proof)]));p.write_text(after)
        assert before[:before.index(old)]==after[:after.index('private theorem source_index_chunk_0')]
        receipt.append({'module':modules[block-64],'old_sha256':hashlib.sha256(before.encode()).hexdigest(),'new_sha256':digest(p),'rows':size,'base':base,'data_unchanged':True})
    source=pathlib.Path(os.environ['GITHUB_WORKSPACE'])/'verification/parts/p0/Round6Audit.lean'
    audit=source.read_text();audit=audit[audit.index('set_option pp.all'):]
    start=audit.index('  let modules := #[');end=audit.index('  let allowed :=',start)
    audit=audit[:start]+'  let modules := #['+','.join('`'+m for m in modules)+']\n'+audit[end:]
    audit=audit.replace('  if names.contains finalBridge then\n    throwError "Final bridge must not be included in the owned-module census"\n','').replace('(names.push finalBridge).qsort','names.qsort')
    start=audit.index('    if name == finalBridge then');end=audit.index('  for (m, count) in counts do',start)
    audit=audit[:start]+'    liftIO <| IO.println s!"P0_ROUND6_DECL {record.compress}"\n'+audit[end:]
    audit='\n'.join('import '+m for m in modules)+'\nimport Lean.Util.CollectAxioms\n'+audit
    (root/'StoredBatchAudit.lean').write_text(audit)
    (logs/'STORED_BATCH_REPAIRS.json').write_text(json.dumps({'green':False,'scope':'blocks064-071 only; cached parent import only; not whole T01','source_commit':os.environ['SOURCE_COMMIT'],'repairs':receipt},indent=2))
    (logs/'modules.txt').write_text('\n'.join(modules)+'\n')
elif mode=='snapshot':
    (logs/'BATCH_OBJECTS_BEFORE.json').write_text(json.dumps(snapshot(),sort_keys=True))
elif mode=='verify':
    before=json.loads((logs/'BATCH_OBJECTS_BEFORE.json').read_text());assert before==snapshot(),'Source/import object changed during replay/audit'
    lines=(logs/'batch-types.log').read_text().splitlines()
    ds=[json.loads(x.removeprefix('P0_ROUND6_DECL ')) for x in lines if x.startswith('P0_ROUND6_DECL ')]
    inv=[json.loads(x.removeprefix('P0_ROUND6_SERIALIZED ')) for x in lines if x.startswith('P0_ROUND6_SERIALIZED ')]
    assert {x['module'] for x in inv}==set(modules) and len(inv)==len(modules)
    assert len({x['name'] for x in ds})==len(ds)
    for m in modules:
        names={d['name'] for d in ds if d['module']==m};i=next(i for i in inv if i['module']==m)
        assert names==set(i['serialized_constant_names'])==set(i['environment_constant_names'])
        if 'StoredBlock' in m: assert all(m+'.'+s in names for s in ['rows','rows_size','source_index_at'])
    assert all(not(d['is_unsafe'] or d['is_partial'] or d['is_axiom']) and set(d['axioms'])<={'propext','Classical.choice','Quot.sound'} and all(d[k].strip() and '⋯' not in d[k] for k in ['type','readable_type']) for d in ds)
    replay=[x.removeprefix('replaying ') for x in (logs/'batch-checker.log').read_text().splitlines() if x.startswith('replaying ')]
    assert len(replay)==len(modules) and set(replay)==set(modules)
    (logs/'BATCH_ACCEPTANCE.json').write_text(json.dumps({'status':'PASS_SELECTED_BLOCKS_ONLY','modules':modules,'complete_serialized_declarations':len(ds),'source_commit':os.environ['SOURCE_COMMIT'],'whole_t01_accepted':False,'proof_artifact_hash':digest(logs/'BATCH_OBJECTS_BEFORE.json')},indent=2))
else:raise SystemExit('bad mode')

