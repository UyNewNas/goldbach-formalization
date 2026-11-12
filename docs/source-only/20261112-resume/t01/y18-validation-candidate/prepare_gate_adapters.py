"""Static adaptation of frozen P2/Fine gate source. Does not import/run a gate."""
from pathlib import Path
import ast,difflib,hashlib,json
HERE=Path(__file__).resolve().parent
FINE=HERE.parent/'density-validation-v2'
P2=HERE.parents[2]/'p2-validation-v3'
def read(p):return p.read_text(encoding='utf-8')
def write(n,t):
 ast.parse(t,filename=n);(HERE/n).write_text(t,encoding='utf-8',newline='\n')
def replace(t,a,b):
 assert t.count(a)==1,(a[:100],t.count(a));return t.replace(a,b)
changes=[]
def record(name,old,new):
 changes.append({'file':name,'original_path':str(old),'original_sha256':hashlib.sha256(old.read_bytes()).hexdigest(),'selected_sha256':hashlib.sha256(new.encode()).hexdigest(),'diff':''.join(difflib.unified_diff(read(old).splitlines(True),new.splitlines(True),fromfile=str(old),tofile=name))})

# Original Fine stable snapshot collector: all meaningful object facets and
# source/setup/import provenance stay intact, plus the allowed exact native
# config extension and all1348 selected native paths.
old=FINE/'checkpoint_density.py';s=read(old)
s=s.replace('DENSITY_PROVENANCE.json','Y18_PROVENANCE.json')
s=replace(s,"for f in manifest['native_sources']:","for f in manifest['all_native_sources']:")
s=replace(s,"        good = head == pkg['rev'] and not dirty",'''        allowed_native_configuration = False
        if pkg['name'] == 'goldbach' and head == pkg['rev']:
            selected_config = manifest['native_configuration']['selected']
            changed = subprocess.check_output(['git', '-C', str(directory), 'diff', '--name-only', 'HEAD', '--'], text=True).splitlines()
            allowed_native_configuration = (changed == ['lakefile.toml']
                and (directory / 'lakefile.toml').is_file()
                and digest(directory / 'lakefile.toml') == selected_config['sha256'])
        good = head == pkg['rev'] and (not dirty or allowed_native_configuration)''')
s=s.replace("'tracked_sources_clean': not bool(dirty),","'tracked_sources_clean': not bool(dirty), 'exact_reviewed_native_configuration_only': allowed_native_configuration,")
s=s.replace('Rerun exact1854 kernel modules (1851 mathematical suppliers plus3 built audit wrappers) and complete FineDensity type/axiom gates.','Rerun exact798 kernel modules (797 mathematical suppliers plus1 actually built audit wrapper) and complete strict Y18 serialized/types/axioms/17-dual-report gates. Canonical888 are source/object bound dependencies, not individually declaration-audited.')
write('checkpoint_y18.py',s);record('checkpoint_y18.py',old,s)

# Strict collector keeps every P2 rejection. Mathematical scope and wrapper
# kernel scope are bound to independent explicit arrays, not historical counts.
old=FINE/'collect_density.py';s=read(old).replace("os.environ['DENSITY_MANIFEST']","os.environ['Y18_MANIFEST']")
s=replace(s,"targets=[manifest['targets'][0]['primary_module']]","targets=manifest['targets'][0]['primary_modules']")
s=s.replace('==1851','==797').replace('==1854','==798')
s=replace(s,"assert modules==[r['module'] for r in manifest['files']], 'Exact declared closure differs'","assert modules==[r['module'] for r in manifest['files']], 'Exact declared closure differs'")
s=replace(s,"'whole_PP_accepted':False","'whole_PP_accepted':False,'whole_P2_or_K_accepted':False")
write('collect_y18.py',s);record('collect_y18.py',old,s)

# Source/config/actual effective command/import-artifact joins. We require fresh
# source-bound production for standard goldbach888 as well as overlays460;
# this does not call their canonical public/private serialized sets audited.
old=FINE/'bind_compile_receipts.py';s=read(old)
s=s.replace('DENSITY_MANIFEST.json','Y18_MANIFEST.json')
s=replace(s,"        if role=='goldbach':assert libraries[0]['globs']==['MathlibNt','MathlibNt.+']",'''        if role=='goldbach':
            assert c['lean_lib']==cfg['goldbach']['selected_libraries']
            assert all(x.get('moreLeanArgs',[])==[] and x.get('leanOptions',[])==[] for x in c['lean_lib'])''')
s=s.replace("native_expected={r['module']:r for r in m['native_sources']}","native_expected={r['module']:r for r in m['all_native_sources']}")
s=s.replace('==43 and set(before)','==1348 and set(before)').replace('==1808 and set(owned)','==337 and set(owned)')
s=replace(s,"['SOURCE_PRE.json','SOURCE_POST.json','NATIVE_SOURCE_PRE.json','NATIVE_SOURCE_POST.json','batch-types.log','density-types.log','floor-types.log','FLOOR_TYPE_AXIOM_RESULT.json','batch-checker.log','WRAPPER_OBJECT_BINDINGS.json']","['SOURCE_PRE.json','SOURCE_POST.json','NATIVE_SOURCE_PRE.json','NATIVE_SOURCE_POST.json','batch-types.log','TARGET17_RESULT.json','batch-checker.log','WRAPPER_OBJECT_BINDINGS.json']")
s=replace(s,"    def setup_imports(entry,record):",'''    # Every selected import, including transitive setup entries, must consume
    # the same module's canonical guarded producer facets. No accepted alias or
    # restored project/native cache is available in this candidate.
    selected_output_parts = {}
    for supplier in m['files'] + m['all_native_sources']:
        supplier_root = project if supplier['module'].startswith('ImbalancedChen.') else project/'.lake/packages/goldbach'
        base = supplier_root/'.lake/build/lib/lean'/Path(*supplier['module'].split('.'))
        parts = {}
        for suffix in ['.olean', '.olean.server', '.olean.private', '.ir', '.ir.sig']:
            path = base.with_suffix(suffix).resolve()
            if path.is_file():
                receipt = captured(path)
                assert receipt['bytes'] > 0
                parts[str(path)] = {'part': suffix, 'path': str(path), 'sha256': receipt['sha256'], 'bytes': receipt['bytes']}
        assert str(base.with_suffix('.olean').resolve()) in parts
        selected_output_parts[supplier['module']] = parts
    def setup_imports(entry,record):''')
s=replace(s,"        imported=[]\n        for name in expected:",'''        imported=[]
        for name, arrays in arts.items():
            if name not in selected_output_parts:
                continue
            parts = []
            for array in arrays:
                assert isinstance(array, list)
                for value in array:
                    assert isinstance(value, str)
                    path = Path(value)
                    if not path.is_absolute():
                        path = Path(entry['command']['cwd'])/path
                    path = path.resolve()
                    receipt = captured(path)
                    canonical = selected_output_parts[name]
                    assert str(path) in canonical, ('Selected import consumes another module/path/cache artifact', record['module'], name, str(path), sorted(canonical))
                    producer = canonical[str(path)]
                    assert (receipt['sha256'], receipt['bytes']) == (producer['sha256'], producer['bytes'])
                    parts.append(producer)
            assert any(p['part'] == '.olean' for p in parts), ('Selected setup import missing public canonical olean', record['module'], name)
            imported.append({'module': name, 'selected_canonical_producer_join': parts, 'includes_transitive_setup_entries': True})
        for name in expected:''')
write('bind_compile_receipts_y18.py',s);record('bind_compile_receipts_y18.py',old,s)

# Package ownership includes Architect, already pinned by the unchanged3872B
# main lock. Only the selected goldbach library configuration may be modified.
old=FINE/'record_dependencies.py';s=read(old).replace('DENSITY_PROVENANCE.json','Y18_PROVENANCE.json')
s=replace(s,"    if dirty:\n        raise SystemExit(f'Tracked dependency sources changed: {p[\"name\"]}')",'''    if dirty:
        changed = subprocess.check_output(['git', '-C', str(path), 'diff', '--name-only', 'HEAD', '--'], text=True).splitlines()
        selected = manifest['native_configuration']['selected']
        if p['name'] != 'goldbach' or changed != ['lakefile.toml'] or hashlib.sha256((path/'lakefile.toml').read_bytes()).hexdigest() != selected['sha256']:
            raise SystemExit(f'Tracked dependency sources changed: {p["name"]}')''')
s=replace(s,"provenance['target']['external_imports'] + manifest['audit_external_imports']","provenance['target']['external_imports'] + json.loads((Path(__file__).parent/'ACTUAL_IMPORT_GRAPH.json').read_text())['true_other_external_modules'] + manifest['audit_external_imports']")
write('record_dependencies_y18.py',s);record('record_dependencies_y18.py',old,s)

write('audit_targets_y18.py','''"""Exact17 Y18 original theorem owners/types/collectAxioms/#print axioms dual gate."""
from pathlib import Path
import hashlib,json,os,re
assert os.environ.get('GITHUB_ACTIONS')=='true'
here=Path(__file__).resolve().parent;manifest_path=here/'Y18_MANIFEST.json'
m=json.loads(manifest_path.read_text());logs=Path(os.environ['LOGS']);project=Path(os.environ['PROJECT'])
prov=json.loads((project/'Y18_PROVENANCE.json').read_text());assert prov['manifest_sha256']==hashlib.sha256(manifest_path.read_bytes()).hexdigest()
raw=(logs/'batch-types.log').read_bytes();text=raw.decode('utf-8')
records=[json.loads(line.removeprefix('P0_ROUND6_DECL ')) for line in text.splitlines() if line.startswith('P0_ROUND6_DECL ')]
assert len(records)==len({r['name'] for r in records})
by={r['name']:r for r in records};selected=[];allowed={'propext','Classical.choice','Quot.sound'}
assert len(m['target_declarations'])==len({r['name'] for r in m['target_declarations']})==17
for expected in m['target_declarations']:
 r=by[expected['name']];assert r['module']==expected['module'] and r['kind']==expected['kind']=='theorem'
 assert not(r['is_axiom'] or r['is_partial'] or r['is_unsafe']) and set(r['axioms'])<=allowed
 assert all(isinstance(r[k],str) and r[k].strip() and not any(x in r[k] for x in ['⋯','…']) for k in ['type','readable_type'])
 name=re.escape(r['name'])
 deps=re.findall(r"['\\\"]?"+name+r"['\\\"]?\\s+depends on axioms:\\s*\\[([^\\]]*)\\]",text)
 none=re.findall(r"['\\\"]?"+name+r"['\\\"]?\\s+does not depend on any axioms",text)
 assert len(deps)+len(none)==1,('Missing/duplicate independent axiom output',r['name'])
 printed={x.strip() for x in deps[0].split(',') if x.strip()} if deps else set()
 assert printed==set(r['axioms']);selected.append(r)
out=logs/'TARGET17_RESULT.json';assert not out.exists() and not out.resolve().is_relative_to(project.resolve())
out.write_text(json.dumps({'status':'PASS_EXACT_ORIGINAL17_OWNER_FULL_TYPES_AND_DUAL_AXIOMS','manifest_sha256':prov['manifest_sha256'],'log_sha256':hashlib.sha256(raw).hexdigest(),'targets':selected,'whole_P2_or_PP_or_K_accepted':False},indent=2)+'\\n')
''')

(HERE/'GATE_ADAPTATION_DIFFS.json').write_text(json.dumps(changes,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'adapted_existing_gates':len(changes),'new_leaf_parser':'audit_targets_y18.py','all_adapters_AST_only':True,'no_stage_or_Lean_or_guard_execution':True}))
