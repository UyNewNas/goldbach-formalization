"""Materialize reviewed kernel-bounded proof expressions; never invokes Lean."""
import hashlib, json, os, pathlib, re, sys
root=pathlib.Path(os.environ['PROJECT']); logs=pathlib.Path(os.environ['LOGS'])
mode=sys.argv[1]
targets=['ImbalancedChen.P2OriginalFourthCapProducerInterface']
def imports(text):
    # Lean nested block comments must not create phantom imports.
    text=re.sub(r'--[^\n]*','',text)
    while '/-' in text:
        start=text.index('/-');depth=1;i=start+2
        while depth and i<len(text):
            if text[i:i+2]=='/-':depth+=1;i+=2
            elif text[i:i+2]=='-/':depth-=1;i+=2
            else:i+=1
        assert depth==0
        text=text[:start]+' '+text[i:]
    return [m for line in text.splitlines() if re.match(r'^\s*(?:public\s+)?import\s',line) for m in re.sub(r'^\s*(?:public\s+)?import\s+','',line).split()]
seen=set();modules=[]
def visit(m):
    if m in seen:return
    p=root/(m.replace('.','/')+'.lean')
    if not p.exists():
        assert not m.startswith('ImbalancedChen.'),m
        return
    seen.add(m)
    for n in imports(p.read_text()):visit(n)
    modules.append(m)
for m in targets:visit(m)
assert set(targets)<=set(modules)
manifest=json.loads((pathlib.Path(__file__).resolve().parent/'candidate-manifest.json').read_text())
assert modules==manifest['closure_modules'], 'Candidate local import closure changed'

SCOPED_REFERENCE = {'preserved_public_types': [{'owner': 'ImbalancedChen.FirstExitTree', 'record': {'name': 'ImbalancedChen.evenListLength', 'type': '{α : Type u_1} → List.{u_1} α → Bool', 'readable_type': '{α : Type u_1} → List.{u_1} α → Bool'}}, {'owner': 'ImbalancedChen.FirstExitTree', 'record': {'name': 'ImbalancedChen.firstExitCorrection', 'type': '{α : Type u_1} →\n  (retained : Bool → List.{u_1} α → Bool) →\n    (h : α → Real) → (selectedPrefix : List.{u_1} α) → (positive : Bool) → (mass : Real) → List.{u_1} α → Real', 'readable_type': '{α : Type u_1} → (Bool → List.{u_1} α → Bool) → (α → ℝ) → List.{u_1} α → Bool → ℝ → List.{u_1} α → ℝ'}}, {'owner': 'ImbalancedChen.FirstExitDepthSplice', 'record': {'name': 'ImbalancedChen.firstExitDepthFrontier', 'type': '{α : Type u_1} →\n  (k : Nat) →\n    (parent : Bool → List.{u_1} α → Bool) →\n      (h : α → Real) →\n        (selectedPrefix : List.{u_1} α) →\n          (positive : Bool) → (mass : Real) → List.{u_1} α → List.{u_1} (ImbalancedChen.FirstExitDepthState.{u_1} α)', 'readable_type': '{α : Type u_1} →\n  ℕ →\n    (Bool → List.{u_1} α → Bool) →\n      (α → ℝ) → List.{u_1} α → Bool → ℝ → List.{u_1} α → List.{u_1} (ImbalancedChen.FirstExitDepthState.{u_1} α)'}}, {'owner': 'ImbalancedChen.FirstExitDepthSplice', 'record': {'name': 'ImbalancedChen.firstExitDepthTerminalPolynomial', 'type': '{α : Type u_1} →\n  (k : Nat) →\n    (parent : Bool → List.{u_1} α → Bool) →\n      (h : α → Real) → (selectedPrefix : List.{u_1} α) → (positive : Bool) → (mass : Real) → List.{u_1} α → Real', 'readable_type': '{α : Type u_1} → ℕ → (Bool → List.{u_1} α → Bool) → (α → ℝ) → List.{u_1} α → Bool → ℝ → List.{u_1} α → ℝ'}}, {'owner': 'ImbalancedChen.FirstExitTree', 'record': {'name': 'ImbalancedChen.firstExitRetainedLeaves', 'type': '{α : Type u_1} →\n  (retained : Bool → List.{u_1} α → Bool) →\n    (h : α → Real) →\n      (selectedPrefix : List.{u_1} α) →\n        (positive : Bool) → (mass : Real) → List.{u_1} α → List.{u_1} (ImbalancedChen.FirstExitLeaf.{u_1} α)', 'readable_type': '{α : Type u_1} →\n  (Bool → List.{u_1} α → Bool) →\n    (α → ℝ) → List.{u_1} α → Bool → ℝ → List.{u_1} α → List.{u_1} (ImbalancedChen.FirstExitLeaf.{u_1} α)'}}, {'owner': 'ImbalancedChen.FirstExitTree', 'record': {'name': 'ImbalancedChen.firstExitRetainedPolynomial', 'type': '{α : Type u_1} →\n  (retained : Bool → List.{u_1} α → Bool) →\n    (h : α → Real) → (selectedPrefix : List.{u_1} α) → (positive : Bool) → (mass : Real) → List.{u_1} α → Real', 'readable_type': '{α : Type u_1} → (Bool → List.{u_1} α → Bool) → (α → ℝ) → List.{u_1} α → Bool → ℝ → List.{u_1} α → ℝ'}}], 'proof_api_new_equations': [{'owner': 'ImbalancedChen.FirstExitTree', 'name': 'ImbalancedChen.evenListLength_nil'}, {'owner': 'ImbalancedChen.FirstExitTree', 'name': 'ImbalancedChen.evenListLength_cons'}, {'owner': 'ImbalancedChen.FirstExitTree', 'name': 'ImbalancedChen.firstExitRetainedPolynomial_nil'}, {'owner': 'ImbalancedChen.FirstExitTree', 'name': 'ImbalancedChen.firstExitRetainedPolynomial_cons'}, {'owner': 'ImbalancedChen.FirstExitTree', 'name': 'ImbalancedChen.firstExitCorrection_nil'}, {'owner': 'ImbalancedChen.FirstExitTree', 'name': 'ImbalancedChen.firstExitCorrection_cons'}, {'owner': 'ImbalancedChen.FirstExitTree', 'name': 'ImbalancedChen.firstExitRetainedLeaves_nil'}, {'owner': 'ImbalancedChen.FirstExitTree', 'name': 'ImbalancedChen.firstExitRetainedLeaves_cons'}, {'owner': 'ImbalancedChen.FirstExitDepthSplice', 'name': 'ImbalancedChen.firstExitDepthFrontier_nil'}, {'owner': 'ImbalancedChen.FirstExitDepthSplice', 'name': 'ImbalancedChen.firstExitDepthFrontier_cons'}, {'owner': 'ImbalancedChen.FirstExitDepthSplice', 'name': 'ImbalancedChen.firstExitDepthTerminalPolynomial_nil'}, {'owner': 'ImbalancedChen.FirstExitDepthSplice', 'name': 'ImbalancedChen.firstExitDepthTerminalPolynomial_cons'}]}
assert manifest['preserved_public_types'] == [x['record'] for x in SCOPED_REFERENCE['preserved_public_types'] if x['owner'] in modules], 'Public type scope changed'
assert manifest['proof_api_new_equations'] == [x['name'] for x in SCOPED_REFERENCE['proof_api_new_equations'] if x['owner'] in modules], 'Equation scope changed'
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def snapshot():
    paths=list(root.glob('ImbalancedChen/**/*.lean'))+list(root.glob('.lake/build/lib/lean/**/*.olean*'))+list(root.glob('.lake/packages/*/.lake/build/lib/lean/**/*.olean*'))
    return {str(p.relative_to(root)):digest(p) for p in sorted(paths) if p.is_file()}
if mode=='prepare':
    source=pathlib.Path(os.environ['GITHUB_WORKSPACE'])/'verification/parts/p0/p2-fourth-cap-api/Round6AuditTemplate.lean'
    audit=source.read_text();audit=audit[audit.index('set_option pp.all'):]
    start=audit.index('  let modules := #[');end=audit.index('  let allowed :=',start)
    audit=audit[:start]+'  let modules := #['+','.join('`'+m for m in modules)+']\n'+audit[end:]
    audit=audit.replace('  if names.contains finalBridge then\n    throwError "Final bridge must not be included in the owned-module census"\n','').replace('(names.push finalBridge).qsort','names.qsort')
    start=audit.index('    if name == finalBridge then');end=audit.index('  for (m, count) in counts do',start)
    audit=audit[:start]+'    liftIO <| IO.println s!"P0_ROUND6_DECL {record.compress}"\n'+audit[end:]
    audit='\n'.join('import '+m for m in modules)+'\nimport Lean.Util.CollectAxioms\n'+audit
    (root/'CandidateAudit.lean').write_text(audit)
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
    by_name={d['name']:d for d in ds}
    if 'ImbalancedChen.SmallRoughMainTerm' in modules:
        assert by_name['ImbalancedChen.reciprocalTotientDensity.eq_1']['module'] == 'ImbalancedChen.SmallRoughMainTerm', 'reciprocalTotientDensity equation canonical owner mismatch'
    else:
        assert 'ImbalancedChen.reciprocalTotientDensity.eq_1' not in by_name, 'Out-of-scope generated declaration'
    if 'ImbalancedChen.ActualSmallRosserDensity' in modules:
        assert by_name['ImbalancedChen.actualSmallRosserMinusDensity.eq_1']['module'] == 'ImbalancedChen.ActualSmallRosserDensity', 'actualSmallRosserMinusDensity equation canonical owner mismatch'
    else:
        assert 'ImbalancedChen.actualSmallRosserMinusDensity.eq_1' not in by_name, 'Out-of-scope generated declaration'
    if 'ImbalancedChen.ActualSmallRosserDensity' in modules:
        assert by_name['ImbalancedChen.actualSmallRosserPlusDensity.eq_1']['module'] == 'ImbalancedChen.ActualSmallRosserDensity', 'actualSmallRosserPlusDensity equation canonical owner mismatch'
    else:
        assert 'ImbalancedChen.actualSmallRosserPlusDensity.eq_1' not in by_name, 'Out-of-scope generated declaration'
    if 'ImbalancedChen.PhysicalUpperWeightBridge' in modules:
        assert by_name['ImbalancedChen.physicalDensitySum.eq_1']['module'] == 'ImbalancedChen.PhysicalUpperWeightBridge', 'physicalDensitySum equation canonical owner mismatch'
    else:
        assert 'ImbalancedChen.physicalDensitySum.eq_1' not in by_name, 'Out-of-scope generated declaration'
    if 'ImbalancedChen.FinitePrimeGeometryCore' in modules:
        assert by_name['ImbalancedChen.ordinaryParityRosserPolicy.eq_1']['module'] == 'ImbalancedChen.FinitePrimeGeometryCore', 'ordinaryParityRosserPolicy equation canonical owner mismatch'
    else:
        assert 'ImbalancedChen.ordinaryParityRosserPolicy.eq_1' not in by_name, 'Out-of-scope generated declaration'
    if 'ImbalancedChen.FinitePrimeGeometryCore' in modules:
        assert by_name['ImbalancedChen.ancestorFrozenPolicy.eq_1']['module'] == 'ImbalancedChen.FinitePrimeGeometryCore', 'ancestorFrozenPolicy equation canonical owner mismatch'
    else:
        assert 'ImbalancedChen.ancestorFrozenPolicy.eq_1' not in by_name, 'Out-of-scope generated declaration'
    if 'ImbalancedChen.FinitePrimeGeometryCore' in modules:
        assert by_name['ImbalancedChen.frozenParityRosserPolicy.eq_1']['module'] == 'ImbalancedChen.FinitePrimeGeometryCore', 'frozenParityRosserPolicy equation canonical owner mismatch'
    else:
        assert 'ImbalancedChen.frozenParityRosserPolicy.eq_1' not in by_name, 'Out-of-scope generated declaration'
    assert set(manifest['proof_api_new_equations']) <= set(by_name), 'Computation equation missing'
    for preserved in manifest['preserved_public_types']:
        assert preserved['name'] in by_name, 'Original public definition missing'
        assert all(by_name[preserved['name']][k]==preserved[k] for k in ['type','readable_type']), 'Original public definition type changed'
    for m in modules:
        names={d['name'] for d in ds if d['module']==m};i=next(i for i in inv if i['module']==m)
        assert names==set(i['serialized_constant_names'])==set(i['environment_constant_names'])
        if 'StoredBlock' in m: assert all(m+'.'+s in names for s in ['rows','rows_size','source_index_at'])
    assert all(not(d['is_unsafe'] or d['is_partial'] or d['is_axiom']) and set(d['axioms'])<={'propext','Classical.choice','Quot.sound'} and all(d[k].strip() and '⋯' not in d[k] for k in ['type','readable_type']) for d in ds)
    replay=[x.removeprefix('replaying ') for x in (logs/'batch-checker.log').read_text().splitlines() if x.startswith('replaying ')]
    assert len(replay)==len(modules) and set(replay)==set(modules)
    (logs/'BATCH_ACCEPTANCE.json').write_text(json.dumps({'status':'PASS_EXACT_CANDIDATE_CLOSURE_ONLY','modules':modules,'complete_serialized_declarations':len(ds),'source_commit':os.environ['SOURCE_COMMIT'],'whole_t01_accepted':False, 'whole_p1_accepted':False,'proof_artifact_hash':digest(logs/'BATCH_OBJECTS_BEFORE.json')},indent=2))
else:raise SystemExit('bad mode')
