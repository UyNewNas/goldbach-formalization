from pathlib import Path
import os,sys,hashlib,json,shutil,subprocess,time,tarfile
root=Path('/workspace/p29-atlas-20261126/chart-attempt-004')
old=Path('/workspace/p2-9-20261125')
target='ImbalancedChen.P2OriginalChartDerivativeCore'
sources=json.loads('''[["ImbalancedChen.P2OriginalEulerWordConjugacyCore","29b4397331ac573e1da3c5d3eb972790f58bc9f12f21834dfe4e1398d0f73d8f","d7de1edfd0cd0661e68a73f9e554a33eab46cf1d9def24dc9c478bae4e4ef838"],["ImbalancedChen.P4BSmoothGateUpperStep","7f51e436ec635bf89fbcf69f02e8c35f8b1a46df1183322f04c61dc69ea43764","c55f340219e01672a9777379a86f1d453956fa9aa3f5d5daf90ddb8caf74ef15"],["ImbalancedChen.P2SmoothPositiveArgumentCore","ca41044b480a835b5242f930e166f83159ec7386cd8c0bb78643f09f056481d4","677e39fcb0ae11aa830176b400970ca59f1357433660c158c1d96d0082d0f03f"],["ImbalancedChen.P4BSmoothStepDerivativeBudget","b2eb98634d337d9af63ecc951f34771dac8489361e64961332a7712bb1ef69d4","0eeb4b09869d76cdf83c8e2f5fae80d97c125b21a9135d10f6ad552098ec48b5"],["ImbalancedChen.P2SmoothLogFloorDerivativeCore","bc9fd90fadf2c967df05e4e9a0be2491d642b63369f060cd2aed25bee6c7b472","0fe2ffe476bc30fe476081943f417ea58fac86d9bc55ceb25d19230f33b6c0cd"],["ImbalancedChen.P2OriginalChartDerivativeCore","0c520aa976196d9f2f3d8c8c6eee2628deb599ce61d3edd735b33a4b7f33ee5b",null]]''')
source_text="import ImbalancedChen.P2OriginalEulerWordConjugacyCore\nimport ImbalancedChen.P2SmoothLogFloorDerivativeCore\nimport Mathlib.Analysis.Calculus.ContDiff.Bounds\n\n/-!\nThe finite chart differentiation bounds used by the actual Gamma5 atlas.\nThe original declarations and mathematical bounds are retained, with the\nproofs written for the pinned Lean and Mathlib APIs.\n-/\nnamespace ImbalancedChen.Part5OriginalH430ClassicalSmoothEulerBounds\nnoncomputable section\nopen Finset Set Filter Real\nopen P4B\nopen scoped Classical Topology BigOperators ContDiff\n\n/-- Bounds at every mixed order, uniform in the chart parameters. -/\ndef BoundedDerivatives {ι : Type*} {d : ℕ} (F : ι → E d → ℝ) : Prop :=\n  (∀ i,ContDiff ℝ ∞ (F i)) ∧\n    ∀ n : ℕ,∃ C : ℝ,0≤C ∧ ∀ i x,‖iteratedFDeriv ℝ n (F i) x‖≤C\n\ntheorem affine {ι : Type*} {d : ℕ} {f : ℝ → ℝ} (hf : ScalarBound f) (a slope : ι → ℝ)\n    (L : E d →L[ℝ] ℝ) {R : ℝ} (hR : 0≤R) (hslope : ∀i,|slope i|≤R) :\n    BoundedDerivatives (fun i x => f (a i+slope i*L x)) := by\n  refine ⟨fun i => hf.1.comp (contDiff_const.add (contDiff_const.mul L.contDiff)),?_⟩\n  intro n\n  obtain ⟨A,hA,hfA⟩ := hf.2 n\n  refine ⟨A*(R*‖L‖)^n,mul_nonneg hA (pow_nonneg (mul_nonneg hR (norm_nonneg _)) _),?_⟩\n  intro i x\n  let g := fun t : ℝ => f (a i+t)\n  let M := (slope i) • L\n  have hg : ContDiff ℝ ∞ g := hf.1.comp (contDiff_const.add contDiff_id)\n  change ‖iteratedFDeriv ℝ n (g ∘ M) x‖≤_\n  rw [M.iteratedFDeriv_comp_right hg x (mod_cast (le_top : (n : ℕ∞) ≤ ⊤))]\n  have hnorm := (iteratedFDeriv ℝ n g (M x)).norm_compContinuousLinearMap_le (fun _ : Fin n => M)\n  have heq := congrFun (iteratedDeriv_comp_const_add n f (a i)) (M x)\n  have he : ‖iteratedFDeriv ℝ n g (M x)‖≤A := by\n    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,Real.norm_eq_abs,show iteratedDeriv n g (M x)=_ from heq]\n    exact hfA _\n  have hM : ‖M‖≤R*‖L‖ := by\n    rw [show ‖M‖ = ‖slope i‖ * ‖L‖ from norm_smul (slope i) L, Real.norm_eq_abs]\n    exact mul_le_mul_of_nonneg_right (hslope i) (norm_nonneg _)\n  calc\n    _ ≤ ‖iteratedFDeriv ℝ n g (M x)‖*‖M‖^n := by\n      simpa only [prod_const,card_univ,Fintype.card_fin] using hnorm\n    _ ≤ _ := mul_le_mul he (pow_le_pow_left₀ (norm_nonneg _) hM n) (pow_nonneg (norm_nonneg _) n) hA\n\ntheorem one {ι : Type*} {d : ℕ} : BoundedDerivatives (fun _ : ι => fun _ : E d => (1:ℝ)) := by\n  refine ⟨fun _ => contDiff_const,fun n => ⟨1,zero_le_one,?_⟩⟩\n  intro _ x\n  cases n with\n  | zero => simp\n  | succ n => simp [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]\n\ntheorem add {ι : Type*} {d : ℕ} {F G : ι → E d → ℝ}\n    (hF : BoundedDerivatives F) (hG : BoundedDerivatives G) :\n    BoundedDerivatives (fun i x => F i x+G i x) := by\n  refine ⟨fun i => (hF.1 i).add (hG.1 i),?_⟩\n  intro n\n  obtain ⟨B,hB,hf⟩ := hF.2 n\n  obtain ⟨C,hC,hg⟩ := hG.2 n\n  refine ⟨B+C,add_nonneg hB hC,?_⟩\n  intro i x\n  change ‖iteratedFDeriv ℝ n (F i+G i) x‖≤_\n  rw [iteratedFDeriv_add_apply ((contDiff_infty.mp (hF.1 i)) n).contDiffAt ((contDiff_infty.mp (hG.1 i)) n).contDiffAt]\n  exact (norm_add_le _ _).trans (add_le_add (hf i x) (hg i x))\n\ntheorem sub {ι : Type*} {d : ℕ} {F G : ι → E d → ℝ}\n    (hF : BoundedDerivatives F) (hG : BoundedDerivatives G) :\n    BoundedDerivatives (fun i x => F i x-G i x) := by\n  refine ⟨fun i => (hF.1 i).sub (hG.1 i),?_⟩\n  intro n\n  obtain ⟨B,hB,hf⟩ := hF.2 n\n  obtain ⟨C,hC,hg⟩ := hG.2 n\n  refine ⟨B+C,add_nonneg hB hC,?_⟩\n  intro i x\n  change ‖iteratedFDeriv ℝ n (F i-G i) x‖≤_\n  rw [iteratedFDeriv_sub_apply ((contDiff_infty.mp (hF.1 i)) n).contDiffAt ((contDiff_infty.mp (hG.1 i)) n).contDiffAt]\n  exact (norm_sub_le _ _).trans (add_le_add (hf i x) (hg i x))\n\ntheorem mul {ι : Type*} {d : ℕ} {F G : ι → E d → ℝ}\n    (hF : BoundedDerivatives F) (hG : BoundedDerivatives G) :\n    BoundedDerivatives (fun i x => F i x*G i x) := by\n  refine ⟨fun i => (hF.1 i).mul (hG.1 i),?_⟩\n  choose B hB hf using hF.2\n  choose C hC hg using hG.2\n  intro n\n  refine ⟨∑ j∈range (n+1),(n.choose j:ℝ)*B j*C (n-j),\n    sum_nonneg (fun j _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB j)) (hC _)),?_⟩\n  intro i x\n  have hle : ‖iteratedFDeriv ℝ n (fun y => F i y*G i y) x‖≤\n      ∑ j∈range (n+1),(n.choose j:ℝ)*‖iteratedFDeriv ℝ j (F i) x‖*‖iteratedFDeriv ℝ (n-j) (G i) x‖ :=\n    norm_iteratedFDeriv_mul_le (hF.1 i) (hG.1 i) x (mod_cast (le_top : (n : ℕ∞) ≤ ⊤))\n  apply hle.trans\n  exact sum_le_sum (fun j _ => mul_le_mul (mul_le_mul_of_nonneg_left (hf j i x) (Nat.cast_nonneg _))\n    (hg (n-j) i x) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hB j)))\n\ntheorem prod {ι σ : Type*} [DecidableEq σ] {d : ℕ} (S : Finset σ) (F : σ → ι → E d → ℝ)\n    (hF : ∀ j,BoundedDerivatives (F j)) :\n    BoundedDerivatives (fun i x => ∏ j∈S,F j i x) := by\n  induction S using Finset.induction_on with\n  | empty => simpa only [Finset.prod_empty] using (one (ι:=ι) (d:=d))\n  | @insert j S hj ih => simpa only [Finset.prod_insert hj] using mul (hF j) ih\n\nend\nend ImbalancedChen.Part5OriginalH430ClassicalSmoothEulerBounds\n"
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,v):
 p.parent.mkdir(exist_ok=True,parents=True)
 p.write_text(json.dumps(v,sort_keys=True,indent=2)+'\n')
def require(test,msg):
 if not test:raise ValueError(msg)
root.mkdir(parents=True,exist_ok=False)
os.chdir(root)
out=root/'.lake/p2-private';lib=out/'lib'
oldout=old/'.lake/p2-private';drivers=old/'verification/part2'
sys.path.insert(0,str(drivers))
import run_winner9_private_audit as audit
import run_winner9_private_checks as checks
require(sha(drivers/'run_winner9_private_audit.py')=='571b6137da5e1a1cf9ec9020e03b4f881bc4f0f3f36eae0aa9d62a3a5c0939d5','audit driver mismatch')
require(sha(oldout/'records.json')=='e95c1c2aeaad29c651c897ec0c2ec6669f0719a5554148c68c4421745f3b5ed8','original records drift')
source_records=json.loads((oldout/'records.json').read_text())
records={};originals={}
for n,h,o in sources:
 rel=Path(*n.split('.'))
 source=root/rel.with_suffix('.lean')
 source.parent.mkdir(exist_ok=True,parents=True)
 if n==target:
  source.write_text(source_text)
 else:
  opath=oldout/'lib'/rel.with_suffix('.olean')
  originals[n]=dict(source_sha256=sha(old/rel.with_suffix('.lean')),object_sha256=sha(opath))
  require(originals[n]==dict(source_sha256=h,object_sha256=o),'provider source/object hash mismatch '+n)
  shutil.copy2(old/rel.with_suffix('.lean'),source)
  dest=lib/rel.parent;dest.mkdir(exist_ok=True,parents=True)
  for f in opath.parent.glob(opath.stem+'.*'):
   if f.is_file():shutil.copy2(f,dest/f.name)
  records[n]=source_records[n]
 require(sha(source)==h,'source hash mismatch '+n)
git=lambda p,cmd:subprocess.check_output(['git',*cmd],cwd=p,text=True).strip()
require(git(checks.MATHLIB,['rev-parse','HEAD'])==checks.PIN,'mathlib pin')
toolchain=dict(lean_version=subprocess.check_output([checks.LEAN,'--version'],text=True).strip(),lean_binary_sha256=sha(Path(checks.LEAN)),mathlib_commit=checks.PIN)
nodes=audit.project_nodes(root,target)
require(set(nodes)=={n for n,h,o in sources},'source closure mismatch')
frozen=lambda ns:audit.snapshot(root,lib,ns,toolchain)
dep_nodes={n:node for n,node in nodes.items() if n!=target}
prev=frozen(dep_nodes)
audit.verify_compilation(records,dep_nodes,prev)
deps=nodes[target]['deps'];source=nodes[target]['source'];obj=lib/Path(*target.split('.')).with_suffix('.olean')
require(not obj.exists(),'target object already exists')
env=dict(os.environ);env['PYTHONDONTWRITEBYTECODE']='1'
# Prefer the isolated project roots. The compiler service normally exports locked Mathlib package paths.
mp=Path(checks.MATHLIB);mathpaths=[mp/'.lake/build/lib/lean',*sorted((mp/'.lake/packages').glob('*/.lake/build/lib/lean'))]
env['LEAN_PATH']=':'.join([str(lib),*(str(p) for p in mathpaths if p.is_dir())])
log=out/'logs'/f'{target}.attempt1.log';log.parent.mkdir(parents=True,exist_ok=True)
cmd=[checks.LEAN,'-t0','-j1','-M11264','-DwarningAsError=true','-DmaxRecDepth=50000','-DmaxHeartbeats=40000000','-o',str(obj),str(source.relative_to(root))]
start=time.monotonic()
with log.open('w') as f:
 result=subprocess.run(cmd,cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT)
after=frozen(dep_nodes)
print('NORMAL',result.returncode,log.read_text()[:12000],flush=True)
require(result.returncode==0,'target normal source compile failed')
require(prev==after and sha(source)==sources[-1][1],'normal source/closure changed')
audit.verify_compilation(records,dep_nodes,after)
fd={n:{k:prev['project'][n][k] for k in ('source_sha256','object_sha256')} for n in sorted(prev['project'])}
rec={'module':target,'source':str(source.relative_to(root)),'source_sha256':sha(source),'object':str(obj),'object_sha256':sha(obj),'toolchain':toolchain,'deps':{n:records[n]['object_sha256'] for n in deps},'dependency_signatures':{n:records[n]['closure_signature'] for n in deps},'cache_schema':2,'seconds':round(time.monotonic()-start,3),'command':cmd,'exit_code':result.returncode,'log':str(log.relative_to(root)),'attempts':[{'command':cmd,'exit_code':result.returncode,'log':str(log.relative_to(root))}],'new_strict_compile':True,'dependency_file_check':{'modules':len(fd),'expected_sha256':checks.json_digest(fd),'before_sha256':checks.json_digest(fd),'after_sha256':checks.json_digest(fd),'before_matches_records':True,'after_matches_records':True},'lean':'4.33.0-rc1','mathlib_commit':checks.PIN,'provenance':'New direct strict source compile in isolated private directory; unchanged original audit driver and schema-2 gates.'}
rec['closure_signature']=checks.closure_signature(rec);records[target]=rec
write(out/'records.json',records)
write(root/'normal-snapshots.json',{'before':prev,'after':after,'real_project_source_closure':list(nodes),'compile_command':cmd,'provider_recompiles':0,'mathlib_boundary':toolchain,'lean_path':env['LEAN_PATH']})
audit.verify_compilation(records,nodes,frozen(nodes))
rc=subprocess.run([sys.executable,str(drivers/'run_winner9_private_audit.py'),target,'--summary-name','p29-chart.json','--memory-mb','11264'],env=env,cwd=root).returncode
latest=out/'audit'/target/'latest.json'
receipt=json.loads(latest.read_text()) if latest.is_file() else {}
require(rc==0 and receipt.get('accepted') is True and receipt['replay']['inputs_unchanged'] and receipt['audit']['inputs_unchanged'],'original audit failed '+str(receipt.get('error')))
for art,dgst in receipt['artifacts'].items():require(sha(root/art)==dgst,'artifact hash '+art)
require(sha(obj)==receipt['object_sha256']==rec['object_sha256'],'target postcheck')
for n in originals:
 rel=Path(*n.split('.'))
 require(sha(old/rel.with_suffix('.lean'))==originals[n]['source_sha256'] and sha(oldout/'lib'/rel.with_suffix('.olean'))==originals[n]['object_sha256'],'original provider drift')
require(frozen(dep_nodes)==prev,'provider final postcheck')
include=list(sorted(q for q in root.rglob('*') if q.is_file()))
files={str(q.relative_to(root)):{'sha256':sha(q),'bytes':q.stat().st_size} for q in include}
manifest={'target':target,'source_blob':'195c75bc8052a0f5d69b9471dfda72be1351e817','source_sha256':sha(source),'object_sha256':sha(obj),'declarations':receipt['audit']['declaration_count'],'axioms':receipt['audit']['axiom_counts'],'normal_compiles':[target],'provider_modules':sorted(originals),'receipt_sha256':sha(latest),'files':files,'normal_driver_sha256':sha(Path(__file__)),'original_audit_driver_sha256':sha(drivers/'run_winner9_private_audit.py')}
write(root/'manifest.json',manifest)
arch=root.parent/'qualified-chart-004.tar.gz'
with tarfile.open(arch,'x:gz') as tf:
 for q in [*include,root/'manifest.json']:tf.add(q,arcname=str(q.relative_to(root)),recursive=False)
with tarfile.open(arch) as tf:
 for it in tf.getmembers():require(hashlib.sha256(tf.extractfile(it).read()).hexdigest()==sha(root/it.name),'archive recheck')
print(json.dumps({k:v for k,v in manifest.items() if k!='files'}),flush=True)
print('ARCHIVE',str(arch),arch.stat().st_size,sha(arch),'MANIFEST',sha(root/'manifest.json'),'MEMBERS',len(include)+1,flush=True)
