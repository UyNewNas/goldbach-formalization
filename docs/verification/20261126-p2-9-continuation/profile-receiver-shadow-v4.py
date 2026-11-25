INPUT_TEXT="[{\"module\":\"ImbalancedChen.P2FiniteMarkedGamma5RadialProfileCollar\",\"blob\":\"33196c7c3fc1c4aeac651871482bb142e55deca8\",\"sha256\":\"64959b49ba41fc30534bcbd7d31d97ba8dd803ff7361ef97b69ec24f3297f93d\",\"source\":\"import ImbalancedChen.P2FiniteMarkedGamma5RadialTupleCount\\nimport ImbalancedChen.P2FiniteMarkedGamma5IntegerSupport\\n\\n/-!\\nSOURCE ONLY / UNCOMPILED / ZERO NEW FORMAL CREDIT.\\n\\nThe outer physical-product collar of one existing Gamma5 profile. Width\\nis log(1+h), so nonzero support has complete product < (1+h)N < 2N.\\nThe integer box is derived from positivity and the complete product; no\\ncoordinate is discarded, identified with another slot, or assigned an\\nextra arithmetic filter. Empty old and rough blocks are retained.\\n\\nThe ordinary sum below uses exactly finPhysicalProfile, whose weights\\nalready lie in [0,1]. It is a single fixed-split ambient sum, not the sum\\nof all history marks, a J identification, or a prime-product estimate.\\n-/\\nnamespace ImbalancedChen.P2FiniteMarkedGamma5RadialProfileCollar\\nnoncomputable section\\nopen Filter Finset Real\\nopen Part5OriginalH430FrozenRootRefinement (frozenLeafCutoffFloor)\\nopen P2FiniteMarkedGamma5ActualRank (frozenSourceRankBound)\\nopen P2FiniteMarkedGamma5PhysicalExtension\\nopen P2FiniteMarkedGamma5EulerWordBudget\\nopen P2FiniteMarkedGamma5IntegerSupport\\nopen P2FiniteMarkedGamma5RadialRoughMass\\nopen P2FiniteMarkedGamma5RadialTupleCount\\nopen scoped Classical Topology BigOperators\\n\\ndef radialWidth (h : ℝ) : ℝ := log (1 + h)\\n\\ntheorem radialWidth_pos {h : ℝ} (hp : 0 < h) : 0 < radialWidth h :=\\n  log_pos (by linarith only [hp])\\n\\ntheorem radialWidth_le_one {h : ℝ} (hp : 0 < h) (h8 : h ≤ 1 / 8) :\\n    radialWidth h ≤ 1 := by\\n  have hh := log_le_sub_one_of_pos (show 0 < 1 + h by linarith only [hp])\\n  dsimp only [radialWidth]\\n  linarith only [hh, h8]\\n\\ntheorem exp_radialWidth {h : ℝ} (hp : 0 < h) :\\n    exp (radialWidth h) = 1 + h :=\\n  exp_log (by linarith only [hp])\\n\\ntheorem exp_radialWidth_lt_two {h : ℝ} (hp : 0 < h) (h8 : h ≤ 1 / 8) :\\n    exp (radialWidth h) < 2 := by\\n  rw [exp_radialWidth hp]\\n  linarith only [h8]\\n\\n/-- Every natural nonzero-support coordinate lies in the same finite\\nbox. This uses the complete positive product, not distinctness of primes. -/\\ntheorem profile_integer_box {N k r : ℕ} {logQ h : ℝ}\\n    {u : Fin (k + (2 + r)) → ℕ} (hN : 0 < N)\\n    (hp : 0 < h) (h8 : h ≤ 1 / 8)\\n    (hne : finPhysicalProfile logQ (N : ℝ) (radialWidth h)\\n      ((N : ℝ) ^ frozenLeafCutoffFloor) (fun i => (u i : ℝ)) ≠ 0) :\\n    ∀ i, u i ≤ 2 * N := by\\n  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN\\n  have hfloor := rpow_pos_of_pos hN0 frozenLeafCutoffFloor\\n  have hu := finPhysicalProfile_integer_pos hfloor hne\\n  have hprod : 0 < ∏ i, u i := Finset.prod_pos (fun i _ => hu i)\\n  have hcap := finPhysicalProfile_integer_product_lt hfloor hN0 (radialWidth_pos hp) hne\\n  have hlt : (∏ i, u i : ℕ) < 2 * N := by\\n    exact_mod_cast hcap.trans\\n      (mul_lt_mul_of_pos_right (exp_radialWidth_lt_two hp h8) hN0)\\n  intro i\\n  exact (Nat.le_of_dvd hprod (Finset.dvd_prod_of_mem u (mem_univ i))).trans hlt.le\\n\\ndef profileOuterTuples (N k r : ℕ) (logQ h : ℝ) :\\n    Finset (Fin (k + (2 + r)) → Fin (2 * N + 1)) :=\\n  (Part3.labelledPrimeTuples (k + (2 + r)) (2 * N)).filter (fun t =>\\n    finPhysicalProfile logQ (N : ℝ) (radialWidth h)\\n      ((N : ℝ) ^ frozenLeafCutoffFloor) (fun i => ((t i).val : ℝ)) ≠ 0 ∧\\n      (N : ℝ) < (Part3.labelledProduct t : ℝ))\\n\\ndef profileOuterMass (N k r : ℕ) (logQ h : ℝ) : ℝ :=\\n  ∑ t ∈ profileOuterTuples N k r logQ h,\\n    finPhysicalProfile logQ (N : ℝ) (radialWidth h)\\n      ((N : ℝ) ^ frozenLeafCutoffFloor) (fun i => ((t i).val : ℝ))\\n\\n/-- The Fin box enumerates every prime natural tuple on the nonzero\\nouter support, preserving its exact coordinates and order. -/\\ntheorem profile_outer_integer_enumeration {N k r : ℕ} {logQ h : ℝ}\\n    {u : Fin (k + (2 + r)) → ℕ} (hN : 0 < N)\\n    (hp : 0 < h) (h8 : h ≤ 1 / 8) (hprime : ∀ i, (u i).Prime)\\n    (hne : finPhysicalProfile logQ (N : ℝ) (radialWidth h)\\n      ((N : ℝ) ^ frozenLeafCutoffFloor) (fun i => (u i : ℝ)) ≠ 0)\\n    (houter : (N : ℝ) < ((∏ i, u i : ℕ) : ℝ)) :\\n    ∃ t ∈ profileOuterTuples N k r logQ h, ∀ i, (t i).val = u i := by\\n  have hbox := profile_integer_box hN hp h8 hne\\n  let t : Fin (k + (2 + r)) → Fin (2 * N + 1) :=\\n    fun i => ⟨u i, Nat.lt_succ_of_le (hbox i)⟩\\n  refine ⟨t, ?_, fun i => rfl⟩\\n  refine mem_filter.mpr ⟨?_, hne, houter⟩\\n  exact mem_filter.mpr ⟨mem_univ _, hprime⟩\\n\\ntheorem profile_outer_subset {N k r : ℕ} {logQ h : ℝ}\\n    (hN : 0 < N) (hp : 0 < h)\\n    (hcut : cut N ≤ (N : ℝ) ^ frozenLeafCutoffFloor / 2) :\\n    profileOuterTuples N k r logQ h ⊆\\n      bandTuples N (k + (2 + r)) (1 - 2 * h) (1 + 2 * h) := by\\n  intro t ht\\n  obtain ⟨hprime, hne, houter⟩ := mem_filter.mp ht\\n  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN\\n  obtain ⟨hfloor, hcap⟩ := finPhysicalProfile_nonzero_support\\n    (rpow_pos_of_pos hN0 frozenLeafCutoffFloor) hN0 (radialWidth_pos hp) hne\\n  have hcap' : (Part3.labelledProduct t : ℝ) < (1 + h) * (N : ℝ) := by\\n    simpa only [Part3.labelledProduct, Nat.cast_prod, exp_radialWidth hp] using hcap\\n  refine mem_filter.mpr ⟨hprime, (fun i => hcut.trans (hfloor i).le), ?_, ?_⟩\\n  · have hh : (1 - 2 * h) * (N : ℝ) ≤ (N : ℝ) := by\\n      nlinarith only [hp, hN0]\\n    exact hh.trans_lt houter\\n  · exact hcap'.le.trans\\n      (mul_le_mul_of_nonneg_right (by linarith only [hp]) hN0.le)\\n\\ntheorem profileOuterMass_le_card (N k r : ℕ) (logQ h : ℝ) :\\n    profileOuterMass N k r logQ h ≤ ((profileOuterTuples N k r logQ h).card : ℝ) := by\\n  calc\\n    _ ≤ ∑ _t ∈ profileOuterTuples N k r logQ h, (1 : ℝ) := by\\n      apply Finset.sum_le_sum\\n      intro t _\\n      exact (physicalProfile_bounds logQ (N : ℝ) (radialWidth h)\\n        ((N : ℝ) ^ frozenLeafCutoffFloor)\\n        (finToPhysical k r (fun i => ((t i).val : ℝ)))).2\\n    _ = _ := by simp\\n\\n/-- The fixed h and physical width are chosen before every scale,\\nlogQ and old/rough split. This pays only the radial exterior of one\\nambient profile with the original frozen rank ceiling. -/\\ntheorem absolute_profile_outer_payment {ε : ℝ} (he : 0 < ε) :\\n    ∃ h : ℝ, 0 < h ∧ h ≤ 1 / 8 ∧\\n      0 < radialWidth h ∧ radialWidth h ≤ 1 ∧\\n      ∀ᶠ N : ℕ in atTop, ∀ (k r : ℕ) (logQ : ℝ),\\n        k + 2 + r ≤ frozenSourceRankBound →\\n        P2FiniteMarkedGamma5RadialRoughMass.norm N *\\n          profileOuterMass N k r logQ h ≤ ε := by\\n  obtain ⟨h, hp, h8, H⟩ := absolute_radial_payment he\\n  refine ⟨h, hp, h8, radialWidth_pos hp, radialWidth_le_one hp h8, ?_⟩\\n  filter_upwards [H, eventually_cut_le_half_floor, eventually_gt_atTop (1 : ℕ)]\\n    with N hpaid hcut hlarge\\n  intro k r logQ hkr\\n  have hN : 0 < N := by omega\\n  have hcard : ((profileOuterTuples N k r logQ h).card : ℝ) ≤\\n      boundaryCount N (1 - 2 * h) (1 + 2 * h) := by\\n    apply (Nat.cast_le.mpr (Finset.card_le_card (profile_outer_subset hN hp hcut))).trans\\n    exact rank_card_le_boundaryCount N (k + (2 + r)) _ _ (by omega)\\n  have hnorm : 0 ≤ P2FiniteMarkedGamma5RadialRoughMass.norm N :=\\n    div_nonneg (log_nonneg (by exact_mod_cast hlarge.le)) (Nat.cast_nonneg _)\\n  exact (mul_le_mul_of_nonneg_left\\n    ((profileOuterMass_le_card N k r logQ h).trans hcard) hnorm).trans hpaid\\n\\nend\\nend ImbalancedChen.P2FiniteMarkedGamma5RadialProfileCollar\\n\",\"before_blob\":\"d8d7d976309d45fe71201e5fb09c488b125e3da9\",\"before_sha256\":\"c00f675bd56c1b75741687892396221e00782aaad52e8df079abd3592339bb64\"},{\"module\":\"ImbalancedChen.P2FiniteMarkedGamma5RadialNaturalMass\",\"blob\":\"5a22a4e7aeb47b39b7052e9a184703d577e5c112\",\"sha256\":\"4cb852104310b03c4c1941d997558d9997de9ba8fe4cd3f503f00308a9d2affc\",\"source\":\"import ImbalancedChen.P2FiniteMarkedGamma5RadialProfileCollar\\n\\n/-!\\nSOURCE ONLY / UNCOMPILED / ZERO NEW FORMAL CREDIT.\\n\\nThe complete natural-prime outer support of one existing Gamma5 ambient\\nprofile. The finite carrier is the coordinatewise natural-value image of\\nthe proved bounded enumerator. Its membership theorem identifies it with\\nall prime natural tuples on the original nonzero outer support.\\n\\nThe value map is injective, so the original profile sum is unchanged.\\nEvery coordinate, its order and repeated value are retained. This is a\\nsingle-ambient sum dictionary and payment, not an identification with all\\nold history marks or the manuscript's J.\\n-/\\nnamespace ImbalancedChen.P2FiniteMarkedGamma5RadialNaturalMass\\nnoncomputable section\\nopen Filter Finset Real\\nopen Part5OriginalH430FrozenRootRefinement (frozenLeafCutoffFloor)\\nopen P2FiniteMarkedGamma5ActualRank (frozenSourceRankBound)\\nopen P2FiniteMarkedGamma5EulerWordBudget (finPhysicalProfile)\\nopen P2FiniteMarkedGamma5RadialProfileCollar\\nopen scoped Classical Topology BigOperators\\n\\ndef tupleValues {N d : ℕ} (t : Fin d → Fin (2 * N + 1)) : Fin d → ℕ :=\\n  fun i => (t i).val\\n\\n/-- Taking natural values forgets no bounded-tuple coordinate. -/\\ntheorem tupleValues_injective (N d : ℕ) :\\n    Function.Injective (tupleValues (N := N) (d := d)) := by\\n  intro t s hts\\n  funext i\\n  apply Fin.ext\\n  exact congrFun hts i\\n\\ndef naturalOuterTuples (N k r : ℕ) (logQ h : ℝ) :\\n    Finset (Fin (k + (2 + r)) → ℕ) :=\\n  (profileOuterTuples N k r logQ h).image\\n    (tupleValues (N := N) (d := k + (2 + r)))\\n\\n/-- This finite carrier is exactly the full natural-prime outer support\\nunder the admitted positive width. The reverse implication uses the\\nexisting integer enumeration, not a new support or payment premise. -/\\ntheorem mem_naturalOuterTuples {N k r : ℕ} {logQ h : ℝ}\\n    {u : Fin (k + (2 + r)) → ℕ} (hN : 0 < N)\\n    (hp : 0 < h) (h8 : h ≤ 1 / 8) :\\n    u ∈ naturalOuterTuples N k r logQ h ↔\\n      (∀ i, (u i).Prime) ∧\\n        finPhysicalProfile logQ (N : ℝ) (radialWidth h)\\n          ((N : ℝ) ^ frozenLeafCutoffFloor) (fun i => (u i : ℝ)) ≠ 0 ∧\\n        (N : ℝ) < ((∏ i, u i : ℕ) : ℝ) := by\\n  constructor\\n  · intro hu\\n    obtain ⟨t, ht, rfl⟩ := mem_image.mp hu\\n    obtain ⟨hprime, hne, houter⟩ := mem_filter.mp ht\\n    exact ⟨(mem_filter.mp hprime).2, hne, houter⟩\\n  · rintro ⟨hprime, hne, houter⟩\\n    obtain ⟨t, ht, hvalues⟩ :=\\n      profile_outer_integer_enumeration hN hp h8 hprime hne houter\\n    refine mem_image.mpr ⟨t, ht, ?_⟩\\n    funext i\\n    exact hvalues i\\n\\ndef naturalOuterMass (N k r : ℕ) (logQ h : ℝ) : ℝ :=\\n  ∑ u ∈ naturalOuterTuples N k r logQ h,\\n    finPhysicalProfile logQ (N : ℝ) (radialWidth h)\\n      ((N : ℝ) ^ frozenLeafCutoffFloor) (fun i => (u i : ℝ))\\n\\n/-- The injective value map preserves the exact original weight and the\\nwhole finite sum. No product-image collapse or multiplicity factor is\\nintroduced. This equality itself needs no scale or width assumption. -/\\ntheorem naturalOuterMass_eq_profileOuterMass (N k r : ℕ) (logQ h : ℝ) :\\n    naturalOuterMass N k r logQ h = profileOuterMass N k r logQ h := by\\n  unfold naturalOuterMass naturalOuterTuples\\n  rw [Finset.sum_image\\n    (fun _ _ _ _ hts => tupleValues_injective N (k + (2 + r)) hts)] <;> rfl\\n\\n/-- The same fixed h pays the full natural-prime outer support of each\\none-ambient profile. The order of h, N, k, r and logQ is unchanged. -/\\ntheorem absolute_natural_outer_payment {ε : ℝ} (he : 0 < ε) :\\n    ∃ h : ℝ, 0 < h ∧ h ≤ 1 / 8 ∧\\n      0 < radialWidth h ∧ radialWidth h ≤ 1 ∧\\n      ∀ᶠ N : ℕ in atTop, ∀ (k r : ℕ) (logQ : ℝ),\\n        k + 2 + r ≤ frozenSourceRankBound →\\n        P2FiniteMarkedGamma5RadialRoughMass.norm N *\\n          naturalOuterMass N k r logQ h ≤ ε := by\\n  obtain ⟨h, hp, h8, hw, hw1, H⟩ := absolute_profile_outer_payment he\\n  refine ⟨h, hp, h8, hw, hw1, ?_⟩\\n  filter_upwards [H] with N hpaid\\n  intro k r logQ hkr\\n  rw [naturalOuterMass_eq_profileOuterMass]\\n  exact hpaid k r logQ hkr\\n\\nend\\nend ImbalancedChen.P2FiniteMarkedGamma5RadialNaturalMass\\n\",\"before_blob\":\"6d51477d988bd87c2d9ca90995b09bc65742fdfd\",\"before_sha256\":\"d87ea1f4a38e4cb4f1a9c6c642d4d6225ef5758b1d690c473a65f88ab72ac1c2\"}]"
AUDIT_TEXT="\"import Lean\\nopen Lean\\ndef p29ResolvedImports : IO Unit := do\\n  initSearchPath (← findSysroot)\\n  let names : Array Name := TARGET_MODULE_NAMES\\n  let env ← importModules (names.map fun n => { module := n }) {}\\n  for idx in [:env.header.modules.size] do\\n    let mod := env.header.modules[idx]!\\n    let data := env.header.moduleData[idx]!\\n    let p ← findOLean mod.module\\n    let mut parts : Array System.FilePath := #[p]\\n    if data.isModule then\\n      parts := parts.push (OLeanLevel.server.adjustFileName p)\\n      parts := parts.push (OLeanLevel.private.adjustFileName p)\\n    let irSig := p.withExtension \\\"ir.sig\\\"\\n    if ← irSig.pathExists then\\n      parts := parts.push irSig\\n      parts := parts.push (p.withExtension \\\"ir\\\")\\n    let partRows ← parts.mapM fun q => do\\n      let resolved ← IO.FS.realPath q\\n      return Json.mkObj [\\n        (\\\"path\\\", toJson q.toString),\\n        (\\\"resolved_path\\\", toJson resolved.toString)]\\n    IO.println (\\\"P29_ACTUAL_IMPORT \\\" ++ (Json.mkObj [\\n      (\\\"module\\\", toJson mod.module.toString),\\n      (\\\"is_module\\\", toJson data.isModule),\\n      (\\\"direct_imports\\\", toJson (data.imports.map fun i => i.module.toString)),\\n      (\\\"parts\\\", toJson partRows)]).compress)\\n#eval p29ResolvedImports\\n\""
import os,sys,pathlib,json,hashlib,subprocess,signal,time,datetime,uuid,re,shutil,importlib.util,traceback,tomllib,tarfile
P=pathlib.Path
INPUTS=json.loads(INPUT_TEXT)
AUDIT_TEMPLATE=json.loads(AUDIT_TEXT)
SUPPLY=P('/workspace/p29-native-supply-20261125')
oldroot=P('/workspace/p29-radial-20261125')
oldout=P('/workspace/p29-radial-verification-20261125')
three=oldout/'attempt-3-postnormal'
two=oldout/'fibre-tuple-attempt-3'
receive=P('/workspace/p29-p2-object-supply-20261125')
GUARD=P('/workspace/goldbach-formalization/docs/source-only/20261110-yellow-closure-10t/t01_remote_fifth_kernel/ci_runtime_guard.py')
RUNNER=P('/workspace/blue-build-tools/run_guarded.py')
OWNED=P('/workspace/blue-build-tools/validate_member_roots_owned.py')
PIN='leanprover/lean4:v4.33.0-rc1'
def sha(p):return hashlib.sha256(P(p).read_bytes()).hexdigest()
def stamp(p):
 s=P(p).stat();return [s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns]
def save(p,x):
 p=P(p);p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('x')as f:json.dump(x,f,indent=2);f.write('\n')
def utc():return datetime.datetime.now(datetime.timezone.utc).isoformat()
tools_expected={str(GUARD):'837f00360ca1364eb6adede88c05a72122acbbbbff2437c83026f2851836a877',str(RUNNER):'c202e53a319d9f30ee78db1582f53fe2104872f4ee749e1e5cac7d3ad5cfb526',str(OWNED):'ed4dc724deb5e2cb28cbd461014c59bed52c373f6b18613f07cf663e456d8201'}
assert all(sha(p)==h for p,h in tools_expected.items())
binding=SUPPLY/'supply-bindings/BINDING_RECEIPT.json'
assert sha(binding)=='bb7654da1ea6b5803ba812c3fe13a8212160061a252b84a4c31029208c3a5596'
assert json.loads(binding.read_text())['status']=='PASS_CURRENT_P1_EXISTING_NATIVE_SUPPLY'
assert sha(three/'VALIDATION_RESULTS.json')=='cfd743edf49b26a995a4d86f22c1d74f3440326cfeb5004d4843f27f00d4daf2'
three_receipt=json.loads((three/'VALIDATION_RESULTS.json').read_text())
assert sha(two/'VALIDATION_RESULTS.json')=='a7949e9f91e330d7c08ab67ab6c8112f2cc004c01509389d47de545fc6f2f3c8'
assert sha(two/'SOURCE_AND_OUTPUTS_AFTER.json')=='e974cd33e375cd76bce315aa97ecee6ff435b6a515ea89c3ff897ba99d57067a'
assert sha(two/'ACTUAL_IMPORT_PART_BINDINGS.json')=='a5504938ee9fd2e7efe28cb8d80d67cb6e2264e5934be3825f1c5522acb4c393'
two_receipt=json.loads((two/'VALIDATION_RESULTS.json').read_text())
assert three_receipt['result']=='PASS_THREE_EXACT_SOURCE_MODULES_NORMAL_STOCK_NAMED_KERNEL_FULL_OWNED'
assert two_receipt['result']=='PASS_TWO_EXACT_SOURCE_MODULES_NORMAL_STOCK_NAMED_KERNEL_FULL_OWNED'
assert {x['module']:x['sha256']for x in two_receipt['inputs']}=={
'ImbalancedChen.P2MarkedPrimeProductFibreCore':'ca2a53a58e6f6c858c513dbead63ae469c193f2b0760c2e0dd529144f53563bf',
'ImbalancedChen.P2FiniteMarkedGamma5RadialTupleCount':'20d878534ba9e3fea689a605759e6a349ff3efa675ce54cf7a4e3ca265ac50c2'}
received=json.loads((receive/'RECEPTION_RECEIPT.json').read_text())
assert received['sha256']=='c524f898ff7222d3a1173429e7bf4150f9f71272ba1ae5aa40a7f1bd0e4c4083'
assert sha(receive/'p2-exact-twelve-objects.tar.gz')==received['sha256']
invpath=receive/'contents/inventory.json'
assert sha(invpath)=='aa6465a6ccd1596a695305576933c655b7b9a7514fed559f608976752e1d9477'
p2_inventory=json.loads(invpath.read_text())
assert len(p2_inventory['modules'])==12
for name,row in p2_inventory['members'].items():
 p=receive/'contents'/name;assert p.stat().st_size==row['bytes']and sha(p)==row['sha256'],('Received member drift',name)
for row in INPUTS:assert hashlib.sha256(row['source'].encode()).hexdigest()==row['sha256']
accepted_old_config=json.loads("{\"lake-manifest.json\":{\"bytes\":3176,\"sha256\":\"0c1ed2f4476d4b54d5376b98606e861fd7ecc822ddf3977831f48469c83fc54b\"},\"lakefile.toml\":{\"bytes\":2632,\"sha256\":\"86b052b20a913c4527345da687a427d677c8922486e705f9c4bdb4e273606fef\"},\"lean-toolchain\":{\"bytes\":29,\"sha256\":\"62c2d9c0fc1ec4c67e151c11eff41ca004ef38e179cf9476c230406e6defedef\"}}")
for name,rec in accepted_old_config.items():
 assert (oldroot/name).stat().st_size==rec['bytes']and sha(oldroot/name)==rec['sha256'],('Accepted old workspace configuration drift',name)
assert sha(oldout/'CONFIGURATION_ADAPTATION.json')=='f0b3447bf787dd9914f5486e161221f7a669678eca444e6a6908375265b94621'
assert sha(oldout/'runtime-evidence/state.json')=='8af37ef442df0e4dc7fcebe1d937509b1d526e9ea0e1a99b648efd350a047e22'
accepted_policy=json.loads((oldout/'runtime-evidence/state.json').read_text())['policy']
root=P('/workspace/p29-radial-profile-20261125-pinbind-v4')
out=P('/workspace/p29-radial-profile-verification-20261125-pinbind-v4')
if root.exists()or out.exists():
 suffix=uuid.uuid4().hex[:8];root=P(str(root)+'-'+suffix);out=P(str(out)+'-'+suffix)
root.mkdir();out.mkdir();(out/'driver.py').write_text(SOURCE_TEXT)
mods=[x['module']for x in INPUTS]
oldmods=list(three_receipt['modules'])+list(two_receipt['modules'])
p2mods=sorted(p2_inventory['modules'])
assert len(oldmods)==len(set(oldmods))==5
assert not set(oldmods)&set(p2mods)
borrowedmods=oldmods+p2mods
cache_before={}
protected_outputs={}
knownparts={}
def register_part(path,identity,snapshot,authority):
 path=str(path);p=P(path);st=stamp(p)
 if st!=snapshot:assert sha(p)==identity['sha256'],('Accepted import drift',path)
 cache_before[path]=st
 row={'identity':{'path':path,'bytes':identity['bytes'],'sha256':identity['sha256']},'stat_snapshot':st,'authority':authority}
 for key in [path,str(p.resolve())]:
  if key in knownparts:assert knownparts[key]['identity']['sha256']==identity['sha256'],('Accepted aliases disagree',key)
  knownparts[key]=row
for row in json.loads((SUPPLY/'supply-bindings/IMPORT_PART_BINDINGS.json').read_text())['parts']:
 register_part(row['identity']['path'],row['identity'],row['current_stat_snapshot'],'accepted_native_twelve_import_part')
for prior in [three,two]:
 for row in json.loads((prior/'ACTUAL_IMPORT_PART_BINDINGS.json').read_text())['parts']:
  register_part(row['identity']['path'],row['identity'],row['stat_snapshot'],'accepted_p1_five_import_part')
for prior in [SUPPLY,three,two]:
 doc=json.loads((prior/'SOURCE_AND_OUTPUTS_AFTER.json').read_text())
 for path,row in doc.items():
  assert P(path).stat().st_size==row['bytes']and sha(path)==row['sha256'],('Accepted source/output drift',path)
  protected_outputs[path]=row;cache_before[path]=stamp(path)
borrows={}
lib=root/'.lake/build/lib/lean'
for module in oldmods:
 rel=module.replace('.','/')
 source=oldroot/(rel+'.lean')
 obj=oldroot/'.lake/build/lib/lean'/(rel+'.olean')
 assert str(source)in protected_outputs and str(obj)in protected_outputs
 dest=lib/(rel+'.olean');dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(obj,dest)
 assert sha(dest)==protected_outputs[str(obj)]['sha256']
 cache_before[str(dest)]=stamp(dest)
 borrows[module]={'module':module,'origin':'accepted_P1_three_or_two','source':str(source),'source_sha256':sha(source),'object':str(dest),'object_sha256':sha(dest),'object_bytes':dest.stat().st_size,'original_object':str(obj),'original_evidence':str(three if module in three_receipt['modules']else two),'original_facets_copied':['.olean'],'other_facets_created':False}
for module,row in p2_inventory['modules'].items():
 rel=module.replace('.','/')
 source=receive/'contents/sources'/(rel+'.lean')
 obj=receive/'contents'/row['facets']['.olean']['member']
 assert set(row['facets'])=={'.olean'}
 assert sha(source)==row['record']['source_sha256']and sha(obj)==row['record']['object_sha256']
 assert row['record']['exit_code']==0
 for dep,digest in row['record'].get('deps',{}).items():
  assert dep in p2_inventory['modules']and p2_inventory['modules'][dep]['record']['object_sha256']==digest,('P2 project dependency is not in exact packet',module,dep)
 dest=lib/(rel+'.olean');dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(obj,dest)
 assert sha(dest)==row['record']['object_sha256']
 cache_before[str(dest)]=stamp(dest);cache_before[str(source)]=stamp(source);cache_before[str(obj)]=stamp(obj)
 borrows[module]={'module':module,'origin':'exact_P2_direct_Lean_olean_packet','source':str(source),'source_sha256':sha(source),'object':str(dest),'object_sha256':sha(dest),'object_bytes':dest.stat().st_size,'original_object':row['record']['object'],'received_object':str(obj),'original_compile_record':row['record'],'original_facets_copied':['.olean'],'missing_original_facets':row['missing_adjacent_facets'],'other_facets_created':False}
save(out/'BORROWED_OBJECTS.json',{'module_count':len(borrows),'module_name_intersection':[],'constant_collision_check':'pending_real_importModules_load','objects':borrows})
old_toml=(oldroot/'lakefile.toml').read_text();old_config=tomllib.loads(old_toml)
assert old_config['lean_lib'][0]['name']=='ImbalancedChen' and sum(row.get('name')=='ImbalancedChen'for row in old_config['lean_lib'])==1
assert not any(k in old_config['lean_lib'][0]for k in ['roots','globs'])
decl=r'(?m)^(\[\[lean_lib\]\][ \t]*\nname[ \t]*=[ \t]*"ImbalancedChen"[ \t]*\n)'
scope='roots = '+json.dumps(mods)+'\nglobs = '+json.dumps(mods)+'\n'
new_toml,n=re.subn(decl,lambda m:m.group(1)+scope,old_toml)
assert n==1,'Unexpected library declaration; do not modify config heuristically'
new_config=tomllib.loads(new_toml)
compared=json.loads(json.dumps(new_config));compared['lean_lib'][0].pop('roots');compared['lean_lib'][0].pop('globs')
assert compared==old_config
(root/'lakefile.toml').write_text(new_toml)
for name in ['lake-manifest.json','lean-toolchain']:shutil.copyfile(oldroot/name,root/name)
assert (root/'lean-toolchain').read_text().strip()==PIN
config_before={str(root/name):sha(root/name)for name in ['lakefile.toml','lake-manifest.json','lean-toolchain']}
save(out/'CONFIGURATION_ADAPTATION.json',{'original_root':str(oldroot),'new_root':str(root),'original_lakefile_sha256':sha(oldroot/'lakefile.toml'),'new_lakefile_sha256':sha(root/'lakefile.toml'),'changes_only':{'lean_lib.roots':mods,'lean_lib.globs':mods},'all_other_options_semantically_unchanged':True,'borrowed_objects_in_unified_ImbalancedChen_namespace':True,'borrowed_sources_not_local_lake_targets':True,'borrowed_olean_only_true_facets':True,'original_lake_manifest_sha256':sha(oldroot/'lake-manifest.json'),'new_lake_manifest_sha256':sha(root/'lake-manifest.json')})
allowed_sources=set()
for row in INPUTS:
 p=root/(row['module'].replace('.','/')+'.lean');p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(row['source'].encode())
 allowed_sources.add(str(p.resolve()))
 save(out/'input-blobs'/(row['module']+'.json'),{k:v for k,v in row.items()if k!='source'})
runtime_parent=root/'runtime';runtime_parent.mkdir()
runtime_evidence=out/'runtime-evidence'
base_env=os.environ.copy()
for k in ['LEAN_SYSROOT','LEAN','LEAN_AR','LEAN_CC','LAKE','LAKE_HOME','LAKE_OVERRIDE_LEAN','LEAN_PATH','LEAN_SRC_PATH','P0_CI_GUARD_STATE','P0_COMPILER_SLOT_HELD','P0_COMPILER_SLOT_FD','P0_COMPILER_SLOT_TOOL']:base_env.pop(k,None)
base_env.update(LEAN_NUM_THREADS='2',ELAN_TOOLCHAIN=PIN,ELAN_HOME='/workspace/.elan',RUNNER_TEMP=str(runtime_parent),LEAN_ACTION_DIR='/workspace/blue-build-tools/lean-action',GITHUB_ENV=str(out/'runtime.env'),GITHUB_PATH=str(out/'runtime.path'))
base_env['PATH']='/workspace/.elan/bin:'+base_env.get('PATH','')
setup_cmd=['python3',str(GUARD),'setup','--evidence',str(runtime_evidence)]
with (out/'runtime-setup.log').open('xb')as f:r=subprocess.run(setup_cmd,cwd=root,env=base_env,stdout=f,stderr=subprocess.STDOUT)
save(out/'runtime-setup-process.json',{'command':setup_cmd,'cwd':str(root),'exit_code':r.returncode,'log_sha256':sha(out/'runtime-setup.log')})
assert r.returncode==0,'Original runtime guard setup failed'
state_path=runtime_evidence/'state.json';state=json.loads(state_path.read_text());guardlog=P(state['log'])
state_sha_before=sha(state_path)
assert state['policy']==accepted_policy,'Original runtime policy changed'
runprefix=['python3',str(RUNNER),'--state',str(state_path)]
runs=[]
def stage(label,command,stdin=None,allow_sources=(),allow_audit=False,timeout=900):
 initial=guardlog.stat().st_size;pos=initial;pending=b'';rows=[];bad=[];started=utc();t0=time.monotonic();last=t0
 log=out/(label+'.log')
 with log.open('xb')as f:
  proc=subprocess.Popen(command,cwd=root,env=base_env,stdin=subprocess.PIPE if stdin is not None else None,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
  if stdin is not None:proc.stdin.write(stdin);proc.stdin.close()
  while True:
   with guardlog.open('rb')as g:g.seek(pos);raw=g.read();pos+=len(raw)
   pending+=raw;lines=pending.split(b'\n');pending=lines.pop()
   for line in lines:
    if not line.strip():continue
    row=json.loads(line);rows.append(row)
    if row.get('tool')=='lean':
     args=row.get('input_args',[])
     if '--stdin'in args and not allow_audit:bad.append({'reason':'UNEXPECTED_STDIN_AUDIT','record':row})
     for a in args:
      if str(a).endswith('.lean'):
       q=P(a);q=q if q.is_absolute()else P(row['cwd'])/q
       if str(q.resolve())not in allow_sources and not(allow_audit and q.resolve().is_relative_to(out.resolve())):
        bad.append({'reason':'UNAUTHORIZED_SOURCE_REBUILD','record':row})
   code=proc.poll()
   if code is not None:break
   if bad or time.monotonic()-t0>timeout:
    os.killpg(proc.pid,signal.SIGTERM)
    try:proc.wait(timeout=10)
    except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);proc.wait()
    code=96 if bad else 124;break
   if time.monotonic()-last>=30:
    print(json.dumps({'stage':label,'root':str(root),'elapsed_seconds':round(time.monotonic()-t0,1),'forbidden_source_calls':len(bad)}),flush=True);last=time.monotonic()
   time.sleep(.2)
 if bad and code==0:code=96
 rec={'stage':label,'command':command,'cwd':str(root),'started_utc':started,'finished_utc':utc(),'exit_code':code,'guard_log_start':initial,'guard_log_end':pos,'guarded_commands':rows,'forbidden_source_calls':bad,'log_path':str(log),'log_sha256':sha(log)}
 if stdin is not None:rec['stdin_sha256']=hashlib.sha256(stdin).hexdigest()
 save(out/(label+'-process.json'),rec);runs.append(rec)
 print(json.dumps({'stage':label,'exit_code':code,'forbidden_source_calls':len(bad),'log_path':str(log)}),flush=True)
 if code:print(log.read_text()[-22000:],flush=True);raise RuntimeError('Gate failed: '+label)
 return rec

sys.dont_write_bytecode=True
spec=importlib.util.spec_from_file_location('p29_original_owned_auditor',OWNED)
auditor=importlib.util.module_from_spec(spec);spec.loader.exec_module(auditor)
def facet_of(module,path):
 name=module.rsplit('.',1)[-1];base=P(path).name
 assert base.startswith(name+'.'),('Unexpected artifact name',module,path)
 return base[len(name):]
LEAN_COMMIT='62eed1db4d67327ec8120be05f1a1b0847d74561'
TC=P('/workspace/toolchains/lean-4.33.0-rc1-linux').resolve()
TOOL_LIB=(TC/'lib/lean').resolve()
package_revisions={'mathlib': 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1', 'plausible': 'b1c4a69a7e247ab7df20460212001673d74f08c0', 'LeanSearchClient': '0498c7c070c143a3bf7379f4d99a2c63bb9d9715', 'importGraph': '18a90119a5d316358fde6c86e0ca24e59212e32c', 'proofwidgets': 'b1436dc749e722c9920036b52cdc43b3451d0b69', 'aesop': '57d3325be72a842920813bcb40f96a6f7393c185', 'Qq': 'ee41917ae11d38479fb8fb24745f7ca4bf0a784d', 'batteries': '41bd267b3f6b7252f6676af46d4ffc6783b64de9', 'Cli': 'da07ca808b6718cb2aed14dba154e5a08b8f8ecf'}
package_bindings={}
release_binding={}
def bind_release():
 rec=stage('pinned-lean-version',runprefix+['lake','env','lean','--version'])
 ver=(out/'pinned-lean-version.log').read_text().strip()
 assert 'version 4.33.0-rc1,'in ver and 'commit '+LEAN_COMMIT+','in ver,ver
 stage('pinned-lean-prefix',runprefix+['lake','env','lean','--print-prefix'])
 prefix=(out/'pinned-lean-prefix.log').read_text().splitlines()
 shadow=P(state['shadow'])
 assert prefix and P(prefix[-1])==shadow and state['environment']['LEAN_SYSROOT']==str(shadow),('Guard-reported shadow prefix mismatch',prefix,shadow)
 assert P(state['realbin'])==(TC/'bin').resolve() and (shadow/'lib').is_symlink() and (shadow/'lib/lean').resolve()==TOOL_LIB,('Wrong actual guarded library carrier',shadow,TC)
 release_binding['guarded_shadow']={'prefix':str(shadow),'release_lib_from_shadow':str((shadow/'lib/lean').resolve()),'state_sha256':state_sha_before}
 for name,shadow_name in [('lean','lean-runtime'),('lake','lake')]:
  p=TC/'bin'/name;q=shadow/'bin'/shadow_name
  assert p.is_file()and q.is_file()and not q.is_symlink()
  digest=sha(p);assert digest==sha(q)==state['runtime_sha256'][str(p)]==state['runtime_sha256'][str(q)],('Pinned guard binary copies differ',p,q)
  entry={'path':str(p),'bytes':p.stat().st_size,'sha256':digest,'shadow_binary':str(q)}
  cache_before[str(p)]=stamp(p);cache_before[str(q)]=stamp(q);release_binding[name]=entry
 release_binding.update(pin=PIN,lean_commit=LEAN_COMMIT,sysroot=str(TC),lib_root=str(TOOL_LIB),
   version_log_sha256=rec['log_sha256'],workspace_toolchain_sha256=sha(root/'lean-toolchain'))
 save(out/'PINNED_TOOLCHAIN.json',release_binding)
def bind_fresh_part(module,p):
 facet=facet_of(module,p)
 assert facet in {'.olean','.olean.server','.olean.private','.ir.sig','.ir'},('Unsupported import facet',module,p)
 expected=P(module.replace('.','/')+facet)
 if p.is_relative_to(TOOL_LIB):
  assert p.relative_to(TOOL_LIB)==expected,('Wrong pinned release member',module,p,expected)
  return 'fresh_actual_pinned_lean_release_part',{'provider':'leanprover/lean4','revision':LEAN_COMMIT,'provider_identity':'PINNED_TOOLCHAIN.json','relative_artifact':str(expected)}
 assert p.parts[-len(expected.parts):]==expected.parts,('Module-to-path mismatch',module,p)
 lib=p.parents[len(expected.parts)-1]
 assert lib.parts[-4:]==('.lake','build','lib','lean'),('Unbound package output root',module,p)
 pkg=lib.parents[3]
 # Only a package with the pinned manifest identity and an actual checkout
 # at its own top level can introduce a previously unbound external object.
 if str(pkg) not in package_bindings:
  def git(*args):
   return subprocess.check_output(['git','-C',str(pkg),*args],text=True).strip()
  name=pkg.name
  assert name in package_revisions,('Unknown package',module,p,pkg)
  head=git('rev-parse','HEAD')
  assert P(git('rev-parse','--show-toplevel')).resolve()==pkg and head==package_revisions[name],('Wrong pinned checkout',pkg,head)
  package_bindings[str(pkg)]={'name':name,'revision':head,'checkout':str(pkg),'lib_root':str(lib),'workspace_manifest_sha256':sha(root/'lake-manifest.json')}
 return 'fresh_actual_pinned_package_part',{**package_bindings[str(pkg)],'relative_artifact':str(expected)}
def compile_audit_text(module_names):
 names='#['+', '.join(chr(96)+m for m in module_names)+']'
 return AUDIT_TEMPLATE.replace('TARGET_MODULE_NAMES',names).encode()
def load_actual_imports(label,module_names,production=None):
 production=production or {}
 code=compile_audit_text(module_names)
 (out/(label+'.lean')).write_bytes(code)
 process=stage(label,runprefix+['lake','env','lean','-DmaxRecDepth=100000','-DmaxHeartbeats=4000000','--stdin'],stdin=code,allow_audit=True)
 rows=[]
 for line in (out/(label+'.log')).read_text().splitlines():
  if line.startswith('P29_ACTUAL_IMPORT '):rows.append(json.loads(line[len('P29_ACTUAL_IMPORT '):]))
 assert rows and len(rows)==len({r['module']for r in rows})
 actual={r['module']:r for r in rows}
 assert set(module_names)<=set(actual)
 for module in actual:
  if module.startswith('ImbalancedChen.'):
   assert module in borrows or module in mods,('Unregistered project dependency',module)
 known_owned={str(P(row['object']).resolve()):(module,row)for module,row in borrows.items()}
 parts=[];counts={};hashes={}
 for row in rows:
  row['part_identities']=[]
  for pathrow in row['parts']:
   path=pathrow['resolved_path'];p=P(path);st=stamp(p);authority=None;original=None;provider_binding=None
   if path in known_owned:
    module,old=known_owned[path];assert module==row['module']
    assert st[2]==old['object_bytes']and sha(path)==old['object_sha256']
    identity={'path':path,'bytes':st[2],'sha256':old['object_sha256']}
    authority=old['origin'];original=old['original_object']
   elif path in production or str(p)in production:
    expected=production.get(path,production.get(str(p)));assert sha(p)==expected['sha256']
    identity={'path':path,**expected};authority='current_new_consumer_normal_output'
   elif path in knownparts or pathrow['path']in knownparts:
    old=knownparts.get(path,knownparts.get(pathrow['path']))
    op=old['identity']['path'];assert stamp(op)==cache_before[op],('Accepted input changed while audit ran',op)
    if st!=old['stat_snapshot']:assert sha(path)==old['identity']['sha256']
    identity={'path':path,'bytes':st[2],'sha256':old['identity']['sha256']};authority=old['authority'];original=op
   elif path in protected_outputs:
    expected=protected_outputs[path];assert sha(path)==expected['sha256']
    identity={'path':path,**expected};authority='accepted_native_owned_output'
   else:
    module=row['module']
    authority,provider_binding=bind_fresh_part(module,p)
    identity={'path':path,'bytes':st[2],'sha256':sha(path)}
   assert stamp(path)==st
   cache_before[path]=st
   record={'module':row['module'],'facet':facet_of(row['module'],path),'identity':identity,'requested_path':pathrow['path'],'stat_snapshot':st,'authority':authority}
   if provider_binding:record['provider_binding']=provider_binding
   if original:record['prior_bound_path']=original
   parts.append(record);row['part_identities'].append(record)
   counts[authority]=counts.get(authority,0)+1
   hashes[(row['module'],record['facet'])]=identity['sha256']
 data={'schema':'p29_current_actual_Lean_findOLean_import_graph_v1','roots':module_names,'module_count':len(rows),'part_count':len(parts),'counts':counts,'actual_modules':rows,'parts':parts,'loading_api':'Lean.importModules at private level; Lean.findOLean; default fallback facets as defined in pinned Lean.Environment.readModuleDataPartsOfMod/readIRPartsOfMod','constant_collision_check':'PASS importing all listed roots in one Environment'}
 save(out/(label+'-bindings.json'),data)
 return data,actual,hashes
def source_outputs():
 result={}
 for row in INPUTS:
  rel=row['module'].replace('.','/')
  paths=[root/(rel+'.lean')]+[root/'.lake/build/lib/lean'/(rel+s)for s in ['.olean','.ilean','.trace']]+[root/'.lake/build/ir'/(rel+s)for s in ['.c','.setup.json']]
  for p in paths:result[str(p)]={'bytes':p.stat().st_size,'sha256':sha(p)}
 return result
def named_kernel(label,module_names):
 rec=stage(label,runprefix+['lake','env','leanchecker','--verbose',*module_names])
 replayed=[l.removeprefix('replaying ')for l in (out/(label+'.log')).read_text().splitlines()if l.startswith('replaying ')]
 assert len(replayed)==len(set(replayed))==len(module_names)and set(replayed)==set(module_names)
 return rec
def full_owned(label,module_names):
 code=auditor.make_audit_code(module_names).encode();(out/(label+'.lean')).write_bytes(code)
 rec=stage(label,runprefix+['lake','env','lean','-DmaxRecDepth=100000','-DmaxHeartbeats=4000000','--stdin'],stdin=code,allow_audit=True)
 decls,inventory,axioms=auditor.read_audit((out/(label+'.log')).read_text(),module_names,rec['exit_code'])
 save(out/(label+'-DECLARATION_TYPES_AXIOMS.json'),decls)
 save(out/(label+'-INVENTORY_NAME_SET_CHECK.json'),inventory)
 return rec,decls,inventory,axioms

try:
 stage('runtime-initial-audit',runprefix+['python3',str(GUARD),'audit','--state',str(state_path),'--probe'])
 bind_release()
 before,actual,hashes=load_actual_imports('borrowed-actual-imports',borrowedmods)
 drift=[];p1comparisons=[];affected=[]
 for module in oldmods:
  setup=oldroot/'.lake/build/ir'/(module.replace('.','/')+'.setup.json')
  original=json.loads(setup.read_text());assert original['name']==module
  disagreements=[];project_deps=[]
  for dep,groups in original['importArts'].items():
   if dep.startswith('ImbalancedChen.'):project_deps.append(dep)
   for group in groups:
    for path in group:
     assert path in knownparts or path in protected_outputs,('Missing accepted P1 original input binding',module,dep,path)
     expected=protected_outputs[path]['sha256']if path in protected_outputs else knownparts[path]['identity']['sha256']
     facet=facet_of(dep,path)
     observed=hashes.get((dep,facet))
     if observed!=expected:disagreements.append({'import_module':dep,'facet':facet,'original_path':path,'expected_sha256':expected,'current_sha256':observed})
  row={'module':module,'original_setup_path':str(setup),'original_setup_sha256':sha(setup),'project_imports':project_deps,'overlap_with_P2_modules':sorted(set(project_deps)&set(p2mods)),'disagreements':disagreements}
  p1comparisons.append(row)
  if disagreements:affected.append(module);drift.extend([{'owner':module,**d}for d in disagreements])
 save(out/'P1_FIVE_IMPORT_COMPARISON.json',{'modules':p1comparisons,'affected_modules':affected,'drift':drift,'all_original_facet_bytes_preserved':not drift})
 for module in p2mods:
  rec=p2_inventory['modules'][module]['record']
  for dep,h in rec.get('deps',{}).items():
   assert hashes.get((dep,'.olean'))==h,('Current P2 project import differs from original producer',module,dep)
  projimports=[x for x in actual[module]['direct_imports']if x.startswith('ImbalancedChen.')]
  assert set(projimports)==set(rec.get('deps',{})),('P2 direct project import set differs from source/producer',module,projimports)
 supply_mods=p2mods+affected
 supply_kernel=named_kernel('borrowed-named-kernel',supply_mods)
 supply_owned,supply_decls,supply_inventory,supply_axioms=full_owned('borrowed-full-owned',supply_mods)
 for module,row in borrows.items():assert sha(row['object'])==row['object_sha256']
 supply_receipt={'schema':'p29_P2_exact_objects_current_P1_carrier_qualification_v1','result':'PASS_CURRENT_P1_RESOLVED_INPUTS_NAMED_KERNEL_FULL_OWNED_ZERO_SOURCE_REBUILD','original_P2_export_job':'e90d8d7e7720478ead08403a1d45d2d6','original_packet_blob':'45cb5e4272907279bd0fe0d13c3169995ab3889b','original_packet_sha256':received['sha256'],'original_inventory_sha256':sha(invpath),'original_producer_facets':['.olean'],'original_standard_Mathlib_part_hashes_not_recorded':True,'old_and_current_standard_Mathlib_byte_equality_claim':False,'borrowed_objects':borrows,'P2_modules_requalified':p2mods,'P1_old_modules_with_changed_actual_inputs_requalified':affected,'current_input_bindings_sha256':sha(out/'borrowed-actual-imports-bindings.json'),'original_P1_comparison_sha256':sha(out/'P1_FIVE_IMPORT_COMPARISON.json'),'kernel':supply_kernel,'owned':supply_owned,'owned_declarations':len(supply_decls),'owned_declaration_counts':supply_inventory['module_counts'],'observed_axioms':supply_axioms,'all_owned_private_generated_types_universes':True,'source_compilations':0,'new_mathematical_theorem_credit':0,'scope_note':'Original exact proof objects are requalified under the explicitly bound current P1 carrier. This does not invent absent old producer trace/setup, or claim byte equality of unrecorded original standard Mathlib parts.'}
 save(out/'P2_CURRENT_P1_QUALIFICATION.json',supply_receipt)
 print(json.dumps({'stage':'P2-current-P1-supply-qualified','modules':len(p2mods),'additional_P1_affected_modules':affected,'owned':len(supply_decls),'receipt':str(out/'P2_CURRENT_P1_QUALIFICATION.json'),'receipt_sha256':sha(out/'P2_CURRENT_P1_QUALIFICATION.json'),'source_recompilations':0}),flush=True)
 normal=stage('normal-build',runprefix+['lake','build',*['+'+m+':olean'for m in mods]],allow_sources=allowed_sources)
 production=source_outputs();save(out/'SOURCE_AND_OUTPUTS_AFTER_NORMAL.json',production)
 after,actual_after,hashes_after=load_actual_imports('consumer-actual-imports',mods,production)
 setup_matches=[]
 for module in mods:
  path=root/'.lake/build/ir'/(module.replace('.','/')+'.setup.json')
  setup=json.loads(path.read_text());assert setup['name']==module
  checked=0
  for dep,groups in setup['importArts'].items():
   for group in groups:
    for p in group:
     assert hashes_after.get((dep,facet_of(dep,p)))==sha(p),('Lake actual importArts override differs from probed loader carrier',module,dep,p)
     checked+=1
  setup_matches.append({'module':module,'setup_path':str(path),'setup_sha256':sha(path),'explicit_setup_artifact_count':checked,'explicit_parts_match_current_resolver':True,'unlisted_external_imports_bound_via_actual_loader_graph':True})
 save(out/'CONSUMER_SETUP_IMPORT_MATCH.json',setup_matches)
 kernel=named_kernel('named-kernel',mods)
 owned,decls,inventory,axioms=full_owned('full-owned',mods)
 stock=stage('final-stock',runprefix+['lake','--no-build','build',*['+'+m+':olean'for m in mods]])
 assert not any(r.get('tool')=='lean'and('--stdin'in r.get('input_args',[])or any(str(a).endswith('.lean')for a in r.get('input_args',[])))for r in stock['guarded_commands'])
 stage('runtime-final-audit',runprefix+['python3',str(GUARD),'audit','--state',str(state_path),'--probe','--require-source'])
 final=source_outputs();assert final==production
 assert sha(state_path)==state_sha_before
 assert {p:sha(p)for p in config_before}==config_before
 assert all(sha(oldroot/name)==rec['sha256']for name,rec in accepted_old_config.items())
 assert all(sha(p)==h for p,h in tools_expected.items())
 assert all(sha(p)==r['sha256']for p,r in protected_outputs.items())
 changed=[p for p,s in cache_before.items()if not P(p).is_file()or stamp(p)!=s]
 assert not changed,('Accepted or received cache changed',changed[:20])
 for m,r in borrows.items():assert sha(r['object'])==r['object_sha256']
 save(out/'SOURCE_AND_OUTPUTS_AFTER.json',final)
 result={'schema':'p29_profile_natural_normal_stock_named_kernel_full_owned_v1','result':'PASS_TWO_NEW_CONSUMERS_NORMAL_STOCK_NAMED_KERNEL_FULL_OWNED','root':str(root),'evidence':str(out),'modules':mods,'inputs':[{k:v for k,v in row.items()if k!='source'}for row in INPUTS],'normal':normal,'kernel':kernel,'owned':owned,'stock':stock,'owned_declarations':len(decls),'owned_declaration_counts':inventory['module_counts'],'observed_axioms':axioms,'full_owned_private_generated_ast_universes':True,'source_and_outputs_unchanged_after_normal':True,'monitored_parts_unchanged':len(cache_before),'runtime_policy':state['policy'],'original_audited_tools_unchanged':tools_expected,'native_twelve_receipt_sha256':sha(binding),'original_three_receipt_sha256':sha(three/'VALIDATION_RESULTS.json'),'original_fibre_tuple_receipt_sha256':sha(two/'VALIDATION_RESULTS.json'),'P2_current_P1_supply_qualification_sha256':sha(out/'P2_CURRENT_P1_QUALIFICATION.json'),'actual_import_bindings_sha256':sha(out/'consumer-actual-imports-bindings.json'),'consumer_setup_import_match_sha256':sha(out/'CONSUMER_SETUP_IMPORT_MATCH.json'),'recompiled_old_project_or_native_sources':0,'all_import_replay_claim':False,'scope_note':'These are the original single fixed-split ambient profile outer mass and the exact natural tuple sum dictionary. No whole-history aggregation, original J identification, additive-prime test, or moving-family PP estimate is claimed.'}
 save(out/'VALIDATION_RESULTS.json',result)
 print(json.dumps({k:result[k]for k in ['result','root','evidence','modules','owned_declarations','owned_declaration_counts','observed_axioms','monitored_parts_unchanged','actual_import_bindings_sha256']}),flush=True)
 print(json.dumps({'validation_results_sha256':sha(out/'VALIDATION_RESULTS.json'),'source_outputs_sha256':sha(out/'SOURCE_AND_OUTPUTS_AFTER.json'),'declarations_sha256':sha(out/'full-owned-DECLARATION_TYPES_AXIOMS.json'),'inventory_sha256':sha(out/'full-owned-INVENTORY_NAME_SET_CHECK.json')}),flush=True)
except Exception as e:
 failure={'schema':'p29_profile_natural_gate_failure_v1','root':str(root),'evidence':str(out),'error':str(e),'traceback':traceback.format_exc(),'completed_stages':[r['stage']for r in runs],'borrowed_cache_changed':[p for p,s in cache_before.items()if not P(p).is_file()or stamp(p)!=s]}
 save(out/'FAILURE.json',failure)
 print(json.dumps(failure),flush=True)
 raise
if 'result' in globals() and result.get('result')=='PASS_TWO_NEW_CONSUMERS_NORMAL_STOCK_NAMED_KERNEL_FULL_OWNED':
 import base64
 export=out/'portable';export.mkdir()
 take=[out/'VALIDATION_RESULTS.json',out/'SOURCE_AND_OUTPUTS_AFTER.json',out/'full-owned-DECLARATION_TYPES_AXIOMS.json',out/'full-owned-INVENTORY_NAME_SET_CHECK.json',out/'borrowed-full-owned-DECLARATION_TYPES_AXIOMS.json',out/'borrowed-full-owned-INVENTORY_NAME_SET_CHECK.json',out/'P2_CURRENT_P1_QUALIFICATION.json',out/'P1_FIVE_IMPORT_COMPARISON.json',out/'CONSUMER_SETUP_IMPORT_MATCH.json',out/'CONFIGURATION_ADAPTATION.json',out/'PINNED_TOOLCHAIN.json',out/'BORROWED_OBJECTS.json']
 take+=sorted(out.glob('*-process.json'))+[out/'runtime-evidence/state.json',guardlog]
 entries={'config/'+name:root/name for name in ['lakefile.toml','lake-manifest.json','lean-toolchain']}
 for path in final:
  p=P(path);entries['project/'+str(p.relative_to(root))]=p
 for p in take:
  name=str(p.relative_to(out))if p.is_relative_to(out)else 'runtime-evidence/actual-guard-log.jsonl'
  entries['evidence/'+name]=p
 portable=export/'PROFILE_NATURAL_REUSABLE_OBJECTS_AND_ORIGINAL_AUDITS.tar.xz'
 def pack(destination,members):
  with tarfile.open(destination,'w:xz',preset=3)as tar:
   for k,v in sorted(members.items()):tar.add(v,arcname=k,recursive=False)
 member_inventory={name:{'bytes':p.stat().st_size,'sha256':sha(p)}for name,p in entries.items()}
 save(export/'MEMBERS.json',member_inventory);entries['MEMBERS.json']=export/'MEMBERS.json'
 pack(portable,entries)
 complete=export/'PROFILE_NATURAL_COMPLETE_EVIDENCE.tar.xz'
 complete_entries={'evidence/'+str(p.relative_to(out)):p for p in out.rglob('*')if p.is_file()and export not in p.parents}
 complete_entries.update({k:v for k,v in entries.items()if k.startswith(('project/','config/'))})
 pack(complete,complete_entries)
 sent=0
 for p in [portable,complete]:
  emit=(sent+p.stat().st_size)<=5600000
  print('P29_ARCHIVE '+json.dumps({'name':p.name,'path':str(p),'bytes':p.stat().st_size,'sha256':sha(p),'emitted':emit,'files':len(entries)if p==portable else len(complete_entries)}),flush=True)
  if emit:
   print('P29_DATA '+p.name+' '+base64.b64encode(p.read_bytes()).decode(),flush=True);sent+=p.stat().st_size
