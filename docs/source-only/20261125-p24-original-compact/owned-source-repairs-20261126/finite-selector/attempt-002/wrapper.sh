set -euo pipefail
cd /workspace/p2-4-compact-proof-20261125
export PYTHONDONTWRITEBYTECODE=1
export GIT_OPTIONAL_LOCKS=0
exec 9<.lake/p2-private/p24-migration.lock
flock -n 9
python3 -B - <<'P24_SELECTOR_LIST_REC_02'
import hashlib, json, os, pathlib, signal, subprocess, sys, time
root=pathlib.Path("/workspace/p2-4-compact-proof-20261125")
out=pathlib.Path("/workspace/p24-finite-selector-list-rec-20261126/attempt-002")
payload=json.loads(r'''{"candidate":"import ImbalancedChen.ActualThirdOriginalSixTentOrdinaryMassCeil\n\n/-!\nSOURCEONLY / UNCOMPILED / HOLD_ELABORATION / OPEN30.\nThe import is the frozen 20261024w AllBranches-V2 ordinary supplier,\nSHA256 0aefb001448b56e64e227e71dfb71a84167b45ea309007d054102fe455b79eb5.\n\nThis is the original BELOW-mu minorant selector, including the initial B\ncandidate. It maximizes the sum of the TWO EXACT PLANE RANGE endpoints,\nretaining the FIRST candidate on equal scores. It does not minimize OLD\nchord values, and it does not apply mean_upper residual/low tests before\nchoosing the plane. The final theorem supplies the existing analytic V2\nbound when the selected candidate is one of the ordinary tent branches.\nThe B winner and the other mean_upper dispatch branches are separate.\n-/\nnamespace ImbalancedChen.OriginalThirdP4AOrdinaryFiniteSelectorSourceOnly\nnoncomputable section\nopen Set MeasureTheory\nopen OriginalThirdBoxMomentsSourceOnly OriginalThirdSixTentCandidatesSourceOnly\nopen OriginalThirdLiteralTentSelectorGuardBridgeSourceOnly\nopen OriginalThirdSixTentRoundedConsumerSourceOnly\nopen OriginalThirdSixTentOrdinaryMassCeilSourceOnly\nopen OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly\nopen OriginalThirdPositiveLogSourceOnly OriginalThirdCompactPartitionSourceOnly\nopen OriginalU2StoredNodeBlockDataSourceOnly OriginalU2StoredNodeBlockCheckerSourceOnly\nopen OriginalU2StoredQueryLookupSourceOnly\n\n/-- The seed B is really present before the original six-loop candidates. -/\ninductive Candidate where\n  | base\n  | tent (sum : TentSum) (side : TentSide)\n\ndef sourceSums : List TentSum := [.x,.y,.xy,.xz,.yz,.xyz]\n\ndef rawSum (s : TentSum) (v : Fin 3 → ℤ) : ℤ :=\n  literalTentX s*v 0+literalTentY s*v 1+literalTentZ s*v 2\n\ndef deltaNumerator (D : ℤ) (s : TentSum) (v : Fin 3 → ℤ) : ℤ :=\n  -50*D+256*rawSum s v\n\n/-- This if/elif is evaluated before the root filter and before mean_upper. -/\ndef sourcePair (lo hi : Fin 3 → ℤ) (D : ℤ) (s : TentSum) : List Candidate :=\n  if deltaNumerator D s hi≤0 then [.tent s .rise]\n  else if 0≤deltaNumerator D s lo then [.tent s .fall] else []\n\ndef sourceRaw (lo hi : Fin 3 → ℤ) (D : ℤ) : List Candidate :=\n  .base :: sourceSums.flatMap (sourcePair lo hi D)\n\ndef branchTest (lo hi : Fin 3 → ℤ) (D : ℤ) (s : TentSum) (k : TentSide) : Prop :=\n  match k with\n  | .rise => deltaNumerator D s hi≤0\n  | .fall => ¬deltaNumerator D s hi≤0 ∧ 0≤deltaNumerator D s lo\n\n/-- Integer form of the original plane_range(c,p)[1] <= T filter. -/\ndef rootTest (lo hi : Fin 3 → ℤ) (D T : ℤ) : Candidate → Prop\n  | .base => 153*D-96*lo 2≤256*T\n  | .tent s .rise => D+rawSum s hi≤2*T\n  | .tent s .fall => 57*D-96*rawSum s lo≤64*T\n\ndef sourceCandidates (lo hi : Fin 3 → ℤ) (D T : ℤ) : List Candidate := by\n  classical\n  exact (sourceRaw lo hi D).filter (fun p => decide (rootTest lo hi D T p))\n\n/-- Literal Fraction endpoints of plane_range; these are not OLD endpoints. -/\ndef rangeLow (lo hi : Fin 3 → ℤ) (D : ℤ) : Candidate → ℚ\n  | .base => ((153*D-96*hi 2:ℤ):ℚ)/256\n  | .tent s .rise => ((D+rawSum s lo:ℤ):ℚ)/2\n  | .tent s .fall => ((57*D-96*rawSum s hi:ℤ):ℚ)/64\n\ndef rangeHigh (lo hi : Fin 3 → ℤ) (D : ℤ) : Candidate → ℚ\n  | .base => ((153*D-96*lo 2:ℤ):ℚ)/256\n  | .tent s .rise => ((D+rawSum s hi:ℤ):ℚ)/2\n  | .tent s .fall => ((57*D-96*rawSum s lo:ℤ):ℚ)/64\n\ndef sourceScore (lo hi : Fin 3 → ℤ) (D : ℤ) (p : Candidate) : ℚ :=\n  rangeLow lo hi D p+rangeHigh lo hi D p\n\ntheorem rootTest_iff_rangeHigh (lo hi : Fin 3 → ℤ) (D T : ℤ) (p : Candidate) :\n    rootTest lo hi D T p ↔ rangeHigh lo hi D p≤(T:ℚ) := by\n  cases p with\n  | base =>\n      simp only [rootTest,rangeHigh]\n      rw [div_le_iff₀ (by norm_num : (0:ℚ)<256)]\n      constructor <;> intro h <;> norm_cast at * <;> omega\n  | tent s k =>\n      cases k <;> simp only [rootTest,rangeHigh] <;>\n        rw [div_le_iff₀ (by norm_num)] <;>\n        constructor <;> intro h <;> norm_cast at * <;> omega\n\ntheorem tent_mem_sourcePair_iff (lo hi : Fin 3 → ℤ) (D : ℤ)\n    (s : TentSum) (k : TentSide) :\n    Candidate.tent s k∈sourcePair lo hi D s ↔ branchTest lo hi D s k := by\n  classical\n  cases k <;> unfold sourcePair branchTest <;>\n    split_ifs <;> simp_all\n\ntheorem tent_mem_sourceRaw_iff (lo hi : Fin 3 → ℤ) (D : ℤ)\n    (s : TentSum) (k : TentSide) :\n    Candidate.tent s k∈sourceRaw lo hi D ↔ branchTest lo hi D s k := by\n  classical\n  have hsum : s∈sourceSums := by cases s <;> simp [sourceSums]\n  constructor\n  · intro h\n    have hm : Candidate.tent s k∈sourceSums.flatMap (sourcePair lo hi D) := by\n      simpa only [sourceRaw,List.mem_cons,reduceCtorEq,false_or] using h\n    obtain ⟨s\u0027,hs\u0027,hp⟩ := List.mem_flatMap.mp hm\n    unfold sourcePair at hp\n    split_ifs at hp with hu hl\n    · have he : s=s\u0027 ∧ k=TentSide.rise := by\n        simpa only [List.mem_singleton,Candidate.tent.injEq] using hp\n      rcases he with ⟨rfl,rfl⟩\n      exact hu\n    · have he : s=s\u0027 ∧ k=TentSide.fall := by\n        simpa only [List.mem_singleton,Candidate.tent.injEq] using hp\n      rcases he with ⟨rfl,rfl⟩\n      exact ⟨hu,hl⟩\n    · simp only [List.not_mem_nil] at hp\n  · intro h\n    apply List.mem_cons_of_mem\n    exact List.mem_flatMap.mpr ⟨s,hsum,(tent_mem_sourcePair_iff lo hi D s k).mpr h⟩\n\ntheorem tent_mem_candidates_iff (lo hi : Fin 3 → ℤ) (D T : ℤ)\n    (s : TentSum) (k : TentSide) :\n    Candidate.tent s k∈sourceCandidates lo hi D T ↔\n      branchTest lo hi D s k ∧ rootTest lo hi D T (.tent s k) := by\n  classical\n  simp only [sourceCandidates,List.mem_filter,decide_eq_true_eq,\n    tent_mem_sourceRaw_iff]\n\n/-- The <= test is deliberately in this direction: the earlier head wins ties. -/\ndef firstMax {α : Type*} (score : α → ℚ) : List α → Option α :=\n  List.rec (motive := fun _ => Option α) none (fun a _ previous =>\n    match previous with\n    | none => some a\n    | some b => if score b≤score a then some a else some b)\n\ntheorem firstMax_none_iff {α : Type*} (score : α → ℚ) (xs : List α) :\n    firstMax score xs=none ↔ xs=[] := by\n  cases xs with\n  | nil => simp [firstMax]\n  | cons a as =>\n      cases ht : firstMax score as with\n      | none => simp [firstMax,ht]\n      | some b =>\n          by_cases hb : score b≤score a <;> simp [firstMax,ht,hb]\n\ntheorem firstMax_mem_max {α : Type*} (score : α → ℚ) (xs : List α) (p : α)\n    (h : firstMax score xs=some p) :\n    p∈xs ∧ ∀ q∈xs, score q≤score p := by\n  induction xs generalizing p with\n  | nil => simp [firstMax] at h\n  | cons a as ih =>\n      cases ht : firstMax score as with\n      | none =>\n          have he := (firstMax_none_iff score as).mp ht\n          subst as\n          have hp : a=p := by simpa only [firstMax,Option.some.injEq] using h\n          subst p\n          simp\n      | some b =>\n          have hb := ih b ht\n          by_cases hba : score b≤score a\n          · have hp : a=p := by simpa only [firstMax,ht,if_pos hba,Option.some.injEq] using h\n            subst p\n            refine ⟨by simp,?_⟩\n            intro q hq\n            rcases List.mem_cons.mp hq with rfl | hq\n            · exact le_rfl\n            · exact (hb.2 q hq).trans hba\n          · have hp : b=p := by simpa only [firstMax,ht,if_neg hba,Option.some.injEq] using h\n            subst p\n            refine ⟨List.mem_cons_of_mem a hb.1,?_⟩\n            intro q hq\n            rcases List.mem_cons.mp hq with rfl | hq\n            · exact (lt_of_not_ge hba).le\n            · exact hb.2 q hq\n\n/-- A complete first-tie certificate: every earlier entry has STRICTLY smaller\nscore; entries after the winner may tie. No index/rank assumption is supplied. -/\ntheorem firstMax_priority {α : Type*} (score : α → ℚ) (xs : List α) (p : α)\n    (h : firstMax score xs=some p) :\n    ∃ before after, xs=before++p::after ∧\n      (∀ q∈before, score q<score p) ∧ (∀ q∈after, score q≤score p) := by\n  induction xs generalizing p with\n  | nil => simp [firstMax] at h\n  | cons a as ih =>\n      cases ht : firstMax score as with\n      | none =>\n          have he := (firstMax_none_iff score as).mp ht\n          subst as\n          have hp : a=p := by simpa only [firstMax,Option.some.injEq] using h\n          subst p\n          exact ⟨[],[],rfl,by simp,by simp⟩\n      | some b =>\n          have hb := firstMax_mem_max score as b ht\n          by_cases hba : score b≤score a\n          · have hp : a=p := by simpa only [firstMax,ht,if_pos hba,Option.some.injEq] using h\n            subst p\n            refine ⟨[],as,rfl,by simp,?_⟩\n            exact fun q hq => (hb.2 q hq).trans hba\n          · have hp : b=p := by simpa only [firstMax,ht,if_neg hba,Option.some.injEq] using h\n            subst p\n            obtain ⟨before,after,he,hl,hr⟩ := ih b ht\n            refine ⟨a::before,after,?_,?_,hr⟩\n            · simp only [List.cons_append,he]\n            · intro q hq\n              rcases List.mem_cons.mp hq with rfl | hq\n              · exact lt_of_not_ge hba\n              · exact hl q hq\n\ndef originalMinorant (lo hi : Fin 3 → ℤ) (D T : ℤ) : Option Candidate :=\n  firstMax (sourceScore lo hi D) (sourceCandidates lo hi D T)\n\ntheorem selected_tent_guards (lo hi : Fin 3 → ℤ) (D T : ℤ)\n    (s : TentSum) (k : TentSide)\n    (hselected : originalMinorant lo hi D T=some (.tent s k)) :\n    branchTest lo hi D s k ∧ rootTest lo hi D T (.tent s k) := by\n  exact (tent_mem_candidates_iff lo hi D T s k).mp\n    (firstMax_mem_max _ _ _ hselected).1\n\ntheorem selected_base_root (lo hi : Fin 3 → ℤ) (D T : ℤ)\n    (hselected : originalMinorant lo hi D T=some .base) :\n    153*D-96*lo 2≤256*T := by\n  classical\n  have hm := (firstMax_mem_max _ _ _ hselected).1\n  have hr := (List.mem_filter.mp hm).2\n  let : Decidable (rootTest lo hi D T .base) := Classical.propDecidable _\n  have hroot : rootTest lo hi D T .base := of_decide_eq_true hr\n  exact hroot\n\ntheorem selected_is_original_first_max (lo hi : Fin 3 → ℤ) (D T : ℤ)\n    (p : Candidate) (hselected : originalMinorant lo hi D T=some p) :\n    ∃ before after, sourceCandidates lo hi D T=before++p::after ∧\n      (∀ q∈before, sourceScore lo hi D q<sourceScore lo hi D p) ∧\n      (∀ q∈after, sourceScore lo hi D q≤sourceScore lo hi D p) := by\n  exact firstMax_priority _ _ _ hselected\n\n/-- No residual/OLD-domain test is hidden in this characterization. -/\ntheorem originalMinorant_none_iff (lo hi : Fin 3 → ℤ) (D T : ℤ) :\n    originalMinorant lo hi D T=none ↔\n      ∀ p∈sourceRaw lo hi D, ¬rootTest lo hi D T p := by\n  classical\n  rw [originalMinorant,firstMax_none_iff]\n  simp [sourceCandidates,List.filter_eq_nil_iff]\n\n/-- The original seed B passes the root filter on the actual positive boxes.\nThus a missing below-mu minorant is impossible even if every tent is absent. -/\ntheorem originalMinorant_ne_none (lo hi : Fin 3 → ℤ) (D T : ℤ)\n    (hD : D=48000*2^24) (hT : T=481573208064) (hz : 0≤lo 2) :\n    originalMinorant lo hi D T≠none := by\n  intro hn\n  have he := (originalMinorant_none_iff lo hi D T).mp hn .base (by simp [sourceRaw])\n  apply he\n  change 153*D-96*lo 2≤256*T\n  have hc : 153*D≤256*T := by rw [hD,hT]; norm_num\n  omega\n\n/-- Actual selected-tent leaf estimate, with all finite branch/root selection\npremises discharged from the executable source selector. The selected plane\u0027s\nresidual and low>=2 remain genuine POST-selection mean_upper guards. -/\ntheorem original_finite_selected_tent_integer_upper\n    (table : CheckedBlockTable)\n    (s : TentSum) (k : TentSide) (lo hi : Fin 3 → ℤ)\n    (D T : ℤ) (a b : BoxPoint)\n    (hD : D=48000*2^24) (hT : T=481573208064)\n    (haBind : ∀ i, a i=(lo i:ℝ)/(D:ℝ))\n    (hbBind : ∀ i, b i=(hi i:ℝ)/(D:ℝ))\n    (ha : ∀ i, 0<a i) (hab : ∀ i, a i<b i)\n    (hcut : (1:ℝ)/100≤a 2) (hyx : b 1≤a 0) (hzy : b 2≤a 1)\n    (hmu : b 0≤VariableEnvelope.mu)\n    (hfull : b 0+b 1+3*b 2≤thirdPrefixTheta)\n    (hselected : originalMinorant lo hi D T=some (.tent s k))\n    (hres : match k with\n      | .rise => 0<D+(literalTentX s-2)*hi 0+(literalTentY s-2)*hi 1\n      | .fall => 0<57*D+(-96*literalTentX s-64)*hi 0+(-96*literalTentY s-64)*hi 1)\n    (hlow : 2≤(literalTentEndpoint s k hi D:ℝ))\n    (hratio : ∀ i : Fin 2, b i.castSucc/a i.castSucc≤2)\n    (hpositive : ∀ i : Fin 2, 0<(originalLnUnit (b i.castSucc/a i.castSucc)).lo) :\n    (∫ t in compactRegion ∩ Icc a b, compactKernel t)≤\n      value (literalOrdinaryUpper lo hi (meanHigh\n        (ordinaryTentWeight s k a b (literalTentEndpoint s k hi D)\n          (literalTentEndpoint s k lo D)).lo\n        (ordinaryTentWeight s k a b (literalTentEndpoint s k hi D)\n          (literalTentEndpoint s k lo D)).hi\n        (readQueryLo160 (assembledRead table.blocks)\n          (literalTentEndpoint s k hi D).num ((literalTentEndpoint s k hi D).den:ℤ))\n        (readQueryLo160 (assembledRead table.blocks)\n          (literalTentEndpoint s k lo D).num ((literalTentEndpoint s k lo D).den:ℤ))\n        (readQueryHi160 (assembledRead table.blocks) (ordinaryNew a b).hi P160))) := by\n  have hg := selected_tent_guards lo hi D T s k hselected\n  have hbranch := hg.1\n  have hroot := hg.2\n  dsimp [branchTest,deltaNumerator,rawSum] at hbranch\n  dsimp [rootTest,rawSum] at hroot\n  refine original_selected_tent_stored_integer_upper table s k lo hi D T a b\n    (literalTentEndpoint s k hi D) (literalTentEndpoint s k lo D) _ _ _\n    hD hT haBind hbBind ha hab hcut hyx hzy hmu hfull ?_ ?_ ?_\n    rfl rfl hlow hratio hpositive rfl rfl rfl\n  · cases k <;> exact hbranch\n  · cases k with\n    | rise => simpa only [add_assoc] using hroot\n    | fall => exact hroot\n  · cases k <;> exact hres\n\n/-- Exact integer box() behavior when mean_upper is absent. -/\ndef applyOptionalMean (high : ℤ) : Option ℤ → ℤ\n  | none => high\n  | some j => min high j\n\ntheorem applyOptionalMean_none (high : ℤ) : applyOptionalMean high none=high := by\n  rfl\n\ntheorem applyOptionalMean_some (high j : ℤ) :\n    value (applyOptionalMean high (some j))=min (value high) (value j) := by\n  exact value_min high j\n\n/-- max0 and the original OUT-minus-OLD structure commute with the outer min. -/\ntheorem min_max0_sub (high out old : ℤ) (hh : 0≤high) :\n    min high (max 0 (out-old))=max 0 (min high (out-old)) := by\n  by_cases hd : 0≤out-old\n  · rw [max_eq_right hd,max_eq_right (le_min hh hd)]\n  · have hdn : out-old≤0 := le_of_not_ge hd\n    rw [max_eq_left hdn,min_eq_right hh,min_eq_right (hdn.trans hh),max_eq_left hdn]\n\ntheorem max0_sub_antitone (out old₁ old₂ : ℤ) (h : old₁≤old₂) :\n    max 0 (out-old₂)≤max 0 (out-old₁) := by\n  exact max_le_max le_rfl (sub_le_sub_left h out)\n\n/-- This comparison is arithmetic only. Source plane score is not OLD chord\nscore, so this identity must not be substituted for originalMinorant. -/\ntheorem min_max0_sub_eq (out old₁ old₂ : ℤ) :\n    min (max 0 (out-old₁)) (max 0 (out-old₂))=\n      max 0 (out-max old₁ old₂) := by\n  rcases le_total old₁ old₂ with h | h\n  · rw [max_eq_right h,min_eq_right (max0_sub_antitone out old₁ old₂ h)]\n  · rw [max_eq_left h,min_eq_left (max0_sub_antitone out old₂ old₁ h)]\n\nend\nend ImbalancedChen.OriginalThirdP4AOrdinaryFiniteSelectorSourceOnly\n","oldBlock":"def firstMax {α : Type*} (score : α → ℚ) : List α → Option α\n  | [] => none\n  | a::as => match firstMax score as with\n    | none => some a\n    | some b => if score b≤score a then some a else some b","newBlock":"def firstMax {α : Type*} (score : α → ℚ) : List α → Option α :=\n  List.rec (motive := fun _ => Option α) none (fun a _ previous =>\n    match previous with\n    | none => some a\n    | some b => if score b≤score a then some a else some b)"}''')
target="ImbalancedChen.ActualThirdOriginalP4AOrdinaryFiniteSelector"
pin="6e616f4e0372555f7a78bcdba3e198d0e277eec8"
snapshot_path=pathlib.Path("/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/qualifications/attempt-003/EXTERNAL_SNAPSHOT.json")
snapshot_expected="ad4386f160e7d59bcaca2820fb9123434d05593595b266ca24fa742e48367d27"
native_context_expected="71451bbb4a755fb5ec8744663121d0630ba5afd3d5774f7d0ec7931d9d387e90"
expected={
 "verification/part2/run_winner9_private_checks.py":"164bc271d8806ed45ebdd71c8f394c4706d7cfdaf4a121b633d738e094bad7ac",
 "verification/part2/run_winner9_private_audit.py":"571b6137da5e1a1cf9ec9020e03b4f881bc4f0f3f36eae0aa9d62a3a5c0939d5",
 "verification/part2/winner9_private_audit_template.lean":"2975fe381dfc6de3b297a67bcc9db9dd064bcad37a0b45ee13bc1fcd957ee85b",
 "verification/part2/winner9_external_snapshot.py":"a57b658beef42ebfe75ccb09d84f7f1ee7252c289f267396063c93ae5e0bbedf",
 "verification/part2/inspect_winner9_owner_native.py":"9460e319b2f247b4deb6c4c12ad7b59732bfde939f5dc68e541b4a5714aed90d",
}
def digest(path):
 with pathlib.Path(path).open("rb") as f: return hashlib.file_digest(f,"sha256").hexdigest()
def jd(value):
 return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(",",":")).encode()).hexdigest()
def info(path):
 return {"path":str(path),"bytes":pathlib.Path(path).stat().st_size,"sha256":digest(path)}
def write(name,value):
 (out/name).write_text(json.dumps(value,ensure_ascii=False,indent=2)+"\n")
def check_source():
 assert subprocess.check_output(["git","rev-parse","HEAD"],cwd=root,text=True).strip()==pin
 assert not subprocess.check_output(["git","status","--porcelain","--untracked-files=no"],cwd=root,text=True).strip()
 assert {n:digest(root/n) for n in expected}==expected

check_source()
sys.path.insert(0,str(root/"verification/part2"))
from run_winner9_private_audit import LEAN, LEANCHECKER, MATHLIB, PIN, project_nodes, snapshot, verify_compilation
from winner9_external_snapshot import ExternalSnapshot, mark_project_nodes
assert PIN=="e4c91783ca8e6a7c693ae624ade32fd22d4e43c1"
runtime_expected={LEAN:"e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550",LEANCHECKER:"ed46f21c763051c26f89481096cbaaf5db9665d674d602e3daf3391613ba0e6a"}
assert {n:digest(n) for n in runtime_expected}==runtime_expected
assert subprocess.check_output(["git","rev-parse","HEAD"],cwd=MATHLIB,text=True).strip()==PIN
assert digest(snapshot_path)==snapshot_expected
nodes=project_nodes(root,target)
lib=root/".lake/p2-private/lib"
registry=root/".lake/p2-private/records.json"
external=ExternalSnapshot(snapshot_path,lean=LEAN,mathlib_pin=PIN,project_lib=lib)
native_before=external.binding()
assert native_before["snapshot_sha256"]==snapshot_expected
assert native_before["context_signature"]==native_context_expected
assert native_before["verification_helper_sha256"]==expected["verification/part2/winner9_external_snapshot.py"]
mark_project_nodes(nodes,set(external.modules))
toolchain={"lean_version":subprocess.check_output([LEAN,"--version"],text=True).strip(),"lean_binary_sha256":runtime_expected[LEAN],"mathlib_commit":PIN}
records=json.loads(registry.read_text())
registry_before=digest(registry)
before=snapshot(root,lib,nodes,toolchain,external)
verify_compilation(records,nodes,before)
source=pathlib.Path(nodes[target]["source"]).read_bytes()
assert hashlib.sha1(b"blob "+str(len(source)).encode()+b"\0"+source).hexdigest()=="df536731c2b67dd2129522f1a96b9470cd405f4f"
import base64,gzip
assert len(source)>0 and hashlib.sha256(source).hexdigest()=="f16eb47f1407020aa844a2ba8f5fe1b24e1b3c5181a094aa8e61a5e2d18344e1"
candidate=payload["candidate"].encode("utf-8")
old_block=payload["oldBlock"].encode("utf-8")
new_block=payload["newBlock"].encode("utf-8")
assert source.count(old_block)==1
assert candidate==source.replace(old_block,new_block,1)
assert candidate.replace(new_block,old_block,1)==source
assert hashlib.sha256(candidate).hexdigest()=="a13913bf01cc70dc6d0417c87cb73cf749cfed4961338b62c059ac019446d839"
out.mkdir(parents=True,exist_ok=False)
candidate_module="FiniteSelectorCandidate"
relative=pathlib.Path(candidate_module+".lean")
candidate_path=out/relative
candidate_path.parent.mkdir(parents=True,exist_ok=True)
candidate_path.write_bytes(candidate)
(out/"FiniteSelector-original.lean").write_bytes(source)
candidate_lib=out/"lib"
candidate_object=candidate_lib/relative.with_suffix(".olean")
candidate_object.parent.mkdir(parents=True)
template=(root/"verification/part2/winner9_private_audit_template.lean").read_bytes()
original_target=b"ImbalancedChen.P2Winner9FiniteMomentKernel"
assert template.count(original_target)==2
audit=template.replace(original_target,candidate_module.encode())
assert audit.replace(candidate_module.encode(),original_target)==template
(out/"OriginalAuditTemplate.lean").write_bytes(template)
(out/"Audit.lean").write_bytes(audit)
write("before-snapshot.json",before)
original_env=external.environment(os.environ)
env=dict(original_env)
env["LEAN_PATH"]=str(candidate_lib)+os.pathsep+original_env["LEAN_PATH"]
flags=["-t0","-j1","-M11264","-DwarningAsError=true","-DmaxRecDepth=50000","-DmaxHeartbeats=40000000"]
receipt={
 "purpose":"isolated firstMax List.rec candidate compile replay original full-owned audit",
 "source_pin":pin,"module":target,"candidate_module":candidate_module,"canonical_closure_size":len(nodes),
 "original_source":info(out/"FiniteSelector-original.lean"),"candidate_source":info(candidate_path),
 "sole_source_change":"firstMax named recursion to direct List.rec; identical branches and score b<=score a tie direction",
 "inverse_source_bytes_equal":True,"all_other_definitions_and_complete_theorem_blocks_unchanged":True,
 "template":info(out/"OriginalAuditTemplate.lean"),"audit_source":info(out/"Audit.lean"),
 "template_target_replacements":2,"template_other_bytes_equal":True,
 "canonical_source_and_object":before["project"][target],
 "registry_sha256_before":registry_before,"native_before":native_before,
 "runtime_sha256":runtime_expected,"verifier_sha256":expected,
 "before_snapshot_sha256":jd(before),"lean_path":env["LEAN_PATH"],"lean_sysroot":env["LEAN_SYSROOT"],
 "environment_only_delta":"isolated candidate lib prepended; original ExternalSnapshot environment retained after it",
 "production_changed":False,"registry_writeback":False,"native_qualification_run":False,
 "canonical_credit":False,"full_P2_credit":False,"stages":[],
}
write("receipt.json",receipt)
print("P24_SELECTOR_CANDIDATE_BEGIN "+json.dumps({k:receipt[k] for k in ["source_pin","module","candidate_module","canonical_closure_size","candidate_source","original_source","template","audit_source","registry_sha256_before"]},ensure_ascii=False),flush=True)
deadline=time.monotonic()+760
def run_stage(name,command):
 log_path=out/(name+".log")
 started=time.monotonic()
 left=deadline-started
 if left<=0:raise RuntimeError("Isolated diagnostic soft deadline exceeded")
 timed_out=False
 with log_path.open("wb") as log:
  proc=subprocess.Popen(command,cwd=out,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
  try:rc=proc.wait(timeout=left)
  except subprocess.TimeoutExpired:
   timed_out=True
   os.killpg(proc.pid,signal.SIGKILL);proc.wait();rc=124
 stage={"stage":name,"command":command,"exit_code":rc,"timed_out":timed_out,"seconds":time.monotonic()-started,"log":info(log_path)}
 receipt["stages"].append(stage)
 write("receipt.json",receipt)
 print("P24_SELECTOR_CANDIDATE_STAGE "+json.dumps(stage,ensure_ascii=False),flush=True)
 return rc
compile_rc=run_stage("compile",[LEAN]+flags+["-o",str(candidate_object),str(relative)])
rc=compile_rc
if compile_rc==0:
 receipt["candidate_object_before"]=info(candidate_object)
 write("receipt.json",receipt)
 replay_rc=run_stage("replay",[LEANCHECKER,"--verbose",candidate_module])
 audit_rc=run_stage("audit",[LEAN]+flags+["Audit.lean"])
 rc=replay_rc if replay_rc!=0 else audit_rc
 receipt["candidate_object_after"]=info(candidate_object)
 receipt["candidate_object_unchanged"]=receipt["candidate_object_before"]==receipt["candidate_object_after"]
 receipt["all_three_stages_passed"]=replay_rc==0 and audit_rc==0
postchecks={}
errors=[]
def perform(name,action):
 try:action();postchecks[name]=True
 except Exception as e:postchecks[name]=False;errors.append({"check":name,"error":type(e).__name__+": "+str(e)})
perform("source_pin_tracked_clean_original_verifiers",check_source)
def check_runtime():
 assert {n:digest(n) for n in runtime_expected}==runtime_expected
 assert subprocess.check_output(["git","rev-parse","HEAD"],cwd=MATHLIB,text=True).strip()==PIN
perform("runtime_bytes_and_pin_unchanged",check_runtime)
def check_native():assert external.verify()==native_before
perform("native_binding_unchanged",check_native)
def check_bindings():
 after=snapshot(root,lib,nodes,toolchain,external)
 write("after-snapshot.json",after)
 assert after==before
 assert digest(registry)==registry_before
 verify_compilation(json.loads(registry.read_text()),nodes,after)
perform("canonical_closure_source_objects_and_registry_unchanged",check_bindings)
def check_isolated_inputs():
 assert candidate_path.read_bytes()==candidate
 assert (out/"OriginalAuditTemplate.lean").read_bytes()==template
 assert (out/"Audit.lean").read_bytes()==audit
 if compile_rc==0:assert receipt["candidate_object_unchanged"]
perform("isolated_inputs_and_object_unchanged",check_isolated_inputs)
if compile_rc==0 and receipt.get("all_three_stages_passed"):
 def check_audit():
  lines=(out/"audit.log").read_text().splitlines()
  inventory=[json.loads(x[len("P0_QUEUE_INVENTORY "):]) for x in lines if x.startswith("P0_QUEUE_INVENTORY ")]
  declarations=[json.loads(x[len("P0_QUEUE_DECL "):]) for x in lines if x.startswith("P0_QUEUE_DECL ")]
  assert len(inventory)==1
  names=[d["name"] for d in declarations]
  assert names and len(names)==len(set(names))
  assert sorted(names)==sorted(inventory[0]["serialized"])==sorted(inventory[0]["environment"])
  assert all(not d["unsafe"] and not d["partial"] and not d["axiom"] and set(d["axioms"])<={"propext","Classical.choice","Quot.sound"} and "⋯" not in d["type"] for d in declarations)
  receipt["audit_summary"]={"owned_count":len(names),"exact_inventory":True,"all_safe_nonpartial_nonaxiom":True,"allowed_axioms_only":True,"axiom_union":sorted({a for d in declarations for a in d["axioms"]}),"firstMax_declarations":[d for d in declarations if ".firstMax" in d["name"]]}
 perform("original_full_owned_audit_exact_inventory_and_rules",check_audit)
receipt["postchecks"]=postchecks
receipt["postcheck_errors"]=errors
receipt["registry_sha256_after"]=digest(registry)
receipt["wrapper_exit_code"]=rc if rc!=0 else (125 if errors else 0)
write("receipt.json",receipt)
print("P24_SELECTOR_CANDIDATE_DONE "+json.dumps({"receipt":info(out/"receipt.json"),"stages":receipt["stages"],"postchecks":postchecks,"postcheck_errors":errors,"wrapper_exit_code":receipt["wrapper_exit_code"],"audit_summary":receipt.get("audit_summary")},ensure_ascii=False),flush=True)
for name in ["receipt.json"]+[s["stage"]+".log" for s in receipt["stages"]]:
 raw=(out/name).read_bytes()
 compressed=gzip.compress(raw,mtime=0)
 packet={"file":info(out/name),"encoding":"base64(gzip(raw))","gzip_bytes":len(compressed),"gzip_sha256":hashlib.sha256(compressed).hexdigest(),"data":base64.b64encode(compressed).decode()}
 print("P24_SELECTOR_EVIDENCE "+json.dumps(packet),flush=True)
raise SystemExit(receipt["wrapper_exit_code"])

P24_SELECTOR_LIST_REC_02
