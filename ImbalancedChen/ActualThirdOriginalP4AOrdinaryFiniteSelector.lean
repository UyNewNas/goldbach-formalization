import ImbalancedChen.ActualThirdOriginalSixTentOrdinaryMassCeil

/-!
SOURCEONLY / UNCOMPILED / HOLD_ELABORATION / OPEN30.
The import is the frozen 20261024w AllBranches-V2 ordinary supplier,
SHA256 0aefb001448b56e64e227e71dfb71a84167b45ea309007d054102fe455b79eb5.

This is the original BELOW-mu minorant selector, including the initial B
candidate. It maximizes the sum of the TWO EXACT PLANE RANGE endpoints,
retaining the FIRST candidate on equal scores. It does not minimize OLD
chord values, and it does not apply mean_upper residual/low tests before
choosing the plane. The final theorem supplies the existing analytic V2
bound when the selected candidate is one of the ordinary tent branches.
The B winner and the other mean_upper dispatch branches are separate.
-/
namespace ImbalancedChen.OriginalThirdP4AOrdinaryFiniteSelectorSourceOnly
noncomputable section
open Set MeasureTheory
open OriginalThirdBoxMomentsSourceOnly OriginalThirdSixTentCandidatesSourceOnly
open OriginalThirdLiteralTentSelectorGuardBridgeSourceOnly
open OriginalThirdSixTentRoundedConsumerSourceOnly
open OriginalThirdSixTentOrdinaryMassCeilSourceOnly
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open OriginalThirdPositiveLogSourceOnly OriginalThirdCompactPartitionSourceOnly
open OriginalU2StoredNodeBlockDataSourceOnly OriginalU2StoredNodeBlockCheckerSourceOnly
open OriginalU2StoredQueryLookupSourceOnly

/-- The seed B is really present before the original six-loop candidates. -/
inductive Candidate where
  | base
  | tent (sum : TentSum) (side : TentSide)

def sourceSums : List TentSum := [.x,.y,.xy,.xz,.yz,.xyz]

def rawSum (s : TentSum) (v : Fin 3 → ℤ) : ℤ :=
  literalTentX s*v 0+literalTentY s*v 1+literalTentZ s*v 2

def deltaNumerator (D : ℤ) (s : TentSum) (v : Fin 3 → ℤ) : ℤ :=
  -50*D+256*rawSum s v

/-- This if/elif is evaluated before the root filter and before mean_upper. -/
def sourcePair (lo hi : Fin 3 → ℤ) (D : ℤ) (s : TentSum) : List Candidate :=
  if deltaNumerator D s hi≤0 then [.tent s .rise]
  else if 0≤deltaNumerator D s lo then [.tent s .fall] else []

def sourceRaw (lo hi : Fin 3 → ℤ) (D : ℤ) : List Candidate :=
  .base :: sourceSums.flatMap (sourcePair lo hi D)

def branchTest (lo hi : Fin 3 → ℤ) (D : ℤ) (s : TentSum) (k : TentSide) : Prop :=
  match k with
  | .rise => deltaNumerator D s hi≤0
  | .fall => ¬deltaNumerator D s hi≤0 ∧ 0≤deltaNumerator D s lo

/-- Integer form of the original plane_range(c,p)[1] <= T filter. -/
def rootTest (lo hi : Fin 3 → ℤ) (D T : ℤ) : Candidate → Prop
  | .base => 153*D-96*lo 2≤256*T
  | .tent s .rise => D+rawSum s hi≤2*T
  | .tent s .fall => 57*D-96*rawSum s lo≤64*T

def sourceCandidates (lo hi : Fin 3 → ℤ) (D T : ℤ) : List Candidate := by
  classical
  exact (sourceRaw lo hi D).filter (fun p => decide (rootTest lo hi D T p))

/-- Literal Fraction endpoints of plane_range; these are not OLD endpoints. -/
def rangeLow (lo hi : Fin 3 → ℤ) (D : ℤ) : Candidate → ℚ
  | .base => ((153*D-96*hi 2:ℤ):ℚ)/256
  | .tent s .rise => ((D+rawSum s lo:ℤ):ℚ)/2
  | .tent s .fall => ((57*D-96*rawSum s hi:ℤ):ℚ)/64

def rangeHigh (lo hi : Fin 3 → ℤ) (D : ℤ) : Candidate → ℚ
  | .base => ((153*D-96*lo 2:ℤ):ℚ)/256
  | .tent s .rise => ((D+rawSum s hi:ℤ):ℚ)/2
  | .tent s .fall => ((57*D-96*rawSum s lo:ℤ):ℚ)/64

def sourceScore (lo hi : Fin 3 → ℤ) (D : ℤ) (p : Candidate) : ℚ :=
  rangeLow lo hi D p+rangeHigh lo hi D p

theorem rootTest_iff_rangeHigh (lo hi : Fin 3 → ℤ) (D T : ℤ) (p : Candidate) :
    rootTest lo hi D T p ↔ rangeHigh lo hi D p≤(T:ℚ) := by
  cases p with
  | base =>
      simp only [rootTest,rangeHigh]
      rw [div_le_iff₀ (by norm_num : (0:ℚ)<256)]
      constructor <;> intro h <;> norm_cast at * <;> omega
  | tent s k =>
      cases k <;> simp only [rootTest,rangeHigh] <;>
        rw [div_le_iff₀ (by norm_num)] <;>
        constructor <;> intro h <;> norm_cast at * <;> omega

theorem tent_mem_sourcePair_iff (lo hi : Fin 3 → ℤ) (D : ℤ)
    (s : TentSum) (k : TentSide) :
    Candidate.tent s k∈sourcePair lo hi D s ↔ branchTest lo hi D s k := by
  classical
  cases k <;> unfold sourcePair branchTest <;>
    split_ifs <;> simp_all

theorem tent_mem_sourceRaw_iff (lo hi : Fin 3 → ℤ) (D : ℤ)
    (s : TentSum) (k : TentSide) :
    Candidate.tent s k∈sourceRaw lo hi D ↔ branchTest lo hi D s k := by
  classical
  have hsum : s∈sourceSums := by cases s <;> simp [sourceSums]
  constructor
  · intro h
    have hm : Candidate.tent s k∈sourceSums.flatMap (sourcePair lo hi D) := by
      simpa only [sourceRaw,List.mem_cons,reduceCtorEq,false_or] using h
    obtain ⟨s',hs',hp⟩ := List.mem_flatMap.mp hm
    unfold sourcePair at hp
    split_ifs at hp with hu hl
    · have he : s=s' ∧ k=TentSide.rise := by
        simpa only [List.mem_singleton,Candidate.tent.injEq] using hp
      rcases he with ⟨rfl,rfl⟩
      exact hu
    · have he : s=s' ∧ k=TentSide.fall := by
        simpa only [List.mem_singleton,Candidate.tent.injEq] using hp
      rcases he with ⟨rfl,rfl⟩
      exact ⟨hu,hl⟩
    · simp only [List.not_mem_nil] at hp
  · intro h
    apply List.mem_cons_of_mem
    exact List.mem_flatMap.mpr ⟨s,hsum,(tent_mem_sourcePair_iff lo hi D s k).mpr h⟩

theorem tent_mem_candidates_iff (lo hi : Fin 3 → ℤ) (D T : ℤ)
    (s : TentSum) (k : TentSide) :
    Candidate.tent s k∈sourceCandidates lo hi D T ↔
      branchTest lo hi D s k ∧ rootTest lo hi D T (.tent s k) := by
  classical
  simp only [sourceCandidates,List.mem_filter,decide_eq_true_eq,
    tent_mem_sourceRaw_iff]

/-- The <= test is deliberately in this direction: the earlier head wins ties. -/
def firstMax {α : Type*} (score : α → ℚ) : List α → Option α
  | [] => none
  | a::as => match firstMax score as with
    | none => some a
    | some b => if score b≤score a then some a else some b

theorem firstMax_none_iff {α : Type*} (score : α → ℚ) (xs : List α) :
    firstMax score xs=none ↔ xs=[] := by
  cases xs with
  | nil => simp [firstMax]
  | cons a as =>
      cases ht : firstMax score as with
      | none => simp [firstMax,ht]
      | some b =>
          by_cases hb : score b≤score a <;> simp [firstMax,ht,hb]

theorem firstMax_mem_max {α : Type*} (score : α → ℚ) (xs : List α) (p : α)
    (h : firstMax score xs=some p) :
    p∈xs ∧ ∀ q∈xs, score q≤score p := by
  induction xs generalizing p with
  | nil => simp [firstMax] at h
  | cons a as ih =>
      cases ht : firstMax score as with
      | none =>
          have he := (firstMax_none_iff score as).mp ht
          subst as
          have hp : a=p := by simpa only [firstMax,Option.some.injEq] using h
          subst p
          simp
      | some b =>
          have hb := ih b ht
          by_cases hba : score b≤score a
          · have hp : a=p := by simpa only [firstMax,ht,if_pos hba,Option.some.injEq] using h
            subst p
            refine ⟨by simp,?_⟩
            intro q hq
            rcases List.mem_cons.mp hq with rfl | hq
            · exact le_rfl
            · exact (hb.2 q hq).trans hba
          · have hp : b=p := by simpa only [firstMax,ht,if_neg hba,Option.some.injEq] using h
            subst p
            refine ⟨List.mem_cons_of_mem a hb.1,?_⟩
            intro q hq
            rcases List.mem_cons.mp hq with rfl | hq
            · exact (lt_of_not_ge hba).le
            · exact hb.2 q hq

/-- A complete first-tie certificate: every earlier entry has STRICTLY smaller
score; entries after the winner may tie. No index/rank assumption is supplied. -/
theorem firstMax_priority {α : Type*} (score : α → ℚ) (xs : List α) (p : α)
    (h : firstMax score xs=some p) :
    ∃ before after, xs=before++p::after ∧
      (∀ q∈before, score q<score p) ∧ (∀ q∈after, score q≤score p) := by
  induction xs generalizing p with
  | nil => simp [firstMax] at h
  | cons a as ih =>
      cases ht : firstMax score as with
      | none =>
          have he := (firstMax_none_iff score as).mp ht
          subst as
          have hp : a=p := by simpa only [firstMax,Option.some.injEq] using h
          subst p
          exact ⟨[],[],rfl,by simp,by simp⟩
      | some b =>
          have hb := firstMax_mem_max score as b ht
          by_cases hba : score b≤score a
          · have hp : a=p := by simpa only [firstMax,ht,if_pos hba,Option.some.injEq] using h
            subst p
            refine ⟨[],as,rfl,by simp,?_⟩
            exact fun q hq => (hb.2 q hq).trans hba
          · have hp : b=p := by simpa only [firstMax,ht,if_neg hba,Option.some.injEq] using h
            subst p
            obtain ⟨before,after,he,hl,hr⟩ := ih b ht
            refine ⟨a::before,after,?_,?_,hr⟩
            · simp only [List.cons_append,he]
            · intro q hq
              rcases List.mem_cons.mp hq with rfl | hq
              · exact lt_of_not_ge hba
              · exact hl q hq

def originalMinorant (lo hi : Fin 3 → ℤ) (D T : ℤ) : Option Candidate :=
  firstMax (sourceScore lo hi D) (sourceCandidates lo hi D T)

theorem selected_tent_guards (lo hi : Fin 3 → ℤ) (D T : ℤ)
    (s : TentSum) (k : TentSide)
    (hselected : originalMinorant lo hi D T=some (.tent s k)) :
    branchTest lo hi D s k ∧ rootTest lo hi D T (.tent s k) := by
  exact (tent_mem_candidates_iff lo hi D T s k).mp
    (firstMax_mem_max _ _ _ hselected).1

theorem selected_base_root (lo hi : Fin 3 → ℤ) (D T : ℤ)
    (hselected : originalMinorant lo hi D T=some .base) :
    153*D-96*lo 2≤256*T := by
  classical
  have hm := (firstMax_mem_max _ _ _ hselected).1
  have hr := (List.mem_filter.mp hm).2
  simpa only [decide_eq_true_eq,rootTest] using hr

theorem selected_is_original_first_max (lo hi : Fin 3 → ℤ) (D T : ℤ)
    (p : Candidate) (hselected : originalMinorant lo hi D T=some p) :
    ∃ before after, sourceCandidates lo hi D T=before++p::after ∧
      (∀ q∈before, sourceScore lo hi D q<sourceScore lo hi D p) ∧
      (∀ q∈after, sourceScore lo hi D q≤sourceScore lo hi D p) := by
  exact firstMax_priority _ _ _ hselected

/-- No residual/OLD-domain test is hidden in this characterization. -/
theorem originalMinorant_none_iff (lo hi : Fin 3 → ℤ) (D T : ℤ) :
    originalMinorant lo hi D T=none ↔
      ∀ p∈sourceRaw lo hi D, ¬rootTest lo hi D T p := by
  classical
  rw [originalMinorant,firstMax_none_iff]
  simp [sourceCandidates,List.filter_eq_nil_iff]

/-- The original seed B passes the root filter on the actual positive boxes.
Thus a missing below-mu minorant is impossible even if every tent is absent. -/
theorem originalMinorant_ne_none (lo hi : Fin 3 → ℤ) (D T : ℤ)
    (hD : D=48000*2^24) (hT : T=481573208064) (hz : 0≤lo 2) :
    originalMinorant lo hi D T≠none := by
  intro hn
  have he := (originalMinorant_none_iff lo hi D T).mp hn .base (by simp [sourceRaw])
  apply he
  change 153*D-96*lo 2≤256*T
  have hc : 153*D≤256*T := by rw [hD,hT]; norm_num
  omega

/-- Actual selected-tent leaf estimate, with all finite branch/root selection
premises discharged from the executable source selector. The selected plane's
residual and low>=2 remain genuine POST-selection mean_upper guards. -/
theorem original_finite_selected_tent_integer_upper
    (table : CheckedBlockTable)
    (s : TentSum) (k : TentSide) (lo hi : Fin 3 → ℤ)
    (D T : ℤ) (a b : BoxPoint)
    (hD : D=48000*2^24) (hT : T=481573208064)
    (haBind : ∀ i, a i=(lo i:ℝ)/(D:ℝ))
    (hbBind : ∀ i, b i=(hi i:ℝ)/(D:ℝ))
    (ha : ∀ i, 0<a i) (hab : ∀ i, a i<b i)
    (hcut : (1:ℝ)/100≤a 2) (hyx : b 1≤a 0) (hzy : b 2≤a 1)
    (hmu : b 0≤VariableEnvelope.mu)
    (hfull : b 0+b 1+3*b 2≤thirdPrefixTheta)
    (hselected : originalMinorant lo hi D T=some (.tent s k))
    (hres : match k with
      | .rise => 0<D+(literalTentX s-2)*hi 0+(literalTentY s-2)*hi 1
      | .fall => 0<57*D+(-96*literalTentX s-64)*hi 0+(-96*literalTentY s-64)*hi 1)
    (hlow : 2≤(literalTentEndpoint s k hi D:ℝ))
    (hratio : ∀ i : Fin 2, b i.castSucc/a i.castSucc≤2)
    (hpositive : ∀ i : Fin 2, 0<(originalLnUnit (b i.castSucc/a i.castSucc)).lo) :
    (∫ t in compactRegion ∩ Icc a b, compactKernel t)≤
      value (literalOrdinaryUpper lo hi (meanHigh
        (ordinaryTentWeight s k a b (literalTentEndpoint s k hi D)
          (literalTentEndpoint s k lo D)).lo
        (ordinaryTentWeight s k a b (literalTentEndpoint s k hi D)
          (literalTentEndpoint s k lo D)).hi
        (readQueryLo160 (assembledRead table.blocks)
          (literalTentEndpoint s k hi D).num ((literalTentEndpoint s k hi D).den:ℤ))
        (readQueryLo160 (assembledRead table.blocks)
          (literalTentEndpoint s k lo D).num ((literalTentEndpoint s k lo D).den:ℤ))
        (readQueryHi160 (assembledRead table.blocks) (ordinaryNew a b).hi P160))) := by
  have hg := selected_tent_guards lo hi D T s k hselected
  have hbranch := hg.1
  have hroot := hg.2
  dsimp [branchTest,deltaNumerator,rawSum] at hbranch
  dsimp [rootTest,rawSum] at hroot
  exact original_selected_tent_stored_integer_upper table s k lo hi D T a b
    (literalTentEndpoint s k hi D) (literalTentEndpoint s k lo D) _ _ _
    hD hT haBind hbBind ha hab hcut hyx hzy hmu hfull hbranch hroot hres
    rfl rfl hlow hratio hpositive rfl rfl rfl

/-- Exact integer box() behavior when mean_upper is absent. -/
def applyOptionalMean (high : ℤ) : Option ℤ → ℤ
  | none => high
  | some j => min high j

theorem applyOptionalMean_none (high : ℤ) : applyOptionalMean high none=high := by
  rfl

theorem applyOptionalMean_some (high j : ℤ) :
    value (applyOptionalMean high (some j))=min (value high) (value j) := by
  exact value_min high j

/-- max0 and the original OUT-minus-OLD structure commute with the outer min. -/
theorem min_max0_sub (high out old : ℤ) (hh : 0≤high) :
    min high (max 0 (out-old))=max 0 (min high (out-old)) := by
  by_cases hd : 0≤out-old
  · rw [max_eq_right hd,max_eq_right (le_min hh hd)]
  · have hdn : out-old≤0 := le_of_not_ge hd
    rw [max_eq_left hdn,min_eq_right hh,min_eq_right (hdn.trans hh),max_eq_left hdn]

theorem max0_sub_antitone (out old₁ old₂ : ℤ) (h : old₁≤old₂) :
    max 0 (out-old₂)≤max 0 (out-old₁) := by
  exact max_le_max le_rfl (sub_le_sub_left h out)

/-- This comparison is arithmetic only. Source plane score is not OLD chord
score, so this identity must not be substituted for originalMinorant. -/
theorem min_max0_sub_eq (out old₁ old₂ : ℤ) :
    min (max 0 (out-old₁)) (max 0 (out-old₂))=
      max 0 (out-max old₁ old₂) := by
  rcases le_total old₁ old₂ with h | h
  · rw [max_eq_right h,min_eq_right (max0_sub_antitone out old₁ old₂ h)]
  · rw [max_eq_left h,min_eq_left (max0_sub_antitone out old₂ old₁ h)]

end
end ImbalancedChen.OriginalThirdP4AOrdinaryFiniteSelectorSourceOnly
