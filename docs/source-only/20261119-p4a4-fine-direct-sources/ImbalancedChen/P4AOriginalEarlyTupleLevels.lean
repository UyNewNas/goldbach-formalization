import ImbalancedChen.P4AOriginalEarlyHistoricalSums
import ImbalancedChen.P5OriginalFifthArchiveFallbackSeparation

namespace ImbalancedChen.P4AOriginalEarlyTupleLevels
noncomputable section
open scoped Classical BigOperators
open Set VariableEnvelope HistoricalThirdCoarse
open P5OriginalCommonRefinedConstructor (OriginalData originalSeed)
open P1OriginalVariableFourthContinuation (producerEligible finiteMax_eq_seed_of_outside)
open P1OriginalVariableFifthContinuation (eligible)
open P5OriginalCommonRefinedSeedHull (oldFourth oldFifth)
open P5OriginalCommonFourthSourceNavigation (firstCoordinate firstCoordinate_ancestor guards_false_below_mu)
open P4AOriginalOrderedThirdFullPolicy (Root prior current current_ancestor fourth fifth third cap5)
open P4AOriginalOrderedThirdTable (atPoint capValue infimum rawExponent envelope)
open P4AOriginalOrderedSixthStages (ownFifth)
open P4AOriginalFiniteFallbackPolicy (high)
open P1GuardFrozenFiniteCapAlgebra (protect rounded protect_error rounded_error)
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalEarlyFiniteStages (seed level4 level5 third_le_fourth fourth_le_fifth cap5_as_protect)
open P4AOriginalEarlyHistoricalSums (oldLevel3)

def occurs4 (d : OriginalData) (N : ℝ) (h : List ℕ) : Prop :=
  ∃ r∈d.rows4, producerEligible d.licensed4 r (primeHistoryLogCoordinates N 4 h)

def occurs5 (d : OriginalData) (N : ℝ) (h : List ℕ) : Prop :=
  ∃ r∈d.rows5, eligible d.e d.chi d.m d.omega d.J5 r (primeHistoryLogCoordinates N 5 h)

theorem seed_nonneg (d : OriginalData) (he : 0≤(d.e:ℝ)) (he' : (d.e:ℝ)≤1/384)
    (w N : ℝ) (h : List ℕ) : 0≤seed d w N h := by
  have hi : 0≤initial (d.e:ℝ) := by
    dsimp [initial,extendedDistributionCap]; linarith
  have hk {j : Cell d.m} (hj : j∈P4AOriginalOrderedThirdTable.retained (d.e:ℝ) d.m) :
      0≤capValue (d.e:ℝ) d.m j := by
    have hr := (Finset.mem_filter.mp hj).2
    have hb : (1/2:ℝ)≤infimum d.m j (actualExtendedThirdRobustBaseBranch 0) := by
      apply le_csInf (hr.1.image _)
      rintro _ ⟨s,hs,rfl⟩
      apply half_le_v_of_extended_range (hs.2.1.trans (hs.2.2.1.trans hs.2.2.2))
      linarith [(hs.1 0 (mem_univ _)).2,hr.2]
    have hg : 1/2≤envelope (d.e:ℝ) d.m j := by
      unfold envelope; split_ifs <;> first | exact hb.trans (le_max_left _ _) | exact hb
    change 0≤min (thirdPrefixTheta-2*(d.e:ℝ)) (envelope (d.e:ℝ) d.m j-2*(d.e:ℝ))
    apply le_min <;> dsimp [thirdPrefixTheta] <;> linarith
  unfold seed current rawExponent atPoint
  split_ifs with hAct hcell
  · exact hk hcell.choose_spec.1
  all_goals exact hi

theorem protect_self (n : ℕ) {s : ℝ} (hs : 0≤s) : protect n s s=s := by
  apply max_eq_left
  by_cases h : s≤cap
  · exact (rounded_error n s hs h).2.2
  · exact (P4AOrderedThirdGlobalRange.rounded_le n s).trans (le_of_not_ge h)

/-- This includes the initial fallback value, which can lie strictly above
the quantizer's clamping ceiling. In that case no row can improve it. -/
theorem protect_bounded (n : ℕ) {s x : ℝ} (hs : 0≤s) (hsx : s≤x) (hx : x≤max s cap) :
    s≤protect n s x ∧ protect n s x≤x ∧ |protect n s x-x|≤2*width n := by
  by_cases h : s≤cap
  · have H := protect_error n s x hs hsx (hx.trans_eq (max_eq_right h))
    exact ⟨H.1,H.2.2,by rw [abs_of_nonpos (sub_nonpos.mpr H.2.2)]; linarith [H.2.1]⟩
  · have heq : x=s := le_antisymm (hx.trans_eq (max_eq_left (le_of_not_ge h))) hsx
    rw [heq,protect_self n hs,sub_self,abs_zero]
    exact ⟨le_rfl,le_rfl,by linarith [width_pos n]⟩

theorem raw_bound (d : OriginalData) (he : 0≤d.e) (R : Root) (N : ℝ) (h : List ℕ) :
    R.scalar≤fourth R d N h ∧ fourth R d N h≤max R.scalar cap ∧
    R.scalar≤fifth R d N h ∧ fifth R d N h≤max R.scalar cap := by
  let C := max R.scalar cap
  have stage := (P4AOrderedThirdGlobalRange.stages R d he N C (le_max_right _ _) (le_max_left _ _) 0).1
  have H : ∀ z : List ℕ, fourth R d N z≤C := by
    intro z
    unfold fourth
    have ht : third R N z≤C := by
      unfold third
      apply max_le (le_max_left _ _)
      split_ifs <;> first | exact (v_le_cap _).trans (le_max_right _ _) | exact le_max_left _ _
    split
    · apply P1OriginalVariableFourthContinuation.finiteMax_le _ _ _ _ _ ht
      intro r _ _
      rw [r.bufferedCandidate_eq]
      have hcap := (v_le_cap (∑i∈r.selected,primeHistoryLogCoordinates N 4 z i)).trans (le_max_right R.scalar cap)
      have he' : 0≤(d.e:ℝ) := by exact_mod_cast he
      linarith
    · exact ht
  exact ⟨(le_max_left _ _).trans (third_le_fourth _ _ _ _),H h,
    ((le_max_left _ _).trans (third_le_fourth _ _ _ _)).trans (fourth_le_fifth _ _ _ _),stage h⟩

theorem old_level (d : OriginalData) (N : ℕ) (h : List ℕ) :
    oldLevel3 d N (rosserAncestor 3 h)=(N:ℝ)^originalSeed d N h :=
  P1OriginalVariableFourthContinuation.frozenLevel_eq_rpow_seed _ _ _ _ _ _

theorem raw_fourth_on_owner (d : OriginalData) (w N : ℝ) (h : List ℕ) (hl : h.length=4)
    (hlo : ¬high N h) (ho : current d w N h=prior d N h) :
    fourth (current d w N h) d N h=oldFourth d N h := by
  obtain ⟨hs,ht⟩ := guards_false_below_mu N h (by omega) (le_of_not_gt hlo)
  rw [ho]
  simp only [fourth,third,if_pos hl,if_neg ht,if_neg hs,max_self,oldFourth,
    P1OriginalVariableFourthContinuation.exponent4,P1OriginalVariableFourthContinuation.profile4] <;> rfl

theorem raw_fifth_on_owner (d : OriginalData) (w N : ℝ) (h : List ℕ) (hl : h.length=5)
    (hx : primeHistoryLogCoordinates N 5 h 0≤mu) (ho : current d w N h=prior d N h) :
    fifth (current d w N h) d N h=oldFifth d N h := by
  rw [ho,P4AOriginalOrderedThirdFullPolicy.fifth_prior]
  exact P5OriginalFifthArchiveFallbackSeparation.fifth_eq_old_below_mu d N h hl hx

theorem high_ancestor4 (N : ℝ) (h : List ℕ) : high N (rosserAncestor 4 h) ↔ high N h := by
  change mu<firstCoordinate N (rosserAncestor 4 h) ↔ _
  rw [firstCoordinate_ancestor N 4 (by decide)]
  rfl

theorem fourth_off (n : ℕ) (d : OriginalData) (w N : ℝ) (h : List ℕ) (hl : h.length=4)
    (hs : 0≤seed d w N h) (hn : ¬occurs4 d N h) :
    level4 n d w N h=seed d w N h ∧ oldFourth d N h=originalSeed d N h := by
  have out : ∀r∈d.rows4,¬ producerEligible d.licensed4 r (primeHistoryLogCoordinates N 4 h) :=
    fun r hr H => hn ⟨r,hr,H⟩
  refine ⟨?_,P1OriginalVariableFourthContinuation.exponent4_outside _ _ _ _ _ _ _ _ _ out⟩
  by_cases hi : high N h
  · exact if_pos hi
  have hg := guards_false_below_mu N h (by omega) (le_of_not_gt hi)
  have hraw : fourth (current d w N h) d N h=seed d w N h := by
    rw [fourth,if_pos hl,finiteMax_eq_seed_of_outside _ _ _ _ out]
    simp [third,hg.1,hg.2,seed]
  simp only [level4,if_neg hi,hraw]
  split <;> first | exact protect_self n hs | rfl

theorem fifth_off (n : ℕ) (d : OriginalData) (w N : ℝ) (h : List ℕ) (hl : h.length=5)
    (hn : ¬occurs5 d N h) :
    level5 n d w N h=level4 n d w N (rosserAncestor 4 h) ∧
      oldFifth d N h=oldFourth d N (rosserAncestor 4 h) := by
  have out : ∀r∈d.rows5,¬eligible d.e d.chi d.m d.omega d.J5 r (primeHistoryLogCoordinates N 5 h) :=
    fun r hr H => hn ⟨r,hr,H⟩
  have raw : fifth (current d w N h) d N h=fourth (current d w N h) d N (rosserAncestor 4 h) := by
    rw [fifth,if_pos hl,finiteMax_eq_seed_of_outside _ _ _ _ out]
  refine ⟨?_,?_⟩
  · simp only [level5,level4,high_ancestor4,current_ancestor d w N h 4 (by decide),ownFifth,
      cap5_as_protect,raw]
    split_ifs <;> rfl
  · unfold oldFifth P1OriginalVariableFifthContinuation.exponent5
    rw [if_pos hl,finiteMax_eq_seed_of_outside _ _ _ _ out] <;> rfl

/-- Each true protected exponent has the same parent floor and lies at
distance at most twice the mesh width from its original raw exponent. -/
theorem fourth_range (n : ℕ) (d : OriginalData) (he : 0≤d.e) (he' : (d.e:ℝ)≤1/384)
    (w N : ℝ) (h : List ℕ) (hl : h.length=4) (hlo : ¬high N h) (ho : current d w N h=prior d N h) :
    let x := oldFourth d N h
    let y := level4 n d w N h
    x∈Icc (0:ℝ) 1 ∧ y∈Icc (0:ℝ) 1 ∧ seed d w N h≤x ∧ seed d w N h≤y ∧ |y-x|≤2*width n := by
  dsimp only
  have heR : 0≤(d.e:ℝ) := by exact_mod_cast he
  have hs := seed_nonneg d heR he' w N h
  have HB := raw_bound d he (current d w N h) N h
  rw [raw_fourth_on_owner d w N h hl hlo ho] at HB
  have HU := P4AOrderedThirdGlobalRange.seed_le d he w N h
  have U : max (seed d w N h) cap≤1 := max_le (HU.trans (by norm_num [P4AFull87UnionCompilerPayment.top]))
    (by norm_num [cap])
  have X : oldFourth d N h∈Icc (0:ℝ) 1 := ⟨hs.trans HB.1,HB.2.1.trans U⟩
  have hp := protect_bounded n hs HB.1 HB.2.1
  rw [level4,if_neg hlo,raw_fourth_on_owner d w N h hl hlo ho]
  split
  · exact ⟨X,⟨hs.trans hp.1,hp.2.1.trans X.2⟩,HB.1,hp.1,hp.2.2⟩
  · exact ⟨X,X,HB.1,HB.1,by rw [sub_self,abs_zero]; linarith [width_pos n]⟩

theorem fifth_range (n : ℕ) (d : OriginalData) (he : 0≤d.e) (he' : (d.e:ℝ)≤1/384)
    (w N : ℝ) (h : List ℕ) (hl : h.length=5) (hlo : ¬high N h)
    (hx : primeHistoryLogCoordinates N 5 h 0≤mu) (ho : current d w N h=prior d N h) :
    oldFifth d N h∈Icc (0:ℝ) 1 ∧ level5 n d w N h∈Icc (0:ℝ) 1 ∧
      |level5 n d w N h-oldFifth d N h|≤2*width n := by
  have hs := seed_nonneg d (by exact_mod_cast he) he' w N h
  have HB := raw_bound d he (current d w N h) N h
  have hraw := raw_fifth_on_owner d w N h hl hx ho
  rw [hraw] at HB
  have HU := P4AOrderedThirdGlobalRange.seed_le d he w N h
  have U : max (seed d w N h) cap≤1 := max_le (HU.trans (by norm_num [P4AFull87UnionCompilerPayment.top]))
    (by norm_num [cap])
  have X : oldFifth d N h∈Icc (0:ℝ) 1 := ⟨hs.trans HB.2.2.1,HB.2.2.2.trans U⟩
  have hp := protect_bounded n hs HB.2.2.1 HB.2.2.2
  rw [level5,if_neg hlo,ownFifth]
  split
  · rw [cap5_as_protect,hraw]
    exact ⟨X,⟨hs.trans hp.1,hp.2.1.trans X.2⟩,hp.2.2⟩
  · rw [hraw]; exact ⟨X,X,by rw [sub_self,abs_zero]; linarith [width_pos n]⟩

end
end ImbalancedChen.P4AOriginalEarlyTupleLevels

