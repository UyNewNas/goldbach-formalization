import ImbalancedChen.P2EnhancedSeedInheritedCellBounds

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual second-seed W2 functional, with all three singleton and four
pair contributions. The disjoint split is support versus its complement
WITHIN each original term: the seven geometric domains need not be disjoint.
This proves an exact real identity, not a count licence or a numerical
lower bound on lambda. In particular lambda/50 > 13/5000 remains OPEN.
-/

namespace ImbalancedChen.P2EnhancedSeedActualFeedbackAssembly

noncomputable section
open Set MeasureTheory Classical
open scoped BigOperators
open P2EnhancedSeedSingletonPrimitive
open P5OriginalActionMassBound (Point W2SingletonDomain W2PairDomain)
open P5OriginalFeedbackDomains (pairProfile)

def actualFeedback (J : ℝ) : ℝ :=
  P5OriginalActionMassBound.W2FeedbackValue parameters (seedUpper J) (seedLower J)

def singletonTerm (J : ℝ) (j : Fin 3) : ℝ :=
  ∫ u in W2SingletonDomain parameters j,
    P5OriginalActionMassBound.singletonKernel u * seedLower J (profile u)

def pairTerm (J : ℝ) (j : Fin 4) : ℝ :=
  ∫ x in W2PairDomain parameters j,
    P5OriginalActionMassBound.pairKernel x * seedUpper J (pairProfile parameters j x)

def pairCut (j : Fin 4) : Set Point := {x | pairProfile parameters j x ≤ S}
def supportedPair (j : Fin 4) : Set Point := W2PairDomain parameters j ∩ pairCut j
def excludedPair (j : Fin 4) : Set Point := W2PairDomain parameters j ∩ (pairCut j)ᶜ

theorem pair_support_disjoint (j : Fin 4) : Disjoint (supportedPair j) (excludedPair j) := by
  rw [Set.disjoint_left]
  exact fun _ h h' => h'.2 h.2

theorem pair_support_union (j : Fin 4) :
    supportedPair j ∪ excludedPair j = W2PairDomain parameters j := by
  ext x
  simp only [supportedPair,excludedPair,mem_union,mem_inter_iff,mem_compl_iff]
  tauto

theorem pair_feedback_zero_off_support (J : ℝ) (j : Fin 4) {x : Point}
    (hx : x ∈ excludedPair j) : seedUpper J (pairProfile parameters j x)=0 := by
  have hout : pairProfile parameters j x ∉ Icc (1 : ℝ) S := fun h => hx.2 h.2
  exact indicator_of_notMem hout _

theorem singletonTerm_exact (J : ℝ) (j : Fin 3) :
    singletonTerm J j = J * ∫ u in Icc uStar (cap j),singletonLogKernel u := by
  calc
    _ = ∫ u in W2SingletonDomain parameters j,singletonFeedback J u := by
      apply setIntegral_congr_fun (P5OriginalFeedbackDomains.measurableSet_W2SingletonDomain _ _)
      intro u hu
      rw [P5OriginalActionMassBound.singletonKernel_eq_raw
        (P5OriginalActionMassBound.W2SingletonDomain_subset parameters_geometry j hu)]
      dsimp [singletonFeedback]
      ring
    _ = _ := singleton_feedback_original_domain_exact J j

theorem pairTerm_exact (J : ℝ) (j : Fin 4) :
    pairTerm J j = J * ∫ x in supportedPair j,P2EnhancedSeedPairD6Primitive.pairKernel x := by
  have hcut : MeasurableSet (pairCut j) :=
    measurableSet_le (P5OriginalFeedbackDomains.measurable_pairProfile parameters j) measurable_const
  calc
    _ = ∫ x in W2PairDomain parameters j,(pairCut j).indicator
        (fun x => J*P2EnhancedSeedPairD6Primitive.pairKernel x) x := by
      apply setIntegral_congr_fun (P5OriginalFeedbackDomains.measurableSet_W2PairDomain _ _)
      intro x hx
      have hg := P5OriginalFeedbackDomains.W2PairDomain_geometry parameters_geometry j hx
      have hp := (P5OriginalFeedbackDomains.W2PairDomain_profile_bounds parameters_geometry j hx).1
      rw [P5OriginalActionMassBound.pairKernel_eq_raw hg.1 hg.2]
      by_cases hs : pairProfile parameters j x ≤ S
      · rw [seedUpper,indicator_of_mem ⟨hp.le,hs⟩,indicator_of_mem hs]
        dsimp [P2EnhancedSeedPairD6Primitive.pairKernel]
        ring
      · rw [seedUpper,indicator_of_notMem (fun h => hs h.2),indicator_of_notMem hs,mul_zero]
    _ = _ := by rw [setIntegral_indicator hcut,integral_const_mul]; rfl

/-- Exactly the original W2 operator; the two unchanged-prefix point
masses vanish because both anchors exceed S. Division by five occurs once. -/
theorem actualFeedback_seven_terms (J : ℝ) :
    actualFeedback J = (singletonTerm J 0 + singletonTerm J 1 + singletonTerm J 2 +
      pairTerm J 0 + pairTerm J 1 + pairTerm J 2 + pairTerm J 3)/5 := by
  have h0 : seedUpper J parameters.s0=0 := by norm_num [seedUpper,parameters,S]
  have h1 : seedUpper J parameters.phi1=0 := by norm_num [seedUpper,parameters,S]
  unfold actualFeedback P5OriginalActionMassBound.W2FeedbackValue
  rw [h0,h1]
  change (4*0+0+singletonTerm J 0+singletonTerm J 1+singletonTerm J 2+
    pairTerm J 0+pairTerm J 1+pairTerm J 2+pairTerm J 3)/5 = _
  ring

def singletonCoefficient (j : Fin 3) : ℝ := ∫ u in Icc uStar (cap j),singletonLogKernel u
def pairCoefficient (j : Fin 4) : ℝ :=
  ∫ x in supportedPair j,P2EnhancedSeedPairD6Primitive.pairKernel x
def lambda : ℝ := (singletonCoefficient 0+singletonCoefficient 1+singletonCoefficient 2+
  pairCoefficient 0+pairCoefficient 1+pairCoefficient 2+pairCoefficient 3)/5

/-- Literal actual logarithmic singleton kernels and support-restricted
pair kernels, rather than an abstract seven-summand wrapper. -/
theorem actualFeedback_eq_mul_lambda (J : ℝ) : actualFeedback J=J*lambda := by
  rw [actualFeedback_seven_terms]
  simp only [singletonTerm_exact,pairTerm_exact]
  dsimp [lambda,singletonCoefficient,pairCoefficient]
  ring

/-- This additive identity concerns the explicit linear MODEL operator.
It does not authorise adding two alternative estimates for the same count. -/
theorem actualFeedback_add (J K : ℝ) :
    actualFeedback (J+K)=actualFeedback J+actualFeedback K := by
  simp only [actualFeedback_eq_mul_lambda]
  ring

theorem actualFeedback_one_fiftieth : actualFeedback (1/50)=lambda/50 := by
  rw [actualFeedback_eq_mul_lambda]
  ring

theorem D6_support_exact : supportedPair 1=P2EnhancedSeedPairD6Primitive.D6 := by
  ext x
  constructor
  · exact fun h => h.1
  · intro hx
    refine ⟨hx,?_⟩
    have hp := P2EnhancedSeedPairD6Primitive.D6_actual_profile hx
    change P2EnhancedSeedPairD6Primitive.fixedProfile x ≤ S
    exact hp.2.le.trans (by norm_num [S])

/-- The untruncated D6 coefficient is its actual outer logarithm. -/
theorem pairCoefficient_D6_log : pairCoefficient 1 =
    ∫ u in Ioo P2EnhancedSeedPairD6Primitive.uLo P2EnhancedSeedPairD6Primitive.uHi,
      P2EnhancedSeedInheritedCellBounds.d6OuterSlice u := by
  rw [pairCoefficient,D6_support_exact,P2EnhancedSeedPairD6Primitive.integral_D6_nested]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  exact P2EnhancedSeedPairD6Primitive.D6_inner_slice hu

end
end ImbalancedChen.P2EnhancedSeedActualFeedbackAssembly
