import ImbalancedChen.P2GammaPairThetaZero
import ImbalancedChen.P2EnhancedThetaReciprocalMass
import ImbalancedChen.P2GammaRankScaledUpperLogSaving

/-!
SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
Actual finite subfamilies, their exact original error, and the existing
physical Theta. Equal products keep the sum of ALL original label weights.
The reciprocal-mass lower bound is supplied by the existing singular-series
and true-li theorem. No lower bound on a selected family is manufactured.
-/
namespace ImbalancedChen.P2GammaSelectedPhysicalTheta
noncomputable section
open scoped Classical BigOperators
open P2GammaJointRetainedReduction P2GammaRetainedSameRhoMother
open P2OriginalGammaUpperLowRankConsumer
open P2EnhancedTwentyOneSameQWeighted (Theta)
open P2OriginalChildPhysicalNormalization (thetaAtom Theta_eq_sum_atoms)
open P2EnhancedThetaReciprocalMass
open MathlibNt.SieveTheory.SingularSeries
open P5OriginalU5CausalFinite (pairSupport)

abbrev Pair := ℕ × ℕ

def selectedWeight (S : Finset Pair) (sigma : Pair → ℝ) (t : Pair) : ℝ :=
  if t ∈ S then sigma t else 0

/-- Zero extension, not renormalization or deletion of a repeated product. -/
theorem selectedWeight_test {S U : Finset Pair} (hS : S ⊆ U)
    (sigma F : Pair → ℝ) :
    (∑ t ∈ U,selectedWeight S sigma t * F t) = ∑ t ∈ S,sigma t * F t := by
  have hf : U.filter (fun t => t ∈ S) = S := by
    ext t
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨hS h,h⟩⟩
  simp only [selectedWeight,ite_mul,zero_mul]
  rw [← Finset.sum_filter,hf]

/-- The literal selected original Gamma source. -/
def selectedGamma (N : ℕ) (moduli : Finset ℕ) (rho : ℕ → ℝ)
    (S : Finset Pair) (sigma : Pair → ℝ) : ℝ :=
  ∑ t ∈ S,sigma t * ∑ q ∈ moduli,rho q * gammaDiscrepancy N t q

/-- The previous unchanged smooth-trimmed EMPTY mother lane. -/
def selectedEmpty (N : ℕ) (moduli : Finset ℕ) (rho : ℕ → ℝ)
    (T : ℝ) (S : Finset Pair) (sigma : Pair → ℝ) : ℝ :=
  ∑ t ∈ S,sigma t * emptyPairError N t moduli rho T

/-- Exactly the already-estimated original source minus its unpaid empty
lane; it is not a definition forcing any target bound to hold. -/
def selectedResidual (N : ℕ) (moduli : Finset ℕ) (rho : ℕ → ℝ)
    (T : ℝ) (S : Finset Pair) (sigma : Pair → ℝ) : ℝ :=
  selectedGamma N moduli rho S sigma - selectedEmpty N moduli rho T S sigma

theorem selectedGamma_eq_original {N : ℕ} {S : Finset Pair}
    (hS : S ⊆ pairSupport N) (moduli : Finset ℕ) (rho : ℕ → ℝ) (sigma : Pair → ℝ) :
    selectedGamma N moduli rho S sigma =
      originalJointGammaError N moduli rho (selectedWeight S sigma) :=
  (selectedWeight_test hS sigma _).symm

theorem selectedEmpty_eq_original {N : ℕ} {S : Finset Pair}
    (hS : S ⊆ pairSupport N) (moduli : Finset ℕ) (rho : ℕ → ℝ)
    (T : ℝ) (sigma : Pair → ℝ) :
    selectedEmpty N moduli rho T S sigma =
      emptyJointError N moduli rho (selectedWeight S sigma) T :=
  (selectedWeight_test hS sigma _).symm

theorem selectedResidual_eq_original {N : ℕ} {S : Finset Pair}
    (hS : S ⊆ pairSupport N) (moduli : Finset ℕ) (rho : ℕ → ℝ)
    (T : ℝ) (sigma : Pair → ℝ) :
    selectedResidual N moduli rho T S sigma =
      originalJointGammaError N moduli rho (selectedWeight S sigma) -
        emptyJointError N moduli rho (selectedWeight S sigma) T := by
  rw [selectedResidual,selectedGamma_eq_original hS,selectedEmpty_eq_original hS]

theorem selectedResidual_smul (N : ℕ) (moduli : Finset ℕ) (rho : ℕ → ℝ)
    (T : ℝ) (S : Finset Pair) (sigma : Pair → ℝ) (a : ℝ) :
    selectedResidual N moduli rho T S (fun t => a*sigma t) =
      a*selectedResidual N moduli rho T S sigma := by
  simp only [selectedResidual,selectedGamma,selectedEmpty,mul_sub,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro t ht <;> ring

theorem selectedResidual_zero (N : ℕ) (moduli : Finset ℕ) (rho : ℕ → ℝ)
    (T : ℝ) (S : Finset Pair) (sigma : Pair → ℝ)
    (hs : ∀ t ∈ S,sigma t = 0) : selectedResidual N moduli rho T S sigma = 0 := by
  have hg : selectedGamma N moduli rho S sigma = 0 :=
    Finset.sum_eq_zero (fun t ht => by rw [hs t ht,zero_mul])
  have he : selectedEmpty N moduli rho T S sigma = 0 :=
    Finset.sum_eq_zero (fun t ht => by rw [hs t ht,zero_mul])
  rw [selectedResidual,hg,he,sub_self]

/-- Restricting to S does not prove the complementary selected family
small. This identity explicitly retains everything outside S. -/
theorem selectedResidual_partition {N : ℕ} {S : Finset Pair}
    (hS : S ⊆ pairSupport N) (moduli : Finset ℕ) (rho : ℕ → ℝ)
    (T : ℝ) (sigma : Pair → ℝ) :
    selectedResidual N moduli rho T (pairSupport N) sigma =
      selectedResidual N moduli rho T S sigma +
        selectedResidual N moduli rho T (pairSupport N \ S) sigma := by
  have hp (F : Pair → ℝ) :
      (∑ t ∈ pairSupport N,sigma t*F t) =
        (∑ t ∈ S,sigma t*F t) + ∑ t ∈ pairSupport N \ S,sigma t*F t := by
    rw [← selectedWeight_test hS sigma F,
      ← selectedWeight_test (Finset.sdiff_subset : pairSupport N \ S ⊆ pairSupport N) sigma F,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    by_cases hs : t ∈ S <;> simp [selectedWeight,Finset.mem_sdiff,ht,hs]
  simp only [selectedResidual,selectedGamma,selectedEmpty]
  rw [hp,hp]
  ring

def reciprocalMass (S : Finset Pair) (sigma : Pair → ℝ) : ℝ :=
  ∑ t ∈ S,sigma t / ((t.1*t.2 : ℕ) : ℝ)

/-- The EXISTING Theta, on the exact product pushforward of S. -/
def selectedTheta (N : ℕ) (Qphys : ℝ) (S : Finset Pair) (sigma : Pair → ℝ) : ℝ :=
  Theta N Qphys (P5PrimePairEndpoint.productImage S)
    (P5PrimePairEndpoint.productWeight S sigma)

theorem selectedTheta_eq_atoms (N : ℕ) (Qphys : ℝ) (S : Finset Pair)
    (sigma : Pair → ℝ) :
    selectedTheta N Qphys S sigma =
      ∑ t ∈ S,sigma t * thetaAtom N Qphys (t.1*t.2) := by
  rw [selectedTheta,Theta_eq_sum_atoms]
  exact P5PrimePairEndpoint.productWeight_sum S sigma (thetaAtom N Qphys)

theorem reciprocalMass_pushforward (S : Finset Pair) (sigma : Pair → ℝ) :
    (∑ d ∈ P5PrimePairEndpoint.productImage S,
      P5PrimePairEndpoint.productWeight S sigma d / (d : ℝ)) =
        reciprocalMass S sigma := by
  simpa only [div_eq_mul_inv,one_div,reciprocalMass,P5PrimePairEndpoint.product] using
    P5PrimePairEndpoint.productWeight_sum S sigma (fun d => 1/(d : ℝ))

theorem selectedTheta_lower {N : ℕ} (hN : 4 ≤ N) (Qphys : ℝ)
    (S : Finset Pair) (sigma : Pair → ℝ) (hS : S ⊆ pairSupport N)
    (hs : ∀ t ∈ S,0 ≤ sigma t)
    (hQ : ∀ t ∈ S,1 < Qphys/((t.1*t.2 : ℕ) : ℝ) ∧
      Qphys/((t.1*t.2 : ℕ) : ℝ) ≤ N) :
    (2*liuUniversalProduct*(N : ℝ)/(Real.log (N : ℝ))^2) * reciprocalMass S sigma ≤
      selectedTheta N Qphys S sigma := by
  have hd : ∀ d ∈ P5PrimePairEndpoint.productImage S,0 < d := by
    intro d hd
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hd
    exact P2OriginalU5SmallPartnerRootPayment.pair_product_pos (hS ht)
  have hw : ∀ d ∈ P5PrimePairEndpoint.productImage S,
      0 ≤ P5PrimePairEndpoint.productWeight S sigma d := by
    intro d hd
    exact Finset.sum_nonneg (fun t ht => hs t (Finset.mem_filter.mp ht).1)
  have hl : ∀ d ∈ P5PrimePairEndpoint.productImage S,
      1 < Qphys/(d : ℝ) ∧ Qphys/(d : ℝ) ≤ N := by
    intro d hd
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hd
    exact hQ t ht
  have h := Theta_lower hN Qphys (P5PrimePairEndpoint.productImage S)
    (P5PrimePairEndpoint.productWeight S sigma) hd hw hl
  rw [reciprocalMass_pushforward] at h
  exact h

/-- Zero reciprocal mass forces every nonnegative labelled weight to
vanish; empty S and repeated products require no special normalization. -/
theorem reciprocalMass_zero_iff {N : ℕ} (S : Finset Pair) (sigma : Pair → ℝ)
    (hS : S ⊆ pairSupport N) (hs : ∀ t ∈ S,0 ≤ sigma t) :
    reciprocalMass S sigma = 0 ↔ ∀ t ∈ S,sigma t = 0 := by
  constructor
  · intro hm t ht
    have hd : (0 : ℝ) < ((t.1*t.2 : ℕ) : ℝ) := by
      exact_mod_cast P2OriginalU5SmallPartnerRootPayment.pair_product_pos (hS ht)
    have hv : sigma t / ((t.1*t.2 : ℕ) : ℝ) ≤ 0 := by
      calc
        _ ≤ reciprocalMass S sigma := Finset.single_le_sum
          (fun u hu => div_nonneg (hs u hu) (Nat.cast_nonneg _)) ht
        _ = 0 := hm
    have hnonpos := (div_le_iff₀ hd).mp hv
    exact le_antisymm (by simpa only [zero_mul] using hnonpos) (hs t ht)
  · intro hz
    exact Finset.sum_eq_zero (fun t ht => by rw [hz t ht,zero_div])

theorem selectedTheta_zero_iff {N : ℕ} (hN : 4 ≤ N) (Qphys : ℝ)
    (S : Finset Pair) (sigma : Pair → ℝ) (hS : S ⊆ pairSupport N)
    (hs : ∀ t ∈ S,0 ≤ sigma t)
    (hQ : ∀ t ∈ S,1 < Qphys/((t.1*t.2 : ℕ) : ℝ) ∧
      Qphys/((t.1*t.2 : ℕ) : ℝ) ≤ N) :
    selectedTheta N Qphys S sigma = 0 ↔ reciprocalMass S sigma = 0 := by
  have hU := liuUniversalProduct_pos
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc : 0 < 2*liuUniversalProduct*(N : ℝ)/(Real.log (N : ℝ))^2 := by positivity
  constructor
  · intro hz
    have h := selectedTheta_lower hN Qphys S sigma hS hs hQ
    rw [hz] at h
    have hm : 0 ≤ reciprocalMass S sigma :=
      Finset.sum_nonneg (fun t ht => div_nonneg (hs t ht) (Nat.cast_nonneg _))
    nlinarith
  · intro hz
    have hs0 := (reciprocalMass_zero_iff S sigma hS hs).mp hz
    rw [selectedTheta_eq_atoms]
    exact Finset.sum_eq_zero (fun t ht => by rw [hs0 t ht,zero_mul])

/-- A concrete quantitative sufficient test: a retained subfamily carries
pointwise weight at least a*height and has an explicit reciprocal mass.
Neither condition is inferred from mere nonemptiness or positivity. -/
theorem reciprocalMass_of_subfamily {S U : Finset Pair} (hU : U ⊆ S)
    (sigma : Pair → ℝ) (hs : ∀ t ∈ S,0 ≤ sigma t)
    (a height : ℝ) (hweight : ∀ t ∈ U,a*height ≤ sigma t) :
    a*height*(∑ t ∈ U,1/((t.1*t.2 : ℕ) : ℝ)) ≤ reciprocalMass S sigma := by
  calc
    _ = ∑ t ∈ U,(a*height)/((t.1*t.2 : ℕ) : ℝ) := by rw [Finset.mul_sum]; simp [div_eq_mul_inv]
    _ ≤ ∑ t ∈ U,sigma t/((t.1*t.2 : ℕ) : ℝ) :=
      Finset.sum_le_sum (fun t ht => div_le_div_of_nonneg_right (hweight t ht) (Nat.cast_nonneg _))
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hU
      (fun t ht hnot => div_nonneg (hs t ht) (Nat.cast_nonneg _))

end
end ImbalancedChen.P2GammaSelectedPhysicalTheta
