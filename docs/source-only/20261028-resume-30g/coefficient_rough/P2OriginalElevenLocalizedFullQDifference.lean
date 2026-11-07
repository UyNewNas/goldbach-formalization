import ImbalancedChen.P2OriginalElevenActualDifferenceLocalization
import ImbalancedChen.FiniteUpperCarrierCore
import ImbalancedChen.P4BSignedErrorPayment

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The two concrete common-policy coefficients are placed on one genuine
small/rough union carrier. Their full signed difference is localized to
the paid original omitted-prefix divisor cover BEFORE a test is applied.
The AP specialization keeps the exact original count and coprime mean.
It supplies source/arithmetic licence, not an analytic AP budget.
-/
namespace ImbalancedChen.P2OriginalElevenLocalizedFullQDifference
noncomputable section
open Classical
open scoped BigOperators
open P5OriginalCommonRefinedConstructor P2OriginalElevenCompactGatedPolicy
open P2OriginalElevenActualDifferenceLocalization
open Certificates.P2OriginalSixthElevenLogSemantics
open P2OriginalElevenFullModulusOmittedCover

def commonRough (d : OriginalData) (n N cap : ℕ) (w z : ℝ) : Finset ℕ :=
  fixedRoughSupport ((compactPolicy8 d n (N : ℝ)) false) N cap w z ∪
    fixedRoughSupport ((policy8 d (N : ℝ)) false) N cap w z

def paidRough (d : OriginalData) (n N cap : ℕ) (w z : ℝ) : Finset ℕ :=
  (commonRough d n N cap w z).filter (PaidDivisorCover n N)

def commonQ (d : OriginalData) (n N cap : ℕ) (w z : ℝ) : Finset ℕ :=
  smallRoughModuli (actualSmallRosserSupport N cap w) (commonRough d n N cap w z)

def deltaRho (d : OriginalData) (n N cap : ℕ) (w z L : ℝ) (q : ℕ) : ℝ :=
  actualSmallRoughRho ((compactPolicy8 d n (N : ℝ)) false) N cap w z L q - rho d N cap w z L q

def deltaPair (d : OriginalData) (n N cap : ℕ) (w z L : ℝ) (x : ℕ × ℕ) : ℝ :=
  smallRoughPairCoefficient (fixedRoughCoefficient ((compactPolicy8 d n (N : ℝ)) false) N cap w z)
      (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L) x -
    smallRoughPairCoefficient (fixedRoughCoefficient ((policy8 d (N : ℝ)) false) N cap w z)
      (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L) x

/-- The localized ACTUAL difference carrier lies in the very full-small/
residual divisor classes paid in F, on each of its two genuine policies.
No canonical-prefix-only or ALL16 support assertion is substituted. -/
theorem paidRough_subset_F_paid_cells (d : OriginalData) (n N cap : ℕ) (w z : ℝ) :
    paidRough d n N cap w z ⊆ allCells.toFinset.biUnion (fun c =>
      omittedRough ((compactPolicy8 d n (N : ℝ)) false) c n N cap w z ∪
        omittedRough ((policy8 d (N : ℝ)) false) c n N cap w z) := by
  intro b hb
  obtain ⟨hbU,c,p,hp,hdiv⟩ := Finset.mem_filter.mp hb
  apply Finset.mem_biUnion.mpr
  refine ⟨c,List.mem_toFinset.mpr (allCells_complete c),?_⟩
  rcases Finset.mem_union.mp hbU with hbnew | hbold
  · exact Finset.mem_union_left _
      (actual_omitted_prefix_covered _ c n N cap w z hbnew hp hdiv)
  · exact Finset.mem_union_right _
      (actual_omitted_prefix_covered _ c n N cap w z hbold hp hdiv)

theorem commonRough_rough (d : OriginalData) (n N cap : ℕ) (w z : ℝ)
    {b : ℕ} (hb : b ∈ commonRough d n N cap w z) : RoughPrimeSupportedAt w b := by
  rcases Finset.mem_union.mp hb with hb | hb
  · exact fixedRoughSupport_roughPrimeSupportedAt _ N cap w z hb
  · exact fixedRoughSupport_roughPrimeSupportedAt _ N cap w z hb

theorem commonQ_squarefree_coprime (d : OriginalData) (n N cap : ℕ) (w z : ℝ)
    {q : ℕ} (hq : q ∈ commonQ d n N cap w z) : Squarefree q ∧ q.Coprime N := by
  obtain ⟨⟨e,b⟩,heb,rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨he,hb⟩ := Finset.mem_product.mp heb
  rcases Finset.mem_union.mp hb with hb | hb
  · have hm : e*b ∈ actualSmallRoughModuli ((compactPolicy8 d n (N : ℝ)) false) N cap w z :=
      Finset.mem_image.mpr ⟨(e,b),Finset.mem_product.mpr ⟨he,hb⟩,rfl⟩
    exact ⟨actualSmallRoughModuli_squarefree _ N cap w z hm,
      actualSmallRoughModuli_coprime_target _ N cap w z hm⟩
  · have hm : e*b ∈ actualSmallRoughModuli ((policy8 d (N : ℝ)) false) N cap w z :=
      Finset.mem_image.mpr ⟨(e,b),Finset.mem_product.mpr ⟨he,hb⟩,rfl⟩
    exact ⟨actualSmallRoughModuli_squarefree _ N cap w z hm,
      actualSmallRoughModuli_coprime_target _ N cap w z hm⟩

theorem deltaPair_eq_zero_off_cover (d : OriginalData) (n N cap : ℕ) (hN : 1 < N)
    (w z L : ℝ) (x : ℕ × ℕ) (hgood : ¬PaidDivisorCover n N x.2) :
    deltaPair d n N cap w z L x = 0 := by
  have h := actual_fixed_rough_eq_off_paid_cover d n N cap hN w z x.2 hgood
  simp only [deltaPair,smallRoughPairCoefficient,h,sub_self]

/-- The common-carrier delta really is NEW original physical source minus
OLD original physical source, each on its own independently defined Q. -/
theorem delta_test_eq_two_original_sources (d : OriginalData) (n N cap : ℕ)
    (w z L : ℝ) (F : ℕ → ℝ) :
    (∑ q ∈ commonQ d n N cap w z, deltaRho d n N cap w z L q * F q) =
      (∑ q ∈ actualSmallRoughModuli ((compactPolicy8 d n (N : ℝ)) false) N cap w z,
        actualSmallRoughRho ((compactPolicy8 d n (N : ℝ)) false) N cap w z L q * F q) -
      (∑ q ∈ actualSmallRoughModuli ((policy8 d (N : ℝ)) false) N cap w z,
        rho d N cap w z L q * F q) := by
  let U := commonRough d n N cap w z
  have hnew : fixedRoughSupport ((compactPolicy8 d n (N : ℝ)) false) N cap w z ⊆ U :=
    Finset.subset_union_left
  have hold : fixedRoughSupport ((policy8 d (N : ℝ)) false) N cap w z ⊆ U :=
    Finset.subset_union_right
  have hn := sum_actualSmallRoughRho_mul_eq_on_common_carrier
    ((compactPolicy8 d n (N : ℝ)) false) N cap w z L U hnew F
  have ho := sum_actualSmallRoughRho_mul_eq_on_common_carrier
    ((policy8 d (N : ℝ)) false) N cap w z L U hold F
  rw [actualSmallRoughRho_eq_on_common_carrier _ N cap w z L U hnew] at hn
  rw [actualSmallRoughRho_eq_on_common_carrier _ N cap w z L U hold] at ho
  simp only [deltaRho,rho,sub_mul,Finset.sum_sub_distrib]
  exact congrArg₂ (fun a b : ℝ => a-b) hn ho

/-- This equality concerns the ACTUAL two physical coefficients, not two
aliases of a newly proposed delta coefficient. Every small factor and
every residual rough modulus remains in the original finite sum. -/
theorem actual_delta_test_localized (d : OriginalData) (n N cap : ℕ) (hN : 1 < N)
    (w z L : ℝ) (F : ℕ → ℝ) :
    (∑ q ∈ commonQ d n N cap w z, deltaRho d n N cap w z L q * F q) =
      ∑ x ∈ smallRoughPairs (actualSmallRosserSupport N cap w) (paidRough d n N cap w z),
        deltaPair d n N cap w z L x * F (x.1*x.2) := by
  let U := commonRough d n N cap w z
  have hnew : fixedRoughSupport ((compactPolicy8 d n (N : ℝ)) false) N cap w z ⊆ U :=
    Finset.subset_union_left
  have hold : fixedRoughSupport ((policy8 d (N : ℝ)) false) N cap w z ⊆ U :=
    Finset.subset_union_right
  have hsets : smallRoughPairs (actualSmallRosserSupport N cap w) (paidRough d n N cap w z) =
      (smallRoughPairs (actualSmallRosserSupport N cap w) U).filter
        (fun x => PaidDivisorCover n N x.2) := by
    ext x
    simp only [smallRoughPairs,paidRough,Finset.mem_product,Finset.mem_filter]
    tauto
  have hfull : (∑ q ∈ commonQ d n N cap w z, deltaRho d n N cap w z L q * F q) =
      ∑ x ∈ smallRoughPairs (actualSmallRosserSupport N cap w) U,
        deltaPair d n N cap w z L x * F (x.1*x.2) := by
    unfold deltaRho rho
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    rw [← actualSmallRoughRho_eq_on_common_carrier _ N cap w z L U hnew,
      ← actualSmallRoughRho_eq_on_common_carrier _ N cap w z L U hold]
    rw [sum_smallRoughRho_mul
      (fun _ he => actualSmallRosserSupport_smallPrimeSupportedAt N cap w he)
      (fun _ hb => commonRough_rough d n N cap w z hb),
      sum_smallRoughRho_mul
      (fun _ he => actualSmallRosserSupport_smallPrimeSupportedAt N cap w he)
      (fun _ hb => commonRough_rough d n N cap w z hb)]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    dsimp only [deltaPair]
    ring
  rw [hfull,hsets,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hbad : PaidDivisorCover n N x.2
  · simp only [if_pos hbad]
  · simp only [if_neg hbad,deltaPair_eq_zero_off_cover d n N cap hN w z L x hbad,zero_mul]

/-- Same-Q AP source after actual difference localization.  Its count
and exact coprime mean are untouched; no density-to-AP implication or
final PP hypothesis occurs in this declaration. -/
theorem actual_AP_difference_localized (d : OriginalData) (n N cap : ℕ) (hN : 1 < N)
    (w z L b T : ℝ) :
    realPhysicalDistributionError b N T (commonQ d n N cap w z) (deltaRho d n N cap w z L) =
      ∑ x ∈ smallRoughPairs (actualSmallRosserSupport N cap w) (paidRough d n N cap w z),
        deltaPair d n N cap w z L x *
          (realHalfProductCongruenceMass b N T (x.1*x.2) -
            realHalfProductCoprimeMass b N T (x.1*x.2)/(Nat.totient (x.1*x.2) : ℝ)) :=
  actual_delta_test_localized d n N cap hN w z L _

theorem two_actual_AP_sources_difference_localized (d : OriginalData) (n N cap : ℕ) (hN : 1 < N)
    (w z L b T : ℝ) :
    realPhysicalDistributionError b N T
        (actualSmallRoughModuli ((compactPolicy8 d n (N : ℝ)) false) N cap w z)
        (actualSmallRoughRho ((compactPolicy8 d n (N : ℝ)) false) N cap w z L) -
      realPhysicalDistributionError b N T (moduli d N cap w z) (rho d N cap w z L) =
      ∑ x ∈ smallRoughPairs (actualSmallRosserSupport N cap w) (paidRough d n N cap w z),
        deltaPair d n N cap w z L x *
          (realHalfProductCongruenceMass b N T (x.1*x.2) -
            realHalfProductCoprimeMass b N T (x.1*x.2)/(Nat.totient (x.1*x.2) : ℝ)) := by
  unfold realPhysicalDistributionError moduli
  rw [← delta_test_eq_two_original_sources d n N cap w z L
    (fun q => realHalfProductCongruenceMass b N T q -
      realHalfProductCoprimeMass b N T q/(Nat.totient q : ℝ))]
  exact actual_AP_difference_localized d n N cap hN w z L b T

end
end ImbalancedChen.P2OriginalElevenLocalizedFullQDifference
