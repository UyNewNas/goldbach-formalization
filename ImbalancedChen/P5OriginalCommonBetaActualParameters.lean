import ImbalancedChen.P5OriginalOrdinaryPresievedDensityComparison
import ImbalancedChen.P5OriginalOrdinaryPresievedQuotientUpper
import ImbalancedChen.P5ZU1011OriginalSixteenNearCapCommonSmallParameters

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Actual original selected-cell cutoffs, not abstract positive gate data,
choose the common beta budget. The analytic epsilon choice then occurs
before N, E and all selected tuples. It simultaneously supplies the true
common small prime wall, the positive physical small level, and the
delta/8 active-factor budget. The original count upper and actual physical
density comparison are both consequences for the SAME presievedSigma.
The all-prime native sigma is not changed or identified with it.
-/

namespace ImbalancedChen.P5Z.OriginalCommonBetaActualParameters

noncomputable section
open scoped BigOperators
open Classical
open U1011OriginalSixteenArithmeticProducts P5U1011JointOverlap
open U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenCommonSmallParameters (selectedCells mem_selectedCells owner_mem_selected)
open OriginalOrdinaryPresievedSigma OriginalOrdinaryPresievedDensityComparison
open OriginalOrdinaryPresievedQuotientUpper

def cellCutoff (n:ℕ) (eta:ℚ) (j:Grid n) : ℚ :=
  U1011OriginalSixteenNearCapBoxProfiles.cutoffExponent
    (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta

theorem selected_cutoff_pos {n:ℕ} (eta:ℚ) (heta:0<eta) (j:Grid n)
    (hj:j∈selectedCells n) : 0<cellCutoff n eta j := by
  have hcert := (U1011OriginalSixteenStaticNativeCompiler.boxPolicy_certificate
    (gridBox n j) ((mem_selectedCells j).mp hj)).2
  exact (U1011OriginalSixteenNearCapBoxProfiles.rational_parameters
    (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta
    (gridBox_valid n j) (gridBox_lower_positive n j 3) hcert heta).2.2.2.2.2.2

def cutoffValues (n:ℕ) (eta:ℚ) : Finset ℚ :=
  insert (1/8) ((selectedCells n).image (cellCutoff n eta))

theorem cutoffValues_nonempty (n:ℕ) (eta:ℚ) : (cutoffValues n eta).Nonempty :=
  ⟨1/8,Finset.mem_insert_self _ _⟩

def cutoffMin (n:ℕ) (eta:ℚ) : ℚ :=
  (cutoffValues n eta).min' (cutoffValues_nonempty n eta)

theorem cutoffMin_pos (n:ℕ) (eta:ℚ) (heta:0<eta) : 0<cutoffMin n eta := by
  have hm := Finset.min'_mem (cutoffValues n eta) (cutoffValues_nonempty n eta)
  rcases Finset.mem_insert.mp hm with h|h
  · change (cutoffValues n eta).min' (cutoffValues_nonempty n eta)=1/8 at h
    change 0<(cutoffValues n eta).min' (cutoffValues_nonempty n eta)
    rw [h]
    norm_num
  · obtain ⟨j,hj,heq⟩ := Finset.mem_image.mp h
    change 0<(cutoffValues n eta).min' (cutoffValues_nonempty n eta)
    rw [←heq]
    exact selected_cutoff_pos eta heta j hj

theorem cutoffMin_le_cell {n:ℕ} (eta:ℚ) (j:Grid n) (hj:j∈selectedCells n) :
    cutoffMin n eta≤cellCutoff n eta j := by
  apply Finset.min'_le
  exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨j,hj,rfl⟩))

/-- The finite actual cutoff budget and actual delta budget are fixed at
the physical precision, before the analytic beta choice or any N. -/
def epsilonBudget (n:ℕ) (eta:ℚ) (nu:ℝ) : ℝ :=
  min (1/8) (min ((cutoffMin n eta:ℝ)/nu)
    ((U1011OriginalSixteenNearCapCommonSmallParameters.ellMax n eta:ℝ)/(4*nu)))

theorem epsilonBudget_pos (n:ℕ) (eta:ℚ) (heta:0<eta) (nu:ℝ) (hnu:0<nu) :
    0<epsilonBudget n eta nu := by
  have hc : (0:ℝ)<cutoffMin n eta := by exact_mod_cast cutoffMin_pos n eta heta
  have he : (0:ℝ)<U1011OriginalSixteenNearCapCommonSmallParameters.ellMax n eta := by
    exact_mod_cast U1011OriginalSixteenNearCapCommonSmallParameters.ellMax_pos n eta heta
  exact lt_min (by norm_num) (lt_min (div_pos hc hnu) (div_pos he (by positivity)))

/-- All parameter conditions for the actual common beta pair are derived
from the actual selected owner. The upper cutoff is the ORIGINAL59/250
prime wall; no variable cutoff or delta bound is assumed. -/
theorem parameters_on_original_tuple {n N:ℕ} {eta:ℚ} {nu epsilon:ℝ}
    (hN:1<N) (heta:0<eta) (hnu:0<nu) (he:0<epsilon)
    (heBudget:epsilon<epsilonBudget n eta nu) {E:ℕ×ℕ→Prop} {t:Four}
    (ht:t∈tuples n N E) :
    1<(N:ℝ)^(nu*epsilon) ∧
      (N:ℝ)^(nu*epsilon^2)≤(N:ℝ)^(nu*epsilon) ∧
      (N:ℝ)^(nu*epsilon^2)≤U1011OriginalSixteenJointNearCapCompiler.Z n N eta t ∧
      U1011OriginalSixteenJointNearCapCompiler.Z n N eta t≤(N:ℝ)^(59/250:ℝ) ∧
      nu*epsilon≤(U1011OriginalSixteenNearCapBoxProfiles.delta
        (U1011OriginalSixteenStaticNativeCompiler.selectedPolicy n N t)
        (U1011OriginalSixteenStaticNativeCompiler.ownerBox n N t) eta:ℝ)/8 := by
  have htOrd := (Finset.mem_filter.mp ht).1
  have hs := (Finset.mem_filter.mp htOrd).1
  have htag : U1011OriginalSixteenStaticNativeCompiler.tupleTag n N t≠0 :=
    (Finset.mem_filter.mp htOrd).2
  have hj := owner_mem_selected htag
  have hcut : (cutoffMin n eta:ℝ)≤
      (U1011OriginalSixteenNearCapBoxProfiles.cutoffExponent
        (U1011OriginalSixteenStaticNativeCompiler.selectedPolicy n N t)
        (U1011OriginalSixteenStaticNativeCompiler.ownerBox n N t) eta:ℝ) := by
    exact_mod_cast cutoffMin_le_cell eta _ hj
  have hell : (U1011OriginalSixteenNearCapCommonSmallParameters.ellMax n eta:ℝ)≤
      (U1011OriginalSixteenNearCapBoxProfiles.delta
        (U1011OriginalSixteenStaticNativeCompiler.selectedPolicy n N t)
        (U1011OriginalSixteenStaticNativeCompiler.ownerBox n N t) eta:ℝ)/2 := by
    exact_mod_cast U1011OriginalSixteenNearCapCommonSmallParameters.ellMax_le_cell eta _ hj
  have he8 : epsilon≤1/8 := heBudget.le.trans (min_le_left _ _)
  have heCut : epsilon≤(cutoffMin n eta:ℝ)/nu :=
    heBudget.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have heEll : epsilon≤
      (U1011OriginalSixteenNearCapCommonSmallParameters.ellMax n eta:ℝ)/(4*nu) :=
    heBudget.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hcutLinear := (le_div_iff₀ hnu).mp heCut
  have hellLinear := (le_div_iff₀ (by positivity:0<4*nu)).mp heEll
  have heSquare : epsilon^2≤epsilon := by nlinarith
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hlevel := Real.one_lt_rpow hn (mul_pos hnu he)
  have hlevels : (N:ℝ)^(nu*epsilon^2)≤(N:ℝ)^(nu*epsilon) :=
    Real.rpow_le_rpow_of_exponent_le hn.le (mul_le_mul_of_nonneg_left heSquare hnu.le)
  have hw : (N:ℝ)^(nu*epsilon^2)≤U1011OriginalSixteenJointNearCapCompiler.Z n N eta t := by
    change (N:ℝ)^(nu*epsilon^2)≤(N:ℝ)^
      (U1011OriginalSixteenNearCapBoxProfiles.cutoffExponent
        (U1011OriginalSixteenStaticNativeCompiler.selectedPolicy n N t)
        (U1011OriginalSixteenStaticNativeCompiler.ownerBox n N t) eta:ℝ)
    apply Real.rpow_le_rpow_of_exponent_le hn.le
    exact (mul_le_mul_of_nonneg_left heSquare hnu.le).trans (by nlinarith [hcut])
  have hlegal := U1011OriginalSixteenJointNearCapCompiler.compiled_legality hN heta htOrd
  obtain ⟨h1,h2,h3,h4,h12,h23,h34⟩ := joint_carrier_order hs
  have hp14 : (t.1.1:ℝ)≤t.2.2 := by exact_mod_cast (h12.trans (h23.trans h34)).le
  have hzmax : U1011OriginalSixteenJointNearCapCompiler.Z n N eta t≤(N:ℝ)^(59/250:ℝ) :=
    (hlegal.2.2.1.trans hp14).trans (joint_band_and_mask hs).2.2.1.le
  exact ⟨hlevel,hlevels,hw,hzmax,by nlinarith [hell]⟩

/-- One genuinely constructed common beta pair supplies BOTH original
ordinary count upper and actual presieved physical density comparison,
with no cutoff-budget or small-factor-size assumption left to the caller.
The explicit native ordinary density and signed AP terms remain to bound. -/
theorem exists_actual_common_beta_model (n:ℕ) (eta:ℚ) (heta:0<eta)
    (nu reserve:ℝ) (hnu:0<nu) (hreserve:0<reserve) :
    ∃epsilon:ℝ,0<epsilon ∧ epsilon<epsilonBudget n eta nu ∧
      ∃N0:ℕ,2≤N0 ∧ ∀N:ℕ,N0≤N → Even N → ∀E:ℕ×ℕ→Prop,
        let w:=(N:ℝ)^(nu*epsilon^2)
        let B:=(N:ℝ)^(nu*epsilon)
        ((∑t∈tuples n N E,U11Adaptive.weight N t) ≤
          MathlibNt.SieveTheory.BombieriVinogradov.trueLogarithmicIntegral N*density n N eta w B E +
            signedAP n N eta w B E-signedCentre n N eta w B E) ∧
        (physicalDensitySum (physicalSupport n N eta w E) (presievedSigma n N eta w B E) ≤
          (∑t∈tuples n N E,(1/(Nat.totient (fullPrefix t):ℝ))*
            actualSmallRosserPlusDensity N (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
              (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
              (U1011OriginalSixteenJointNearCapCompiler.D n N eta t)) +
          (reserve*singularSeries N/Real.log (N:ℝ))*∑t∈tuples n N E,1/(Nat.totient (fullPrefix t):ℝ)) ∧
        ∀t∈tuples n N E,nu*epsilon≤
          (U1011OriginalSixteenNearCapBoxProfiles.delta
            (U1011OriginalSixteenStaticNativeCompiler.selectedPolicy n N t)
            (U1011OriginalSixteenStaticNativeCompiler.ownerBox n N t) eta:ℝ)/8 := by
  have hr : 0<(59/250:ℝ)/nu := div_pos (by norm_num) hnu
  obtain ⟨epsilon,he,_he8,heBudget,_her,N0,hN0,hcomparison⟩ :=
    exists_same_presieved_sigma_density_comparison n eta heta nu ((59/250:ℝ)/nu) reserve
      (epsilonBudget n eta nu) hnu hr hreserve (epsilonBudget_pos n eta heta nu hnu)
  refine ⟨epsilon,he,heBudget,N0,hN0,?_⟩
  intro N hN hEven E
  have hN1 : 1<N := by omega
  have hn : (1:ℝ)<N := by exact_mod_cast hN1
  have he8 : epsilon≤1/8 := heBudget.le.trans (min_le_left _ _)
  have heSquare : epsilon^2≤epsilon := by nlinarith
  have hB : 1<(N:ℝ)^(nu*epsilon) := Real.one_lt_rpow hn (mul_pos hnu he)
  have hwB : (N:ℝ)^(nu*epsilon^2)≤(N:ℝ)^(nu*epsilon) :=
    Real.rpow_le_rpow_of_exponent_le hn.le (mul_le_mul_of_nonneg_left heSquare hnu.le)
  have hp (t:Four) (ht:t∈tuples n N E) :=
    parameters_on_original_tuple hN1 heta hnu he heBudget ht
  have hscale : nu*((59/250:ℝ)/nu)=59/250 := by field_simp [hnu.ne']
  have hdensity := hcomparison N hN hEven E (by
    intro t ht
    exact ⟨(hp t ht).2.2.1,by simpa only [hscale] using (hp t ht).2.2.2.1⟩)
  dsimp only
  exact ⟨original_same_presieved_sigma_upper hN1 heta hB hwB E (fun t ht=>(hp t ht).2.2.1),
    hdensity,fun t ht=>(hp t ht).2.2.2.2⟩

end
end ImbalancedChen.P5Z.OriginalCommonBetaActualParameters
