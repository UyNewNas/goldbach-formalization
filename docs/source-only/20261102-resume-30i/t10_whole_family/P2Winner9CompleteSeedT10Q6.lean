import ImbalancedChen.P2Winner9CompleteSeedMomentDecoder
import ImbalancedChen.P2Winner9SelectedRowIntegralFloor
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
One analytic chain for every actual original row. All polynomial moments,
normalization and directed rounding are independent of the real enclosure.
The older factorwise log branch is not inferred from the common-affine bound.
-/
namespace ImbalancedChen.P2Winner9CompleteSeedT10Q6
noncomputable section
open Set MeasureTheory
open scoped BigOperators
open ImbalancedChen.P2Winner9CompleteSeedData
open ImbalancedChen.P2Winner9CompleteSeedPositiveDomains
open ImbalancedChen.P2Winner9SelectedRowRealJacobian
open ImbalancedChen.P2Winner9SelectedRowIntegerScales
open ImbalancedChen.P2Winner9SelectedRowAnalyticCaps
open ImbalancedChen.P2Winner9PhysicalAffineTransfer
open ImbalancedChen.P2Winner9PhysicalVertexInterpolation
open ImbalancedChen.P2Winner9BarycentricMixedDegreeOne
open ImbalancedChen.P2Winner9CompleteSeedMomentDecoder
open ImbalancedChen.P2Winner9T10TailJensen
open ImbalancedChen.P2Winner9SelectedAnalyticRemainders
open ImbalancedChen.P2PositiveAffineSimplexLogJensenSourceOnly

-- Locally qualify the all-row decoder rather than the old Fin2 definitions.
local notation "muQ" => P2Winner9CompleteSeedMomentDecoder.means
local notation "uQ" => P2Winner9CompleteSeedMomentDecoder.upper
local notation "loQ" => P2Winner9CompleteSeedMomentDecoder.pLower
local notation "vQ" => P2Winner9CompleteSeedMomentDecoder.transverseUpper
local notation "yQ" => P2Winner9CompleteSeedMomentDecoder.yUpper

def μ (i : RowIndex) : Measure Ambient := volume.restrict (actualSupport i)
def ν (i : RowIndex) : Measure Ambient := weightedProbability (μ i) physicalGap
def U (i : RowIndex) : ℝ := (uQ i : ℝ)
def P (i : RowIndex) (z : Ambient) : ℝ := physicalP (fun j => (muQ i j : ℝ)) z
def Y (i : RowIndex) (z : Ambient) : ℝ := physicalY (fun j => (muQ i j : ℝ)) (U i) z
def A (i : RowIndex) (j : Fin 10) (z : Ambient) : ℝ :=
  normalizedFactor (fun k => (muQ i k : ℝ)) j z
def V (i : RowIndex) (j : Fin 10) : ℝ := (vQ i j : ℝ)
def B (i : RowIndex) (j : Fin 10) (z : Ambient) : ℝ := A i j z - P i z
def invP10 (i : RowIndex) (z : Ambient) : ℝ := 1 / (P i z)^10
def prodInv (i : RowIndex) (z : Ambient) : ℝ := 1 / ∏ j : Fin 10, A i j z

theorem U_pos (i : RowIndex) : 0 < U i := by exact_mod_cast (all_source_facts i).upper_pos

theorem support_caps (i : RowIndex) {z : Ambient} (hz : z ∈ actualSupport i) :
    (loQ i : ℝ) ≤ P i z ∧ P i z ≤ U i ∧
      ∀ j : Fin 10, 0 < A i j z ∧ A i j z ≤ V i j ∧ P i z ≤ V i j := by
  have h := all_source_facts i
  have ha (j : Fin 10) : 0 < A i j z :=
    div_pos ((all_actual_support_positive i hz).2 j).2
      (by exact_mod_cast all_original_means_positive i j)
  rcases hz with ⟨x, hx, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [P, physicalP_vertexMap]
    apply affine_lower hx
    intro k
    rw [← rawP_cast]
    exact_mod_cast (h.vertex_caps k).1
  · rw [P, physicalP_vertexMap]
    apply affine_upper hx
    intro k
    rw [← rawP_cast]
    exact_mod_cast (h.vertex_caps k).2.1
  · intro j
    refine ⟨ha j, ?_, ?_⟩
    · rw [A, normalizedFactor_vertexMap]
      apply affine_upper hx
      intro k
      change physicalFactor j (realVertices (physicalVertices i) k) / (muQ i j : ℝ) ≤ _
      rw [← rawFactor_cast]
      exact_mod_cast ((h.vertex_caps k).2.2 j).1
    · rw [P, physicalP_vertexMap]
      apply affine_upper hx
      intro k
      rw [← rawP_cast]
      exact_mod_cast ((h.vertex_caps k).2.2 j).2

theorem P_pos (i : RowIndex) {z : Ambient} (hz : z ∈ actualSupport i) : 0 < P i z :=
  lt_of_lt_of_le (by exact_mod_cast (all_source_facts i).lower_pos) (support_caps i hz).1

theorem Y_mem (i : RowIndex) {z : Ambient} (hz : z ∈ actualSupport i) :
    Y i z ∈ Icc (0 : ℝ) (yQ i : ℝ) := by
  have h := support_caps i hz
  have hu := U_pos i
  have he : (yQ i : ℝ) = 1 - (loQ i : ℝ) / U i := by simp [yUpper, U]
  rw [he]
  change 0 ≤ 1 - P i z / U i ∧ 1 - P i z / U i ≤ _
  constructor
  · exact sub_nonneg.mpr ((div_le_one hu).2 h.2.1)
  · exact sub_le_sub_left ((div_le_div_iff_of_pos_right hu).2 h.1) 1

theorem q_lt_one (i : RowIndex) : (yQ i : ℝ) < 1 := by
  have hu := U_pos i
  have hl : (0 : ℝ) < (loQ i : ℝ) := by exact_mod_cast (all_source_facts i).lower_pos
  have he : (yQ i : ℝ) = 1 - (loQ i : ℝ) / U i := by simp [yUpper, U]
  rw [he]
  linarith [div_pos hl hu]

theorem Y_lt_one (i : RowIndex) {z : Ambient} (hz : z ∈ actualSupport i) : Y i z < 1 :=
  lt_of_le_of_lt (Y_mem i hz).2 (q_lt_one i)

theorem μ_support (i : RowIndex) : ∀ᵐ z ∂μ i, z ∈ actualSupport i :=
  ae_restrict_mem (all_actual_support_measurable i)
theorem gap_nonneg_ae (i : RowIndex) : ∀ᵐ z ∂μ i, 0 ≤ physicalGap z :=
  (μ_support i).mono (fun z hz => (all_actual_support_positive i hz).1)
theorem gap_integrable (i : RowIndex) : Integrable physicalGap (μ i) :=
  continuous_physicalGap.continuousOn.integrableOn_compact (all_actual_support_compact i)

instance row_probability (i : RowIndex) : IsProbabilityMeasure (ν i) :=
  weightedProbability_isProbability (μ i) physicalGap (gap_integrable i)
    (gap_nonneg_ae i) (gapMass_pos i)

theorem ν_support (i : RowIndex) : ∀ᵐ z ∂ν i, z ∈ actualSupport i :=
  (withDensity_absolutelyContinuous _ _).ae_le (μ_support i)

theorem weighted_integral (i : RowIndex) (f : Ambient → ℝ) :
    (∫ z, f z ∂ν i) = (∫ z in actualSupport i, physicalGap z * f z) / gapMass i :=
  integral_weightedProbability (μ i) physicalGap continuous_physicalGap.measurable
    (gap_nonneg_ae i) (gapMass_pos i) f

theorem weighted_integrable (i : RowIndex) {f : Ambient → ℝ}
    (hf : ContinuousOn f (actualSupport i)) : Integrable f (ν i) := by
  apply integrable_weightedProbability (μ i) physicalGap
    continuous_physicalGap.measurable (gap_nonneg_ae i) (gapMass_pos i)
  exact (continuous_physicalGap.continuousOn.mul hf).integrableOn_compact
    (all_actual_support_compact i)

theorem normalized_continuous (i : RowIndex) (j : Fin 10) : Continuous (A i j) :=
  (continuous_physicalFactor j).div_const _
theorem P_continuous (i : RowIndex) : Continuous (P i) := by
  have hn := normalized_continuous i
  change Continuous (fun z => (∑ j : Fin 10, A i j z) / 10)
  fun_prop
theorem Y_continuous (i : RowIndex) : Continuous (Y i) :=
  continuous_const.sub ((P_continuous i).div_const _)
theorem B_continuous (i : RowIndex) (j : Fin 10) : Continuous (B i j) :=
  (normalized_continuous i j).sub (P_continuous i)

theorem fY_continuousOn (i : RowIndex) :
    ContinuousOn (fun z => 1 / (1 - Y i z)^10) (actualSupport i) := by
  apply continuous_const.continuousOn.div
    ((continuous_const.sub (Y_continuous i)).pow 10).continuousOn
  intro z hz
  exact pow_ne_zero _ (ne_of_gt (sub_pos.mpr (Y_lt_one i hz)))
theorem invP10_continuousOn (i : RowIndex) : ContinuousOn (invP10 i) (actualSupport i) := by
  apply continuous_const.continuousOn.div ((P_continuous i).pow 10).continuousOn
  intro z hz
  exact pow_ne_zero _ (P_pos i hz).ne'
theorem prodInv_continuousOn (i : RowIndex) : ContinuousOn (prodInv i) (actualSupport i) := by
  have hp : Continuous (fun z => ∏ j : Fin 10, A i j z) := by
    have ha := normalized_continuous i
    fun_prop
  apply continuous_const.continuousOn.div hp.continuousOn
  intro z hz
  exact ne_of_gt (Finset.prod_pos (fun j _ => (support_caps i hz).2.2 j |>.1))

theorem integral_Y_pow (i : RowIndex) (k : ℕ) :
    (∫ z, (Y i z)^k ∂ν i) = (powerMoment i k : ℝ) := by
  rw [weighted_integral]
  exact actual_power_mean i k

theorem integral_Y (i : RowIndex) : (∫ z, Y i z ∂ν i) = 1 - 1 / U i := by
  have h := integral_Y_pow i 1
  rw [(all_source_facts i).y_mean] at h
  simpa [U] using h

theorem invP10_scaled (i : RowIndex) {z : Ambient} (hz : z ∈ actualSupport i) :
    invP10 i z = (1 / (U i)^10) * (1 / (1 - Y i z)^10) := by
  have hp := (P_pos i hz).ne'
  have hu := (U_pos i).ne'
  have hy : 1 - Y i z = P i z / U i := by unfold Y physicalY P; ring
  rw [hy]
  unfold invP10
  field_simp [hu, hp] <;> ring

/-- Tail convexity, real probability normalization and actual power moments
prove the T10 gap simultaneously for the entire original family. -/
theorem actual_T10_lower (i : RowIndex) :
    1 + (t10 i : ℝ) ≤ ∫ z, invP10 i z ∂ν i := by
  have hgap := probability_T10_gap (ν i) (Y i) (q_lt_one i)
    ((ν_support i).mono (fun z hz => Y_mem i hz))
    (weighted_integrable i (Y_continuous i).continuousOn)
    (weighted_integrable i (fY_continuousOn i))
    (fun k _ => weighted_integrable i ((Y_continuous i).pow k).continuousOn)
  have hscale : 0 ≤ 1 / (U i)^10 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hgap hscale
  have hI : (∫ z, invP10 i z ∂ν i) =
      (1 / (U i)^10) * ∫ z, 1 / (1 - Y i z)^10 ∂ν i := by
    rw [← integral_const_mul]
    exact integral_congr_ae ((ν_support i).mono (fun z hz => invP10_scaled i hz))
  have hunit : (1 / (U i)^10) * (1 / (1 - ∫ z, Y i z ∂ν i)^10) = 1 := by
    rw [integral_Y]
    have hu := (U_pos i).ne'
    field_simp [hu] <;> ring
  rw [← hI, mul_add, hunit] at hscaled
  simp_rw [integral_Y_pow] at hscaled
  have hMean : (∫ z, Y i z ∂ν i) = (powerMoment i 1 : ℝ) := by
    simpa only [pow_one] using integral_Y_pow i 1
  rw [hMean] at hscaled
  simpa [t10, U] using hscaled

def S (i : RowIndex) (z : Ambient) : ℝ :=
  ∑ j : Fin 10, (B i j z)^2 / (2 * (V i j)^2)
def cTerm (i : RowIndex) (j : Fin 10) (k : Fin 7) (z : Ambient) : ℝ :=
  (((9 + k.val).choose k.val : ℝ) * (Y i z)^k.val * (B i j z)^2) /
    (2 * (V i j)^2 * (U i)^10)
def C6 (i : RowIndex) (z : Ambient) : ℝ := ∑ j : Fin 10, ∑ k : Fin 7, cTerm i j k z

theorem C6_factorization (i : RowIndex) (z : Ambient) :
    C6 i z = (1 / (U i)^10) * P2Winner9SelectedRowIntegralFloor.binomial6 (Y i z) * S i z := by
  unfold C6 S
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [P2Winner9SelectedRowIntegralFloor.binomial6, Finset.sum_mul, Finset.mul_sum, cTerm]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem pointwise_product_Q6 (i : RowIndex) {z : Ambient}
    (hz : z ∈ actualSupport i) : invP10 i z + C6 i z ≤ prodInv i z := by
  have hc := support_caps i hz
  have hq := reciprocal_product_quadratic (fun j => A i j z) (V i) (P i z)
    (fun j => (hc.2.2 j).1) (P_pos i hz)
    (fun j => (hc.2.2 j).2.1) (fun j => (hc.2.2 j).2.2)
    (by unfold A P physicalP; ring)
  have hquad : invP10 i z * (1 + S i z) ≤ prodInv i z := by
    convert hq using 1 <;> dsimp [invP10, S, B, prodInv] <;> ring
  have hbin := mul_le_mul_of_nonneg_left
    (P2Winner9SelectedRowIntegralFloor.binomial6_minorant (Y_mem i hz).1 (Y_lt_one i hz))
    (by positivity : (0 : ℝ) ≤ 1 / (U i)^10)
  rw [← invP10_scaled i hz] at hbin
  have hS : 0 ≤ S i z :=
    Finset.sum_nonneg (fun j _ => div_nonneg (sq_nonneg _) (by positivity))
  have hcorr := mul_le_mul_of_nonneg_right hbin hS
  rw [C6_factorization]
  nlinarith

theorem cTerm_continuous (i : RowIndex) (j : Fin 10) (k : Fin 7) :
    Continuous (cTerm i j k) := by
  have hY := Y_continuous i
  have hB := B_continuous i j
  unfold cTerm
  fun_prop

theorem moment_probability (i : RowIndex) (j : Fin 10) (k : Fin 7) :
    (∫ z, (Y i z)^k.val * (B i j z)^2 ∂ν i) = (mixedMoment i j k.val : ℝ) := by
  rw [weighted_integral]
  exact actual_mixed_mean i j k.val

theorem integral_cTerm (i : RowIndex) (j : Fin 10) (k : Fin 7) :
    (∫ z, cTerm i j k z ∂ν i) = (mixedTerm i j k : ℝ) := by
  have he (z : Ambient) : cTerm i j k z =
      ((((9 + k.val).choose k.val : ℝ) / (2 * (V i j)^2 * (U i)^10)) *
        ((Y i z)^k.val * (B i j z)^2)) := by unfold cTerm; ring
  simp_rw [he]
  rw [integral_const_mul, moment_probability]
  simp [mixedTerm, V, U] <;> ring

theorem C6_integrable (i : RowIndex) : Integrable (C6 i) (ν i) := by
  apply weighted_integrable i
  unfold C6
  have hc := cTerm_continuous i
  fun_prop

theorem integral_C6 (i : RowIndex) : (∫ z, C6 i z ∂ν i) = (q6 i : ℝ) := by
  have hi (j : Fin 10) (k : Fin 7) : Integrable (cTerm i j k) (ν i) :=
    weighted_integrable i (cTerm_continuous i j k).continuousOn
  have hj (j : Fin 10) : Integrable (fun z => ∑ k : Fin 7, cTerm i j k z) (ν i) :=
    integrable_finsetSum Finset.univ (fun k _ => hi j k)
  unfold C6
  rw [integral_finsetSum Finset.univ (fun j _ => hj j)]
  simp_rw [integral_finsetSum Finset.univ (fun k _ => hi _ k), integral_cTerm]
  simp [q6]

/-- Actual same-row enclosure. There is no row-enclosure premise. -/
theorem actual_normalized_enclosure (i : RowIndex) :
    1 + (t10 i : ℝ) + (q6 i : ℝ) ≤ ∫ z, prodInv i z ∂ν i := by
  have hiP := weighted_integrable i (invP10_continuousOn i)
  have hiC := C6_integrable i
  have hiA := weighted_integrable i (prodInv_continuousOn i)
  have h := integral_mono_ae (hiP.add hiC) hiA
    ((ν_support i).mono (fun z hz => pointwise_product_Q6 i hz))
  rw [integral_add hiP hiC, integral_C6] at h
  linarith [actual_T10_lower i]

def meanProduct (i : RowIndex) : ℝ := ∏ j : Fin 10, (muQ i j : ℝ)
theorem meanProduct_pos (i : RowIndex) : 0 < meanProduct i :=
  Finset.prod_pos (fun j _ => by exact_mod_cast all_original_means_positive i j)

theorem jensen_pos (i : RowIndex) : (0 : ℝ) < ((entry i).jensen : ℝ) := by
  rw [actual_Jensen_factor]
  exact div_pos (mul_pos (by norm_num) (gapMass_pos i)) (meanProduct_pos i)

/-- Factor4 and the ten original denominator factors are preserved. -/
theorem density_probability_normalization (i : RowIndex) :
    (∫ z in actualSupport i, physicalUpperIntegrand z) =
      ((entry i).jensen : ℝ) * (∫ z, prodInv i z ∂ν i) := by
  rw [actual_Jensen_factor, weighted_integral]
  have hμ := (meanProduct_pos i).ne'
  have hm := (gapMass_pos i).ne'
  have he : (∫ z in actualSupport i, physicalGap z * prodInv i z) =
      (meanProduct i / 4) * ∫ z in actualSupport i, physicalUpperIntegrand z := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun (all_actual_support_measurable i)
    intro z hz
    have hF : (∏ j : Fin 10, physicalFactor j z) ≠ 0 :=
      ne_of_gt (Finset.prod_pos (fun j _ => ((all_actual_support_positive i hz).2 j).2))
    unfold prodInv A normalizedFactor physicalUpperIntegrand meanProduct
    rw [Finset.prod_div_distrib]
    field_simp [hμ, hF] <;> ring
  rw [he]
  change _ = (4 * gapMass i / meanProduct i) * ((meanProduct i / 4) * _ / gapMass i)
  field_simp [hμ, hm] <;> ring

theorem actual_physical_enclosure (i : RowIndex) :
    ((entry i).jensen : ℝ) * (1 + (t10 i : ℝ) + (q6 i : ℝ)) ≤
      ∫ z in actualSupport i, physicalUpperIntegrand z := by
  rw [density_probability_normalization]
  exact mul_le_mul_of_nonneg_left (actual_normalized_enclosure i) (jensen_pos i).le

/-- The independently decoded TWO rounding stages precede the actual
integral theorem. No numerical floor execution or enclosure assumption. -/
theorem all_original_raw_floors (i : RowIndex) :
    ((entry i).mixedRaw : ℝ) / (q96 : ℝ) ≤
      ∫ z in actualSupport i, physicalUpperIntegrand z := by
  have ht : ((entry i).mixedTotalQ80 : ℝ) / (q80 : ℝ) ≤ (t10 i : ℝ) + (q6 i : ℝ) := by
    exact_mod_cast (all_field_facts i).mixed_total.1
  have hr : ((entry i).mixedRaw : ℝ) / (q96 : ℝ) ≤
      ((entry i).jensen : ℝ) * (1 + ((entry i).mixedTotalQ80 : ℝ) / (q80 : ℝ)) := by
    exact_mod_cast (all_field_facts i).mixed_raw.1
  have h := mul_le_mul_of_nonneg_left (add_le_add_left ht 1) (jensen_pos i).le
  exact le_trans hr (le_trans (by simpa only [add_assoc] using h) (actual_physical_enclosure i))

/-- Q6 raw dominates the older Q0 raw in the original producer; all actual
curvature raw floors therefore also receive same-support analytic soundness. -/
theorem all_original_curvature_raw_floors (i : RowIndex) :
    ((entry i).curvatureRaw : ℝ) / (q96 : ℝ) ≤
      ∫ z in actualSupport i, physicalUpperIntegrand z := by
  have h : ((entry i).curvatureRaw : ℝ) ≤ (entry i).mixedRaw :=
    by exact_mod_cast (all_field_facts i).raw_monotone
  exact le_trans (div_le_div_of_nonneg_right h (by norm_num [q96])) (all_original_raw_floors i)

end
end ImbalancedChen.P2Winner9CompleteSeedT10Q6

