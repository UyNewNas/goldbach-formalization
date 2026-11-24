import ImbalancedChen.P2Winner9ActualRowProbability
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The true T10 Jensen-gap bound and actual Q6 physical moments are combined
with the original pointwise reciprocal-product quadratic inequality.
The literal Jensen factor then converts the probability inequality into
the real physical density integral. Original directed raw row floors are
consumed last. No final enclosure or gain is assumed.
-/

namespace ImbalancedChen.P2Winner9SelectedRowIntegralFloor

noncomputable section

open Set MeasureTheory
open scoped BigOperators
open ImbalancedChen.P2Winner9SelectedRowRealJacobian
open ImbalancedChen.P2Winner9SelectedRowAnalyticCaps
open ImbalancedChen.P2Winner9SelectedAnalyticRemainders
open ImbalancedChen.P2Winner9SelectedAllMixedMoments
open ImbalancedChen.P2Winner9SelectedPhysicalMeans
open ImbalancedChen.P2Winner9SelectedPhysicalQ6Floor
open ImbalancedChen.P2Winner9ActualT10Moments
open ImbalancedChen.P2Winner9ActualRowProbability
open ImbalancedChen.P2Winner9PhysicalAffineTransfer
open ImbalancedChen.P2Winner9CurvatureFullExactAssembly
open ImbalancedChen.P2Winner9CurvatureExactMomentFloor
open ImbalancedChen.P2Winner9MixedDegreeSixExactAssembly

def A (r : Fin 2) (j : Fin 10) (z : Ambient) : ℝ :=
  normalizedFactor (fun k => (means r k : ℝ)) j z

def V (r : Fin 2) (j : Fin 10) : ℝ := ((data r).maxima j : ℝ) / (data r).L

def B (r : Fin 2) (j : Fin 10) (z : Ambient) : ℝ := A r j z - P r z

def prodInv (r : Fin 2) (z : Ambient) : ℝ := 1 / ∏ j : Fin 10, A r j z

def S (r : Fin 2) (z : Ambient) : ℝ :=
  ∑ j : Fin 10, (B r j z)^2 / (2 * (V r j)^2)

def binomial6 (y : ℝ) : ℝ := ∑ k : Fin 7, ((9 + k.val).choose k.val : ℝ) * y^k.val

def cTerm (r : Fin 2) (j : Fin 10) (k : Fin 7) (z : Ambient) : ℝ :=
  (((9 + k.val).choose k.val : ℝ) * (Y r z)^k.val * (B r j z)^2) /
    (2 * (V r j)^2 * (U r)^10)

def C6 (r : Fin 2) (z : Ambient) : ℝ := ∑ j : Fin 10, ∑ k : Fin 7, cTerm r j k z

theorem U_typed (r : Fin 2) : U r = ((data r).U : ℝ) / (data r).L := by
  fin_cases r <;> simp [U, upper, data, P2Winner9SelectedRowIntegerScales.Row21.upper,
    P2Winner9SelectedRowIntegerScales.Row22.upper]

theorem binomial6_minorant {y : ℝ} (hy : 0 ≤ y) (hy1 : y < 1) :
    binomial6 y ≤ 1 / (1 - y)^10 := by
  have hid : (1 - y)^10 * binomial6 y +
      y^7 * (∑ j ∈ Finset.range 10, ((6 + j).choose j : ℝ) * (1 - y)^j) = 1 := by
    norm_num [binomial6, Fin.sum_univ_succ, Finset.sum_range_succ]
    ring
  have hr : 0 ≤ y^7 * (∑ j ∈ Finset.range 10,
      ((6 + j).choose j : ℝ) * (1 - y)^j) := by
    apply mul_nonneg (pow_nonneg hy _)
    exact Finset.sum_nonneg (fun j _ =>
      mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (sub_nonneg.mpr hy1.le) _))
  apply (le_div_iff₀ (by positivity : 0 < (1 - y)^10)).2
  nlinarith

theorem C6_factorization (r : Fin 2) (z : Ambient) :
    C6 r z = (1 / (U r)^10) * binomial6 (Y r z) * S r z := by
  unfold C6 S
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [binomial6, Finset.sum_mul, Finset.mul_sum, cTerm]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem S_nonneg (r : Fin 2) (z : Ambient) : 0 ≤ S r z :=
  Finset.sum_nonneg (fun j _ => div_nonneg (sq_nonneg _) (by positivity))

/-- The binomial correction is inserted only into the nonnegative
transverse term; the full P^-10 is retained for the T10 Jensen-gap bound. -/
theorem pointwise_product_Q6 (r : Fin 2) {z : Ambient}
    (hz : z ∈ sourceSupport (vertices r)) : invP10 r z + C6 r z ≤ prodInv r z := by
  have hq := actual_row_product_quadratic r hz
  have hquad : invP10 r z * (1 + S r z) ≤ prodInv r z := by
    convert hq using 1 <;>
      simp [invP10, S, B, A, P, V, transverseUpper, prodInv, physicalDeviation,
        div_eq_mul_inv] <;> ring
  have hy := Y_mem r hz
  have hbin := mul_le_mul_of_nonneg_left
    (binomial6_minorant hy.1 (Y_lt_one r hz))
    (by positivity : (0 : ℝ) ≤ 1 / (U r)^10)
  rw [← invP10_scaled r hz] at hbin
  have hcorr := mul_le_mul_of_nonneg_right hbin (S_nonneg r z)
  rw [C6_factorization]
  nlinarith

theorem B_continuous (r : Fin 2) (j : Fin 10) : Continuous (B r j) :=
  (normalized_continuous r j).sub (P_continuous r)

theorem cTerm_continuous (r : Fin 2) (j : Fin 10) (k : Fin 7) :
    Continuous (cTerm r j k) := by
  have hY := Y_continuous r
  have hB := B_continuous r j
  unfold cTerm
  fun_prop

theorem C6_integrable (r : Fin 2) : Integrable (C6 r) (ν r) := by
  apply weighted_integrable r
  unfold C6
  have hc := cTerm_continuous r
  fun_prop

theorem prodInv_continuousOn (r : Fin 2) :
    ContinuousOn (prodInv r) (sourceSupport (vertices r)) := by
  have hp : Continuous (fun z => ∏ j : Fin 10, A r j z) := by
    have ha := normalized_continuous r
    unfold A
    fun_prop
  apply continuous_const.continuousOn.div hp.continuousOn
  intro z hz
  exact ne_of_gt (Finset.prod_pos (fun j _ => ((actual_support_caps r hz).2.2.2.2 j).1))

theorem moment_probability (r : Fin 2) (j : Fin 10) (k : Fin 7) :
    (∫ z, (Y r z)^k.val * (B r j z)^2 ∂ν r) =
      actualMixedExpectationK (data r) j k.val := by
  rw [weighted_integral]
  have he : (∫ z in sourceSupport (vertices r),
      physicalGap z * ((Y r z)^k.val * (B r j z)^2)) =
      ∫ z in sourceSupport (vertices r),
        physicalMixedK (fun i => (means r i : ℝ)) (upper r : ℝ) j k.val z := by
    apply setIntegral_congr_fun (sourceSupport_measurable (vertices r) (row_det_ne_zero r))
    intro z hz
    simp [physicalMixedK, B, A, P, Y, U, physicalDeviation]
    ring
  rw [he]
  exact physical_mixed_expectation r j k

theorem integral_cTerm (r : Fin 2) (j : Fin 10) (k : Fin 7) :
    (∫ z, cTerm r j k z ∂ν r) = (value (mixedTerm (data r) j k) : ℝ) := by
  have he (z : Ambient) : cTerm r j k z =
      ((((9 + k.val).choose k.val : ℝ) / (2 * (V r j)^2 * (U r)^10)) *
        ((Y r z)^k.val * (B r j z)^2)) := by
    unfold cTerm
    ring
  simp_rw [he]
  rw [integral_const_mul, moment_probability]
  have h := actual_row_mixed_term r j k
  rw [← U_typed] at h
  simpa only [V, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h.symm

theorem integral_C6 (r : Fin 2) : (∫ z, C6 r z ∂ν r) = (value (q6 (data r)) : ℝ) := by
  have hi (j : Fin 10) (k : Fin 7) : Integrable (cTerm r j k) (ν r) :=
    weighted_integrable r (cTerm_continuous r j k).continuousOn
  have hj (j : Fin 10) : Integrable (fun z => ∑ k : Fin 7, cTerm r j k z) (ν r) :=
    integrable_finsetSum Finset.univ (fun k _ => hi j k)
  unfold C6
  rw [integral_finsetSum Finset.univ (fun j _ => hj j)]
  simp_rw [integral_finsetSum Finset.univ (fun k _ => hi _ k), integral_cTerm]
  rw [q6_value]
  simp [mixedTerms, List.map_flatten, List.sum_flatten]

/-- Genuine normalized analytic enclosure on the same actual row. -/
theorem actual_normalized_enclosure (r : Fin 2) :
    1 + (value (t10 (data r)) : ℝ) + (value (q6 (data r)) : ℝ) ≤
      ∫ z, prodInv r z ∂ν r := by
  have hiP := weighted_integrable r (invP10_continuousOn r)
  have hiC := C6_integrable r
  have hiA := weighted_integrable r (prodInv_continuousOn r)
  have h := integral_mono_ae (hiP.add hiC) hiA
    ((ν_support r).mono (fun z hz => pointwise_product_Q6 r hz))
  rw [integral_add hiP hiC, integral_C6] at h
  linarith [actual_T10_lower r]

def meanProduct (r : Fin 2) : ℝ := ∏ j : Fin 10, (means r j : ℝ)

theorem meanProduct_pos (r : Fin 2) : 0 < meanProduct r :=
  Finset.prod_pos (fun j _ => by exact_mod_cast (actual_vertex_guards r).2.2.2.1 j |>.1)

/-- Exact physical integral normalization, retaining factor4 and all ten
true physical factors. The Jensen factor is the actual mass/mean product. -/
theorem density_probability_normalization (r : Fin 2) :
    (∫ z in sourceSupport (vertices r), physicalUpperIntegrand z) =
      (((data r).jensenNum : ℝ) / (data r).jensenDen) *
        (∫ z, prodInv r z ∂ν r) := by
  rw [actual_Jensen_factor, weighted_integral]
  have hμ := (meanProduct_pos r).ne'
  have hm := (gapMass_pos r).ne'
  have he : (∫ z in sourceSupport (vertices r), physicalGap z * prodInv r z) =
      (meanProduct r / 4) * ∫ z in sourceSupport (vertices r), physicalUpperIntegrand z := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun (sourceSupport_measurable (vertices r) (row_det_ne_zero r))
    intro z hz
    have hF : (∏ j : Fin 10, physicalFactor j z) ≠ 0 :=
      ne_of_gt (Finset.prod_pos (fun j _ => ((actual_support_caps r hz).2.1 j).2))
    unfold prodInv A normalizedFactor physicalUpperIntegrand meanProduct
    rw [Finset.prod_div_distrib]
    field_simp [hμ, hF] <;> ring
  rw [he]
  change _ = (4 * gapMass r / meanProduct r) *
    ((meanProduct r / 4) * _ / gapMass r)
  field_simp [hμ, hm] <;> ring

/-- Actual selected-row density enclosure; no hEnclosure/hCertificate
premise is used. All finite source checks remain separately unexecuted. -/
theorem actual_physical_enclosure (r : Fin 2) :
    (((data r).jensenNum : ℝ) / (data r).jensenDen) *
      (1 + (value (t10 (data r)) : ℝ) + (value (q6 (data r)) : ℝ)) ≤
      ∫ z in sourceSupport (vertices r), physicalUpperIntegrand z := by
  have hJ : 0 ≤ ((data r).jensenNum : ℝ) / (data r).jensenDen := by positivity
  have h := mul_le_mul_of_nonneg_left (actual_normalized_enclosure r) hJ
  rw [density_probability_normalization]
  exact h

/-- Original directed Q6 raw row floors are now below the actual
physical density integral, rather than only below a source expression. -/
theorem original_raw_floor_actual_integral (r : Fin 2) :
    (rawFloor r : ℝ) / (q96 : ℝ) ≤
      ∫ z in sourceSupport (vertices r), physicalUpperIntegrand z := by
  have h := original_floor_measured_expression r
  rw [physicalQ6_eq_source] at h
  exact le_trans h (actual_physical_enclosure r)

/-- Original row21 selected mixed floor, on its actual physical support. -/
theorem row21_original_Q96_integral_lower :
    (33553775924834770601 : ℝ) / 79228162514264337593543950336 ≤
      ∫ z in sourceSupport P2Winner9SelectedRowEdgeGeometry.row21,
        physicalUpperIntegrand z := by
  simpa [rawFloor, vertices, q96] using original_raw_floor_actual_integral (0 : Fin 2)

/-- Original row22 selected mixed floor, with its own actual support. -/
theorem row22_original_Q96_integral_lower :
    (6463231997558714529 : ℝ) / 79228162514264337593543950336 ≤
      ∫ z in sourceSupport P2Winner9SelectedRowEdgeGeometry.row22,
        physicalUpperIntegrand z := by
  simpa [rawFloor, vertices, q96] using original_raw_floor_actual_integral (1 : Fin 2)

end

end ImbalancedChen.P2Winner9SelectedRowIntegralFloor
