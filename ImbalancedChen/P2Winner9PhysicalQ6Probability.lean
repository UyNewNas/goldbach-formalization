import ImbalancedChen.P2Winner9PhysicalCurvatureProbability
import ImbalancedChen.P2Winner9T10TailJensen

/-! The physical Q6 correction on the selected rows, expressed in measured moments. -/

namespace ImbalancedChen.P2Winner9PhysicalQ6Probability

noncomputable section

open Set MeasureTheory
open scoped BigOperators
open P2Winner9SelectedRowRealJacobian
open P2Winner9SelectedRowAnalyticCaps
open P2Winner9SelectedPhysicalMeans
open P2Winner9ActualRowProbability
open P2Winner9PhysicalAffineTransfer
open P2Winner9PhysicalConstantCurvature
open P2Winner9PhysicalCurvatureProbability
open P2Winner9ReciprocalProduct
open P2Winner9T10TailJensen (binomial10 binomial10_pointwise)

def binomial6 (y : ℝ) : ℝ :=
  ∑ k : Fin 7, ((9 + k.val).choose k.val : ℝ) * y^k.val

theorem binomial6_minorant {y : ℝ} (hy : 0 ≤ y) (h1 : y < 1) :
    binomial6 y ≤ 1 / (1 - y)^10 := by
  calc
    binomial6 y = ∑ k ∈ Finset.range 7, ((9 + k).choose k : ℝ) * y^k :=
      Fin.sum_univ_eq_sum_range (fun k : ℕ => ((9 + k).choose k : ℝ) * y^k) 7
    _ ≤ binomial10 y := by
      unfold binomial10
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by decide))
      intro k _ _
      exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hy _)
    _ ≤ 1 / (1 - y)^10 := binomial10_pointwise hy h1

def transverseSum (r : Fin 2) (z : Ambient) : ℝ :=
  ∑ j : Fin 10, (B r j z)^2 / (2 * (V r j)^2)

def cTerm (r : Fin 2) (j : Fin 10) (k : Fin 7) (z : Ambient) : ℝ :=
  (((9 + k.val).choose k.val : ℝ) * (Y r z)^k.val * (B r j z)^2) /
    (2 * (V r j)^2 * (U r)^10)

def C6 (r : Fin 2) (z : Ambient) : ℝ :=
  ∑ j : Fin 10, ∑ k : Fin 7, cTerm r j k z

theorem C6_factorization (r : Fin 2) (z : Ambient) :
    C6 r z = (1 / (U r)^10) * binomial6 (Y r z) * transverseSum r z := by
  unfold C6 transverseSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [binomial6, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  unfold cTerm
  rw [← div_div]
  ring

theorem transverseSum_nonneg (r : Fin 2) (z : Ambient) : 0 ≤ transverseSum r z :=
  Finset.sum_nonneg (fun _ _ => div_nonneg (sq_nonneg _) (by positivity))

theorem pointwise_Q6 (r : Fin 2) {z : Ambient}
    (hz : z ∈ sourceSupport (vertices r)) :
    invP10 r z + C6 r z ≤ prodInv r z := by
  have caps := actual_support_caps r hz
  have hsum : ∑ j : Fin 10, A r j z = 10 * P r z := by
    unfold A P physicalP
    ring
  have hquadratic : (1 + transverseSum r z) / (P r z)^10 ≤ prodInv r z :=
    reciprocal_product_quadratic (fun j => A r j z) (V r) (P r z)
      (fun j => (caps.2.2.2.2 j).1) (P_pos r hz)
      (fun j => (caps.2.2.2.2 j).2.1) (fun j => (caps.2.2.2.2 j).2.2) hsum
  have hscaled :=
    mul_le_mul_of_nonneg_left
      (binomial6_minorant (Y_mem r hz).1 (Y_lt_one r hz))
      (by positivity : 0 ≤ 1 / (U r)^10)
  rw [← invP10_scaled r hz] at hscaled
  have hC : C6 r z ≤ invP10 r z * transverseSum r z := by
    rw [C6_factorization]
    exact mul_le_mul_of_nonneg_right hscaled (transverseSum_nonneg r z)
  calc
    invP10 r z + C6 r z ≤ invP10 r z + invP10 r z * transverseSum r z :=
      add_le_add le_rfl hC
    _ = (1 + transverseSum r z) / (P r z)^10 := by
      unfold invP10
      ring
    _ ≤ prodInv r z := hquadratic

theorem cTerm_continuous (r : Fin 2) (j : Fin 10) (k : Fin 7) :
    Continuous (cTerm r j k) := by
  have hY := Y_continuous r
  have hB := B_continuous r j
  unfold cTerm
  fun_prop

theorem C6_integrable (r : Fin 2) : Integrable (C6 r) (ν r) := by
  apply weighted_integrable r
  have hc := cTerm_continuous r
  unfold C6
  fun_prop

/-- The actual probability moment, with the same physical gap weighting
and the same normalized factor deviations as the pointwise estimate. -/
def mixedMoment (r : Fin 2) (j : Fin 10) (k : Fin 7) : ℝ :=
  ∫ z, (Y r z)^k.val * (B r j z)^2 ∂ν r

theorem mixedMoment_eq_physical (r : Fin 2) (j : Fin 10) (k : Fin 7) :
    mixedMoment r j k =
      (∫ z in sourceSupport (vertices r),
        physicalGap z * (Y r z)^k.val * (B r j z)^2) / gapMass r := by
  unfold mixedMoment
  rw [weighted_integral]
  simp only [mul_assoc]

theorem integral_cTerm (r : Fin 2) (j : Fin 10) (k : Fin 7) :
    (∫ z, cTerm r j k z ∂ν r) =
      ((9 + k.val).choose k.val : ℝ) * mixedMoment r j k /
        (2 * (V r j)^2 * (U r)^10) := by
  simp only [cTerm, mixedMoment, mul_assoc, integral_div, integral_const_mul]

/-- The expectation contains all ten factors at all seven degrees. -/
theorem C6_expectation (r : Fin 2) :
    (∫ z, C6 r z ∂ν r) =
      ∑ j : Fin 10, ∑ k : Fin 7,
        ((9 + k.val).choose k.val : ℝ) * mixedMoment r j k /
          (2 * (V r j)^2 * (U r)^10) := by
  have hk (j : Fin 10) (k : Fin 7) : Integrable (cTerm r j k) (ν r) :=
    weighted_integrable r (cTerm_continuous r j k).continuousOn
  have hj (j : Fin 10) :
      Integrable (fun z => ∑ k : Fin 7, cTerm r j k z) (ν r) :=
    integrable_finsetSum Finset.univ (fun k _ => hk j k)
  unfold C6
  rw [integral_finsetSum Finset.univ (fun j _ => hj j)]
  simp_rw [integral_finsetSum Finset.univ (fun k _ => hk _ k), integral_cTerm]

theorem Q6_expectation_lower (r : Fin 2) :
    (∫ z, invP10 r z ∂ν r) + (∫ z, C6 r z ∂ν r) ≤
      ∫ z, prodInv r z ∂ν r := by
  have hi := weighted_integrable r (invP10_continuousOn r)
  have hc := C6_integrable r
  have hp := weighted_integrable r (prodInv_continuousOn r)
  have hrow : ∀ᵐ z ∂ν r, invP10 r z + C6 r z ≤ prodInv r z :=
    (ν_support r).mono (fun _ hz => pointwise_Q6 r hz)
  have h := integral_mono_ae (hi.add hc) hp hrow
  simpa only [Pi.add_apply, integral_add hi hc] using h

theorem physical_density_Q6_lower (r : Fin 2) :
    (((data r).jensenNum : ℝ) / (data r).jensenDen) *
      ((∫ z, invP10 r z ∂ν r) + (∫ z, C6 r z ∂ν r)) ≤
      ∫ z in sourceSupport (vertices r), physicalUpperIntegrand z := by
  rw [density_probability_normalization]
  exact mul_le_mul_of_nonneg_left (Q6_expectation_lower r) (by positivity)

end

end ImbalancedChen.P2Winner9PhysicalQ6Probability
