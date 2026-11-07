import ImbalancedChen.P5ZU1011OriginalSixteenRationalGridGeometry
import ImbalancedChen.P5ZU1011OriginalSixteenEnvelopeBoxBounds
import ImbalancedChen.P5ZU1011OriginalSixteenFullHarmonic

/-!
# Directed rational integral certificates for the true original16 minimum

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Automatic generated source6 inner/outer grids and exact rational volumes
come from the preceding geometry module. Actual full16 box bounds and
actual weighted integrability come from their independent source proofs.
No hCover, hCellBound, integral estimate or mean is an input.

The policy minimum remains INSIDE the genuine original integral. Rational
lower sums use inner cells; rational upper sums pay whole outer cells.
Both reciprocal-coordinate endpoint weights have the correct direction.
The final Boolean contains finite rational comparisons only. Its truth
at any saved endpoint is neither asserted nor evaluated. The current
coarse switched box bounds do not justify a mesh-width-to-zero claim.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenRationalIntegralCertificates

noncomputable section

open Set MeasureTheory U11Integral
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSourceGeometryMesh U1011OriginalSixteenRationalGridGeometry
open OriginalSixteenEnvelopeBoxBounds
open scoped BigOperators
open Classical

def weight (v : LogFour) : ℝ := ∏ i : Fin 4, 1 / v i
def weightedKernel (v : LogFour) : ℝ := actualEnvelope v * weight v
def fullIntegral : ℝ := ∫ v in sourceDomain, weightedKernel v

theorem weightedKernel_eq_fullMean_kernel : weightedKernel =
    (fun v => U1011OriginalSixteenFullHarmonic.actualMinimum v * harmonicDensity v) := by
  funext v
  rw [U1011OriginalSixteenFullHarmonic.harmonicDensity_eq_prod]
  rfl

theorem fullIntegral_eq_original_fullMean_integral : fullIntegral =
    ∫ v in U1011OriginalSixteenFullHarmonic.domain,
      U1011OriginalSixteenFullHarmonic.actualMinimum v * harmonicDensity v := by
  rw [fullIntegral, weightedKernel_eq_fullMean_kernel]
  rfl

theorem sourceDomain_measurable : MeasurableSet sourceDomain :=
  measurableSet_originalDomain ∅ measurableSet_empty

theorem weightedKernel_integrable : IntegrableOn weightedKernel sourceDomain volume := by
  rw [weightedKernel_eq_fullMean_kernel]
  exact U1011OriginalSixteenFullHarmonic.integrableOn_actual_weighted

theorem weighted_indicator_integrable : Integrable (sourceDomain.indicator weightedKernel) :=
  weightedKernel_integrable.integrable_indicator sourceDomain_measurable

theorem actualEnvelope_nonneg {v : LogFour} (hv : v ∈ sourceDomain) : 0 ≤ actualEnvelope v :=
  (U1011OriginalSixteenReassembly.actualMinimum_bounds ∅ v hv).1

theorem weight_nonneg_on_domain {v : LogFour} (hv : v ∈ sourceDomain) : 0 ≤ weight v := by
  have h := U11Canonical.originalDomain_subset_compactBox ∅ hv
  apply Finset.prod_nonneg
  intro i hi
  exact (one_div_pos.mpr (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 417 / 5000) (h.1 i))).le

theorem weightedKernel_nonneg {v : LogFour} (hv : v ∈ sourceDomain) : 0 ≤ weightedKernel v :=
  mul_nonneg (actualEnvelope_nonneg hv) (weight_nonneg_on_domain hv)

theorem weighted_indicator_nonneg (v : LogFour) : 0 ≤ sourceDomain.indicator weightedKernel v := by
  by_cases hv : v ∈ sourceDomain
  · simpa only [indicator_of_mem hv] using weightedKernel_nonneg hv
  · simp only [indicator_of_notMem hv, le_refl]

theorem grid_lo_pos (n : ℕ) (j : Index n) (i : Fin 4) : 0 < (gridBox n j).lo i :=
  lt_of_lt_of_le (by norm_num [a]) (gridBox_corner_bounds n j i).1

theorem grid_hi_pos (n : ℕ) (j : Index n) (i : Fin 4) : 0 < (gridBox n j).hi i :=
  (grid_lo_pos n j i).trans_le (gridBox_valid n j i)

def weightLower (n : ℕ) (j : Index n) : ℚ := ∏ i : Fin 4, 1 / (gridBox n j).hi i
def weightUpper (n : ℕ) (j : Index n) : ℚ := ∏ i : Fin 4, 1 / (gridBox n j).lo i

def densityLower (n : ℕ) (j : Index n) : ℚ :=
  max 0 (boxLower (gridBox n j)) * weightLower n j
def densityUpper (n : ℕ) (j : Index n) : ℚ :=
  max 0 (boxUpper (gridBox n j)) * weightUpper n j

theorem densityLower_nonneg (n : ℕ) (j : Index n) : 0 ≤ densityLower n j :=
  mul_nonneg (le_max_left _ _) (Finset.prod_nonneg (fun i _ => (one_div_pos.mpr (grid_hi_pos n j i)).le))

theorem densityUpper_nonneg (n : ℕ) (j : Index n) : 0 ≤ densityUpper n j :=
  mul_nonneg (le_max_left _ _) (Finset.prod_nonneg (fun i _ => (one_div_pos.mpr (grid_lo_pos n j i)).le))

theorem weight_bounds (n : ℕ) (j : Index n) {v : LogFour} (hv : v ∈ cell n j) :
    (weightLower n j : ℝ) ≤ weight v ∧ weight v ≤ (weightUpper n j : ℝ) := by
  have hB := cell_subset_closedBox n j hv
  have hL (i : Fin 4) : (0 : ℝ) < ((gridBox n j).lo i : ℝ) := by
    exact_mod_cast grid_lo_pos n j i
  have hpos (i : Fin 4) : 0 < v i := (hL i).trans_le (hB.1 i)
  simp only [weightLower, weightUpper, Rat.cast_prod, Rat.cast_div, Rat.cast_one, weight]
  constructor
  · apply Finset.prod_le_prod (fun i _ => (one_div_pos.mpr ((hpos i).trans_le (hB.2 i))).le)
    intro i hi
    exact one_div_le_one_div_of_le (hpos i) (hB.2 i)
  · apply Finset.prod_le_prod (fun i _ => (one_div_pos.mpr (hpos i)).le)
    intro i hi
    exact one_div_le_one_div_of_le (hL i) (hB.1 i)

/-- Actual nonlinear minimum bounds are applied BEFORE weighting and
integration. No policy minimum is exchanged with a sum or an integral. -/
theorem weighted_cell_bounds (n : ℕ) (j : Index n) {v : LogFour}
    (hv : v ∈ cell n j) (hD : v ∈ sourceDomain) :
    (densityLower n j : ℝ) ≤ weightedKernel v ∧
      weightedKernel v ≤ (densityUpper n j : ℝ) := by
  have hB := cell_subset_closedBox n j hv
  have hc := actual_envelope_bounds ∅ (gridBox n j) hB hD
  have hw := weight_bounds n j hv
  have hE0 := actualEnvelope_nonneg hD
  have hw0 := weight_nonneg_on_domain hD
  have hWL0 : (0 : ℝ) ≤ (weightLower n j : ℝ) := by
    exact_mod_cast (Finset.prod_nonneg (fun i _ => (one_div_pos.mpr (grid_hi_pos n j i)).le) :
      (0 : ℚ) ≤ weightLower n j)
  have hEL : ((max (0 : ℚ) (boxLower (gridBox n j)) : ℚ) : ℝ) ≤ actualEnvelope v := by
    rw [Rat.cast_max, Rat.cast_zero]
    exact max_le hE0 hc.1
  have hEU : actualEnvelope v ≤ ((max (0 : ℚ) (boxUpper (gridBox n j)) : ℚ) : ℝ) := by
    rw [Rat.cast_max, Rat.cast_zero]
    exact hc.2.trans (le_max_right _ _)
  have hEU0 : (0 : ℝ) ≤ ((max (0 : ℚ) (boxUpper (gridBox n j)) : ℚ) : ℝ) := by
    rw [Rat.cast_max, Rat.cast_zero]
    exact le_max_left _ _
  simp only [densityLower, densityUpper, Rat.cast_mul, weightedKernel]
  exact ⟨mul_le_mul hEL hw.1 hWL0 hE0, mul_le_mul hEU hw.2 hw0 hEU0⟩

def minorant (n : ℕ) (j : Index n) : LogFour → ℝ :=
  (cell n j).indicator (fun _ => (densityLower n j : ℝ))
def majorant (n : ℕ) (j : Index n) : LogFour → ℝ :=
  (cell n j).indicator (fun _ => (densityUpper n j : ℝ))

theorem cell_constant_integrable (n : ℕ) (j : Index n) (q : ℚ) :
    Integrable ((cell n j).indicator (fun _ : LogFour => (q : ℝ))) := by
  have hc : IsCompact (gridBox n j).region := by
    change IsCompact (Icc (fun i => ((gridBox n j).lo i : ℝ))
      (fun i => ((gridBox n j).hi i : ℝ)))
    exact isCompact_Icc
  have hi : IntegrableOn (fun _ : LogFour => (q : ℝ)) (gridBox n j).region :=
    continuousOn_const.integrableOn_compact hc
  exact (hi.mono_set (cell_subset_closedBox n j)).integrable_indicator (cell_measurable n j)

theorem integral_cell_constant (n : ℕ) (j : Index n) (q : ℚ) :
    (∫ v, (cell n j).indicator (fun _ : LogFour => (q : ℝ)) v) =
      ((q * cellVolume n : ℚ) : ℝ) := by
  have hvol : (volume (cell n j)).toReal = (cellVolume n : ℝ) := cell_volume_real n j
  rw [integral_indicator (cell_measurable n j), integral_const]
  simp only [Measure.real, Measure.restrict_apply measurableSet_univ, univ_inter,
    smul_eq_mul, hvol, Rat.cast_mul]
  ring

theorem majorant_nonneg (n : ℕ) (j : Index n) (v : LogFour) : 0 ≤ majorant n j v := by
  by_cases hv : v ∈ cell n j
  · rw [majorant, indicator_of_mem hv]
    exact_mod_cast densityUpper_nonneg n j
  · simp only [majorant, indicator_of_notMem hv, le_refl]

def rationalLower (n : ℕ) : ℚ :=
  ∑ j ∈ inner n, densityLower n j * cellVolume n
def rationalUpper (n : ℕ) : ℚ :=
  ∑ j ∈ outer n, densityUpper n j * cellVolume n

theorem actual_fullIntegral_le_rationalUpper (n : ℕ) :
    fullIntegral ≤ (rationalUpper n : ℝ) := by
  have hg : Integrable (fun v => ∑ j ∈ outer n, majorant n j v) :=
    integrable_finsetSum (outer n) (fun j _ => cell_constant_integrable n j _)
  have hpoint (v : LogFour) : sourceDomain.indicator weightedKernel v ≤
      ∑ j ∈ outer n, majorant n j v := by
    by_cases hv : v ∈ sourceDomain
    · obtain ⟨j, hj, hvj⟩ := domain_outer_cover n hv
      rw [indicator_of_mem hv]
      calc
        weightedKernel v ≤ (densityUpper n j : ℝ) := (weighted_cell_bounds n j hvj hv).2
        _ = majorant n j v := (indicator_of_mem hvj _).symm
        _ ≤ _ := Finset.single_le_sum (fun k _ => majorant_nonneg n k v) hj
    · rw [indicator_of_notMem hv]
      exact Finset.sum_nonneg (fun j _ => majorant_nonneg n j v)
  calc
    fullIntegral = ∫ v, sourceDomain.indicator weightedKernel v :=
      (integral_indicator sourceDomain_measurable).symm
    _ ≤ ∫ v, ∑ j ∈ outer n, majorant n j v :=
      integral_mono weighted_indicator_integrable hg hpoint
    _ = ∑ j ∈ outer n, ∫ v, majorant n j v :=
      integral_finsetSum (outer n) (fun j _ => cell_constant_integrable n j _)
    _ = ∑ j ∈ outer n, ((densityUpper n j * cellVolume n : ℚ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact integral_cell_constant n j _
    _ = (rationalUpper n : ℝ) := by simp [rationalUpper]

theorem rationalLower_le_actual_fullIntegral (n : ℕ) :
    (rationalLower n : ℝ) ≤ fullIntegral := by
  have hf : Integrable (fun v => ∑ j ∈ inner n, minorant n j v) :=
    integrable_finsetSum (inner n) (fun j _ => cell_constant_integrable n j _)
  have hpoint (v : LogFour) : (∑ j ∈ inner n, minorant n j v) ≤
      sourceDomain.indicator weightedKernel v := by
    by_cases hex : ∃ j ∈ inner n, v ∈ cell n j
    · obtain ⟨j, hj, hvj⟩ := hex
      have hvD := inner_cell_subset_domain n hj hvj
      have heq : (∑ k ∈ inner n, minorant n k v) = minorant n j v := by
        apply Finset.sum_eq_single j
        · intro k hk hkj
          have hnot : v ∉ cell n k := fun hvk => hkj (cell_unique hvk hvj)
          exact indicator_of_notMem hnot _
        · intro hnot
          exact (hnot hj).elim
      rw [heq, minorant, indicator_of_mem hvj, indicator_of_mem hvD]
      exact (weighted_cell_bounds n j hvj hvD).1
    · have hz : (∑ j ∈ inner n, minorant n j v) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        exact indicator_of_notMem (fun hvj => hex ⟨j, hj, hvj⟩) _
      rw [hz]
      exact weighted_indicator_nonneg v
  calc
    (rationalLower n : ℝ) = ∑ j ∈ inner n, ((densityLower n j * cellVolume n : ℚ) : ℝ) := by
      simp [rationalLower]
    _ = ∑ j ∈ inner n, ∫ v, minorant n j v := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (integral_cell_constant n j _).symm
    _ = ∫ v, ∑ j ∈ inner n, minorant n j v :=
      (integral_finsetSum (inner n) (fun j _ => cell_constant_integrable n j _)).symm
    _ ≤ ∫ v, sourceDomain.indicator weightedKernel v :=
      integral_mono hf weighted_indicator_integrable hpoint
    _ = fullIntegral := integral_indicator sourceDomain_measurable

/-- Finite rational data only. No real integral or arithmetic mean occurs
in this Boolean, and no concrete passing instance is asserted. -/
def directedCheck (nL nU : ℕ) (lower upper : ℚ) : Bool := decide
  (lower ≤ rationalLower nL ∧ rationalUpper nU ≤ upper)

theorem directedCheck_sound (nL nU : ℕ) (lower upper : ℚ)
    (hcheck : directedCheck nL nU lower upper = true) :
    (lower : ℝ) ≤ fullIntegral ∧ fullIntegral ≤ (upper : ℝ) := by
  have hc : lower ≤ rationalLower nL ∧ rationalUpper nU ≤ upper := of_decide_eq_true hcheck
  have hL : (lower : ℝ) ≤ (rationalLower nL : ℝ) := by exact_mod_cast hc.1
  have hU : (rationalUpper nU : ℝ) ≤ (upper : ℝ) := by exact_mod_cast hc.2
  exact ⟨hL.trans (rationalLower_le_actual_fullIntegral nL),
    (actual_fullIntegral_le_rationalUpper nU).trans hU⟩

end

end ImbalancedChen.P5Z.U1011OriginalSixteenRationalIntegralCertificates
