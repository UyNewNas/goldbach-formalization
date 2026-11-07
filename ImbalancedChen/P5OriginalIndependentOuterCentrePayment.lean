import ImbalancedChen.P5OriginalPresievedOuterAtomCoefficient
import ImbalancedChen.PowerErrorBudget
import ImbalancedChen.ChenInitialCorrectionBudget

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Centre payment for the ACTUAL independent outerSigma: no original tuple
source filter occurs. Unit amplitude is derived from the actual separated
label fibre theorem; active physical153/256 support is derived from the
genuine frozen common-beta coefficient and padded interval endpoints.
No equality to jointPresievedSigma or strong distribution is asserted.
-/
namespace ImbalancedChen.P5Z.OriginalIndependentOuterCentrePayment
noncomputable section
open Set Filter Topology Classical
open scoped BigOperators
open U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenCommonSmallParameters (selectedCells)
open OriginalCommonBetaActualParameters
open OriginalPresievedOuterAtomSupport OriginalPresievedOuterAtomCoefficient
open OriginalPresievedOuterAtomArithmetic

def physicalSupport (n : ℕ) (eta : ℚ) (j : Grid n) (N : ℕ) (w : ℝ) (a b : Fin 4 → ℝ) : Finset ℕ :=
  (outerMarks n eta j N w a b).image outerModulus

theorem outerSigma_zero_off_support (n : ℕ) (eta : ℚ) (j : Grid n) (N : ℕ) (w ell : ℝ)
    (a b : Fin 4 → ℝ) (inner : Bool) (delta : ℝ) (fine : ℕ) (cell : Grid fine)
    {q : ℕ} (hq : q ∉ physicalSupport n eta j N w a b) :
    outerSigma n eta j N w ell a b inner delta fine cell q = 0 := by
  apply Finset.sum_eq_zero
  intro m hm
  obtain ⟨hm, hmod⟩ := Finset.mem_filter.mp hm
  exact (hq (Finset.mem_image.mpr ⟨m, hm, hmod⟩)).elim

/-- Nonzero independent outer coefficients expose an ACTUAL frozen mark.
Its positivity and power support need no original source ownership. -/
theorem outerSigma_active_positive_cap {n N q : ℕ} {eta : ℚ} {nu epsilon width : ℝ}
    (hN : 1 < N) (heta : 0 < eta) (hnu : 0 < nu) (he : 0 < epsilon)
    (heBudget : epsilon < epsilonBudget n eta nu) (j : Grid n) (hj : j ∈ selectedCells n)
    (a b : Fin 4 → ℝ)
    (hhi : ∀ i, b i ≤ ((gridBox n j).hi i : ℝ) + width)
    (hwidth : width ≤ (U1011OriginalSixteenNearCapBoxProfiles.delta
      (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta : ℝ) / 32)
    (inner : Bool) (delta : ℝ) (fine : ℕ) (cell : Grid fine)
    (hq : outerSigma n eta j N ((N : ℝ) ^ (nu * epsilon ^ 2)) (nu * epsilon)
      a b inner delta fine cell q ≠ 0) :
    0 < q ∧ (q : ℝ) < (N : ℝ) ^ (153 / 256 : ℝ) := by
  have hex : ∃ m ∈ outerMarks n eta j N ((N : ℝ) ^ (nu * epsilon ^ 2)) a b,
      outerModulus m = q ∧ frozenCoefficient n eta j N ((N : ℝ) ^ (nu * epsilon ^ 2))
        (nu * epsilon) m.2 ≠ 0 := by
    by_contra hn
    apply hq
    apply Finset.sum_eq_zero
    intro m hm
    obtain ⟨hm, hmod⟩ := Finset.mem_filter.mp hm
    have hz : frozenCoefficient n eta j N ((N : ℝ) ^ (nu * epsilon ^ 2)) (nu * epsilon) m.2 = 0 := by
      by_contra hactive
      exact hn ⟨m, hm, hmod, hactive⟩
    simp only [hz, zero_mul]
  obtain ⟨m, hm, hmod, hactive⟩ := hex
  obtain ⟨ht, hr⟩ := Finset.mem_product.mp hm
  have hprefix : 0 < ∏ i, m.1 i := Finset.prod_pos
    (fun i _ => (mem_actualPrimeBoxTuples_iff.mp ht i).1.pos)
  have hrsf : Squarefree m.2 := actualSmallRoughModuli_squarefree _ _ _ _ _ hr
  have hrpos : 0 < m.2 := Nat.pos_of_ne_zero hrsf.ne_zero
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hpadded (i : Fin 4) : (m.1 i : ℝ) ≤ (N : ℝ) ^ (((gridBox n j).hi i : ℝ) + width) :=
    (mem_actualPrimeBoxTuples_iff.mp ht i).2.2.2.le.trans
      (Real.rpow_le_rpow_of_exponent_le hn.le (hhi i))
  have hparams := common_parameters_on_selected_cell hN hnu he heBudget j hj
  have hcap := actual_padded_physical_support hN heta j hj ((N : ℝ) ^ (nu * epsilon ^ 2))
    (nu * epsilon) width hparams.2 hwidth m.1 hpadded hactive
  rw [← hmod]
  exact ⟨Nat.mul_pos hprefix hrpos, hcap⟩

def activeSupport (n : ℕ) (eta : ℚ) (j : Grid n) (N : ℕ) (w ell : ℝ)
    (a b : Fin 4 → ℝ) (inner : Bool) (delta : ℝ) (fine : ℕ) (cell : Grid fine) : Finset ℕ :=
  (physicalSupport n eta j N w a b).filter
    (fun q => outerSigma n eta j N w ell a b inner delta fine cell q ≠ 0)

def outerCentre (n : ℕ) (eta : ℚ) (j : Grid n) (N : ℕ) (w ell : ℝ)
    (a b : Fin 4 → ℝ) (inner : Bool) (delta : ℝ) (fine : ℕ) (cell : Grid fine) : ℝ :=
  ∑ q ∈ physicalSupport n eta j N w a b,
    outerSigma n eta j N w ell a b inner delta fine cell q * chenCentrePrimeAPCount N N q

theorem outerCentre_eq_active (n : ℕ) (eta : ℚ) (j : Grid n) (N : ℕ) (w ell : ℝ)
    (a b : Fin 4 → ℝ) (inner : Bool) (delta : ℝ) (fine : ℕ) (cell : Grid fine) :
    outerCentre n eta j N w ell a b inner delta fine cell =
      ∑ q ∈ activeSupport n eta j N w ell a b inner delta fine cell,
        outerSigma n eta j N w ell a b inner delta fine cell q * chenCentrePrimeAPCount N N q := by
  unfold outerCentre activeSupport
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hz : outerSigma n eta j N w ell a b inner delta fine cell q = 0 <;> simp [hz]

/-- Both amplitude and physical cap are conclusions from primitive
interval separation/cutoff/padding, never premises about the coefficient. -/
theorem abs_outerCentre_le_power_log {n N : ℕ} {eta : ℚ} {nu epsilon width : ℝ}
    (hN : 1 < N) (heta : 0 < eta) (hnu : 0 < nu) (he : 0 < epsilon)
    (heBudget : epsilon < epsilonBudget n eta nu) (j : Grid n) (hj : j ∈ selectedCells n)
    (a b : Fin 4 → ℝ) (hsep : ∀ i : Fin 3, b i.succ ≤ a i.castSucc)
    (hcut : ∀ i, (U1011OriginalSixteenNearCapBoxProfiles.cutoffExponent
      (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta : ℝ) ≤ a i)
    (hhi : ∀ i, b i ≤ ((gridBox n j).hi i : ℝ) + width)
    (hwidth : width ≤ (U1011OriginalSixteenNearCapBoxProfiles.delta
      (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta : ℝ) / 32)
    (inner : Bool) (delta : ℝ) (fine : ℕ) (cell : Grid fine) :
    |outerCentre n eta j N ((N : ℝ) ^ (nu * epsilon ^ 2)) (nu * epsilon) a b inner delta fine cell| ≤
      (N : ℝ) ^ (153 / 256 : ℝ) * (Real.log (N : ℝ) / Real.log 2) := by
  let A := activeSupport n eta j N ((N : ℝ) ^ (nu * epsilon ^ 2)) (nu * epsilon) a b inner delta fine cell
  have hsub : A ⊆ Finset.Icc 1 (Nat.floor ((N : ℝ) ^ (153 / 256 : ℝ))) := by
    intro q hq
    have hs := outerSigma_active_positive_cap hN heta hnu he heBudget j hj a b hhi hwidth
      inner delta fine cell (Finset.mem_filter.mp hq).2
    exact Finset.mem_Icc.mpr ⟨hs.1, Nat.le_floor hs.2.le⟩
  have hcard : (A.card : ℝ) ≤ (N : ℝ) ^ (153 / 256 : ℝ) := by
    calc
      _ ≤ ((Finset.Icc 1 (Nat.floor ((N : ℝ) ^ (153 / 256 : ℝ)))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      _ = (Nat.floor ((N : ℝ) ^ (153 / 256 : ℝ)) : ℝ) := by simp
      _ ≤ (N : ℝ) ^ (153 / 256 : ℝ) := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  have hNpos : 0 < N := by omega
  have hlog : 0 ≤ Real.log (N : ℝ) / Real.log 2 :=
    div_nonneg (Real.log_pos (by exact_mod_cast hN)).le (Real.log_pos (by norm_num)).le
  have hpoint (q : ℕ) (hq : q ∈ A) :
      |outerSigma n eta j N ((N : ℝ) ^ (nu * epsilon ^ 2)) (nu * epsilon) a b inner delta fine cell q *
        chenCentrePrimeAPCount N N q| ≤ Real.log (N : ℝ) / Real.log 2 := by
    have ha := outerSigma_abs_le_one hN hnu he heBudget j hj a b hsep hcut inner delta fine cell q
    have hc := (chenCentrePrimeAPCount_le_divisorCount N N q).trans (chenPrimeDivisorCount_le_log N hNpos)
    rw [abs_mul, abs_of_nonneg (chenCentrePrimeAPCount_nonneg N N q)]
    exact (mul_le_mul ha hc (chenCentrePrimeAPCount_nonneg N N q) zero_le_one).trans_eq (one_mul _)
  calc
    _ = |∑ q ∈ A, outerSigma n eta j N ((N : ℝ) ^ (nu * epsilon ^ 2)) (nu * epsilon)
        a b inner delta fine cell q * chenCentrePrimeAPCount N N q| := by rw [outerCentre_eq_active]
    _ ≤ ∑ q ∈ A, |outerSigma n eta j N ((N : ℝ) ^ (nu * epsilon ^ 2)) (nu * epsilon)
        a b inner delta fine cell q * chenCentrePrimeAPCount N N q| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _q ∈ A, Real.log (N : ℝ) / Real.log 2 := Finset.sum_le_sum hpoint
    _ = (A.card : ℝ) * (Real.log (N : ℝ) / Real.log 2) := by simp
    _ ≤ (N : ℝ) ^ (153 / 256 : ℝ) * (Real.log (N : ℝ) / Real.log 2) :=
      mul_le_mul_of_nonneg_right hcard hlog

/-- Actual independent profile payment: one threshold before every later
selected row, common pair, separated padded box and canonical smooth atom. -/
theorem eventually_independent_outerCentre_paid (reserve : ℝ) (hreserve : 0 < reserve) :
    ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, ∀ eta : ℚ, 0 < eta → ∀ nu epsilon width : ℝ,
      0 < nu → 0 < epsilon → epsilon < epsilonBudget n eta nu → ∀ j : Grid n,
        j ∈ selectedCells n → ∀ a b : Fin 4 → ℝ,
          (∀ i : Fin 3, b i.succ ≤ a i.castSucc) →
          (∀ i, (U1011OriginalSixteenNearCapBoxProfiles.cutoffExponent
            (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta : ℝ) ≤ a i) →
          (∀ i, b i ≤ ((gridBox n j).hi i : ℝ) + width) →
          width ≤ (U1011OriginalSixteenNearCapBoxProfiles.delta
            (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta : ℝ) / 32 →
          ∀ inner : Bool, ∀ delta : ℝ, ∀ fine : ℕ, ∀ cell : Grid fine,
            |outerCentre n eta j N ((N : ℝ) ^ (nu * epsilon ^ 2)) (nu * epsilon)
              a b inner delta fine cell| ≤ reserve * singularNormalization N := by
  have hp := eventually_powerLog_le_singularNormalization (1 / Real.log 2) (153 / 256 : ℝ) 1
    (by norm_num) reserve hreserve
  filter_upwards [hp, eventually_ge_atTop (2 : ℕ)] with N hpower hN
  intro n eta heta nu epsilon width hnu he heBudget j hj a b hsep hcut hhi hwidth inner delta fine cell
  exact (abs_outerCentre_le_power_log (by omega) heta hnu he heBudget j hj a b hsep hcut hhi hwidth
    inner delta fine cell).trans (by
      simpa only [pow_one, mul_div_assoc, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hpower)

end
end ImbalancedChen.P5Z.OriginalIndependentOuterCentrePayment
