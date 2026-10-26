import ImbalancedChen.P5OriginalCommonBetaMainWallReserve
import ImbalancedChen.P5ZU1011SameRhoSmoothMainApproximation

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The purely geometric separated-box error supplier is reused. All analytic
payments in this file use the ACTUAL constructed common-beta row MAIN,
not the old all-prime native row. For every already-fixed admissible beta
pair: requested tolerance -> refinement mesh -> smoothing width -> common
N threshold. Source bands, original E, selected ALL16/W row and complete
physical modulus are unchanged. AP/centre/strong PP remain OPEN.
-/
namespace ImbalancedChen.P5Z.OriginalCommonBetaSmoothMainReserve
noncomputable section
open Set Filter Topology Classical
open scoped BigOperators
open U11Integral U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenArithmeticProducts
open U1011OriginalSixteenJointNearCapCompiler (ordinaryTuples)
open U1011OriginalSixteenEligibilityState U1011OriginalSixteenMixedGatePrimeTests
open U1011FourDimensionalSmoothBoxAtoms U1011AffineSmoothBoxCover
open U1011SameRhoMeshFaceReserveSelection U1011SameRhoSmoothMainApproximation
open OriginalCommonBetaActualParameters OriginalCommonBetaMainWallReserve

def commonSmoothMainError {ι : Type*} (n N : ℕ) (eta : ℚ) (nu epsilon : ℝ)
    (E : ℕ × ℕ → Prop) (g : ι → MixedGate) (inner : Bool) (m : ℕ) (δ : ℝ) : ℝ :=
  |∑ t ∈ ordinaryTuples n N E, rowMain n N eta nu epsilon t *
    (smoothCover inner δ (chosenCells inner g m) (coordinates N t) -
      regionIndicator g (coordinates N t))|

/-- Complete presieved divisor sum and full physical modulus survive
the exact common-pair smooth MAIN discrepancy. -/
theorem commonSmoothMainError_le {ι : Type*} [Fintype ι]
    (n N : ℕ) (eta : ℚ) (nu epsilon : ℝ) (E : ℕ × ℕ → Prop) (hN : 1 < N)
    (g : ι → MixedGate) (inner : Bool) (m : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    commonSmoothMainError n N eta nu epsilon E g inner m δ ≤
      boundary n N eta nu epsilon E (reducedForms g) (reducedBounds g)
        (wallScale g * logPrimeMeshStep (lower : ℝ) (upper : ℝ) m) +
      ((Fintype.card (Grid m) : ℝ) + 1) *
        boundary n N eta nu epsilon E (faceForms m) (faceBounds m) δ := by
  unfold commonSmoothMainError boundary
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro t ht
  have hv : coordinates N t ∈ cube :=
    U1011OriginalFifteenJointNativeRows.joint_coordinates_cube hN (Finset.mem_filter.mp ht).1
  have herr := smooth_error_pointwise g inner m hδ hv
  have h := mul_le_mul_of_nonneg_left herr (abs_nonneg (rowMain n N eta nu epsilon t))
  rw [abs_mul]
  by_cases hw : coordinates N t ∈ primeAffineWallStrip (reducedForms g) (reducedBounds g)
      (wallScale g * logPrimeMeshStep (lower : ℝ) (upper : ℝ) m)
  <;> by_cases hf : coordinates N t ∈ primeAffineWallStrip (faceForms m) (faceBounds m) δ
  <;> simp only [hw, hf, if_true, if_false, mul_one, mul_zero, add_zero, zero_add] at h ⊢
  <;> nlinarith

theorem common_boundary_mono_width {r n N : ℕ} (eta : ℚ) (nu epsilon : ℝ)
    (E : ℕ × ℕ → Prop) (L : Fin r → LogFour →L[ℝ] ℝ) (c : Fin r → ℝ)
    {δ w : ℝ} (hδw : δ ≤ w) :
    boundary n N eta nu epsilon E L c δ ≤ boundary n N eta nu epsilon E L c w := by
  unfold boundary
  apply Finset.sum_le_sum
  intro t ht
  by_cases hs : coordinates N t ∈ primeAffineWallStrip L c δ
  · obtain ⟨i, hi⟩ := hs
    have hs' : coordinates N t ∈ primeAffineWallStrip L c δ := ⟨i, hi⟩
    have hb : coordinates N t ∈ primeAffineWallStrip L c w := ⟨i, hi.trans hδw⟩
    simp only [if_pos hs', if_pos hb, le_refl]
  · simp only [if_neg hs]
    split_ifs <;> positivity

/-- The common pair is fixed BEFORE the approximation tolerance. Both
inner/outer separated covers receive one mesh, one positive smoothing
width and one threshold for every original E, without a new beta choice. -/
theorem exists_fixed_common_beta_smooth_main_reserve {ι : Type*} [Fintype ι]
    (n : ℕ) (eta : ℚ) (heta : 0 < eta) (nu epsilon : ℝ)
    (hnu : 0 < nu) (he : 0 < epsilon) (heBudget : epsilon < epsilonBudget n eta nu)
    (g : ι → MixedGate) (reserve : ℝ) (hreserve : 0 < reserve) :
    ∃ m : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ E : ℕ × ℕ → Prop, ∀ inner : Bool,
        commonSmoothMainError n N eta nu epsilon E g inner m δ < reserve := by
  obtain ⟨w, hw, N1, hN1, hwall⟩ := exists_common_beta_main_wall_reserve n eta heta nu epsilon
    hnu he heBudget (reducedForms g) (reducedBounds g) (reducedForms_ne_zero g)
    (reserve / 2) (half_pos hreserve)
  have hlim : Tendsto (fun m : ℕ => wallScale g *
      logPrimeMeshStep (lower : ℝ) (upper : ℝ) m) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_logPrimeMeshStep (lower : ℝ) (upper : ℝ)).const_mul (wallScale g)
  obtain ⟨m, hm⟩ := (hlim.eventually (gt_mem_nhds hw)).exists
  let K : ℝ := (Fintype.card (Grid m) : ℝ) + 1
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨δ, hδ, N2, hN2, hface⟩ := exists_common_beta_main_wall_reserve n eta heta nu epsilon
    hnu he heBudget (faceForms m) (faceBounds m) (faceForms_ne_zero m)
    (reserve / (2 * K)) (div_pos hreserve (mul_pos (by norm_num) hK))
  refine ⟨m, δ, hδ, max N1 N2, hN1.trans (le_max_left _ _), ?_⟩
  intro N hN hEven E inner
  have hN1' : N1 ≤ N := (le_max_left _ _).trans hN
  have hN2' : N2 ≤ N := (le_max_right _ _).trans hN
  have hlarge : 1 < N := by omega
  have hb := commonSmoothMainError_le n N eta nu epsilon E hlarge g inner m hδ
  have hwpaid := (common_boundary_mono_width eta nu epsilon E (reducedForms g) (reducedBounds g) hm.le).trans_lt
    (hwall N hN1' hEven E)
  have hfpaid := mul_lt_mul_of_pos_left (hface N hN2' hEven E) hK
  have hc : K * (reserve / (2 * K)) = reserve / 2 := by field_simp [hK.ne']; ring
  rw [hc] at hfpaid
  change commonSmoothMainError n N eta nu epsilon E g inner m δ ≤
    boundary n N eta nu epsilon E (reducedForms g) (reducedBounds g)
      (wallScale g * logPrimeMeshStep (lower : ℝ) (upper : ℝ) m) +
      K * boundary n N eta nu epsilon E (faceForms m) (faceBounds m) δ at hb
  linarith

end
end ImbalancedChen.P5Z.OriginalCommonBetaSmoothMainReserve
