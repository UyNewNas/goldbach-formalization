import ImbalancedChen.P5OriginalJointCommonBetaModel
import ImbalancedChen.ActualUpperPolicyDensity
import ImbalancedChen.SmallRosserErrorLimit

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
For EVERY previously fixed admissible beta precision, the actual attached
physical density is nonnegative and has a finite normalized envelope,
uniform over later variable rough cutoffs and retained policies. The small
Rosser weights are summed with their signs. Absolute values are used only
for the proved rough error mass, never for individual beta coefficients.
The actual ALL16 joint model, including W and the same E, is then attached
without choosing a new beta precision.
-/
namespace ImbalancedChen.P5Z.OriginalFixedCommonBetaDensityEnvelope
noncomputable section
open Filter Topology Classical
open scoped BigOperators

theorem exists_fixed_beta_variable_cutoff_envelope (r epsilon : ℝ)
    (hr : 0 < r) (he : 0 < epsilon) (he8 : epsilon < 1 / 8) :
    ∃ A : ℝ, 0 < A ∧ ∃ D0 : ℝ, 2 ≤ D0 ∧ ∀ D : ℝ, D0 ≤ D →
      ∀ N cap : ℕ, 0 < N → Even N → D ^ (epsilon ^ 2) ≤ (cap : ℝ) →
      ∀ z : ℝ, D ^ (epsilon ^ 2) ≤ z → z ≤ D ^ r → ∀ retainOdd : List ℕ → Bool,
        let density := physicalDensitySum
          (actualSmallRoughModuli retainOdd N cap (D ^ (epsilon ^ 2)) z)
          (actualSmallRoughRho retainOdd N cap (D ^ (epsilon ^ 2)) z (D ^ epsilon))
        0 ≤ density ∧ density ≤ A * (singularSeries N / Real.log D) := by
  obtain ⟨CE, hCE, hEuler⟩ := exists_actualSmallEulerProduct_le_singularSeries_log
  obtain ⟨C, K, hC, hK, hsieve⟩ := exists_actualSmallRoughRho_density_error
  obtain ⟨KR, hKR, hrough⟩ := exists_fixedRoughAbsoluteDensity_le_logRatio
  obtain ⟨Ds, hDs, hsupply⟩ := hsieve epsilon he he8
  have hKR0 : 0 < KR := by linarith
  let Q : ℝ := (r / epsilon ^ 2) * (1 + KR / epsilon ^ 2)
  have hQ : 0 < Q := by dsimp [Q]; positivity
  let A : ℝ := (CE / epsilon ^ 2) * (C + 2) * Q
  have hA : 0 < A := by dsimp [A]; positivity
  have herror : ∀ᶠ D : ℝ in atTop, actualSmallRosserDensityError C K D epsilon < C + 1 := by
    have hfloor : C * Real.exp (-(1 / epsilon)) < C + 1 := by
      have hexp : Real.exp (-(1 / epsilon)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (one_div_nonneg.mpr he.le))
      nlinarith [mul_le_mul_of_nonneg_left hexp hC.le]
    exact (tendsto_actualSmallRosserDensityError C K epsilon he).eventually (gt_mem_nhds hfloor)
  have hlog : ∀ᶠ D : ℝ in atTop, 1 ≤ Real.log D :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  obtain ⟨Da, hDa⟩ := eventually_atTop.mp
    (herror.and (hlog.and (eventually_four_le_smallRosserPower epsilon he)))
  refine ⟨A, hA, max Ds Da, hDs.trans (le_max_left _ _), ?_⟩
  intro D hD N cap hN hEven hcap z hwz hzmax retainOdd
  have hD2 : 2 ≤ D := hDs.trans ((le_max_left _ _).trans hD)
  have hD1 : 1 < D := by linarith
  have hDp : 0 < D := by linarith
  have hlogp : 0 < Real.log D := Real.log_pos hD1
  have haux := hDa D ((le_max_right _ _).trans hD)
  let w : ℝ := D ^ (epsilon ^ 2)
  let V : ℝ := actualSmallEulerProduct N cap w
  let R : ℝ := reciprocalTotientDensity (fixedRoughSupport retainOdd N cap w z)
    (fixedRoughCoefficient retainOdd N cap w z)
  let M : ℝ := reciprocalTotientDensity (fixedRoughSupport retainOdd N cap w z)
    (fun d => |fixedRoughCoefficient retainOdd N cap w z d|)
  let E : ℝ := actualSmallRosserDensityError C K D epsilon
  have hw : 1 < w := Real.one_lt_rpow hD1 (sq_pos_of_pos he)
  have hlogw : 0 < Real.log w := Real.log_pos hw
  have hV : 0 ≤ V := (actualSmallEulerProduct_pos N cap w hEven).le
  have hR : 0 ≤ R := UpperPolicyFiniteBridge.fixedRoughDensity_nonneg retainOdd N cap w z
  have hM : 0 ≤ M := by
    unfold M reciprocalTotientDensity
    exact Finset.sum_nonneg (fun _ _ => div_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
  have hRM : R ≤ M := by
    unfold R M reciprocalTotientDensity
    exact Finset.sum_le_sum (fun d _ => div_le_div_of_nonneg_right (le_abs_self _) (Nat.cast_nonneg _))
  have hE : 0 ≤ E := by dsimp [E, actualSmallRosserDensityError]; positivity
  have herr := hsupply D ((le_max_left _ _).trans hD) N cap hEven retainOdd z
  dsimp only at herr ⊢
  have herr' : 0 ≤ physicalDensitySum
      (actualSmallRoughModuli retainOdd N cap w z)
      (actualSmallRoughRho retainOdd N cap w z (D ^ epsilon)) - V * R ∧
      physicalDensitySum (actualSmallRoughModuli retainOdd N cap w z)
        (actualSmallRoughRho retainOdd N cap w z (D ^ epsilon)) - V * R ≤ (V * E) * M := herr
  have hnonneg := (mul_nonneg hV hR).trans (sub_nonneg.mp herr'.1)
  have hratio : Real.log z / Real.log w ≤ r / epsilon ^ 2 := by
    have hzp : 0 < z := (zero_lt_one.trans hw).trans_le hwz
    have hzlog := Real.log_le_log hzp hzmax
    rw [Real.log_rpow hDp] at hzlog
    calc
      _ ≤ (r * Real.log D) / Real.log w := div_le_div_of_nonneg_right hzlog hlogw.le
      _ = r / epsilon ^ 2 := by dsimp [w]; rw [Real.log_rpow hDp]; field_simp [hlogp.ne', he.ne']
  have hcorrection : 1 + KR / Real.log w ≤ 1 + KR / epsilon ^ 2 := by
    apply add_le_add_left
    have hden : epsilon ^ 2 ≤ Real.log w := by dsimp [w]; rw [Real.log_rpow hDp]; nlinarith [haux.2.1]
    exact div_le_div_of_nonneg_left hKR0.le (sq_pos_of_pos he) hden
  have hMbound : M ≤ Q := by
    have hh := hrough retainOdd N cap hEven w z hw hwz
    exact hh.trans (mul_le_mul hratio hcorrection
      (by positivity : 0 ≤ 1 + KR / Real.log w) (div_nonneg hr.le (sq_nonneg epsilon)))
  have hVbound : V ≤ CE * singularSeries N / (epsilon ^ 2 * Real.log D) := by
    have hh := hEuler N cap hN hEven w haux.2.2 hcap
    simpa only [w, Real.log_rpow hDp] using hh
  have hdensity : physicalDensitySum
      (actualSmallRoughModuli retainOdd N cap w z)
      (actualSmallRoughRho retainOdd N cap w z (D ^ epsilon)) ≤ V * (1 + E) * M := by
    have hbase : V * R ≤ V * M := mul_le_mul_of_nonneg_left hRM hV
    nlinarith [herr'.2]
  refine ⟨hnonneg, hdensity.trans ?_⟩
  calc
    V * (1 + E) * M ≤ V * (C + 2) * Q := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (by dsimp [E]; linarith [haux.1]) hV
      · exact hMbound
      · exact hM
      · exact mul_nonneg hV (by linarith)
    _ ≤ (CE * singularSeries N / (epsilon ^ 2 * Real.log D)) * (C + 2) * Q :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hVbound (by linarith)) hQ.le
    _ = A * (singularSeries N / Real.log D) := by dsimp [A]; ring

open U1011OriginalSixteenArithmeticProducts
open OriginalOrdinaryPresievedSigma OriginalOrdinaryPresievedDensityComparison
open OriginalJointCommonBetaModel OriginalCommonBetaActualParameters

/-- Every actual ALL16 selected row of the ALREADY FIXED common pair has
one nonnegative normalized absolute density envelope. No beta re-selection
is hidden in the quantifiers; eta, nu and epsilon precede the threshold. -/
theorem exists_fixed_joint_row_density_envelope (n : ℕ) (eta : ℚ) (heta : 0 < eta)
    (nu epsilon : ℝ) (hnu : 0 < nu) (he : 0 < epsilon)
    (heBudget : epsilon < epsilonBudget n eta nu) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ E : ℕ × ℕ → Prop, ∀ t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
        let w := (N : ℝ) ^ (nu * epsilon ^ 2)
        let B := (N : ℝ) ^ (nu * epsilon)
        0 ≤ rowDensity n N eta w B t ∧
          |rowDensity n N eta w B t * Real.log (N : ℝ) / singularSeries N| ≤ C := by
  have he8 : epsilon < 1 / 8 := heBudget.trans_le (min_le_left _ _)
  let r : ℝ := (59 / 250 : ℝ) / nu
  have hr : 0 < r := div_pos (by norm_num) hnu
  obtain ⟨A, hA, D0, hD0, hsupply⟩ := exists_fixed_beta_variable_cutoff_envelope r epsilon hr he he8
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ nu) atTop atTop :=
    (tendsto_rpow_atTop hnu).comp tendsto_natCast_atTop_atTop
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop D0))
  refine ⟨A / nu, div_pos hA hnu, max 2 N1, le_max_left _ _, ?_⟩
  intro N hN hEven E t htuple
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hN1' : 1 < N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN1')
  have hp := parameters_on_joint_row hN1' heta hnu he heBudget htuple
  have hscale : nu * r = 59 / 250 := by dsimp [r]; field_simp [hnu.ne']
  have h := hsupply ((N : ℝ) ^ nu) (hN1 N ((le_max_right _ _).trans hN)) N
    (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
    (by omega) hEven
    (by simpa only [← Real.rpow_mul hNp.le] using hp.1.trans (Nat.le_ceil _))
    (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
    (by simpa only [← Real.rpow_mul hNp.le] using hp.1)
    (by simpa only [← Real.rpow_mul hNp.le, hscale] using hp.2.1)
    (OriginalOrdinaryCommonBetaModel.ordinaryRetainOdd (U1011OriginalSixteenJointNearCapCompiler.D n N eta t))
  dsimp only at h ⊢
  simp only [← Real.rpow_mul hNp.le, Real.log_rpow hNp] at h
  change 0 ≤ rowDensity n N eta _ _ t ∧ _
  have hrow : rowDensity n N eta ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * epsilon)) t ≤
      A * (singularSeries N / (nu * Real.log (N : ℝ))) := h.2
  have hnonneg : 0 ≤ rowDensity n N eta ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * epsilon)) t := h.1
  refine ⟨hnonneg, ?_⟩
  rw [abs_of_nonneg (div_nonneg (mul_nonneg hnonneg hlog.le) (singularSeries_pos N).le)]
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hrow hlog.le) (singularSeries_pos N).le
  convert hh using 1 <;> field_simp [hnu.ne', hlog.ne', (singularSeries_pos N).ne'] <;> ring

end
end ImbalancedChen.P5Z.OriginalFixedCommonBetaDensityEnvelope
