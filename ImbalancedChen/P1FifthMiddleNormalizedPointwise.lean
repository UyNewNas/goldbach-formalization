import ImbalancedChen.P1OriginalFifthMovingScaleLimit
import ImbalancedChen.ActualSmallEulerNormalization

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Actual same-cutoff lower-density supplier on the moving middle shell.
Residual levels are arbitrary physical Rold,Rnew. No coarse old5 lookup,
target remainder, or density limit is assumed. The complete main-plus-error
Suzuki envelope is bounded by C*x^2/omega^3, where x=log(y)/log(N).
The real carrier must supply its physical residual gaps; coarse and
corrected carriers are never identified here.
-/

namespace ImbalancedChen.P1FifthMiddleNormalizedPointwise

noncomputable section
open Filter Topology
open P1OriginalFifthMovingHarmonicEnvelope
open P1OriginalFifthMovingScaleLimit
open P1OriginalSmallCutoffActualLowerTail

def logCoordinate (N : ℕ) (y : ℝ) : ℝ := Real.log y / Real.log (N : ℝ)

def tupleBudget (omega : ℝ) (N : ℕ) (y : ℝ) : ℝ :=
  omega / (2 * logCoordinate N y)

/-- Cubic exponential decay pays the Euler 1/x and leaves two powers of x. -/
theorem exp_inverse_div_le_quadratic (omega x : ℝ)
    (homega : 0 < omega) (hx : 0 < x) :
    Real.exp (-(omega / (2 * x))) / x ≤ 48 * x ^ 2 / omega ^ 3 := by
  let u : ℝ := omega / (2 * x)
  have hu : 0 < u := by dsimp [u]; positivity
  have hp := Real.pow_div_factorial_le_exp hu.le 3
  norm_num at hp
  have hm := mul_le_mul_of_nonneg_right hp (Real.exp_pos (-u)).le
  have hc : Real.exp u * Real.exp (-u) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [hc] at hm
  have he : Real.exp (-u) ≤ 6 / u ^ 3 := by
    apply (le_div_iff₀ (pow_pos hu 3)).mpr
    nlinarith only [hm]
  calc
    _ ≤ (6 / u ^ 3) / x := div_le_div_of_nonneg_right he hx.le
    _ = _ := by
      dsimp [u]
      field_simp [homega.ne', hx.ne']
      <;> ring

/-- The genuine Euler normalization supplier gives exactly E/x. -/
theorem exists_actualEuler_normalized_logCoordinate_bound :
    ∃ E : ℝ, 0 < E ∧ ∀ N cap : ℕ, 1 < N → Even N →
      ∀ y : ℝ, 4 ≤ y → y ≤ (cap : ℝ) →
      actualSmallEulerProduct N cap y * |Real.log (N : ℝ) / singularSeries N| ≤
        E / logCoordinate N y := by
  obtain ⟨E, hE, hEuler⟩ := exists_actualSmallEulerProduct_le_singularSeries_log
  refine ⟨E, hE, ?_⟩
  intro N cap hN hEven y hy hcap
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hlogN := Real.log_pos hn
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hscale : 0 ≤ Real.log (N : ℝ) / singularSeries N :=
    div_nonneg hlogN.le (singularSeries_pos N).le
  rw [abs_of_nonneg hscale]
  calc
    _ ≤ (E * singularSeries N / Real.log y) *
        (Real.log (N : ℝ) / singularSeries N) :=
      mul_le_mul_of_nonneg_right (hEuler N cap (by omega) hEven y hy hcap) hscale
    _ = _ := by
      unfold logCoordinate
      field_simp [hlogN.ne', hlogy.ne', (singularSeries_pos N).ne']
      <;> ring

/-- Generic envelope bound: BOTH the A exp(-T) main deficit and the
B log(ceil R)^(-1/3) explicit error are included. -/
theorem exists_normalizedTailPair_quadratic_bound :
    ∃ E : ℝ, 0 < E ∧ ∀ A B K omega : ℝ, 0 ≤ A → 0 ≤ B → 0 < omega →
      ∀ N cap : ℕ, 1 < N → Even N → ∀ y Rold Rnew : ℝ,
      4 ≤ y → y ≤ (cap : ℝ) →
      1 ≤ Real.log (Nat.ceil Rold : ℝ) → 1 ≤ Real.log (Nat.ceil Rnew : ℝ) →
      |Real.log (N : ℝ) / singularSeries N| *
        (actualSmallEulerProduct N cap y *
          (tailEnvelope A B K Rold (tupleBudget omega N y) +
            tailEnvelope A B K Rnew (tupleBudget omega N y))) ≤
        (96 * E * (A + B * Real.exp (Real.sqrt K)) / omega ^ 3) *
          (logCoordinate N y) ^ 2 := by
  obtain ⟨E, hE, hEuler⟩ := exists_actualEuler_normalized_logCoordinate_bound
  refine ⟨E, hE, ?_⟩
  intro A B K omega hA hB homega N cap hN hEven y Rold Rnew hy hcap hlo hln
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hx : 0 < logCoordinate N y :=
    div_pos (Real.log_pos (by linarith : 1 < y)) (Real.log_pos hn)
  have hold := tailEnvelope_le_uniform_exp A B K Rold
    (tupleBudget omega N y) (tupleBudget omega N y) hA hB le_rfl hlo
  have hnew := tailEnvelope_le_uniform_exp A B K Rnew
    (tupleBudget omega N y) (tupleBudget omega N y) hA hB le_rfl hln
  have hV := (actualSmallEulerProduct_pos N cap y hEven).le
  have he := hEuler N cap hN hEven y hy hcap
  have hP : 0 ≤ A + B * Real.exp (Real.sqrt K) := by positivity
  calc
    _ ≤ |Real.log (N : ℝ) / singularSeries N| *
        (actualSmallEulerProduct N cap y *
          (2 * (A + B * Real.exp (Real.sqrt K)) * Real.exp (-tupleBudget omega N y))) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply mul_le_mul_of_nonneg_left _ hV
      linarith [hold, hnew]
    _ = (actualSmallEulerProduct N cap y * |Real.log (N : ℝ) / singularSeries N|) *
        (2 * (A + B * Real.exp (Real.sqrt K)) * Real.exp (-tupleBudget omega N y)) := by ring
    _ ≤ (E / logCoordinate N y) *
        (2 * (A + B * Real.exp (Real.sqrt K)) * Real.exp (-tupleBudget omega N y)) :=
      mul_le_mul_of_nonneg_right he (by positivity)
    _ = (2 * E * (A + B * Real.exp (Real.sqrt K))) *
        (Real.exp (-(omega / (2 * logCoordinate N y))) / logCoordinate N y) := by
      unfold tupleBudget
      ring
    _ ≤ (2 * E * (A + B * Real.exp (Real.sqrt K))) *
        (48 * (logCoordinate N y) ^ 2 / omega ^ 3) :=
      mul_le_mul_of_nonneg_left (exp_inverse_div_le_quadratic omega _ homega hx) (by positivity)
    _ = _ := by ring

/-- The actual same-cutoff lower residual pair, with an absolute constant
chosen before omega,N,y and both arbitrary physical residual levels. -/
theorem exists_actualMinus_normalized_quadratic_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ omega : ℝ, 0 < omega →
      ∀ N cap : ℕ, 1 < N → Even N → ∀ y Rold Rnew : ℝ,
      4 ≤ y → y ≤ (cap : ℝ) →
      sourceBudget y Rold (tupleBudget omega N y) →
      sourceBudget y Rnew (tupleBudget omega N y) →
      |(actualSmallRosserMinusDensity N cap y Rnew -
          actualSmallRosserMinusDensity N cap y Rold) * Real.log (N : ℝ) / singularSeries N| ≤
        (C / omega ^ 3) * (logCoordinate N y) ^ 2 := by
  obtain ⟨A, B, K, hA, hB, _hK, hsource⟩ := exists_actualMinus_pair_exp_bound
  obtain ⟨E, hE, hnorm⟩ := exists_normalizedTailPair_quadratic_bound
  refine ⟨96 * E * (A + B * Real.exp (Real.sqrt K)), by positivity, ?_⟩
  intro omega homega N cap hN hEven y Rold Rnew hy hcap ho hn
  have hyPower : y ≤ y ^ tupleBudget omega N y := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by linarith : 1 ≤ y) (by linarith [ho.1] : 1 ≤ tupleBudget omega N y)
  have hb := hsource N cap hEven y Rold Rnew
    (tupleBudget omega N y) (tupleBudget omega N y)
    hcap (by linarith) (hyPower.trans ho.2.1) (hyPower.trans hn.2.1)
    ho.1 hn.1 ho.2.1 hn.2.1 ho.2.2.1 hn.2.2.1 ho.2.2.2 hn.2.2.2
  have he : (1 : ℝ) ≤ Real.exp 1 := by
    simpa only [Real.exp_zero] using
      (Real.exp_le_exp.mpr (by norm_num : (0 : ℝ) ≤ 1))
  calc
    _ = |Real.log (N : ℝ) / singularSeries N| *
        |actualSmallRosserMinusDensity N cap y Rnew - actualSmallRosserMinusDensity N cap y Rold| := by
      rw [mul_div_assoc, abs_mul]
      ring
    _ ≤ |Real.log (N : ℝ) / singularSeries N| *
        (actualSmallEulerProduct N cap y *
          (tailEnvelope A B K Rold (tupleBudget omega N y) +
            tailEnvelope A B K Rnew (tupleBudget omega N y))) :=
      mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ ≤ _ := hnorm A B K omega hA.le hB.le homega N cap hN hEven
      y Rold Rnew hy hcap (he.trans ho.2.2.2) (he.trans hn.2.2.2)

/-- The terminal prime 3, and every y<4, is eventually outside the middle
shell. This follows from its actual logarithmic lower cutoff. -/
theorem eventually_log_four_lt_movingCutoff_mul_log
    (omega : ℝ) (homega : 0 < omega) :
    ∀ᶠ N : ℕ in atTop,
      Real.log 4 < movingCutoff omega N * Real.log (N : ℝ) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)) /
      Real.log (N : ℝ)) atTop (𝓝 0) := by
    have hh : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
      simpa only [pow_one] using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    exact hh.comp hlog
  have hfour : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  have hsmall := hratio.eventually (gt_mem_nhds
    (div_pos homega (mul_pos (by norm_num) hfour)))
  filter_upwards [hsmall, eventually_moving_scale_budgets omega homega]
    with N hs hb
  obtain ⟨hN, _ha0, _ha, hT, _haT, _hbudget, _hsourceLog⟩ := hb
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hll : 0 < Real.log (Real.log (N : ℝ)) := by
    unfold movingBudget at hT
    linarith
  have hm := (div_lt_div_iff₀ hlogN (by positivity : 0 < 16 * Real.log (4 : ℝ))).mp hs
  rw [movingCutoff, div_mul_eq_mul_div]
  apply (lt_div_iff₀ (by positivity : 0 < 16 * Real.log (Real.log (N : ℝ)))).mpr
  nlinarith only [hm]

/-- Both actual residual source budgets, both strict physical square gates,
and y>=4 are consequences of the middle shell and the common physical
lower level. Thresholds depend only on omega, not on a,y or either R. -/
theorem eventually_middle_physical_parameters (omega : ℝ) (homega : 0 < omega) :
    ∀ᶠ N : ℕ in atTop, 1 < N ∧ ∀ y Rold Rnew a : ℝ,
      0 < y → a ≤ omega / 6 →
      movingCutoff omega N ≤ logCoordinate N y → logCoordinate N y < a →
      (N : ℝ) ^ (omega / 2) ≤ Rold → (N : ℝ) ^ (omega / 2) ≤ Rnew →
      4 ≤ y ∧ sourceBudget y Rold (tupleBudget omega N y) ∧
        sourceBudget y Rnew (tupleBudget omega N y) ∧ y ^ 2 < Rold ∧ y ^ 2 < Rnew := by
  filter_upwards [eventually_moving_scale_budgets omega homega,
    eventually_log_four_lt_movingCutoff_mul_log omega homega] with N hb hf
  obtain ⟨hN, ha0, _ha, hL, _haL, hLbudget, hSourceLog⟩ := hb
  have hN' : 1 < N := by omega
  refine ⟨hN', ?_⟩
  intro y Rold Rnew a hy ha hmiddle hsmall hold hnew
  have hn : (1 : ℝ) < N := by exact_mod_cast hN'
  have hn0 : (0 : ℝ) < N := by linarith
  have hlogN := Real.log_pos hn
  have hx : 0 < logCoordinate N y := ha0.trans_le hmiddle
  have hlogy : Real.log (4 : ℝ) < Real.log y :=
    hf.trans_le ((le_div_iff₀ hlogN).mp hmiddle)
  have hy4 : 4 ≤ y := by
    have hh := Real.exp_lt_exp.mpr hlogy
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 4), Real.exp_log hy] at hh
    exact hh.le
  have hlogy0 : 0 < Real.log y := Real.log_pos (by linarith)
  have hT : 2 < tupleBudget omega N y := by
    unfold tupleBudget
    apply (lt_div_iff₀ (by positivity : 0 < 2 * logCoordinate N y)).mpr
    linarith
  have hll : 0 < Real.log (Real.log (N : ℝ)) := by
    unfold movingBudget at hL
    linarith
  have hprod : movingCutoff omega N * movingBudget N = omega / 2 := by
    unfold movingCutoff movingBudget
    field_simp [hll.ne']
    <;> ring
  have hTL : tupleBudget omega N y ≤ movingBudget N := by
    have hm := mul_le_mul_of_nonneg_right hmiddle (show 0 ≤ movingBudget N by linarith)
    rw [hprod] at hm
    unfold tupleBudget
    apply (div_le_iff₀ (by positivity : 0 < 2 * logCoordinate N y)).mpr
    nlinarith only [hm]
  have hTbudget : (tupleBudget omega N y) ^ 13 ≤ (omega / 2) * Real.log (N : ℝ) :=
    (pow_le_pow_left₀ (by linarith : 0 ≤ tupleBudget omega N y) hTL 13).trans hLbudget
  have hpower : y ^ tupleBudget omega N y = (N : ℝ) ^ (omega / 2) := by
    rw [Real.rpow_def_of_pos hy, Real.rpow_def_of_pos hn0]
    congr 1
    unfold tupleBudget logCoordinate
    field_simp [hlogN.ne', hlogy0.ne']
    <;> ring
  have hlogR : ∀ R : ℝ, (N : ℝ) ^ (omega / 2) ≤ R →
      (omega / 2) * Real.log (N : ℝ) ≤ Real.log (Nat.ceil R : ℝ) := by
    intro R hR
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hn0 (omega / 2))
      (hR.trans (Nat.le_ceil R))
    simpa only [Real.log_rpow hn0] using hh
  have hbo : sourceBudget y Rold (tupleBudget omega N y) :=
    ⟨hT.le, hpower.le.trans hold, hTbudget.trans (hlogR Rold hold),
      hSourceLog.trans (hlogR Rold hold)⟩
  have hbn : sourceBudget y Rnew (tupleBudget omega N y) :=
    ⟨hT.le, hpower.le.trans hnew, hTbudget.trans (hlogR Rnew hnew),
      hSourceLog.trans (hlogR Rnew hnew)⟩
  have hsquare : y ^ 2 < (N : ℝ) ^ (omega / 2) := by
    rw [← hpower]
    simpa only [Real.rpow_two] using
      Real.rpow_lt_rpow_of_exponent_lt (by linarith : 1 < y) hT
  exact ⟨hy4, hbo, hbn, hsquare.trans_le hold, hsquare.trans_le hnew⟩

/-- Direct middle-shell actual-source API: only the physical lower-level
gap remains for the original corrected carrier to supply. Legal budgets,
the exceptional small terminal primes, and both strict gates are handled. -/
theorem exists_eventually_actualMinus_middle_quadratic_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ omega : ℝ, 0 < omega →
      ∀ᶠ N : ℕ in atTop, ∀ cap : ℕ, Even N → ∀ y Rold Rnew a : ℝ,
      0 < y → y ≤ (cap : ℝ) → a ≤ omega / 6 →
      movingCutoff omega N ≤ logCoordinate N y → logCoordinate N y < a →
      (N : ℝ) ^ (omega / 2) ≤ Rold → (N : ℝ) ^ (omega / 2) ≤ Rnew →
      |(actualSmallRosserMinusDensity N cap y Rnew -
          actualSmallRosserMinusDensity N cap y Rold) * Real.log (N : ℝ) / singularSeries N| ≤
        (C / omega ^ 3) * (logCoordinate N y) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_actualMinus_normalized_quadratic_bound
  refine ⟨C, hC, ?_⟩
  intro omega homega
  filter_upwards [eventually_middle_physical_parameters omega homega] with N hparameters
  intro cap hEven y Rold Rnew a hy hcap ha hmiddle hsmall hold hnew
  obtain ⟨hy4, ho, hn, _hgo, _hgn⟩ := hparameters.2
    y Rold Rnew a hy ha hmiddle hsmall hold hnew
  exact hbound omega homega N cap hparameters.1 hEven y Rold Rnew hy4 hcap ho hn

end

end ImbalancedChen.P1FifthMiddleNormalizedPointwise
