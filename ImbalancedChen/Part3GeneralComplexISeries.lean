import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.ChangeOrigin

/-!
Literal general complex-order modified-I series. The reciprocal-Gamma recurrence
is unconditional. For `-1 < re nu`, a proved factorial majorant gives absolute
convergence at every core argument, uniform convergence on each norm ball, and
an entire core. No differential equation or convergence is assumed.

SOURCE ONLY: not compiled and not ROOT accepted.
-/

noncomputable section

open scoped BigOperators
open Filter Set

namespace ImbalancedChen.Part3.GeneralComplexISeriesSourceOnly

def generalICoeff (nu : ℂ) (n : ℕ) : ℂ :=
  ((n.factorial : ℂ) * Complex.Gamma ((n : ℂ) + nu + 1))⁻¹

def generalICore (nu z : ℂ) : ℂ :=
  ∑' n, generalICoeff nu n * z ^ n

def generalI (nu : ℂ) (q : ℝ) : ℂ :=
  (((q / 2 : ℝ) : ℂ) ^ nu) *
    generalICore nu ((((q / 2 : ℝ) : ℂ)) ^ 2)

/-- The genuine Gamma recurrence, including orders at Gamma poles. -/
theorem generalICoeff_recurrence (nu : ℂ) (n : ℕ) :
    (((n + 1 : ℕ) : ℂ) * ((n : ℂ) + nu + 1) *
      generalICoeff nu (n + 1)) = generalICoeff nu n := by
  have hk : ((n + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hs : ((n + 1 : ℕ) : ℂ) + nu + 1 = ((n : ℂ) + nu + 1) + 1 := by
    push_cast
    ring
  have hf : (((n + 1).factorial : ℕ) : ℂ) =
      ((n + 1 : ℕ) : ℂ) * (n.factorial : ℂ) := by
    simp [Nat.factorial_succ]
  have hg := Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one
    ((n : ℂ) + nu + 1)
  unfold generalICoeff
  rw [hf, hs, mul_inv_rev, mul_inv_rev]
  calc
    _ = (((n + 1 : ℕ) : ℂ) * (((n + 1 : ℕ) : ℂ))⁻¹) *
        ((n.factorial : ℂ)⁻¹ * (((n : ℂ) + nu + 1) *
          (Complex.Gamma (((n : ℂ) + nu + 1) + 1))⁻¹)) := by ring
    _ = (n.factorial : ℂ)⁻¹ * (Complex.Gamma ((n : ℂ) + nu + 1))⁻¹ := by
      rw [mul_inv_cancel₀ hk, one_mul, ← hg]
    _ = _ := by rw [mul_inv_rev]; ring

/-- Each successive Gamma factor is bounded below by the positive real part
of the initial factor. This permits arbitrary imaginary order. -/
theorem generalICoeff_factor_lower (nu : ℂ) (n : ℕ) :
    nu.re + 1 ≤ ‖(n : ℂ) + nu + 1‖ := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hr := Complex.re_le_norm ((n : ℂ) + nu + 1)
  simp only [Complex.add_re, Complex.natCast_re, Complex.one_re] at hr
  linarith

theorem generalICoeff_weighted_norm_le {nu : ℂ} (hnu : -1 < nu.re) (n : ℕ) :
    ‖generalICoeff nu n‖ * ((nu.re + 1) ^ n * (n.factorial : ℝ)) ≤
      ‖(Complex.Gamma (nu + 1))⁻¹‖ := by
  have hd : 0 < nu.re + 1 := by linarith
  induction n with
  | zero => simp [generalICoeff]
  | succ n ih =>
    have hrec := congrArg norm (generalICoeff_recurrence nu n)
    simp only [norm_mul, Complex.norm_natCast, Nat.cast_add, Nat.cast_one] at hrec
    have hw : 0 ≤ (nu.re + 1) ^ n * (n.factorial : ℝ) :=
      mul_nonneg (pow_nonneg hd.le _) (Nat.cast_nonneg _)
    have hn : 0 ≤ (n : ℝ) + 1 := by positivity
    calc
      ‖generalICoeff nu (n + 1)‖ *
          ((nu.re + 1) ^ (n + 1) * ((n + 1).factorial : ℝ)) =
          (‖generalICoeff nu (n + 1)‖ * (((n : ℝ) + 1) * (nu.re + 1))) *
            ((nu.re + 1) ^ n * (n.factorial : ℝ)) := by
        rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        ring
      _ ≤ (‖generalICoeff nu (n + 1)‖ *
          (((n : ℝ) + 1) * ‖(n : ℂ) + nu + 1‖)) *
            ((nu.re + 1) ^ n * (n.factorial : ℝ)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (generalICoeff_factor_lower nu n) hn)
            (norm_nonneg _)) hw
      _ = ‖generalICoeff nu n‖ * ((nu.re + 1) ^ n * (n.factorial : ℝ)) := by
        congr 1
        simpa [mul_comm, mul_left_comm, mul_assoc] using hrec
      _ ≤ _ := ih

/-- A proved coefficient majorant, with no supplied bound or convergence. -/
theorem generalICoeff_norm_le {nu : ℂ} (hnu : -1 < nu.re) (n : ℕ) :
    ‖generalICoeff nu n‖ ≤ ‖(Complex.Gamma (nu + 1))⁻¹‖ /
      ((nu.re + 1) ^ n * (n.factorial : ℝ)) := by
  have hd : 0 < nu.re + 1 := by linarith
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  exact (le_div_iff₀ (mul_pos (pow_pos hd _) hf)).mpr
    (generalICoeff_weighted_norm_le hnu n)

theorem summable_norm_generalICoeff_mul_pow {nu : ℂ}
    (hnu : -1 < nu.re) (R : ℝ) (hR : 0 ≤ R) :
    Summable (fun n => ‖generalICoeff nu n‖ * R ^ n) := by
  have hmajor := (Real.summable_pow_div_factorial (R / (nu.re + 1))).mul_left
    ‖(Complex.Gamma (nu + 1))⁻¹‖
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hR _)) (fun n => ?_) hmajor
  calc
    ‖generalICoeff nu n‖ * R ^ n ≤
        (‖(Complex.Gamma (nu + 1))⁻¹‖ /
          ((nu.re + 1) ^ n * (n.factorial : ℝ))) * R ^ n :=
      mul_le_mul_of_nonneg_right (generalICoeff_norm_le hnu n) (pow_nonneg hR _)
    _ = ‖(Complex.Gamma (nu + 1))⁻¹‖ *
        ((R / (nu.re + 1)) ^ n / (n.factorial : ℝ)) := by
      rw [div_pow]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

theorem summable_norm_generalICore {nu : ℂ} (hnu : -1 < nu.re) (z : ℂ) :
    Summable (fun n => ‖generalICoeff nu n * z ^ n‖) := by
  simpa only [norm_mul, norm_pow] using
    summable_norm_generalICoeff_mul_pow hnu ‖z‖ (norm_nonneg z)

theorem generalICore_hasSum {nu : ℂ} (hnu : -1 < nu.re) (z : ℂ) :
    HasSum (fun n => generalICoeff nu n * z ^ n) (generalICore nu z) :=
  (summable_norm_generalICore hnu z).of_norm.hasSum

theorem generalICore_tendstoUniformlyOn {nu : ℂ} (hnu : -1 < nu.re)
    (R : ℝ) (hR : 0 ≤ R) :
    TendstoUniformlyOn
      (fun N z => ∑ n ∈ Finset.range N, generalICoeff nu n * z ^ n)
      (generalICore nu) atTop {z : ℂ | ‖z‖ ≤ R} := by
  apply tendstoUniformlyOn_tsum_nat (summable_norm_generalICoeff_mul_pow hnu R hR)
  intro n z hz
  simp only [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hz n)
    (norm_nonneg _)

def generalICoreSeries (nu : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (generalICoeff nu)

theorem generalICoreSeries_radius {nu : ℂ} (hnu : -1 < nu.re) :
    (generalICoreSeries nu).radius = ∞ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro R
  simpa only [generalICoreSeries, FormalMultilinearSeries.ofScalars_norm] using
    summable_norm_generalICoeff_mul_pow hnu (R : ℝ) R.coe_nonneg

theorem generalICoreSeries_sum (nu : ℂ) :
    (generalICoreSeries nu).sum = generalICore nu := by
  funext z
  simpa only [generalICoreSeries, FormalMultilinearSeries.ofScalarsSum,
    generalICore, smul_eq_mul] using
      FormalMultilinearSeries.ofScalars_sum_eq (generalICoeff nu) z

theorem analyticAt_generalICore {nu : ℂ} (hnu : -1 < nu.re) (z : ℂ) :
    AnalyticAt ℂ (generalICore nu) z := by
  have hr := generalICoreSeries_radius hnu
  have hp := (generalICoreSeries nu).hasFPowerSeriesOnBall (by rw [hr]; simp)
  rw [generalICoreSeries_sum] at hp
  exact hp.analyticAt_of_mem (by simp [hr])

theorem continuous_generalICore {nu : ℂ} (hnu : -1 < nu.re) :
    Continuous (generalICore nu) :=
  continuous_iff_continuousAt.mpr fun z => (analyticAt_generalICore hnu z).continuousAt

theorem generalICore_zero (nu : ℂ) :
    generalICore nu 0 = (Complex.Gamma (nu + 1))⁻¹ := by
  rw [← generalICoreSeries_sum]
  change FormalMultilinearSeries.ofScalarsSum (generalICoeff nu) 0 = _
  simp [generalICoeff]

/-- Absolute convergence of the literal modified-I series, including its
complex-power prefactor. On positive q this is the usual principal branch. -/
theorem summable_norm_generalI {nu : ℂ} (hnu : -1 < nu.re) (q : ℝ) :
    Summable (fun n => ‖(((q / 2 : ℝ) : ℂ) ^ nu) *
      (generalICoeff nu n * ((((q / 2 : ℝ) : ℂ)) ^ 2) ^ n)‖) := by
  simpa only [norm_mul] using
    (summable_norm_generalICore hnu ((((q / 2 : ℝ) : ℂ)) ^ 2)).mul_left
      ‖(((q / 2 : ℝ) : ℂ) ^ nu)‖

theorem generalI_hasSum {nu : ℂ} (hnu : -1 < nu.re) (q : ℝ) :
    HasSum (fun n => (((q / 2 : ℝ) : ℂ) ^ nu) *
      (generalICoeff nu n * ((((q / 2 : ℝ) : ℂ)) ^ 2) ^ n)) (generalI nu q) :=
  (generalICore_hasSum hnu ((((q / 2 : ℝ) : ℂ)) ^ 2)).mul_left _

/-- Local uniform convergence of the literal I series on the positive q-axis.
The compact-set bounds are derived from continuity; none is a supplier input. -/
theorem generalI_tendstoUniformlyOn_compact {nu : ℂ} (hnu : -1 < nu.re)
    {K : Set ℝ} (hK : IsCompact K) (hpos : ∀ q ∈ K, 0 < q) :
    TendstoUniformlyOn
      (fun N q => ∑ n ∈ Finset.range N,
        (((q / 2 : ℝ) : ℂ) ^ nu) *
          (generalICoeff nu n * ((((q / 2 : ℝ) : ℂ)) ^ 2) ^ n))
      (generalI nu) atTop K := by
  have hb : Continuous (fun q : ℝ => ((q / 2 : ℝ) : ℂ)) := by fun_prop
  have hp : ContinuousOn (fun q : ℝ => (((q / 2 : ℝ) : ℂ) ^ nu)) K :=
    hb.continuousOn.cpow_const (fun q hq => Or.inl (by
      simpa using (div_pos (hpos q hq) (by norm_num : (0 : ℝ) < 2))))
  have hz : Continuous (fun q : ℝ => (((q / 2 : ℝ) : ℂ)) ^ 2) := hb.pow 2
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn hp
  obtain ⟨R₀, hR₀⟩ := hK.exists_bound_of_continuousOn hz.continuousOn
  let C := max C₀ 0
  let R := max R₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  have hR : 0 ≤ R := le_max_right _ _
  have hmajor := (summable_norm_generalICoeff_mul_pow hnu R hR).mul_left C
  have hu := tendstoUniformlyOn_tsum_nat hmajor
    (s := K) (f := fun n q => (((q / 2 : ℝ) : ℂ) ^ nu) *
      (generalICoeff nu n * ((((q / 2 : ℝ) : ℂ)) ^ 2) ^ n))
    (fun n q hq => show ‖(((q / 2 : ℝ) : ℂ) ^ nu) *
        (generalICoeff nu n * ((((q / 2 : ℝ) : ℂ)) ^ 2) ^ n)‖ ≤
        C * (‖generalICoeff nu n‖ * R ^ n) from by
      rw [norm_mul, norm_mul, norm_pow]
      apply mul_le_mul ((hC₀ q hq).trans (le_max_left _ _))
      · exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _)
            ((hR₀ q hq).trans (le_max_left _ _)) n) (norm_nonneg _)
      · exact mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
      · exact hC)
  have heq : (fun q : ℝ => ∑' n, (((q / 2 : ℝ) : ℂ) ^ nu) *
      (generalICoeff nu n * ((((q / 2 : ℝ) : ℂ)) ^ 2) ^ n)) = generalI nu :=
    funext fun q => (generalI_hasSum hnu q).tsum_eq
  rw [heq] at hu
  exact hu

end ImbalancedChen.Part3.GeneralComplexISeriesSourceOnly
