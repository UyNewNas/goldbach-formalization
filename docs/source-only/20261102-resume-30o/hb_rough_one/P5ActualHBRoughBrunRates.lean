import ImbalancedChen.P5ActualHBRoughBrunFinite
import ImbalancedChen.P5OriginalOneLongExplicitBrunRates
import ImbalancedChen.Part3ActualRoughContourParameters
import AnalyticNumberTheory.Mertens.PartialSummation

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Real x throughout. Exact z=x^(1/(loglog x)^3), h=2 floor((loglog x)^2),
next order h+1, and the literal finite prime sum. The natural-parameter
archived exponential-series inequality is reused only in its scalar form.
Mertens is the existing precise classical source; no rough cancellation
or Brun-gap asymptotic is assumed.
-/
namespace ImbalancedChen.P5Z.ActualHBRoughBrunRates
noncomputable section
open Classical Filter Finset
open scoped Topology BigOperators
open ActualHBRoughBrunFinite
open ImbalancedChen.Part3.ActualRoughContourParameters20261026b
open OriginalOneLongE5FiniteBudget Part3.BrunFactorialRecurrenceE1

def loglog (x : ℝ) : ℝ := Real.log (Real.log x)
def halfOrder (x : ℝ) : ℕ := Nat.floor ((loglog x)^2)
def nextOrder (x : ℝ) : ℕ := 2*halfOrder x+1
def supportSize (x : ℝ) : ℝ := roughZ x ^ nextOrder x
def epsilon (x : ℝ) : ℝ := gapDensity (roughZ x) (halfOrder x)

theorem tendsto_loglog : Tendsto loglog atTop atTop :=
  Real.tendsto_log_atTop.comp Real.tendsto_log_atTop

theorem nextOrder_bounds (x : ℝ) (hL : 1 ≤ loglog x) :
    (loglog x)^2 ≤ (nextOrder x : ℝ) ∧
      (nextOrder x : ℝ) ≤ 3*(loglog x)^2 := by
  have hflo := Nat.floor_le (sq_nonneg (loglog x))
  have hfhi := Nat.lt_floor_add_one ((loglog x)^2)
  unfold nextOrder halfOrder
  push_cast
  constructor <;> nlinarith [sq_nonneg (loglog x-1)]

theorem eventually_actual_cutoff :
    ∀ᶠ x : ℝ in atTop, 1 < x ∧ 1 ≤ roughZ x ∧ roughZ x ≤ x := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    tendsto_loglog.eventually (eventually_ge_atTop 1)] with x hx hL
  have hLp : 0 < loglog x := zero_lt_one.trans_le hL
  have hc : 1 ≤ (loglog x)^3 := by
    simpa using pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) hL 3
  have he : 1/(loglog x)^3 ≤ 1 := (div_le_one (pow_pos hLp 3)).mpr hc
  refine ⟨hx, Real.one_le_rpow hx.le (by positivity), ?_⟩
  simpa only [roughZ, loglog, Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le hx.le he

/-- The threshold precedes every finite chart alphabet below real x. -/
theorem eventually_real_chart_harmonic :
    ∀ᶠ x : ℝ in atTop, ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, (p : ℝ) ≤ x) →
        chartHarmonic P ≤ 2*loglog x := by
  obtain ⟨C, hC, hmertens⟩ := AnalyticNumberTheory.Mertens.mertensSecond_nat
  filter_upwards [eventually_ge_atTop (max 4 (Real.exp 1+2)),
    tendsto_loglog.eventually
      (eventually_ge_atTop (AnalyticNumberTheory.Mertens.mertensSecondConstant+C))]
    with x hx hL
  intro P hP hcap
  have hx4 : 4 ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 ≤ x := by linarith
  have hN : 2 ≤ Nat.floor x := (Nat.le_floor_iff hx0).mpr (by linarith)
  have hexp : Real.exp 1 ≤ (Nat.floor x : ℝ) := by
    have hf := Nat.lt_floor_add_one x
    have he := (le_max_right (4 : ℝ) (Real.exp 1+2)).trans hx
    linarith
  have hlogN : 1 ≤ Real.log (Nat.floor x : ℝ) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hexp
  have hNpos : (0 : ℝ) < Nat.floor x := (Real.exp_pos 1).trans_le hexp
  have hll : Real.log (Real.log (Nat.floor x : ℝ)) ≤ loglog x := by
    exact Real.log_le_log (by linarith)
      (Real.log_le_log hNpos (Nat.floor_le hx0))
  have hsub : P ⊆ AnalyticNumberTheory.Mertens.primesUpTo (Nat.floor x) := by
    intro p hp
    exact AnalyticNumberTheory.Mertens.mem_primesUpTo.mpr
      ⟨hP p hp, (Nat.le_floor_iff hx0).mpr (hcap p hp)⟩
  have hsum : chartHarmonic P ≤
      AnalyticNumberTheory.Mertens.primeReciprocalSum (Nat.floor x) := by
    unfold chartHarmonic AnalyticNumberTheory.Mertens.primeReciprocalSum
    simpa only [one_div] using Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun p _ _ => (by positivity : (0 : ℝ) ≤ 1/(p : ℝ)))
  have he := (abs_le.mp (hmertens (Nat.floor x) hN)).2
  have hrem : C/Real.log (Nat.floor x : ℝ) ≤ C := div_le_self hC.le hlogN
  linarith

theorem eventually_actual_harmonic :
    ∀ᶠ x : ℝ in atTop,
      0 ≤ chartHarmonic (chartPrimes (roughZ x)) ∧
        chartHarmonic (chartPrimes (roughZ x)) ≤ 2*loglog x := by
  filter_upwards [eventually_actual_cutoff, eventually_real_chart_harmonic] with x hz hH
  refine ⟨by unfold chartHarmonic; positivity, ?_⟩
  apply hH _ (chartPrimes_prime _)
  intro p hp
  exact ((mem_chartPrimes (show 0 ≤ roughZ x by linarith [hz.2.1]) p).mp hp).2.trans hz.2.2

/-- The exact next support is subpower, without replacing the cutoff or
rounding the growing Brun order. -/
theorem eventually_support_le_power (delta : ℝ) (hd : 0 < delta) :
    ∀ᶠ x : ℝ in atTop, 1 < x ∧ 1 ≤ roughZ x ∧ supportSize x ≤ x^delta := by
  filter_upwards [eventually_actual_cutoff,
    tendsto_loglog.eventually (eventually_ge_atTop (max 1 (3/delta)))] with x hz hL
  have hL1 : 1 ≤ loglog x := (le_max_left _ _).trans hL
  have hLp : 0 < loglog x := zero_lt_one.trans_le hL1
  have hx0 : 0 < x := zero_lt_one.trans hz.1
  have hlogx : 0 ≤ Real.log x := (Real.log_pos hz.1).le
  have hz0 : 0 < roughZ x := zero_lt_one.trans_le hz.2.1
  have horder := (nextOrder_bounds x hL1).2
  have hdelta : 3 ≤ delta*loglog x :=
    (div_le_iff₀ hd).mp ((le_max_right _ _).trans hL)
  refine ⟨hz.1, hz.2.1, ?_⟩
  apply (Real.log_le_log_iff (pow_pos hz0 _) (Real.rpow_pos_of_pos hx0 _)).mp
  rw [supportSize, Real.log_pow, roughZ, Real.log_rpow hx0, Real.log_rpow hx0]
  change (nextOrder x : ℝ)*((1/(loglog x)^3)*Real.log x) ≤ delta*Real.log x
  calc
    _ ≤ (3*(loglog x)^2)*((1/(loglog x)^3)*Real.log x) :=
      mul_le_mul_of_nonneg_right horder (by positivity)
    _ = 3*Real.log x/loglog x := by field_simp [hLp.ne']; ring
    _ ≤ delta*Real.log x := (div_le_iff₀ hLp).mpr (by
      have hh := mul_le_mul_of_nonneg_right hdelta hlogx
      nlinarith)

/-- The actual h+1 support lies strictly below U^(1/4), simultaneously
over every U>=x^xi. No upper restriction on U is needed. -/
theorem eventually_support_lt_quarter (xi : ℝ) (hxi : 0 < xi) :
    ∀ᶠ x : ℝ in atTop, ∀ U : ℝ, x^xi ≤ U →
      supportSize x < U^(1/4 : ℝ) := by
  filter_upwards [eventually_support_le_power (xi/8) (by linarith)] with x hx
  intro U hU
  have hx0 : 0 < x := zero_lt_one.trans hx.1
  have hp : x^(xi/8) < x^(xi/4) :=
    Real.rpow_lt_rpow_of_exponent_lt hx.1 (by linarith)
  have hUq : x^(xi/4) ≤ U^(1/4 : ℝ) := by
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg hx0.le _) hU
      (by norm_num : (0 : ℝ) ≤ 1/4)
    rw [← Real.rpow_mul hx0.le] at hh
    convert hh using 1 <;> ring
  exact hx.2.2.trans_lt (hp.trans_le hUq)

theorem eventually_epsilon_le_exp :
    ∀ᶠ x : ℝ in atTop, epsilon x ≤ Real.exp (-((loglog x)^2)) := by
  filter_upwards [eventually_actual_harmonic,
    tendsto_loglog.eventually (eventually_ge_atTop (max 1 (2*Real.exp 2)))] with x hH hL
  have hL1 : 1 ≤ loglog x := (le_max_left _ _).trans hL
  have hL0 : 0 ≤ loglog x := by linarith
  have hLexp : 2*Real.exp 2 ≤ loglog x := (le_max_right _ _).trans hL
  have hlo := (nextOrder_bounds x hL1).1
  have hf := OriginalOneLongExplicitBrunRates.factorial_gap_le_exp
    (chartHarmonic (chartPrimes (roughZ x))) (nextOrder x) hH.1
  change epsilon x ≤ _ at hf
  refine hf.trans (Real.exp_le_exp.mpr ?_)
  have hh := mul_le_mul_of_nonneg_left hH.2 (Real.exp_pos 2).le
  have hs := mul_le_mul_of_nonneg_right hLexp hL0
  nlinarith

/-- Every real fixed log power is paid at one threshold before q and the
interval vary. No support factor multiplies this gap. -/
theorem eventually_epsilon_log_saving (A : ℝ) :
    ∀ᶠ x : ℝ in atTop, 0 < Real.log x ∧
      epsilon x ≤ 1/(Real.log x)^A := by
  filter_upwards [eventually_epsilon_le_exp, eventually_gt_atTop (1 : ℝ),
    tendsto_loglog.eventually (eventually_ge_atTop (max 0 A))] with x he hx hL
  have hlp : 0 < Real.log x := Real.log_pos hx
  have hL0 : 0 ≤ loglog x := (le_max_left _ _).trans hL
  have hLA : A ≤ loglog x := (le_max_right _ _).trans hL
  refine ⟨hlp, he.trans ?_⟩
  calc
    _ ≤ Real.exp (-A*loglog x) := Real.exp_le_exp.mpr (by
      have hm := mul_le_mul_of_nonneg_right hLA hL0
      nlinarith)
    _ = 1/(Real.log x)^A := by
      rw [Real.rpow_def_of_pos hlp, one_div, ← Real.exp_neg]
      congr 1
      unfold loglog
      ring

theorem eventually_logPower_le_power (A delta : ℝ) (hd : 0 < delta) :
    ∀ᶠ x : ℝ in atTop, 1 < x ∧ (Real.log x)^A ≤ x^delta := by
  have hdecay := (isLittleO_log_rpow_rpow_atTop A hd).tendsto_div_nhds_zero
  filter_upwards [hdecay.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    eventually_gt_atTop (1 : ℝ)] with x hs hx
  refine ⟨hx, ?_⟩
  exact (div_le_one (Real.rpow_pos_of_pos (zero_lt_one.trans hx) _)).mp hs.le

/-- Power remainder and factorial density are paid separately. -/
theorem eventually_actual_brun_payments (xi A : ℝ) (hxi : 0 < xi) :
    ∀ᶠ x : ℝ in atTop, 1 < x ∧ 1 ≤ roughZ x ∧ 0 < Real.log x ∧
      supportSize x ≤ x^xi/(Real.log x)^A ∧
      epsilon x ≤ 1/(Real.log x)^A ∧
      ∀ U : ℝ, x^xi ≤ U → supportSize x < U^(1/4 : ℝ) := by
  filter_upwards [eventually_support_le_power (xi/2) (by linarith),
    eventually_logPower_le_power A (xi/2) (by linarith),
    eventually_epsilon_log_saving A, eventually_support_lt_quarter xi hxi]
    with x hY hlog he hquarter
  have hx0 : 0 < x := zero_lt_one.trans hY.1
  have hden : 0 < (Real.log x)^A := Real.rpow_pos_of_pos he.1 _
  refine ⟨hY.1, hY.2.1, he.1, ?_, he.2, hquarter⟩
  apply (le_div_iff₀ hden).mpr
  calc
    supportSize x*(Real.log x)^A ≤ x^(xi/2)*x^(xi/2) :=
      mul_le_mul hY.2.2 hlog.2 hden.le (Real.rpow_nonneg hx0.le _)
    _ = x^xi := by rw [← Real.rpow_add hx0]; congr 1; ring

end
end ImbalancedChen.P5Z.ActualHBRoughBrunRates
