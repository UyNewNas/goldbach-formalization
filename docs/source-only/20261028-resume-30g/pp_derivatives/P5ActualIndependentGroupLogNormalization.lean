import ImbalancedChen.P5ActualEtaPsiOccurrenceBudget
import ImbalancedChen.P5NativeSelectedFourOrderedEuler
import ImbalancedChen.P4BSmoothProfileDirectionalDerivativeBudget
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib

/-!
SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
The actual reciprocal-log factor of EACH original independent group.
Its smooth zero-near-origin extension agrees with 1/log n at EVERY
natural n, including 0 and 1. It supplies no primality or modulus filter.
Finite scalar jets and arbitrary repeated occurrence words are derived.
-/
namespace ImbalancedChen.P5Z.ActualIndependentGroupLogNormalization
noncomputable section
open Classical Set Filter Topology
open scoped BigOperators
open ActualEtaPsiOccurrenceBudget NativeSelectedFourOrderedEuler
open AllWordAmbientOccurrenceBound OccurrenceWordFourFactorLeibniz
open AdmissibleAllRankIntegerGeometricFamily GroupedOccurrenceLogShift

def logGate (x : ℝ) : ℝ := etaLog (2*x - Real.log 2)
def reciprocalLogChart (x : ℝ) : ℝ := if 0 < x then logGate x / x else 0
def logReciprocal (u : ℝ) : ℝ := if 0 < u then reciprocalLogChart (Real.log u) else 0

theorem logGate_smooth : ContDiff ℝ ∞ logGate :=
  etaLog_smooth.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem logGate_zero {x : ℝ} (hx : x ≤ Real.log 2 / 2) : logGate x = 0 :=
  etaLog_zero (by linarith)

theorem logGate_one {x : ℝ} (hx : Real.log 2 ≤ x) : logGate x = 1 :=
  etaLog_one (by linarith)

theorem reciprocalLogChart_zero {x : ℝ} (hx : x ≤ Real.log 2 / 2) :
    reciprocalLogChart x = 0 := by
  by_cases h : 0 < x
  · simp [reciprocalLogChart, h, logGate_zero hx]
  · simp [reciprocalLogChart, h]

theorem reciprocalLogChart_eq_inverse {x : ℝ} (hx : Real.log 2 ≤ x) :
    reciprocalLogChart x = 1 / x := by
  have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  simp [reciprocalLogChart, h2.trans_le hx, logGate_one hx]

theorem reciprocalLogChart_smooth : ContDiff ℝ ∞ reciprocalLogChart := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : 0 < x
  · have hraw : ContDiffAt ℝ ∞ (fun y => logGate y / y) x :=
      logGate_smooth.contDiffAt.div contDiffAt_id hx.ne'
    have heq : reciprocalLogChart =ᶠ[𝓝 x] (fun y => logGate y / y) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      simp [reciprocalLogChart, hy]
    exact hraw.congr_of_eventuallyEq heq
  · have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have heq : reciprocalLogChart =ᶠ[𝓝 x] 0 := by
      filter_upwards [Iio_mem_nhds (show x < Real.log 2 / 2 by linarith)] with y hy
      exact reciprocalLogChart_zero hy.le
    exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℝ)) x).
      congr_of_eventuallyEq heq

theorem inverse_iteratedDeriv_abs (n : ℕ) {x : ℝ} (hx : 0 < x) :
    |iteratedDeriv n (fun y : ℝ => 1/y) x| = (n.factorial : ℝ) / x^(n+1) := by
  have h := iteratedDerivWithin_one_div (𝕜 := ℝ) n isOpen_univ x (mem_univ x)
  rw [iteratedDerivWithin_univ] at h
  rw [h]
  have hz : (-1 - (n : ℤ)) = -((n+1 : ℕ) : ℤ) := by omega
  rw [hz, zpow_neg, zpow_natCast]
  simp [abs_mul, abs_pow, abs_inv, abs_of_pos hx, div_eq_mul_inv]

theorem inverse_iteratedDeriv_abs_le (n : ℕ) {a x : ℝ} (ha : 0 < a) (hx : a ≤ x) :
    |iteratedDeriv n (fun y : ℝ => 1/y) x| ≤ (n.factorial : ℝ) / a^(n+1) := by
  rw [inverse_iteratedDeriv_abs n (ha.trans_le hx)]
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (pow_pos ha (n+1))
    (pow_le_pow_left₀ ha.le hx (n+1))

/-- A derived finite constant; the reciprocal singularity is excluded by
the actual logGate floor, not by a formal bounded-derivative hypothesis. -/
theorem exists_reciprocalLogChart_order_bound (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x, |iteratedDeriv n reciprocalLogChart x| ≤ C := by
  obtain ⟨M, hM, hm⟩ := finite_order_constants etaLog exists_etaLog_order_bound n
  let a : ℝ := Real.log 2 / 4
  have ha : 0 < a := by dsimp [a]; exact div_pos (Real.log_pos (by norm_num)) (by norm_num)
  let C : ℝ := ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) *
    ((2 : ℝ)^j * M) * (((n-j).factorial : ℝ) / a^(n-j+1))
  refine ⟨max C 1, le_max_right _ _, ?_⟩
  intro x
  by_cases hx : x < a
  · have hzero : reciprocalLogChart =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [Iio_mem_nhds (show x < Real.log 2 / 2 by dsimp [a] at hx; linarith)] with y hy
      exact reciprocalLogChart_zero hy.le
    rw [Filter.EventuallyEq.iteratedDeriv_eq n hzero]
    simp only [iteratedDeriv_const, ite_self, abs_zero]
    exact zero_le_one.trans (le_max_right _ _)
  · have hax : a ≤ x := le_of_not_gt hx
    have hxp : 0 < x := ha.trans_le hax
    have heq : reciprocalLogChart =ᶠ[𝓝 x] (fun y => logGate y * (1/y)) := by
      filter_upwards [Ioi_mem_nhds hxp] with y hy
      simp [reciprocalLogChart, hy, div_eq_mul_inv]
    rw [Filter.EventuallyEq.iteratedDeriv_eq n heq]
    have hgate : ContDiffAt ℝ n logGate x := logGate_smooth.contDiffAt.of_le (by simp)
    have hinv : ContDiffAt ℝ n (fun y : ℝ => 1/y) x := contDiffAt_const.div contDiffAt_id hxp.ne'
    rw [iteratedDeriv_fun_mul hgate hinv]
    apply le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans ?_ (le_max_left C 1))
    apply Finset.sum_le_sum
    intro j hj
    have hjn : j ≤ n := by have := Finset.mem_range.mp hj; omega
    have hgj : |iteratedDeriv j logGate x| ≤ (2 : ℝ)^j * M := by
      have he : logGate = fun y => etaLog (-Real.log 2 + 2*y) := by funext y; unfold logGate; congr 1; ring
      rw [he, P4B.iteratedDeriv_comp_real_affine j etaLog etaLog_smooth,
        abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact mul_le_mul_of_nonneg_left (hm j hjn _) (by positivity)
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (n.choose j))]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hgj (Nat.cast_nonneg _))
      (inverse_iteratedDeriv_abs_le (n-j) ha hax) (abs_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (by positivity))

theorem logReciprocal_zero {u : ℝ} (hu : u ≤ 1) : logReciprocal u = 0 := by
  by_cases hp : 0 < u
  · have hl : Real.log u ≤ 0 := Real.log_nonpos hp.le hu
    have h2 : 0 ≤ Real.log (2 : ℝ) / 2 := div_nonneg (Real.log_pos (by norm_num)).le (by norm_num)
    simp [logReciprocal, hp, reciprocalLogChart_zero (hl.trans h2)]
  · simp [logReciprocal, hp]

theorem logReciprocal_smooth : ContDiff ℝ ∞ logReciprocal := by
  apply contDiff_iff_contDiffAt.mpr
  intro u
  by_cases hu : 0 < u
  · have hraw := reciprocalLogChart_smooth.contDiffAt.comp u (Real.contDiffAt_log hu.ne')
    have heq : logReciprocal =ᶠ[𝓝 u] (fun x => reciprocalLogChart (Real.log x)) := by
      filter_upwards [Ioi_mem_nhds hu] with x hx
      simp only [logReciprocal, if_pos hx]
    exact hraw.congr_of_eventuallyEq heq
  · have heq : logReciprocal =ᶠ[𝓝 u] 0 := by
      filter_upwards [Iio_mem_nhds (show u < (1 : ℝ) by linarith [le_of_not_gt hu])] with x hx
      exact logReciprocal_zero hx.le
    exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℝ)) u).
      congr_of_eventuallyEq heq

theorem logReciprocal_eq_inverse {u : ℝ} (hu : 2 ≤ u) :
    logReciprocal u = 1 / Real.log u := by
  have hp : 0 < u := lt_of_lt_of_le (by norm_num) hu
  simp only [logReciprocal, if_pos hp]
  exact reciprocalLogChart_eq_inverse (Real.log_le_log (by norm_num) hu)

/-- Exact on the HB integer group product too; n=0,1 are not silently
excluded as prime inputs. Thus no extra arithmetic filter or reserve is added. -/
theorem logReciprocal_nat (n : ℕ) : logReciprocal (n : ℝ) = 1 / Real.log (n : ℝ) := by
  by_cases hn : 2 ≤ n
  · exact logReciprocal_eq_inverse (by exact_mod_cast hn)
  · have hcases : n = 0 ∨ n = 1 := by omega
    rcases hcases with rfl | rfl <;> norm_num [logReciprocal, reciprocalLogChart]

def groupLogProduct {r : ℕ} (u : Fin r → ℝ) : ℝ := ∏ i, logReciprocal (u i)

def normalize {r : ℕ} (f : (Fin r → ℝ) → ℝ) (u : Fin r → ℝ) : ℝ :=
  f u * groupLogProduct u

theorem groupLogProduct_smooth (r : ℕ) : ContDiff ℝ ∞ (groupLogProduct (r := r)) := by
  unfold groupLogProduct
  apply contDiff_prod
  intro i hi
  exact logReciprocal_smooth.comp (contDiff_apply ℝ ℝ i)

theorem normalize_smooth {r : ℕ} (f : (Fin r → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (normalize f) := hf.mul (groupLogProduct_smooth r)

theorem normalize_nat {r : ℕ} (f : (Fin r → ℝ) → ℝ) (u : Fin r → ℕ) :
    normalize f (fun i => (u i : ℝ)) =
      f (fun i => (u i : ℝ)) / ∏ i, Real.log (u i : ℝ) := by
  unfold normalize groupLogProduct
  simp only [logReciprocal_nat, ← Finset.prod_div_distrib, Finset.prod_const_one, div_eq_mul_inv]

theorem normalize_nonzero {r : ℕ} {f : (Fin r → ℝ) → ℝ} {u : Fin r → ℝ}
    (hu : normalize f u ≠ 0) : f u ≠ 0 := (mul_ne_zero_iff.mp hu).1

theorem groupLogProduct_eventually_zero {r : ℕ} (u : Fin r → ℝ)
    (hu : ∃ i, u i ≤ 0) : groupLogProduct =ᶠ[𝓝 u] 0 := by
  obtain ⟨i, hi⟩ := hu
  have hopen : IsOpen {x : Fin r → ℝ | x i < 1} := isOpen_lt (continuous_apply i) continuous_const
  filter_upwards [hopen.mem_nhds (hi.trans_lt zero_lt_one)] with x hx
  exact Finset.prod_eq_zero (Finset.mem_univ i) (logReciprocal_zero hx.le)

/-- The per-group normalizer pulls back through the ORIGINAL owners. -/
theorem groupLogProduct_chart {r m : ℕ} (owner : Fin m → Fin r) (U : Fin m → ℝ)
    (hU : ∀ a, 0 < U a) :
    (fun z => groupLogProduct (fun i => groupProduct owner U i z)) =
      groupTensor owner (fun i => Real.log (groupBase owner U i)) (fun _ => reciprocalLogChart) := by
  funext z
  unfold groupLogProduct groupTensor
  apply Finset.prod_congr rfl
  intro i hi
  have hb : 0 < groupBase owner U i := groupBase_pos owner U hU i
  simp only [groupProduct, logReciprocal, if_pos (mul_pos hb (Real.exp_pos _)),
    Real.log_mul hb.ne' (Real.exp_pos _).ne', Real.log_exp]

theorem groupLogProduct_word_budget (rMax q : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ r ≤ rMax, ∀ m (owner : Fin m → Fin r)
      (U : Fin m → ℝ), (∀ a, 0 < U a) → ∀ (w : List (Fin m)) z,
      w.length ≤ q → |occWord w (fun y => groupLogProduct
        (fun i => groupProduct owner U i y)) z| ≤ C := by
  obtain ⟨M, hM, hm⟩ := finite_order_constants reciprocalLogChart exists_reciprocalLogChart_order_bound q
  refine ⟨M^rMax, one_le_pow₀ hM, ?_⟩
  intro r hr m owner U hU w z hw
  rw [groupLogProduct_chart owner U hU]
  exact (groupTensor_word_bound owner _ reciprocalLogChart w z M (zero_le_one.trans hM)
    (fun n hn => hm n (hn.trans hw))).trans (pow_le_pow_right₀ hM hr)

/-- All-real-point Euler budget, including the true zero neighbourhood
at nonpositive axes; no original rank is padded by a zero function. -/
theorem groupLogProduct_mixedEuler (rMax q : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ r ≤ rMax, ∀ (w : List (Fin r)) u,
      w.length ≤ q → |eulerWord w groupLogProduct u| ≤ C := by
  obtain ⟨C, hC, hb⟩ := groupLogProduct_word_budget rMax q
  refine ⟨C, hC, ?_⟩
  intro r hr w u hw
  by_cases hu : ∀ i, 0 < u i
  · have h := hb r hr r id u hu w 0 hw
    have hraw : |occWord w (fun y => groupLogProduct (multiplicativeChart u y)) 0| ≤ C := by
      simpa only [groupProduct_identity] using h
    rw [← orderedEuler_occurrence_dictionary groupLogProduct (groupLogProduct_smooth r) w u 0] at hraw
    simpa only [multiplicativeChart_zero] using hraw
  · obtain ⟨i, hi⟩ := not_forall.mp hu
    rw [(eulerWord_eventually_zero w groupLogProduct u
      (groupLogProduct_eventually_zero u ⟨i, le_of_not_gt hi⟩)).eq_of_nhds, abs_zero]
    exact zero_le_one.trans hC

end
end ImbalancedChen.P5Z.ActualIndependentGroupLogNormalization
