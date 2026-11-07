import ImbalancedChen.ActualSmallEulerNormalization
import ImbalancedChen.CenterEulerTail
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Leading Euler normalization at every positive power cutoff

The ordinary strict prime product is evaluated at the inclusive Mertens
endpoint `ceil(N^a) - 1`. Its logarithm has scale `a * log N`, and the
proved Mertens estimate supplies the exact Euler--Mascheroni constant.
The finite odd-prime product and the actual target-prime tail then give
the leading constant for the same target-dependent sieve Euler product.
No density asymptotic or prime-distribution assertion is assumed.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology

private theorem tendsto_power_cutoff {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ a) atTop atTop :=
  (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop

private theorem tendsto_power_cap {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => Nat.ceil ((N : ℝ) ^ a)) atTop atTop :=
  tendsto_nat_ceil_atTop.comp (tendsto_power_cutoff ha)

private theorem tendsto_power_endpoint {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => Nat.ceil ((N : ℝ) ^ a) - 1) atTop atTop :=
  (tendsto_sub_atTop_nat 1).comp (tendsto_power_cap ha)

private theorem tendsto_natural_log :
    Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

private theorem tendsto_power_endpoint_div_power {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => ((Nat.ceil ((N : ℝ) ^ a) - 1 : ℕ) : ℝ) /
      (N : ℝ) ^ a) atTop (𝓝 1) := by
  have hceil := tendsto_nat_ceil_div_atTop.comp (tendsto_power_cutoff ha)
  have hinv := (tendsto_power_cutoff ha).const_div_atTop (1 : ℝ)
  have hlim : Tendsto (fun N : ℕ =>
      (Nat.ceil ((N : ℝ) ^ a) : ℝ) / (N : ℝ) ^ a - 1 / (N : ℝ) ^ a)
      atTop (𝓝 1) := by
    simpa only [sub_zero, Function.comp_def] using hceil.sub hinv
  apply hlim.congr'
  filter_upwards [(tendsto_power_cap ha).eventually (eventually_ge_atTop 1)] with N hN
  rw [Nat.cast_sub hN, Nat.cast_one, sub_div]

/-- The inclusive predecessor of the strict real cutoff has exactly the
same logarithmic scale. This includes integer values of the power cutoff. -/
theorem tendsto_log_power_endpoint_div_log {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => Real.log ((Nat.ceil ((N : ℝ) ^ a) - 1 : ℕ) : ℝ) /
      Real.log (N : ℝ)) atTop (𝓝 a) := by
  have hlogRel : Tendsto (fun N : ℕ =>
      Real.log (((Nat.ceil ((N : ℝ) ^ a) - 1 : ℕ) : ℝ) / (N : ℝ) ^ a))
      atTop (𝓝 0) := by
    simpa only [Real.log_one, Function.comp_def] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
        (tendsto_power_endpoint_div_power ha)
  have hsmall : Tendsto (fun N : ℕ =>
      Real.log (((Nat.ceil ((N : ℝ) ^ a) - 1 : ℕ) : ℝ) / (N : ℝ) ^ a) /
        Real.log (N : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_one_div] using
      hlogRel.mul (tendsto_natural_log.const_div_atTop (1 : ℝ))
  have hlim : Tendsto (fun N : ℕ => a +
      Real.log (((Nat.ceil ((N : ℝ) ^ a) - 1 : ℕ) : ℝ) / (N : ℝ) ^ a) /
        Real.log (N : ℝ)) atTop (𝓝 a) := by
    simpa only [add_zero] using hsmall.const_add a
  apply hlim.congr'
  filter_upwards [(tendsto_power_endpoint ha).eventually (eventually_ge_atTop 1),
    eventually_ge_atTop (2 : ℕ)] with N hx hN
  have hxpos : (0 : ℝ) < (Nat.ceil ((N : ℝ) ^ a) - 1 : ℕ) := by
    exact_mod_cast (show 0 < Nat.ceil ((N : ℝ) ^ a) - 1 by omega)
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNpos := lt_trans zero_lt_one hN1
  rw [Real.log_div hxpos.ne' (Real.rpow_pos_of_pos hNpos a).ne',
    Real.log_rpow hNpos]
  field_simp [(Real.log_pos hN1).ne']
  ring

private theorem tendsto_mertensPrimeProduct_mul_log :
    Tendsto (fun n : ℕ =>
      MathlibNt.SieveTheory.MertensTheorem.primeProduct n * Real.log (n : ℝ))
      atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) := by
  obtain ⟨C, hMertens⟩ := MathlibNt.SieveTheory.MertensTheorem.mertens_product_formula
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  have hsmall : ∀ᶠ n : ℕ in atTop, C / Real.log (n : ℝ) < epsilon :=
    (tendsto_order.1 (tendsto_natural_log.const_div_atTop C)).2 epsilon hepsilon
  filter_upwards [hsmall, eventually_ge_atTop (2 : ℕ)] with n hsmallN hn
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  rw [Real.dist_eq]
  have heq :
      |MathlibNt.SieveTheory.MertensTheorem.primeProduct n * Real.log (n : ℝ) -
        Real.exp (-Real.eulerMascheroniConstant)| =
      |MathlibNt.SieveTheory.MertensTheorem.primeProduct n -
        Real.exp (-Real.eulerMascheroniConstant) / Real.log (n : ℝ)| *
          Real.log (n : ℝ) := by
    have hid :
        (MathlibNt.SieveTheory.MertensTheorem.primeProduct n -
          Real.exp (-Real.eulerMascheroniConstant) / Real.log (n : ℝ)) *
            Real.log (n : ℝ) =
        MathlibNt.SieveTheory.MertensTheorem.primeProduct n * Real.log (n : ℝ) -
          Real.exp (-Real.eulerMascheroniConstant) := by
      rw [sub_mul, div_mul_cancel₀ _ hlog.ne']
    rw [← hid, abs_mul, abs_of_pos hlog]
  rw [heq]
  have hbound := mul_le_mul_of_nonneg_right (hMertens n hn) hlog.le
  have hsimp : C / Real.log (n : ℝ) ^ 2 * Real.log (n : ℝ) =
      C / Real.log (n : ℝ) := by field_simp
  rw [hsimp] at hbound
  exact hbound.trans_lt hsmallN

/-- Mertens' exact leading constant at the literal strict power cutoff. -/
theorem tendsto_primeEulerProduct_power_mul_log {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => primeEulerProduct (Nat.ceil ((N : ℝ) ^ a)) *
      Real.log (N : ℝ)) atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant) / a)) := by
  have hprod := tendsto_mertensPrimeProduct_mul_log.comp (tendsto_power_endpoint ha)
  have hratio := tendsto_log_power_endpoint_div_log ha
  have hlim := hprod.div hratio ha.ne'
  apply hlim.congr'
  filter_upwards [(tendsto_power_endpoint ha).eventually (eventually_ge_atTop 2)]
    with N hx
  have hcap : 1 ≤ Nat.ceil ((N : ℝ) ^ a) := by omega
  have hx1 : (1 : ℝ) < (Nat.ceil ((N : ℝ) ^ a) - 1 : ℕ) := by
    exact_mod_cast (show 1 < Nat.ceil ((N : ℝ) ^ a) - 1 by omega)
  rw [primeEulerProduct_eq_mertensPrimeProduct_pred hcap]
  dsimp only [Function.comp_def, Pi.div_apply]
  rw [div_div_eq_mul_div, mul_right_comm,
    mul_div_cancel_right₀ _ (Real.log_pos hx1).ne']

private theorem tendsto_power_odd_div_tail {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => oddEulerProduct (Nat.ceil ((N : ℝ) ^ a)) /
      (twinPrimeConstant * centerEulerTail N ((N : ℝ) ^ a))) atTop (𝓝 1) := by
  have hnum := tendsto_oddEulerProduct.comp (tendsto_power_cap ha)
  have hden : Tendsto (fun N : ℕ => twinPrimeConstant *
      centerEulerTail N ((N : ℝ) ^ a)) atTop (𝓝 twinPrimeConstant) := by
    simpa only [mul_one] using (tendsto_centerEulerTail_power ha).const_mul twinPrimeConstant
  have h := hnum.div hden twinPrimeConstant_pos.ne'
  change Tendsto (fun N : ℕ => oddEulerProduct (Nat.ceil ((N : ℝ) ^ a)) /
    (twinPrimeConstant * centerEulerTail N ((N : ℝ) ^ a)))
    atTop (𝓝 (twinPrimeConstant / twinPrimeConstant)) at h
  simpa only [div_self twinPrimeConstant_pos.ne'] using h

/-- The actual target-dependent Euler product has the full manuscript
constant at every fixed positive power cutoff, along positive even targets. -/
theorem tendsto_finiteSieveDensity_power_normalized {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => finiteSieveDensity N (Nat.ceil ((N : ℝ) ^ a)) *
      Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (2 * Real.exp (-Real.eulerMascheroniConstant) / a)) := by
  have hlim : Tendsto (fun N : ℕ =>
      2 * (primeEulerProduct (Nat.ceil ((N : ℝ) ^ a)) * Real.log (N : ℝ)) *
        (oddEulerProduct (Nat.ceil ((N : ℝ) ^ a)) /
          (twinPrimeConstant * centerEulerTail N ((N : ℝ) ^ a))))
      atTop (𝓝 (2 * Real.exp (-Real.eulerMascheroniConstant) / a)) := by
    simpa only [mul_one, mul_div_assoc] using
      ((tendsto_primeEulerProduct_power_mul_log ha).const_mul 2).mul
        (tendsto_power_odd_div_tail ha)
  apply (hlim.mono_left inf_le_left).congr'
  simp only [Filter.EventuallyEq, Filter.eventually_inf_principal]
  filter_upwards [(tendsto_power_cap ha).eventually (eventually_gt_atTop 2)]
    with N hcap
  rintro ⟨hNpos, hEven⟩
  have hid := normalizedFiniteSieveDensity_eq_odd_div_tail
    (Nat.ne_of_gt hNpos) hEven hcap
  change normalizedFiniteSieveDensity N (Nat.ceil ((N : ℝ) ^ a)) =
    oddEulerProduct (Nat.ceil ((N : ℝ) ^ a)) /
      (twinPrimeConstant * centerEulerTail N ((N : ℝ) ^ a)) at hid
  rw [← hid]
  unfold normalizedFiniteSieveDensity
  field_simp [(primeEulerProduct_pos (Nat.ceil ((N : ℝ) ^ a))).ne',
    (singularSeries_pos N).ne']

/-- Ratios at two fixed positive power cutoffs cancel the actual singular
series and the Euler--Mascheroni constant, leaving b/a. -/
theorem tendsto_finiteSieveDensity_power_ratio {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun N : ℕ =>
      finiteSieveDensity N (Nat.ceil ((N : ℝ) ^ a)) /
        finiteSieveDensity N (Nat.ceil ((N : ℝ) ^ b)))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 (b / a)) := by
  have hden : 2 * Real.exp (-Real.eulerMascheroniConstant) / b ≠ 0 := by positivity
  have hlim := (tendsto_finiteSieveDensity_power_normalized ha).div
    (tendsto_finiteSieveDensity_power_normalized hb) hden
  have hconstant :
      (2 * Real.exp (-Real.eulerMascheroniConstant) / a) /
        (2 * Real.exp (-Real.eulerMascheroniConstant) / b) = b / a := by
    field_simp [ha.ne', hb.ne', Real.exp_ne_zero]
  rw [hconstant] at hlim
  apply hlim.congr'
  simp only [Filter.EventuallyEq, Filter.eventually_inf_principal, Pi.div_apply]
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  intro _hEven
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  rw [div_div_div_cancel_right₀ (singularSeries_pos N).ne',
    mul_div_mul_right _ _ (Real.log_pos hN1).ne']

end

end ImbalancedChen
