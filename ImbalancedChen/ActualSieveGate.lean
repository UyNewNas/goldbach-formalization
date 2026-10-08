import ImbalancedChen.LogCutoffError
import ImbalancedChen.PowerErrorBudget
import ImbalancedChen.SieveSourceCoprimality
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega

/-!
# The actual logarithmic cutoff clears the actual sieve cap

For the literal cutoff `T(N) = N / (log N)^10` and the natural cap
`ceil(N^(1/5))`, the geometric sieve gate holds eventually for every fixed
real `b > 1/2`. In particular it holds throughout the manuscript's interval
`1/2 < b < 1`, including all of its rational exponents.

The proof uses the genuine log-power limit from `PowerErrorBudget` twice.
First, `log(N)^10 = o(N^(1/4))` gives `N^(3/4) ≤ T(N)` eventually.
Second, `1 = o(N^(1/20))` absorbs the exact natural-ceiling loss and gives
`ceil(N^(1/5)) ≤ N^(1/4)`. Finally `b/(1+b) > 1/3` supplies the exponent
comparison. No growth hypothesis, pointwise gate, distribution estimate,
or counting estimate is assumed.

The final corollaries specialize the proved finite sieve-coprimality
lemmas to the actual cutoff and actual cap. The source, allowed-prime
sieving product, and retained additive-prime mask are unchanged.
-/

namespace ImbalancedChen

open Filter Topology

/-- The fixed logarithmic cutoff eventually dominates the three-quarter
power. Positivity of the literal cutoff is proved at the same time. -/
theorem eventually_threeQuarterPower_le_logCutoff :
    ∀ᶠ N : ℕ in atTop,
      0 < logCutoff N ∧ (N : ℝ) ^ (3 / 4 : ℝ) ≤ logCutoff N := by
  have hsmall : ∀ᶠ N : ℕ in atTop,
      (Real.log (N : ℝ)) ^ 10 / (N : ℝ) ^ (1 / 4 : ℝ) < 1 :=
    (tendsto_nat_log_pow_div_rpow 10 (by norm_num : (0 : ℝ) < 1 / 4)).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hsmall, eventually_ge_atTop (2 : ℕ)] with N hsmallN hN
  have hNreal : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_trans zero_lt_one hNreal
  have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos hNreal
  have hlogpow : (Real.log (N : ℝ)) ^ 10 < (N : ℝ) ^ (1 / 4 : ℝ) := by
    have h := (div_lt_iff₀ (Real.rpow_pos_of_pos hNpos (1 / 4 : ℝ))).mp hsmallN
    simpa only [one_mul] using h
  refine ⟨div_pos hNpos (pow_pos hlogpos 10), ?_⟩
  unfold logCutoff
  apply (le_div_iff₀ (pow_pos hlogpos 10)).mpr
  calc
    (N : ℝ) ^ (3 / 4 : ℝ) * (Real.log (N : ℝ)) ^ 10 ≤
        (N : ℝ) ^ (3 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left hlogpow.le
        (Real.rpow_nonneg (Nat.cast_nonneg N) (3 / 4 : ℝ))
    _ = (N : ℝ) := by
      rw [← Real.rpow_add hNpos]
      norm_num

/-- The exact natural ceiling of the fifth-root cap is eventually bounded
by the quarter power; the extra unit is absorbed by a proved limit. -/
theorem eventually_ceil_fifthRoot_le_quarterPower :
    ∀ᶠ N : ℕ in atTop,
      (Nat.ceil ((N : ℝ) ^ (1 / 5 : ℝ)) : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
  have hdecay : Tendsto (fun N : ℕ => 1 / (N : ℝ) ^ (1 / 20 : ℝ))
      atTop (𝓝 0) := by
    simpa only [pow_zero] using
      tendsto_nat_log_pow_div_rpow 0 (by norm_num : (0 : ℝ) < 1 / 20)
  have hsmall : ∀ᶠ N : ℕ in atTop,
      1 / (N : ℝ) ^ (1 / 20 : ℝ) < 1 / 2 :=
    hdecay.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℕ)] with N hsmallN hN
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le zero_lt_one hNreal
  have hgap : (2 : ℝ) ≤ (N : ℝ) ^ (1 / 20 : ℝ) := by
    have h := (div_lt_iff₀ (Real.rpow_pos_of_pos hNpos (1 / 20 : ℝ))).mp hsmallN
    linarith
  have hone : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 5 : ℝ) :=
    Real.one_le_rpow hNreal (by norm_num)
  have hnonneg : (0 : ℝ) ≤ (N : ℝ) ^ (1 / 5 : ℝ) :=
    Real.rpow_nonneg (Nat.cast_nonneg N) (1 / 5 : ℝ)
  calc
    (Nat.ceil ((N : ℝ) ^ (1 / 5 : ℝ)) : ℝ) ≤
        (N : ℝ) ^ (1 / 5 : ℝ) + 1 := (Nat.ceil_lt_add_one hnonneg).le
    _ ≤ 2 * (N : ℝ) ^ (1 / 5 : ℝ) := by linarith
    _ = (N : ℝ) ^ (1 / 5 : ℝ) * 2 := mul_comm _ _
    _ ≤ (N : ℝ) ^ (1 / 5 : ℝ) * (N : ℝ) ^ (1 / 20 : ℝ) :=
      mul_le_mul_of_nonneg_left hgap hnonneg
    _ = (N : ℝ) ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_add hNpos]
      norm_num

/-- The geometric gate for the original fixed cutoff and exact natural
sieve cap. The upper restriction `b < 1` is unnecessary for this gate. -/
theorem eventually_actual_sieve_gate {b : ℝ} (hb : 1 / 2 < b) :
    ∀ᶠ N : ℕ in atTop,
      0 < logCutoff N ∧
        (Nat.ceil ((N : ℝ) ^ (1 / 5 : ℝ)) : ℝ) ≤
          (logCutoff N) ^ (b / (1 + b)) := by
  have hden : 0 < 1 + b := by linarith
  have halpha : (1 / 3 : ℝ) < b / (1 + b) := by
    apply (lt_div_iff₀ hden).mpr
    linarith
  have halphaNonneg : 0 ≤ b / (1 + b) := by linarith
  have hexponent : (1 / 4 : ℝ) ≤ (3 / 4 : ℝ) * (b / (1 + b)) := by
    linarith
  filter_upwards [eventually_threeQuarterPower_le_logCutoff,
    eventually_ceil_fifthRoot_le_quarterPower, eventually_ge_atTop (1 : ℕ)]
    with N hcut hceil hN
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  refine ⟨hcut.1, ?_⟩
  calc
    (Nat.ceil ((N : ℝ) ^ (1 / 5 : ℝ)) : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := hceil
    _ ≤ (N : ℝ) ^ ((3 / 4 : ℝ) * (b / (1 + b))) :=
      Real.rpow_le_rpow_of_exponent_le hNreal hexponent
    _ = ((N : ℝ) ^ (3 / 4 : ℝ)) ^ (b / (1 + b)) :=
      Real.rpow_mul (Nat.cast_nonneg N) (3 / 4 : ℝ) (b / (1 + b))
    _ ≤ (logCutoff N) ^ (b / (1 + b)) :=
      Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg N) (3 / 4 : ℝ))
        hcut.2 halphaNonneg

/-- A natural-numerator formulation for fixed rational exponents.
`den < 2 * num` is exactly the needed strict lower restriction. -/
theorem eventually_actual_sieve_gate_rational (num den : ℕ)
    (hden : 0 < den) (hhalf : den < 2 * num) :
    ∀ᶠ N : ℕ in atTop,
      0 < logCutoff N ∧
        (Nat.ceil ((N : ℝ) ^ (1 / 5 : ℝ)) : ℝ) ≤
          (logCutoff N) ^ (((num : ℝ) / (den : ℝ)) /
            (1 + (num : ℝ) / (den : ℝ))) := by
  apply eventually_actual_sieve_gate
  have hdenR : (0 : ℝ) < (den : ℝ) := Nat.cast_pos.mpr hden
  have hhalfR : (den : ℝ) < 2 * (num : ℝ) := by exact_mod_cast hhalf
  apply (lt_div_iff₀ hdenR).mpr
  linarith

/-- Every actual source member is coprime to every divisor of the actual
sieve product, eventually, with no geometric hypothesis left to discharge. -/
theorem eventually_actual_halfProductSource_coprime (num den : ℕ)
    (hden : 0 < den) (hhalf : den < 2 * num) :
    ∀ᶠ N : ℕ in atTop, ∀ m d : ℕ,
      m ∈ halfProductSource num den N (logCutoff N) →
      d ∣ sieveProduct N (Nat.ceil ((N : ℝ) ^ (1 / 5 : ℝ))) →
      Nat.Coprime m d := by
  have hnum : 0 < num := by omega
  filter_upwards [eventually_actual_sieve_gate_rational num den hden hhalf]
    with N hgate
  intro m d hm hd
  exact halfProductSource_coprime_of_dvd_sieveProduct
    hnum hden hgate.1 hgate.2 hm hd

/-- The same coprimality statement for the retained original bad receivers.
Their original additive-prime restriction remains in the membership premise. -/
theorem eventually_actual_retainedBadReceivers_coprime (num den : ℕ)
    (hden : 0 < den) (hhalf : den < 2 * num) :
    ∀ᶠ N : ℕ in atTop, ∀ m d : ℕ,
      m ∈ retainedBadReceiversReal num den N (logCutoff N) →
      d ∣ sieveProduct N (Nat.ceil ((N : ℝ) ^ (1 / 5 : ℝ))) →
      Nat.Coprime m d := by
  filter_upwards [eventually_actual_halfProductSource_coprime num den hden hhalf]
    with N hcoprime
  intro m d hm hd
  exact hcoprime m d
    (retainedBadReceiversReal_subset_halfProductSource num den N (logCutoff N) hm) hd

/-- The actual allowed moduli are primitive, all actual source members
are coprime to them, and divisibility is exactly the residue-class mask. -/
theorem eventually_actual_sieve_modulus_data (num den : ℕ)
    (hden : 0 < den) (hhalf : den < 2 * num) :
    ∀ᶠ N : ℕ in atTop, ∀ d : ℕ,
      d ∣ sieveProduct N (Nat.ceil ((N : ℝ) ^ (1 / 5 : ℝ))) →
      Nat.Coprime d N ∧
        (∀ m : ℕ, m ∈ halfProductSource num den N (logCutoff N) → Nat.Coprime m d) ∧
        ((halfProductSource num den N (logCutoff N)).filter
          (fun m : ℕ => d ∣ N - m)).card =
        ((halfProductSource num den N (logCutoff N)).filter
          (fun m : ℕ => Nat.ModEq d m N)).card := by
  classical
  have hnum : 0 < num := by omega
  filter_upwards [eventually_actual_sieve_gate_rational num den hden hhalf]
    with N hgate
  intro d hd
  exact halfProductSource_sieve_modulus_data hnum hden hgate.1 hgate.2 hd

end ImbalancedChen
