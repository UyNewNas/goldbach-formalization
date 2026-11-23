import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-! The equality endpoint at a rational power of the actual centre. -/
namespace ImbalancedChen.P5OriginalCoprimeRationalEndpoint

theorem prime_ne_coprime_power {N q : ℕ} (hp : q.Prime) (hc : q.Coprime N)
    (num den : ℕ) (hd : den ≠ 0) : (q : ℝ) ≠ (N : ℝ)^((num:ℝ)/den) := by
  intro he
  have hd' : (den:ℝ) ≠ 0 := by exact_mod_cast hd
  have hpow : (q:ℝ)^den = (N:ℝ)^num := by
    calc
      _ = ((N:ℝ)^((num:ℝ)/den))^den := congrArg (fun x : ℝ => x^den) he
      _ = (N:ℝ)^(((num:ℝ)/den)*(den:ℝ)) :=
        (Real.rpow_mul_natCast (Nat.cast_nonneg N) _ den).symm
      _ = (N:ℝ)^(num:ℝ) := by rw [div_mul_cancel₀ _ hd']
      _ = _ := Real.rpow_natCast _ _
  have hnat : q^den = N^num := by exact_mod_cast hpow
  have hdiv : q ∣ N^num := by rw [←hnat]; exact dvd_pow_self q hd
  exact (hp.coprime_iff_not_dvd.mp hc) (hp.dvd_of_dvd_pow hdiv)

theorem original_cutoff_strict {N q : ℕ} (hp : q.Prime) (hc : q.Coprime N)
    (h : (q:ℝ) ≤ (N:ℝ)^(417/5000:ℝ)) : (q:ℝ) < (N:ℝ)^(417/5000:ℝ) := by
  exact lt_of_le_of_ne h (prime_ne_coprime_power hp hc 417 5000 (by decide))

end ImbalancedChen.P5OriginalCoprimeRationalEndpoint
