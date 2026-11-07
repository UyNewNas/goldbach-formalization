import ImbalancedChen.Part3NormalizedEisensteinPrimeAmplitude
import Mathlib.Analysis.Analytic.Uniqueness

/-! The finite normalized divisor amplitudes are entire. Their genuine
prime-frequency identity, already obtained from actual convergent series
on Re(s)>1/2, therefore extends to every complex parameter. No completion
factor is divided and no central derivative or held Fourier API is used.
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT. -/

noncomputable section
open Set Filter Complex
open scoped Topology
open ImbalancedChen.Part3ActualRamanujanDirichletSeries
open ImbalancedChen.Part3.NormalizedEisensteinPrimeAmplitude20261026b

namespace ImbalancedChen.Part3.EntireEisensteinPrimeAmplitude20261026b

/-- The literal finite divisor factor is entire in the spectral parameter,
including the empty n=0 divisor carrier. -/
theorem divisorFactor_twice_differentiable (n : ℕ) :
    Differentiable ℂ (fun s : ℂ => divisorFactor n (2 * s)) := by
  unfold divisorFactor
  apply Differentiable.fun_sum
  intro d hd
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_of_mem_divisors hd).ne'
  exact (differentiable_const.sub (differentiable_id.const_mul (2 : ℂ))).const_cpow (.inl hd0)

/-- Genuine entire normalized amplitudes. At n=0 the actual empty divisor
sum vanishes, so no analyticity of a totalized power of zero is assumed. -/
theorem normalizedDivisorAmplitude_differentiable (n : ℕ) :
    Differentiable ℂ (normalizedDivisorAmplitude n) := by
  by_cases hn : n = 0
  · subst n
    simpa [normalizedDivisorAmplitude, divisorFactor] using
      (differentiable_const (0 : ℂ) : Differentiable ℂ (fun _ : ℂ => (0 : ℂ)))
  · have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    exact ((differentiable_id.sub_const _).const_cpow (.inl hn0)).mul
      (divisorFactor_twice_differentiable n)

private theorem primeEigenvalue_differentiable {p : ℕ} (hp : p.Prime) :
    Differentiable ℂ (fun s : ℂ =>
      (p : ℂ) ^ (s - 1 / 2) + (p : ℂ) ^ (1 / 2 - s)) := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  exact ((differentiable_id.sub_const _).const_cpow (.inl hp0)).add
    ((differentiable_const.sub differentiable_id).const_cpow (.inl hp0))

/-- Entire arithmetic prime-frequency identity, including the entire
critical line and its center. The proof uses analytic uniqueness of the
actual finite amplitude functions, not an assumed Fourier eigenrelation. -/
theorem normalizedDivisorAmplitude_prime_hecke_entire {p : ℕ} (hp : p.Prime)
    (n : ℕ) (hn : 0 < n) (s : ℂ) :
    normalizedDivisorAmplitude (p * n) s +
      (if p ∣ n then normalizedDivisorAmplitude (n / p) s else 0) =
        ((p : ℂ) ^ (s - 1 / 2) + (p : ℂ) ^ (1 / 2 - s)) *
          normalizedDivisorAmplitude n s := by
  classical
  let F : ℂ → ℂ := fun w => normalizedDivisorAmplitude (p * n) w +
    (if p ∣ n then normalizedDivisorAmplitude (n / p) w else 0)
  let G : ℂ → ℂ := fun w =>
    ((p : ℂ) ^ (w - 1 / 2) + (p : ℂ) ^ (1 / 2 - w)) *
      normalizedDivisorAmplitude n w
  have hFd : Differentiable ℂ F := by
    dsimp only [F]
    by_cases hd : p ∣ n
    · simp only [if_pos hd]
      exact (normalizedDivisorAmplitude_differentiable (p * n)).add
        (normalizedDivisorAmplitude_differentiable (n / p))
    · simp only [if_neg hd, add_zero]
      exact normalizedDivisorAmplitude_differentiable (p * n)
  have hGd : Differentiable ℂ G :=
    (primeEigenvalue_differentiable hp).mul (normalizedDivisorAmplitude_differentiable n)
  have hFa : AnalyticOnNhd ℂ F univ := hFd.differentiableOn.analyticOnNhd isOpen_univ
  have hGa : AnalyticOnNhd ℂ G univ := hGd.differentiableOn.analyticOnNhd isOpen_univ
  have he : F =ᶠ[𝓝 (1 : ℂ)] G := by
    have hhalf : {w : ℂ | 1 / 2 < w.re} ∈ 𝓝 (1 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hhalf] with w hw
    exact normalizedDivisorAmplitude_prime_hecke hp n hn w hw
  exact congrFun (hFa.eq_of_eventuallyEq hGa he) s

/-- Actual central arithmetic value: both prime powers equal one. -/
theorem normalizedDivisorAmplitude_prime_hecke_center {p : ℕ} (hp : p.Prime)
    (n : ℕ) (hn : 0 < n) :
    normalizedDivisorAmplitude (p * n) (1 / 2) +
      (if p ∣ n then normalizedDivisorAmplitude (n / p) (1 / 2) else 0) =
        2 * normalizedDivisorAmplitude n (1 / 2) := by
  simpa using
    normalizedDivisorAmplitude_prime_hecke_entire hp n hn (1 / 2)

end ImbalancedChen.Part3.EntireEisensteinPrimeAmplitude20261026b
