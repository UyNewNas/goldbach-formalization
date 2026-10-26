import ImbalancedChen.Part3LevelOldformScatteringMoments
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

Exact two-channel prime Euler factor. Its two entries are identified with
the outgoing moments of the literal completed oldform list. The critical
Gram identities retain BOTH entries; a bound on a single entry is not used.
This leaf does not identify all physical cusp integrals or assert an
automorphic spectral resolution.
-/

noncomputable section
open Complex
open scoped BigOperators
open ImbalancedChen.Part3.FiniteLevelEisensteinOldforms20261025a
open ImbalancedChen.Part3.LevelOldformScattering20261026a
open ImbalancedChen.Part3.CriticalEisensteinScattering20261025a
open ImbalancedChen.Part3.LevelEisensteinScatteringFactors20261025a

namespace ImbalancedChen.Part3.PrimeScatteringLocal20261026b

def primeRatio (p : ℕ) (s : ℂ) : ℂ := (p : ℂ) ^ (-s)

def primeDiagonal (p : ℕ) (s : ℂ) : ℂ :=
  ((p : ℂ) - 1) * (primeRatio p s) ^ 2 / (1 - (primeRatio p s) ^ 2)

def primeOffDiagonal (p : ℕ) (s : ℂ) : ℂ :=
  primeRatio p s * (1 - (p : ℂ) * (primeRatio p s) ^ 2) /
    (1 - (primeRatio p s) ^ 2)

theorem primeRatio_sq {p : ℕ} (hp : p.Prime) (s : ℂ) :
    (primeRatio p s) ^ 2 = (p : ℂ) ^ (-2 * s) := by
  rw [primeRatio, pow_two, ← Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hp.ne_zero)]
  congr 1
  ring

theorem prime_power_one_sub {p : ℕ} (hp : p.Prime) (s : ℂ) :
    (p : ℂ) ^ (1 - 2 * s) = (p : ℂ) * (primeRatio p s) ^ 2 := by
  rw [primeRatio_sq hp, show (1 : ℂ) - 2 * s = 1 + (-2 * s) by ring,
    Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hp.ne_zero), Complex.cpow_one]

theorem prime_local_denominator_ne_zero {p : ℕ} (hp : p.Prime)
    {s : ℂ} (hs : 0 < s.re) : 1 - (primeRatio p s) ^ 2 ≠ 0 := by
  rw [primeRatio_sq hp]
  exact localScatteringFactor_denominator_ne_zero hp hs

theorem canonicalPrimeList_prime {p : ℕ} (hp : p.Prime) :
    canonicalPrimeList p = [⟨p, hp⟩] := by
  simp [canonicalPrimeList, Nat.primeFactorsList_prime hp]

/-- The diagonal entry comes from the actual outgoing infinity moment. -/
theorem primeDiagonal_eq_infinity_moment {p : ℕ} (hp : p.Prime) (s : ℂ) :
    primeDiagonal p s = normalizedHeightMoment p s (1 - s) := by
  rw [infinity_outgoing_moment p hp.pos, canonicalPrimeList_prime hp]
  simp only [List.toFinset_cons, List.toFinset_nil, Finset.insert_empty_eq,
    Finset.prod_singleton]
  rw [prime_power_one_sub hp, ← primeRatio_sq hp]
  have hc : (p : ℂ) * (1 - (p : ℂ) ^ (-1 : ℂ)) = (p : ℂ) - 1 := by
    rw [Complex.cpow_neg_one, mul_sub, mul_one,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hp.ne_zero)]
  unfold primeDiagonal
  calc
    _ = ((p : ℂ) * (1 - (p : ℂ) ^ (-1 : ℂ))) * (primeRatio p s) ^ 2 /
        (1 - (primeRatio p s) ^ 2) := by rw [hc]
    _ = _ := by ring

/-- The second entry comes from the literal N/n reflected height moment. -/
theorem primeOffDiagonal_eq_reflected_moment {p : ℕ} (hp : p.Prime) (s : ℂ) :
    primeOffDiagonal p s = reflectedHeightMoment p s (1 - s) := by
  rw [reflected_outgoing_moment p hp.pos, canonicalPrimeList_prime hp]
  simp only [List.toFinset_cons, List.toFinset_nil, Finset.insert_empty_eq,
    Finset.prod_singleton]
  rw [prime_power_one_sub hp, ← primeRatio_sq hp]
  rfl

/-- The only critical input to the finite algebra is proved from the
actual complex power, rather than assumed as a unitary-matrix premise. -/
theorem primeRatio_critical_balance {p : ℕ} (hp : p.Prime) (t : ℝ) :
    (p : ℂ) * primeRatio p (criticalParameter t) *
      conj (primeRatio p (criticalParameter t)) = 1 := by
  have hn : ‖primeRatio p (criticalParameter t)‖ ^ 2 = 1 / (p : ℝ) := by
    calc
      _ = ‖(primeRatio p (criticalParameter t)) ^ 2‖ := (norm_pow _ 2).symm
      _ = _ := by rw [primeRatio_sq hp, critical_primeRatio_norm hp t]
  rw [mul_assoc, Complex.mul_conj', hn]
  push_cast
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hp.ne_zero)

private theorem two_numerator_gram (p : ℕ) (q : ℂ)
    (hq : (p : ℂ) * q * conj q = 1) :
    (((p : ℂ) - 1) * q ^ 2) * conj (((p : ℂ) - 1) * q ^ 2) +
      (q * (1 - (p : ℂ) * q ^ 2)) * conj (q * (1 - (p : ℂ) * q ^ 2)) =
        (1 - q ^ 2) * conj (1 - q ^ 2) := by
  simp only [map_mul, map_sub, map_pow, map_natCast, map_one]
  apply sub_eq_zero.mp
  calc
    _ = ((p : ℂ) * q * conj q - 1) *
        ((p : ℂ) * q ^ 2 * (conj q) ^ 2 + ((p : ℂ) - 1) * q * conj q +
          1 - q ^ 2 - (conj q) ^ 2) := by ring
    _ = 0 := by rw [hq]; ring

private theorem two_numerator_cross (p : ℕ) (q : ℂ)
    (hq : (p : ℂ) * q * conj q = 1) :
    (((p : ℂ) - 1) * q ^ 2) * conj (q * (1 - (p : ℂ) * q ^ 2)) +
      (q * (1 - (p : ℂ) * q ^ 2)) * conj (((p : ℂ) - 1) * q ^ 2) = 0 := by
  simp only [map_mul, map_sub, map_pow, map_natCast, map_one]
  calc
    _ = ((p : ℂ) * q * conj q - 1) *
      (-((p : ℂ) - 1) * q * conj q * (q + conj q)) := by ring
    _ = 0 := by rw [hq]; ring

/-- Exact sum of the two channel masses. Both are essential. -/
theorem prime_critical_gram {p : ℕ} (hp : p.Prime) (t : ℝ) :
    primeDiagonal p (criticalParameter t) * conj (primeDiagonal p (criticalParameter t)) +
      primeOffDiagonal p (criticalParameter t) *
        conj (primeOffDiagonal p (criticalParameter t)) = 1 := by
  let q := primeRatio p (criticalParameter t)
  have hd : 1 - q ^ 2 ≠ 0 := prime_local_denominator_ne_zero hp
    (by rw [criticalParameter_re]; norm_num)
  have hdc : conj (1 - q ^ 2) ≠ 0 := by
    intro h
    apply hd
    simpa using congrArg conj h
  have hnum := two_numerator_gram p q (primeRatio_critical_balance hp t)
  change (((p : ℂ) - 1) * q ^ 2 / (1 - q ^ 2)) *
      conj (((p : ℂ) - 1) * q ^ 2 / (1 - q ^ 2)) +
    (q * (1 - (p : ℂ) * q ^ 2) / (1 - q ^ 2)) *
      conj (q * (1 - (p : ℂ) * q ^ 2) / (1 - q ^ 2)) = 1
  simp only [map_div₀]
  calc
    _ = ((((p : ℂ) - 1) * q ^ 2) * conj (((p : ℂ) - 1) * q ^ 2) +
      (q * (1 - (p : ℂ) * q ^ 2)) * conj (q * (1 - (p : ℂ) * q ^ 2))) /
        ((1 - q ^ 2) * conj (1 - q ^ 2)) := by ring
    _ = 1 := by rw [hnum, div_self (mul_ne_zero hd hdc)]

/-- Exact off-diagonal orthogonality of the two ramified channels. -/
theorem prime_critical_cross {p : ℕ} (hp : p.Prime) (t : ℝ) :
    primeDiagonal p (criticalParameter t) * conj (primeOffDiagonal p (criticalParameter t)) +
      primeOffDiagonal p (criticalParameter t) *
        conj (primeDiagonal p (criticalParameter t)) = 0 := by
  let q := primeRatio p (criticalParameter t)
  change (((p : ℂ) - 1) * q ^ 2 / (1 - q ^ 2)) *
      conj (q * (1 - (p : ℂ) * q ^ 2) / (1 - q ^ 2)) +
    (q * (1 - (p : ℂ) * q ^ 2) / (1 - q ^ 2)) *
      conj (((p : ℂ) - 1) * q ^ 2 / (1 - q ^ 2)) = 0
  simp only [map_div₀]
  calc
    _ = ((((p : ℂ) - 1) * q ^ 2) * conj (q * (1 - (p : ℂ) * q ^ 2)) +
      (q * (1 - (p : ℂ) * q ^ 2)) * conj (((p : ℂ) - 1) * q ^ 2)) /
        ((1 - q ^ 2) * conj (1 - q ^ 2)) := by ring
    _ = 0 := by rw [two_numerator_cross p q (primeRatio_critical_balance hp t), zero_div]

/-- Matrix of the proved finite prime factors, before the full-level
Gamma/zeta scalar and physical Fourier integral identification. -/
def primeLocalMatrix (p : ℕ) (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![primeDiagonal p s, primeOffDiagonal p s;
     primeOffDiagonal p s, primeDiagonal p s]

theorem primeLocalMatrix_critical_mul_conjTranspose {p : ℕ} (hp : p.Prime) (t : ℝ) :
    primeLocalMatrix p (criticalParameter t) *
      (primeLocalMatrix p (criticalParameter t)).conjTranspose = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [primeLocalMatrix, Matrix.mul_fin_two, Matrix.conjTranspose_apply] using
      prime_critical_gram hp t
  · simpa [primeLocalMatrix, Matrix.mul_fin_two, Matrix.conjTranspose_apply] using
      prime_critical_cross hp t
  · simpa [primeLocalMatrix, Matrix.mul_fin_two, Matrix.conjTranspose_apply, add_comm] using
      prime_critical_cross hp t
  · simpa [primeLocalMatrix, Matrix.mul_fin_two, Matrix.conjTranspose_apply, add_comm] using
      prime_critical_gram hp t

end ImbalancedChen.Part3.PrimeScatteringLocal20261026b
