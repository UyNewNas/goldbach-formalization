import ImbalancedChen.Part3LevelEisensteinScatteringFactors
import ImbalancedChen.Part3ActualRamanujanLevelZetaFactors
import ImbalancedChen.Part3ActualEisensteinRamanujanCSum
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

The actual level-N infinity zero-mode coefficient, not an assumed local
factor formula. The separately proved restricted Ramanujan/totient series
identity is used on its true convergence halfplane. Its literal local-tail
quotients are converted by exact positive-base cpow algebra to the finite
scattering factors. Hence the original restricted series, and then the
original actual parabolic Eisenstein Fourier zero coefficient for real
s>1, acquire precisely the full-level scattering scalar times that finite
prime-power correction.

The critical entry is the true central extension already constructed from
the full-level residue limit and the finite holomorphic factor. It has
central value -1 and norm at most one. For multicusp levels this theorem
identifies ONE infinity-to-infinity entry; no scalar or matrix unitarity
is asserted, and no physical Eisenstein continuation is assumed.
-/

namespace ImbalancedChen.Part3.ActualLevelEisensteinConstant20261025a

noncomputable section

open Set Complex Finset
open ImbalancedChen.Part3.LevelEisensteinScatteringFactors20261025a
open ImbalancedChen.Part3.ActualLevelDirichletFactors
open ImbalancedChen.Part3.ActualRamanujanSinglePrimeLevelSplit
open ImbalancedChen.Part3.ActualRamanujanLevelZetaFactors
open ImbalancedChen.Part3.ActualEisensteinFourierInterchange20261025a
open ImbalancedChen.Part3.ActualEisensteinRamanujanCSum20261025a
open ImbalancedChen.Part3.OriginalSmoothPoissonTail
open ImbalancedChen.Part3.OriginalSmoothPoissonTail.Physical.ZeroMode
open ImbalancedChen.Part3.ActualComplexEisensteinCanonicalFourier

/-- The actual local-tail quotient is exactly the explicit scattering
factor at positive valuation, including all cpow branches and normalizations. -/
theorem zeroLocalCorrection_succ_eq_scatteringFactor {p : ℕ} (hp : p.Prime)
    (k : ℕ) (s : ℂ) (hs : 1 < s.re) :
    localTail p 0 (k + 1) ((p : ℂ) ^ (-(2 * s))) /
      localTail p 0 0 ((p : ℂ) ^ (-(2 * s))) = localScatteringFactor p (k + 1) s := by
  have hw : 1 < (2 * s).re := by
    simp only [Complex.mul_re, Complex.ofNat_re, Complex.ofNat_im, zero_mul, sub_zero]
    linarith
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  rw [zero_localCorrection_succ hp k (2 * s) hw,
    show -(2 * s) = (-2 : ℂ) * s by ring]
  have hpower : (p : ℂ) ^ (-2 * s) * ((p : ℂ) * (p : ℂ) ^ (-2 * s)) ^ k =
      (p : ℂ) ^ (((k + 1 : ℕ) : ℂ) - 1 - 2 * ((k + 1 : ℕ) : ℂ) * s) := by
    rw [mul_pow, ← Complex.cpow_natCast, ← Complex.cpow_nat_mul]
    simp only [Complex.cpow_def_of_ne_zero hpC, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold localScatteringFactor
  congr 1
  rw [mul_assoc, hpower]

/-- Every genuine level-prime valuation is positive; thus no exponent-zero
formula is silently used for a prime dividing the actual positive level. -/
theorem levelPrime_valuation_pos (N : ℕ) (hN : N ≠ 0) (p : ℕ)
    (hpN : p ∈ N.primeFactors) : 0 < padicValNat p N := by
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpN
  rw [← Nat.factorization_def N hp]
  exact hp.factorization_pos_of_dvd hN (Nat.dvd_of_mem_primeFactors hpN)

/-- The actual finite local-tail quotient product equals the explicit
finite scattering product, proved factor by factor from the true local sums. -/
theorem localCorrectionProduct_zero_eq_levelFiniteFactor
    (N : ℕ) (hN : N ≠ 0) (s : ℂ) (hs : 1 < s.re) :
    localCorrectionProduct N 0 (2 * s) = levelFiniteFactor N s := by
  unfold localCorrectionProduct levelFiniteFactor
  apply Finset.prod_congr rfl
  intro p hpN
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpN
  obtain ⟨k, hk⟩ : ∃ k : ℕ, padicValNat p N = k + 1 :=
    Nat.exists_eq_succ_of_ne_zero (levelPrime_valuation_pos N hN p hpN).ne'
  rw [hk]
  exact zeroLocalCorrection_succ_eq_scatteringFactor hp k s hs

/-- True restricted totient/Ramanujan series with the precise level factor;
all convergence, extraction and local divisions were proved in the supplier. -/
theorem restrictedSeries_zero_eq_levelFactor
    (N : ℕ) (hN : N ≠ 0) (s : ℂ) (hs : 1 < s.re) :
    restrictedSeries N 0 (2 * s) =
      (riemannZeta (2 * s - 1) / riemannZeta (2 * s)) * levelFiniteFactor N s := by
  have hw : 2 < (2 * s).re := by
    simp only [Complex.mul_re, Complex.ofNat_re, Complex.ofNat_im, zero_mul, sub_zero]
    linarith
  rw [restrictedSeries_zero_zeta_formula N hN (2 * s) hw,
    localCorrectionProduct_zero_eq_levelFiniteFactor N hN s hs]

/-- The initial infinity scattering coefficient defined from the ACTUAL
restricted zero-frequency arithmetic series, rather than a chosen product. -/
def initialInfinityScattering (N : ℕ) (s : ℂ) : ℂ :=
  ((Real.sqrt Real.pi : ℂ) * Complex.Gamma (s - 1 / 2) / Complex.Gamma s) *
    restrictedSeries N 0 (2 * s)

/-- The desired level formula is DERIVED from the original restricted
series: phi_N,infty,infty(s)=phi_1(s)*the actual finite prime-power product. -/
theorem initialInfinityScattering_eq_levelScattering
    (N : ℕ) (hN : N ≠ 0) (s : ℂ) (hs : 1 < s.re) :
    initialInfinityScattering N s = levelScattering N s := by
  rw [initialInfinityScattering, restrictedSeries_zero_eq_levelFactor N hN s hs]
  unfold levelScattering complexScattering
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The original real-power positive-c series is exactly the literal
restricted complex-power series on the same level, with only a zero term
inserted at c=0. No Dirichlet identity or summability is assumed for this bridge. -/
theorem restrictedSeries_ofReal_eq_levelRamanujan (N : ℕ) (s : ℝ) (n : ℤ) :
    restrictedSeries N n (2 * (s : ℂ)) = levelRamanujanSeries N s n := by
  let f : ℕ → ℂ := fun c => if N ∣ c then
    (((c : ℝ) ^ (-(2 * s)) : ℝ) : ℂ) * ramanujan c n else 0
  have hf0 : f 0 = 0 := by simp [f, ramanujan, kloosterman]
  have hpower (c : ℕ) : (c : ℂ) ^ (-(2 * (s : ℂ))) =
      (((c : ℝ) ^ (-(2 * s)) : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat,
      Complex.ofReal_natCast] using
      (Complex.ofReal_cpow (Nat.cast_nonneg c) (-(2 * s))).symm
  calc
    _ = ∑' c : ℕ, f c := by
      unfold restrictedSeries
      apply tsum_congr
      intro c
      by_cases hc : N ∣ c
      · simp only [if_pos hc, actualTerm, f, hpower]
        exact mul_comm _ _
      · simp only [if_neg hc, f]
    _ = ∑' c : ℕ+, f (c : ℕ) := (tsum_pnat_eq_tsum_of_eq_zero hf0).symm
    _ = _ := rfl

theorem restrictedSeries_zero_ofReal_eq_totient (N : ℕ) (s : ℝ) :
    restrictedSeries N 0 (2 * (s : ℂ)) =
      ((∑' c : ℕ+, levelTotientTerm N s c : ℝ) : ℂ) := by
  rw [restrictedSeries_ofReal_eq_levelRamanujan]
  simp only [levelRamanujanSeries, levelRamanujanTerm_zero, Complex.ofReal_tsum]

/-- ACTUAL parabolic Eisenstein scalar Fourier zero coefficient, initially
for real s>1, with the scattering scalar defined by its original arithmetic. -/
theorem actualEisensteinFourier_zero_eq_initialInfinityScattering
    (N : ℕ) (s : ℝ) (hs : 1 < s) (y : ℝ) (hy : 0 < y) :
    actualEisensteinFourier N s y hy 0 =
      (y ^ s : ℂ) + initialInfinityScattering N (s : ℂ) * (y ^ (1 - s) : ℂ) := by
  have hhalf : (s : ℂ) - 1 / 2 = ((s - 1 / 2 : ℝ) : ℂ) := by push_cast
  rw [actualEisensteinFourier_zero N s hs y hy]
  simp only [Complex.ofReal_add, Complex.ofReal_mul]
  rw [← restrictedSeries_zero_ofReal_eq_totient N s]
  unfold initialInfinityScattering
  rw [hhalf, Complex.Gamma_ofReal, Complex.Gamma_ofReal]
  simp only [Complex.ofReal_div, Complex.ofReal_mul]
  ring

/-- The actual level-N Fourier zero mode now has the derived finite Euler
correction multiplying the genuine full-level Gamma/zeta scattering scalar. -/
theorem actualEisensteinFourier_zero_eq_levelScattering
    (N : ℕ) (hN : N ≠ 0) (s : ℝ) (hs : 1 < s) (y : ℝ) (hy : 0 < y) :
    actualEisensteinFourier N s y hy 0 =
      (y ^ s : ℂ) + levelScattering N (s : ℂ) * (y ^ (1 - s) : ℂ) := by
  rw [actualEisensteinFourier_zero_eq_initialInfinityScattering N s hs y hy,
    initialInfinityScattering_eq_levelScattering N hN (s : ℂ) (by simpa using hs)]

end
end ImbalancedChen.Part3.ActualLevelEisensteinConstant20261025a
