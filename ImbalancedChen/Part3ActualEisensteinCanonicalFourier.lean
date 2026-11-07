import ImbalancedChen.Part3ActualEisensteinRamanujanCSum
import ImbalancedChen.Part3ActualTotientDirichletSeries
import ImbalancedChen.Part3ActualRamanujanDirichletSeries
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

Canonical scalar Fourier coefficients of the ACTUAL level-one parabolic
Eisenstein series for real s>1. The earlier actual half-primitive-row
normalization, signed-c pairing, integral interchange and full c-series
formula are used without modification. The separately proved actual
Euler-totient and nonzero-frequency Ramanujan Dirichlet identities evaluate
the remaining arithmetic factors. Thus the constant term has the precise
sqrt(pi) Gamma(s-1/2) zeta(2s-1)/(Gamma(s) zeta(2s)) coefficient, and every
nonzero Fourier coefficient has the precise factor 2, finite divisor sum,
zeta denominator and actual real-order K function.

The conclusion is about the scalar Fourier integral of the genuine
GammaInfinity\SL2(Z) Poincare sum and also of the existing primitive
Eisenstein object. No raw-series identity, target normalization, or target
Fourier coefficient is a hypothesis. No complex-parameter continuation,
Fourier reconstruction or spectral identity is claimed here.
-/

namespace ImbalancedChen.Part3.ActualEisensteinCanonicalFourier20261025a

noncomputable section

open Set MeasureTheory
open scoped UpperHalfPlane
open ImbalancedChen.Part3.Gamma0ParabolicEisensteinHalfPairs20261025a
open ImbalancedChen.Part3.PrimitiveRealEisensteinAutomorphy
open ImbalancedChen.Part3.PowerSeedFourierLaplaceFubini
open ImbalancedChen.Part3.ActualEisensteinFourierInterchange20261025a
open ImbalancedChen.Part3.ActualEisensteinRamanujanCSum20261025a
open ImbalancedChen.Part3.ActualTotientDirichletSeries
open ImbalancedChen.Part3ActualRamanujanDirichletSeries
open ImbalancedChen.Part3.OriginalSmoothPoissonTail
open ImbalancedChen.Part3.OriginalSmoothPoissonTail.Physical.ZeroMode

/-- The canonical scattering scalar, with all factors and the zeta
arguments literal. It is evaluated below as the actual constant coefficient. -/
def canonicalScattering (s : ℝ) : ℂ :=
  (Real.sqrt Real.pi : ℂ) * (Real.Gamma (s - 1 / 2) : ℂ) *
    riemannZeta ((2 * s - 1 : ℝ) : ℂ) /
      ((Real.Gamma s : ℂ) * riemannZeta ((2 * s : ℝ) : ℂ))

/-- The literal finite generalized divisor sum at the signed frequency n. -/
def canonicalDivisorFactor (s : ℝ) (n : ℤ) : ℝ :=
  ∑ d ∈ n.natAbs.divisors, (d : ℝ) ^ (1 - 2 * s)

/-- The full canonical nonzero Fourier coefficient, including the actual
K height factor. The factor 2 is fixed by the original primitive normalization. -/
def canonicalNonzeroCoefficient (s y : ℝ) (n : ℤ) : ℂ :=
  ((2 * Real.pi ^ s : ℝ) : ℂ) /
      ((Real.Gamma s : ℂ) * riemannZeta ((2 * s : ℝ) : ℂ)) *
    ((|(n : ℝ)| ^ (s - 1 / 2) * canonicalDivisorFactor s n * Real.sqrt y *
      RealOrderKExceptionalSourceOnly.realOrderK (s - 1 / 2)
        (2 * Real.pi * |(n : ℝ)| * y) : ℝ) : ℂ)

/-- All canonical scalar coefficients; this is an explicit value, not a
new Eisenstein series or a coefficient supplied as a premise. -/
def canonicalFourierCoefficient (s y : ℝ) (n : ℤ) : ℂ :=
  if n = 0 then (y ^ s : ℂ) + canonicalScattering s * (y ^ (1 - s) : ℂ)
  else canonicalNonzeroCoefficient s y n

/-- Exact positive-natural/natural-index bridge for the true full-level
phi term. The inserted n=0 summand is proved zero by its definition. -/
theorem fullLevelTotientSeries_eq_nat (s : ℝ) :
    (∑' c : ℕ+, levelTotientTerm 1 s c) = ∑' c : ℕ, totientTerm s c := by
  calc
    _ = ∑' c : ℕ+, totientTerm s (c : ℕ) := by
      apply tsum_congr
      intro c
      simp only [levelTotientTerm, one_dvd, if_true, totientTerm,
        Real.rpow_neg, div_eq_mul_inv]
      ring
    _ = _ := tsum_pnat_eq_tsum_of_eq_zero (totientTerm_zero s)

/-- The original full-level arithmetic factor is the actual zeta quotient,
not an assumed evaluation of the Fourier coefficient. -/
theorem fullLevelTotientSeries_eq_zeta (s : ℝ) (hs : 1 < s) :
    ((∑' c : ℕ+, levelTotientTerm 1 s c : ℝ) : ℂ) =
      riemannZeta ((2 * s - 1 : ℝ) : ℂ) / riemannZeta ((2 * s : ℝ) : ℂ) := by
  rw [fullLevelTotientSeries_eq_nat]
  exact actual_totient_series_eq_zeta_quotient s hs

/-- Exact positive-natural/natural bridge for the genuine full-level
Ramanujan series. This changes no arithmetic summand and inserts only zero. -/
theorem fullLevelRamanujanSeries_eq_nat (s : ℝ) (n : ℤ) :
    levelRamanujanSeries 1 s n =
      ∑' c : ℕ, ramanujan c n * (((c : ℝ) ^ (-(2 * s)) : ℝ) : ℂ) := by
  unfold levelRamanujanSeries
  calc
    _ = ∑' c : ℕ+, ramanujan (c : ℕ) n *
        (((c : ℝ) ^ (-(2 * s)) : ℝ) : ℂ) := by
      apply tsum_congr
      intro c
      simp only [levelRamanujanTerm, one_dvd, if_true]
      exact mul_comm _ _
    _ = _ := tsum_pnat_eq_tsum_of_eq_zero (by simp [ramanujan, kloosterman])

/-- Evaluation of the actual full-level Ramanujan arithmetic factor for
nonzero n, using the separately proved convergent Moebius/divisor theorem. -/
theorem fullLevelRamanujanSeries_eq_divisor_zeta
    (s : ℝ) (hs : 1 < s) (n : ℤ) (hn : n ≠ 0) :
    levelRamanujanSeries 1 s n =
      (canonicalDivisorFactor s n : ℂ) / riemannZeta ((2 * s : ℝ) : ℂ) := by
  rw [fullLevelRamanujanSeries_eq_nat]
  exact real_ramanujan_dirichlet_formula n hn (by linarith : 1 < 2 * s)

/-- The exact canonical constant coefficient of the ACTUAL parabolic
Eisenstein series, with the previous 1/2 primitive normalization retained. -/
theorem actualEisensteinFourier_zero_canonical
    (s : ℝ) (hs : 1 < s) (y : ℝ) (hy : 0 < y) :
    actualEisensteinFourier 1 s y hy 0 =
      (y ^ s : ℂ) + canonicalScattering s * (y ^ (1 - s) : ℂ) := by
  rw [actualEisensteinFourier_zero 1 s hs y hy]
  simp only [Complex.ofReal_add, Complex.ofReal_mul]
  rw [fullLevelTotientSeries_eq_zeta s hs]
  unfold canonicalScattering
  simp only [Complex.ofReal_div, Complex.ofReal_mul, div_eq_mul_inv, mul_inv_rev]
  ring

/-- The exact canonical divisor/K coefficient of the ACTUAL parabolic
Eisenstein series. Both signs of n use |n| and divisors of natAbs n. -/
theorem actualEisensteinFourier_nonzero_canonical
    (s : ℝ) (hs : 1 < s) (y : ℝ) (hy : 0 < y) (n : ℤ) (hn : n ≠ 0) :
    actualEisensteinFourier 1 s y hy n = canonicalNonzeroCoefficient s y n := by
  rw [actualEisensteinFourier_nonzero 1 s hs y hy n hn,
    fullLevelRamanujanSeries_eq_divisor_zeta s hs n hn]
  unfold canonicalNonzeroCoefficient
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat,
    div_eq_mul_inv, mul_inv_rev]
  ring

/-- Every scalar coefficient of the original actual Poincare sum equals
its fully evaluated canonical value for real s>1. -/
theorem actualEisensteinFourier_eq_canonical
    (s : ℝ) (hs : 1 < s) (y : ℝ) (hy : 0 < y) (n : ℤ) :
    actualEisensteinFourier 1 s y hy n = canonicalFourierCoefficient s y n := by
  by_cases hn : n = 0
  · subst n
    simpa only [canonicalFourierCoefficient, if_true] using
      actualEisensteinFourier_zero_canonical s hs y hy
  · simpa only [canonicalFourierCoefficient, if_neg hn] using
      actualEisensteinFourier_nonzero_canonical s hs y hy n hn

/-- The conclusion is a literal scalar integral of the ACTUAL
GammaInfinity\SL2(Z) sum, not only a theorem about a raw arithmetic series. -/
theorem actualParabolicEisenstein_scalar_fourier
    (s : ℝ) (hs : 1 < s) (y : ℝ) (hy : 0 < y) (n : ℤ) :
    (∫ x in (0 : ℝ)..1, fourierPhase n x *
      (actualParabolicEisenstein 1 s (horizontalPoint y hy x) : ℂ)) =
        canonicalFourierCoefficient s y n :=
  actualEisensteinFourier_eq_canonical s hs y hy n

/-- Caller bridge to the EXISTING half-primitive-pair Eisenstein family.
Its normalization was previously derived from the actual two-point sign
fibers; hence this formula adds no independent factor-of-two convention. -/
theorem primitiveEisenstein_scalar_fourier
    (s : ℝ) (hs : 1 < s) (y : ℝ) (hy : 0 < y) (n : ℤ) :
    (∫ x in (0 : ℝ)..1, fourierPhase n x *
      (primitiveEisenstein s (horizontalPoint y hy x) : ℂ)) =
        canonicalFourierCoefficient s y n := by
  calc
    _ = actualEisensteinFourier 1 s y hy n := by
      unfold actualEisensteinFourier
      apply intervalIntegral.integral_congr
      intro x _hx
      rw [actualParabolicEisenstein_one_eq_primitive s hs]
    _ = _ := actualEisensteinFourier_eq_canonical s hs y hy n

end
end ImbalancedChen.Part3.ActualEisensteinCanonicalFourier20261025a
