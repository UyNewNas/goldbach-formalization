import ImbalancedChen.Part3QuotientRealKFourierCoefficient
import ImbalancedChen.Part3CuspLocalImaginaryKShape
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The preexisting quotientRho is the amplitude of sqrt(y) K_nu(2*pi*|n|*y).
It is NOT Drappeau/ABL's coefficient of W_{0,nu}(4*pi*|n|*y).
The physical weight-zero Whittaker expression is
  2*sqrt(|n|*y)*K_nu(2*pi*|n|*y).
Thus rho_W=rho_K/(2*sqrt(|n|)) and R_W=sqrt(|n|)*rho_W=rho_K/2.
In particular the preexisting quotientR=sqrt(|n|)*rho_K is not R_W.

All public real-order amplitudes below are computed from the ORIGINAL
quotient Fourier integral. The imaginary-order existence/uniqueness
theorems consume the ORIGINAL cusp-local PDE, periodicity and raw L2 norm,
not an assumed coefficient shape. Signed n, tau=0 and the true cusp-tail
domain are retained. No height-one imaginary-K division is used.

No new Whittaker function is defined. The displayed physical expression
matches standard W by DLMF 13.18.9, as recorded separately in REPORT.
This local amplitude conversion supplies neither a spectral basis nor a
full Fourier expansion, all-cusp Eisenstein realization or Kuznetsov trace.

The imaginary-order source retains its explicit INSTALLATION HOLD:
Part3ImaginaryRadialTailDerivativeL2 requires d4d0a104..., whereas the
existing target is c51501c5.... Neither old file is modified or bypassed.
-/

namespace ImbalancedChen.Part3.ActualMaassWhittakerNormalization20261102

noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane
open QuotientRealKFourierCoefficient20261026b
open ActualPoincareSpectralCoefficient20261026a ActualMaassFourierODE20261026a
open ActualFourierBesselConjugation20261026a ComplexOrderKBridgeSourceOnly
open Gamma0QuotientCellPushforward20261025a
open CuspLocalFourierCalculus20261026b CuspLocalImaginaryKShape20261026b
attribute [local instance] Measure.Subtype.measureSpace

private theorem sqrt_abs_index_ne_zero {n : ℤ} (hn : n ≠ 0) :
    (Real.sqrt |(n : ℝ)| : ℂ) ≠ 0 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (abs_pos.mpr hnR)).ne'

private theorem sqrt_index_height (n : ℤ) (y : ℝ) :
    (Real.sqrt (|(n : ℝ)| * y) : ℂ) =
      (Real.sqrt |(n : ℝ)| : ℂ) * (Real.sqrt y : ℂ) := by
  rw [Real.sqrt_mul (abs_nonneg _), Complex.ofReal_mul]

private theorem actualK_amplitude_rescale {n : ℤ} (hn : n ≠ 0)
    (rho : ℂ) (nu : ℂ) (y : ℝ) :
    rho * (Real.sqrt y : ℂ) * complexOrderK nu (2*Real.pi*|(n : ℝ)|*y) =
      (rho / (2 * (Real.sqrt |(n : ℝ)| : ℂ))) *
        (2 * (Real.sqrt (|(n : ℝ)| * y) : ℂ)) *
          complexOrderK nu (2*Real.pi*|(n : ℝ)|*y) := by
  rw [sqrt_index_height]
  field_simp [sqrt_abs_index_ne_zero hn] <;> ring

/-- Computed from the actual original quotient Fourier integral. -/
def realQuotientWhittakerRho (N : ℕ) (U : Gamma0OrbitSpace N → ℂ)
    (nu : ℝ) (n : ℤ) : ℂ :=
  quotientRho N U nu n / (2 * (Real.sqrt |(n : ℝ)| : ℂ))

/-- The normalized coefficient in Drappeau/ABL's weight-zero convention. -/
def realQuotientWhittakerR (N : ℕ) (U : Gamma0OrbitSpace N → ℂ)
    (nu : ℝ) (n : ℤ) : ℂ :=
  (Real.sqrt |(n : ℝ)| : ℂ) * realQuotientWhittakerRho N U nu n

theorem realQuotientWhittakerR_eq_half_native (N : ℕ)
    (U : Gamma0OrbitSpace N → ℂ) (nu : ℝ) {n : ℤ} (hn : n ≠ 0) :
    realQuotientWhittakerR N U nu n = quotientRho N U nu n / 2 := by
  unfold realQuotientWhittakerR realQuotientWhittakerRho
  field_simp [sqrt_abs_index_ne_zero hn] <;> ring

/-- The extra sqrt(|n|) in the old quotientR must be divided out as well. -/
theorem realQuotientWhittakerR_eq_old_quotientR (N : ℕ)
    (U : Gamma0OrbitSpace N → ℂ) (nu : ℝ) {n : ℤ} (hn : n ≠ 0) :
    realQuotientWhittakerR N U nu n =
      quotientR N U nu n / (2 * (Real.sqrt |(n : ℝ)| : ℂ)) := by
  rw [realQuotientWhittakerR_eq_half_native N U nu hn]
  unfold quotientR
  field_simp [sqrt_abs_index_ne_zero hn] <;> ring

variable (N : ℕ) [NeZero N] (U : Gamma0OrbitSpace N → ℂ)
  (hU : Continuous (testLift N U)) (hU2 : MemLp U 2 (carrierPushforward N))
  (hC2 : ContDiffOn ℝ 2 (maassChart N U) upperDomain)
  (nu : ℝ) (hnu : 0 ≤ nu)
  (hPDE : ∀ p ∈ upperDomain,
    -(p.2 : ℂ)^2 * (partialX (partialX (maassChart N U)) p +
      partialY (partialY (maassChart N U)) p) = (1/4-(nu : ℂ)^2)*maassChart N U p)

/-- Actual quotient Fourier coefficient, with every Whittaker scale factor
visible in the existing physical K expression. No K-shape premise. -/
theorem actual_quotient_fourier_eq_whittaker_normalization_real
    {n : ℤ} (hn : n ≠ 0) {y : ℝ} (hy : 0 < y) :
    actualTestFourier N U n y = realQuotientWhittakerRho N U nu n *
      (2 * (Real.sqrt (|(n : ℝ)| * y) : ℂ)) *
        complexOrderK (nu : ℂ) (2*Real.pi*|(n : ℝ)|*y) := by
  rw [actual_quotient_fourier_eq_realK N U hU hU2 hC2 nu hnu hPDE hn hy]
  exact actualK_amplitude_rescale hn (quotientRho N U nu n) (nu : ℂ) y

/-- The physical coefficient of normalized R is 2*sqrt(y), not sqrt(y/|n|). -/
theorem actual_quotient_fourier_eq_normalizedR_real
    {n : ℤ} (hn : n ≠ 0) {y : ℝ} (hy : 0 < y) :
    actualTestFourier N U n y = (2 * realQuotientWhittakerR N U nu n) *
      (Real.sqrt y : ℂ) * complexOrderK (nu : ℂ) (2*Real.pi*|(n : ℝ)|*y) := by
  rw [actual_quotient_fourier_eq_realK N U hU hU2 hC2 nu hnu hPDE hn hy,
    realQuotientWhittakerR_eq_half_native N U nu hn]
  ring

/-- Actual coefficient products acquire the factor 1/4. This is a local
product identity, not a spectral sum or trace assertion. -/
theorem realQuotientWhittakerR_product (N : ℕ)
    (U V : Gamma0OrbitSpace N → ℂ) (nu mu : ℝ)
    {m n : ℤ} (hm : m ≠ 0) (hn : n ≠ 0) :
    starRingEnd ℂ (realQuotientWhittakerR N U nu m) *
      realQuotientWhittakerR N V mu n =
        (starRingEnd ℂ (quotientRho N U nu m) * quotientRho N V mu n) / 4 := by
  rw [realQuotientWhittakerR_eq_half_native N U nu hm,
    realQuotientWhittakerR_eq_half_native N V mu hn]
  simp only [map_div]
  norm_num <;> ring

/-- Unique Whittaker-normalized amplitude of the ORIGINAL signed cusp-local
Fourier integral. The existing imaginary-K classification supplies its
existence and uniqueness from physical hypotheses, including tau=0. -/
theorem actual_cusp_local_unique_whittaker_amplitude
    {u : ℝ × ℝ → ℂ} {tau Y : ℝ} {n : ℤ}
    (hu : ContDiffOn ℝ 2 u (cuspDomain Y))
    (hp : ∀ x y : ℝ, Y < y → u (x+1,y)=u(x,y))
    (hPDE : ∀ p ∈ cuspDomain Y,
      -(p.2 : ℂ)^2*(partialX (partialX u) p+partialY (partialY u) p) =
        ((1/4+tau^2 : ℝ) : ℂ)*u p)
    (hn : n ≠ 0) (hY : 0 < Y)
    (hstrip : Integrable (fun p : PeriodCell × ℝ => p.2⁻¹^2*‖u (p.1,p.2)‖^2)
      ((volume : Measure PeriodCell).prod (volume.restrict (Ioi Y)))) :
    ∃! rhoW : ℂ, ∀ y : ℝ, Y < y →
      coefficient u n y = rhoW * (2 * (Real.sqrt (|(n : ℝ)| * y) : ℂ)) *
        complexOrderK ((tau : ℂ)*Complex.I) (2*Real.pi*|(n : ℝ)|*y) := by
  obtain ⟨rho, hrho, huniq⟩ :=
    cusp_local_nonzero_coefficient_eq_unique_imaginaryK hu hp hPDE hn hY hstrip
  refine ⟨rho / (2 * (Real.sqrt |(n : ℝ)| : ℂ)), ?_, ?_⟩
  · intro y hy
    rw [hrho y hy]
    exact actualK_amplitude_rescale hn rho ((tau : ℂ)*Complex.I) y
  · intro d hd
    have hdK : ∀ y : ℝ, Y < y → coefficient u n y =
        (2 * (Real.sqrt |(n : ℝ)| : ℂ) * d) * (Real.sqrt y : ℂ) *
          complexOrderK ((tau : ℂ)*Complex.I) (2*Real.pi*|(n : ℝ)|*y) := by
      intro y hy
      rw [hd y hy, sqrt_index_height]
      ring
    have heq := huniq (2 * (Real.sqrt |(n : ℝ)| : ℂ) * d) hdK
    apply (eq_div_iff (mul_ne_zero (by norm_num) (sqrt_abs_index_ne_zero hn))).mpr
    calc
      d * (2 * (Real.sqrt |(n : ℝ)| : ℂ)) =
          2 * (Real.sqrt |(n : ℝ)| : ℂ) * d := by ring
      _ = rho := heq

/-- The corresponding normalized R is unique and is half the actual K
amplitude. No quotient at a possible imaginary-K zero is used. -/
theorem actual_cusp_local_unique_normalizedR
    {u : ℝ × ℝ → ℂ} {tau Y : ℝ} {n : ℤ}
    (hu : ContDiffOn ℝ 2 u (cuspDomain Y))
    (hp : ∀ x y : ℝ, Y < y → u (x+1,y)=u(x,y))
    (hPDE : ∀ p ∈ cuspDomain Y,
      -(p.2 : ℂ)^2*(partialX (partialX u) p+partialY (partialY u) p) =
        ((1/4+tau^2 : ℝ) : ℂ)*u p)
    (hn : n ≠ 0) (hY : 0 < Y)
    (hstrip : Integrable (fun p : PeriodCell × ℝ => p.2⁻¹^2*‖u (p.1,p.2)‖^2)
      ((volume : Measure PeriodCell).prod (volume.restrict (Ioi Y)))) :
    ∃! R : ℂ, ∀ y : ℝ, Y < y → coefficient u n y =
      (2 * R) * (Real.sqrt y : ℂ) *
        complexOrderK ((tau : ℂ)*Complex.I) (2*Real.pi*|(n : ℝ)|*y) := by
  obtain ⟨rho, hrho, huniq⟩ :=
    cusp_local_nonzero_coefficient_eq_unique_imaginaryK hu hp hPDE hn hY hstrip
  refine ⟨rho / 2, ?_, ?_⟩
  · intro y hy
    rw [hrho y hy]
    ring
  · intro d hd
    have heq : 2 * d = rho := huniq (2 * d) hd
    apply (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).mpr
    simpa only [mul_comm] using heq

end
end ImbalancedChen.Part3.ActualMaassWhittakerNormalization20261102
