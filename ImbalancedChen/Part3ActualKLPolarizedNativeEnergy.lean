import ImbalancedChen.Part3ActualKLNativeFormDomain
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

Polarized actual KL energy on the complete original radial form domain.
The tau-weighted map is proved complex linear from the actual unitary
and quotient representatives. Its diagonal identity is the native form
moment theorem, and polarization proves the mixed identity. Actual L2
Cauchy--Schwarz gives integrability of the mixed weighted integrand.
No mixed-energy or assumed form-transport premise occurs.
-/

namespace ImbalancedChen.Part3.ActualKLPolarizedNativeEnergy20261026a

noncomputable section
open MeasureTheory Filter
open RadialSchrodingerL2Form20261025a
open ActualKLCoreTransform20261025a ActualKLCoordinateMeasures20261025a
open ActualKLOntoUnitary20261025a ActualKLNativeFormDomain20261026a

def formTauLinear : radialClosedEnergyDomain 1 →ₗ[ℂ] RawTauL2 where
  toFun := formTauL2
  map_add' e d := by
    have hKL : actualKLUnitary (radialPhysicalEmbedding 1 (e + d)) =
        actualKLUnitary (radialPhysicalEmbedding 1 e) +
          actualKLUnitary (radialPhysicalEmbedding 1 d) := by
      simp only [map_add]
    apply Lp.ext
    filter_upwards [formTauL2_coe_ae (e + d), formTauL2_coe_ae e, formTauL2_coe_ae d,
      Lp.coeFn_add (formTauL2 e) (formTauL2 d),
      Lp.coeFn_add (actualKLUnitary (radialPhysicalEmbedding 1 e))
        (actualKLUnitary (radialPhysicalEmbedding 1 d))] with τ hl he hd hr hsum
    rw [hl, hr, he, hd]
    simp only [tauProduct, hKL, hsum, mul_add]
  map_smul' c e := by
    have hKL : actualKLUnitary (radialPhysicalEmbedding 1 (c • e)) =
        c • actualKLUnitary (radialPhysicalEmbedding 1 e) := by
      simp only [map_smul]
    apply Lp.ext
    filter_upwards [formTauL2_coe_ae (c • e), formTauL2_coe_ae e,
      Lp.coeFn_smul c (formTauL2 e),
      Lp.coeFn_smul c (actualKLUnitary (radialPhysicalEmbedding 1 e))] with τ hl he hr hsmul
    rw [hl, hr, he]
    simp only [tauProduct, hKL, hsmul, smul_eq_mul]
    ring

/-- Polarization written in the domain variables of an actual linear
map, so that its diagonal norm identities can be substituted directly. -/
private theorem linear_inner_polarization
    {V H : Type*} [AddCommGroup V] [Module ℂ V]
    [SeminormedAddCommGroup H] [InnerProductSpace ℂ H]
    (L : V →ₗ[ℂ] H) (e d : V) :
    inner ℂ (L e) (L d) =
      ((‖L (e + d)‖ : ℂ) ^ 2 - (‖L (e - d)‖ : ℂ) ^ 2 +
        ((‖L (e - Complex.I • d)‖ : ℂ) ^ 2 -
          (‖L (e + Complex.I • d)‖ : ℂ) ^ 2) * Complex.I) / 4 := by
  rw [inner_eq_sum_norm_sq_div_four]
  simp only [map_add, map_sub, map_smul]

theorem formTauLinear_inner (e d : radialClosedEnergyDomain 1) :
    inner ℂ (formTauLinear e) (formTauLinear d) =
      inner ℂ (radialClosedDerivative 1 e) (radialClosedDerivative 1 d) +
        inner ℂ (radialClosedExponential 1 e) (radialClosedExponential 1 d) := by
  have hsq (x : radialClosedEnergyDomain 1) :
      (‖formTauLinear x‖ : ℂ) ^ 2 =
        (‖radialClosedDerivative 1 x‖ : ℂ) ^ 2 +
          (‖radialClosedExponential 1 x‖ : ℂ) ^ 2 := by
    exact_mod_cast formTauL2_norm_sq x
  rw [linear_inner_polarization formTauLinear,
    linear_inner_polarization (radialClosedDerivative 1).toLinearMap,
    linear_inner_polarization (radialClosedExponential 1).toLinearMap]
  simp_rw [hsq]
  ring

private theorem tauProduct_inner (g h : RawTauL2) (τ : ℝ) :
    inner ℂ (tauProduct g τ) (tauProduct h τ) =
      (τ ^ 2 : ℂ) * (star (g τ) * h τ) := by
  simp only [tauProduct, RCLike.inner_apply', star_mul,
    Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring

theorem actualKL_form_pairing_integrable (e d : radialClosedEnergyDomain 1) :
    Integrable (fun τ : ℝ => (τ ^ 2 : ℂ) *
      (star (actualKLUnitary (radialPhysicalEmbedding 1 e) τ) *
        actualKLUnitary (radialPhysicalEmbedding 1 d) τ)) tauMeasure := by
  apply (L2.integrable_inner (𝕜 := ℂ) (formTauL2 e) (formTauL2 d)).congr
  filter_upwards [formTauL2_coe_ae e, formTauL2_coe_ae d] with τ he hd
  rw [he, hd, tauProduct_inner]

theorem actualKL_polarized_energy (e d : radialClosedEnergyDomain 1) :
    inner ℂ (radialClosedDerivative 1 e) (radialClosedDerivative 1 d) +
        inner ℂ (radialClosedExponential 1 e) (radialClosedExponential 1 d) =
      ∫ τ : ℝ, (τ ^ 2 : ℂ) *
        (star (actualKLUnitary (radialPhysicalEmbedding 1 e) τ) *
          actualKLUnitary (radialPhysicalEmbedding 1 d) τ) ∂tauMeasure := by
  rw [← formTauLinear_inner]
  change inner ℂ (formTauL2 e) (formTauL2 d) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [formTauL2_coe_ae e, formTauL2_coe_ae d] with τ he hd
  rw [he, hd, tauProduct_inner]

/-- Full physical form pairing: the mass term remains the original
physical inner product, and the derivative/exponential part is polarized. -/
theorem actualKL_full_form_pairing (e d : radialClosedEnergyDomain 1) :
    inner ℂ e d =
      inner ℂ (radialPhysicalEmbedding 1 e) (radialPhysicalEmbedding 1 d) +
        ∫ τ : ℝ, (τ ^ 2 : ℂ) *
          (star (actualKLUnitary (radialPhysicalEmbedding 1 e) τ) *
            actualKLUnitary (radialPhysicalEmbedding 1 d) τ) ∂tauMeasure := by
  rw [← actualKL_polarized_energy, radialClosedEnergy_inner 1 (by norm_num)]
  norm_num
  <;> ring

end
end ImbalancedChen.Part3.ActualKLPolarizedNativeEnergy20261026a
