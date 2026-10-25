import ImbalancedChen.Part3GenericUnboundedRealBorelCalculus

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.
The actual bounded Borel operator with coefficient (m-z)^(-1), for every
nonreal z and arbitrary measurable real m. Its sharp uniform estimate,
first resolvent identity and adjoint formula follow from actual scalar
coefficients. Native graph/inverse binding is in the next module.
-/

namespace ImbalancedChen.Part3.GenericRealBorelNonrealResolvent20261025a

noncomputable section
open MeasureTheory
open ImbalancedChen.Part3.GenericResolventScalarMeasure20261025a
open ImbalancedChen.Part3.GenericResolventGlobalSpectralAssembly20261025a
open ImbalancedChen.Part3.GenericBoundedBorelCalculus20261025a
open ImbalancedChen.Part3.GenericUnboundedRealBorelCalculus20261025a

/-- A real scalar never equals a nonreal spectral parameter. -/
theorem real_sub_nonreal_ne_zero (x : ℝ) (z : ℂ) (hz : z.im ≠ 0) : (x : ℂ) - z ≠ 0 := by
  intro h
  apply hz
  have hi := congrArg Complex.im h
  simpa only [Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.zero_im, neg_eq_zero] using hi

theorem reciprocal_norm_le (x : ℝ) (z : ℂ) (hz : z.im ≠ 0) :
    ‖((x : ℂ) - z)⁻¹‖ ≤ 1 / |z.im| := by
  have hlow : |z.im| ≤ ‖(x : ℂ) - z‖ := by
    simpa only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] using
      Complex.abs_im_le_norm ((x : ℂ) - z)
  simpa only [norm_inv, one_div] using
    one_div_le_one_div_of_le (abs_pos.mpr hz) hlow

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)
variable (m : ResolventSpectrum R → ℝ) (hm : Measurable m)

def reciprocalSymbol (z : ℂ) (hz : z.im ≠ 0) : BoundedBorelFunction (ResolventSpectrum R) where
  toFun := fun t => ((m t : ℂ) - z)⁻¹
  measurable_toFun := by fun_prop
  bound := 1 / |z.im|
  bound_nonneg := by positivity
  norm_le_bound := fun t => reciprocal_norm_le (m t) z hz

def nonrealResolvent (z : ℂ) (hz : z.im ≠ 0) : H →L[ℂ] H :=
  borelFunctionalCalculus R hSA (reciprocalSymbol R m hm z hz)

theorem nonrealResolvent_opNorm_le (z : ℂ) (hz : z.im ≠ 0) :
    ‖nonrealResolvent R hSA m hm z hz‖ ≤ 1 / |z.im| :=
  borelFunctionalCalculus_opNorm_le R hSA _

theorem nonrealResolvent_norm_le (z : ℂ) (hz : z.im ≠ 0) (f : H) :
    ‖nonrealResolvent R hSA m hm z hz f‖ ≤ (1 / |z.im|) * ‖f‖ :=
  borelFunctionalCalculus_norm_le R hSA _ f

theorem nonrealResolvent_coordinates_ae (z : ℂ) (hz : z.im ≠ 0) (f : H)
    (i : SpectralIndex R hSA) :
    ((spectralUnitary R hSA).symm (nonrealResolvent R hSA m hm z hz f)) i =ᵐ[scalarMeasure R hSA (i : H)]
      (fun t => ((m t : ℂ) - z)⁻¹ * (((spectralUnitary R hSA).symm f) i) t) := by
  unfold nonrealResolvent
  rw [borelFunctionalCalculus_coordinates]
  exact fiberMultiplier_coe_ae R hSA (i : H) _ _

theorem nonrealResolvent_injective (z : ℂ) (hz : z.im ≠ 0) :
    Function.Injective (nonrealResolvent R hSA m hm z hz) :=
  calculus_injective_of_ne_zero R hSA _
    (fun t => inv_ne_zero (real_sub_nonreal_ne_zero (m t) z hz))

/-- The standard first identity has the sign dictated by (A-z)^(-1). -/
theorem nonrealResolvent_first_identity (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    nonrealResolvent R hSA m hm z hz - nonrealResolvent R hSA m hm w hw =
      (z-w) • ((nonrealResolvent R hSA m hm z hz).comp (nonrealResolvent R hSA m hm w hw)) := by
  unfold nonrealResolvent
  rw [← borelFunctionalCalculus_sub]
  calc
    _ = borelFunctionalCalculus R hSA
        ((BoundedBorelFunction.const (z-w)).mul
          ((reciprocalSymbol R m hm z hz).mul (reciprocalSymbol R m hm w hw))) := by
      apply borelFunctionalCalculus_congr
      intro t
      change ((m t : ℂ)-z)⁻¹ - ((m t : ℂ)-w)⁻¹ =
        (z-w) * (((m t : ℂ)-z)⁻¹ * ((m t : ℂ)-w)⁻¹)
      field_simp [real_sub_nonreal_ne_zero (m t) z hz, real_sub_nonreal_ne_zero (m t) w hw]
      <;> ring
    _ = _ := by
      rw [borelFunctionalCalculus_mul, borelFunctionalCalculus_mul, borelFunctionalCalculus_const]
      ext f
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]

theorem nonreal_star (z : ℂ) (hz : z.im ≠ 0) : (star z).im ≠ 0 := by simpa using hz

/-- Conjugating the parameter gives the genuine Hilbert adjoint. -/
theorem nonrealResolvent_adjoint (z : ℂ) (hz : z.im ≠ 0) :
    (nonrealResolvent R hSA m hm z hz).adjoint =
      nonrealResolvent R hSA m hm (star z) (nonreal_star z hz) := by
  unfold nonrealResolvent
  rw [← borelFunctionalCalculus_conj]
  apply borelFunctionalCalculus_congr
  intro t
  change star (((m t : ℂ)-z)⁻¹) = ((m t : ℂ)-star z)⁻¹
  simp [Complex.star_def]

end
end ImbalancedChen.Part3.GenericRealBorelNonrealResolvent20261025a

