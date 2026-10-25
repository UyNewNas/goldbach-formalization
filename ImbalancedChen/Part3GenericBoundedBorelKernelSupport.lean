import ImbalancedChen.Part3GenericBoundedBorelNorm

/-! SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
The exact kernel is the range of the actual zero-set projection. For arbitrary
complex coefficients, the adjoint kernel is proved equal before identifying the
closure of the range. No self-adjointness shortcut or kernel premise is used. -/
namespace ImbalancedChen.Part3.GenericBoundedBorelKernelSupport20261025a
noncomputable section
open MeasureTheory
open ImbalancedChen.Part3.GenericResolventScalarMeasure20261025a
open ImbalancedChen.Part3.GenericGlobalBorelProjection20261025a
open ImbalancedChen.Part3.GenericBoundedBorelCalculus20261025a
open ImbalancedChen.Part3.GenericBoundedBorelNorm20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)

def zeroSet (φ : BoundedBorelFunction (ResolventSpectrum R)) : Set (ResolventSpectrum R) :=
  {t | φ t = 0}

theorem zeroSet_measurable (φ : BoundedBorelFunction (ResolventSpectrum R)) :
    MeasurableSet (zeroSet R φ) := φ.measurable_toFun measurableSet_singleton

def zeroProjection (φ : BoundedBorelFunction (ResolventSpectrum R)) : H →L[ℂ] H :=
  globalBorelProjection R hSA (zeroSet R φ) (zeroSet_measurable R φ)

/-- Exact scalar-measure-a.e. description of the kernel at each vector. -/
theorem borelFunctionalCalculus_apply_eq_zero_iff
    (φ : BoundedBorelFunction (ResolventSpectrum R)) (u : H) :
    borelFunctionalCalculus R hSA φ u = 0 ↔
      ∀ᵐ t ∂scalarMeasure R hSA u, φ t = 0 := by
  constructor
  · intro hu
    have hi : (∫ t, ‖φ t‖ ^ 2 ∂scalarMeasure R hSA u) = 0 := by
      rw [← borelFunctionalCalculus_norm_square, hu]
      simp
    have hz := (integral_eq_zero_iff_of_nonneg (fun t => sq_nonneg ‖φ t‖)
      (integrable_norm_square φ (scalarMeasure R hSA u))).mp hi
    filter_upwards [hz] with t ht
    have hn : ‖φ t‖ = 0 := by
      change ‖φ t‖ ^ 2 = 0 at ht
      nlinarith [norm_nonneg (φ t)]
    exact norm_eq_zero.mp hn
  · intro hφ
    have h := borelFunctionalCalculus_apply_eq_of_ae R hSA φ (BoundedBorelFunction.const 0) u hφ
    rw [borelFunctionalCalculus_const] at h
    simpa using h

theorem borelFunctionalCalculus_comp_zeroProjection
    (φ : BoundedBorelFunction (ResolventSpectrum R)) :
    (borelFunctionalCalculus R hSA φ).comp (zeroProjection R hSA φ) = 0 := by
  unfold zeroProjection
  rw [← borelFunctionalCalculus_indicator, ← borelFunctionalCalculus_mul]
  have h := borelFunctionalCalculus_congr R hSA
    (φ.mul (BoundedBorelFunction.indicator (zeroSet R φ) (zeroSet_measurable R φ)))
    (BoundedBorelFunction.const 0) (fun t => by
      by_cases ht : φ t = 0
      · simp [BoundedBorelFunction.mul, BoundedBorelFunction.indicator,
          BoundedBorelFunction.const, zeroSet, ht]
      · simp [BoundedBorelFunction.mul, BoundedBorelFunction.indicator,
          BoundedBorelFunction.const, zeroSet, ht])
  rw [h, borelFunctionalCalculus_const]
  simp

theorem zeroProjection_fixed_of_kernel
    (φ : BoundedBorelFunction (ResolventSpectrum R)) (u : H)
    (hu : borelFunctionalCalculus R hSA φ u = 0) : zeroProjection R hSA φ u = u := by
  have hz := (borelFunctionalCalculus_apply_eq_zero_iff R hSA φ u).mp hu
  have hae : BoundedBorelFunction.indicator (zeroSet R φ) (zeroSet_measurable R φ)
      =ᵐ[scalarMeasure R hSA u] BoundedBorelFunction.const 1 := by
    filter_upwards [hz] with t ht
    simp [BoundedBorelFunction.indicator, BoundedBorelFunction.const, zeroSet, ht]
  have h := borelFunctionalCalculus_apply_eq_of_ae R hSA _ _ u hae
  rw [borelFunctionalCalculus_indicator, borelFunctionalCalculus_const] at h
  simpa only [one_smul, ContinuousLinearMap.id_apply] using h

theorem kernel_eq_zeroProjection_range
    (φ : BoundedBorelFunction (ResolventSpectrum R)) :
    (borelFunctionalCalculus R hSA φ).ker = (zeroProjection R hSA φ).range := by
  ext u
  change (borelFunctionalCalculus R hSA φ u = 0) ↔ ∃ v, zeroProjection R hSA φ v = u
  constructor
  · intro hu
    exact ⟨u, zeroProjection_fixed_of_kernel R hSA φ u hu⟩
  · rintro ⟨v, rfl⟩
    have h := congrArg (fun T : H →L[ℂ] H => T v)
      (borelFunctionalCalculus_comp_zeroProjection R hSA φ)
    exact h

/-- The adjoint kernel calculation is valid for arbitrary complex φ. -/
theorem adjoint_kernel_eq_kernel
    (φ : BoundedBorelFunction (ResolventSpectrum R)) :
    (borelFunctionalCalculus R hSA φ).adjoint.ker = (borelFunctionalCalculus R hSA φ).ker := by
  ext u
  change ((borelFunctionalCalculus R hSA φ).adjoint u = 0) ↔
    (borelFunctionalCalculus R hSA φ u = 0)
  rw [← borelFunctionalCalculus_conj, borelFunctionalCalculus_apply_eq_zero_iff,
    borelFunctionalCalculus_apply_eq_zero_iff]
  constructor
  · intro h
    filter_upwards [h] with t ht
    change star (φ t) = 0 at ht
    simpa using congrArg star ht
  · intro h
    filter_upwards [h] with t ht
    change star (φ t) = 0
    simp only [ht, star_zero]

theorem closure_range_eq_zeroProjection_orthogonal
    (φ : BoundedBorelFunction (ResolventSpectrum R)) :
    (borelFunctionalCalculus R hSA φ).range.topologicalClosure =
      (zeroProjection R hSA φ).rangeᗮ := by
  have h := (borelFunctionalCalculus R hSA φ).adjoint.orthogonal_ker
  rw [ContinuousLinearMap.adjoint_adjoint, adjoint_kernel_eq_kernel,
    kernel_eq_zeroProjection_range] at h
  exact h.symm

/-- A pointwise nonvanishing coefficient gives actual injectivity. No lower
bound is needed for this kernel conclusion. -/
theorem borelFunctionalCalculus_injective_of_nonzero
    (φ : BoundedBorelFunction (ResolventSpectrum R)) (hφ : ∀ t, φ t ≠ 0) :
    Function.Injective (borelFunctionalCalculus R hSA φ) := by
  have hz : zeroSet R φ = ∅ := by
    ext t
    simp [zeroSet, hφ t]
  have hk : (borelFunctionalCalculus R hSA φ).ker = ⊥ := by
    rw [kernel_eq_zeroProjection_range]
    unfold zeroProjection
    simp [hz, globalBorelProjection_empty]
  exact LinearMap.ker_eq_bot.mp hk

end
end ImbalancedChen.Part3.GenericBoundedBorelKernelSupport20261025a