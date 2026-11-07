import ImbalancedChen.Part3GenericBoundedBorelKernelSupport

/-! SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
A genuine positive lower bound constructs the literal measurable reciprocal,
with its actual uniform bound. The actual Borel operators are proved two-sided
inverses, producing a native continuous linear equivalence and lower norm bound.
No invertibility or inverse-operator premise is assumed. -/
namespace ImbalancedChen.Part3.GenericBoundedBorelReciprocal20261025a
noncomputable section
open MeasureTheory
open ImbalancedChen.Part3.GenericResolventScalarMeasure20261025a
open ImbalancedChen.Part3.GenericBoundedBorelCalculus20261025a

variable {X : Type*} [MeasurableSpace X]

def boundedReciprocal (φ : BoundedBorelFunction X) (c : ℝ) (hc : 0 < c)
    (hlower : ∀ t, c ≤ ‖φ t‖) : BoundedBorelFunction X where
  toFun := fun t => (φ t)⁻¹
  measurable_toFun := φ.measurable_toFun.inv
  bound := c⁻¹
  bound_nonneg := inv_nonneg.mpr hc.le
  norm_le_bound := fun t => by
    rw [norm_inv]
    simpa only [one_div] using one_div_le_one_div_of_le hc (hlower t)

theorem boundedReciprocal_nonzero (φ : BoundedBorelFunction X) (c : ℝ) (hc : 0 < c)
    (hlower : ∀ t, c ≤ ‖φ t‖) (t : X) : φ t ≠ 0 := by
  intro ht
  have h := hlower t
  rw [ht, norm_zero] at h
  exact (not_le.mpr hc) h

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)

theorem borelFunctionalCalculus_reciprocal_left
    (φ : BoundedBorelFunction (ResolventSpectrum R)) (c : ℝ) (hc : 0 < c)
    (hlower : ∀ t, c ≤ ‖φ t‖) :
    (borelFunctionalCalculus R hSA (boundedReciprocal φ c hc hlower)).comp
      (borelFunctionalCalculus R hSA φ) = ContinuousLinearMap.id ℂ H := by
  rw [← borelFunctionalCalculus_mul]
  have h := borelFunctionalCalculus_congr R hSA
    ((boundedReciprocal φ c hc hlower).mul φ) (BoundedBorelFunction.const 1) (fun t => by
      change (φ t)⁻¹ * φ t = 1
      exact inv_mul_cancel₀ (boundedReciprocal_nonzero φ c hc hlower t))
  rw [h, borelFunctionalCalculus_const, one_smul]

theorem borelFunctionalCalculus_reciprocal_right
    (φ : BoundedBorelFunction (ResolventSpectrum R)) (c : ℝ) (hc : 0 < c)
    (hlower : ∀ t, c ≤ ‖φ t‖) :
    (borelFunctionalCalculus R hSA φ).comp
      (borelFunctionalCalculus R hSA (boundedReciprocal φ c hc hlower)) =
        ContinuousLinearMap.id ℂ H := by
  rw [← borelFunctionalCalculus_mul]
  have h := borelFunctionalCalculus_congr R hSA
    (φ.mul (boundedReciprocal φ c hc hlower)) (BoundedBorelFunction.const 1) (fun t => by
      change φ t * (φ t)⁻¹ = 1
      exact mul_inv_cancel₀ (boundedReciprocal_nonzero φ c hc hlower t))
  rw [h, borelFunctionalCalculus_const, one_smul]

def borelFunctionalCalculusEquiv
    (φ : BoundedBorelFunction (ResolventSpectrum R)) (c : ℝ) (hc : 0 < c)
    (hlower : ∀ t, c ≤ ‖φ t‖) : H ≃L[ℂ] H :=
  ContinuousLinearEquiv.equivOfInverse'
    (borelFunctionalCalculus R hSA φ)
    (borelFunctionalCalculus R hSA (boundedReciprocal φ c hc hlower))
    (borelFunctionalCalculus_reciprocal_right R hSA φ c hc hlower)
    (borelFunctionalCalculus_reciprocal_left R hSA φ c hc hlower)

theorem borelFunctionalCalculusEquiv_apply
    (φ : BoundedBorelFunction (ResolventSpectrum R)) (c : ℝ) (hc : 0 < c)
    (hlower : ∀ t, c ≤ ‖φ t‖) (u : H) :
    borelFunctionalCalculusEquiv R hSA φ c hc hlower u = borelFunctionalCalculus R hSA φ u := rfl

theorem borelFunctionalCalculusEquiv_symm_apply
    (φ : BoundedBorelFunction (ResolventSpectrum R)) (c : ℝ) (hc : 0 < c)
    (hlower : ∀ t, c ≤ ‖φ t‖) (u : H) :
    (borelFunctionalCalculusEquiv R hSA φ c hc hlower).symm u =
      borelFunctionalCalculus R hSA (boundedReciprocal φ c hc hlower) u := rfl

theorem borelFunctionalCalculus_reciprocal_norm_le
    (φ : BoundedBorelFunction (ResolventSpectrum R)) (c : ℝ) (hc : 0 < c)
    (hlower : ∀ t, c ≤ ‖φ t‖) :
    ‖borelFunctionalCalculus R hSA (boundedReciprocal φ c hc hlower)‖ ≤ c⁻¹ :=
  borelFunctionalCalculus_opNorm_le R hSA _

theorem borelFunctionalCalculus_norm_lower
    (φ : BoundedBorelFunction (ResolventSpectrum R)) (c : ℝ) (hc : 0 < c)
    (hlower : ∀ t, c ≤ ‖φ t‖) (u : H) :
    c * ‖u‖ ≤ ‖borelFunctionalCalculus R hSA φ u‖ := by
  have hleft := congrArg (fun T : H →L[ℂ] H => T u)
    (borelFunctionalCalculus_reciprocal_left R hSA φ c hc hlower)
  have h := borelFunctionalCalculus_norm_le R hSA (boundedReciprocal φ c hc hlower)
    (borelFunctionalCalculus R hSA φ u)
  change ‖borelFunctionalCalculus R hSA (boundedReciprocal φ c hc hlower)
      (borelFunctionalCalculus R hSA φ u)‖ ≤ c⁻¹ * ‖borelFunctionalCalculus R hSA φ u‖ at h
  change borelFunctionalCalculus R hSA (boundedReciprocal φ c hc hlower)
    (borelFunctionalCalculus R hSA φ u) = u at hleft
  rw [hleft] at h
  have hd : ‖u‖ ≤ ‖borelFunctionalCalculus R hSA φ u‖ / c := by
    simpa only [div_eq_mul_inv, mul_comm] using h
  simpa only [mul_comm] using (le_div_iff₀ hc).mp hd

end
end ImbalancedChen.Part3.GenericBoundedBorelReciprocal20261025a