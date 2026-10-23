import ImbalancedChen.Part3SmoothReciprocityLogMixed

/-!
Regularity and compact support of the literal logarithmic reciprocity weight.
All three real atom parameters are unrestricted. The original positive circle
character and all factors of the actual weight are retained.
-/

namespace ImbalancedChen.Part3

noncomputable section

open scoped SchwartzMap FourierTransform ContDiff
open CommonSmoothCutoff

/-- The literal logarithmic weight is smooth for all signed real atom
parameters, with no scale or phase bound required for regularity. -/
theorem CommonSmoothCutoff.smoothReciprocityLogWeight_contDiff
    {d : ℕ} (a b c : EuclideanSpace ℝ (Fin d))
    (Q : EuclideanSpace ℝ (Fin d) → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (Z u₀ rho₀ : ℝ) :
    ContDiff ℝ ∞ (smoothReciprocityLogWeight a b c Q Z u₀ rho₀) := by
  let U : EuclideanSpace ℝ (Fin d) → ℝ := fun t ↦
    u₀ * Real.exp (inner ℝ a t)
  let R : EuclideanSpace ℝ (Fin d) → ℝ := fun t ↦
    rho₀ * Real.exp (inner ℝ b t)
  let F : 𝓢(ℝ, ℂ) := 𝓕 dyadicCutoffSchwartz
  have hU : ContDiff ℝ ∞ U :=
    contDiff_const.mul (Real.contDiff_exp.comp (innerSL ℝ a).contDiff)
  have hR : ContDiff ℝ ∞ R :=
    contDiff_const.mul (Real.contDiff_exp.comp (innerSL ℝ b).contDiff)
  have hE : ContDiff ℝ ∞ (fun t : EuclideanSpace ℝ (Fin d) ↦
      (Real.exp (inner ℝ c t) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      (Real.contDiff_exp.comp (innerSL ℝ c).contDiff)
  have hlow : ContDiff ℝ ∞ poissonSmoothLowPass := by
    exact dyadicBump.contDiff.comp (contDiff_const.add (contDiff_id.div_const 2))
  have hcut : ContDiff ℝ ∞ (fun t ↦ (poissonSmoothLowPass (U t / Z) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hlow.comp (hU.div_const Z))
  have hF : ContDiff ℝ ∞ (fun t ↦ F (U t)) :=
    (F.smooth (⊤ : ℕ∞)).comp hU
  have hcharacter : ContDiff ℝ ∞
      (fun v : ℝ ↦ fourier (1 : ℤ) (v : UnitAddCircle)) := by
    have heq : (fun v : ℝ ↦ fourier (1 : ℤ) (v : UnitAddCircle)) =
        (fun v : ℝ ↦ Complex.exp ((2 * Real.pi * Complex.I) * (v : ℂ))) := by
      funext v
      simp only [fourier_coe_apply, Int.cast_one, Complex.ofReal_one, mul_one, div_one]
    rw [heq]
    exact Complex.contDiff_exp.comp
      (contDiff_const.mul Complex.ofRealCLM.contDiff)
  have hphase : ContDiff ℝ ∞ (fun t ↦
      fourier (1 : ℤ) ((R t * U t : ℝ) : UnitAddCircle)) :=
    hcharacter.comp (hR.mul hU)
  change ContDiff ℝ ∞ (fun t ↦
    (Q t * (Real.exp (inner ℝ c t) : ℂ)) *
      ((poissonSmoothLowPass (U t / Z) : ℂ) * F (U t) *
        fourier (1 : ℤ) ((R t * U t : ℝ) : UnitAddCircle)))
  exact (hQ.mul hE).mul ((hcut.mul hF).mul hphase)

/-- Multiplication by the actual profile cannot enlarge the localizer's
topological support; no smoothness assumption is needed. -/
theorem CommonSmoothCutoff.smoothReciprocityLogWeight_tsupport_subset
    {d : ℕ} (a b c : EuclideanSpace ℝ (Fin d))
    (Q : EuclideanSpace ℝ (Fin d) → ℂ) (Z u₀ rho₀ : ℝ) :
    tsupport (smoothReciprocityLogWeight a b c Q Z u₀ rho₀) ⊆ tsupport Q := by
  unfold smoothReciprocityLogWeight
  calc
    tsupport (fun t ↦ Q t * (Real.exp (inner ℝ c t) : ℂ) *
        smoothReciprocityProfile Z (rho₀ * Real.exp (inner ℝ b t))
          (u₀ * Real.exp (inner ℝ a t))) ⊆
        tsupport (fun t ↦ Q t * (Real.exp (inner ℝ c t) : ℂ)) :=
      tsupport_mul_subset_left
    _ ⊆ tsupport Q := tsupport_mul_subset_left

/-- Compact support of the localizer suffices for compact support of the
full actual weight, independently of any smoothness hypotheses. -/
theorem CommonSmoothCutoff.smoothReciprocityLogWeight_hasCompactSupport
    {d : ℕ} (a b c : EuclideanSpace ℝ (Fin d))
    (Q : EuclideanSpace ℝ (Fin d) → ℂ) (hQc : HasCompactSupport Q)
    (Z u₀ rho₀ : ℝ) :
    HasCompactSupport (smoothReciprocityLogWeight a b c Q Z u₀ rho₀) := by
  unfold smoothReciprocityLogWeight
  exact hQc.mul_right.mul_right

end

end ImbalancedChen.Part3
