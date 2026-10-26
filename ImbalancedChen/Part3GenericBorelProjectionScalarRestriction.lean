import ImbalancedChen.Part3GenericGlobalProjectionScalarConsistency

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The scalar measure of a genuine Borel-projected vector is the restriction
of its original RMK measure. Complementation is proved in the scalar L2
fibers, then transported through the existing global unitary. The mixed
spectral coefficients of the two complementary sectors vanish, including
after a further arbitrary Borel projection. No measure decomposition or
spectral-completeness premise is introduced.
-/
namespace ImbalancedChen.Part3.GenericBorelProjectionScalarRestriction20261026b

noncomputable section
open Set MeasureTheory
open GenericResolventScalarMeasure20261025a
open GenericResolventCyclicL2Representation20261025a
open GenericResolventGlobalSpectralAssembly20261025a
open GenericCyclicBorelProjection20261025a
open GenericGlobalBorelProjection20261025a
open GenericGlobalProjectionScalarConsistency20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)

theorem borelMultiplier_compl_apply (f : H)
    (B : Set (ResolventSpectrum R)) (hB : MeasurableSet B)
    (ξ : ScalarL2 R hSA f) :
    borelMultiplier R hSA f Bᶜ hB.compl ξ = ξ - borelMultiplier R hSA f B hB ξ := by
  apply Lp.ext
  filter_upwards [borelMultiplier_coe_ae R hSA f Bᶜ hB.compl ξ,
    borelMultiplier_coe_ae R hSA f B hB ξ,
    Lp.coeFn_sub ξ (borelMultiplier R hSA f B hB ξ)] with t hc hb hs
  rw [hc, hs, hb]
  by_cases ht : t ∈ B <;> simp [ht]

theorem diagonalBorel_compl_apply
    (B : Set (ResolventSpectrum R)) (hB : MeasurableSet B)
    (ξ : SpectralSum R hSA) :
    diagonalBorel R hSA Bᶜ hB.compl ξ = ξ - diagonalBorel R hSA B hB ξ := by
  apply lp.ext
  intro i
  exact borelMultiplier_compl_apply R hSA (i : H) B hB (ξ i)

theorem globalBorelProjection_compl_apply
    (B : Set (ResolventSpectrum R)) (hB : MeasurableSet B) (u : H) :
    globalBorelProjection R hSA Bᶜ hB.compl u =
      u - globalBorelProjection R hSA B hB u := by
  rw [globalBorelProjection_apply, diagonalBorel_compl_apply, map_sub,
    (spectralUnitary R hSA).apply_symm_apply]
  rfl

/-- This uses the previously constructed global projections, not a new PVM axiom. -/
theorem globalBorelProjection_apply_comm
    (A B : Set (ResolventSpectrum R)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (u : H) :
    globalBorelProjection R hSA A hA (globalBorelProjection R hSA B hB u) =
      globalBorelProjection R hSA B hB (globalBorelProjection R hSA A hA u) := by
  change ((globalBorelProjection R hSA A hA).comp
    (globalBorelProjection R hSA B hB)) u =
    ((globalBorelProjection R hSA B hB).comp
      (globalBorelProjection R hSA A hA)) u
  rw [globalBorelProjection_comp_inter, globalBorelProjection_comp_inter]
  simp only [Set.inter_comm]

/-- Exact equality of measures for the projected physical vector. -/
theorem scalarMeasure_projection_eq_restrict (u : H)
    (B : Set (ResolventSpectrum R)) (hB : MeasurableSet B) :
    scalarMeasure R hSA (globalBorelProjection R hSA B hB u) =
      (scalarMeasure R hSA u).restrict B := by
  apply Measure.ext
  intro A hA
  rw [Measure.restrict_apply hA,
    scalarMeasure_eq_projection_norm_square R hSA _ A hA,
    scalarMeasure_eq_projection_norm_square R hSA u (A ∩ B) (hA.inter hB)]
  have hcomp := congrArg (fun T : H →L[ℂ] H => T u)
    (globalBorelProjection_comp_inter R hSA A B hA hB)
  change globalBorelProjection R hSA A hA
    (globalBorelProjection R hSA B hB u) =
    globalBorelProjection R hSA (A ∩ B) (hA.inter hB) u at hcomp
  rw [hcomp]

theorem scalarMeasure_residual_eq_restrict_compl (u : H)
    (B : Set (ResolventSpectrum R)) (hB : MeasurableSet B) :
    scalarMeasure R hSA (u - globalBorelProjection R hSA B hB u) =
      (scalarMeasure R hSA u).restrict Bᶜ := by
  rw [← globalBorelProjection_compl_apply R hSA B hB u]
  exact scalarMeasure_projection_eq_restrict R hSA u Bᶜ hB.compl

/-- Genuine complex mixed Borel coefficient, for two independent vectors.
Its vanishing is stronger than merely splitting diagonal masses. -/
theorem projection_residual_cross_zero (u v : H)
    (A B : Set (ResolventSpectrum R)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    inner ℂ (globalBorelProjection R hSA A hA
      (globalBorelProjection R hSA B hB u))
      (v - globalBorelProjection R hSA B hB v) = 0 := by
  have hid : globalBorelProjection R hSA B hB
      (globalBorelProjection R hSA B hB u) =
      globalBorelProjection R hSA B hB u :=
    congrArg (fun T : H →L[ℂ] H => T u)
      (globalBorelProjection_idempotent R hSA B hB)
  have hfixed : globalBorelProjection R hSA B hB
      (globalBorelProjection R hSA A hA (globalBorelProjection R hSA B hB u)) =
      globalBorelProjection R hSA A hA (globalBorelProjection R hSA B hB u) := by
    rw [globalBorelProjection_apply_comm R hSA B A hB hA, hid]
  have hi := globalBorelProjection_inner R hSA B hB
    (globalBorelProjection R hSA A hA (globalBorelProjection R hSA B hB u)) v
  rw [hfixed] at hi
  rw [inner_sub_right, hi, sub_self]

theorem projected_projection_residual_cross_zero (u v : H)
    (A B : Set (ResolventSpectrum R)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    inner ℂ (globalBorelProjection R hSA A hA
      (globalBorelProjection R hSA B hB u))
      (globalBorelProjection R hSA A hA
        (v - globalBorelProjection R hSA B hB v)) = 0 := by
  have hid := congrArg (fun T : H →L[ℂ] H =>
    T (globalBorelProjection R hSA B hB u))
    (globalBorelProjection_idempotent R hSA A hA)
  have hi := globalBorelProjection_inner R hSA A hA
    (globalBorelProjection R hSA A hA (globalBorelProjection R hSA B hB u))
    (v - globalBorelProjection R hSA B hB v)
  rw [show globalBorelProjection R hSA A hA
      (globalBorelProjection R hSA A hA (globalBorelProjection R hSA B hB u)) =
      globalBorelProjection R hSA A hA (globalBorelProjection R hSA B hB u) from hid] at hi
  rw [← hi]
  exact projection_residual_cross_zero R hSA u v A B hA hB

/-- Polarized sector splitting, allowing separate vectors and complex
coefficients. The cross terms vanish before taking real parts. -/
theorem scalarMeasure_complementary_linear_combination (u v : H) (a b : ℂ)
    (B : Set (ResolventSpectrum R)) (hB : MeasurableSet B) :
    scalarMeasure R hSA
      (a • globalBorelProjection R hSA B hB u +
        b • (v - globalBorelProjection R hSA B hB v)) =
      ENNReal.ofReal (‖a‖ ^ 2) • (scalarMeasure R hSA u).restrict B +
        ENNReal.ofReal (‖b‖ ^ 2) • (scalarMeasure R hSA v).restrict Bᶜ := by
  rw [← scalarMeasure_projection_eq_restrict R hSA u B hB,
    ← scalarMeasure_residual_eq_restrict_compl R hSA v B hB]
  apply Measure.ext
  intro A hA
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp only [smul_eq_mul]
  rw [scalarMeasure_eq_projection_norm_square R hSA _ A hA,
    scalarMeasure_eq_projection_norm_square R hSA _ A hA,
    scalarMeasure_eq_projection_norm_square R hSA _ A hA,
    map_add, map_smul, map_smul]
  have hcross : inner ℂ
      (a • globalBorelProjection R hSA A hA (globalBorelProjection R hSA B hB u))
      (b • globalBorelProjection R hSA A hA
        (v - globalBorelProjection R hSA B hB v)) = 0 := by
    rw [inner_smul_left, inner_smul_right,
      projected_projection_residual_cross_zero R hSA u v A B hA hB, mul_zero, mul_zero]
  rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hcross,
    norm_smul, norm_smul, mul_pow, mul_pow,
    ENNReal.ofReal_add (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (mul_nonneg (sq_nonneg _) (sq_nonneg _)),
    ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_mul (sq_nonneg _)]

end
end ImbalancedChen.Part3.GenericBorelProjectionScalarRestriction20261026b
