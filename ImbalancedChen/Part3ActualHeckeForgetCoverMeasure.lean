import ImbalancedChen.Part3ActualHeckeCanonicalCarrierMeasure

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
The actual forget-prime-level map Gamma0(N*p)\H -> Gamma0(N)\H pushes
the EXISTING canonical quotient measure forward to (p+1) times the same
canonical base measure. The degree is derived from actual p+1 disjoint
correspondence cells and the proved canonical carrier bridge. It is not
an assumed finite-cover normalization or an arbitrary level-index formula.
-/

namespace ImbalancedChen.Part3.ActualHeckeForgetCoverMeasure20261026b
noncomputable section
open Set MeasureTheory Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups UpperHalfPlane BigOperators
open ActualPrimeHeckeBranchSeparation20261026b ActualHeckeFiniteCover20261026b
open ActualHeckeCorrespondenceCarrier20261026b ActualHeckeCarrierFundamental20261026b
open ActualHeckeCanonicalCarrierMeasure20261026b Gamma0CarrierAESection20261025a
open Gamma0QuotientCellPushforward20261025a

def forgetPrimeLevel (N p : ℕ) : Gamma0OrbitSpace (N*p) → Gamma0OrbitSpace N :=
  Quotient.lift (orbitProjection N) (by
    intro z w hzw
    obtain ⟨g,hg⟩ := MulAction.orbitRel_apply.mp hzw
    apply Quotient.sound
    exact MulAction.orbitRel_apply.mpr ⟨includePrimeLevel N p g,hg⟩)

theorem forgetPrimeLevel_projection (N p : ℕ) (z : ℍ) :
    forgetPrimeLevel N p (orbitProjection (N*p) z) = orbitProjection N z := rfl

theorem forgetPrimeLevel_measurable (N p : ℕ) : Measurable (forgetPrimeLevel N p) :=
  measurable_from_quotient.mpr (orbitProjection_measurable N)

/-- Actual p+1 canonical-volume contributions, one from each true
representative cell, yield the exact degree of the actual quotient map. -/
theorem forgetPrimeLevel_lintegral (N p : ℕ) [NeZero N] [NeZero (N*p)]
    (hp : p.Prime) (hpN : ¬ p ∣ N) (F : Gamma0OrbitSpace N → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ q, F (forgetPrimeLevel N p q) ∂carrierPushforward (N*p)) =
      (p+1 : ℝ≥0∞) * ∫⁻ q, F q ∂carrierPushforward N := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [← correspondenceCarrier_pushforward_eq N p hp hpN,
    lintegral_cellPushforward (N*p) (correspondenceCarrier N p hp hpN)
      (fun q => F (forgetPrimeLevel N p q)) (hF.comp (forgetPrimeLevel_measurable N p))]
  simp_rw [forgetPrimeLevel_projection]
  rw [correspondenceCarrier_lintegral N p hp hpN (fun z => F (orbitProjection N z))
    (hF.comp (orbitProjection_measurable N))]
  have hsum : (fun z : ℍ => ∑ j : Branch p, F (orbitProjection N (coverAction N p hp hpN j z))) =
      fun z : ℍ => (p+1 : ℝ≥0∞)*F (orbitProjection N z) := by
    funext z
    have hpoint (j : Branch p) : F (orbitProjection N (coverAction N p hp hpN j z)) =
        F (orbitProjection N z) := congrArg F
      (orbitProjection_smul N (coverRepresentative N p hp hpN j) z)
    simp_rw [hpoint]
    simp [branch_card, nsmul_eq_mul]
  rw [hsum, lintegral_const_mul _ (hF.comp (orbitProjection_measurable N)),
    ← lintegral_reducedCarrier N F hF]

/-- Full measure equality for the already-existing canonical quotient
measures, not merely equality of their total volumes. -/
theorem forgetPrimeLevel_map_measure (N p : ℕ) [NeZero N] [NeZero (N*p)]
    (hp : p.Prime) (hpN : ¬ p ∣ N) :
    (carrierPushforward (N*p)).map (forgetPrimeLevel N p) =
      (p+1 : ℝ≥0∞) • carrierPushforward N := by
  ext A hA
  rw [Measure.map_apply (forgetPrimeLevel_measurable N p) hA, Measure.smul_apply, smul_eq_mul]
  have h := forgetPrimeLevel_lintegral N p hp hpN (A.indicator (fun _ => 1))
    (measurable_const.indicator hA)
  have hcomp : (fun q => A.indicator (fun _ => (1 : ℝ≥0∞)) (forgetPrimeLevel N p q)) =
      (forgetPrimeLevel N p ⁻¹' A).indicator (fun _ => 1) := rfl
  rw [hcomp, lintegral_indicator ((forgetPrimeLevel_measurable N p) hA), lintegral_indicator hA] at h
  simpa only [lintegral_one, Measure.restrict_apply_univ] using h

end
end ImbalancedChen.Part3.ActualHeckeForgetCoverMeasure20261026b
