import ImbalancedChen.Part3Gamma0QuotientConullTransport
import ImbalancedChen.Part3Gamma0EffectiveActionKernel
import Mathlib.MeasureTheory.Group.Action
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

Finite Poincare unfolding for the actual Gamma0(N) action and Mathlib's
canonical hyperbolic volume. Translate labels are the actual effective
group Gamma0(N)/ker(action), so the integral matrices +I and -I label the
same cell. The concrete reduced carrier supplies disjoint cells: this is
proved from the original open/closed modular-cell uniqueness theorem,
not assumed as a disjointness or unfolding field.

The finite translated seed sum is then descended through the existing
actual measurable quotient section, with zero off its conull image. Its
quotient integral equals the original seed integral on the finite union
of these actual matrix translates. No spectral decomposition, infinite
Poincare convergence, or Kuznetsov normalization is asserted.
-/

namespace ImbalancedChen.Part3.Gamma0EffectiveFiniteUnfolding20261025a

noncomputable section

open Set MeasureTheory
open scoped UpperHalfPlane Pointwise
open ImbalancedChen.Part3.Gamma0EffectiveActionKernel20261024z
open ImbalancedChen.Part3.Gamma0FiniteMeasureCarrier20261024z
open ImbalancedChen.Part3.Gamma0CarrierInteriorUniqueness20261025a
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0CarrierAESection20261025a
open ImbalancedChen.Part3.Gamma0CarrierMeasurableInverse20261025a
open ImbalancedChen.Part3.Gamma0QuotientConullTransport20261025a

/-- One actual integral Gamma0 matrix for an effective class. The index
set already identifies the complete central action kernel, including -I. -/
def effectiveRepresentative (N : ℕ) (q : effectiveGamma0 N) :
    CongruenceSubgroup.Gamma0 N := Quotient.out q

theorem effectiveRepresentative_class (N : ℕ) (q : effectiveGamma0 N) :
    (QuotientGroup.mk (effectiveRepresentative N q) : effectiveGamma0 N) = q :=
  Quotient.out_eq' q

/-- The chosen matrix action depends only on the effective class. In
particular, replacing a representative by its central negative has no
effect, because the existing action kernel is exactly {+I,-I}. -/
theorem same_effective_class_action (N : ℕ)
    (a b : CongruenceSubgroup.Gamma0 N)
    (hab : (QuotientGroup.mk a : effectiveGamma0 N) = QuotientGroup.mk b)
    (z : UpperHalfPlane) : a • z = b • z := by
  have h := congrArg (fun q : effectiveGamma0 N => effectivePermHom N q z) hab
  simpa only [effectivePermHom, QuotientGroup.kerLift_mk, gamma0PermHom] using h
/-- The actual matrix action, with no abstract supplied transformation. -/
def effectiveMatrixAction (N : ℕ) (q : effectiveGamma0 N)
    (z : UpperHalfPlane) : UpperHalfPlane := effectiveRepresentative N q • z

/-- A translate of the SAME explicit null-boundary-reduced Gamma0 carrier. -/
def effectiveCell (N : ℕ) [NeZero N] (q : effectiveGamma0 N) : Set UpperHalfPlane :=
  effectiveMatrixAction N q '' reducedCarrier N

theorem effectiveMatrixAction_measurable (N : ℕ) (q : effectiveGamma0 N) :
    Measurable (effectiveMatrixAction N q) := by
  change Measurable (fun z : UpperHalfPlane =>
    (SpecialLinearGroup.mapGL ℝ (effectiveRepresentative N q : SL(2, ℤ))) • z)
  exact (continuous_const_smul _).measurable

theorem effectiveMatrixAction_measurableEmbedding (N : ℕ) (q : effectiveGamma0 N) :
    MeasurableEmbedding (effectiveMatrixAction N q) := by
  change MeasurableEmbedding (fun z : UpperHalfPlane =>
    (SpecialLinearGroup.mapGL ℝ (effectiveRepresentative N q : SL(2, ℤ))) • z)
  exact (MeasurableEquiv.smul _).measurableEmbedding

theorem effectiveMatrixAction_measurePreserving (N : ℕ) (q : effectiveGamma0 N) :
    MeasurePreserving (effectiveMatrixAction N q)
      (volume : Measure UpperHalfPlane) (volume : Measure UpperHalfPlane) := by
  change MeasurePreserving (fun z : UpperHalfPlane =>
    (SpecialLinearGroup.mapGL ℝ (effectiveRepresentative N q : SL(2, ℤ))) • z)
      (volume : Measure UpperHalfPlane) (volume : Measure UpperHalfPlane)
  exact measurePreserving_smul _ _

theorem effectiveCell_measurable (N : ℕ) [NeZero N] (q : effectiveGamma0 N) :
    MeasurableSet (effectiveCell N q) :=
  (effectiveMatrixAction_measurableEmbedding N q).measurableSet_image.mpr
    (reducedCarrier_measurable N)

/-- Distinct effective labels give literally disjoint carrier translates.
An intersection would make the relative ACTUAL Gamma0 matrix lie in the
actual action kernel, contradicting distinct quotient labels. -/
theorem effectiveCell_disjoint (N : ℕ) [NeZero N]
    {q r : effectiveGamma0 N} (hqr : q ≠ r) :
    Disjoint (effectiveCell N q) (effectiveCell N r) := by
  apply Set.disjoint_left.mpr
  intro z hzq hzr
  obtain ⟨x, hx, hqx⟩ := hzq
  obtain ⟨y, hy, hry⟩ := hzr
  let a := effectiveRepresentative N q
  let b := effectiveRepresentative N r
  have hmove : (b⁻¹ * a) • x = y := by
    rw [mul_smul]
    change a • x = z at hqx
    change b • y = z at hry
    rw [hqx, ← hry, inv_smul_smul]
  have hreturn : (b⁻¹ * a) • x ∈ gamma0Carrier N := by
    rw [hmove]
    exact hy.1
  have hkernel : b⁻¹ * a ∈ gamma0ActionKernel N :=
    gamma0_open_to_closed_mem_kernel N (b⁻¹ * a)
      (reducedCarrier_subset_open N hx) hreturn
  have hclasses : (QuotientGroup.mk b : effectiveGamma0 N) = QuotientGroup.mk a :=
    QuotientGroup.eq.mpr hkernel
  apply hqr
  calc
    q = (QuotientGroup.mk a : effectiveGamma0 N) :=
      (effectiveRepresentative_class N q).symm
    _ = QuotientGroup.mk b := hclasses.symm
    _ = r := effectiveRepresentative_class N r

/-- Pulling a seed integral back through one actual matrix translate uses
canonical hyperbolic volume and introduces no central multiplicity factor. -/
theorem lintegral_effectiveCell (N : ℕ) [NeZero N]
    (q : effectiveGamma0 N) (f : UpperHalfPlane → ℝ≥0∞) :
    (∫⁻ z in effectiveCell N q, f z) =
      ∫⁻ z in reducedCarrier N, f (effectiveMatrixAction N q z) := by
  exact ((effectiveMatrixAction_measurePreserving N q).setLIntegral_comp_emb
    (effectiveMatrixAction_measurableEmbedding N q) f (reducedCarrier N)).symm

/-- The finite Poincare seed sum on the actual representative carrier. -/
def finiteSeedTrace (N : ℕ) (S : Finset (effectiveGamma0 N))
    (f : UpperHalfPlane → ℝ≥0∞) (z : UpperHalfPlane) : ℝ≥0∞ :=
  ∑ q ∈ S, f (effectiveMatrixAction N q z)

theorem finiteSeedTrace_measurable (N : ℕ) (S : Finset (effectiveGamma0 N))
    (f : UpperHalfPlane → ℝ≥0∞) (hf : Measurable f) :
    Measurable (finiteSeedTrace N S f) := by
  exact S.measurable_sum (fun q _hq => hf.comp (effectiveMatrixAction_measurable N q))

/-- Genuine finite unfolding: the disjointness is proved for the ACTUAL
cells, and the change of variables is the ACTUAL integral matrix action. -/
theorem lintegral_finiteCells (N : ℕ) [NeZero N]
    (S : Finset (effectiveGamma0 N)) (f : UpperHalfPlane → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ z in ⋃ q ∈ S, effectiveCell N q, f z) =
      ∫⁻ z in reducedCarrier N, finiteSeedTrace N S f z := by
  have hdisj : Set.PairwiseDisjoint (↑S) (effectiveCell N) := by
    intro q _hq r _hr hqr
    exact effectiveCell_disjoint N hqr
  rw [lintegral_biUnion_finset hdisj (fun q _hq => effectiveCell_measurable N q) f]
  simp_rw [lintegral_effectiveCell]
  exact (lintegral_finsetSum S
    (fun q _hq => hf.comp (effectiveMatrixAction_measurable N q))).symm

/-- Descend the finite seed trace through the PREVIOUSLY CONSTRUCTED
actual quotient section. The omitted quotient image is conull. -/
def finitePoincare (N : ℕ) [NeZero N] (S : Finset (effectiveGamma0 N))
    (f : UpperHalfPlane → ℝ≥0∞) : Gamma0OrbitSpace N → ℝ≥0∞ :=
  Function.extend (reducedProjection N)
    (fun z : reducedCarrier N => finiteSeedTrace N S f z) (fun _ => 0)

theorem finitePoincare_projection (N : ℕ) [NeZero N]
    (S : Finset (effectiveGamma0 N)) (f : UpperHalfPlane → ℝ≥0∞)
    (z : reducedCarrier N) :
    finitePoincare N S f (reducedProjection N z) = finiteSeedTrace N S f z :=
  (reducedProjection_measurableEmbedding N).injective.extend_apply _ _ z

theorem finitePoincare_measurable (N : ℕ) [NeZero N]
    (S : Finset (effectiveGamma0 N)) (f : UpperHalfPlane → ℝ≥0∞)
    (hf : Measurable f) : Measurable (finitePoincare N S f) :=
  (reducedProjection_measurableEmbedding N).measurable_extend
    ((finiteSeedTrace_measurable N S f hf).comp measurable_subtype_coe) measurable_const

/-- The actual quotient integral, normalized by the canonical carrier
pushforward, has no hypothetical unfolding or section input. -/
theorem lintegral_finitePoincare (N : ℕ) [NeZero N]
    (S : Finset (effectiveGamma0 N)) (f : UpperHalfPlane → ℝ≥0∞) :
    (∫⁻ q, finitePoincare N S f q ∂carrierPushforward N) =
      ∫⁻ z in reducedCarrier N, finiteSeedTrace N S f z := by
  calc
    _ = ∫⁻ z : reducedCarrier N, finiteSeedTrace N S f z
        ∂reducedCarrierMeasure N := by
      rw [← reducedProjection_map_measure N,
        (reducedProjection_measurableEmbedding N).lintegral_map]
      apply lintegral_congr
      intro z
      exact finitePoincare_projection N S f z
    _ = _ := lintegral_subtype_comap (reducedCarrier_measurable N) _

/-- Final finite actual-Gamma0 Poincare unfolding identity. The label type
quotients the full scalar action kernel, so +I and -I are counted once. -/
theorem finite_poincare_unfolding (N : ℕ) [NeZero N]
    (S : Finset (effectiveGamma0 N)) (f : UpperHalfPlane → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ q, finitePoincare N S f q ∂carrierPushforward N) =
      ∫⁻ z in ⋃ q ∈ S, effectiveCell N q, f z :=
  (lintegral_finitePoincare N S f).trans (lintegral_finiteCells N S f hf).symm

end
end ImbalancedChen.Part3.Gamma0EffectiveFiniteUnfolding20261025a