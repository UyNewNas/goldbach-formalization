import ImbalancedChen.Part3Gamma0FiniteMeasureCarrier
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

This constructs a measure on the actual Gamma0 orbit quotient by pushing
forward the restriction of Mathlib's canonical hyperbolic volume to a
specified cell. The main new change-of-cell statement proves that this
pushforward is unchanged under every actual Gamma0 translate of the cell.
The concrete finite carrier gives a finite pushforward and meets every
orbit. No claim of independence under arbitrary fundamental domains or
of almost-everywhere injectivity of that carrier is made here.

In particular, this is a spatial quotient measure construction. It does
not identify any automorphic spectral measure, dt/cosh(pi*t), or the
continuous-spectrum coefficient 1/(4*pi).
-/

namespace ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a

noncomputable section

open Set MeasureTheory
open scoped UpperHalfPlane Pointwise
open ImbalancedChen.Part3.Gamma0FiniteMeasureCarrier20261024z
open ImbalancedChen.Part3.ModularFundamentalFiniteMeasure20261024z

/-- The genuine orbit space for Mathlib's level-N subgroup acting on H. -/
abbrev Gamma0OrbitSpace (N : ℕ) :=
  Quotient (MulAction.orbitRel (CongruenceSubgroup.Gamma0 N) UpperHalfPlane)

/-- The quotient projection, with the quotient measurable space inherited
from the measurable upper half-plane. -/
def orbitProjection (N : ℕ) : UpperHalfPlane → Gamma0OrbitSpace N :=
  Quotient.mk''

theorem orbitProjection_measurable (N : ℕ) : Measurable (orbitProjection N) :=
  measurable_quotient_mk''

/-- Points related by an actual congruence-subgroup matrix have equal images. -/
@[simp] theorem orbitProjection_smul (N : ℕ)
    (γ : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
    orbitProjection N (γ • z) = orbitProjection N z := by
  apply Quotient.sound
  exact (MulAction.orbitRel_apply).mpr ⟨γ, rfl⟩

/-- A saturated preimage is invariant under every Gamma0 element. -/
theorem orbitProjection_preimage_smul (N : ℕ)
    (γ : CongruenceSubgroup.Gamma0 N) (A : Set (Gamma0OrbitSpace N)) :
    γ • (orbitProjection N ⁻¹' A) = orbitProjection N ⁻¹' A := by
  ext z
  rw [mem_smul_set_iff_inv_smul_mem]
  change orbitProjection N (γ⁻¹ • z) ∈ A ↔ orbitProjection N z ∈ A
  rw [orbitProjection_smul]

private instance (N : ℕ) :
    SMulInvariantMeasure (CongruenceSubgroup.Gamma0 N) UpperHalfPlane
      (volume : Measure UpperHalfPlane) where
  measure_preimage_smul γ s hs := by
    change (volume : Measure UpperHalfPlane)
        ((fun z : UpperHalfPlane =>
          (SpecialLinearGroup.mapGL ℝ (γ : SL(2, ℤ))) • z) ⁻¹' s) =
      (volume : Measure UpperHalfPlane) s
    exact SMulInvariantMeasure.measure_preimage_smul
      (SpecialLinearGroup.mapGL ℝ (γ : SL(2, ℤ))) hs

/-- Push canonical hyperbolic volume on a cell to the actual orbit quotient.
The name records the cell dependence that has not yet been eliminated. -/
def cellPushforward (N : ℕ) (s : Set UpperHalfPlane) :
    Measure (Gamma0OrbitSpace N) :=
  ((volume : Measure UpperHalfPlane).restrict s).map (orbitProjection N)

/-- The exact evaluation formula uses the canonical spatial volume. -/
theorem cellPushforward_apply (N : ℕ) (s : Set UpperHalfPlane)
    {A : Set (Gamma0OrbitSpace N)} (hA : MeasurableSet A) :
    cellPushforward N s A =
      (volume : Measure UpperHalfPlane) (orbitProjection N ⁻¹' A ∩ s) := by
  rw [cellPushforward, Measure.map_apply (orbitProjection_measurable N) hA,
    Measure.restrict_apply ((orbitProjection_measurable N) hA)]

/-- The quotient pushforward has exactly the original cell's total mass. -/
theorem cellPushforward_univ (N : ℕ) (s : Set UpperHalfPlane) :
    cellPushforward N s univ = (volume : Measure UpperHalfPlane) s := by
  rw [cellPushforward_apply N s MeasurableSet.univ]
  simp only [preimage_univ, univ_inter]

/-- Removing or changing a null boundary of a cell does not change its
quotient pushforward. No measurability of the cells is needed. -/
theorem cellPushforward_congr (N : ℕ) {s t : Set UpperHalfPlane}
    (hst : s =ᵐ[(volume : Measure UpperHalfPlane)] t) :
    cellPushforward N s = cellPushforward N t := by
  unfold cellPushforward
  rw [Measure.restrict_congr_set hst]

/-- The actual Gamma0 change-of-cell lemma. Saturation of a quotient
preimage and canonical hyperbolic invariance prove equality of measures,
not merely equality of their total masses. -/
theorem cellPushforward_gamma0_translate (N : ℕ)
    (γ : CongruenceSubgroup.Gamma0 N) (s : Set UpperHalfPlane) :
    cellPushforward N (γ • s) = cellPushforward N s := by
  ext A hA
  rw [cellPushforward_apply N (γ • s) hA,
    cellPushforward_apply N s hA]
  calc
    (volume : Measure UpperHalfPlane) (orbitProjection N ⁻¹' A ∩ γ • s) =
        (volume : Measure UpperHalfPlane)
          (γ • (orbitProjection N ⁻¹' A ∩ s)) := by
      rw [smul_set_inter, orbitProjection_preimage_smul]
    _ = (volume : Measure UpperHalfPlane) (orbitProjection N ⁻¹' A ∩ s) :=
      measure_smul (volume : Measure UpperHalfPlane) γ _

/-- The resulting quotient integration formula for nonnegative measurable
functions. This supplies a spatial change of variables, without spectral
normalization assumptions. -/
theorem lintegral_cellPushforward (N : ℕ) (s : Set UpperHalfPlane)
    (F : Gamma0OrbitSpace N → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ q, F q ∂cellPushforward N s) =
      ∫⁻ z in s, F (orbitProjection N z) := by
  exact lintegral_map hF (orbitProjection_measurable N)

/-- A Gamma0 translate preserves all quotient-observable integrals. -/
theorem lintegral_quotient_observable_gamma0_translate (N : ℕ)
    (γ : CongruenceSubgroup.Gamma0 N) (s : Set UpperHalfPlane)
    (F : Gamma0OrbitSpace N → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z in γ • s, F (orbitProjection N z)) =
      ∫⁻ z in s, F (orbitProjection N z) := by
  rw [← lintegral_cellPushforward N (γ • s) F hF,
    cellPushforward_gamma0_translate, lintegral_cellPushforward N s F hF]

/-- The previously constructed concrete carrier supplies a finite measure
on the actual quotient. This definition does not assert a global FD theorem. -/
def carrierPushforward (N : ℕ) [NeZero N] : Measure (Gamma0OrbitSpace N) :=
  cellPushforward N (gamma0Carrier N)

theorem carrierPushforward_mass_le_index (N : ℕ) [NeZero N] :
    carrierPushforward N univ ≤
      ((CongruenceSubgroup.Gamma0 N).index : ℝ≥0∞) *
        (volume : Measure UpperHalfPlane) modularFD := by
  rw [carrierPushforward, cellPushforward_univ]
  exact gamma0Carrier_measure_le_index N

theorem carrierPushforward_finite (N : ℕ) [NeZero N] :
    carrierPushforward N univ < ∞ := by
  rw [carrierPushforward, cellPushforward_univ]
  exact gamma0Carrier_finite N

/-- The actual finite carrier maps onto every Gamma0 orbit. This is
surjectivity; almost-everywhere injectivity is still a separate obligation. -/
theorem orbitProjection_carrier_surjective (N : ℕ) [NeZero N]
    (q : Gamma0OrbitSpace N) :
    ∃ z ∈ gamma0Carrier N, orbitProjection N z = q := by
  refine Quotient.inductionOn q (fun z => ?_)
  obtain ⟨γ, hγ⟩ := exists_gamma0_smul_mem_carrier N z
  exact ⟨γ • z, hγ, orbitProjection_smul N γ z⟩

end
end ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
