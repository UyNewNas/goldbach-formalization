import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Pointwise
import ImbalancedChen.Part3ModularFundamentalFiniteMeasure

/-!
SOURCEONLY / UNCOMPILED / no acceptance credit, 2026-10-24.

For positive `N`, Mathlib's actual `CongruenceSubgroup.Gamma0 N` has finite
index in `SL(2, ℤ)`. We take one representative from every finite quotient
class, invert it, and translate the actual classical modular domain. The
result is a measurable finite-volume carrier for the Gamma0 orbit space.
No almost-everywhere disjointness or quotient Plancherel statement is asserted.
-/

namespace ImbalancedChen.Part3.Gamma0FiniteMeasureCarrier20261024z

noncomputable section

open Set MeasureTheory
open ImbalancedChen.Part3.ModularFundamentalFiniteMeasure20261024z
open scoped UpperHalfPlane Pointwise

private instance : MeasurableConstSMul SL(2, ℤ) UpperHalfPlane where
  measurable_const_smul g := by
    change Measurable (fun z : UpperHalfPlane =>
      (SpecialLinearGroup.mapGL ℝ g) • z)
    exact (continuous_const_smul _).measurable

private instance : SMulInvariantMeasure SL(2, ℤ) UpperHalfPlane
    (volume : Measure UpperHalfPlane) where
  measure_preimage_smul g s hs := by
    change (volume : Measure UpperHalfPlane)
        ((fun z : UpperHalfPlane => (SpecialLinearGroup.mapGL ℝ g) • z) ⁻¹' s) =
      (volume : Measure UpperHalfPlane) s
    exact SMulInvariantMeasure.measure_preimage_smul
      (SpecialLinearGroup.mapGL ℝ g) hs

/-- The actual finite class space for Mathlib's level-`N` Gamma0. -/
abbrev gamma0Classes (N : ℕ) :=
  SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N

/-- `Gamma0 N` has finite index for positive `N`, using Mathlib's instance. -/
theorem gamma0_finiteIndex (N : ℕ) [NeZero N] :
    (CongruenceSubgroup.Gamma0 N).FiniteIndex := inferInstance

local instance (N : ℕ) [NeZero N] : Fintype (gamma0Classes N) :=
  (CongruenceSubgroup.Gamma0 N).fintypeQuotientOfFiniteIndex

/-- The inverse of the chosen representative of a right Gamma0 class.
The inversion turns right cosets into the left translates used by the action. -/
def inverseClassRep (N : ℕ) [NeZero N] (q : gamma0Classes N) : SL(2, ℤ) :=
  (Quotient.out q)⁻¹

/-- A finite union of genuine `SL(2,ℤ)` translates of Mathlib's modular cell. -/
def gamma0Carrier (N : ℕ) [NeZero N] : Set UpperHalfPlane :=
  ⋃ q : gamma0Classes N, inverseClassRep N q • modularFD

/-- Every Gamma0 orbit meets this finite union. This is a covering claim;
it does not assert that distinct translates have null overlap. -/
theorem exists_gamma0_smul_mem_carrier (N : ℕ) [NeZero N]
    (z : UpperHalfPlane) :
    ∃ γ : CongruenceSubgroup.Gamma0 N,
      (γ : SL(2, ℤ)) • z ∈ gamma0Carrier N := by
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
  let q : gamma0Classes N := QuotientGroup.mk g
  let r : SL(2, ℤ) := Quotient.out q
  have hcoset : g ∈ r • (CongruenceSubgroup.Gamma0 N : Set SL(2, ℤ)) := by
    rw [← QuotientGroup.eq_class_eq_leftCoset]
    change (g : gamma0Classes N) = (r : gamma0Classes N)
    exact (Quotient.out_eq' q).symm
  have hmem : r⁻¹ * g ∈ CongruenceSubgroup.Gamma0 N := by
    rwa [mem_leftCoset_iff] at hcoset
  refine ⟨⟨r⁻¹ * g, hmem⟩, ?_⟩
  change (r⁻¹ * g) • z ∈ gamma0Carrier N
  apply Set.mem_iUnion.mpr
  refine ⟨q, ?_⟩
  change (r⁻¹ * g) • z ∈ r⁻¹ • modularFD
  rw [mem_smul_set_iff_inv_smul_mem]
  simpa [smul_smul, r] using hg

theorem gamma0Carrier_measurable (N : ℕ) [NeZero N] :
    MeasurableSet (gamma0Carrier N) := by
  unfold gamma0Carrier
  exact MeasurableSet.iUnion fun q => modularFD_measurable.const_smul _

theorem gamma0Carrier_measure_le_card (N : ℕ) [NeZero N] :
    (volume : Measure UpperHalfPlane) (gamma0Carrier N) ≤
      (Fintype.card (gamma0Classes N) : ℝ≥0∞) *
        (volume : Measure UpperHalfPlane) modularFD := by
  calc
    (volume : Measure UpperHalfPlane) (gamma0Carrier N) ≤
        ∑ q : gamma0Classes N,
          (volume : Measure UpperHalfPlane) (inverseClassRep N q • modularFD) := by
      exact measure_iUnion_fintype_le _ _
    _ = ∑ _q : gamma0Classes N,
          (volume : Measure UpperHalfPlane) modularFD := by
      simp only [measure_smul]
    _ = (Fintype.card (gamma0Classes N) : ℝ≥0∞) *
          (volume : Measure UpperHalfPlane) modularFD := by
      simp [Finset.sum_const, nsmul_eq_mul]

/-- The finite class count is exactly the subgroup index, not a new bound. -/
theorem gamma0Classes_card_eq_index (N : ℕ) [NeZero N] :
    Fintype.card (gamma0Classes N) =
      (CongruenceSubgroup.Gamma0 N).index := by
  rw [(CongruenceSubgroup.Gamma0 N).index_eq_card,
    Nat.card_eq_fintype_card]

theorem gamma0Carrier_measure_le_index (N : ℕ) [NeZero N] :
    (volume : Measure UpperHalfPlane) (gamma0Carrier N) ≤
      ((CongruenceSubgroup.Gamma0 N).index : ℝ≥0∞) *
        (volume : Measure UpperHalfPlane) modularFD := by
  simpa only [gamma0Classes_card_eq_index N] using
    gamma0Carrier_measure_le_card N

/-- In particular, the actual Gamma0 carrier has finite hyperbolic volume. -/
theorem gamma0Carrier_finite (N : ℕ) [NeZero N] :
    (volume : Measure UpperHalfPlane) (gamma0Carrier N) < ∞ := by
  exact (gamma0Carrier_measure_le_index N).trans_lt
    (ENNReal.mul_lt_top (by simp) modularFD_finite)

end
end ImbalancedChen.Part3.Gamma0FiniteMeasureCarrier20261024z
