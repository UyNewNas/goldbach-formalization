import ImbalancedChen.Part3Gamma0QuotientCellPushforward
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.
An arbitrary integral translate of the actual modular cell has quotient
pushforward at most the canonical Gamma0 carrier measure.  The proof
locates its actual finite coset cell and changes that cell by an actual
Gamma0 element.  No arbitrary-frame or local-Lp supplier is assumed.
-/
namespace ImbalancedChen.Part3.Gamma0IntegralCellLp20261026b
noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane Pointwise
open Gamma0FiniteMeasureCarrier20261024z
open Gamma0QuotientCellPushforward20261025a
open ModularFundamentalFiniteMeasure20261024z

/-- The arbitrary integral cell is one of the canonical finite cells,
up to a displayed element of the actual level subgroup. -/
theorem integral_cell_eq_gamma0_translate (N : ℕ) [NeZero N] (g : SL(2, ℤ)) :
    ∃ (q : gamma0Classes N) (η : CongruenceSubgroup.Gamma0 N),
      g • modularFD = η • (inverseClassRep N q • modularFD) := by
  let q : gamma0Classes N := QuotientGroup.mk g⁻¹
  let r : SL(2, ℤ) := Quotient.out q
  have hcoset : g⁻¹ ∈ r • (CongruenceSubgroup.Gamma0 N : Set SL(2, ℤ)) := by
    rw [← QuotientGroup.eq_class_eq_leftCoset]
    change (g⁻¹ : gamma0Classes N) = (r : gamma0Classes N)
    exact (Quotient.out_eq' q).symm
  have hmem : r⁻¹ * g⁻¹ ∈ CongruenceSubgroup.Gamma0 N := by
    rwa [mem_leftCoset_iff] at hcoset
  have hη : g * r ∈ CongruenceSubgroup.Gamma0 N := by
    simpa only [mul_inv_rev, inv_inv] using
      (CongruenceSubgroup.Gamma0 N).inv_mem hmem
  refine ⟨q, ⟨g * r, hη⟩, ?_⟩
  change g • modularFD = (g * r) • (r⁻¹ • modularFD)
  simp only [mul_smul, smul_inv_smul]

theorem integral_cell_pushforward_le (N : ℕ) [NeZero N] (g : SL(2, ℤ)) :
    cellPushforward N (g • modularFD) ≤ carrierPushforward N := by
  obtain ⟨q, η, heq⟩ := integral_cell_eq_gamma0_translate N g
  rw [heq, cellPushforward_gamma0_translate]
  apply Measure.map_mono _ (orbitProjection_measurable N)
  exact Measure.restrict_mono_set _ (Set.subset_iUnion _ q)

/-- True quotient Lp restricts to every actual integral modular cell;
this is valid for arbitrary measurable Lp representatives. -/
theorem quotient_memLp_integral_cell (N : ℕ) [NeZero N] (g : SL(2, ℤ))
    {p : ℝ≥0∞} {F : Gamma0OrbitSpace N → ℂ}
    (hF : MemLp F p (carrierPushforward N)) :
    MemLp (fun z => F (orbitProjection N z)) p
      ((volume : Measure UpperHalfPlane).restrict (g • modularFD)) := by
  have hcell : MemLp F p (cellPushforward N (g • modularFD)) :=
    MemLp.mono_measure (integral_cell_pushforward_le N g) hF
  exact hcell.comp_of_map (orbitProjection_measurable N).aemeasurable

end
end ImbalancedChen.Part3.Gamma0IntegralCellLp20261026b
