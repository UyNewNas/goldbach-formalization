import ImbalancedChen.P5ZU1011OriginalSixteenEligibilityState
import ImbalancedChen.ActualPrimeIcoCellTestFunctions

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The actual sixteen-policy first-failure circuit retains constant true and
constant false rows for disabled tests and the disallowed W branch. Such
rows cannot be supplied to a theorem requiring every affine form nonzero.
This module removes zero rows exactly, reindexes the remaining finite
family by Fin, and supplies the genuine prime harmonic limit. A zero row
which fails makes the complete cell empty; no null-wall claim is used for
a constant row. There is no form-properness or cell-mean premise.
-/
namespace ImbalancedChen.P5Z.U1011OriginalSixteenMixedGatePrimeTests

noncomputable section

open Set MeasureTheory Filter Topology
open Classical
open U11Integral U1011OriginalSixteenEligibilityState
open scoped BigOperators

def mixedRegion {ι : Type*} (g : ι → MixedGate) : Set LogFour :=
  {v | ∀ i, (g i).Holds v}

theorem measurableSet_mixedRegion {ι : Type*} [Fintype ι] (g : ι → MixedGate) :
    MeasurableSet (mixedRegion g) :=
  MeasurableSet.iInter (fun i => MixedGate.measurableSet_holds (g i))

abbrev ProperIndex {ι : Type*} (g : ι → MixedGate) :=
  {i : ι // (g i).linear ≠ 0}

def reducedForms {ι : Type*} [Fintype ι] (g : ι → MixedGate) :
    Fin (Fintype.card (ProperIndex g)) → LogFour →L[ℝ] ℝ :=
  fun j => (g ((Fintype.equivFin (ProperIndex g)).symm j).val).linear

def reducedBounds {ι : Type*} [Fintype ι] (g : ι → MixedGate) :
    Fin (Fintype.card (ProperIndex g)) → ℝ :=
  fun j => (g ((Fintype.equivFin (ProperIndex g)).symm j).val).offset

/-- Nonzero is obtained from the exact finite subtype, not assumed. -/
theorem reducedForms_ne_zero {ι : Type*} [Fintype ι] (g : ι → MixedGate)
    (j : Fin (Fintype.card (ProperIndex g))) : reducedForms g j ≠ 0 :=
  ((Fintype.equivFin (ProperIndex g)).symm j).property

/-- A constant affine row has the same truth value at every point. -/
theorem zero_row_independent (g : MixedGate) (hg : g.linear = 0) (v w : LogFour) :
    g.Holds v ↔ g.Holds w := by
  simp only [MixedGate.Holds, hg, ContinuousLinearMap.zero_apply]

/-- If the literal cell is nonempty, every zero row is a true constant;
strict success of the retained rows therefore implies the entire cell. -/
theorem reduced_strict_subset {ι : Type*} [Fintype ι] (g : ι → MixedGate)
    (hne : (mixedRegion g).Nonempty) :
    primeAffineGateRegion (reducedForms g) (reducedBounds g) ⊆ mixedRegion g := by
  obtain ⟨v₀, hv₀⟩ := hne
  intro v hv i
  by_cases hi : (g i).linear = 0
  · exact (zero_row_independent (g i) hi v₀ v).mp (hv₀ i)
  · let j := (Fintype.equivFin (ProperIndex g)) ⟨i, hi⟩
    have hgate : (g i).linear v < (g i).offset := by
      simpa only [reducedForms, reducedBounds, j, Equiv.symm_apply_apply] using hv j
    cases hs : (g i).strict
    · simpa only [MixedGate.Holds, hs, Bool.false_eq_true, if_false] using hgate.le
    · simpa only [MixedGate.Holds, hs, if_true] using hgate

/-- Every mixed strict/weak row in the actual cell satisfies the weak
closed sandwich of the retained proper rows. -/
theorem mixed_subset_reduced_weak {ι : Type*} [Fintype ι] (g : ι → MixedGate)
    (v : LogFour) (hv : v ∈ mixedRegion g)
    (j : Fin (Fintype.card (ProperIndex g))) :
    reducedForms g j v ≤ reducedBounds g j := by
  let q : ProperIndex g := (Fintype.equivFin (ProperIndex g)).symm j
  change (g q.val).linear v ≤ (g q.val).offset
  have hrow := hv q.val
  cases hs : (g q.val).strict
  · simpa only [MixedGate.Holds, hs, Bool.false_eq_true, if_false] using hrow
  · exact (by simpa only [MixedGate.Holds, hs, if_true] using hrow :
      (g q.val).linear v < (g q.val).offset).le

/-- Genuine four-prime harmonic limit for a finite mixed affine circuit,
including its zero tautologies and contradictions. All properness,
strict/weak sandwich and empty-cell cases are proved here. -/
theorem tendsto_actualPrimeBox_mixedRegion {ι : Type*} [Fintype ι]
    (g : ι → MixedGate) (f : LogFour → ℝ)
    (hf : ContinuousOn f (univ.pi
      (fun _ : Fin 4 => Icc (417 / 5000 : ℝ) (59 / 250 : ℝ)))) :
    Tendsto (fun N : ℕ => actualPrimeBoxTestSum N
      (fun _ : Fin 4 => (417 / 5000 : ℝ)) (fun _ => (59 / 250 : ℝ))
      ((mixedRegion g).indicator f)) atTop
      (𝓝 (∫ v in logPrimeBox (fun _ : Fin 4 => (417 / 5000 : ℝ))
        (fun _ => (59 / 250 : ℝ)) ∩ mixedRegion g, f v * ∏ i, 1 / v i)) := by
  by_cases hne : (mixedRegion g).Nonempty
  · exact tendsto_actualPrimeBoxTestSum_cube_affineSandwich
      (by norm_num : (0 : ℝ) < 417 / 5000)
      (by norm_num : (417 / 5000 : ℝ) < 59 / 250)
      (reducedForms g) (reducedBounds g) (reducedForms_ne_zero g)
      (mixedRegion g) (measurableSet_mixedRegion g)
      (reduced_strict_subset g hne) (mixed_subset_reduced_weak g) f hf
  · have hempty : mixedRegion g = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)) using 1 <;>
      simp [hempty, actualPrimeBoxTestSum]

/-- Direct named limit for every actual original policy's unique
branch/first-failed eligibility cell, with no hForms input. -/
theorem tendsto_actualPrimeBox_policyCell
    (p : U1011OriginalSixteenPolicyBank.Policy) (s : PolicyState)
    (f : LogFour → ℝ)
    (hf : ContinuousOn f (univ.pi
      (fun _ : Fin 4 => Icc (417 / 5000 : ℝ) (59 / 250 : ℝ)))) :
    Tendsto (fun N : ℕ => actualPrimeBoxTestSum N
      (fun _ : Fin 4 => (417 / 5000 : ℝ)) (fun _ => (59 / 250 : ℝ))
      ((policyCell p s).indicator f)) atTop
      (𝓝 (∫ v in logPrimeBox (fun _ : Fin 4 => (417 / 5000 : ℝ))
        (fun _ => (59 / 250 : ℝ)) ∩ policyCell p s, f v * ∏ i, 1 / v i)) := by
  simpa only [policyCell_eq_affineCell, affineCell, mixedRegion] using
    tendsto_actualPrimeBox_mixedRegion (gateFamily p s) f hf

end
end ImbalancedChen.P5Z.U1011OriginalSixteenMixedGatePrimeTests
