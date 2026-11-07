import ImbalancedChen.Part3ActualHeckeFiniteCover
import ImbalancedChen.Part3Gamma0EffectiveFiniteUnfolding

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
The actual finite Hecke correspondence carrier is a union of actual
Gamma0(N) representative translates of the canonical reduced carrier.
The original action kernel is proved to act trivially on every branch,
so the representative effective labels are injective. Actual carrier
disjointness and canonical-volume change of variables then give its
true finite nonnegative integral identity. Equality with the canonical
level-N*p quotient carrier is a separate remaining theorem.
-/

namespace ImbalancedChen.Part3.ActualHeckeCorrespondenceCarrier20261026b
noncomputable section
open Set MeasureTheory Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups UpperHalfPlane BigOperators
open ActualPrimeHeckeBranchSeparation20261026b ActualPrimeHeckeBranchPermutation20261026b
open ActualHeckeBranchTransitivity20261026b ActualHeckeFiniteCover20261026b
open Gamma0EffectiveActionKernel20261024z Gamma0EffectiveFiniteUnfolding20261025a
open Gamma0CarrierAESection20261025a

theorem actionKernel_branch_trivial (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (g : CongruenceSubgroup.Gamma0 N) (hg : g ∈ gamma0ActionKernel N) (j : Branch p) :
    branchImage N p hp hpN g g.property j = j := by
  obtain ⟨a, ha, hea⟩ := branchImage_factor N p hp hpN g g.property j
  have hcentral : branchMatrix p j * ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * branchMatrix p j := by
    rcases (gamma0_actionKernel_iff N g).mp hg with hpos | hneg
    · simp [hpos]
    · simp [hneg]
  exact branch_eq_of_two_factorizations p hp _ j a g (hea.symm.trans hcentral)

def coverEffectiveClass (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N) (j : Branch p) :
    effectiveGamma0 N := QuotientGroup.mk (coverRepresentative N p hp hpN j)

theorem coverEffectiveClass_injective (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N) :
    Function.Injective (coverEffectiveClass N p hp hpN) := by
  intro j k hjk
  let a := coverRepresentative N p hp hpN j
  let b := coverRepresentative N p hp hpN k
  have hker : a⁻¹*b ∈ gamma0ActionKernel N := QuotientGroup.eq.mp hjk
  have hcomp := branchImage_mul N p hp hpN a (a⁻¹*b) none
  have ha := coverRepresentative_branch N p hp hpN j
  have hb := coverRepresentative_branch N p hp hpN k
  have htr := actionKernel_branch_trivial N p hp hpN (a⁻¹*b) hker j
  have heq : a*(a⁻¹*b) = b := by group
  simpa only [heq, ha, hb, htr] using hcomp.symm

def coverAction (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N) (j : Branch p) (z : ℍ) : ℍ :=
  (coverRepresentative N p hp hpN j : SL(2, ℤ)) • z

def coverCell (N p : ℕ) [NeZero N] (hp : p.Prime) (hpN : ¬ p ∣ N) (j : Branch p) : Set ℍ :=
  coverAction N p hp hpN j '' reducedCarrier N

def correspondenceCarrier (N p : ℕ) [NeZero N] (hp : p.Prime) (hpN : ¬ p ∣ N) : Set ℍ :=
  ⋃ j : Branch p, coverCell N p hp hpN j

theorem coverCell_eq_effective (N p : ℕ) [NeZero N] (hp : p.Prime) (hpN : ¬ p ∣ N)
    (j : Branch p) : coverCell N p hp hpN j = effectiveCell N (coverEffectiveClass N p hp hpN j) := by
  change coverAction N p hp hpN j '' reducedCarrier N =
    effectiveMatrixAction N (coverEffectiveClass N p hp hpN j) '' reducedCarrier N
  congr 1
  funext z
  exact same_effective_class_action N (coverRepresentative N p hp hpN j)
    (effectiveRepresentative N (coverEffectiveClass N p hp hpN j))
    (effectiveRepresentative_class N (coverEffectiveClass N p hp hpN j)).symm z

theorem coverCell_measurable (N p : ℕ) [NeZero N] (hp : p.Prime) (hpN : ¬ p ∣ N)
    (j : Branch p) : MeasurableSet (coverCell N p hp hpN j) := by
  rw [coverCell_eq_effective]
  exact effectiveCell_measurable N _

theorem coverCell_disjoint (N p : ℕ) [NeZero N] (hp : p.Prime) (hpN : ¬ p ∣ N)
    {j k : Branch p} (hjk : j ≠ k) : Disjoint (coverCell N p hp hpN j) (coverCell N p hp hpN k) := by
  rw [coverCell_eq_effective, coverCell_eq_effective]
  exact effectiveCell_disjoint N (fun h => hjk (coverEffectiveClass_injective N p hp hpN h))

theorem coverAction_measurePreserving (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N) (j : Branch p) :
    MeasurePreserving (coverAction N p hp hpN j) (volume : Measure ℍ) (volume : Measure ℍ) := by
  change MeasurePreserving (fun z : ℍ =>
    SpecialLinearGroup.mapGL ℝ (coverRepresentative N p hp hpN j : SL(2, ℤ)) • z) _ _
  exact measurePreserving_smul _ _

theorem coverAction_measurableEmbedding (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N) (j : Branch p) :
    MeasurableEmbedding (coverAction N p hp hpN j) := by
  change MeasurableEmbedding (fun z : ℍ =>
    SpecialLinearGroup.mapGL ℝ (coverRepresentative N p hp hpN j : SL(2, ℤ)) • z)
  exact measurableEmbedding_const_smul _

theorem correspondenceCarrier_measurable (N p : ℕ) [NeZero N] (hp : p.Prime) (hpN : ¬ p ∣ N) :
    MeasurableSet (correspondenceCarrier N p hp hpN) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  exact MeasurableSet.iUnion (coverCell_measurable N p hp hpN)

/-- True finite-cell nonnegative integral, proved from actual disjoint
cells and canonical-volume-preserving original matrix actions. -/
theorem correspondenceCarrier_lintegral (N p : ℕ) [NeZero N] (hp : p.Prime) (hpN : ¬ p ∣ N)
    (f : ℍ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z in correspondenceCarrier N p hp hpN, f z) =
      letI : NeZero p := ⟨hp.ne_zero⟩
      ∫⁻ z in reducedCarrier N, ∑ j : Branch p, f (coverAction N p hp hpN j z) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [correspondenceCarrier, lintegral_iUnion (coverCell_measurable N p hp hpN)
    (fun j k hjk => coverCell_disjoint N p hp hpN hjk) f, tsum_fintype]
  have hcell (j : Branch p) : (∫⁻ z in coverCell N p hp hpN j, f z) =
      ∫⁻ z in reducedCarrier N, f (coverAction N p hp hpN j z) :=
    ((coverAction_measurePreserving N p hp hpN j).setLIntegral_comp_emb
      (coverAction_measurableEmbedding N p hp hpN j) f (reducedCarrier N)).symm
  simp_rw [hcell]
  exact (lintegral_finsetSum Finset.univ (fun j hj =>
    hf.comp (coverAction_measurableEmbedding N p hp hpN j).measurable)).symm

end
end ImbalancedChen.Part3.ActualHeckeCorrespondenceCarrier20261026b
