import ImbalancedChen.ActualPrimeOwnCubeAffineIntegral
import ImbalancedChen.OrdinaryUpperFiveAffineGates
import ImbalancedChen.OrdinaryPrimeFrontierAffineRegion
import ImbalancedChen.ActualOwnCubeTupleDictionary

/-!
# A genuine ordinary-parent fifth-candidate integral

The left side is a sum over the literal rank-four ordinary parent frontier
and all its next candidates. A fixed positive logarithmic cube localizes
the selected primes; both old and new own-cube gates remain. The finite
reindexing and the inherited parent tests are proved, so no region-identity
or integral-limit premise is required.

This is a localized ordinary-parent result. It does not identify a causal
multi-stage selected-cap policy, evaluate numerical certificates, or prove
the physical signed progression remainder.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology MeasureTheory
open scoped Classical BigOperators

/-- Actual history densities on every candidate of the ordinary parent,
localized to the selected-prime cube. The candidate's own gate is inside
the density; it is not used to enumerate the parent frontier. -/
def actualOrdinaryUpperFiveCubeResidual (N cap : ℕ) (a b old lambda : ℝ) : ℝ :=
  ((firstExitFrontierCandidates 4 (ordinaryParityRosserPolicy false ((N : ℝ) ^ old))
    (fun q : ℕ => 1 / ((q : ℝ) - 1)) (roughPrimeUniverse N cap 0 ((N : ℝ) ^ b))).map
    (fun candidate =>
      (candidate.selectedPrefix.map (fun q : ℕ => 1 / ((q : ℝ) - 1))).prod *
        (if primeHistoryTuple 5 candidate.selectedPrefix ∈
            actualPrimeBoxTuples N (fun _ : Fin 5 => a) (fun _ => b) then
          actualOwnCubeGatedMinusDensity N cap (fun _ => (N : ℝ) ^ lambda)
            candidate.selectedPrefix * Real.log (N : ℝ) / singularSeries N
        else 0))).sum

/-- Exact equality of the actual candidate cube and the six-row affine
region. In particular, the old fifth-cube test is absent. -/
theorem ordinaryUpperFiveFrontierTuples_cube_filter
    (N cap : ℕ) (a b old : ℝ) (hN : 1 < N) (hold : 0 < old)
    (hcap : (N : ℝ) ^ b ≤ (cap : ℝ)) :
    (firstExitFrontierTuples 4 (ordinaryParityRosserPolicy false ((N : ℝ) ^ old))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ b))).filter
        (fun p => p ∈ actualPrimeBoxTuples N (fun _ : Fin 5 => a) (fun _ => b)) =
      (actualPrimeBoxTuples N (fun _ : Fin 5 => a) (fun _ => b)).filter
        (fun p => actualPrimeTupleLog N p ∈
          primeAffineGateRegion ordinaryUpperFiveGateForms (ordinaryUpperFiveGateBounds old)) := by
  ext p
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hf, hp⟩
    have hh := (mem_ordinaryUpperFiveFrontierTuples_iff_log N cap old 0 _ hN hold hcap p).mp hf
    refine ⟨hp, (mem_ordinaryUpperFiveGateRegion old _).mpr ⟨?_, hh.2.2⟩⟩
    exact (actualPrimeTupleLog_strictAnti_iff hN p (fun i => (hh.2.1 i).1.pos)).mpr hh.1
  · rintro ⟨hp, hg⟩
    have hpi := mem_actualPrimeBoxTuples_iff.mp hp
    have hh := (mem_ordinaryUpperFiveGateRegion old _).mp hg
    refine ⟨(mem_ordinaryUpperFiveFrontierTuples_iff_log N cap old 0 _ hN hold hcap p).mpr
      ⟨?_, ?_, hh.2⟩, hp⟩
    · exact (actualPrimeTupleLog_strictAnti_iff hN p (fun i => (hpi i).1.pos)).mp hh.1
    · exact fun i => ⟨(hpi i).1, (hpi i).2.1, Nat.cast_nonneg _, (hpi i).2.2.2⟩

/-- The original history-density sum is exactly the previously integrated
actual tuple density on the proved parent region. -/
theorem actualOrdinaryUpperFiveCubeResidual_eq_tuple_sum
    (N cap : ℕ) (a b old lambda : ℝ) (hN : 1 < N) (hold : 0 < old)
    (hcap : (N : ℝ) ^ b ≤ (cap : ℝ)) :
    actualOrdinaryUpperFiveCubeResidual N cap a b old lambda =
      actualPrimeBoxOwnCubeMinusSum 4 N cap a b lambda
        (primeAffineGateRegion ordinaryUpperFiveGateForms (ordinaryUpperFiveGateBounds old)) := by
  let parent := ordinaryParityRosserPolicy false ((N : ℝ) ^ old)
  let h (q : ℕ) := 1 / ((q : ℝ) - 1)
  let carrier := roughPrimeUniverse N cap 0 ((N : ℝ) ^ b)
  let B := actualPrimeBoxTuples N (fun _ : Fin 5 => a) (fun _ => b)
  have hrewrite : actualOrdinaryUpperFiveCubeResidual N cap a b old lambda =
      ((firstExitFrontierCandidates 4 parent h carrier).map (fun candidate =>
        (candidate.selectedPrefix.map h).prod *
          (if primeHistoryTuple 5 candidate.selectedPrefix ∈ B then
            actualPrimeTupleOwnCubeMinus N cap lambda (primeHistoryTuple 5 candidate.selectedPrefix)
            else 0))).sum := by
    unfold actualOrdinaryUpperFiveCubeResidual
    congr 1
    apply List.map_congr_left
    intro candidate hc
    have hlen := firstExitFrontierCandidates_selected_length 4 parent h carrier candidate hc
    rw [actualPrimeTupleOwnCubeMinus_primeHistoryTuple N cap lambda hlen]
  rw [hrewrite, firstExitFrontierCandidates_weighted_sum_eq_tuple_sum 4 parent h carrier
    (roughPrimeUniverse_nodup N cap 0 ((N : ℝ) ^ b))
    (fun p => if p ∈ B then actualPrimeTupleOwnCubeMinus N cap lambda p else 0)]
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  rw [show (firstExitFrontierTuples 4 parent carrier).filter (fun p => p ∈ B) =
      B.filter (fun p => actualPrimeTupleLog N p ∈
        primeAffineGateRegion ordinaryUpperFiveGateForms (ordinaryUpperFiveGateBounds old)) from
      ordinaryUpperFiveFrontierTuples_cube_filter N cap a b old hN hold hcap,
    Finset.sum_filter]
  simp only [actualPrimeBoxOwnCubeMinusSum, B, mul_ite, mul_zero]

/-- The actual ordinary-parent localized residual has the true affine
region integral as its limit along positive even targets. -/
theorem tendsto_actualOrdinaryUpperFiveCubeResidual
    (a b old lambda : ℝ) (ha : 0 < a) (hab : a < b) (hold : 0 < old)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ b ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => actualOrdinaryUpperFiveCubeResidual N (cap N) a b old lambda)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (primeOwnCubeAffineIntegral a b lambda ordinaryUpperFiveGateForms
        (ordinaryUpperFiveGateBounds old))) := by
  apply (tendsto_actualPrimeBoxOwnCubeMinusSum_affineGates 4 a b lambda ha hab
    ordinaryUpperFiveGateForms (ordinaryUpperFiveGateBounds old)
    ordinaryUpperFiveGateForms_ne_zero cap hcap).congr'
  have hlarge : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}, 1 < N :=
    (eventually_gt_atTop 1).filter_mono inf_le_left
  filter_upwards [hlarge, hcap] with N hN hc
  exact (actualOrdinaryUpperFiveCubeResidual_eq_tuple_sum N (cap N) a b old lambda hN hold hc).symm

/-- A real fifth-own-cube saving, with the two actual history gates
retained separately, converges to the difference of their true integrals. -/
theorem tendsto_actualOrdinaryUpperFiveCubeSaving
    (a b old lambdaNew : ℝ) (ha : 0 < a) (hab : a < b) (hold : 0 < old)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ b ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      actualOrdinaryUpperFiveCubeResidual N (cap N) a b old lambdaNew -
        actualOrdinaryUpperFiveCubeResidual N (cap N) a b old old)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (primeOwnCubeAffineIntegral a b lambdaNew ordinaryUpperFiveGateForms
          (ordinaryUpperFiveGateBounds old) -
        primeOwnCubeAffineIntegral a b old ordinaryUpperFiveGateForms
          (ordinaryUpperFiveGateBounds old))) := by
  exact (tendsto_actualOrdinaryUpperFiveCubeResidual a b old lambdaNew ha hab hold cap hcap).sub
    (tendsto_actualOrdinaryUpperFiveCubeResidual a b old old ha hab hold cap hcap)

end

end ImbalancedChen
