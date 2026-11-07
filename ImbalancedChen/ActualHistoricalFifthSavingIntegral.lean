import ImbalancedChen.ActualHistoricalFifthCellIntegral

/-!
# Integral of the actual inherited fourth-to-fifth saving

The literal nested candidate sum is identified with the already defined
tuple correction on the same third-capped parent.  The new fifth level
and the old effective fourth ancestor each retain their own strict
own-cube indicator, literal natural product and quotient level.

The finite dictionaries need only the recorded history length.  They do
not discard target divisors, impose a new candidate gate, or assume an
analytic limit.  Finite level checks then identify this saving with the
actual fourth-to-fifth policy density difference.  The common-cell
integral supplies its limit for fixed data and a covering enumeration cap.
The full upper density and the manuscript's adopted certificate instance
remain separate obligations.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped Classical BigOperators

namespace HistoricalPrefixCapData

/-- The actual new residual reads the same complete fifth history as the
tuple's fifth exponent.  No positivity or admission premise is needed. -/
theorem level5_ownCube_normalized_history (D : HistoricalPrefixCapData)
    (N cap : ℕ) {history : List ℕ} (hlen : history.length = 5) :
    actualOwnCubeGatedMinusDensity N cap (D.level5 (N : ℝ)) history *
        Real.log (N : ℝ) / singularSeries N =
      actualPrimeTupleOwnCubeMinus N cap
        (D.exponent5 (actualPrimeTupleLog N (primeHistoryTuple 5 history)) : ℝ)
        (primeHistoryTuple 5 history) := by
  rw [actualPrimeTupleOwnCubeMinus_primeHistoryTuple N cap _ (k := 4) hlen]
  simp only [actualOwnCubeGatedMinusDensity, level5,
    primeHistoryLogCoordinates_eq_actualPrimeTupleLog]
  rfl

/-- The old residual uses the effective fourth ancestor, including its
third-level fallback.  Its own-cube indicator is normalized separately. -/
theorem level4_ancestor_ownCube_normalized_history (D : HistoricalPrefixCapData)
    (N cap : ℕ) {history : List ℕ} (hlen : history.length = 5) :
    actualOwnCubeGatedMinusDensity N cap
        (fun pre => D.level4 (N : ℝ) (rosserAncestor 4 pre)) history *
        Real.log (N : ℝ) / singularSeries N =
      actualPrimeTupleOwnCubeMinus N cap
        (D.exponent4 (historicalPrefixProject (by omega : 4 ≤ 5)
          (actualPrimeTupleLog N (primeHistoryTuple 5 history))) : ℝ)
        (primeHistoryTuple 5 history) := by
  have hcoords : primeHistoryLogCoordinates (N : ℝ) 4 (rosserAncestor 4 history) =
      historicalPrefixProject (by omega : 4 ≤ 5)
        (actualPrimeTupleLog N (primeHistoryTuple 5 history)) := by
    rw [primeHistoryLogCoordinates_eq_historicalPrefixProject
      (N : ℝ) (by omega : 4 ≤ 5) hlen,
      primeHistoryLogCoordinates_eq_actualPrimeTupleLog]
  rw [actualPrimeTupleOwnCubeMinus_primeHistoryTuple N cap _ (k := 4) hlen]
  simp only [actualOwnCubeGatedMinusDensity, level4, hcoords]

/-- The same finite history dictionaries normalize and reindex the
literal nested saving at an arbitrary outer rough-prime cutoff. -/
theorem actualHistoricalFifthSaving_eq_tupleSum_at_cutoff
    (D : HistoricalPrefixCapData) (N cap : ℕ) (z : ℝ) :
    actualHistoricalFifthSaving
        (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
        (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) (D.level5 (N : ℝ)) N cap z *
        Real.log (N : ℝ) / singularSeries N =
      ∑ p ∈ firstExitFrontierTuples 4 (D.upperThirdPolicy (N : ℝ))
        (roughPrimeUniverse N cap 0 z),
        (∏ i, 1 / ((p i : ℝ) - 1)) * D.fifthTupleOwnCubeDifference N cap p := by
  let base := ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ))
  let parent := D.upperThirdPolicy (N : ℝ)
  let h (q : ℕ) := 1 / ((q : ℝ) - 1)
  let states := firstExitDepthFrontier 4 parent h [] true 1 (roughPrimeUniverse N cap 0 z)
  let candidates (s : FirstExitDepthState ℕ) :=
    firstExitNextSelectionCandidates h s.selectedPrefix s.positive s.mass s.remaining
  let residual (history : List ℕ) :=
    actualOwnCubeGatedMinusDensity N cap (D.level5 (N : ℝ)) history -
      actualOwnCubeGatedMinusDensity N cap
        (fun pre => D.level4 (N : ℝ) (rosserAncestor 4 pre)) history
  let f (p : Fin 5 → ℕ) := D.fifthTupleOwnCubeDifference N cap p
  have hn : actualHistoricalFifthSaving base
      (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) (D.level5 (N : ℝ)) N cap z *
      Real.log (N : ℝ) / singularSeries N =
      (states.map (fun s => ((candidates s).map (fun c =>
        (c.selectedPrefix.map h).prod * residual c.selectedPrefix *
          (Real.log (N : ℝ) / singularSeries N))).sum)).sum := by
    simp only [List.sum_map_mul_right]
    change _ * Real.log (N : ℝ) / singularSeries N =
      actualHistoricalFifthSaving base
        (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) (D.level5 (N : ℝ)) N cap z *
          (Real.log (N : ℝ) / singularSeries N)
    ring
  rw [hn]
  have heq : (states.map (fun s => ((candidates s).map (fun c =>
        (c.selectedPrefix.map h).prod * residual c.selectedPrefix *
          (Real.log (N : ℝ) / singularSeries N))).sum)).sum =
      (states.map (fun s => ((candidates s).map (fun c =>
        (c.selectedPrefix.map h).prod *
          f (primeHistoryTuple 5 c.selectedPrefix))).sum)).sum := by
    congr 1
    apply List.map_congr_left
    intro s hs
    congr 1
    apply List.map_congr_left
    intro c hc
    have hlen := (actualPrimeNextSelection_geometry 4 parent N cap z s hs c hc).1
    have hnew := D.level5_ownCube_normalized_history N cap hlen
    have hold := D.level4_ancestor_ownCube_normalized_history N cap hlen
    dsimp [f, fifthTupleOwnCubeDifference]
    rw [← hnew, ← hold]
    dsimp [residual]
    ring
  rw [heq]
  exact actualPrimeFrontier_candidates_weighted_sum_eq_tuple_sum 4 parent h N cap 0 z f

/-- Exact normalization and reindexing of the literal historical saving.
All next candidates occur, even when the old fifth own cube rejects them.
The original reciprocal-prime product mass is unchanged. -/
theorem actualHistoricalFifthSaving_eq_fifthPrimeCorrection
    (D : HistoricalPrefixCapData) (N cap : ℕ) :
    actualHistoricalFifthSaving
        (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
        (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) (D.level5 (N : ℝ))
        N cap ((N : ℝ) ^ (D.b : ℝ)) *
        Real.log (N : ℝ) / singularSeries N =
      D.fifthPrimeCorrection N cap := by
  simpa only [fifthPrimeCorrection] using
    D.actualHistoricalFifthSaving_eq_tupleSum_at_cutoff N cap ((N : ℝ) ^ (D.b : ℝ))

/-- The complete nested saving has the common-cell real integral limit.
Only eventual enumeration-cap coverage is supplied by the caller. -/
theorem tendsto_actualHistoricalFifthSaving (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (hold : 0 < D.old)
    (hcheck : D.levelCheck = true) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      actualHistoricalFifthSaving
          (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
          (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) (D.level5 (N : ℝ))
          N (cap N) ((N : ℝ) ^ (D.b : ℝ)) *
          Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 D.fifthCorrectionIntegral) := by
  apply (D.tendsto_fifthPrimeCorrection ha hab hold hcheck cap hcap).congr'
  exact Eventually.of_forall (fun N =>
    (D.actualHistoricalFifthSaving_eq_fifthPrimeCorrection N (cap N)).symm)

/-- The actual ceiling covers the strict prime cutoff and closes the
enumeration premise for the complete normalized nested saving. -/
theorem tendsto_actualHistoricalFifthSaving_ceil (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (hold : 0 < D.old)
    (hcheck : D.levelCheck = true) :
    Tendsto (fun N : ℕ =>
      actualHistoricalFifthSaving
          (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
          (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) (D.level5 (N : ℝ))
          N (Nat.ceil ((N : ℝ) ^ (D.b : ℝ))) ((N : ℝ) ^ (D.b : ℝ)) *
          Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 D.fifthCorrectionIntegral) :=
  D.tendsto_actualHistoricalFifthSaving ha hab hold hcheck _
    (Eventually.of_forall (fun N => Nat.le_ceil ((N : ℝ) ^ (D.b : ℝ))))

/-- The finite checker supplies both inherited comparisons required by
the actual fourth-to-fifth density identity, on its original parent. -/
theorem upperFourthToFifthSaving_eq (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (hcheck : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < (N : ℝ)) (z : ℝ) :
    firstExitRetainedPolynomial (D.upperFourthPolicy (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) -
      firstExitRetainedPolynomial (D.upperFifthPolicy (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) =
      actualHistoricalFifthSaving
        (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
        (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) (D.level5 (N : ℝ)) N cap z := by
  apply actualHistoricalFifthSaving_eq
  · intro state hstate
    apply D.level3_ancestor_le_level4 hab hcheck (N : ℝ) hN
    exact firstExitDepthFrontier_selected_length 4 _ _ [] _ true 1 (by simp) state hstate
  · intro frontier hfrontier candidate hcandidate
    have hlen := firstExitDepthFrontier_selected_length 4
      (D.upperThirdPolicy (N : ℝ)) (fun p : ℕ => 1 / ((p : ℝ) - 1))
      [] (roughPrimeUniverse N cap 0 z) true 1 (by simp) frontier hfrontier
    obtain ⟨_before, q, _after, _hremaining, rfl⟩ :=
      (mem_firstExitNextSelectionCandidates_iff _ _ _ _ _ candidate).mp hcandidate
    have hnext : (q :: frontier.selectedPrefix).length = 5 := by
      simp only [List.length_cons, hlen]
    have hh := D.level4_ancestor_le_level5 hab hcheck (N : ℝ) hN
      (q :: frontier.selectedPrefix) hnext
    rw [rosserAncestor_cons 4 q frontier.selectedPrefix (by omega),
      rosserAncestor_self_of_length 4 frontier.selectedPrefix hlen] at hh
    exact hh

/-- The normalized actual fourth-to-fifth density difference is the
same complete tuple correction, before any limiting argument. -/
theorem upperFourthToFifthSaving_normalized_eq_fifthPrimeCorrection
    (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (hcheck : D.levelCheck = true) (N cap : ℕ) (hN : 1 < (N : ℝ)) :
    (firstExitRetainedPolynomial (D.upperFourthPolicy (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
        (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ))) -
      firstExitRetainedPolynomial (D.upperFifthPolicy (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
        (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ)))) *
      Real.log (N : ℝ) / singularSeries N = D.fifthPrimeCorrection N cap := by
  rw [D.upperFourthToFifthSaving_eq hab hcheck N cap hN,
    D.actualHistoricalFifthSaving_eq_fifthPrimeCorrection]

/-- The actual fourth-policy density minus the actual fifth-policy
density converges to the finite common-cell integral.  No limit of either
individual full density is assumed or asserted. -/
theorem tendsto_upperFourthToFifthSaving (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (hold : 0 < D.old)
    (hcheck : D.levelCheck = true) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      (firstExitRetainedPolynomial (D.upperFourthPolicy (N : ℝ))
          (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
          (roughPrimeUniverse N (cap N) 0 ((N : ℝ) ^ (D.b : ℝ))) -
        firstExitRetainedPolynomial (D.upperFifthPolicy (N : ℝ))
          (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
          (roughPrimeUniverse N (cap N) 0 ((N : ℝ) ^ (D.b : ℝ)))) *
        Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 D.fifthCorrectionIntegral) := by
  apply (D.tendsto_fifthPrimeCorrection ha hab hold hcheck cap hcap).congr'
  have hlarge : ∀ᶠ N : ℕ in
      atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}, 1 < N :=
    (eventually_gt_atTop 1).filter_mono inf_le_left
  filter_upwards [hlarge] with N hN
  exact (D.upperFourthToFifthSaving_normalized_eq_fifthPrimeCorrection
    hab.le hcheck N (cap N) (by exact_mod_cast hN)).symm

/-- Ceiling specialization for the actual normalized fourth-to-fifth
policy density difference on the target-deleted prime carrier. -/
theorem tendsto_upperFourthToFifthSaving_ceil (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (hold : 0 < D.old)
    (hcheck : D.levelCheck = true) :
    Tendsto (fun N : ℕ =>
      (firstExitRetainedPolynomial (D.upperFourthPolicy (N : ℝ))
          (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
          (roughPrimeUniverse N (Nat.ceil ((N : ℝ) ^ (D.b : ℝ))) 0
            ((N : ℝ) ^ (D.b : ℝ))) -
        firstExitRetainedPolynomial (D.upperFifthPolicy (N : ℝ))
          (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
          (roughPrimeUniverse N (Nat.ceil ((N : ℝ) ^ (D.b : ℝ))) 0
            ((N : ℝ) ^ (D.b : ℝ)))) *
        Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 D.fifthCorrectionIntegral) :=
  D.tendsto_upperFourthToFifthSaving ha hab hold hcheck _
    (Eventually.of_forall (fun N => Nat.le_ceil ((N : ℝ) ^ (D.b : ℝ))))

end HistoricalPrefixCapData

end

end ImbalancedChen
