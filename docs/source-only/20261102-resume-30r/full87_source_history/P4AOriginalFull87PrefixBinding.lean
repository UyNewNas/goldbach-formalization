import ImbalancedChen.P4AOriginalFull87SourceDictionary
import ImbalancedChen.PrimeHistoryLogCoordinates

/-!
SOURCE ONLY / UNCOMPILED. The original ideal third reads its own reversed
rank-three ancestor. The physical source squares below use the very tuple
of an actual prime frontier, including its original prime carrier and
target deletion. No finite approximation or new coefficient is defined.
-/
namespace ImbalancedChen.P4AOriginalFull87PrefixBinding
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87SourceDictionary

/-- The evaluator takes a third prefix; it reads no later coordinate. -/
def idealThirdPrefix (N : ℝ) (pre3 : List ℕ) : ℝ :=
  let t := primeHistoryLogCoordinates N 3 pre3
  actualExtendedThirdIdealCap (t 0) (t 1) (t 2)

theorem idealThirdPrefix_at_eighth_ancestor (N : ℝ) (pre : List ℕ)
    (hlen : pre.length = 8) :
    idealThirdPrefix N (rosserAncestor 3 pre) =
      let t := primeHistoryLogCoordinates N 8 pre
      actualExtendedThirdIdealCap (t 0) (t 1) (t 2) := by
  have h0 := primeHistoryLogCoordinates_ancestor N hlen (by decide : 3 ≤ 8) (0 : Fin 3)
  have h1 := primeHistoryLogCoordinates_ancestor N hlen (by decide : 3 ≤ 8) (1 : Fin 3)
  have h2 := primeHistoryLogCoordinates_ancestor N hlen (by decide : 3 ≤ 8) (2 : Fin 3)
  dsimp only [idealThirdPrefix]
  rw [h0,h1,h2]

theorem source_histories_at_own_third_prefix (N : ℝ) (pre : List ℕ)
    (hlen : pre.length = 8) (c : Cell)
    (hsource : Source c (primeHistoryLogCoordinates N 8 pre)) :
    ∀ j : Fin 4, P4AOriginalRemainingEighthSources.history
      (primeHistoryLogCoordinates N 8 pre) j < idealThirdPrefix N (rosserAncestor 3 pre) := by
  rw [idealThirdPrefix_at_eighth_ancestor N pre hlen]
  exact source_histories_original_ideal hsource

theorem source_ideal_at_own_third_prefix_le_comparison (N : ℝ) (pre : List ℕ)
    (hlen : pre.length = 8) (c : Cell)
    (hsource : Source c (primeHistoryLogCoordinates N 8 pre)) :
    idealThirdPrefix N (rosserAncestor 3 pre) ≤
      comparison c (primeHistoryLogCoordinates N 8 pre) := by
  rw [idealThirdPrefix_at_eighth_ancestor N pre hlen]
  exact source_original_ideal_le_comparison hsource

/-- Source membership and an actual frontier supply the full and selected
integer products at exactly the source cap. Coordinate domination is
derived from the original tuple, rather than supplied by a caller. -/
theorem source_frontier_integer_squares
    (parent : Bool → List ℕ → Bool) (weight : ℕ → ℝ)
    (N enumerationCap : ℕ) (hN : 1 < (N : ℝ)) (w z : ℝ)
    (state : FirstExitDepthState ℕ)
    (hfrontier : state ∈ firstExitDepthFrontier 8 parent weight [] true 1
      (roughPrimeUniverse N enumerationCap w z))
    (c : Cell) (hsource : Source c (primeHistoryLogCoordinates (N : ℝ) 8 state.selectedPrefix)) :
    let t := primeHistoryLogCoordinates (N : ℝ) 8 state.selectedPrefix
    let p := primeHistoryTuple 8 state.selectedPrefix
    (∀ j, ((∏ k ∈ Finset.univ.filter (fun k : Fin 8 => k < j), p k : ℕ) : ℝ) *
      (p j : ℝ)^2 < (N : ℝ)^newCap c t) ∧
    (∀ j ∉ selected c, ((∏ k ∈ selected c, p k : ℕ) : ℝ) *
      ((∏ k ∈ Finset.univ.filter (fun k : Fin 8 => k < j ∧ k ∉ selected c), p k : ℕ) : ℝ) *
      (p j : ℝ)^2 < (N : ℝ)^newCap c t) := by
  dsimp only
  have hcoords := primeHistoryLogCoordinates_frontier 8 parent weight
    N enumerationCap hN w z state hfrontier
  exact source_integer_squares hsource (N : ℝ) hN
    (primeHistoryTuple 8 state.selectedPrefix)
    (fun j => (hcoords.2 j).2.symm.le)

end
end ImbalancedChen.P4AOriginalFull87PrefixBinding
