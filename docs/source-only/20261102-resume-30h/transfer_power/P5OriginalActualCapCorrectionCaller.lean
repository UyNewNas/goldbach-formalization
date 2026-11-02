import ImbalancedChen.P5OriginalActualCapCorrectionSource
import ImbalancedChen.P5OriginalDescending33PrimeCaller
import ImbalancedChen.P5OriginalFifthArchiveFallbackSeparation

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The catalog13 actual_cap source is read on the independently defined
target-deleted prime carrier, using G's literal six-prime/history map.
The current all11 constructor has no active sixth supplier there; its
actual fifth parent equals the original fifth parent since x<mu. These
facts rule out an above-mu fallback explanation, but DO NOT identify the
finite original fifth parent with R0 or add the missing final mask34 rule.

The exact source density identity is transported to those same tuples.
It gives neither prime nonemptiness nor the archived numerical integral.
-/
namespace ImbalancedChen.P5Z.OriginalActualCapCorrectionCaller
noncomputable section
open Classical
open scoped BigOperators
open Certificates.P2OriginalSixthElevenLogSemantics
open P5OriginalCommonRefinedConstructor
open P5OriginalCommonRefinedSeedHull
open P5OriginalFifthArchiveFallbackSeparation
open OriginalActualCapCorrectionSource
open OriginalDescending33PrimeCaller

def correctionTuples (c : Chart) (N : ℕ) : Finset (Fin 6 → ℕ) :=
  (actualPrimeBoxTuples N (fun _ : Fin 6 => (0 : ℝ)) (fun _ => (19/96 : ℝ))).filter
    (fun p => Source c (actualPrimeTupleLog N p))

theorem correctionTuple_prime_target_deleted (c : Chart) (N : ℕ)
    {p : Fin 6 → ℕ} (hp : p ∈ correctionTuples c N) :
    ∀ i, Nat.Prime (p i) ∧ ¬p i ∣ N := by
  have h := mem_actualPrimeBoxTuples_iff.mp (Finset.mem_filter.mp hp).1
  exact fun i => ⟨(h i).1,(h i).2.1⟩

theorem correctionTuples_disjoint_descending33 (c : Chart)
    (pattern : OriginalDescending33ActualOmission.Pattern) (N : ℕ) :
    Disjoint (correctionTuples c N) (descendingTuples pattern N) := by
  apply Finset.disjoint_left.mpr
  intro p hp hd
  exact (Finset.mem_filter.mp hp).2.not_descending33_source pattern
    (Finset.mem_filter.mp hd).2

theorem correctionTuples_disjoint_all11 (c : Chart) (N : ℕ) (cell : Cell) :
    Disjoint (correctionTuples c N)
      (P2OriginalSixthCompactArithmeticFibre.originalTuples cell N) := by
  apply Finset.disjoint_left.mpr
  intro p hp hc
  exact (Finset.mem_filter.mp hp).2.no_all11_supplier cell (Finset.mem_filter.mp hc).2

/-- Actual current constructor equality, with no assumption about an
unknown future full22 constructor or about the fifth cap being R0. -/
theorem current_sixth_eq_parent_on_original_correction
    (d : OriginalData) (N : ℝ) (pre : List ℕ) (c : Chart)
    (h : Source c (primeHistoryLogCoordinates N 6 pre)) :
    lambda6 d N pre = actualParent5 d N pre := by
  apply lambda6_eq_parent_of_no_eligible
  intro cell hc he
  exact h.no_all11_supplier cell he.2.1

/-- The actual same-source parent is unchanged by both above-mu fallbacks.
This is an original-source equality, not a chosen OriginalData flag. -/
theorem actual_parent_eq_original_fifth_on_correction
    (d : OriginalData) (N : ℝ) (pre : List ℕ) (hlen : pre.length = 6) (c : Chart)
    (h : Source c (primeHistoryLogCoordinates N 6 pre)) :
    actualParent5 d N pre = oldFifth d N (rosserAncestor 5 pre) := by
  have h5len : (rosserAncestor 5 pre).length = 5 := by
    rw [rosserAncestor_length,hlen]
    decide
  have hx : primeHistoryLogCoordinates N 5 (rosserAncestor 5 pre) 0 ≤ VariableEnvelope.mu := by
    rw [primeHistoryLogCoordinates_ancestor N hlen (by decide : 5 ≤ 6) (0 : Fin 5)]
    exact h.largest.le
  exact fifth_eq_old_below_mu d N (rosserAncestor 5 pre) h5len hx

theorem actual_tuple_current_sixth_eq_original_fifth
    (d : OriginalData) (c : Chart) (N : ℕ) {p : Fin 6 → ℕ}
    (hp : p ∈ correctionTuples c N) :
    lambda6 d (N : ℝ) (sourceHistory p) =
      oldFifth d (N : ℝ) (rosserAncestor 5 (sourceHistory p)) := by
  have hs : Source c (primeHistoryLogCoordinates (N : ℝ) 6 (sourceHistory p)) := by
    rw [sourceHistory_log]
    exact (Finset.mem_filter.mp hp).2
  rw [current_sixth_eq_parent_on_original_correction d _ _ c hs]
  exact actual_parent_eq_original_fifth_on_correction d _ _ (sourceHistory_length p) c hs

/-- The complete local #9/#10 plus #13 source identity on the actual
arithmetic tuple dictionary; the coordinate density stays six-dimensional. -/
theorem actual_tuple_full_source_density_identity (c : Chart) (N : ℕ)
    {p : Fin 6 → ℕ} (hp : p ∈ correctionTuples c N) :
    fullEndpointKernel c (primeHistoryLogCoordinates (N : ℝ) 6 (sourceHistory p)) =
      comparisonKernel c (actualPrimeTupleLog N p)+correctionKernel (actualPrimeTupleLog N p) := by
  rw [sourceHistory_log]
  exact (Finset.mem_filter.mp hp).2.full_source_density_identity

/-- An identity of finite original-source sums, valid with any same-source
weight. No positivity, distribution or limiting density is postulated. -/
theorem original_correction_source_sum_identity (c : Chart) (N : ℕ)
    (weight : (Fin 6 → ℕ) → ℝ) :
    (∑ p ∈ correctionTuples c N, weight p*fullEndpointKernel c (actualPrimeTupleLog N p)) =
      (∑ p ∈ correctionTuples c N, weight p*comparisonKernel c (actualPrimeTupleLog N p))+
        ∑ p ∈ correctionTuples c N, weight p*correctionKernel (actualPrimeTupleLog N p) := by
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [(Finset.mem_filter.mp hp).2.full_source_density_identity,mul_add]

end
end ImbalancedChen.P5Z.OriginalActualCapCorrectionCaller
