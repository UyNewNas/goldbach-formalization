import ImbalancedChen.P2Saving16WeightedCompilerLedger
import ImbalancedChen.P2Saving16ThirdRowFourthParent

/-! SOURCE_ONLY / UNCOMPILED / UNEVALUATED.
Literal positive-outer and negative-inner occurrences, with their original
full-modulus weights, inside the existing same-Q compiler correction. This
does not identify geometric corners or add a distribution estimate. -/
namespace ImbalancedChen.P2Saving16SignedCorrectionFamilies
noncomputable section
open scoped Classical BigOperators
open P4AUpperTaggedParityCompiler P4AUpperTaggedBetaAttachment
open P2Saving16ActualCompilerDifference P2Saving16WeightedCompilerLedger
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87OrdinarySignedGain (HistoryOnTrim)
open P4AOriginalR17EighthParent (orderedSixth)
open P4AOriginalFull87UnionHistory (sixthPolicy policy)
open P4AOriginalOrderedThirdActualCoefficient (coefficient keep)
open P4AOriginalFull87RawChronology (cutoff)
open P4AOriginalFull87CompiledCounting (moduli)

/-- The two indicator families are disjoint by their actual rough
Möbius sign; the full-modulus weight remains inside each summand. -/
def positiveOuterSum (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau L : ℝ) (G : ℕ → ℝ) : ℝ :=
  ∑ x ∈ smallRoughPairs (actualSmallRosserSupport N cap w) (universe N cap w z),
    (if 0 ≤ (ArithmeticFunction.moebius x.2 : ℝ) ∧
        outer ret tag N cap w z tau x.2 ∧ x.2 ∉ rawSupport ret N cap w z then
      actualSmallRosserPlus N cap w L x.1 else 0) * G (x.1*x.2)

def negativeInnerSum (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau L : ℝ) (G : ℕ → ℝ) : ℝ :=
  ∑ x ∈ smallRoughPairs (actualSmallRosserSupport N cap w) (universe N cap w z),
    (if (ArithmeticFunction.moebius x.2 : ℝ) < 0 ∧
        x.2 ∈ rawSupport ret N cap w z ∧ ¬inner ret tag N cap w z tau x.2 then
      actualSmallRosserMinus N cap w L x.1 else 0) * G (x.1*x.2)

/-- Exact separation of the existing correction; both terms use the same
ordered pair carrier, same test and unchanged beta-plus/minus coefficients. -/
theorem correctionSum_eq_two_families (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau L : ℝ) (G : ℕ → ℝ) :
    correctionSum ret tag N cap w z tau L G =
      positiveOuterSum ret tag N cap w z tau L G +
        negativeInnerSum ret tag N cap w z tau L G := by
  classical
  unfold correctionSum positiveOuterSum negativeInnerSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hs : 0 ≤ (ArithmeticFunction.moebius x.2 : ℝ)
  · simp only [changed, if_pos hs, hs, true_and, not_lt_of_ge hs, false_and, if_false, zero_mul, add_zero]
  · have hn : (ArithmeticFunction.moebius x.2 : ℝ) < 0 := lt_of_not_ge hs
    simp only [changed, if_neg hs, hs, false_and, hn, true_and, if_false, zero_mul, zero_add]

/-- A positive outer addition has a retained witness in this exact cell;
the target word itself is absent from the original retained support. -/
theorem positive_outer_actual_witness (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau : ℝ) {d : ℕ}
    (hs : 0 ≤ (ArithmeticFunction.moebius d : ℝ))
    (hc : changed ret tag N cap w z tau d) :
    d ∉ rawSupport ret N cap w z ∧
      ∃ v ∈ cell tag N cap w z tau d, v ∈ rawSupport ret N cap w z := by
  have h : outer ret tag N cap w z tau d ∧ d ∉ rawSupport ret N cap w z := by
    simpa only [changed, if_pos hs] using hc
  obtain ⟨v, hv⟩ := h.1
  exact ⟨h.2, v, (Finset.mem_inter.mp hv).1, (Finset.mem_inter.mp hv).2⟩

/-- A negative inner deletion has the original retained word and an
unretained witness in its exact cell. -/
theorem negative_inner_actual_witness (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau : ℝ) {d : ℕ}
    (hs : (ArithmeticFunction.moebius d : ℝ) < 0)
    (hc : changed ret tag N cap w z tau d) :
    d ∈ rawSupport ret N cap w z ∧
      ∃ v ∈ cell tag N cap w z tau d, v ∉ rawSupport ret N cap w z := by
  classical
  have hn : ¬ 0 ≤ (ArithmeticFunction.moebius d : ℝ) := not_le_of_gt hs
  have h : d ∈ rawSupport ret N cap w z ∧ ¬ inner ret tag N cap w z tau d := by
    simpa only [changed, if_neg hn] using hc
  refine ⟨h.1, ?_⟩
  by_contra hnone
  apply h.2
  intro v hv
  by_contra hnmem
  exact hnone ⟨v, hv, hnmem⟩

/-- Retained witnesses are literal ordered first-exit leaves for the
same policy, not merely elements of an unweighted geometric set. -/
theorem raw_support_iff_ordered_leaf (ret : List ℕ → Bool)
    (N cap : ℕ) (w z : ℝ) (d : ℕ) :
    d ∈ rawSupport ret N cap w z ↔
      ∃ leaf ∈ oddFirstExitRetainedLeaves ret (fun _ => 1)
        (roughPrimeUniverse N cap w z), leaf.selected.prod = d := by
  exact mem_oddFirstExitRetainedModuli ret (fun _ => 1) (roughPrimeUniverse N cap w z) d

/-- For an outer addition the retained witness comes with its actual
ordered leaf and has the same label, tag and rank as the original word. -/
theorem positive_outer_ordered_leaf (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau : ℝ) {d : ℕ}
    (hs : 0 ≤ (ArithmeticFunction.moebius d : ℝ))
    (hc : changed ret tag N cap w z tau d) :
    d ∉ rawSupport ret N cap w z ∧
    ∃ v ∈ cell tag N cap w z tau d,
      v.primeFactorsList.length = d.primeFactorsList.length ∧ tag v = tag d ∧
      ∃ leaf ∈ oddFirstExitRetainedLeaves ret (fun _ => 1)
        (roughPrimeUniverse N cap w z), leaf.selected.prod = v := by
  obtain ⟨hnot, v, hv, hret⟩ := positive_outer_actual_witness ret tag N cap w z tau hs hc
  exact ⟨hnot, v, hv, cell_rank_preserved tag N cap w z tau hv,
    cell_frozen_tag tag N cap w z tau hv, (raw_support_iff_ordered_leaf ret N cap w z v).mp hret⟩

/-- For an inner deletion the deleted word itself has its original
ordered leaf; an opposite decision exists in its same tagged cell. -/
theorem negative_inner_ordered_leaf (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau : ℝ) {d : ℕ}
    (hs : (ArithmeticFunction.moebius d : ℝ) < 0)
    (hc : changed ret tag N cap w z tau d) :
    (∃ leaf ∈ oddFirstExitRetainedLeaves ret (fun _ => 1)
      (roughPrimeUniverse N cap w z), leaf.selected.prod = d) ∧
    ∃ v ∈ cell tag N cap w z tau d,
      v.primeFactorsList.length = d.primeFactorsList.length ∧ tag v = tag d ∧
      v ∉ rawSupport ret N cap w z := by
  obtain ⟨hret, v, hv, hnot⟩ := negative_inner_actual_witness ret tag N cap w z tau hs hc
  exact ⟨(raw_support_iff_ordered_leaf ret N cap w z d).mp hret, v, hv,
    cell_rank_preserved tag N cap w z tau hv, cell_frozen_tag tag N cap w z tau hv, hnot⟩

/-- The existing R17 full-Q equality with both signed families exposed.
There is exactly one occurrence on the original pair carrier for each
summand and no new reserve or independent sieve bound. -/
theorem r17_same_Q_two_family_ledger
    (r n : ℕ) (e : ℚ) (q : ℕ) (a nu beta tau : ℝ)
    (he : 0 ≤ e) (hcut : nu * beta ^ 2 ≤ a) (hh : HistoryOnTrim r e q a)
    (N : ℕ) (hN : 1 < (N : ℝ)) (G : ℕ → ℝ) :
    let omega := nu * beta ^ 2
    let w := (N : ℝ) ^ omega
    let z := cutoff N
    let L := (N : ℝ) ^ (nu * beta)
    let Q := moduli N w
    let f := keep r n e q a omega N
    (∑ m ∈ Q, coefficient r n e q a omega N tau L m * G m) =
      (∑ m ∈ Q, actualSmallRoughRho (orderedSixth n e q a omega N false) N N w z L m * G m) -
      (∑ m ∈ Q, (actualSmallRoughRho (sixthPolicy n e q a N false) N N w z L m -
        actualSmallRoughRho (policy (width r) n e q a N false) N N w z L m) * G m) +
      (positiveOuterSum f (fun _ => []) N N w z tau L G +
        negativeInnerSum f (fun _ => []) N N w z tau L G) := by
  have h := r17_same_Q_weighted_ledger r n e q a nu beta tau he hcut hh N hN G
  rw [correctionSum_eq_two_families] at h
  exact h


/-- The original compiler expense contains one absolute value of the
combined signed families, not two fresh reserve payments. -/
theorem compilerExpense_eq_one_signed_family_charge
    (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau L : ℝ) :
    P4AFiniteCapTaggedConstructor.compilerExpense ret tag N cap w z tau L =
      (p4aReservePhysicalDensity ret N cap w z L -
        actualSmallEulerProduct N cap w * p4aReserveRawDensity ret N cap w z) +
      |positiveOuterSum ret tag N cap w z tau L (fun m => 1 / (Nat.totient m : ℝ)) +
        negativeInnerSum ret tag N cap w z tau L (fun m => 1 / (Nat.totient m : ℝ))| := by
  rw [compilerExpense_eq_beta_add_correction, correctionSum_eq_two_families]

end
end ImbalancedChen.P2Saving16SignedCorrectionFamilies
