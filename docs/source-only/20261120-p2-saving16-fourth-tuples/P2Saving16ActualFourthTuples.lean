import ImbalancedChen.P2Saving16ActualFourthFrontier
import ImbalancedChen.FirstExitAdmittedFrontierTuples

/-! SOURCE_ONLY / UNCOMPILED / UNEVALUATED.
Reindex the actual compiler-policy fourth frontier by its admitted ordered
prime quadruples, preserving the entire signed full-modulus continuation.
This does not identify an original fourteen-cell geometric corner. -/
namespace ImbalancedChen.P2Saving16ActualFourthTuples
noncomputable section
open scoped Classical BigOperators
open P4AUpperTaggedParityCompiler P4AUpperTaggedBetaAttachment
open P2Saving16SignedCorrectionFamilies P2Saving16ActualFourthFrontier
open P1Pair12RetainedSignedSource
open P4AOriginalOrderedThirdActualCoefficient (coefficient keep)
open P4AOriginalFull87RawChronology (cutoff)
open P4AOriginalFull87CompiledCounting (moduli)

/-- The full physical continuation at an ordered fourth tuple. The
remainder is cut at its actual last selected prime; the signed beta and
G(b*d) stay within the existing terminal test. -/
def fourthTupleTerm (ret : List ℕ → Bool) (N cap : ℕ)
    (w z L : ℝ) (G : ℕ → ℝ) (p : Fin 4 → ℕ) : ℝ :=
  let pre := (List.ofFn p).reverse
  signedTest (oddFirstExitPolicy ret) (fun _ => 1)
    (attachedLeafTest N cap 1 w L G) pre true 1
    (roughPrimeUniverse N cap w (pre.getD 0 0 : ℝ))

/-- At the actual frontier its incoming sign is the positive rank-four
sign; the remaining carrier and original prefix are recovered literally. -/
theorem fourth_state_term_eq_tuple (ret : List ℕ → Bool) (N cap : ℕ)
    (w z L : ℝ) (G : ℕ → ℝ) (s : FirstExitDepthState ℕ)
    (hs : s ∈ firstExitDepthFrontier 4 (oddFirstExitPolicy ret) (fun _ : ℕ => 1)
      [] true 1 (roughPrimeUniverse N cap w z)) :
    signedTest (oddFirstExitPolicy ret) (fun _ => 1) (attachedLeafTest N cap 1 w L G)
        s.selectedPrefix s.positive s.mass s.remaining =
      fourthTupleTerm ret N cap w z L G (primeHistoryTuple 4 s.selectedPrefix) := by
  have hh := fourth_frontier_incoming_sign ret N cap w z s hs
  have hlen := hh.1
  have hmass := hh.2.1
  have hsign := hh.2.2.1
  have hpos : s.positive = true := by
    cases h : s.positive with
    | false => norm_num [h, hmass, signedTreeCoefficient] at hsign
    | true => rfl
  obtain ⟨p, tail, hp, _, hrem⟩ := mem_firstExitDepthFrontier_roughPrime_remaining
    4 (by decide) (oddFirstExitPolicy ret) (fun _ : ℕ => (1 : ℝ))
    N cap w z s hs
  unfold fourthTupleTerm
  rw [primeHistoryTuple_reverse_ofFn hlen, hpos, hmass, hrem, hp]
  rfl

/-- Each admitted tuple occurs once: the original frontier map is nodup,
not merely equal after forgetting multiplicity. -/
theorem fourth_tuple_occurrences_nodup (ret : List ℕ → Bool) (N cap : ℕ)
    (w z : ℝ) :
    ((firstExitDepthFrontier 4 (oddFirstExitPolicy ret) (fun _ : ℕ => 1)
      [] true 1 (roughPrimeUniverse N cap w z)).map
        (fun s => primeHistoryTuple 4 s.selectedPrefix)).Nodup :=
  firstExitRootFrontier_admitted_tuple_nodup 4 (oddFirstExitPolicy ret)
    (fun _ : ℕ => 1) (roughPrimeUniverse N cap w z) (roughPrimeUniverse_nodup N cap w z)

/-- Exact reindexing of the full signed physical source, retaining the
unmodified terminal weight, remaining carrier and one tuple occurrence. -/
theorem fourth_frontier_eq_ordered_tuple_sum (ret : List ℕ → Bool) (N cap : ℕ)
    (w z L : ℝ) (G : ℕ → ℝ) :
    fourthFrontierSource ret N cap w z L G =
      ∑ p ∈ firstExitAdmittedTuples 4 (oddFirstExitPolicy ret) (roughPrimeUniverse N cap w z),
        fourthTupleTerm ret N cap w z L G p := by
  have h := firstExitRootFrontier_sum_eq_admitted_tuple_sum 4 (oddFirstExitPolicy ret)
    (fun _ : ℕ => (1 : ℝ)) (roughPrimeUniverse N cap w z)
    (roughPrimeUniverse_nodup N cap w z) (fourthTupleTerm ret N cap w z L G)
  rw [← h]
  unfold fourthFrontierSource
  apply congrArg List.sum
  apply List.map_congr_left
  intro s hs
  exact fourth_state_term_eq_tuple ret N cap w z L G s hs

/-- Exact membership keeps strict order, positive-w inclusive lower bound,
strict cutoff, coprimality and original policy admission. -/
theorem fourth_tuple_membership (ret : List ℕ → Bool) (N cap : ℕ)
    (w z : ℝ) (hzcap : z ≤ (cap : ℝ)) (p : Fin 4 → ℕ) :
    p ∈ firstExitAdmittedTuples 4 (oddFirstExitPolicy ret) (roughPrimeUniverse N cap w z) ↔
      StrictAnti p ∧
        (∀ i, Nat.Prime (p i) ∧ ¬p i ∣ N ∧ w ≤ (p i : ℝ) ∧ (p i : ℝ) < z) ∧
        FirstExitValidSelection (oddFirstExitPolicy ret) [] true (List.ofFn p) :=
  mem_actualPrimeAdmittedTuples_iff_of_cutoff_le_cap 4
    (oddFirstExitPolicy ret) N cap w z hzcap p

/-- Same actual compiler coefficient and Q as before, now indexed by
actual ordered fourth tuples with their original complete continuations. -/
theorem r17_compiler_on_actual_ordered_fourths
    (r n : ℕ) (e : ℚ) (q : ℕ) (a nu beta tau : ℝ) (N : ℕ) (G : ℕ → ℝ) :
    let omega := nu * beta^2
    let w := (N : ℝ)^omega
    let z := cutoff N
    let L := (N : ℝ)^(nu*beta)
    let Q := moduli N w
    let f := keep r n e q a omega N
    (∑ m ∈ Q, coefficient r n e q a omega N tau L m * G m) =
      stoppedBeforeFour f N N w z L G +
        (∑ p ∈ firstExitAdmittedTuples 4 (oddFirstExitPolicy f) (roughPrimeUniverse N N w z),
          fourthTupleTerm f N N w z L G p) +
        (positiveOuterSum f (fun _ => []) N N w z tau L G +
          negativeInnerSum f (fun _ => []) N N w z tau L G) := by
  have h := r17_compiler_on_actual_fourth_frontier r n e q a nu beta tau N G
  rw [fourth_frontier_eq_ordered_tuple_sum] at h
  exact h

end
end ImbalancedChen.P2Saving16ActualFourthTuples
