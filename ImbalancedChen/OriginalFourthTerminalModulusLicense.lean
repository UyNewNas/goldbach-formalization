import ImbalancedChen.OriginalFourthCausalFrontierFactorization
import ImbalancedChen.Part3ActualAttachedRoughFrontier

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO_FORMAL_CREDIT.

Terminal arithmetic support of the actual original fourth producer. A
valid chosen sublist constructs a real frontier at its own selected rank.
Applying this to a real terminal retained leaf produces the causal
ancestor witness and the complete inherited owned-Q license, including
the strict total-product modulus cutoff. This bridge does not assume that
a terminal leaf was already a frontier, nor discard its negative sign.

Raw twenty-two-stage chronology and external row distribution licenses
remain explicit open suppliers; no global analytic upper bound occurs.
-/

namespace ImbalancedChen.OriginalFourthTerminalModulusLicense20261026b

noncomputable section
open scoped Classical
open HistoricalThirdCoarse P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness P1OriginalFullTableActualProducerAdapter
open P1OriginalVariableFourthContinuation
open OriginalFourthSuccessorTransition20261026b
open OriginalFourthCausalFrontierFactorization20261026b
open Part3.ActualAttachedRoughFrontier

variable (records : List FourthWireRow) (e chi : ℝ) (m : ℕ) (omega N : ℝ)
  (licensed : ProducerRow → Prop)

/-- A real terminal leaf of rank at least four has its original inherited
ancestor, full owned-Q prefix license, and strict arithmetic modulus
cutoff. Neither sign nor positivity of a putative saving is a premise. -/
theorem actual_terminal_leaf_owned_modulus
    (Nnat cap : ℕ) (hN : 1 ≤ (Nnat : ℝ)) (z : ℝ) (weight : ℕ → ℝ)
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves
      (producerPolicy4 e chi m omega (Nnat : ℝ) (fourthFamily records) licensed)
      weight [] true 1 (roughPrimeUniverse Nnat cap 0 z))
    (hrank : 4 ≤ leaf.selected.length) :
    ∃ ancestor ∈ firstExitDepthFrontier 4
        (producerPolicy4 e chi m omega (Nnat : ℝ) (fourthFamily records) licensed)
        weight [] true 1 (roughPrimeUniverse Nnat cap 0 z),
      producerFrozenLevel4 e chi m omega (Nnat : ℝ) (fourthFamily records) licensed
          leaf.selected =
        producerLevel4 e chi m omega (Nnat : ℝ) (fourthFamily records) licensed
          ancestor.selectedPrefix ∧
      ordinaryRosserPrefixAdmissible false
        (producerFrozenLevel4 e chi m omega (Nnat : ℝ) (fourthFamily records) licensed
          leaf.selected) leaf.selected ∧
      (leaf.selected.prod : ℝ) <
        producerFrozenLevel4 e chi m omega (Nnat : ℝ) (fourthFamily records) licensed
          leaf.selected ∧
      ancestorOwner records e chi m omega (Nnat : ℝ) licensed leaf.selected =
        ancestorOwner records e chi m omega (Nnat : ℝ) licensed ancestor.selectedPrefix := by
  obtain ⟨chosen, hsub, hvalid, hselected⟩ :=
    exists_validSelection_of_mem_firstExitRetainedLeaves
      (producerPolicy4 e chi m omega (Nnat : ℝ) (fourthFamily records) licensed)
      weight [] (roughPrimeUniverse Nnat cap 0 z) true 1 leaf hleaf
  obtain ⟨state, hstateRaw, hstateSelected⟩ := valid_selection_frontier_witness
    (producerPolicy4 e chi m omega (Nnat : ℝ) (fourthFamily records) licensed)
    weight hsub [] true 1 hvalid
  have hlen : leaf.selected.length = chosen.length := by
    simp only [hselected, List.length_append, List.length_reverse, List.length_nil, add_zero]
  have hstate : state ∈ firstExitDepthFrontier leaf.selected.length
      (producerPolicy4 e chi m omega (Nnat : ℝ) (fourthFamily records) licensed)
      weight [] true 1 (roughPrimeUniverse Nnat cap 0 z) := by
    simpa only [List.length_nil, zero_add, hlen] using hstateRaw
  have hsame : state.selectedPrefix = leaf.selected := hstateSelected.trans hselected.symm
  obtain ⟨ancestor, hancestor, _hcontinuation, hQ, hadmissible, howner,
    _hsign, _hmass, _hcarrier⟩ :=
    actual_global_history_license records e chi m omega licensed Nnat cap hN z weight
      leaf.selected.length hrank state hstate
  rw [hsame] at hQ hadmissible howner
  exact ⟨ancestor, hancestor, hQ, hadmissible, hadmissible.1, howner⟩

/-- Arithmetic support itself supplies the true selected prime history.
The modulus's original prime-factor rank, not a caller-selected tuple,
determines whether the original fourth continuation has been reached. -/
theorem actual_retained_modulus_owned_cutoff
    (Nnat cap : ℕ) (hN : 1 ≤ (Nnat : ℝ)) (z : ℝ) (d : ℕ)
    (hd : d ∈ firstExitRetainedModuli
      (producerPolicy4 e chi m omega (Nnat : ℝ) (fourthFamily records) licensed)
      (roughPrimeUniverse Nnat cap 0 z))
    (hrank : 4 ≤ ArithmeticFunction.cardFactors d) :
    ∃ state ∈ firstExitDepthFrontier (ArithmeticFunction.cardFactors d)
        (producerPolicy4 e chi m omega (Nnat : ℝ) (fourthFamily records) licensed)
        (fun _ => 1) [] true 1 (roughPrimeUniverse Nnat cap 0 z),
      state.selectedPrefix.prod = d ∧
      ordinaryRosserPrefixAdmissible false
        (producerFrozenLevel4 e chi m omega (Nnat : ℝ) (fourthFamily records) licensed
          state.selectedPrefix) state.selectedPrefix ∧
      (d : ℝ) < producerFrozenLevel4 e chi m omega (Nnat : ℝ)
        (fourthFamily records) licensed state.selectedPrefix := by
  obtain ⟨chosen, hsub, hvalid, hprod⟩ :=
    (mem_firstExitRetainedModuli_iff_validSelection
      (producerPolicy4 e chi m omega (Nnat : ℝ) (fourthFamily records) licensed)
      (roughPrimeUniverse Nnat cap 0 z) d).mp hd
  have hprime : ∀ p ∈ chosen, p.Prime := by
    intro p hp
    exact mem_roughPrimeUniverse_prime (hsub.subset hp)
  have hrankChosen : ArithmeticFunction.cardFactors d = chosen.length := by
    rw [← hprod]
    exact cardFactors_list_prod_eq_length_of_primes chosen hprime
  obtain ⟨state, hstateRaw, hselected⟩ := valid_selection_frontier_witness
    (producerPolicy4 e chi m omega (Nnat : ℝ) (fourthFamily records) licensed)
    (fun _ => 1) hsub [] true 1 hvalid
  have hstate : state ∈ firstExitDepthFrontier (ArithmeticFunction.cardFactors d)
      (producerPolicy4 e chi m omega (Nnat : ℝ) (fourthFamily records) licensed)
      (fun _ => 1) [] true 1 (roughPrimeUniverse Nnat cap 0 z) := by
    simpa only [List.length_nil, zero_add, hrankChosen] using hstateRaw
  have hstateProd : state.selectedPrefix.prod = d := by
    simpa only [hselected, List.append_nil, List.prod_reverse] using hprod
  obtain ⟨_ancestor, _hancestor, _hcontinuation, _hQ, hadmissible,
    _howner, _hsign, _hmass, _hcarrier⟩ :=
    actual_global_history_license records e chi m omega licensed Nnat cap hN z (fun _ => 1)
      (ArithmeticFunction.cardFactors d) hrank state hstate
  refine ⟨state, hstate, hstateProd, hadmissible, ?_⟩
  rw [← hstateProd]
  exact hadmissible.1

end
end ImbalancedChen.OriginalFourthTerminalModulusLicense20261026b
