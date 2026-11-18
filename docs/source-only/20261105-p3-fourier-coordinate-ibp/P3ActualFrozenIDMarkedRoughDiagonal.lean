import ImbalancedChen.P3ActualFrozenTaggedPrimeBox
import ImbalancedChen.P3HBOriginalMarkedFineTarget

/-!
P3.6: admission of REALIZED original Fin n prime IDs selected by the
frozen three-group allocator into a literal rough-HB exact-target fibre.

The selected group words are the original ID words, not an invented
product-only coefficient or a sorted replacement. The hypothesis hmem
is precisely original fine-prime alphabet membership for every ID;
the pre-existing frozen_realized_three_prime_boxes proves group-box
membership, even when the original ID -> label map is NONINJECTIVE.

For even N and z >= 2 the original strict rough projector kills the
complete marked-prime * HB-product = N fibre, group by group, at each
physical q and after the unchanged signed integer rho(q) and exact
coprime mean. The genuine HB roles and +3,-3,+1 scalars are retained.

This covers ONLY a realized frozen original-ID prime assignment paired
with a literal rough-HB factorTuples fibre. It does NOT certify that
every HB/PP compiler atom is such an assignment, nor prove the
nonzero-shift divisor moment or the full PP estimate.
Pinned paper: chen-imbalanced-semiprimes
9731290e8f53cffda44129906cde6a965eaa869b,
prime-product-completion §§2,4 (HB),(F); manuscript-body.tex eq:current-PP.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualFrozenIDMarkedRoughDiagonal

noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualFrozenTaggedPrimeBox
open ImbalancedChen.P3ActualFrozenTaggedPrimeModes
open ImbalancedChen.P3ActualFrozenComplexGroupGamma
open ImbalancedChen.P3HBOriginalMarkedFineTarget
open ImbalancedChen.P3ActualWeightedFineSameRho
open ImbalancedChen.P5Z.LiteralHeathBrownOccurrenceWords
open ImbalancedChen.P5Z.ActualRoughHeathBrownWords

/-- Exactly one realized tagged marked-prime list, all ORIGINAL HB
ordered occurrence slots, original complete product and fineKernel.
No extra whole-product Mobius is inserted into roughTupleWeight. -/
def realizedTaggedHBAtQ (N m j q : ℕ) (z y : ℝ)
    (marked : List ℕ) (W : List ℕ → ℂ) : ℂ :=
  ∑ hb ∈ (factorTuples (2 * (j + 1)) m).filter
        (fun hb => marked.prod * hb.prod = N),
    (W hb * roughTupleWeight z y (roles j) hb) *
      ((fineKernel N q (marked.prod * hb.prod) : ℝ) : ℂ)

/-- A realized prime word in the ORIGINAL fine-label box cannot
sustain an even-target literal rough-HB diagonal. The empty marked
word is also covered, because then the genuine rough HB projector
annihilates the entire even product. -/
theorem realizedTaggedHBAtQ_zero
    (N m j q : ℕ) (τ z y : ℝ)
    (word marked : List ℕ) (W : List ℕ → ℂ)
    (hz : (2 : ℝ) ≤ z) (hN : Even N)
    (hmarked : marked ∈
      actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) word) :
    realizedTaggedHBAtQ N m j q z y marked W = 0 := by
  unfold realizedTaggedHBAtQ
  apply Finset.sum_eq_zero
  intro hb hhb
  have hfactor : hb ∈ factorTuples (2 * (j + 1)) m :=
    (Finset.mem_filter.mp hhb).1
  have hfull : marked.prod * hb.prod = N :=
    (Finset.mem_filter.mp hhb).2
  have hzero : roughTupleWeight z y (roles j) hb = 0 :=
    original_marked_fine_rough_occurrence_target_zero
      N m j τ z y word marked hb hz hN hmarked hfactor hfull
  simp [hzero]

/-- The ACTUAL frozen selected pair allocator preserves box admission
of each of its three ORIGINAL-ID lists. These are not quotient labels
or an assumed permutation-invariant W. -/
theorem frozen_selected_three_realized_atQ_zero {n : ℕ}
    (N m j q : ℕ) (τ z y D A : ℝ) (yz : Bool)
    (upper : Fin n → ℕ) (label : Fin n → ℕ)
    (p : Fin 3 → Fin n) (tail : List (Fin n))
    (values : Fin n → ℕ) (W : Fin 3 → List ℕ → ℂ)
    (hz : (2 : ℝ) ≤ z) (hN : Even N)
    (hmem : ∀ i, values i ∈ actualPrimeFineLabelFinset N τ (label i)) :
    let g := actualFrozenSelectedPairSlots D A yz upper p tail
    (realizedTaggedHBAtQ N m j q z y (g.1.map values) (W 0) = 0) ∧
    (realizedTaggedHBAtQ N m j q z y (g.2.1.map values) (W 1) = 0) ∧
    (realizedTaggedHBAtQ N m j q z y (g.2.2.map values) (W 2) = 0) := by
  let g := actualFrozenSelectedPairSlots D A yz upper p tail
  have hboxes :
      (g.1.map values ∈
        actualPrimeSlotBox (actualPrimeFineLabelFinset N τ)
          (g.1.map label)) ∧
      (g.2.1.map values ∈
        actualPrimeSlotBox (actualPrimeFineLabelFinset N τ)
          (g.2.1.map label)) ∧
      (g.2.2.map values ∈
        actualPrimeSlotBox (actualPrimeFineLabelFinset N τ)
          (g.2.2.map label)) := by
    exact frozen_realized_three_prime_boxes D A yz upper p tail
      (actualPrimeFineLabelFinset N τ) label values hmem
  rcases hboxes with ⟨h0, h1, h2⟩
  exact ⟨
    realizedTaggedHBAtQ_zero N m j q τ z y
      (g.1.map label) (g.1.map values) (W 0) hz hN h0,
    realizedTaggedHBAtQ_zero N m j q τ z y
      (g.2.1.map label) (g.2.1.map values) (W 1) hz hN h1,
    realizedTaggedHBAtQ_zero N m j q τ z y
      (g.2.2.map label) (g.2.2.map values) (W 2) hz hN h2⟩

/-- Same ORIGINAL signed physical rho(q), exact fineKernel mean,
literal +3,-3,+1 HB occurrences and three frozen ID groups.
This is the finite diagonal of THIS realized tagged subsource only;
it does not replace the full compiler or pay off-target discrepancy. -/
theorem frozen_selected_three_same_rho_target_zero {n : ℕ}
    (N m : ℕ) (τ z y D A : ℝ) (yz : Bool)
    (upper : Fin n → ℕ) (label : Fin n → ℕ)
    (p : Fin 3 → Fin n) (tail : List (Fin n))
    (values : Fin n → ℕ) (Q : Finset ℕ) (rho : ℕ → ℤ)
    (W : Fin 3 → ℕ → List ℕ → ℂ)
    (hz : (2 : ℝ) ≤ z) (hN : Even N)
    (hmem : ∀ i, values i ∈ actualPrimeFineLabelFinset N τ (label i)) :
    let g := actualFrozenSelectedPairSlots D A yz upper p tail
    (∑ q ∈ Q, (rho q : ℂ) *
      (∑ j ∈ Finset.range 3,
        ((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
        (realizedTaggedHBAtQ N m j q z y (g.1.map values) (W 0 j) +
         realizedTaggedHBAtQ N m j q z y (g.2.1.map values) (W 1 j) +
         realizedTaggedHBAtQ N m j q z y (g.2.2.map values) (W 2 j)))) = 0 := by
  let g := actualFrozenSelectedPairSlots D A yz upper p tail
  have hboxes := frozen_realized_three_prime_boxes
    D A yz upper p tail (actualPrimeFineLabelFinset N τ) label values hmem
  rcases hboxes with ⟨h0, h1, h2⟩
  apply Finset.sum_eq_zero
  intro q hq
  have hj :
      (∑ j ∈ Finset.range 3,
        ((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
        (realizedTaggedHBAtQ N m j q z y (g.1.map values) (W 0 j) +
         realizedTaggedHBAtQ N m j q z y (g.2.1.map values) (W 1 j) +
         realizedTaggedHBAtQ N m j q z y (g.2.2.map values) (W 2 j))) = 0 := by
    apply Finset.sum_eq_zero
    intro j hjmem
    have hz0 := realizedTaggedHBAtQ_zero N m j q τ z y
      (g.1.map label) (g.1.map values) (W 0 j) hz hN h0
    have hz1 := realizedTaggedHBAtQ_zero N m j q τ z y
      (g.2.1.map label) (g.2.1.map values) (W 1 j) hz hN h1
    have hz2 := realizedTaggedHBAtQ_zero N m j q τ z y
      (g.2.2.map label) (g.2.2.map values) (W 2 j) hz hN h2
    simp [hz0, hz1, hz2]
  simp [hj]

end
end ImbalancedChen.P3ActualFrozenIDMarkedRoughDiagonal
