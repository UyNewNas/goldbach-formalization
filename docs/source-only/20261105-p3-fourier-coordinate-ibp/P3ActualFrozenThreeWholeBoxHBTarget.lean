import ImbalancedChen.P3ActualFrozenTaggedPrimeBox
import ImbalancedChen.P3HBOriginalMarkedFineTarget

/-!
P3.6: THE WHOLE three-group Cartesian prime source paired with a genuine
rough-HB occurrence, using ONE complete physical product.

Prior P3ActualFrozenIDMarkedRoughDiagonal considered three individually
realized marked words, summing their separate product=N tests. That valid
restricted zero identity does NOT model the full prime product of a frozen
three-way atom. This file instead retains all THREE independent full
ordered prime boxes simultaneously and tests a.prod*b.prod*d.prod*hb.prod=N.

Each group retains its original ID-derived label order; repeated labels
and independent prime values are allowed. W is arbitrary in all ordered
positions. The original exact fineKernel and signed integer rho(q) are
used unchanged, without a product-Mobius substitution.

This does not prove that the entire PP/HB compiler is exhausted by these
three original fine-prime boxes, or pay nonzero-shift error or modulus mass.
Frozen manuscript: chen-imbalanced-semiprimes
9731290e8f53cffda44129906cde6a965eaa869b,
prime-product-completion §§2,3,4 and manuscript-body.tex eq:current-PP.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualFrozenThreeWholeBoxHBTarget
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualFrozenTaggedPrimeBox
open ImbalancedChen.P3ActualFrozenComplexGroupGamma
open ImbalancedChen.P3ActualFrozenTaggedPrimeModes
open ImbalancedChen.P3HBOriginalMarkedFineTarget
open ImbalancedChen.P3ActualWeightedFineSameRho
open ImbalancedChen.P5Z.LiteralHeathBrownOccurrenceWords
open ImbalancedChen.P5Z.ActualRoughHeathBrownWords

/-- Append TWO independently realized entire ordered fine-prime boxes.
No common values function or injection on repeated labels is imposed. -/
theorem prime_box_append_mem
    (B : ℕ → Finset ℕ) (u v a b : List ℕ)
    (ha : a ∈ actualPrimeSlotBox B u)
    (hb : b ∈ actualPrimeSlotBox B v) :
    a ++ b ∈ actualPrimeSlotBox B (u ++ v) := by
  induction u generalizing a with
  | nil =>
      have he : a = [] := by
        simpa [actualPrimeSlotBox] using ha
      subst a
      simpa using hb
  | cons i rest ih =>
      change a ∈ ((B i).product (actualPrimeSlotBox B rest)).image
        (fun pair => pair.1 :: pair.2) at ha
      obtain ⟨⟨p, ps⟩, hp, heq⟩ := Finset.mem_image.mp ha
      have hpair := Finset.mem_product.mp hp
      have hnew : p :: (ps ++ b) ∈
          ((B i).product (actualPrimeSlotBox B (rest ++ v))).image
            (fun pair => pair.1 :: pair.2) :=
        Finset.mem_image.mpr
          ⟨(p, ps ++ b), Finset.mem_product.mpr
            ⟨hpair.1, ih ps hpair.2⟩, rfl⟩
      rw [← heq]
      exact hnew

/-- All three simultaneous ordered prime tuples form ONE marked word
in the original concatenated full fine-prime box. -/
theorem three_prime_boxes_whole_mem
    (B : ℕ → Finset ℕ) (u v w a b d : List ℕ)
    (ha : a ∈ actualPrimeSlotBox B u)
    (hb : b ∈ actualPrimeSlotBox B v)
    (hd : d ∈ actualPrimeSlotBox B w) :
    a ++ b ++ d ∈ actualPrimeSlotBox B (u ++ v ++ w) := by
  exact prime_box_append_mem B (u ++ v) w (a ++ b) d
    (prime_box_append_mem B u v a b ha hb) hd

/-- One whole frozen three-group arithmetic source at physical q.
The exact target is the product of ALL three group words and ALL HB
positions. Each prime box is independently enumerated. -/
def threeFineRoughAtQ (N m j q : ℕ) (τ z y : ℝ)
    (u v w : List ℕ)
    (W : List ℕ → List ℕ → List ℕ → List ℕ → ℂ) : ℂ :=
  let B := actualPrimeFineLabelFinset N τ
  ∑ a ∈ actualPrimeSlotBox B u,
    ∑ b ∈ actualPrimeSlotBox B v,
      ∑ d ∈ actualPrimeSlotBox B w,
        ∑ hb ∈ (factorTuples (2 * (j + 1)) m).filter
            (fun hb => a.prod * b.prod * d.prod * hb.prod = N),
          (W a b d hb * roughTupleWeight z y (roles j) hb) *
            ((fineKernel N q (a.prod * b.prod * d.prod * hb.prod) : ℝ) : ℂ)

/-- On an even target the whole three-box/HB complete-product=N fibre
is ZERO, not merely the sum of three individual group-diagonal fibres.
The proof is valid even for empty boxes, repeated labels and tuples
with coincident prime values from distinct original occurrences. -/
theorem threeFineRoughAtQ_zero
    (N m j q : ℕ) (τ z y : ℝ)
    (u v w : List ℕ)
    (W : List ℕ → List ℕ → List ℕ → List ℕ → ℂ)
    (hz : (2 : ℝ) ≤ z) (hN : Even N) :
    threeFineRoughAtQ N m j q τ z y u v w W = 0 := by
  unfold threeFineRoughAtQ
  dsimp
  apply Finset.sum_eq_zero
  intro a ha
  apply Finset.sum_eq_zero
  intro b hb
  apply Finset.sum_eq_zero
  intro d hd
  apply Finset.sum_eq_zero
  intro h hmem
  have hf : h ∈ factorTuples (2 * (j + 1)) m :=
    (Finset.mem_filter.mp hmem).1
  have ht : a.prod * b.prod * d.prod * h.prod = N :=
    (Finset.mem_filter.mp hmem).2
  have hmarked : a ++ b ++ d ∈
      actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) (u ++ v ++ w) :=
    three_prime_boxes_whole_mem _ u v w a b d ha hb hd
  have htarget : (a ++ b ++ d).prod * h.prod = N := by
    simpa only [List.prod_append, mul_assoc] using ht
  have hzero : roughTupleWeight z y (roles j) h = 0 :=
    original_marked_fine_rough_occurrence_target_zero
      N m j τ z y (u ++ v ++ w) (a ++ b ++ d) h
      hz hN hmarked hf htarget
  simp [hzero]

/-- The actual original-ID frozen selector supplies the THREE ordered
label words, not three separate target tests. The full Cartesian product
is retained; every prime value remains a free source variable. -/
def frozenThreeWholeAtQ {n : ℕ}
    (N m j q : ℕ) (τ z y D A : ℝ) (yz : Bool)
    (upper : Fin n → ℕ) (label : Fin n → ℕ)
    (p : Fin 3 → Fin n) (tail : List (Fin n))
    (W : List ℕ → List ℕ → List ℕ → List ℕ → ℂ) : ℂ :=
  let g := actualFrozenSelectedPairSlots D A yz upper p tail
  threeFineRoughAtQ N m j q τ z y
    (g.1.map label) (g.2.1.map label) (g.2.2.map label) W

theorem frozenThreeWholeAtQ_zero {n : ℕ}
    (N m j q : ℕ) (τ z y D A : ℝ) (yz : Bool)
    (upper : Fin n → ℕ) (label : Fin n → ℕ)
    (p : Fin 3 → Fin n) (tail : List (Fin n))
    (W : List ℕ → List ℕ → List ℕ → List ℕ → ℂ)
    (hz : (2 : ℝ) ≤ z) (hN : Even N) :
    frozenThreeWholeAtQ N m j q τ z y D A yz upper label p tail W = 0 := by
  unfold frozenThreeWholeAtQ
  exact threeFineRoughAtQ_zero N m j q τ z y _ _ _ W hz hN

/-- The exact +3,-3,+1 rough-HB source at the SAME integer signed rho,
same physical Q and precise count-minus-coprime-mean fineKernel. This
is a whole three-group zero-fibre identity, not an estimate of PP. -/
theorem frozenThreeWholeSameRhoTarget_zero {n : ℕ}
    (N m : ℕ) (τ z y D A : ℝ) (yz : Bool)
    (upper : Fin n → ℕ) (label : Fin n → ℕ)
    (p : Fin 3 → Fin n) (tail : List (Fin n))
    (Q : Finset ℕ) (rho : ℕ → ℤ)
    (W : ℕ → List ℕ → List ℕ → List ℕ → List ℕ → ℂ)
    (hz : (2 : ℝ) ≤ z) (hN : Even N) :
    (∑ q ∈ Q, (rho q : ℂ) *
      (∑ j ∈ Finset.range 3,
        ((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
          frozenThreeWholeAtQ N m j q τ z y D A yz
            upper label p tail (W j))) = 0 := by
  apply Finset.sum_eq_zero
  intro q hq
  have hj :
      (∑ j ∈ Finset.range 3,
        ((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
          frozenThreeWholeAtQ N m j q τ z y D A yz
            upper label p tail (W j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hjmem
    rw [frozenThreeWholeAtQ_zero
      N m j q τ z y D A yz upper label p tail (W j) hz hN]
    simp
  simp [hj]

end
end ImbalancedChen.P3ActualFrozenThreeWholeBoxHBTarget
