import ImbalancedChen.ActualPrimeFineWordSlotRegrouping
import ImbalancedChen.P5OriginalJointPresievedCompiler

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

An arbitrary real weight on the ACTUAL sorted fine-word carrier need not
be symmetric in its original labelled coordinates. On this sorted carrier
the complete prime product uniquely determines the tuple, so the finite
fibre sum below recovers that weight exactly. This supplies the algebraic
coefficient/label identity needed before smooth Fourier separation.

The original M_J, three group factorials, global Mobius factor, literal AP
residue and exact coprime mean remain in one identity under the NEW ALL16
common-beta physical sigma. The smooth Fourier norm, HB/rough fibres,
collision power saving and final all-family PP estimate are separate.
-/

namespace ImbalancedChen
namespace P5Z.ActualSortedWeightPrimeGroupTensor

noncomputable section
open scoped Classical BigOperators
open U1011OriginalSixteenArithmeticProducts (fullPrefix)

def sortedWord (N : ℕ) (τ : ℝ) (input : List ℕ) : Finset (List ℕ) :=
  (actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) input).filter List.SortedGT

/-- No choice of representative: this is the exact finite product fibre.
On the sorted source every occupied fibre contains one original tuple. -/
def weightAtProduct (N : ℕ) (τ : ℝ) (input : List ℕ)
    (W : List ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ ps ∈ (sortedWord N τ input).filter (fun ps => ps.prod = n), W ps

theorem sortedWord_product_injective (N : ℕ) (τ : ℝ) (input : List ℕ) :
    ∀ ps ∈ sortedWord N τ input, ∀ qs ∈ sortedWord N τ input,
      ps.prod = qs.prod → ps = qs := by
  simpa only [sortedWord, actualPrimeFineLabelSortedTuples,
    actualPrimeFineLabelBlocksOfWord_word] using
    (actualPrimeFineLabelSortedTuples_product_injective N τ
      (actualPrimeFineLabelBlocksOfWord input))

/-- The arbitrary labelled weight is recovered at the unique actual
sorted tuple with product `ps.prod`; no symmetry of W is assumed. -/
theorem weightAtProduct_of_mem (N : ℕ) (τ : ℝ) (input : List ℕ)
    (W : List ℕ → ℝ) {ps : List ℕ} (hps : ps ∈ sortedWord N τ input) :
    weightAtProduct N τ input W ps.prod = W ps := by
  unfold weightAtProduct
  rw [Finset.sum_eq_single ps]
  · rfl
  · intro qs hqs hne
    obtain ⟨hqs', hprod⟩ := Finset.mem_filter.mp hqs
    exact (hne ((sortedWord_product_injective N τ input qs hqs' ps hps) hprod)).elim
  · intro hnot
    exact (hnot (Finset.mem_filter.mpr ⟨hps, rfl⟩)).elim

/-- Exact weighted product-fibre disintegration, retaining every original
label and tuple weight before any arithmetic modulus is evaluated. -/
theorem sortedWord_weighted_sum_by_product
    (N : ℕ) (τ : ℝ) (input : List ℕ)
    (W : List ℕ → ℝ) (H : ℕ → ℝ) :
    (∑ ps ∈ sortedWord N τ input, W ps * H ps.prod) =
      ∑ n ∈ (sortedWord N τ input).image List.prod,
        weightAtProduct N τ input W n * H n := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun ps hps => Finset.mem_image_of_mem List.prod hps)
    (fun ps => W ps * H ps.prod)]
  apply Finset.sum_congr rfl
  intro n hn
  unfold weightAtProduct
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ps hps
  rw [(Finset.mem_filter.mp hps).2]

def primeProductAPDifference (T q n : ℕ) : ℝ :=
  (if Nat.ModEq q n T then (1 : ℝ) else 0) -
    (if Nat.Coprime n q then (1 : ℝ) else 0) / (Nat.totient q : ℝ)

def weightedWordPP
    (T N : ℕ) (τ : ℝ) (input : List ℕ)
    (W : List ℕ → ℝ) (c : ℝ) (q : ℕ) : ℝ :=
  c * ∑ ps ∈ sortedWord N τ input,
    W ps * ((ArithmeticFunction.moebius (q * ps.prod) : ℝ) *
      primeProductAPDifference T q ps.prod)

/-- The original three fixed groups, with the actual sorted weight
transported through its unique product fibre. -/
def weightedGroupPP
    (T N : ℕ) (τ D A : ℝ) (yz : Bool)
    (p : Fin 3 → ℕ) (tail : List ℕ)
    (W : List ℕ → ℝ) (c : ℝ) (q : ℕ) : ℝ :=
  let input := p 0 :: p 1 :: p 2 :: tail
  let slots := actualFrozenSelectedPairSlots D A yz
    (actualPrimeFineLabelIntegerUpper N τ) p tail
  let B := actualPrimeFineLabelFinset N τ
  let T₁ := actualPrimeSlotBox B slots.1
  let T₂ := actualPrimeSlotBox B slots.2.1
  let T₃ := actualPrimeSlotBox B slots.2.2
  ∑ a ∈ T₁.image List.prod, ∑ b ∈ T₂.image List.prod,
    ∑ d ∈ T₃.image List.prod,
      ((c / (actualPrimeFineWordMultiplicity input : ℝ)) *
        (slots.1.length.factorial : ℝ) *
        (slots.2.1.length.factorial : ℝ) *
        (slots.2.2.length.factorial : ℝ)) *
        actualNormalizedPrimeTupleCoefficient T₁ slots.1.length a *
        actualNormalizedPrimeTupleCoefficient T₂ slots.2.1.length b *
        actualNormalizedPrimeTupleCoefficient T₃ slots.2.2.length d *
          ((ArithmeticFunction.moebius (q * (a * b * d)) : ℝ) *
            (weightAtProduct N τ input W (a * b * d) *
              primeProductAPDifference T q (a * b * d)))

/-- Exact algebraic tensor identity for EVERY weight on the actual sorted
fine-word source. The weight remains coupled as a function of `a*b*d`;
its smooth separation and coefficient norm are not inferred here. -/
theorem weightedWordPP_eq_weightedGroupPP
    {N : ℕ} (hN : 1 ≤ N) {τ : ℝ} (hτ : 0 ≤ τ)
    (T : ℕ) (D A : ℝ) (yz : Bool)
    (p : Fin 3 → ℕ) (tail : List ℕ)
    (horder : (p 0 :: p 1 :: p 2 :: tail).Pairwise (· ≥ ·))
    (W : List ℕ → ℝ) (c : ℝ) (q : ℕ) :
    weightedWordPP T N τ (p 0 :: p 1 :: p 2 :: tail) W c q =
      weightedGroupPP T N τ D A yz p tail W c q := by
  unfold weightedWordPP weightedGroupPP
  let input := p 0 :: p 1 :: p 2 :: tail
  let H : ℕ → ℝ := fun n =>
    weightAtProduct N τ input W n * primeProductAPDifference T q n
  calc
    c * (∑ ps ∈ sortedWord N τ input,
        W ps * ((ArithmeticFunction.moebius (q * ps.prod) : ℝ) *
          primeProductAPDifference T q ps.prod)) =
      c * ∑ n ∈ (sortedWord N τ input).image List.prod,
        (ArithmeticFunction.moebius (q * n) : ℝ) * H n := by
      rw [sortedWord_weighted_sum_by_product N τ input W
        (fun n => (ArithmeticFunction.moebius (q * n) : ℝ) *
          primeProductAPDifference T q n)]
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      dsimp [H]
      ring
    _ = _ := by
      simpa only [input, H, sortedWord] using
        (actualPrimeFineWord_sameSlots_original_scalar hN hτ D A yz p tail
          horder q c H)

/-- The NEW ALL16 common-beta physical sigma is fixed before W and before
the AP test. Its exact mark pushforward and the weighted group identity
use the SAME sigma and the SAME coprime mean. -/
theorem jointPresieved_weighted_primeGroup_AP
    {N : ℕ} (hN : 1 ≤ N) {τ : ℝ} (hτ : 0 ≤ τ)
    (n T : ℕ) (eta : ℚ) (w B D A c : ℝ) (yz : Bool)
    (E : ℕ × ℕ → Prop) (p : Fin 3 → ℕ) (tail : List ℕ)
    (horder : (p 0 :: p 1 :: p 2 :: tail).Pairwise (· ≥ ·))
    (W : List ℕ → ℝ) :
    (∑ t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
      ∑ r ∈ OriginalOrdinaryPresievedSigma.rowSupport n N eta w t,
        OriginalOrdinaryPresievedSigma.rowCoefficient n N eta w B t r *
          weightedWordPP T N τ (p 0 :: p 1 :: p 2 :: tail) W c
            (fullPrefix t * r)) =
      ∑ q ∈ OriginalJointPresievedCompiler.jointSupport n N eta w E,
        OriginalJointPresievedCompiler.jointPresievedSigma n N eta w B E q *
          weightedGroupPP T N τ D A yz p tail W c q := by
  calc
    _ = ∑ q ∈ OriginalJointPresievedCompiler.jointSupport n N eta w E,
          OriginalJointPresievedCompiler.jointPresievedSigma n N eta w B E q *
            weightedWordPP T N τ (p 0 :: p 1 :: p 2 :: tail) W c q :=
      OriginalJointPresievedCompiler.joint_exact_pushforward n N eta w B E
        (weightedWordPP T N τ (p 0 :: p 1 :: p 2 :: tail) W c)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [weightedWordPP_eq_weightedGroupPP hN hτ T D A yz p tail horder W c q]

end
end P5Z.ActualSortedWeightPrimeGroupTensor
end ImbalancedChen
