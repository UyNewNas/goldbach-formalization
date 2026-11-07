import ImbalancedChen.P5ActualSortedWeightPrimeGroupTensor
import ImbalancedChen.ActualPrimeSlotSquarefreeSymmetry
import ImbalancedChen.Part3DistributionTargets

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The Part3 finite vector source is filtered by the ACTUAL sorted fine-word
carrier. Its vector-to-list map is injective and preserves the complete
prime product. An arbitrary coordinate-dependent weight is extended by
zero off that typed carrier, then transported exactly to the list source
without assuming a product-only weight or an endpoint cover of all lists.

The literal Part3 PP has NO Mobius(q*product). The existing weighted
marked branch cannot be identified with it. Here the original sorted
distinct-prime product has Mobius(product)=(-1)^rank; multiplying by that
same fixed sign on the raw tensor side gives exactly the PLAIN Part3 AP
kernel while retaining the global prime-product square collision test.
The physical NEW ALL16 common-beta sigma stays unchanged. This is a
finite identity only; smooth Fourier norms and HB fibres remain separate.
-/

namespace ImbalancedChen
namespace P5Z.TypedLabelledPlainPrimeProductTensor

noncomputable section
open scoped Classical BigOperators
open ActualSortedWeightPrimeGroupTensor

def tupleList {k P : ℕ} (t : Fin k → Fin (P + 1)) : List ℕ :=
  List.ofFn (fun i => (t i).val)

theorem tupleList_injective {k P : ℕ} :
    Function.Injective (tupleList (k := k) (P := P)) := by
  intro t u h
  have hv : (fun i : Fin k => (t i).val) = (fun i => (u i).val) :=
    List.ofFn_injective h
  funext i
  exact Fin.ext (congrFun hv i)

theorem tupleList_product {k P : ℕ} (t : Fin k → Fin (P + 1)) :
    (tupleList t).prod = Part3.labelledProduct t := by
  simp only [tupleList, List.prod_ofFn, Part3.labelledProduct]

/-- This is the exact typed Part3 carrier covered by one original sorted
fine word. P may be smaller than other endpoints; no surjectivity onto the
whole unbounded list box is asserted. -/
def typedSortedCarrier (N P : ℕ) (τ : ℝ) (input : List ℕ) :
    Finset (Fin input.length → Fin (P + 1)) :=
  (Part3.labelledPrimeTuples input.length P).filter
    (fun t => tupleList t ∈ sortedWord N τ input)

def weightOnList (N P : ℕ) (τ : ℝ) (input : List ℕ)
    (W : (Fin input.length → Fin (P + 1)) → ℝ) (ps : List ℕ) : ℝ :=
  ∑ t ∈ (typedSortedCarrier N P τ input).filter (fun t => tupleList t = ps), W t

theorem weightOnList_of_mem (N P : ℕ) (τ : ℝ) (input : List ℕ)
    (W : (Fin input.length → Fin (P + 1)) → ℝ)
    {t : Fin input.length → Fin (P + 1)}
    (ht : t ∈ typedSortedCarrier N P τ input) :
    weightOnList N P τ input W (tupleList t) = W t := by
  unfold weightOnList
  rw [Finset.sum_eq_single t]
  · rfl
  · intro u hu hne
    exact (hne (tupleList_injective (Finset.mem_filter.mp hu).2)).elim
  · intro hnot
    exact (hnot (Finset.mem_filter.mpr ⟨ht, rfl⟩)).elim

/-- Exact typed vector/list weighted fibre identity at every test function
of the complete prime product. Original labels and their multiplicities
are retained by the typed carrier and the fibre weight. -/
theorem typedSorted_weighted_sum_eq_list
    (N P : ℕ) (τ : ℝ) (input : List ℕ)
    (W : (Fin input.length → Fin (P + 1)) → ℝ) (H : ℕ → ℝ) :
    (∑ t ∈ typedSortedCarrier N P τ input,
      W t * H (Part3.labelledProduct t)) =
      ∑ ps ∈ sortedWord N τ input,
        weightOnList N P τ input W ps * H ps.prod := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := typedSortedCarrier N P τ input) (t := sortedWord N τ input)
    (g := tupleList)
    (fun t ht => (Finset.mem_filter.mp ht).2)
    (fun t => W t * H (Part3.labelledProduct t))]
  apply Finset.sum_congr rfl
  intro ps hps
  unfold weightOnList
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t ht
  rw [← (Finset.mem_filter.mp ht).2, tupleList_product]

/-- Zero extension into the literal Part3 full labelled-prime universe. -/
def typedWeight (N P : ℕ) (τ : ℝ) (input : List ℕ)
    (W : (Fin input.length → Fin (P + 1)) → ℝ)
    (t : Fin input.length → Fin (P + 1)) : ℝ :=
  if tupleList t ∈ sortedWord N τ input then W t else 0

/-- The typed actual carrier has exactly the literal Part3 signed PP
error with the SAME arbitrary physical rho and exact coprime mean. -/
theorem typedPart3_error_eq_sortedWord
    (N P T : ℕ) (τ : ℝ) (input : List ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ)
    (W : (Fin input.length → Fin (P + 1)) → ℝ) :
    Part3.primeProductSignedError input.length P T Q rho
      (typedWeight N P τ input W) =
      ∑ q ∈ Q, rho q *
        (∑ ps ∈ sortedWord N τ input,
          weightOnList N P τ input W ps *
            primeProductAPDifference T q ps.prod) := by
  unfold Part3.primeProductSignedError
  apply Finset.sum_congr rfl
  intro q hq
  congr 1
  calc
    (∑ t ∈ Part3.labelledPrimeTuples input.length P,
      typedWeight N P τ input W t *
        primeProductAPDifference T q (Part3.labelledProduct t)) =
      ∑ t ∈ typedSortedCarrier N P τ input,
        W t * primeProductAPDifference T q (Part3.labelledProduct t) := by
      simp [typedWeight, typedSortedCarrier, Finset.sum_filter,
        primeProductAPDifference]
    _ = _ := typedSorted_weighted_sum_eq_list N P τ input W
      (primeProductAPDifference T q)

/-- On a sorted actual prime word, the original full-product Mobius is a
fixed rank sign. This avoids inserting the extraneous Mobius(q*product)
from the marked branch into the literal Part3 PP. -/
theorem sortedWord_moebius_sign (N : ℕ) (τ : ℝ) (input ps : List ℕ)
    (hps : ps ∈ sortedWord N τ input) :
    (ArithmeticFunction.moebius ps.prod : ℝ) = (-1 : ℝ) ^ input.length := by
  obtain ⟨hbox, hsorted⟩ := Finset.mem_filter.mp hps
  have hprime : ∀ p ∈ ps, Nat.Prime p :=
    actualPrimeSlotBox_prime (actualPrimeFineLabelFinset N τ) input
      (fun _ _ p hp => (mem_actualPrimeFineLabelFinset.mp hp).1) ps hbox
  have hlen := actualPrimeSlotBox_length
    (actualPrimeFineLabelFinset N τ) input ps hbox
  have hsign := actualPrimeVector_moebius_eq_sign ps hprime hsorted.nodup
  rw [hlen] at hsign
  exact_mod_cast hsign

private theorem rankSign_square (k : ℕ) :
    ((-1 : ℝ) ^ k) * ((-1 : ℝ) ^ k) = 1 := by
  rw [← pow_add]
  have h : k + k = 2 * k := by omega
  rw [h, pow_mul]
  norm_num

/-- The plain Part3 PP group expression. Global Mobius tests only the
prime-product tuple, with the fixed rank sign cancelling on the sorted
source. It does not test the physical modulus times that product. -/
def plainGroupPP
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
          ((ArithmeticFunction.moebius (a * b * d) : ℝ) *
            (((-1 : ℝ) ^ input.length) *
              weightAtProduct N τ input W (a * b * d) *
                primeProductAPDifference T q (a * b * d)))

/-- Exact PLAIN AP tensor for an arbitrary weight on the actual sorted
fine-word carrier, with original M_J and every cross-group collision. -/
theorem sortedPlainPP_eq_group
    {N : ℕ} (hN : 1 ≤ N) {τ : ℝ} (hτ : 0 ≤ τ)
    (T : ℕ) (D A : ℝ) (yz : Bool)
    (p : Fin 3 → ℕ) (tail : List ℕ)
    (horder : (p 0 :: p 1 :: p 2 :: tail).Pairwise (· ≥ ·))
    (W : List ℕ → ℝ) (c : ℝ) (q : ℕ) :
    c * (∑ ps ∈ sortedWord N τ (p 0 :: p 1 :: p 2 :: tail),
      W ps * primeProductAPDifference T q ps.prod) =
      plainGroupPP T N τ D A yz p tail W c q := by
  unfold plainGroupPP
  let input := p 0 :: p 1 :: p 2 :: tail
  let H : ℕ → ℝ := fun n =>
    ((-1 : ℝ) ^ input.length) *
      weightAtProduct N τ input W n * primeProductAPDifference T q n
  calc
    c * (∑ ps ∈ sortedWord N τ input,
      W ps * primeProductAPDifference T q ps.prod) =
      c * ∑ n ∈ (sortedWord N τ input).image List.prod,
        weightAtProduct N τ input W n * primeProductAPDifference T q n := by
      rw [sortedWord_weighted_sum_by_product N τ input W
        (primeProductAPDifference T q)]
    _ = c * ∑ n ∈ (sortedWord N τ input).image List.prod,
          (ArithmeticFunction.moebius n : ℝ) * H n := by
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      obtain ⟨ps, hps, rfl⟩ := Finset.mem_image.mp hn
      rw [sortedWord_moebius_sign N τ input ps hps]
      dsimp [H]
      calc
        _ = (((-1 : ℝ) ^ input.length) * ((-1 : ℝ) ^ input.length)) *
            (weightAtProduct N τ input W ps.prod *
              primeProductAPDifference T q ps.prod) := by ring
        _ = _ := by rw [rankSign_square]; ring
    _ = _ := by
      simpa only [input, H, sortedWord, one_mul] using
        (actualPrimeFineWord_sameSlots_original_scalar hN hτ D A yz p tail
          horder 1 c H)

/-- Typed literal Part3 PP now reaches the plain three-group tensor for
any zero-extended actual sorted carrier weight. The signed physical rho
remains outside the entire count-minus-coprime-mean expression. -/
theorem typedPart3_error_eq_plainGroup
    {N : ℕ} (hN : 1 ≤ N) {τ : ℝ} (hτ : 0 ≤ τ)
    (P T : ℕ) (D A : ℝ) (yz : Bool)
    (p : Fin 3 → ℕ) (tail : List ℕ)
    (horder : (p 0 :: p 1 :: p 2 :: tail).Pairwise (· ≥ ·))
    (Q : Finset ℕ) (rho : ℕ → ℝ)
    (W : (Fin (p 0 :: p 1 :: p 2 :: tail).length → Fin (P + 1)) → ℝ) :
    Part3.primeProductSignedError (p 0 :: p 1 :: p 2 :: tail).length P T Q rho
      (typedWeight N P τ (p 0 :: p 1 :: p 2 :: tail) W) =
      ∑ q ∈ Q, rho q *
        plainGroupPP T N τ D A yz p tail
          (weightOnList N P τ (p 0 :: p 1 :: p 2 :: tail) W) 1 q := by
  rw [typedPart3_error_eq_sortedWord N P T τ
    (p 0 :: p 1 :: p 2 :: tail) Q rho W]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← sortedPlainPP_eq_group hN hτ T D A yz p tail horder
    (weightOnList N P τ (p 0 :: p 1 :: p 2 :: tail) W) 1 q]
  simp only [one_mul]

/-- Concrete NEW ALL16 common-beta physical coefficient. No transfer to
the old native sigma or analytic PP estimate is inferred. -/
theorem jointPresieved_typedPart3_eq_plainGroup
    {N : ℕ} (hN : 1 ≤ N) {τ : ℝ} (hτ : 0 ≤ τ)
    (P T n : ℕ) (eta : ℚ) (w B D A : ℝ) (yz : Bool)
    (E : ℕ × ℕ → Prop) (p : Fin 3 → ℕ) (tail : List ℕ)
    (horder : (p 0 :: p 1 :: p 2 :: tail).Pairwise (· ≥ ·))
    (W : (Fin (p 0 :: p 1 :: p 2 :: tail).length → Fin (P + 1)) → ℝ) :
    Part3.primeProductSignedError (p 0 :: p 1 :: p 2 :: tail).length P T
      (OriginalJointPresievedCompiler.jointSupport n N eta w E)
      (OriginalJointPresievedCompiler.jointPresievedSigma n N eta w B E)
      (typedWeight N P τ (p 0 :: p 1 :: p 2 :: tail) W) =
      ∑ q ∈ OriginalJointPresievedCompiler.jointSupport n N eta w E,
        OriginalJointPresievedCompiler.jointPresievedSigma n N eta w B E q *
          plainGroupPP T N τ D A yz p tail
            (weightOnList N P τ (p 0 :: p 1 :: p 2 :: tail) W) 1 q := by
  exact typedPart3_error_eq_plainGroup hN hτ P T D A yz p tail horder
    (OriginalJointPresievedCompiler.jointSupport n N eta w E)
    (OriginalJointPresievedCompiler.jointPresievedSigma n N eta w B E) W

end
end P5Z.TypedLabelledPlainPrimeProductTensor
end ImbalancedChen
