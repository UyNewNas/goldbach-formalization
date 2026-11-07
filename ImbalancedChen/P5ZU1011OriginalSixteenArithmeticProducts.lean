import ImbalancedChen.P5ZU1011OriginalSixteenPolicyBank
import ImbalancedChen.CurrentChenUpsilon1011JointOverlapFiniteMean
import ImbalancedChen.FinitePrimeGeometryCore
import ImbalancedChen.SelectedPrefixBoxCap

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The original sixteen-policy bit masks now select literal natural prime
subproducts on the actual U10/U11 common carrier. Arithmetic labels increase
p1<p2<p3<p4; the policy slots DECREASE ![p4,p3,p2,p1]. The W policy is a
separate non-subset policy and selects no artificial prime subproduct.

This file supplies fullprefix/selected/remainder and remaining-prefix
products, their actual coprimality and totient dictionary, their exact
logarithmic selected mass, and all genuine original square gates on those
integer products. It does not supply a table density bound, a physical
distribution license, an adaptive analytic mean, or a final count estimate.
Generic adaptive winner and same-rho finite Rosser/AP/centre identities
already exist and are deliberately not reproduced here.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenArithmeticProducts

noncomputable section
open scoped BigOperators
open Classical
open U11Integral
open U1011OriginalSixteenPolicyBank
open P5U1011JointOverlap

abbrev Four := (ℕ × ℕ) × (ℕ × ℕ)

/-- Exact reversal from increasing arithmetic labels to decreasing policy
slots; bit0 reads p4, bit3 reads p1. -/
def slots (t : Four) : Fin 4 → ℕ := ![t.2.2, t.2.1, t.1.2, t.1.1]

def coordinates (N : ℕ) (t : Four) : LogFour := actualPrimeTupleLog N (slots t)

def selectedIndices (p : Policy) : Finset (Fin 4) := Finset.univ.filter (Selected p)
def remainderIndices (p : Policy) : Finset (Fin 4) := Finset.univ.filter (fun i => ¬ Selected p i)
def prefixIndices (j : Fin 4) : Finset (Fin 4) := Finset.univ.filter (fun i => i.val < j.val)
def earlierRemainderIndices (p : Policy) (j : Fin 4) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => i.val < j.val ∧ ¬ Selected p i)
def laterRemainderIndices (p : Policy) (j : Fin 4) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => j.val ≤ i.val ∧ ¬ Selected p i)

def selectedProduct (p : Policy) (t : Four) : ℕ := ∏ i ∈ selectedIndices p, slots t i
def remainderProduct (p : Policy) (t : Four) : ℕ := ∏ i ∈ remainderIndices p, slots t i
def fullPrefix (t : Four) : ℕ := ∏ i : Fin 4, slots t i
def prefixProduct (j : Fin 4) (t : Four) : ℕ := ∏ i ∈ prefixIndices j, slots t i
def earlierRemainderProduct (p : Policy) (j : Fin 4) (t : Four) : ℕ :=
  ∏ i ∈ earlierRemainderIndices p j, slots t i
def laterRemainderProduct (p : Policy) (j : Fin 4) (t : Four) : ℕ :=
  ∏ i ∈ laterRemainderIndices p j, slots t i

theorem slots_carrier {N : ℕ} {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) (i : Fin 4) : slots t i ∈ chenAdditivePrimeCarrier N := by
  obtain ⟨h1,h2,h3,h4,_⟩ := joint_carrier_order ht
  fin_cases i
  · simpa [slots] using h4
  · simpa [slots] using h3
  · simpa [slots] using h2
  · simpa [slots] using h1

theorem slots_prime {N : ℕ} {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) (i : Fin 4) : Nat.Prime (slots t i) :=
  (mem_chenAdditivePrimeCarrier.mp (slots_carrier ht i)).2.1

theorem slots_pos {N : ℕ} {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) (i : Fin 4) : 0 < slots t i := (slots_prime ht i).pos

theorem slots_strictAnti {N : ℕ} {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) : StrictAnti (slots t) := by
  obtain ⟨_,_,_,_,h12,h23,h34⟩ := joint_carrier_order ht
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [slots] at hij ⊢ <;> omega

theorem coordinates_strictAnti {N : ℕ} (hN : 1 < N) {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) : StrictAnti (coordinates N t) :=
  (actualPrimeTupleLog_strictAnti_iff hN (slots t) (slots_pos ht)).mpr (slots_strictAnti ht)

theorem fullPrefix_eq_multiplier (t : Four) : fullPrefix t = P5U10OriginalMean.multiplier t := by
  simp [fullPrefix,slots,Fin.prod_univ_succ,P5U10OriginalMean.multiplier]
  <;> ring

/-- No bit is reinterpreted as an increasing arithmetic position. -/
theorem selected_first_largest (t : Four) : selectedProduct first t = t.2.2 := by
  norm_num [selectedProduct,selectedIndices,Selected,sourceId,first,slots,
    Finset.prod_filter,Fin.prod_univ_succ]

theorem selected_W_eq_one (t : Four) : selectedProduct wPolicy t = 1 := by
  simp [selectedProduct,selectedIndices,Selected,wPolicy]

theorem selected_mul_remainder (p : Policy) (t : Four) :
    selectedProduct p t * remainderProduct p t = fullPrefix t := by
  exact Finset.prod_filter_mul_prod_filter_not Finset.univ (Selected p) (slots t)

/-- Before an unselected slot j, precisely the earlier unselected primes
have occurred; all selected primes are already in selectedProduct. -/
theorem remainder_prefix_split (p : Policy) (j : Fin 4) (t : Four) :
    earlierRemainderProduct p j t * laterRemainderProduct p j t = remainderProduct p t := by
  have hearly : (remainderIndices p).filter (fun i => i.val < j.val) =
      earlierRemainderIndices p j := by
    ext i
    simp [remainderIndices,earlierRemainderIndices,and_comm]
  have hlate : (remainderIndices p).filter (fun i => ¬ i.val < j.val) =
      laterRemainderIndices p j := by
    ext i
    simp [remainderIndices,laterRemainderIndices,not_lt,and_comm]
  have h := Finset.prod_filter_mul_prod_filter_not (remainderIndices p)
    (fun i => i.val < j.val) (slots t)
  simpa only [hearly,hlate,earlierRemainderProduct,laterRemainderProduct,remainderProduct] using h

theorem selected_remainder_prefix_split (p : Policy) (j : Fin 4) (t : Four) :
    selectedProduct p t * earlierRemainderProduct p j t * laterRemainderProduct p j t =
      fullPrefix t := by
  rw [mul_assoc,remainder_prefix_split,selected_mul_remainder]

theorem selected_remainder_coprime {N : ℕ} {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) (p : Policy) :
    Nat.Coprime (selectedProduct p t) (remainderProduct p t) := by
  unfold selectedProduct remainderProduct
  apply Nat.coprime_prod_left_iff.mpr
  intro i hi
  apply Nat.coprime_prod_right_iff.mpr
  intro j hj
  apply (Nat.coprime_primes (slots_prime ht i) (slots_prime ht j)).mpr
  intro heq
  have hij := (slots_strictAnti ht).injective heq
  have hsi : Selected p i := (Finset.mem_filter.mp hi).2
  have hsj : ¬Selected p j := (Finset.mem_filter.mp hj).2
  exact hsj (hij ▸ hsi)

theorem subproduct_coprime_target {N : ℕ} {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) (I : Finset (Fin 4)) :
    Nat.Coprime (∏ i ∈ I, slots t i) N := by
  apply Nat.coprime_prod_left_iff.mpr
  intro i _
  exact (mem_chenAdditivePrimeCarrier.mp (slots_carrier ht i)).2.2

theorem selected_remainder_totient {N : ℕ} {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) (p : Policy) :
    Nat.totient (fullPrefix t) =
      Nat.totient (selectedProduct p t) * Nat.totient (remainderProduct p t) := by
  rw [← selected_mul_remainder p t]
  exact Nat.totient_mul (selected_remainder_coprime ht p)

/-- The selected bit sum is the logarithm of the actual selected natural
product, including the empty W product whose logarithm is zero. -/
theorem subproduct_log {N : ℕ} {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) (I : Finset (Fin 4)) :
    Real.log ((∏ i ∈ I, slots t i : ℕ) : ℝ) / Real.log (N : ℝ) =
      ∑ i ∈ I, coordinates N t i := by
  rw [Nat.cast_prod,Real.log_prod (fun i _ => by exact_mod_cast (slots_pos ht i).ne')]
  simp only [Finset.sum_div,coordinates,actualPrimeTupleLog]

theorem selectedMass_eq_log_product {N : ℕ} {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) (p : Policy) :
    selectedMass p (coordinates N t) =
      Real.log (selectedProduct p t : ℝ) / Real.log (N : ℝ) := by
  rw [selectedProduct,subproduct_log ht]
  simp [selectedIndices,selectedMass,Finset.sum_filter]

theorem subproduct_rpow {N : ℕ} (hN : 1 < N) {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) (I : Finset (Fin 4)) :
    (N : ℝ) ^ (∑ i ∈ I, coordinates N t i) = ((∏ i ∈ I, slots t i : ℕ) : ℝ) := by
  rw [Real.rpow_sum_of_pos (by exact_mod_cast (zero_lt_one.trans hN)),Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact actualPrimeTupleLog_rpow hN (slots t) (slots_pos ht) i

theorem selectedSquare_eq_generic (p : Policy) (v : LogFour) (j : Fin 4) :
    selectedSquare p j v = selectedSquareExpr (selectedIndices p) v j := by
  simp [selectedSquare,selectedSquareExpr,selectedIndices,selectedMass,Finset.sum_filter,
    Fin.lt_def]

theorem fullSquare_eq_generic (v : LogFour) (j : Fin 4) :
    fullSquare j v = prefixSquareExpr v j := by
  simp [fullSquare,prefixSquareExpr,Finset.sum_filter,Fin.lt_def]

/-- Literal original full and selected-square tests imply the corresponding
strict natural product tests on this same arithmetic tuple. W contributes
the full tests only; no W-specific selected-subproduct is invented. -/
theorem actual_original_square_gates {N : ℕ} (hN : 1 < N)
    {E : ℕ × ℕ → Prop} {t : Four} (ht : t ∈ jointSelector N E)
    (p : Policy) (he : TypedEligible p (coordinates N t)) :
    (∀ j : Fin 4, (prefixProduct j t : ℝ) * (slots t j : ℝ) ^ 2 <
      (N : ℝ) ^ cap p (coordinates N t)) ∧
    (p.val < 15 → ∀ j : Fin 4, ¬Selected p j →
      (selectedProduct p t : ℝ) * (earlierRemainderProduct p j t : ℝ) * (slots t j : ℝ) ^ 2 <
        (N : ℝ) ^ cap p (coordinates N t)) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hp : ∀ i, (slots t i : ℝ) ≤ (N : ℝ) ^ coordinates N t i := by
    intro i
    exact le_of_eq (actualPrimeTupleLog_rpow hN (slots t) (slots_pos ht) i).symm
  constructor
  · intro j
    have hg := he.2.1 j
    rw [fullSquare_eq_generic] at hg
    simpa only [prefixProduct,prefixIndices,Fin.lt_def] using
      prefixSquareExpr_actual_gate (N : ℝ) hNr (slots t) (coordinates N t) hp j hg
  · intro hmask j hj
    have hselected : ∀ j : Fin 4, ¬Selected p j →
        selectedSquare p j (coordinates N t) < cap p (coordinates N t) := by
      simpa only [if_pos hmask] using he.2.2
    have hg := hselected j hj
    rw [selectedSquare_eq_generic] at hg
    simpa only [selectedProduct,earlierRemainderProduct,earlierRemainderIndices,
      selectedIndices,Finset.mem_filter,Finset.mem_univ,true_and,Fin.lt_def] using
      selectedSquareExpr_actual_gate (selectedIndices p) (N : ℝ) hNr (slots t)
        (coordinates N t) hp j hg

/-- The residual ordinary sieve is strictly below the smallest specified
prime. Thus the full specified prefix and its two actual mask blocks are
coprime to every actual residual Rosser divisor; no overlap is ignored. -/
theorem fullPrefix_coprime_lowered_sieve {N : ℕ} {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) {Z : ℝ} (hZ : Z ≤ (slots t 3 : ℝ)) :
    Nat.Coprime (fullPrefix t) (sieveProduct N (Nat.ceil Z)) := by
  apply chen_prime_product_coprime_sieveProduct Finset.univ (slots t) N Z
  intro i _
  refine ⟨slots_prime ht i, hZ.trans ?_⟩
  exact_mod_cast (slots_strictAnti ht).antitone (show i ≤ (3 : Fin 4) by omega)

theorem residual_totient_dictionary {N d : ℕ} {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) (p : Policy) {Z : ℝ} (hZ : Z ≤ (slots t 3 : ℝ))
    (hd : d ∈ actualSmallRosserSupport N (Nat.ceil Z) Z) :
    Nat.totient (fullPrefix t * d) = Nat.totient (selectedProduct p t) *
      Nat.totient (remainderProduct p t) * Nat.totient d := by
  have hdvd : d ∣ sieveProduct N (Nat.ceil Z) := by
    have h := (Nat.mem_divisors.mp hd).1
    rwa [currentChen_actualSmallPrimeProduct_eq_sieveProduct N (Nat.ceil Z) Z (Nat.le_ceil Z)] at h
  rw [Nat.totient_mul (chenQuotient_allowed_coprime
    (fullPrefix_coprime_lowered_sieve ht hZ) hdvd),selected_remainder_totient ht p]

end
end ImbalancedChen.P5Z.U1011OriginalSixteenArithmeticProducts
