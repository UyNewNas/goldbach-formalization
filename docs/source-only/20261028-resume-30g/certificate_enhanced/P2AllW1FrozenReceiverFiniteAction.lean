import ImbalancedChen.P2FrozenReceiverCountActions
import ImbalancedChen.P5OriginalActionMassBound

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The genuine finite three-prime weight at every original7-by10 W1 pair.
The receiver is frozen, negative children use their actual same-Q Rosser
level, and the positive term retains its ORIGINAL quotient mask d*N*q1.
It is not identified with an absolutely rough strict positiveTripleWords
tail. Old-prefix and q1-exempt repetitions still require their actual
count conversion/payment before a positive-K I/8 bound can be inferred.
-/
namespace ImbalancedChen.P2AllW1FrozenReceiverFiniteAction

noncomputable section
open Finset Wu2008DoubleSieve
open P2FrozenReceiverCountActions
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2EnhancedActualBuchstabTransfer (childWindow childLevel child_level_geometry)
open P5OriginalActionMassBound (W1Target W1Anchor)
open scoped Classical BigOperators

/-- This is the actual raw positive triple count. Its mask still exempts
the old prefix and the first selected triple prime below the middle. -/
def rawTripleCount (N d M : ℕ) (E : ℕ → Prop) (z w : ℝ) : ℤ :=
  ∑ t∈orderedTriples (primeWindow M z w),
    quotientCount N (d*(t.1*t.2.1*t.2.2)) (M*t.1) E (t.2.1:ℝ)

/-- The generic finite three-prime theorem is applied to the actual
receiver-filtered carrier. No count estimate or K cost is a premise. -/
theorem frozen_three_prime_weight (N d M : ℕ) (E : ℕ → Prop)
    {z w : ℝ} (hzw : z≤w) :
    2*quotientCount N d M E w≤2*quotientCount N d M E z-
      (∑ q∈primeWindow M z w,quotientCount N (d*q) M E z)+rawTripleCount N d M E z w := by
  have h := finite_three_prime_upper_weight ((sieveCarrier N d M z).filter E)
    (fun ell => (N-ell)/d) (primeWindow M z w)
  have hs : siftedIndices ((sieveCarrier N d M z).filter E)
      (fun ell => (N-ell)/d) (primeWindow M z w) = (sieveCarrier N d M w).filter E := by
    rw [←siftedIndices_sieveCarrier N d M hzw]
    ext ell
    simp only [siftedIndices,mem_filter]
    tauto
  have hsingle : singleMass ((sieveCarrier N d M z).filter E)
      (fun ell => (N-ell)/d) (primeWindow M z w) =
      ∑ q∈primeWindow M z w,quotientCount N (d*q) M E z := by
    unfold singleMass
    apply sum_congr rfl
    intro q hq
    have hf : ((sieveCarrier N d M z).filter E).filter (fun ell => q∣(N-ell)/d) =
        ((sieveCarrier N d M z).filter (fun ell => q∣(N-ell)/d)).filter E := by
      ext ell
      simp only [mem_filter]
      tauto
    rw [hf,singleCarrier_eq N d M (mem_primeWindow.mp hq).1 (mem_primeWindow.mp hq).2.2.1]
    rfl
  have htriple : tripleMass ((sieveCarrier N d M z).filter E)
      (fun ell => (N-ell)/d) (primeWindow M z w)=rawTripleCount N d M E z w := by
    unfold tripleMass rawTripleCount
    apply sum_congr rfl
    rintro ⟨a,b,c⟩ ht
    have hf : ((sieveCarrier N d M z).filter E).filter
        (fun ell => tripleSurvives (primeWindow M z w) ((N-ell)/d) (a,b,c)) =
        ((sieveCarrier N d M z).filter
          (fun ell => tripleSurvives (primeWindow M z w) ((N-ell)/d) (a,b,c))).filter E := by
      ext ell
      simp only [mem_filter]
      tauto
    rw [hf,tripleCarrier_eq N d M ht]
    rfl
  rw [hs,hsingle,htriple] at h
  exact h

/-- A newly selected q lies above the negative child's strict cutoff.
Only then may its factor be added to the mask without changing the count. -/
theorem negative_child_eq_frozen (N d : ℕ) (E : ℕ → Prop) {q : ℕ} {z : ℝ}
    (hq : q.Prime) (hzq : z≤(q:ℝ)) :
    quotientCount N (d*q) (d*N) E z=frozenCount N (d*q) E z := by
  have hsel : Sifted (d*N) (d*q) z := by
    rw [sifted_mul_iff]
    refine ⟨?_,sifted_prime_of_le hq hzq⟩
    intro r hr hc hrz
    exact siftedLE_of_dvd_modulus (dvd_mul_right d N) z r hr hc hrz.le
  have heq := sourceSieveCarrier_eq_ite N (d*q) (d*N) z
  rw [if_pos hsel] at heq
  have hprod : ordinarySievePrimeProduct ((d*q)*N) z=ordinarySievePrimeProduct (d*N) z := by
    unfold ordinarySievePrimeProduct
    rw [show (d*q)*N=q*(d*N) by ring,primeWindow_mul_of_prime_above (d*N) hq hzq]
  have hc : sourceSieveCarrier N (d*q) ((d*q)*N) z=
      sourceSieveCarrier N (d*q) (d*N) z := by
    ext ell
    simp only [sourceSieveCarrier,mem_filter,sifted_iff_product_coprime,hprod]
  unfold quotientCount frozenCount frozenCarrier
  rw [hc,heq]

theorem frozen_selected_three_prime_weight (N d : ℕ) (E : ℕ → Prop)
    {z w : ℝ} (hzw : z≤w) :
    2*frozenCount N d E w≤2*frozenCount N d E z-
      (∑ q∈primeWindow (d*N) z w,frozenCount N (d*q) E z)+rawTripleCount N d (d*N) E z w := by
  have h := frozen_three_prime_weight N d (d*N) E hzw
  have hd (x : ℝ) : quotientCount N d (d*N) E x=frozenCount N d E x := by
    unfold quotientCount frozenCount frozenCarrier
    rw [(source_double_sieve_carriers N d x).1]
  rw [hd w,hd z] at h
  have hsingle : (∑ q∈primeWindow (d*N) z w,quotientCount N (d*q) (d*N) E z)=
      ∑ q∈primeWindow (d*N) z w,frozenCount N (d*q) E z := by
    apply sum_congr rfl
    intro q hq
    exact negative_child_eq_frozen N d E (mem_primeWindow.mp hq).1 (mem_primeWindow.mp hq).2.2.1
  rw [hsingle] at h
  exact h

theorem original_W1_parameters (i : Fin 7) (j : Fin 10) :
    2≤W1Target i ∧ W1Target i≤W1Anchor j ∧ W1Anchor j≤5 := by
  have hi0 : (0:ℝ)≤i.val := Nat.cast_nonneg _
  have hi6 : (i.val:ℝ)≤6 := by exact_mod_cast (show i.val≤6 by omega)
  have hj0 : (0:ℝ)≤j.val := Nat.cast_nonneg _
  have hj9 : (j.val:ℝ)≤9 := by exact_mod_cast (show j.val≤9 by omega)
  dsimp [W1Target,W1Anchor]
  constructor
  · linarith
  · constructor <;> linarith

def negativePolynomial (N : ℕ) (Q : ℝ) (d : ℕ) (E : ℕ → Prop)
    (i : Fin 7) (j : Fin 10) : ℝ :=
  ∑ q∈childWindow N d Q (W1Target i) (W1Anchor j),
    frozenPolynomial false N (d*q) (childLevel Q d q) E (cutoff Q d (W1Anchor j))

/-- This comparison uses each actual child coefficient at its true full
Q/(d*q) level and its original anchor cutoff, keeping signed discrepancy. -/
theorem negativePolynomial_le_actual (N : ℕ) (Q : ℝ) (d : ℕ) (E : ℕ → Prop)
    (i : Fin 7) (j : Fin 10) (hd : 0<d) (hR : 1<Q/(d:ℝ)) :
    negativePolynomial N Q d E i j≤
      ∑ q∈childWindow N d Q (W1Target i) (W1Anchor j),
        (frozenCount N (d*q) E (cutoff Q d (W1Anchor j)):ℝ) := by
  unfold negativePolynomial
  apply sum_le_sum
  intro q hq
  have hzq := (mem_primeWindow.mp hq).2.2.1
  have hlevel := child_level_geometry hd hR (original_W1_parameters i j).1 hq
  exact frozenRosser_lower_finite E (hzq.trans hlevel.2)

/-- Every original W1 pair is a genuine same-Q frozen-receiver count
action. The raw positive count remains explicit; a K I/8 licence has not
been inserted in place of this arithmetic source. -/
theorem original_W1_actual_count_action (N : ℕ) (Q : ℝ) (d : ℕ) (E : ℕ → Prop)
    (i : Fin 7) (j : Fin 10) (hd : 0<d) (hR : 1<Q/(d:ℝ)) :
    (frozenCount N d E (cutoff Q d (W1Target i)):ℝ)≤
      (frozenCount N d E (cutoff Q d (W1Anchor j)):ℝ)-negativePolynomial N Q d E i j/2+
        (rawTripleCount N d (d*N) E (cutoff Q d (W1Anchor j))
          (cutoff Q d (W1Target i)):ℝ)/2 := by
  have hp := original_W1_parameters i j
  have hcut : cutoff Q d (W1Anchor j)≤cutoff Q d (W1Target i) :=
    Real.rpow_le_rpow_of_exponent_le hR.le
      (one_div_le_one_div_of_le (by linarith : 0<W1Target i) hp.2.1)
  have h := frozen_selected_three_prime_weight N d E hcut
  have hRcast : 2*(frozenCount N d E (cutoff Q d (W1Target i)):ℝ)≤
      2*(frozenCount N d E (cutoff Q d (W1Anchor j)):ℝ)-
      (∑ q∈childWindow N d Q (W1Target i) (W1Anchor j),
        (frozenCount N (d*q) E (cutoff Q d (W1Anchor j)):ℝ))+
      (rawTripleCount N d (d*N) E (cutoff Q d (W1Anchor j)) (cutoff Q d (W1Target i)):ℝ) := by
    exact_mod_cast h
  have hnegative := negativePolynomial_le_actual N Q d E i j hd hR
  linarith

def markedNegative {ι : Type*} (N : ℕ) (Q : ℝ) (L : Finset ι)
    (B : ι → ℕ) (sigma : ι → ℝ) (E : ι → ℕ → Prop) (i : Fin 7) (j : Fin 10) : ℝ :=
  ∑ a∈L,sigma a*negativePolynomial N Q (B a) (E a) i j

def markedRawPositive {ι : Type*} (N : ℕ) (Q : ℝ) (L : Finset ι)
    (B : ι → ℕ) (sigma : ι → ℝ) (E : ι → ℕ → Prop) (i : Fin 7) (j : Fin 10) : ℝ :=
  ∑ a∈L,sigma a*(rawTripleCount N (B a) (B a*N) (E a)
    (cutoff Q (B a) (W1Anchor j)) (cutoff Q (B a) (W1Target i)):ℝ)

/-- All7*10 original actions, retaining each label, receiver and sigma
occurrence. This is the actual finite count step before analytic costs. -/
theorem all70_original_W1_marked_count_actions {ι : Type*} (N : ℕ) (Q : ℝ) (L : Finset ι)
    (B : ι → ℕ) (sigma : ι → ℝ) (E : ι → ℕ → Prop)
    (hB : ∀a∈L,0<B a) (hsigma : ∀a∈L,0≤sigma a) (hR : ∀a∈L,1<Q/(B a:ℝ))
    (i : Fin 7) (j : Fin 10) :
    markedPhi N Q L B sigma E (W1Target i)≤markedPhi N Q L B sigma E (W1Anchor j)-
      markedNegative N Q L B sigma E i j/2+markedRawPositive N Q L B sigma E i j/2 := by
  have hlocal (a : ι) (ha : a∈L) := mul_le_mul_of_nonneg_left
    (original_W1_actual_count_action N Q (B a) (E a) i j (hB a ha) (hR a ha))
    (hsigma a ha)
  have h := sum_le_sum hlocal
  have heq : (∑ a∈L,sigma a*((frozenCount N (B a) (E a) (cutoff Q (B a) (W1Anchor j)):ℝ)-
      negativePolynomial N Q (B a) (E a) i j/2+
        (rawTripleCount N (B a) (B a*N) (E a) (cutoff Q (B a) (W1Anchor j))
          (cutoff Q (B a) (W1Target i)):ℝ)/2)) =
      markedPhi N Q L B sigma E (W1Anchor j)-markedNegative N Q L B sigma E i j/2+
        markedRawPositive N Q L B sigma E i j/2 := by
    simp only [markedPhi,markedNegative,markedRawPositive,mul_add,mul_sub,mul_div_assoc,
      sum_add_distrib,sum_sub_distrib,sum_div]
  rw [heq] at h
  exact h

end
end ImbalancedChen.P2AllW1FrozenReceiverFiniteAction
