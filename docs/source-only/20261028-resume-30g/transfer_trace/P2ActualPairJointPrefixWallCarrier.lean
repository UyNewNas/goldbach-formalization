import ImbalancedChen.P2CanonicalTentFiniteCapsAndCoarsePayment

/-!
# Genuine U6 pair-root / canonical rough joint-prefix wall carrier

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The external pair is not put into the rough tail or deleted from its
physical modulus. Its original disjoint A,H,D bands precede the complete
canonical rough word. Strict order supplies distinct labels, and the
actual full prime product supplies the prefix/tail coprimality. Thus a
wall on the JOINT coordinates has a fixed intercept; a pairRoot(N,p) sum
is never silently treated as a constant independent of N.

This carrier statement is independent of any successful selector or
adopted-bank identity, and asserts neither full W coverage nor total rho
density convergence.
-/

namespace ImbalancedChen.P2ActualPairJointPrefixWallCarrier

noncomputable section
open scoped Classical BigOperators
open P2LowerFiniteCellRounding P2LowerCanonicalRetainedTrace
open P2LowerCapPlanIntegerRetention P2CanonicalWallFullResidualPayment
open P5SelectedMaskTransport

def aExponent : ℝ := 417 / 5000
def hExponent : ℝ := 19 / 125
def dExponent : ℝ := 59 / 250

def fullWord (p : ℕ × ℕ) (r : ℕ) : List ℕ :=
  p.2 :: p.1 :: r.primeFactorsList.reverse

def jointWord (j : ℕ) (p : ℕ × ℕ) (r : ℕ) : List ℕ :=
  p.2 :: p.1 :: r.primeFactorsList.reverse.take j

def jointPrefix (j : ℕ) (p : ℕ × ℕ) (r : ℕ) : Fin (2 + j) → ℕ :=
  primeHistoryTuple (2 + j) (jointWord j p r).reverse

private theorem root_and_rough_data {N enum r : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ sixthSupport N) {omega : ℝ}
    (hr : r ∈ universe N enum ((N : ℝ) ^ omega) ((N : ℝ) ^ aExponent)) :
    Nat.Prime p.1 ∧ Nat.Prime p.2 ∧ ¬p.1 ∣ N ∧ ¬p.2 ∣ N ∧
      (N : ℝ) ^ aExponent ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) < (N : ℝ) ^ hExponent ∧
      (N : ℝ) ^ hExponent ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) < (N : ℝ) ^ dExponent ∧
      (∀ q ∈ r.primeFactorsList.reverse,
        Nat.Prime q ∧ ¬q ∣ N ∧ (N : ℝ) ^ omega ≤ (q : ℝ) ∧
          (q : ℝ) < (N : ℝ) ^ aExponent) ∧
      r.primeFactorsList.reverse.Pairwise (· > ·) ∧ r.primeFactorsList.reverse.prod = r := by
  obtain ⟨hpair, ha, h1, h2, hd⟩ := Finset.mem_filter.mp hp
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hpair
  have hc1 := mem_chenAdditivePrimeCarrier.mp hp1
  have hc2 := mem_chenAdditivePrimeCarrier.mp hp2
  obtain ⟨hsub, hprod⟩ := canonical_subword_of_universe N enum _ _ hr
  refine ⟨hc1.2.1, hc2.2.1,
    hc1.2.1.coprime_iff_not_dvd.mp hc1.2.2,
    hc2.2.1.coprime_iff_not_dvd.mp hc2.2.2, ha, h1, h2, hd, ?_, ?_, hprod⟩
  · intro q hq
    exact (mem_roughPrimeUniverse.mp (hsub.subset hq)).2
  · exact (roughPrimeUniverse_pairwise_gt N enum _ _).sublist hsub

/-- These are the actual complete physical prime factors in chronological
decreasing order. No pair-root or rough-support licence is an input. -/
theorem fullWord_data {N enum r : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ sixthSupport N) {omega : ℝ}
    (hr : r ∈ universe N enum ((N : ℝ) ^ omega) ((N : ℝ) ^ aExponent)) :
    (fullWord p r).Pairwise (· > ·) ∧
      (∀ q ∈ fullWord p r, Nat.Prime q) ∧
      (fullWord p r).prod = (p.1 * p.2) * r := by
  obtain ⟨hp1, hp2, hn1, hn2, ha, h1, h2, hd, hrough, hsort, hprod⟩ :=
    root_and_rough_data hp hr
  have h12 : p.1 < p.2 := by exact_mod_cast h1.trans_le h2
  have hq1 : ∀ q ∈ r.primeFactorsList.reverse, q < p.1 := by
    intro q hq
    exact_mod_cast (hrough q hq).2.2.2.trans_le ha
  refine ⟨?_, ?_, ?_⟩
  · apply List.pairwise_cons.mpr
    constructor
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact h12
      · exact (hq1 q hq).trans h12
    · exact List.pairwise_cons.mpr ⟨hq1, hsort⟩
  · intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hp2
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hp1
    · exact (hrough q hq).1
  · simp only [fullWord, List.prod_cons, hprod]
    ring

theorem jointPrefix_ofFn {j r : ℕ} (p : ℕ × ℕ)
    (hj : j ≤ r.primeFactorsList.length) :
    List.ofFn (jointPrefix j p r) = jointWord j p r := by
  have hlen : (jointWord j p r).reverse.length = 2 + j := by
    simp only [jointWord, List.length_reverse, List.length_cons,
      List.length_take, Nat.min_eq_left hj]
    omega
  simpa only [jointPrefix, List.reverse_reverse] using primeHistoryTuple_ofFn hlen

/-- The original external bands and real rough cutoffs produce a genuine
joint prime tuple, distinct labels, full residual divisor and exact product. -/
theorem joint_prefix_tail_data {N enum j r : ℕ} {p : ℕ × ℕ}
    (hN : 1 < (N : ℝ)) (hp : p ∈ sixthSupport N)
    {omega : ℝ} (homega : omega ≤ aExponent)
    (hr : r ∈ universe N enum ((N : ℝ) ^ omega) ((N : ℝ) ^ aExponent))
    (hj : j ≤ r.primeFactorsList.length) :
    jointPrefix j p r ∈ actualPrimeBoxTuples N (fun _ => omega) (fun _ => dExponent) ∧
      Function.Injective (jointPrefix j p r) ∧
      canonicalTail j r ∈ universe N enum ((N : ℝ) ^ omega) ((N : ℝ) ^ aExponent) ∧
      Nat.Coprime (∏ i, jointPrefix j p r i) (canonicalTail j r) ∧
      (∏ i, jointPrefix j p r i) * canonicalTail j r = (p.1 * p.2) * r := by
  obtain ⟨hp1, hp2, hn1, hn2, ha, h1, h2, hd, hrough, hsort, hprod⟩ :=
    root_and_rough_data hp hr
  have hAH : (N : ℝ) ^ aExponent ≤ (N : ℝ) ^ hExponent :=
    Real.rpow_le_rpow_of_exponent_le hN.le (by norm_num [aExponent, hExponent])
  have hHD : (N : ℝ) ^ hExponent ≤ (N : ℝ) ^ dExponent :=
    Real.rpow_le_rpow_of_exponent_le hN.le (by norm_num [hExponent, dExponent])
  have hlow : (N : ℝ) ^ omega ≤ (N : ℝ) ^ aExponent :=
    Real.rpow_le_rpow_of_exponent_le hN.le homega
  have hof := jointPrefix_ofFn p hj
  have hsub : jointWord j p r <+ fullWord p r :=
    List.Sublist.cons₂ _ (List.Sublist.cons₂ _ (List.take_sublist j _))
  obtain ⟨hfullsort, hfullprime, hfullprod⟩ := fullWord_data hp hr
  have hinj : Function.Injective (jointPrefix j p r) := by
    have hs : (List.ofFn (jointPrefix j p r)).Pairwise (· > ·) := by
      rw [hof]
      exact hfullsort.sublist hsub
    exact (List.pairwise_ofFn.mp hs).injective
  have htuple : jointPrefix j p r ∈
      actualPrimeBoxTuples N (fun _ => omega) (fun _ => dExponent) := by
    apply mem_actualPrimeBoxTuples_iff.mpr
    intro i
    have hm : jointPrefix j p r i ∈ jointWord j p r := by
      rw [← hof]
      exact List.mem_ofFn.mpr ⟨i, rfl⟩
    rcases List.mem_cons.mp hm with hm | hm
    · rw [hm]
      exact ⟨hp2, hn2, hlow.trans (ha.trans (h1.le.trans h2)), hd⟩
    rcases List.mem_cons.mp hm with hm | hm
    · rw [hm]
      exact ⟨hp1, hn1, hlow.trans ha, h1.trans_le hHD⟩
    · have hq := hrough _ ((List.take_sublist j _).subset hm)
      exact ⟨hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.trans_le (hAH.trans hHD)⟩
  have hrec : (∏ i, jointPrefix j p r i) * canonicalTail j r = (p.1 * p.2) * r := by
    rw [← List.prod_ofFn, hof]
    have hsplit : (r.primeFactorsList.reverse.take j).prod *
        (r.primeFactorsList.reverse.drop j).prod = r := by
      rw [← List.prod_append, List.take_append_drop]
      exact hprod
    simp only [jointWord, List.prod_cons, canonicalTail]
    calc
      p.2 * (p.1 * (r.primeFactorsList.reverse.take j).prod) *
          (r.primeFactorsList.reverse.drop j).prod =
          (p.1 * p.2) * ((r.primeFactorsList.reverse.take j).prod *
            (r.primeFactorsList.reverse.drop j).prod) := by ring
      _ = (p.1 * p.2) * r := by rw [hsplit]
  have hfullsf : Squarefree ((p.1 * p.2) * r) := by
    rw [← hfullprod]
    exact list_prod_squarefree_of_nodup_primes _ hfullsort.nodup hfullprime
  have hcop : Nat.Coprime (∏ i, jointPrefix j p r i) (canonicalTail j r) := by
    apply Nat.coprime_of_squarefree_mul
    rwa [hrec]
  have htail := (canonical_prefix_tail_data hr hj).2.2.1
  exact ⟨htuple, hinj, htail, hcop, hrec⟩

/-- The full physical modulus determines the original two external primes
and rough divisor uniquely, by the original disjoint prime bands. -/
theorem pair_rough_product_injOn (N enum : ℕ) (omega : ℝ) :
    Set.InjOn (fun x : (ℕ × ℕ) × ℕ => (x.1.1 * x.1.2) * x.2)
      (sixthSupport N ×ˢ universe N enum ((N : ℝ) ^ omega) ((N : ℝ) ^ aExponent)) := by
  intro x hx y hy heq
  obtain ⟨hpx, hrx⟩ := Finset.mem_product.mp hx
  obtain ⟨hpy, hry⟩ := Finset.mem_product.mp hy
  obtain ⟨hsx, hqx, hprodX⟩ := fullWord_data hpx hrx
  obtain ⟨hsy, hqy, hprodY⟩ := fullWord_data hpy hry
  have hpermX := Nat.primeFactorsList_unique hprodX hqx
  have hprodY' : (fullWord y.1 y.2).prod = (x.1.1 * x.1.2) * x.2 :=
    hprodY.trans heq.symm
  have hpermY := Nat.primeFactorsList_unique hprodY' hqy
  have hw := (hpermX.trans hpermY.symm).eq_of_pairwise'
    (hsx.imp (fun h => h.le)) (hsy.imp (fun h => h.le))
  have htwo := List.cons.inj hw
  have hone := List.cons.inj htwo.2
  have hrxy : x.2 = y.2 := by
    have hp := congrArg List.prod hone.2
    have hxprod := (canonical_subword_of_universe N enum _ _ hrx).2
    have hyprod := (canonical_subword_of_universe N enum _ _ hry).2
    simpa only [hxprod, hyprod] using hp
  exact Prod.ext (Prod.ext hone.1 htwo.1) hrxy

end
end ImbalancedChen.P2ActualPairJointPrefixWallCarrier
