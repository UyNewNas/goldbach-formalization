import ImbalancedChen.ActualExtendedThirdDistinctPrimeHarmonic

/-!
# The original strictly ordered prefix product harmonic dictionary

Strictly ordered prime triples have distinct products.  We prove that
fact using prime factor uniqueness and the actual strict ordering; no
factorial or permutation count is inserted.  The literal finite prime
sum is then transported to its own product image with exactly 1/phi(n)
and the same nonlinear test at the uniquely recovered original triple.

This is a finite arithmetic dictionary and its harmonic limit.  It
does not identify the full signed first-exit sieve coefficient or pay
its physical counting remainder.
-/

namespace ImbalancedChen

noncomputable section

open Set Filter Topology
open scoped Classical BigOperators

def actualExtendedThirdDistinctCellPrimeTuples (N : ℕ) (h : ℝ) (m : ℕ)
    (j : ActualExtendedThirdDyadicLabel m) : Finset (Fin 3 → ℕ) :=
  (actualPrimeBoxTuples N (fun _ : Fin 3 => h / 2) (fun _ => thirdPrefixRho + 1)).filter
    (fun p => actualPrimeTupleLog N p ∈ actualExtendedThirdDistinctCellPrimeRegion m j)

def actualExtendedThirdDistinctCellPrimeProducts (N : ℕ) (h : ℝ) (m : ℕ)
    (j : ActualExtendedThirdDyadicLabel m) : Finset ℕ :=
  (actualExtendedThirdDistinctCellPrimeTuples N h m j).image (fun p => ∏ i : Fin 3, p i)

private theorem descending_three_pairwise {a b c : ℕ} (hba : b < a) (hcb : c < b) :
    [a, b, c].Pairwise (fun x y => y ≤ x) := by
  apply List.pairwise_cons.mpr
  constructor
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hba.le
    · have hx' : x = c := List.mem_singleton.mp hx
      subst x
      exact (hcb.trans hba).le
  · exact List.pairwise_pair.mpr hcb.le

/-- This is injectivity on the actual arithmetic selector, including its
owned cell endpoints and the original target-divisor exclusions. -/
theorem actualExtendedThirdDistinctCellPrimeTuples_product_injOn {N : ℕ}
    (hN : 1 < N) (h : ℝ) (m : ℕ) (j : ActualExtendedThirdDyadicLabel m) :
    Set.InjOn (fun p : Fin 3 → ℕ => ∏ i, p i)
      (actualExtendedThirdDistinctCellPrimeTuples N h m j) := by
  intro p hp q hq hpq
  obtain ⟨hpbox, hpregion⟩ := Finset.mem_filter.mp hp
  obtain ⟨hqbox, hqregion⟩ := Finset.mem_filter.mp hq
  obtain ⟨hp10, hp21⟩ := actualExtendedThirdDistinctCellPrimeRegion_prime_order hN hpbox hpregion
  obtain ⟨hq10, hq21⟩ := actualExtendedThirdDistinctCellPrimeRegion_prime_order hN hqbox hqregion
  have hpprime (i : Fin 3) : Nat.Prime (p i) := (mem_actualPrimeBoxTuples_iff.mp hpbox i).1
  have hqprime (i : Fin 3) : Nat.Prime (q i) := (mem_actualPrimeBoxTuples_iff.mp hqbox i).1
  have hpl : ∀ a ∈ [p 0, p 1, p 2], Nat.Prime a := by
    intro a ha
    simp only [List.mem_cons, List.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact hpprime 0
    · exact hpprime 1
    · exact hpprime 2
  have hql : ∀ a ∈ [q 0, q 1, q 2], Nat.Prime a := by
    intro a ha
    simp only [List.mem_cons, List.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact hqprime 0
    · exact hqprime 1
    · exact hqprime 2
  have hprod : [p 0, p 1, p 2].prod = [q 0, q 1, q 2].prod := by
    simpa only [List.prod_cons, List.prod_nil, mul_one, Fin.prod_univ_three, mul_assoc] using hpq
  have hperm := (Nat.primeFactorsList_unique hprod hpl).trans
    (Nat.primeFactorsList_unique rfl hql).symm
  have heq : [p 0, p 1, p 2] = [q 0, q 1, q 2] :=
    List.Perm.eq_of_pairwise (fun _ _ _ _ hab hba => Nat.le_antisymm hba hab)
      (descending_three_pairwise hp10 hp21) (descending_three_pairwise hq10 hq21) hperm
  have hc : p 0 = q 0 ∧ p 1 = q 1 ∧ p 2 = q 2 := by
    simpa only [List.cons.injEq, and_true] using heq
  funext i
  fin_cases i
  · exact hc.1
  · exact hc.2.1
  · exact hc.2.2

/-- Outside the actual product carrier the total representative is zero.
On the carrier its membership and exact product are proved below. -/
def actualExtendedThirdDistinctCellProductTuple (N : ℕ) (h : ℝ) (m : ℕ)
    (j : ActualExtendedThirdDyadicLabel m) (n : ℕ) : Fin 3 → ℕ :=
  if hn : n ∈ actualExtendedThirdDistinctCellPrimeProducts N h m j then
    Classical.choose (Finset.mem_image.mp hn)
  else fun _ => 0

theorem actualExtendedThirdDistinctCellProductTuple_spec {N : ℕ} {h : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} {n : ℕ}
    (hn : n ∈ actualExtendedThirdDistinctCellPrimeProducts N h m j) :
    actualExtendedThirdDistinctCellProductTuple N h m j n ∈
        actualExtendedThirdDistinctCellPrimeTuples N h m j ∧
      (∏ i : Fin 3, actualExtendedThirdDistinctCellProductTuple N h m j n i) = n := by
  simpa only [actualExtendedThirdDistinctCellProductTuple, dif_pos hn] using
    Classical.choose_spec (Finset.mem_image.mp hn)

theorem actualExtendedThirdDistinctCellProductTuple_product {N : ℕ} (hN : 1 < N)
    {h : ℝ} {m : ℕ} {j : ActualExtendedThirdDyadicLabel m} {p : Fin 3 → ℕ}
    (hp : p ∈ actualExtendedThirdDistinctCellPrimeTuples N h m j) :
    actualExtendedThirdDistinctCellProductTuple N h m j (∏ i : Fin 3, p i) = p := by
  have hn : (∏ i : Fin 3, p i) ∈ actualExtendedThirdDistinctCellPrimeProducts N h m j :=
    Finset.mem_image.mpr ⟨p, hp, rfl⟩
  have hs := actualExtendedThirdDistinctCellProductTuple_spec hn
  exact actualExtendedThirdDistinctCellPrimeTuples_product_injOn hN h m j hs.1 hp hs.2

/-- Arbitrary signed tests of the original triple are preserved, rather
than replaced by a product-only test or by a supremum. -/
theorem actualExtendedThirdDistinctCellPrimeTuples_totient_sum {N : ℕ}
    (hN : 1 < N) (h : ℝ) (m : ℕ) (j : ActualExtendedThirdDyadicLabel m)
    (G : (Fin 3 → ℕ) → ℝ) :
    (∑ p ∈ actualExtendedThirdDistinctCellPrimeTuples N h m j,
      (∏ i : Fin 3, 1 / ((p i : ℝ) - 1)) * G p) =
      ∑ n ∈ actualExtendedThirdDistinctCellPrimeProducts N h m j,
        1 / (Nat.totient n : ℝ) * G (actualExtendedThirdDistinctCellProductTuple N h m j n) := by
  rw [actualExtendedThirdDistinctCellPrimeProducts,
    Finset.sum_image (actualExtendedThirdDistinctCellPrimeTuples_product_injOn hN h m j)]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hpbox, hpregion⟩ := Finset.mem_filter.mp hp
  rw [actualExtendedThirdDistinctCellProductTuple_product hN hp,
    actualExtendedThirdDistinctCellPrimeRegion_weight hN hpbox hpregion]

def actualExtendedThirdDistinctCellProductHarmonicSum (N : ℕ) (e h : ℝ) (m : ℕ)
    (j : ActualExtendedThirdDyadicLabel m) : ℝ :=
  ∑ n ∈ actualExtendedThirdDistinctCellPrimeProducts N h m j,
    1 / (Nat.totient n : ℝ) *
      actualExtendedThirdCompactHarmonicProfile e h (actualExtendedThirdPhysicalLevel e m j)
        (actualPrimeTupleLog N (actualExtendedThirdDistinctCellProductTuple N h m j n))

theorem actualExtendedThirdDistinctCellProductHarmonicSum_eq {N : ℕ} (hN : 1 < N)
    (e h : ℝ) (m : ℕ) (j : ActualExtendedThirdDyadicLabel m) :
    actualExtendedThirdDistinctCellProductHarmonicSum N e h m j =
      actualExtendedThirdDistinctCellPrimeSum N e h m j := by
  rw [actualExtendedThirdDistinctCellProductHarmonicSum,
    ← actualExtendedThirdDistinctCellPrimeTuples_totient_sum hN]
  rw [actualExtendedThirdDistinctCellPrimeSum, actualPrimeBoxTestSum,
    actualExtendedThirdDistinctCellPrimeTuples, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : actualPrimeTupleLog N p ∈ actualExtendedThirdDistinctCellPrimeRegion m j
  · rw [if_pos hp, Set.indicator_of_mem hp]
  · rw [if_neg hp, Set.indicator_of_notMem hp, mul_zero]

theorem tendsto_actualExtendedThirdDistinctCellProductHarmonicSum {e h : ℝ} {m : ℕ}
    (hh : 0 < h) {j : ActualExtendedThirdDyadicLabel m}
    (hj : j ∈ actualExtendedThirdCompactCells e h m) :
    Tendsto (fun N : ℕ => actualExtendedThirdDistinctCellProductHarmonicSum N e h m j) atTop
      (𝓝 (actualExtendedThirdRetainedCellIntegral e m j)) := by
  apply (tendsto_actualExtendedThirdDistinctCellPrimeSum hh hj).congr'
  filter_upwards [eventually_gt_atTop 1] with N hN
  exact (actualExtendedThirdDistinctCellProductHarmonicSum_eq hN e h m j).symm

def actualExtendedThirdDistinctCompactProductHarmonicSum (N : ℕ) (e h : ℝ) (m : ℕ) : ℝ :=
  ∑ j ∈ actualExtendedThirdCompactCells e h m,
    actualExtendedThirdDistinctCellProductHarmonicSum N e h m j

theorem actualExtendedThirdDistinctCompactProductHarmonicSum_eq {N : ℕ} (hN : 1 < N)
    (e h : ℝ) (m : ℕ) :
    actualExtendedThirdDistinctCompactProductHarmonicSum N e h m =
      actualExtendedThirdDistinctCompactPrimeSum N e h m := by
  apply Finset.sum_congr rfl
  intro j _
  exact actualExtendedThirdDistinctCellProductHarmonicSum_eq hN e h m j

theorem tendsto_actualExtendedThirdDistinctCompactProductHarmonicSum {e h : ℝ}
    (hh : 0 < h) (he0 : 0 ≤ e) (he : e ≤ 1 / 384) (m : ℕ) :
    Tendsto (fun N : ℕ => actualExtendedThirdDistinctCompactProductHarmonicSum N e h m) atTop
      (𝓝 (actualExtendedThirdCompactCellFunctional e h m)) := by
  apply (tendsto_actualExtendedThirdDistinctCompactPrimeSum hh he0 he m).congr'
  filter_upwards [eventually_gt_atTop 1] with N hN
  exact (actualExtendedThirdDistinctCompactProductHarmonicSum_eq hN e h m).symm

/-- All cutoffs and the finite owned grid are chosen before N.  The same
nonlinear manuscript functional is recovered on the literal product carrier. -/
theorem exists_actualExtendedThirdDistinctCompactProductHarmonicSum_approx_ideal
    {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℝ, 0 < h ∧ ∃ e : ℝ, 0 < e ∧ e ≤ 1 / 384 ∧ ∃ m : ℕ,
      ∀ᶠ N : ℕ in atTop,
        |actualExtendedThirdDistinctCompactProductHarmonicSum N e h m -
          actualExtendedThirdIdealFunctional| ≤ ε := by
  obtain ⟨h, hh, e, he0, he, m, hlim⟩ :=
    exists_actualExtendedThirdDistinctCompactPrimeSum_approx_ideal hε
  refine ⟨h, hh, e, he0, he, m, ?_⟩
  filter_upwards [hlim, eventually_gt_atTop 1] with N hlimN hN
  simpa only [actualExtendedThirdDistinctCompactProductHarmonicSum_eq hN e h m] using hlimN

end

end ImbalancedChen
