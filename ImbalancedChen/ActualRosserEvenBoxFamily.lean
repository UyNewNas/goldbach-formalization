import ImbalancedChen.ActualRosserEvenBox
import ImbalancedChen.ActualRosserTripleBoxFamily

/-!
# Finite families of actual even Rosser boundary boxes

Disjoint boxes enter the same literal lower Rosser boundary expansion.
Their nonnegative Euler-weighted masses are subtracted from one once.
Strict order removes repeated tuples, and tail cardinality distinguishes
ranks. The eventual threshold is chosen before the target and every
covering enumeration cap; empty families are included.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators

/-- One actual lower Rosser expansion subtracts the summed Euler mass of all
disjoint boxes in a fixed even layer, with its constant term counted once. -/
theorem actualSmallRosserMinusDensity_ratio_le_evenBoxFamily
    (k : ℕ) {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (a b : ι → Fin (2 * k + 2) → ℝ)
    (N cap : ℕ) (hN : 1 < N) (hEven : Even N) (u beta : ℝ)
    (hbeta : 0 < beta) (hubeta : u ≤ beta)
    (hab : ∀ j ∈ I, ∀ i, a j i < b j i)
    (hsep : ∀ j ∈ I, ∀ i : Fin (2 * k + 1), b j i.succ ≤ a j i.castSucc)
    (hbu : ∀ j ∈ I, b j 0 ≤ u)
    (hprod : ∀ j ∈ I, (∑ i : Fin (2 * k + 1), b j i.castSucc) ≤ beta)
    (hprefix : ∀ j ∈ I, ∀ i : Fin (2 * k + 1), Odd i.val →
      (∑ t : Fin (2 * k + 1) with t.val < i.val, b j t.castSucc) +
        3 * b j i.castSucc ≤ beta)
    (hshell : ∀ j ∈ I, beta ≤ (∑ i : Fin (2 * k + 1), a j i.castSucc) +
      3 * a j (Fin.last (2 * k + 1)))
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ∃ t, b i t ≤ a j t ∨ b j t ≤ a i t)
    (hcap : (N : ℝ) ^ u ≤ (cap : ℝ)) :
    actualSmallRosserMinusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ beta) /
        actualSmallEulerProduct N cap ((N : ℝ) ^ u) ≤
      1 - (∑ j ∈ I, actualPrimeBoxEulerMass N cap (a j) (b j) u (Fin.last (2 * k + 1))) := by
  let T := I.biUnion (fun j => actualPrimeBoxTuples N (a j) (b j))
  let P := actualSmallPrimeFinset N cap ((N : ℝ) ^ u)
  let B := fun q => actualLowerRosserBoundarySets N cap
    ((N : ℝ) ^ u) ((N : ℝ) ^ beta) q
  let f := fun z : Sigma (fun _ : ℕ => Finset ℕ) =>
    actualLowerRosserBoundaryTerm N cap ((N : ℝ) ^ u) z.1 z.2
  let e := actualRosserEvenBoundaryMap (k := k)
  have hNreal : (1 : ℝ) < N := by exact_mod_cast hN
  have hlevel : ∀ p ∈ P, (p : ℝ) < (N : ℝ) ^ beta := by
    intro p hp
    exact (mem_actualSmallPrimeFinset.mp hp).2.2.2.trans_le
      (Real.rpow_le_rpow_of_exponent_le hNreal.le hubeta)
  have hpairwise : Set.PairwiseDisjoint (I : Set ι)
      (fun j => actualPrimeBoxTuples N (a j) (b j)) := by
    intro i hi j hj hij
    exact actualPrimeBoxTuples_disjoint_of_axis_separation N (by omega)
      (a i) (b i) (a j) (b j) (hdisj i hi j hj hij)
  have hanti (p : Fin (2 * k + 2) → ℕ) (hp : p ∈ T) : StrictAnti p := by
    obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hp
    exact actualPrimeBoxTuples_strictAnti (by omega : 1 ≤ N) (hsep j hj) hpj
  have hsubset : T.image e ⊆ P.sigma B := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hp
    have hmem := actualRosserEvenBox_mem_boundary k N cap hN (a j) (b j) u beta
      hbeta (hab j hj) (hsep j hj) (hbu j hj) (hprod j hj) (hprefix j hj)
      (hshell j hj) hcap hpj
    exact Finset.mem_sigma.mpr ⟨hmem.1, hmem.2.1⟩
  rw [actualSmallRosserMinusDensity_ratio_eq_one_sub_boundary N cap hEven
    ((N : ℝ) ^ u) ((N : ℝ) ^ beta) hcap
    (Real.one_lt_rpow hNreal hbeta) hlevel]
  apply sub_le_sub_left
  calc
    (∑ j ∈ I, actualPrimeBoxEulerMass N cap (a j) (b j) u (Fin.last (2 * k + 1))) =
        ∑ p ∈ T, f (e p) := by
      simp only [actualPrimeBoxEulerMass]
      rw [← Finset.sum_biUnion hpairwise]
      apply Finset.sum_congr rfl
      intro p hp
      dsimp [f, e, actualRosserEvenBoundaryMap, actualLowerRosserBoundaryTerm, actualUpperRosserBoundaryTerm]
      rw [actualRosserEvenTail_prod (hanti p hp).injective, Fin.prod_univ_castSucc]
      ring
    _ = ∑ z ∈ T.image e, f z :=
      (Finset.sum_image (actualRosserEvenBoundaryMap_injOn_strictAnti T hanti)).symm
    _ ≤ ∑ z ∈ P.sigma B, f z := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro z hz _
      have hz' := Finset.mem_sigma.mp hz
      apply actualLowerRosserBoundaryTerm_nonneg N cap hEven ((N : ℝ) ^ u) hz'.1
      exact (Finset.mem_powerset.mp (Finset.mem_filter.mp hz'.2).1).trans
        (Finset.filter_subset _ _)
    _ = _ := Finset.sum_sigma P B f

/-- A single threshold supplies all logarithmic box gains of a fixed even
layer, uniformly in every later even target and complete enumeration cap. -/
theorem exists_actualSmallRosserMinusDensity_evenBoxFamily_upper_threshold
    (k : ℕ) {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (a b : ι → Fin (2 * k + 2) → ℝ)
    (u beta : ℝ) (hu : 0 < u) (hbeta : 0 < beta) (hubeta : u ≤ beta)
    (ha : ∀ j ∈ I, ∀ i, 0 < a j i)
    (hab : ∀ j ∈ I, ∀ i, a j i < b j i)
    (hsep : ∀ j ∈ I, ∀ i : Fin (2 * k + 1), b j i.succ ≤ a j i.castSucc)
    (hbu : ∀ j ∈ I, b j 0 ≤ u)
    (hprod : ∀ j ∈ I, (∑ i : Fin (2 * k + 1), b j i.castSucc) ≤ beta)
    (hprefix : ∀ j ∈ I, ∀ i : Fin (2 * k + 1), Odd i.val →
      (∑ t : Fin (2 * k + 1) with t.val < i.val, b j t.castSucc) +
        3 * b j i.castSucc ≤ beta)
    (hshell : ∀ j ∈ I, beta ≤ (∑ i : Fin (2 * k + 1), a j i.castSucc) +
      3 * a j (Fin.last (2 * k + 1)))
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ∃ t, b i t ≤ a j t ∨ b j t ≤ a i t)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
        actualSmallRosserMinusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ beta) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ u) ≤
          1 - (∑ j ∈ I, (u / b j (Fin.last (2 * k + 1))) *
            (∏ i, Real.log (b j i / a j i))) + eta := by
  let eps := eta / ((I.card : ℝ) + 1)
  have heps : 0 < eps := div_pos heta (by positivity)
  have hbuLast (j : ι) (hj : j ∈ I) : b j (Fin.last (2 * k + 1)) ≤ u := by
    have hb : Antitone (b j) := Fin.antitone_iff_succ_le.mpr
      (fun i => (hsep j hj i).trans (hab j hj i.castSucc).le)
    exact (hb (Fin.zero_le _)).trans (hbu j hj)
  have heach (j : I) := exists_actualPrimeBoxEulerMass_lower_threshold
    (a j) (b j) (ha j j.property) (hab j j.property) u hu (Fin.last (2 * k + 1))
    (hbuLast j j.property) eps heps
  choose n hn2 hn using heach
  let N0 := max 2 (Finset.univ.sup n)
  refine ⟨N0, le_max_left _ _, ?_⟩
  intro N hN hEven cap hcap
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hsum : (∑ j ∈ I, ((u / b j (Fin.last (2 * k + 1))) *
      (∏ i, Real.log (b j i / a j i)) - eps)) ≤
        ∑ j ∈ I, actualPrimeBoxEulerMass N cap (a j) (b j) u (Fin.last (2 * k + 1)) := by
    apply Finset.sum_le_sum
    intro j hj
    have hjN : n ⟨j, hj⟩ ≤ N :=
      (Finset.le_sup (f := n) (Finset.mem_univ ⟨j, hj⟩)).trans
        ((le_max_right _ _).trans hN)
    exact hn ⟨j, hj⟩ N hjN hEven cap hcap
  rw [Finset.sum_sub_distrib] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  have hloss : (I.card : ℝ) * eps ≤ eta := by
    dsimp [eps]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (I.card : ℝ) + 1)).mpr
    nlinarith
  have hfull := actualSmallRosserMinusDensity_ratio_le_evenBoxFamily k I a b
    N cap (by omega) hEven u beta hbeta hubeta hab hsep hbu hprod hprefix hshell hdisj hcap
  linarith

end

end ImbalancedChen
