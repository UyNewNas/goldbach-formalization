import ImbalancedChen.ActualRosserOddBox
import ImbalancedChen.ActualRosserTripleBoxFamily

/-!
# Disjoint box families in a fixed odd Rosser layer

For any fixed rank, all separated boxes are joined before their tuples are
injected into the actual positive boundary expansion. Thus the constant
term one occurs only once. The exact terminal/tail weight is the previously
proved actual Euler-weighted tuple mass. The limiting threshold precedes
the target and enumeration cap; empty families and empty boundary tails
are both included.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators

/-- One actual Rosser expansion contains the summed Euler mass of all
disjoint boxes in a fixed odd layer, with its constant term counted once. -/
theorem actualSmallRosserPlusDensity_ratio_ge_oddBoxFamily
    (k : ℕ) {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (a b : ι → Fin (2 * k + 1) → ℝ)
    (N cap : ℕ) (hN : 1 < N) (hEven : Even N) (u beta : ℝ)
    (hbeta : 0 < beta) (hubeta : u ≤ beta)
    (hab : ∀ j ∈ I, ∀ i, a j i < b j i)
    (hsep : ∀ j ∈ I, ∀ i : Fin (2 * k), b j i.succ ≤ a j i.castSucc)
    (hbu : ∀ j ∈ I, b j 0 ≤ u)
    (hprod : ∀ j ∈ I, (∑ i : Fin (2 * k), b j i.castSucc) ≤ beta)
    (hprefix : ∀ j ∈ I, ∀ i : Fin (2 * k), Even i.val →
      (∑ t : Fin (2 * k) with t.val < i.val, b j t.castSucc) +
        3 * b j i.castSucc ≤ beta)
    (hshell : ∀ j ∈ I, beta ≤ (∑ i : Fin (2 * k), a j i.castSucc) +
      3 * a j (Fin.last (2 * k)))
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ∃ t, b i t ≤ a j t ∨ b j t ≤ a i t)
    (hcap : (N : ℝ) ^ u ≤ (cap : ℝ)) :
    1 + (∑ j ∈ I, actualPrimeBoxEulerMass N cap (a j) (b j) u (Fin.last (2 * k))) ≤
      actualSmallRosserPlusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ beta) /
        actualSmallEulerProduct N cap ((N : ℝ) ^ u) := by
  let T := I.biUnion (fun j => actualPrimeBoxTuples N (a j) (b j))
  let P := actualSmallPrimeFinset N cap ((N : ℝ) ^ u)
  let B := fun q => actualUpperRosserBoundarySets N cap
    ((N : ℝ) ^ u) ((N : ℝ) ^ beta) q
  let f := fun z : Sigma (fun _ : ℕ => Finset ℕ) =>
    actualUpperRosserBoundaryTerm N cap ((N : ℝ) ^ u) z.1 z.2
  let e := actualRosserOddBoundaryMap (k := k)
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
  have hanti (p : Fin (2 * k + 1) → ℕ) (hp : p ∈ T) : StrictAnti p := by
    obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hp
    exact actualPrimeBoxTuples_strictAnti (by omega : 1 ≤ N) (hsep j hj) hpj
  have hsubset : T.image e ⊆ P.sigma B := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hp
    have hmem := actualRosserOddBox_mem_boundary k N cap hN (a j) (b j) u beta
      hbeta (hab j hj) (hsep j hj) (hbu j hj) (hprod j hj) (hprefix j hj)
      (hshell j hj) hcap hpj
    exact Finset.mem_sigma.mpr ⟨hmem.1, hmem.2.1⟩
  rw [actualSmallRosserPlusDensity_ratio_eq_one_add_boundary N cap hEven
    ((N : ℝ) ^ u) ((N : ℝ) ^ beta) hcap
    (Real.one_lt_rpow hNreal hbeta) hlevel]
  apply add_le_add (le_refl (1 : ℝ))
  calc
    (∑ j ∈ I, actualPrimeBoxEulerMass N cap (a j) (b j) u (Fin.last (2 * k))) =
        ∑ p ∈ T, f (e p) := by
      simp only [actualPrimeBoxEulerMass]
      rw [← Finset.sum_biUnion hpairwise]
      apply Finset.sum_congr rfl
      intro p hp
      dsimp [f, e, actualRosserOddBoundaryMap, actualUpperRosserBoundaryTerm]
      rw [actualRosserOddTail_prod (hanti p hp).injective, Fin.prod_univ_castSucc]
      ring
    _ = ∑ z ∈ T.image e, f z :=
      (Finset.sum_image (actualRosserOddBoundaryMap_injOn_strictAnti T hanti)).symm
    _ ≤ ∑ z ∈ P.sigma B, f z := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro z hz _
      have hz' := Finset.mem_sigma.mp hz
      apply actualUpperRosserBoundaryTerm_nonneg N cap hEven ((N : ℝ) ^ u) hz'.1
      exact (Finset.mem_powerset.mp (Finset.mem_filter.mp hz'.2).1).trans
        (Finset.filter_subset _ _)
    _ = _ := Finset.sum_sigma P B f

/-- A single threshold supplies all logarithmic box gains of a fixed odd
layer, uniformly in every later even target and complete enumeration cap. -/
theorem exists_actualSmallRosserPlusDensity_oddBoxFamily_lower_threshold
    (k : ℕ) {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (a b : ι → Fin (2 * k + 1) → ℝ)
    (u beta : ℝ) (hu : 0 < u) (hbeta : 0 < beta) (hubeta : u ≤ beta)
    (ha : ∀ j ∈ I, ∀ i, 0 < a j i)
    (hab : ∀ j ∈ I, ∀ i, a j i < b j i)
    (hsep : ∀ j ∈ I, ∀ i : Fin (2 * k), b j i.succ ≤ a j i.castSucc)
    (hbu : ∀ j ∈ I, b j 0 ≤ u)
    (hprod : ∀ j ∈ I, (∑ i : Fin (2 * k), b j i.castSucc) ≤ beta)
    (hprefix : ∀ j ∈ I, ∀ i : Fin (2 * k), Even i.val →
      (∑ t : Fin (2 * k) with t.val < i.val, b j t.castSucc) +
        3 * b j i.castSucc ≤ beta)
    (hshell : ∀ j ∈ I, beta ≤ (∑ i : Fin (2 * k), a j i.castSucc) +
      3 * a j (Fin.last (2 * k)))
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ∃ t, b i t ≤ a j t ∨ b j t ≤ a i t)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
        1 + (∑ j ∈ I, (u / b j (Fin.last (2 * k))) *
          (∏ i, Real.log (b j i / a j i))) - eta ≤
          actualSmallRosserPlusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ beta) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ u) := by
  let eps := eta / ((I.card : ℝ) + 1)
  have heps : 0 < eps := div_pos heta (by positivity)
  have hbuLast (j : ι) (hj : j ∈ I) : b j (Fin.last (2 * k)) ≤ u := by
    have hb : Antitone (b j) := Fin.antitone_iff_succ_le.mpr
      (fun i => (hsep j hj i).trans (hab j hj i.castSucc).le)
    exact (hb (Fin.zero_le _)).trans (hbu j hj)
  have heach (j : I) := exists_actualPrimeBoxEulerMass_lower_threshold
    (a j) (b j) (ha j j.property) (hab j j.property) u hu (Fin.last (2 * k))
    (hbuLast j j.property) eps heps
  choose n hn2 hn using heach
  let N0 := max 2 (Finset.univ.sup n)
  refine ⟨N0, le_max_left _ _, ?_⟩
  intro N hN hEven cap hcap
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hsum : (∑ j ∈ I, ((u / b j (Fin.last (2 * k))) *
      (∏ i, Real.log (b j i / a j i)) - eps)) ≤
        ∑ j ∈ I, actualPrimeBoxEulerMass N cap (a j) (b j) u (Fin.last (2 * k)) := by
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
  have hfull := actualSmallRosserPlusDensity_ratio_ge_oddBoxFamily k I a b
    N cap (by omega) hEven u beta hbeta hubeta hab hsep hbu hprod hprefix hshell hdisj hcap
  linarith

end

end ImbalancedChen
