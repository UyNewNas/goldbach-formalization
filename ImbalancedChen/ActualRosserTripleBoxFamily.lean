import ImbalancedChen.ActualRosserTripleBox

/-!
# Finite disjoint families of actual three-prime boundary boxes

The tuple carriers of separated logarithmic boxes are disjoint. Their union
is injected once into the same actual upper Rosser boundary, so the constant
one is counted once, not once per box. A finite maximum of the actual box
thresholds supplies a common eventual lower bound independent of the later
even target and its enumeration cap. The empty family is included.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open MathlibNt.SieveTheory

/-- Separation of one exponent interval makes the true tuple carriers
disjoint. Equality of adjacent endpoints is allowed by the half-open cells. -/
theorem actualPrimeBoxTuples_disjoint_of_axis_separation
    {k : ℕ} (N : ℕ) (hN : 1 ≤ N) (a b c d : Fin k → ℝ)
    (hsep : ∃ i, b i ≤ c i ∨ d i ≤ a i) :
    Disjoint (actualPrimeBoxTuples N a b) (actualPrimeBoxTuples N c d) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hp' := mem_actualPrimeBoxTuples_iff.mp hp
  have hq' := mem_actualPrimeBoxTuples_iff.mp hq
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨i, hi | hi⟩ := hsep
  · have hpow := Real.rpow_le_rpow_of_exponent_le hNreal hi
    exact (not_lt_of_ge (hq' i).2.2.1) ((hp' i).2.2.2.trans_le hpow)
  · have hpow := Real.rpow_le_rpow_of_exponent_le hNreal hi
    exact (not_lt_of_ge (hp' i).2.2.1) ((hq' i).2.2.2.trans_le hpow)

private theorem triple_range_eq_pair_union (p : Fin 3 → ℕ) :
    Set.range p = (↑({p 0, p 1} : Finset ℕ) : Set ℕ) ∪ {p 2} := by
  ext n
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hn
    simp only [Set.mem_union, Finset.mem_coe, Finset.mem_insert,
      Finset.mem_singleton, Set.mem_singleton_iff] at hn
    rcases hn with (rfl | rfl) | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

/-- The boundary map is injective on every family of decreasing triples,
even when the triples originate in different boxes. -/
theorem actualRosserTripleBoundaryMap_injOn_strictAnti
    (T : Finset (Fin 3 → ℕ)) (hT : ∀ p ∈ T, StrictAnti p) :
    Set.InjOn (fun p : Fin 3 → ℕ =>
      (⟨p 2, {p 0, p 1}⟩ : Sigma (fun _ : ℕ => Finset ℕ))) T := by
  intro p hp r hr heq
  have hq : p 2 = r 2 := congrArg Sigma.fst heq
  have hs : ({p 0, p 1} : Finset ℕ) = {r 0, r 1} :=
    congrArg (fun z : Sigma (fun _ : ℕ => Finset ℕ) => z.2) heq
  apply ((hT p hp).range_inj (hT r hr)).mp
  rw [triple_range_eq_pair_union p, triple_range_eq_pair_union r, hs, hq]

/-- The whole disjoint family contributes to one actual Rosser expansion.
The constant term is one, including for an empty family. -/
theorem actualSmallRosserPlusDensity_ratio_ge_tripleBoxFamily
    {ι : Type*} [DecidableEq ι] (I : Finset ι) (a b : ι → Fin 3 → ℝ)
    (N cap : ℕ) (hN : 1 < N) (hEven : Even N) (u beta : ℝ)
    (hu : 0 < u) (hubeta : u ≤ beta)
    (hab : ∀ j ∈ I, ∀ i, a j i < b j i)
    (hsep : ∀ j ∈ I, ∀ i : Fin 2, b j i.succ ≤ a j i.castSucc)
    (hbu : ∀ j ∈ I, b j 0 ≤ u)
    (hcube : ∀ j ∈ I, 3 * b j 0 ≤ beta)
    (hshell : ∀ j ∈ I, beta ≤ a j 0 + a j 1 + 3 * a j 2)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ∃ k, b i k ≤ a j k ∨ b j k ≤ a i k)
    (hcap : (N : ℝ) ^ u ≤ (cap : ℝ)) :
    1 + (∑ j ∈ I, actualPrimeBoxEulerMass N cap (a j) (b j) u 2) ≤
      actualSmallRosserPlusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ beta) /
        actualSmallEulerProduct N cap ((N : ℝ) ^ u) := by
  let T := I.biUnion (fun j => actualPrimeBoxTuples N (a j) (b j))
  let P := actualSmallPrimeFinset N cap ((N : ℝ) ^ u)
  let B := fun q => actualUpperRosserBoundarySets N cap
    ((N : ℝ) ^ u) ((N : ℝ) ^ beta) q
  let f := fun z : Sigma (fun _ : ℕ => Finset ℕ) =>
    actualUpperRosserBoundaryTerm N cap ((N : ℝ) ^ u) z.1 z.2
  let e := fun p : Fin 3 → ℕ =>
    (⟨p 2, {p 0, p 1}⟩ : Sigma (fun _ : ℕ => Finset ℕ))
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
  have hanti (p : Fin 3 → ℕ) (hp : p ∈ T) : StrictAnti p := by
    obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hp
    exact actualPrimeBoxTuples_strictAnti (by omega : 1 ≤ N) (hsep j hj) hpj
  have hsubset : T.image e ⊆ P.sigma B := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hp
    exact Finset.mem_sigma.mpr
      (actualRosserTripleBox_mem_boundary N cap hN (a j) (b j) u beta
        (hab j hj) (hsep j hj) (hbu j hj) (hcube j hj) (hshell j hj) hcap hpj)
  rw [actualSmallRosserPlusDensity_ratio_eq_one_add_boundary N cap hEven
    ((N : ℝ) ^ u) ((N : ℝ) ^ beta) hcap
    (Real.one_lt_rpow hNreal (hu.trans_le hubeta)) hlevel]
  apply add_le_add (le_refl (1 : ℝ))
  calc
    (∑ j ∈ I, actualPrimeBoxEulerMass N cap (a j) (b j) u 2) =
        ∑ p ∈ T, f (e p) := by
      simp only [actualPrimeBoxEulerMass]
      rw [← Finset.sum_biUnion hpairwise]
      apply Finset.sum_congr rfl
      intro p hp
      have hne : p 0 ≠ p 1 := ne_of_gt (hanti p hp (by decide))
      dsimp [f, e, actualUpperRosserBoundaryTerm]
      simp [Fin.prod_univ_succ, hne, mul_comm, mul_left_comm, mul_assoc]
      ring
    _ = ∑ z ∈ T.image e, f z :=
      (Finset.sum_image (actualRosserTripleBoundaryMap_injOn_strictAnti T hanti)).symm
    _ ≤ ∑ z ∈ P.sigma B, f z := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro z hz _
      have hz' := Finset.mem_sigma.mp hz
      apply actualUpperRosserBoundaryTerm_nonneg N cap hEven ((N : ℝ) ^ u) hz'.1
      exact (Finset.mem_powerset.mp (Finset.mem_filter.mp hz'.2).1).trans
        (Finset.filter_subset _ _)
    _ = _ := Finset.sum_sigma P B f

/-- One threshold works for the sum of all gains in a fixed disjoint
family, every later even target, and every cap covering the outer cutoff.
All analytic inputs are the already proved actual one-box suppliers. -/
theorem exists_actualSmallRosserPlusDensity_tripleBoxFamily_lower_threshold
    {ι : Type*} [DecidableEq ι] (I : Finset ι) (a b : ι → Fin 3 → ℝ)
    (u beta : ℝ) (hu : 0 < u) (hubeta : u ≤ beta)
    (ha : ∀ j ∈ I, ∀ k, 0 < a j k)
    (hab : ∀ j ∈ I, ∀ k, a j k < b j k)
    (hsep : ∀ j ∈ I, ∀ k : Fin 2, b j k.succ ≤ a j k.castSucc)
    (hbu : ∀ j ∈ I, b j 0 ≤ u)
    (hcube : ∀ j ∈ I, 3 * b j 0 ≤ beta)
    (hshell : ∀ j ∈ I, beta ≤ a j 0 + a j 1 + 3 * a j 2)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ∃ k, b i k ≤ a j k ∨ b j k ≤ a i k)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
        1 + (∑ j ∈ I, (u / b j 2) * (∏ k, Real.log (b j k / a j k))) - eta ≤
          actualSmallRosserPlusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ beta) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ u) := by
  let eps := eta / ((I.card : ℝ) + 1)
  have heps : 0 < eps := div_pos heta (by positivity)
  have hbu2 (j : ι) (hj : j ∈ I) : b j 2 ≤ u := by
    have h01 := hsep j hj 0
    have h12 := hsep j hj 1
    exact h12.trans ((hab j hj 1).le.trans
      (h01.trans ((hab j hj 0).le.trans (hbu j hj))))
  have heach (j : I) := exists_actualPrimeBoxEulerMass_lower_threshold
    (a j) (b j) (ha j j.property) (hab j j.property) u hu 2
    (hbu2 j j.property) eps heps
  choose n hn2 hn using heach
  let N0 := max 2 (Finset.univ.sup n)
  refine ⟨N0, le_max_left _ _, ?_⟩
  intro N hN hEven cap hcap
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hsum : (∑ j ∈ I, ((u / b j 2) * (∏ k, Real.log (b j k / a j k)) - eps)) ≤
      ∑ j ∈ I, actualPrimeBoxEulerMass N cap (a j) (b j) u 2 := by
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
  have hfull := actualSmallRosserPlusDensity_ratio_ge_tripleBoxFamily I a b
    N cap (by omega) hEven u beta hu hubeta hab hsep hbu hcube hshell hdisj hcap
  linarith

end

end ImbalancedChen
