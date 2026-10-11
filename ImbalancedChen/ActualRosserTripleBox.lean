import ImbalancedChen.ActualRosserBoundaryExpansion
import ImbalancedChen.ActualPrimeBoxEulerLower
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Order.WellFounded

/-!
# A genuine three-prime box in the actual upper Rosser boundary

Adjacent separated logarithmic intervals give three decreasing primes.
Explicit exponent inequalities put their least prime and remaining pair
in the exact upper Rosser boundary at `ceil (N ^ beta)`. The tuple map is
injective, so its actual Euler-weighted mass is counted once in the full
positive boundary expansion. All target-prime exclusions are preserved.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open MathlibNt.SieveTheory

private theorem triple_box_upper_le {a b : Fin 3 → ℝ} {u : ℝ}
    (hab : ∀ i, a i < b i)
    (hsep : ∀ i : Fin 2, b i.succ ≤ a i.castSucc) (hbu : b 0 ≤ u) :
    ∀ i, b i ≤ u := by
  have h01 := hsep 0
  have h12 := hsep 1
  intro i
  fin_cases i
  · exact hbu
  · exact h01.trans ((hab 0).le.trans hbu)
  · exact h12.trans ((hab 1).le.trans (h01.trans ((hab 0).le.trans hbu)))

/-- Every tuple in a box satisfying the two cubic exponent gates lies in
the literal first nonempty Rosser boundary. Both natural ceiling tests are
derived from exact real inequalities, including integer levels. -/
theorem actualRosserTripleBox_mem_boundary
    (N cap : ℕ) (hN : 1 < N) (a b : Fin 3 → ℝ) (u beta : ℝ)
    (hab : ∀ i, a i < b i)
    (hsep : ∀ i : Fin 2, b i.succ ≤ a i.castSucc)
    (hbu : b 0 ≤ u) (hcube : 3 * b 0 ≤ beta)
    (hshell : beta ≤ a 0 + a 1 + 3 * a 2)
    (hcap : (N : ℝ) ^ u ≤ (cap : ℝ))
    {p : Fin 3 → ℕ} (hp : p ∈ actualPrimeBoxTuples N a b) :
    p 2 ∈ actualSmallPrimeFinset N cap ((N : ℝ) ^ u) ∧
      ({p 0, p 1} : Finset ℕ) ∈ actualUpperRosserBoundarySets N cap
        ((N : ℝ) ^ u) ((N : ℝ) ^ beta) (p 2) := by
  have hNreal : (1 : ℝ) < N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hNreal
  have hm := mem_actualPrimeBoxTuples_iff.mp hp
  have hanti := actualPrimeBoxTuples_strictAnti (by omega : 1 ≤ N) hsep hp
  have h10 : p 1 < p 0 := hanti (by decide)
  have h21 : p 2 < p 1 := hanti (by decide)
  have hP (i : Fin 3) : p i ∈ actualSmallPrimeFinset N cap ((N : ℝ) ^ u) := by
    rw [mem_actualSmallPrimeFinset_iff_of_cutoff_le_cap hcap]
    exact ⟨(hm i).1, (hm i).2.1, (hm i).2.2.2.trans_le
      (Real.rpow_le_rpow_of_exponent_le hNreal.le (triple_box_upper_le hab hsep hbu i))⟩
  have hcubereal : (p 0 : ℝ) ^ 3 < (N : ℝ) ^ beta := by
    calc
      (p 0 : ℝ) ^ 3 < ((N : ℝ) ^ b 0) ^ 3 := by
        exact pow_lt_pow_left₀ (hm 0).2.2.2 (Nat.cast_nonneg _) (by decide)
      _ = (N : ℝ) ^ (b 0 * 3) := (Real.rpow_mul_natCast hNpos.le (b 0) 3).symm
      _ ≤ (N : ℝ) ^ beta :=
        Real.rpow_le_rpow_of_exponent_le hNreal.le (by linarith)
  have hshellreal : (N : ℝ) ^ beta ≤ (p 1 : ℝ) * p 0 * (p 2 : ℝ) ^ 3 := by
    calc
      (N : ℝ) ^ beta ≤ (N : ℝ) ^ (a 0 + a 1 + 3 * a 2) :=
        Real.rpow_le_rpow_of_exponent_le hNreal.le hshell
      _ = ((N : ℝ) ^ a 1 * (N : ℝ) ^ a 0) * ((N : ℝ) ^ a 2) ^ 3 := by
        rw [Real.rpow_add hNpos, Real.rpow_add hNpos,
          show 3 * a 2 = a 2 * (3 : ℕ) by ring,
          Real.rpow_mul_natCast hNpos.le]
        ring
      _ ≤ (p 1 : ℝ) * p 0 * (p 2 : ℝ) ^ 3 := by
        apply mul_le_mul
        · exact mul_le_mul (hm 1).2.2.1 (hm 0).2.2.1
            (Real.rpow_nonneg hNpos.le _) (Nat.cast_nonneg _)
        · exact pow_le_pow_left₀ (Real.rpow_nonneg hNpos.le _) (hm 2).2.2.1 3
        · positivity
        · positivity
  have hboundary : LinearSieve.UpperRosserBoundarySet (Nat.ceil ((N : ℝ) ^ beta))
      (p 2) {p 1, p 0} := by
    apply (LinearSieve.upperRosserBoundarySet_pair_iff (hm 2).1 (hm 0).1 h21 h10).mpr
    constructor
    · apply Nat.lt_ceil.mpr
      exact_mod_cast hcubereal
    · apply Nat.ceil_le.mpr
      exact_mod_cast hshellreal
  refine ⟨hP 2, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩⟩
  · intro r hr
    rcases Finset.mem_insert.mp hr with hr | hr
    · subst r
      exact Finset.mem_filter.mpr ⟨hP 0, h21.trans h10⟩
    · have hr' := Finset.mem_singleton.mp hr
      subst r
      exact Finset.mem_filter.mpr ⟨hP 1, h21⟩
  · simpa only [Finset.pair_comm (p 1) (p 0)] using hboundary

private theorem triple_range (p : Fin 3 → ℕ) :
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

/-- The terminal-prime/pair map loses no multiplicity on a separated box.
Strict order recovers the tuple from its range. -/
theorem actualRosserTripleBox_boundary_injOn
    (N : ℕ) (hN : 1 ≤ N) (a b : Fin 3 → ℝ)
    (hsep : ∀ i : Fin 2, b i.succ ≤ a i.castSucc) :
    Set.InjOn (fun p : Fin 3 → ℕ =>
      (⟨p 2, {p 0, p 1}⟩ : Sigma (fun _ : ℕ => Finset ℕ)))
      (actualPrimeBoxTuples N a b) := by
  intro p hp r hr heq
  have hq : p 2 = r 2 := congrArg Sigma.fst heq
  have hs : ({p 0, p 1} : Finset ℕ) = {r 0, r 1} :=
    congrArg (fun z : Sigma (fun _ : ℕ => Finset ℕ) => z.2) heq
  apply ((actualPrimeBoxTuples_strictAnti hN hsep hp).range_inj
    (actualPrimeBoxTuples_strictAnti hN hsep hr)).mp
  rw [triple_range p, triple_range r, hs, hq]

/-- The actual Euler-weighted three-prime box embeds once into the full
positive boundary sum of the same raw upper Rosser coefficient. -/
theorem actualSmallRosserPlusDensity_ratio_ge_tripleBox
    (N cap : ℕ) (hN : 1 < N) (hEven : Even N)
    (a b : Fin 3 → ℝ) (u beta : ℝ)
    (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i)
    (hsep : ∀ i : Fin 2, b i.succ ≤ a i.castSucc)
    (hbu : b 0 ≤ u) (hcube : 3 * b 0 ≤ beta)
    (hshell : beta ≤ a 0 + a 1 + 3 * a 2) (hubeta : u ≤ beta)
    (hcap : (N : ℝ) ^ u ≤ (cap : ℝ)) :
    1 + actualPrimeBoxEulerMass N cap a b u 2 ≤
      actualSmallRosserPlusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ beta) /
        actualSmallEulerProduct N cap ((N : ℝ) ^ u) := by
  let P := actualSmallPrimeFinset N cap ((N : ℝ) ^ u)
  let B := fun q => actualUpperRosserBoundarySets N cap
    ((N : ℝ) ^ u) ((N : ℝ) ^ beta) q
  let f := fun z : Sigma (fun _ : ℕ => Finset ℕ) =>
    actualUpperRosserBoundaryTerm N cap ((N : ℝ) ^ u) z.1 z.2
  let e := fun p : Fin 3 → ℕ => (⟨p 2, {p 0, p 1}⟩ : Sigma (fun _ : ℕ => Finset ℕ))
  have hNreal : (1 : ℝ) < N := by exact_mod_cast hN
  have hbeta : 0 < beta := (ha 0).trans_le ((hab 0).le.trans (hbu.trans hubeta))
  have hlevel : ∀ p ∈ P, (p : ℝ) < (N : ℝ) ^ beta := by
    intro p hp
    exact (mem_actualSmallPrimeFinset.mp hp).2.2.2.trans_le
      (Real.rpow_le_rpow_of_exponent_le hNreal.le hubeta)
  rw [actualSmallRosserPlusDensity_ratio_eq_one_add_boundary N cap hEven
    ((N : ℝ) ^ u) ((N : ℝ) ^ beta) hcap (Real.one_lt_rpow hNreal hbeta) hlevel]
  apply add_le_add (le_refl (1 : ℝ))
  have hsubset : (actualPrimeBoxTuples N a b).image e ⊆ P.sigma B := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_sigma.mpr
      (actualRosserTripleBox_mem_boundary N cap hN a b u beta hab hsep
        hbu hcube hshell hcap hp)
  calc
    actualPrimeBoxEulerMass N cap a b u 2 =
        ∑ p ∈ actualPrimeBoxTuples N a b, f (e p) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hne : p 0 ≠ p 1 := ne_of_gt
        (actualPrimeBoxTuples_strictAnti (by omega : 1 ≤ N) hsep hp (by decide))
      dsimp [f, e, actualUpperRosserBoundaryTerm]
      simp [Fin.prod_univ_succ, hne, mul_comm, mul_left_comm, mul_assoc]
      ring
    _ = ∑ z ∈ (actualPrimeBoxTuples N a b).image e, f z :=
      (Finset.sum_image (actualRosserTripleBox_boundary_injOn N (by omega)
        a b hsep)).symm
    _ ≤ ∑ z ∈ P.sigma B, f z := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro z hz _
      have hz' := Finset.mem_sigma.mp hz
      apply actualUpperRosserBoundaryTerm_nonneg N cap hEven ((N : ℝ) ^ u) hz'.1
      exact (Finset.mem_powerset.mp (Finset.mem_filter.mp hz'.2).1).trans
        (Finset.filter_subset _ _)
    _ = _ := Finset.sum_sigma P B f

/-- The explicit box contribution gives a proved eventual lower bound on
the normalized actual raw density, uniformly in every covering cap. -/
theorem exists_actualSmallRosserPlusDensity_tripleBox_lower_threshold
    (a b : Fin 3 → ℝ) (u beta : ℝ)
    (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i)
    (hsep : ∀ i : Fin 2, b i.succ ≤ a i.castSucc)
    (hbu : b 0 ≤ u) (hcube : 3 * b 0 ≤ beta)
    (hshell : beta ≤ a 0 + a 1 + 3 * a 2) (hubeta : u ≤ beta)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
        1 + (u / b 2) * (∏ i, Real.log (b i / a i)) - eta ≤
          actualSmallRosserPlusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ beta) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ u) := by
  have hu : 0 < u := (ha 0).trans_le ((hab 0).le.trans hbu)
  obtain ⟨N0, hN0, hbound⟩ := exists_actualPrimeBoxEulerMass_lower_threshold
    a b ha hab u hu 2 (triple_box_upper_le hab hsep hbu 2) eta heta
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven cap hcap
  have hmass := hbound N hN hEven cap hcap
  have hfull := actualSmallRosserPlusDensity_ratio_ge_tripleBox N cap (by omega)
    hEven a b u beta ha hab hsep hbu hcube hshell hubeta hcap
  linarith

/-- The concrete separated box [.30,.32) x [.27,.29) x [.17,.19)
lies inside the first nonempty boundary at residual coordinate three.
Its explicit positive gain is supplied without any geometric premise. -/
theorem exists_actualSmallRosserPlusDensity_oneThird_box_lower_threshold
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ (1 / 3 : ℝ) ≤ (cap : ℝ) →
        1 + (100 / 57 : ℝ) * Real.log (16 / 15 : ℝ) *
            Real.log (29 / 27 : ℝ) * Real.log (19 / 17 : ℝ) - eta ≤
          actualSmallRosserPlusDensity N cap ((N : ℝ) ^ (1 / 3 : ℝ)) (N : ℝ) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ (1 / 3 : ℝ)) := by
  let a : Fin 3 → ℝ := ![3 / 10, 27 / 100, 17 / 100]
  let b : Fin 3 → ℝ := ![8 / 25, 29 / 100, 19 / 100]
  have ha : ∀ i, 0 < a i := by intro i; fin_cases i <;> norm_num [a]
  have hab : ∀ i, a i < b i := by intro i; fin_cases i <;> norm_num [a, b]
  have hsep : ∀ i : Fin 2, b i.succ ≤ a i.castSucc := by
    intro i
    fin_cases i <;> norm_num [a, b, Matrix.cons_val_two]
  obtain ⟨N0, hN0, hbound⟩ := exists_actualSmallRosserPlusDensity_tripleBox_lower_threshold
    a b (1 / 3) 1 ha hab hsep (by norm_num [b]) (by norm_num [b])
    (by norm_num [a, Matrix.cons_val_two]) (by norm_num) eta heta
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven cap hcap
  have h := hbound N hN hEven cap hcap
  have hgain : ((1 / 3 : ℝ) / b 2) * (∏ i, Real.log (b i / a i)) =
      (100 / 57 : ℝ) * Real.log (16 / 15 : ℝ) *
        Real.log (29 / 27 : ℝ) * Real.log (19 / 17 : ℝ) := by
    norm_num [a, b, Fin.prod_univ_succ, Matrix.cons_val_two]
    ring
  rw [hgain] at h
  simpa only [Real.rpow_one] using h

/-- A fully numeric, nontrivial lower bound for the same actual raw upper
coefficient at residual coordinate three. This single box does not claim
the sharp F(3) constant or any control of the omitted positive layers. -/
theorem exists_actualSmallRosserPlusDensity_oneThird_ge_one_add_one_div_twoThousand :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ (1 / 3 : ℝ) ≤ (cap : ℝ) →
        1 + (1 / 2000 : ℝ) ≤
          actualSmallRosserPlusDensity N cap ((N : ℝ) ^ (1 / 3 : ℝ)) (N : ℝ) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ (1 / 3 : ℝ)) := by
  have h1 : (1 / 16 : ℝ) ≤ Real.log (16 / 15 : ℝ) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 16 / 15)
    norm_num at h
    exact h
  have h2 : (2 / 29 : ℝ) ≤ Real.log (29 / 27 : ℝ) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 29 / 27)
    norm_num at h
    exact h
  have h3 : (2 / 19 : ℝ) ≤ Real.log (19 / 17 : ℝ) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 19 / 17)
    norm_num at h
    exact h
  have h12 := mul_le_mul h1 h2 (by norm_num : (0 : ℝ) ≤ 2 / 29)
    ((by norm_num : (0 : ℝ) ≤ 1 / 16).trans h1)
  have h123 := mul_le_mul h12 h3 (by norm_num : (0 : ℝ) ≤ 2 / 19)
    ((by norm_num : (0 : ℝ) ≤ (1 / 16) * (2 / 29)).trans h12)
  have hgain : (25 / 31407 : ℝ) ≤
      (100 / 57 : ℝ) * Real.log (16 / 15 : ℝ) *
        Real.log (29 / 27 : ℝ) * Real.log (19 / 17 : ℝ) := by
    calc
      (25 / 31407 : ℝ) = (100 / 57) * ((1 / 16) * (2 / 29) * (2 / 19)) := by norm_num
      _ ≤ (100 / 57) * (Real.log (16 / 15 : ℝ) * Real.log (29 / 27 : ℝ) *
          Real.log (19 / 17 : ℝ)) := mul_le_mul_of_nonneg_left h123 (by norm_num)
      _ = _ := by ring
  obtain ⟨N0, hN0, hbound⟩ :=
    exists_actualSmallRosserPlusDensity_oneThird_box_lower_threshold (1 / 10000) (by norm_num)
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven cap hcap
  have h := hbound N hN hEven cap hcap
  linarith

end

end ImbalancedChen
