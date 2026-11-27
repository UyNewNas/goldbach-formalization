import ImbalancedChen.ActualRosserOddBoxFamily

/-!
# Finite unions of different odd Rosser layers

Within each rank, disjoint boxes give distinct actual tuples and strict
order makes their boundary map injective. Between ranks, the boundary tail
cardinality distinguishes the images. The entire finite union therefore
enters the same positive raw-density expansion once, with one constant term.

The limiting theorem chooses the thresholds of the finitely many actual
boxes before the target and enumeration cap. It requires no uniform estimate
over all ranks and uses only the already proved box-mass supplier.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators

/-- All selected boxes in all selected ranks contribute to one actual
boundary expansion. The initial one is counted once even for empty ranks. -/
theorem actualSmallRosserPlusDensity_ratio_ge_oddBoxUnion
    (K : Finset ℕ) {ι : ℕ → Type*} [∀ k, DecidableEq (ι k)]
    (J : ∀ k, Finset (ι k)) (a b : ∀ k, ι k → Fin (2 * k + 1) → ℝ)
    (N cap : ℕ) (hN : 1 < N) (hEven : Even N) (u beta : ℝ)
    (hbeta : 0 < beta) (hubeta : u ≤ beta)
    (hab : ∀ k ∈ K, ∀ j ∈ J k, ∀ i, a k j i < b k j i)
    (hsep : ∀ k ∈ K, ∀ j ∈ J k, ∀ i : Fin (2 * k),
      b k j i.succ ≤ a k j i.castSucc)
    (hbu : ∀ k ∈ K, ∀ j ∈ J k, b k j 0 ≤ u)
    (hprod : ∀ k ∈ K, ∀ j ∈ J k, (∑ i : Fin (2 * k), b k j i.castSucc) ≤ beta)
    (hprefix : ∀ k ∈ K, ∀ j ∈ J k, ∀ i : Fin (2 * k), Even i.val →
      (∑ t : Fin (2 * k) with t.val < i.val, b k j t.castSucc) +
        3 * b k j i.castSucc ≤ beta)
    (hshell : ∀ k ∈ K, ∀ j ∈ J k,
      beta ≤ (∑ i : Fin (2 * k), a k j i.castSucc) + 3 * a k j (Fin.last (2 * k)))
    (hdisj : ∀ k ∈ K, ∀ i ∈ J k, ∀ j ∈ J k, i ≠ j →
      ∃ t, b k i t ≤ a k j t ∨ b k j t ≤ a k i t)
    (hcap : (N : ℝ) ^ u ≤ (cap : ℝ)) :
    1 + (∑ k ∈ K, ∑ j ∈ J k,
      actualPrimeBoxEulerMass N cap (a k j) (b k j) u (Fin.last (2 * k))) ≤
      actualSmallRosserPlusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ beta) /
        actualSmallEulerProduct N cap ((N : ℝ) ^ u) := by
  let T := fun k => (J k).biUnion (fun j => actualPrimeBoxTuples N (a k j) (b k j))
  let E := fun k => (T k).image (actualRosserOddBoundaryMap (k := k))
  let P := actualSmallPrimeFinset N cap ((N : ℝ) ^ u)
  let B := fun q => actualUpperRosserBoundarySets N cap
    ((N : ℝ) ^ u) ((N : ℝ) ^ beta) q
  let f := fun z : Sigma (fun _ : ℕ => Finset ℕ) =>
    actualUpperRosserBoundaryTerm N cap ((N : ℝ) ^ u) z.1 z.2
  have hNreal : (1 : ℝ) < N := by exact_mod_cast hN
  have hlevel : ∀ p ∈ P, (p : ℝ) < (N : ℝ) ^ beta := by
    intro p hp
    exact (mem_actualSmallPrimeFinset.mp hp).2.2.2.trans_le
      (Real.rpow_le_rpow_of_exponent_le hNreal.le hubeta)
  have hboxDisjoint (k : ℕ) (hk : k ∈ K) :
      Set.PairwiseDisjoint (J k : Set (ι k))
        (fun j => actualPrimeBoxTuples N (a k j) (b k j)) := by
    intro i hi j hj hij
    exact actualPrimeBoxTuples_disjoint_of_axis_separation N (by omega)
      (a k i) (b k i) (a k j) (b k j) (hdisj k hk i hi j hj hij)
  have hanti (k : ℕ) (hk : k ∈ K) (p : Fin (2 * k + 1) → ℕ) (hp : p ∈ T k) :
      StrictAnti p := by
    obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hp
    exact actualPrimeBoxTuples_strictAnti (by omega : 1 ≤ N) (hsep k hk j hj) hpj
  have hRanksDisjoint : Set.PairwiseDisjoint (K : Set ℕ) E := by
    intro k hk l hl hkl
    apply Finset.disjoint_left.mpr
    intro z hzk hzl
    obtain ⟨p, hp, hep⟩ := Finset.mem_image.mp hzk
    obtain ⟨r, hr, her⟩ := Finset.mem_image.mp hzl
    have ht : actualRosserOddTail p = actualRosserOddTail r :=
      congrArg (fun z : Sigma (fun _ : ℕ => Finset ℕ) => z.2) (hep.trans her.symm)
    exact hkl (actualRosserOddTail_rank_eq (hanti k hk p hp).injective
      (hanti l hl r hr).injective ht)
  have hsubset : K.biUnion E ⊆ P.sigma B := by
    intro z hz
    obtain ⟨k, hk, hzk⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hzk
    obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hp
    have hmem := actualRosserOddBox_mem_boundary k N cap hN (a k j) (b k j) u beta
      hbeta (hab k hk j hj) (hsep k hk j hj) (hbu k hk j hj) (hprod k hk j hj)
      (hprefix k hk j hj) (hshell k hk j hj) hcap hpj
    exact Finset.mem_sigma.mpr ⟨hmem.1, hmem.2.1⟩
  have hmass (k : ℕ) (hk : k ∈ K) :
      (∑ j ∈ J k, actualPrimeBoxEulerMass N cap (a k j) (b k j) u (Fin.last (2 * k))) =
        ∑ z ∈ E k, f z := by
    calc
      _ = ∑ p ∈ T k, f (actualRosserOddBoundaryMap p) := by
        simp only [actualPrimeBoxEulerMass]
        rw [← Finset.sum_biUnion (hboxDisjoint k hk)]
        apply Finset.sum_congr rfl
        intro p hp
        dsimp [f, actualRosserOddBoundaryMap, actualUpperRosserBoundaryTerm]
        rw [actualRosserOddTail_prod (hanti k hk p hp).injective, Fin.prod_univ_castSucc]
        ring
      _ = _ :=
        (Finset.sum_image (actualRosserOddBoundaryMap_injOn_strictAnti (T k) (hanti k hk))).symm
  rw [actualSmallRosserPlusDensity_ratio_eq_one_add_boundary N cap hEven
    ((N : ℝ) ^ u) ((N : ℝ) ^ beta) hcap
    (Real.one_lt_rpow hNreal hbeta) hlevel]
  apply add_le_add (le_refl (1 : ℝ))
  calc
    (∑ k ∈ K, ∑ j ∈ J k,
        actualPrimeBoxEulerMass N cap (a k j) (b k j) u (Fin.last (2 * k))) =
        ∑ k ∈ K, ∑ z ∈ E k, f z := Finset.sum_congr rfl hmass
    _ = ∑ z ∈ K.biUnion E, f z := (Finset.sum_biUnion hRanksDisjoint).symm
    _ ≤ ∑ z ∈ P.sigma B, f z := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro z hz _
      have hz' := Finset.mem_sigma.mp hz
      apply actualUpperRosserBoundaryTerm_nonneg N cap hEven ((N : ℝ) ^ u) hz'.1
      exact (Finset.mem_powerset.mp (Finset.mem_filter.mp hz'.2).1).trans
        (Finset.filter_subset _ _)
    _ = _ := Finset.sum_sigma P B f

/-- One common threshold supplies the logarithmic gains of every selected
box in every selected finite rank, with no assumed prime-density limit. -/
theorem exists_actualSmallRosserPlusDensity_oddBoxUnion_lower_threshold
    (K : Finset ℕ) {ι : ℕ → Type*} [∀ k, DecidableEq (ι k)]
    (J : ∀ k, Finset (ι k)) (a b : ∀ k, ι k → Fin (2 * k + 1) → ℝ)
    (u beta : ℝ) (hu : 0 < u) (hbeta : 0 < beta) (hubeta : u ≤ beta)
    (ha : ∀ k ∈ K, ∀ j ∈ J k, ∀ i, 0 < a k j i)
    (hab : ∀ k ∈ K, ∀ j ∈ J k, ∀ i, a k j i < b k j i)
    (hsep : ∀ k ∈ K, ∀ j ∈ J k, ∀ i : Fin (2 * k),
      b k j i.succ ≤ a k j i.castSucc)
    (hbu : ∀ k ∈ K, ∀ j ∈ J k, b k j 0 ≤ u)
    (hprod : ∀ k ∈ K, ∀ j ∈ J k, (∑ i : Fin (2 * k), b k j i.castSucc) ≤ beta)
    (hprefix : ∀ k ∈ K, ∀ j ∈ J k, ∀ i : Fin (2 * k), Even i.val →
      (∑ t : Fin (2 * k) with t.val < i.val, b k j t.castSucc) +
        3 * b k j i.castSucc ≤ beta)
    (hshell : ∀ k ∈ K, ∀ j ∈ J k,
      beta ≤ (∑ i : Fin (2 * k), a k j i.castSucc) + 3 * a k j (Fin.last (2 * k)))
    (hdisj : ∀ k ∈ K, ∀ i ∈ J k, ∀ j ∈ J k, i ≠ j →
      ∃ t, b k i t ≤ a k j t ∨ b k j t ≤ a k i t)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
        1 + (∑ k ∈ K, ∑ j ∈ J k, (u / b k j (Fin.last (2 * k))) *
          (∏ i, Real.log (b k j i / a k j i))) - eta ≤
          actualSmallRosserPlusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ beta) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ u) := by
  let S := K.sigma J
  let gain := fun z : Sigma ι => (u / b z.1 z.2 (Fin.last (2 * z.1))) *
    (∏ i, Real.log (b z.1 z.2 i / a z.1 z.2 i))
  let mass := fun (N cap : ℕ) (z : Sigma ι) =>
    actualPrimeBoxEulerMass N cap (a z.1 z.2) (b z.1 z.2) u (Fin.last (2 * z.1))
  let eps := eta / ((S.card : ℝ) + 1)
  have heps : 0 < eps := div_pos heta (by positivity)
  have hbuLast (k : ℕ) (hk : k ∈ K) (j : ι k) (hj : j ∈ J k) :
      b k j (Fin.last (2 * k)) ≤ u := by
    have hb : Antitone (b k j) := Fin.antitone_iff_succ_le.mpr
      (fun i => (hsep k hk j hj i).trans (hab k hk j hj i.castSucc).le)
    exact (hb (Fin.zero_le _)).trans (hbu k hk j hj)
  have heach (z : S) : ∃ n : ℕ, 2 ≤ n ∧ ∀ N : ℕ, n ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) → gain z.val - eps ≤ mass N cap z.val := by
    have hz := Finset.mem_sigma.mp z.property
    exact exists_actualPrimeBoxEulerMass_lower_threshold
      (a z.val.1 z.val.2) (b z.val.1 z.val.2)
      (ha z.val.1 hz.1 z.val.2 hz.2) (hab z.val.1 hz.1 z.val.2 hz.2)
      u hu (Fin.last (2 * z.val.1)) (hbuLast z.val.1 hz.1 z.val.2 hz.2) eps heps
  choose n hn2 hn using heach
  let N0 := max 2 (Finset.univ.sup n)
  refine ⟨N0, le_max_left _ _, ?_⟩
  intro N hN hEven cap hcap
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hsum : (∑ z ∈ S, (gain z - eps)) ≤ ∑ z ∈ S, mass N cap z := by
    apply Finset.sum_le_sum
    intro z hz
    have hzN : n ⟨z, hz⟩ ≤ N :=
      (Finset.le_sup (f := n) (Finset.mem_univ ⟨z, hz⟩)).trans
        ((le_max_right _ _).trans hN)
    exact hn ⟨z, hz⟩ N hzN hEven cap hcap
  rw [Finset.sum_sub_distrib] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  have hloss : (S.card : ℝ) * eps ≤ eta := by
    dsimp [eps]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (S.card : ℝ) + 1)).mpr
    nlinarith
  have hfull := actualSmallRosserPlusDensity_ratio_ge_oddBoxUnion K J a b
    N cap (by omega) hEven u beta hbeta hubeta hab hsep hbu hprod hprefix hshell hdisj hcap
  have hgain : (∑ z ∈ S, gain z) = ∑ k ∈ K, ∑ j ∈ J k,
      (u / b k j (Fin.last (2 * k))) * (∏ i, Real.log (b k j i / a k j i)) :=
    Finset.sum_sigma K J gain
  have hmass : (∑ z ∈ S, mass N cap z) = ∑ k ∈ K, ∑ j ∈ J k,
      actualPrimeBoxEulerMass N cap (a k j) (b k j) u (Fin.last (2 * k)) :=
    Finset.sum_sigma K J (mass N cap)
  rw [hgain, hmass] at hsum
  linarith

end

end ImbalancedChen
