import ImbalancedChen.Part3ProperPrimePowerCount
import ImbalancedChen.Part3SignedModulusPayment
import Mathlib

/-!
# Proper-prime-power payment for the original labelled source

This is the finite arithmetic step in the frozen 2026-11-06 manuscript,
coefficient appendix, proof of Proposition D.3: removing proper prime powers
keeps the complete product, the original modulus weights, and the coprime
mean.  The proper-power tuples form a union, so a tuple marked in several
coordinates is subtracted only once.

The modulus-row argument is provided by `Part3SignedModulusPayment`.
The diagonal divisor-tuple injection follows the existing source-only
`P5ProperPowerSignedModulusPayment.collisionWords_card_le_divisor_power`,
adapted to the actual finite labelled coordinates of the current baseline.
These finite estimates do not assert the later asymptotic chart budget.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset
open scoped BigOperators

/-- The union of the proper-power marked tuples in a coordinate box. -/
def properPowerBox (k P : ℕ) (U : Fin k → ℕ) : Finset (Fin k → Fin (P + 1)) :=
  Finset.univ.filter (fun t => (∀ i, (t i).val ≤ U i) ∧
    ∃ i, properPrimePower (t i).val)

/-- A union bound, using the already proved count of proper prime powers. -/
def properPowerBoxBudget (k : ℕ) (U : Fin k → ℕ) : ℕ :=
  ∑ i : Fin k, Nat.sqrt (U i) * Nat.log 2 (U i) *
    ∏ j ∈ Finset.univ.erase i, (U j + 1)

private def properPowerBoxMarked (k P : ℕ) (U : Fin k → ℕ) (i : Fin k) :
    Finset (Fin k → Fin (P + 1)) :=
  Finset.univ.filter (fun t => (∀ j, (t j).val ≤ U j) ∧ properPrimePower (t i).val)

private theorem card_properPowerBoxMarked_le (k P : ℕ) (U : Fin k → ℕ) (i : Fin k) :
    (properPowerBoxMarked k P U i).card ≤
      Nat.sqrt (U i) * Nat.log 2 (U i) *
        ∏ j ∈ Finset.univ.erase i, (U j + 1) := by
  let S (j : Fin k) : Finset ℕ :=
    if j = i then (Finset.range (U j + 1)).filter properPrimePower
    else Finset.range (U j + 1)
  let T := properPowerBoxMarked k P U i
  have hmem (t : T) (j : Fin k) : (t.val j).val ∈ S j := by
    have ht := (Finset.mem_filter.mp t.property).2
    have hu : (t.val j).val ∈ Finset.range (U j + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le (ht.1 j))
    by_cases hji : j = i
    · subst j
      exact (by simpa only [S, if_pos rfl] using Finset.mem_filter.mpr ⟨hu, ht.2⟩)
    · simpa only [S, if_neg hji] using hu
  let encode : T → (j : Fin k) → S j := fun t j => ⟨(t.val j).val, hmem t j⟩
  have hinj : Function.Injective encode := by
    intro t u h
    apply Subtype.ext
    funext j
    apply Fin.ext
    exact congrArg (fun f : (j : Fin k) → S j => (f j).val) h
  have hcard : T.card ≤ ∏ j : Fin k, (S j).card := by
    simpa only [Fintype.card_coe, Fintype.card_pi] using
      Fintype.card_le_of_injective encode hinj
  have hprod : (∏ j : Fin k, (S j).card) =
      ((Finset.range (U i + 1)).filter properPrimePower).card *
        ∏ j ∈ Finset.univ.erase i, (U j + 1) := by
    rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin k)) (fun j => (S j).card)
      (Finset.mem_univ i)]
    congr 1
    · simp [S]
    · apply Finset.prod_congr rfl
      intro j hj
      simp only [S, if_neg (Finset.mem_erase.mp hj).1, Finset.card_range]
  rw [hprod] at hcard
  exact hcard.trans (Nat.mul_le_mul_right _ (card_properPrimePowers_range_le (U i)))

theorem card_properPowerBox_le (k P : ℕ) (U : Fin k → ℕ) :
    (properPowerBox k P U).card ≤ properPowerBoxBudget k U := by
  have heq : properPowerBox k P U =
      Finset.univ.biUnion (properPowerBoxMarked k P U) := by
    ext t
    simp only [properPowerBox, properPowerBoxMarked, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_biUnion, exists_and_left]
  rw [heq]
  exact Finset.card_biUnion_le.trans
    (Finset.sum_le_sum (fun i _ => card_properPowerBoxMarked_le k P U i))

/-- A zero complete product has zero von Mangoldt coefficient, even though
the set of marked tuples itself can contain tuples with a zero coordinate. -/
theorem labelledVonMangoldtWeight_eq_zero_of_product_eq_zero
    {k P : ℕ} (t : Fin k → Fin (P + 1)) (ht : labelledProduct t = 0) :
    labelledVonMangoldtWeight t = 0 := by
  change (∏ i : Fin k, (t i).val) = 0 at ht
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp ht
  unfold labelledVonMangoldtWeight
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [vonMangoldtOverLog, hi]

theorem labelledProperPowerResidual_zero
    (k P : ℕ) (W : (Fin k → Fin (P + 1)) → ℝ) :
    labelledProperPowerResidual k P W 0 = 0 := by
  unfold labelledProperPowerResidual finiteProductMass
  apply Finset.sum_eq_zero
  intro t _
  by_cases ht : labelledProduct t = 0
  · simp [ht, labelledVonMangoldtWeight_eq_zero_of_product_eq_zero t ht]
  · simp [ht]

private theorem norm_labelledProperPowerResidual_le_effective
    (k P : ℕ) (W : (Fin k → Fin (P + 1)) → ℝ) (U : Fin k → ℕ)
    (hU : ∀ t, W t * labelledVonMangoldtWeight t ≠ 0 → ∀ i, (t i).val ≤ U i)
    (b : ℕ) :
    ‖labelledProperPowerResidual k P W b‖ ≤
      ∑ t ∈ properPowerBox k P U,
        if labelledProduct t = b then |W t| else 0 := by
  unfold labelledProperPowerResidual finiteProductMass
  refine (norm_sum_le _ _).trans ?_
  unfold properPowerBox
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_le_sum
  intro t _
  by_cases hb : labelledProduct t = b
  · by_cases hp : ∃ i, properPrimePower (t i).val
    · by_cases hz : W t * labelledVonMangoldtWeight t = 0
      · simp only [hb, hp, hz, if_pos, Complex.ofReal_zero, norm_zero]
        positivity
      · have hbox := hU t hz
        have hbox' : (∀ i, (t i).val ≤ U i) ∧ ∃ i, properPrimePower (t i).val := ⟨hbox, hp⟩
        simp only [if_pos hp, if_pos hb, if_pos hbox',
          Complex.norm_real, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (labelledVonMangoldtWeight_mem_Icc t).1]
        exact mul_le_of_le_one_right (abs_nonneg _) (labelledVonMangoldtWeight_mem_Icc t).2
    · simp [hp]
  · simp [hb]

/-- Total residual mass on any finite product carrier. The support
hypothesis is imposed only where the original coefficient is nonzero. -/
theorem sum_norm_labelledProperPowerResidual_le
    (k P : ℕ) (W : (Fin k → Fin (P + 1)) → ℝ) (U : Fin k → ℕ)
    (B : Finset ℕ) {M : ℝ} (hM : 0 ≤ M) (hW : ∀ t, |W t| ≤ M)
    (hU : ∀ t, W t * labelledVonMangoldtWeight t ≠ 0 → ∀ i, (t i).val ≤ U i) :
    (∑ b ∈ B, ‖labelledProperPowerResidual k P W b‖) ≤
      M * (properPowerBoxBudget k U : ℝ) := by
  calc
    _ ≤ ∑ b ∈ B, ∑ t ∈ properPowerBox k P U,
        if labelledProduct t = b then |W t| else 0 :=
      Finset.sum_le_sum (fun b _ => norm_labelledProperPowerResidual_le_effective k P W U hU b)
    _ = ∑ t ∈ properPowerBox k P U, ∑ b ∈ B,
        if labelledProduct t = b then |W t| else 0 := Finset.sum_comm
    _ ≤ ∑ t ∈ properPowerBox k P U, M := by
      apply Finset.sum_le_sum
      intro t _
      rw [Finset.sum_ite_eq]
      split_ifs
      · exact hW t
      · exact hM
    _ = M * ((properPowerBox k P U).card : ℝ) := by simp [mul_comm]
    _ ≤ M * (properPowerBoxBudget k U : ℝ) :=
      mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_properPowerBox_le k P U)) hM

/-- Any original labelled integer tuple in a nonzero product fibre
injects into the tuple of divisors of that complete product. -/
theorem card_labelledProduct_fibre_le (k P N : ℕ) (hN : N ≠ 0) :
    ((Finset.univ : Finset (Fin k → Fin (P + 1))).filter
      (fun t => labelledProduct t = N)).card ≤ N.divisors.card ^ k := by
  let S := (Finset.univ : Finset (Fin k → Fin (P + 1))).filter
    (fun t => labelledProduct t = N)
  have hdiv (t : S) (i : Fin k) : (t.val i).val ∈ N.divisors := by
    apply Nat.mem_divisors.mpr
    refine ⟨?_, hN⟩
    rw [← (Finset.mem_filter.mp t.property).2]
    exact Finset.dvd_prod_of_mem (fun i => (t.val i).val) (Finset.mem_univ i)
  let encode : S → (Fin k → N.divisors) := fun t i => ⟨(t.val i).val, hdiv t i⟩
  have hinj : Function.Injective encode := by
    intro t u h
    apply Subtype.ext
    funext i
    apply Fin.ext
    exact congrArg (fun f : Fin k → N.divisors => (f i).val) h
  simpa only [Fintype.card_coe, Fintype.card_pi_const, Fintype.card_fin] using
    Fintype.card_le_of_injective encode hinj

/-- The genuine product diagonal has the labelled integer multiplicity,
without imposing a prime-only multiplicity estimate. -/
theorem norm_labelledProperPowerResidual_le_diagonal
    (k P N : ℕ) (W : (Fin k → Fin (P + 1)) → ℝ) (hN : N ≠ 0)
    {M : ℝ} (hM : 0 ≤ M) (hW : ∀ t, |W t| ≤ M) :
    ‖labelledProperPowerResidual k P W N‖ ≤ M * (N.divisors.card : ℝ) ^ k := by
  let S := (Finset.univ : Finset (Fin k → Fin (P + 1))).filter
    (fun t => labelledProduct t = N)
  calc
    _ ≤ ∑ t ∈ Finset.univ.filter (fun t : Fin k → Fin (P + 1) =>
        ∃ i, properPrimePower (t i).val),
        if labelledProduct t = N then |W t| else 0 := norm_labelledProperPowerResidual_le k P W N
    _ ≤ ∑ t : Fin k → Fin (P + 1), if labelledProduct t = N then |W t| else 0 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun t _ _ => by split_ifs <;> positivity)
    _ = ∑ t ∈ S, |W t| := by simp only [S, Finset.sum_filter]
    _ ≤ ∑ _t ∈ S, M := Finset.sum_le_sum (fun t _ => hW t)
    _ = M * (S.card : ℝ) := by simp [mul_comm]
    _ ≤ M * (N.divisors.card : ℝ) ^ k := by
      apply mul_le_mul_of_nonneg_left _ hM
      exact_mod_cast card_labelledProduct_fibre_le k P N hN

/-- The zero target has no diagonal coefficient; other targets keep the
true divisor tuple multiplicity. -/
def properPowerDiagonalBudget (k N : ℕ) : ℕ :=
  if N = 0 then 0 else N.divisors.card ^ k

theorem norm_labelledProperPowerResidual_le_diagonalBudget
    (k P N : ℕ) (W : (Fin k → Fin (P + 1)) → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hW : ∀ t, |W t| ≤ M) :
    ‖labelledProperPowerResidual k P W N‖ ≤ M * (properPowerDiagonalBudget k N : ℝ) := by
  by_cases hN : N = 0
  · subst N
    simp [labelledProperPowerResidual_zero, properPowerDiagonalBudget]
  · simpa only [properPowerDiagonalBudget, if_neg hN, Nat.cast_pow] using
      norm_labelledProperPowerResidual_le_diagonal k P N W hN hM hW

/-- The proper-power correction is paid after the complete modulus sum.
The same coefficient `ρ` remains in both progression count and coprime mean;
the exact-product diagonal is paid separately. -/
theorem labelledProperPowerResidual_signedError_norm_le
    (k P N J D : ℕ) (B Q : Finset ℕ) (ρ : ℕ → ℂ)
    (W : (Fin k → Fin (P + 1)) → ℝ) (U : Fin k → ℕ)
    {M Cρ : ℝ} (hM : 0 ≤ M) (hCρ : 0 ≤ Cρ)
    (hW : ∀ t, |W t| ≤ M)
    (hU : ∀ t, W t * labelledVonMangoldtWeight t ≠ 0 → ∀ i, (t i).val ≤ U i)
    (hρ : ∀ q ∈ Q, ‖ρ q‖ ≤ Cρ * (q.divisors.card : ℝ) ^ J)
    (hD : ∀ b ∈ B, b ≠ N → (Nat.dist b N).divisors.card ≤ D) :
    ‖finiteProductSignedError B Q N ρ (labelledProperPowerResidual k P W)‖ ≤
      (M * (properPowerBoxBudget k U : ℝ)) *
        (Cρ * (D : ℝ) ^ (J + 1) + SignedModulusPayment.meanMass Q ρ) +
      (M * (properPowerDiagonalBudget k N : ℝ)) * SignedModulusPayment.modulusMass Q ρ := by
  simpa only [finiteProductSignedError, finiteProductKernel] using
    SignedModulusPayment.signedError_norm_le_budget B Q N J D ρ
      (labelledProperPowerResidual k P W) hCρ hρ hD
      (sum_norm_labelledProperPowerResidual_le k P W U B hM hW hU)
      (norm_labelledProperPowerResidual_le_diagonalBudget k P N W hM hW)

/-- The off-diagonal divisor envelope is computed from the finite carrier,
so this version has no additional divisor-budget assumption. -/
theorem labelledProperPowerResidual_signedError_norm_le_finite
    (k P N J : ℕ) (B Q : Finset ℕ) (ρ : ℕ → ℂ)
    (W : (Fin k → Fin (P + 1)) → ℝ) (U : Fin k → ℕ)
    {M Cρ : ℝ} (hM : 0 ≤ M) (hCρ : 0 ≤ Cρ)
    (hW : ∀ t, |W t| ≤ M)
    (hU : ∀ t, W t * labelledVonMangoldtWeight t ≠ 0 → ∀ i, (t i).val ≤ U i)
    (hρ : ∀ q ∈ Q, ‖ρ q‖ ≤ Cρ * (q.divisors.card : ℝ) ^ J) :
    ‖finiteProductSignedError B Q N ρ (labelledProperPowerResidual k P W)‖ ≤
      (M * (properPowerBoxBudget k U : ℝ)) *
        (Cρ * (((B.erase N).sup (fun b => (Nat.dist b N).divisors.card) : ℕ) : ℝ) ^ (J + 1) +
          SignedModulusPayment.meanMass Q ρ) +
      (M * (properPowerDiagonalBudget k N : ℝ)) * SignedModulusPayment.modulusMass Q ρ := by
  exact labelledProperPowerResidual_signedError_norm_le k P N J _ B Q ρ W U hM hCρ hW hU hρ
    (fun _ hb hbN => SignedModulusPayment.dist_divisors_card_le_sup B N hb hbN)

/-- The proved residual payment attaches directly to the existing exact
prime/von-Mangoldt identity, on the same finite carrier and modulus weights. -/
theorem primeProductSignedError_sub_vonMangoldt_norm_le
    (k P N J D : ℕ) (B Q : Finset ℕ) (ρ : ℕ → ℝ)
    (W : (Fin k → Fin (P + 1)) → ℝ) (U : Fin k → ℕ)
    {M Cρ : ℝ} (hM : 0 ≤ M) (hCρ : 0 ≤ Cρ)
    (hW : ∀ t, |W t| ≤ M)
    (hU : ∀ t, W t * labelledVonMangoldtWeight t ≠ 0 → ∀ i, (t i).val ≤ U i)
    (hρ : ∀ q ∈ Q, |ρ q| ≤ Cρ * (q.divisors.card : ℝ) ^ J)
    (hD : ∀ b ∈ B, b ≠ N → (Nat.dist b N).divisors.card ≤ D)
    (hB : ∀ t ∈ labelledPrimeTuples k P, W t ≠ 0 → labelledProduct t ∈ B) :
    ‖(primeProductSignedError k P N Q ρ W : ℂ) -
        finiteProductSignedError B Q N (fun q => (ρ q : ℂ))
          (labelledVonMangoldtProductMass k P W)‖ ≤
      (M * (properPowerBoxBudget k U : ℝ)) *
        (Cρ * (D : ℝ) ^ (J + 1) + SignedModulusPayment.meanMass Q (fun q => (ρ q : ℂ))) +
      (M * (properPowerDiagonalBudget k N : ℝ)) *
        SignedModulusPayment.modulusMass Q (fun q => (ρ q : ℂ)) := by
  rw [primeProductSignedError_eq_vonMangoldt_sub_properPower k P N Q B ρ W hB,
    sub_sub_cancel_left, norm_neg]
  exact labelledProperPowerResidual_signedError_norm_le k P N J D B Q (fun q => (ρ q : ℂ))
    W U hM hCρ hW hU
    (fun q hq => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hρ q hq) hD

end
end ImbalancedChen.Part3
