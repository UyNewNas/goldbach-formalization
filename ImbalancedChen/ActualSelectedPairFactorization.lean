import ImbalancedChen.ActualTwoFactorRepairMonomials

/-!
# The actual selected-pair natural factorization action

The capacity test is made by the action itself.  When C≥1 it keeps the
actual selected pair and allocates its inherited remainder.  When C<1 it
reruns the entire original vector and sets the third factor to one.
Both branches prove the three original numerical constraints at residue
exponent 1+3κ, with one parameter fixed at the original cell representative.

This is an arithmetic factorization for each actual tuple.  It does not
yet prove a common slot assignment for an entire prime box, bounded grouped
convolution coefficients, a distribution estimate or an arithmetic mean.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical

/-- The literal three natural factors, with the capacity case decided here. -/
def actualSelectedPairFactors (D A : ℝ) (yz : Bool) (p : Fin 3 → ℕ)
    (tail : List ℕ) : ℕ × ℕ × ℕ :=
  if 1 ≤ D / (A * (actualSelectedPairProduct yz p : ℝ)) then
    let ac := actualTwoCapacityFactors A (actualSelectedPairRemainingPrime yz p :: tail)
    (ac.1, actualSelectedPairProduct yz p, ac.2)
  else
    let ab := actualTwoCapacityFactors A (p 0 :: p 1 :: p 2 :: tail)
    (ab.1, ab.2, 1)

theorem selectedPair_monomials {x δ θ α A a b c : ℝ}
    (hx : 1 < x) (hApos : 0 < A) (hapos : 0 < a) (hbpos : 0 < b) (hcpos : 0 < c)
    (hcap : A * b * c ≤ x ^ (θ - 2 * δ))
    (hblower : x ^ (2 * θ - 1) ≤ b)
    (hbupper : b ≤ x ^ actualSelectedSubproductUpper α θ) (ha : a ≤ A) :
    A ^ 2 * b * c ^ 2 ≤ x ^ (1 - 4 * δ) ∧
      x ^ (7 * α / 32) * A * a * b ^ 5 * c ^ 2 ≤ x ^ (2 - 4 * δ) ∧
      (A * c / b) ^ (7 / 16 : ℝ) * A * a * b ^ 5 * c ^ 2 ≤
        x ^ (2 - 39 * δ / 8) := by
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hL : 0 < Real.log x := Real.log_pos hx
  have hlogcap := (Real.le_rpow_iff_log_le (mul_pos (mul_pos hApos hbpos) hcpos) hxpos).mp hcap
  rw [Real.log_mul (mul_ne_zero hApos.ne' hbpos.ne') hcpos.ne',
    Real.log_mul hApos.ne' hbpos.ne'] at hlogcap
  have hloglower : (2 * θ - 1) * Real.log x ≤ Real.log b := by
    have h := (Real.log_le_log_iff (Real.rpow_pos_of_pos hxpos _) hbpos).mpr hblower
    rwa [Real.log_rpow hxpos] at h
  have hlogupper := (Real.le_rpow_iff_log_le hbpos hxpos).mp hbupper
  have hlogupper₁ : Real.log b ≤ ((32 - 39 * θ) / 34) * Real.log x :=
    hlogupper.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hL.le)
  have hlogupper₂ : Real.log b ≤ ((2 - 2 * θ - 7 * α / 32) / 3) * Real.log x :=
    hlogupper.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hL.le)
  have hloga : Real.log a ≤ Real.log A := (Real.log_le_log_iff hapos hApos).mpr ha
  refine ⟨?_, ?_, ?_⟩
  · apply Real.le_rpow_of_log_le hxpos
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) hbpos.ne']
    simp only [Real.log_pow]
    nlinarith
  · apply Real.le_rpow_of_log_le hxpos
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) hapos.ne',
      Real.log_mul (by positivity) hApos.ne', Real.log_rpow hxpos]
    simp only [Real.log_pow]
    nlinarith
  · apply Real.le_rpow_of_log_le hxpos
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) hapos.ne',
      Real.log_mul (by positivity) hApos.ne',
      Real.log_rpow (div_pos (mul_pos hApos hcpos) hbpos),
      Real.log_div (mul_ne_zero hApos.ne' hcpos.ne') hbpos.ne',
      Real.log_mul hApos.ne' hcpos.ne']
    simp only [Real.log_pow]
    nlinarith

/-- One actual pair action supplies a factorization and all three targets.
The caller supplies original policy support and the original A range;
neither the capacity case nor a core factorization license is an input. -/
theorem actualExtendedThirdSelectedPair_factorization {e κ δ A : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hκ : κ ≤ e / 4) (hδ0 : 0 < δ) (hδ : δ < 1 / 100000) (hδfine : δ ≤ e / 32)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 32)
    (hfull : actualExtendedThirdDyadicHi m j 0 ≤ VariableEnvelope.mu - 4 * e)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdPhysicalCell m j)
    (yz : Bool) (hk : actualExtendedThirdLeastWinningIndex e m j = if yz then 7 else 6)
    (x : ℝ) (hx : 1 < x) (p : Fin 3 → ℕ)
    (hs : actualSelectedPrimeCoordinates x p ∈ actualExtendedThirdPhysicalCell m j)
    (tail : List ℕ) (hpositive : ∀ q ∈ p 0 :: p 1 :: p 2 :: tail, 0 < q)
    (hsupport : actualDwellSupport (x ^ actualExtendedThirdPhysicalLevel e m j)
      (p 0 :: p 1 :: p 2 :: tail))
    (hAlower : x ^ δ ≤ A) (hAupper : A ≤ x ^ (1 / 3 - δ / 2)) :
    let θ := actualExtendedThirdPairParameter e m j t yz
    let abc := actualSelectedPairFactors (x ^ (θ - 2 * δ)) A yz p tail
    abc.1 * abc.2.1 * abc.2.2 = (p 0 :: p 1 :: p 2 :: tail).prod ∧ (abc.1 : ℝ) ≤ A ∧
      A ^ 2 * (abc.2.1 : ℝ) * (abc.2.2 : ℝ) ^ 2 ≤ x ^ (1 - 3 * δ) ∧
      x ^ (7 * (1 + 3 * κ) / 32) * A * (abc.1 : ℝ) *
        (abc.2.1 : ℝ) ^ 5 * (abc.2.2 : ℝ) ^ 2 ≤ x ^ (2 - 3 * δ) ∧
      (A * (abc.2.2 : ℝ) / (abc.2.1 : ℝ)) ^ (7 / 16 : ℝ) * A * (abc.1 : ℝ) *
        (abc.2.1 : ℝ) ^ 5 * (abc.2.2 : ℝ) ^ 2 ≤ x ^ (2 - 2 * δ) := by
  have hp : ∀ i, 0 < p i := by
    intro i
    fin_cases i <;> exact hpositive _ (by simp)
  obtain ⟨_, _, hblower, hbupper⟩ := actualExtendedThirdSelectedPair_arithmeticInputs
    he0 he hκ hδfine hmesh hfull ht yz hk x hx p hp hs tail hsupport
  have hone : (1 : ℝ) ≤ x ^ δ := by
    simpa only [Real.rpow_zero] using
      (Real.rpow_le_rpow_of_exponent_le hx.le hδ0.le)
  have hA : 1 ≤ A := hone.trans hAlower
  have hApos : 0 < A := zero_lt_one.trans_le hA
  by_cases hC : 1 ≤ x ^ (actualExtendedThirdPairParameter e m j t yz - 2 * δ) /
      (A * (actualSelectedPairProduct yz p : ℝ))
  · obtain ⟨hprod, ha, hc⟩ := actualExtendedThirdSelectedPair_allocate
      he0 he hκ hδfine hmesh hfull ht yz hk x hx p hp hs tail hsupport hA hC
    let ac := actualTwoCapacityFactors A (actualSelectedPairRemainingPrime yz p :: tail)
    have hprodpos : 0 < ac.1 * actualSelectedPairProduct yz p * ac.2 := by
      rw [hprod]
      exact List.prod_pos hpositive
    have hapos : (0 : ℝ) < ac.1 := by
      exact_mod_cast Nat.pos_of_mul_pos_right (Nat.pos_of_mul_pos_right hprodpos)
    have hbpos : (0 : ℝ) < actualSelectedPairProduct yz p := by
      exact_mod_cast Nat.pos_of_mul_pos_left (Nat.pos_of_mul_pos_right hprodpos)
    have hcpos : (0 : ℝ) < ac.2 := by
      exact_mod_cast Nat.pos_of_mul_pos_left hprodpos
    have hcap : A * (actualSelectedPairProduct yz p : ℝ) * (ac.2 : ℝ) ≤
        x ^ (actualExtendedThirdPairParameter e m j t yz - 2 * δ) := by
      calc
        _ = (ac.2 : ℝ) * (A * (actualSelectedPairProduct yz p : ℝ)) := by ring
        _ ≤ _ := (le_div_iff₀ (mul_pos hApos hbpos)).mp hc
    obtain ⟨hfirst, hsecond, hthird⟩ := selectedPair_monomials hx hApos hapos hbpos hcpos
      hcap hblower hbupper ha
    dsimp only
    rw [actualSelectedPairFactors, if_pos hC]
    exact ⟨hprod, ha,
      hfirst.trans (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)),
      hsecond.trans (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)),
      hthird.trans (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith))⟩
  · have hrepair := actualExtendedThirdSelectedPair_smallCapacity_targets
      he0 he hκ hδ0 hδ hδfine hmesh hfull ht yz hk x hx p hs tail hpositive
      hsupport hAlower hAupper (lt_of_not_ge hC)
    dsimp only
    rw [actualSelectedPairFactors, if_neg hC]
    simpa only [Nat.cast_one, one_pow, mul_one] using hrepair

end

end ImbalancedChen
